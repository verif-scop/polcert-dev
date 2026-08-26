#!/usr/bin/env python3
"""Small OpenScop storage probe.

This is not a full OpenScop parser.  It extracts enough structure for storage
survey evidence:

- array names from the <arrays> extension;
- access relation arity for each array id;
- dependence count from the <dependence> extension.

It is useful for checking whether a tool changed a scalar access into an
indexed access, as Candl -scalexp does for scalar temporaries.
"""

from __future__ import annotations

import argparse
import re
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path


ACCESS_RE = re.compile(r"^\s*0\s+-1(?P<rest>(?:\s+[-0-9]+)+)\s+##\s+Arr\s*==\s*(?P<name>\S+)")
ARRAY_MAP_RE = re.compile(r"^\s*(?P<id>\d+)\s+(?P<name>\S+)\s*$")
DEPENDENCE_COUNT_RE = re.compile(r"^# Number of dependences\s*$")


@dataclass(frozen=True)
class ScopSummary:
    path: Path
    access_dims: dict[str, list[int]]
    access_index_rows: dict[str, list[str]]
    dependence_count: int | None


def parse_scop(path: Path) -> ScopSummary:
    lines = path.read_text(errors="replace").splitlines()
    access_dims: dict[str, list[int]] = defaultdict(list)
    access_index_rows: dict[str, list[str]] = defaultdict(list)
    dep_count: int | None = None

    for idx, line in enumerate(lines):
        match = ACCESS_RE.match(line)
        if match:
            # OpenScop access relation header line immediately above has shape:
            #   <rows> <cols> <out dims> ...
            # For storage survey, the first integer on the previous non-comment
            # line is enough: scalar access uses 1 output dim (array id only),
            # indexed access uses 2+ output dims (array id plus indices).
            dims = None
            for prev in range(idx - 1, max(idx - 5, -1), -1):
                text = lines[prev].strip()
                if not text or text.startswith("#"):
                    continue
                parts = text.split()
                if parts and parts[0].lstrip("-").isdigit():
                    dims = int(parts[0])
                    break
            if dims is not None:
                name = match.group("name")
                access_dims[name].append(dims)
                for next_idx in range(idx + 1, min(idx + max(dims, 1), len(lines))):
                    next_line = lines[next_idx]
                    if "## [" in next_line:
                        access_index_rows[name].append(next_line.strip())
            continue

        if DEPENDENCE_COUNT_RE.match(line) and idx + 1 < len(lines):
            try:
                dep_count = int(lines[idx + 1].strip())
            except ValueError:
                pass

    return ScopSummary(
        path=path,
        access_dims=dict(access_dims),
        access_index_rows=dict(access_index_rows),
        dependence_count=dep_count,
    )


def format_dims(dims: list[int]) -> str:
    counts: dict[int, int] = defaultdict(int)
    for dim in dims:
        counts[dim] += 1
    return ", ".join(f"{dim}D x{count}" for dim, count in sorted(counts.items()))


def main() -> int:
    parser = argparse.ArgumentParser(description="Compare storage-relevant OpenScop access shapes.")
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    args = parser.parse_args()

    before = parse_scop(args.before)
    after = parse_scop(args.after)

    names = sorted(set(before.access_dims) | set(after.access_dims))
    print(f"before: {before.path}")
    print(f"after:  {after.path}")
    print()
    print("Access arity by array:")
    for name in names:
        b = format_dims(before.access_dims.get(name, [])) or "-"
        a = format_dims(after.access_dims.get(name, [])) or "-"
        marker = " changed" if b != a else ""
        print(f"  {name}: {b} -> {a}{marker}")

    print()
    print("Dependence count:")
    print(f"  before: {before.dependence_count if before.dependence_count is not None else 'unknown'}")
    print(f"  after:  {after.dependence_count if after.dependence_count is not None else 'unknown'}")

    print()
    print("Index relation rows by array:")
    for name in names:
        b_rows = before.access_index_rows.get(name, [])
        a_rows = after.access_index_rows.get(name, [])
        marker = " changed" if b_rows != a_rows else ""
        if not b_rows and not a_rows:
            continue
        print(f"  {name}:{marker}")
        print(f"    before: {b_rows if b_rows else '-'}")
        print(f"    after:  {a_rows if a_rows else '-'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
