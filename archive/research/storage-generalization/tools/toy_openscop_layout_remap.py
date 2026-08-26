#!/usr/bin/env python3
"""Toy OpenScop layout-remap probe.

This tool rewrites a simple one-dimensional access relation for a named array
from `[1] == i` to `[1] == scale * i`.  It is intentionally narrow: it is a
survey probe for access-level layout remapping, not a full OpenScop
transformation framework.

Expected relation shape:

  WRITE/READ
  2 6 2 1 0 1
  # e/i| Arr [1]| i | N | 1
     0 -1  0 0 0 A    ## Arr == name
     0  0 -1 1 0 0    ## [1] == i

The output keeps the same array id and relation arity, but changes the affine
index row coefficient from `1` to `scale`.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path


ARR_RE = re.compile(r"^(?P<prefix>\s*0\s+-1(?:\s+[-0-9]+)+\s+##\s+Arr\s*==\s*)(?P<name>\S+)(?P<suffix>.*)$")


def parse_relation_header(lines: list[str], arr_idx: int) -> tuple[int, int] | None:
    for prev in range(arr_idx - 1, max(arr_idx - 8, -1), -1):
        text = lines[prev].strip()
        if not text or text.startswith("#"):
            continue
        parts = text.split()
        if len(parts) >= 4 and all(part.lstrip("-").isdigit() for part in parts[:4]):
            out_dims = int(parts[2])
            in_dims = int(parts[3])
            return out_dims, in_dims
    return None


def rewrite_index_line(line: str, out_dims: int, scale: int) -> str:
    if "## [" not in line:
        return line
    body, comment = line.split("##", 1)
    values = body.split()
    if len(values) <= out_dims + 1:
        raise ValueError(f"cannot rewrite index row: {line}")

    # Columns are: equality flag, output dims..., input dims..., params..., const.
    first_input_col = 1 + out_dims
    values[first_input_col] = str(scale)
    return "   " + " ".join(f"{int(value):4d}" for value in values) + "    ##" + comment


def transform(input_path: Path, output_path: Path, array: str, scale: int) -> int:
    lines = input_path.read_text(errors="replace").splitlines()
    rewrites = 0
    idx = 0
    while idx < len(lines):
        match = ARR_RE.match(lines[idx])
        if not match or match.group("name") != array:
            idx += 1
            continue

        header = parse_relation_header(lines, idx)
        if header is None:
            raise ValueError(f"could not find relation header before line {idx + 1}")
        out_dims, in_dims = header
        if out_dims != 2 or in_dims != 1:
            raise ValueError(
                f"only one-dimensional array accesses are supported; "
                f"found out_dims={out_dims}, in_dims={in_dims} at line {idx + 1}"
            )
        if idx + 1 >= len(lines):
            raise ValueError(f"missing index row after line {idx + 1}")
        lines[idx + 1] = rewrite_index_line(lines[idx + 1], out_dims, scale)
        rewrites += 1
        idx += 2

    if rewrites == 0:
        raise ValueError(f"array {array!r} was not rewritten")

    output_path.write_text("\n".join(lines) + "\n")
    return rewrites


def main() -> int:
    parser = argparse.ArgumentParser(description="Toy OpenScop one-dimensional layout remap.")
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--array", required=True)
    parser.add_argument("--scale", type=int, required=True)
    args = parser.parse_args()

    rewrites = transform(args.input, args.output, args.array, args.scale)
    print(f"rewrote {rewrites} access relation(s) for array {args.array} with scale {args.scale}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
