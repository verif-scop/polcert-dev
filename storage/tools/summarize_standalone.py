#!/usr/bin/env python3
"""Summarize standalone storage validation logs.

The standalone prototype prints blocks like:

  PASS case_name [classification]
    - obligation

and negative checks like:

  PASS_NEG bad_case [case_name]: rejected (reason)

This helper turns those logs into Markdown or JSON so the storage survey can
track coverage without hand-maintaining tables.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, asdict
from pathlib import Path


PASS_RE = re.compile(r"^PASS\s+(?P<name>\S+)\s+\[(?P<classification>[^\]]+)\]")
OBLIGATION_RE = re.compile(r"^\s+-\s+(?P<text>.+?)\s*$")
PASS_NEG_RE = re.compile(
    r"^PASS_NEG\s+(?P<neg>\S+)\s+\[(?P<case>\S+)\]:\s+rejected\s+\((?P<reason>.*)\)"
)


@dataclass
class PositiveCase:
    name: str
    classification: str
    obligations: list[str]


@dataclass
class NegativeCase:
    name: str
    case: str
    reason: str


def parse_positive(path: Path) -> list[PositiveCase]:
    cases: list[PositiveCase] = []
    current: PositiveCase | None = None
    for line in path.read_text(errors="replace").splitlines():
        match = PASS_RE.match(line)
        if match:
            current = PositiveCase(
                name=match.group("name"),
                classification=match.group("classification"),
                obligations=[],
            )
            cases.append(current)
            continue
        obligation = OBLIGATION_RE.match(line)
        if obligation and current is not None:
            current.obligations.append(obligation.group("text"))
    return cases


def parse_negative(path: Path) -> list[NegativeCase]:
    cases: list[NegativeCase] = []
    for line in path.read_text(errors="replace").splitlines():
        match = PASS_NEG_RE.match(line)
        if match:
            cases.append(
                NegativeCase(
                    name=match.group("neg"),
                    case=match.group("case"),
                    reason=match.group("reason"),
                )
            )
    return cases


def write_markdown(positive: list[PositiveCase], negative: list[NegativeCase]) -> str:
    neg_by_case: dict[str, list[NegativeCase]] = {}
    for neg in negative:
        neg_by_case.setdefault(neg.case, []).append(neg)

    lines: list[str] = [
        "# Standalone Storage Coverage",
        "",
        "Generated from `standalone_positive.log` and `standalone_negative.log`.",
        "",
        f"- positive cases: {len(positive)}",
        f"- negative cases: {len(negative)}",
        "",
        "## Positive Cases",
        "",
        "| Case | Classification | Obligations | Negative checks |",
        "|---|---|---:|---:|",
    ]

    for case in positive:
        lines.append(
            f"| `{case.name}` | {case.classification} | "
            f"{len(case.obligations)} | {len(neg_by_case.get(case.name, []))} |"
        )

    lines.extend(["", "## Details", ""])
    for case in positive:
        lines.extend([f"### `{case.name}`", "", f"Classification: {case.classification}", ""])
        lines.append("Obligations:")
        for obligation in case.obligations:
            lines.append(f"- {obligation}")
        related_neg = neg_by_case.get(case.name, [])
        if related_neg:
            lines.extend(["", "Rejected malformed witnesses:"])
            for neg in related_neg:
                lines.append(f"- `{neg.name}`: {neg.reason}")
        lines.append("")

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Summarize standalone storage validation logs.")
    parser.add_argument("positive", type=Path)
    parser.add_argument("negative", type=Path)
    parser.add_argument("--format", choices=["markdown", "json"], default="markdown")
    args = parser.parse_args()

    positive = parse_positive(args.positive)
    negative = parse_negative(args.negative)

    if args.format == "json":
        print(
            json.dumps(
                {
                    "positive": [asdict(case) for case in positive],
                    "negative": [asdict(case) for case in negative],
                },
                indent=2,
                sort_keys=True,
            )
        )
    else:
        print(write_markdown(positive, negative))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

