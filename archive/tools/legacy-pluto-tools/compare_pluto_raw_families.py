#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import tempfile
from dataclasses import dataclass


ROOT = pathlib.Path("/polcert")
PLUTO_FLAGS = [
    "--dumpscop",
    "--nointratileopt",
    "--nodiamond-tile",
    "--noprevector",
    "--smartfuse",
    "--nounrolljam",
    "--noparallel",
    "--notile",
    "--rar",
]


def run(cmd: list[str], cwd: pathlib.Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=True)


@dataclass
class ScopSummary:
    path: pathlib.Path
    domain_meta: list[str]
    scattering_meta: list[str]


def parse_scop(path: pathlib.Path) -> ScopSummary:
    domain_meta: list[str] = []
    scattering_meta: list[str] = []
    lines = path.read_text().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line in {"DOMAIN", "SCATTERING"}:
            j = i + 1
            while j < len(lines):
                nxt = lines[j].strip()
                if nxt == "" or nxt.startswith("#"):
                    j += 1
                    continue
                if line == "DOMAIN":
                    domain_meta.append(nxt)
                else:
                    scattering_meta.append(nxt)
                break
            i = j
        i += 1
    return ScopSummary(path=path, domain_meta=domain_meta, scattering_meta=scattering_meta)


def collect_our(case: str, work: pathlib.Path) -> tuple[ScopSummary, ScopSummary]:
    loop_path = ROOT / "tests" / "polopt-regression" / "inputs" / f"{case}.loop"
    before = work / "our.before.scop"
    proc = run([str(ROOT / "polopt"), "--extract-only", str(loop_path)], cwd=ROOT)
    before.write_text(proc.stdout)
    run(["pluto", "--readscop", *PLUTO_FLAGS, str(before)], cwd=work)
    after = work / "our.before.scop.afterscheduling.scop"
    return parse_scop(before), parse_scop(after)


def collect_c(case: str, work: pathlib.Path) -> tuple[ScopSummary, ScopSummary]:
    src = ROOT / "tests" / "pluto-all" / case / f"{case}.c"
    in_c = work / "in.c"
    shutil.copy2(src, in_c)
    run(["pluto", *PLUTO_FLAGS, str(in_c)], cwd=work)
    before = work / "in.beforescheduling.scop"
    after = work / "in.afterscheduling.scop"
    return parse_scop(before), parse_scop(after)


def case_names() -> list[str]:
    inputs = ROOT / "tests" / "polopt-regression" / "inputs"
    return sorted(p.stem for p in inputs.glob("*.loop"))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-json", required=True)
    parser.add_argument("--output-md", required=True)
    parser.add_argument("--limit", type=int, default=0)
    args = parser.parse_args()

    cases = case_names()
    if args.limit > 0:
        cases = cases[: args.limit]

    raw: dict[str, object] = {"cases": []}
    rows: list[str] = []
    mismatch_before = 0
    mismatch_after = 0

    with tempfile.TemporaryDirectory(prefix="polcert-pluto-compare-") as td:
        base = pathlib.Path(td)
        for case in cases:
            work = base / case
            work.mkdir(parents=True, exist_ok=True)
            our_before, our_after = collect_our(case, work)
            c_before, c_after = collect_c(case, work)
            before_domain_match = our_before.domain_meta == c_before.domain_meta
            before_scattering_match = our_before.scattering_meta == c_before.scattering_meta
            after_scattering_match = our_after.scattering_meta == c_after.scattering_meta
            if not (before_domain_match and before_scattering_match):
                mismatch_before += 1
            if not after_scattering_match:
                mismatch_after += 1
            raw["cases"].append(
                {
                    "case": case,
                    "our_before": {
                        "domain_meta": our_before.domain_meta,
                        "scattering_meta": our_before.scattering_meta,
                    },
                    "c_before": {
                        "domain_meta": c_before.domain_meta,
                        "scattering_meta": c_before.scattering_meta,
                    },
                    "our_after": {
                        "scattering_meta": our_after.scattering_meta,
                    },
                    "c_after": {
                        "scattering_meta": c_after.scattering_meta,
                    },
                    "before_domain_match": before_domain_match,
                    "before_scattering_match": before_scattering_match,
                    "after_scattering_match": after_scattering_match,
                }
            )
            rows.append(
                "| {case} | {bd} | {bs} | {as_} | `{ob}` | `{cb}` | `{oa}` | `{ca}` |".format(
                    case=case,
                    bd="yes" if before_domain_match else "no",
                    bs="yes" if before_scattering_match else "no",
                    as_="yes" if after_scattering_match else "no",
                    ob="; ".join(our_before.scattering_meta),
                    cb="; ".join(c_before.scattering_meta),
                    oa="; ".join(our_after.scattering_meta),
                    ca="; ".join(c_after.scattering_meta),
                )
            )

    pathlib.Path(args.output_json).write_text(json.dumps(raw, indent=2, sort_keys=True) + "\n")
    pathlib.Path(args.output_md).write_text(
        "\n".join(
            [
                "# Raw Pluto Family Comparison",
                "",
                "Date: 2026-03-08",
                "",
                "Comparison method:",
                "- our path: `polopt --extract-only` -> raw `before.scop` -> `pluto --readscop` with README flags",
                "- C path: `tests/pluto-all/<case>/<case>.c` -> `pluto` with README flags",
                "- compare raw OpenScop structural signals only",
                "- do not use cross-source `polcert` as an oracle",
                "",
                f"- cases compared: `{len(cases)}`",
                f"- before mismatches (domain or scattering): `{mismatch_before}`",
                f"- after scattering mismatches: `{mismatch_after}`",
                "",
                "| case | before domain | before scattering | after scattering | our before scattering | c before scattering | our after scattering | c after scattering |",
                "| --- | --- | --- | --- | --- | --- | --- | --- |",
                *rows,
                "",
            ]
        )
        + "\n"
    )


if __name__ == "__main__":
    main()
