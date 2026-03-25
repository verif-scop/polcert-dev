#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import re
import shutil
import subprocess
import tempfile

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

BEGIN = "== Debug Extracted OpenScop ==\n"
END = "== Debug Roundtrip-Before OpenScop ==\n"


def run(cmd: list[str], cwd: pathlib.Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=cwd, text=True, capture_output=True, check=True)


def parse_scop(path: pathlib.Path) -> dict[str, list[str]]:
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
    return {"domain_meta": domain_meta, "scattering_meta": scattering_meta}


def extract_strengthened_before(case: str, work: pathlib.Path) -> pathlib.Path:
    loop_path = ROOT / "tests" / "polopt-regression" / "inputs" / f"{case}.loop"
    proc = run([str(ROOT / "polopt"), "--debug-scheduler", str(loop_path)], cwd=ROOT)
    txt = proc.stdout
    start = txt.index(BEGIN) + len(BEGIN)
    end = txt.index(END, start)
    body = txt[start:end].strip() + "\n"
    out = work / "strengthened.before.scop"
    out.write_text(body)
    return out


def extract_c_before(case: str, work: pathlib.Path) -> pathlib.Path:
    src = ROOT / "tests" / "pluto-all" / case / f"{case}.c"
    in_c = work / "in.c"
    shutil.copy2(src, in_c)
    run(["pluto", *PLUTO_FLAGS, str(in_c)], cwd=work)
    return work / "in.beforescheduling.scop"


def case_names() -> list[str]:
    inputs = ROOT / "tests" / "polopt-regression" / "inputs"
    return sorted(p.stem for p in inputs.glob("*.loop"))


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--output-json", required=True)
    ap.add_argument("--output-md", required=True)
    args = ap.parse_args()

    cases = case_names()
    if args.limit > 0:
        cases = cases[: args.limit]

    rows = []
    raw = {"cases": []}
    dom_mismatch = 0
    scat_mismatch = 0

    with tempfile.TemporaryDirectory(prefix="polcert-strengthened-before-") as td:
        base = pathlib.Path(td)
        for case in cases:
            work = base / case
            work.mkdir(parents=True, exist_ok=True)
            our_before = extract_strengthened_before(case, work)
            c_before = extract_c_before(case, work)
            our = parse_scop(our_before)
            c = parse_scop(c_before)
            dom_ok = our["domain_meta"] == c["domain_meta"]
            scat_ok = our["scattering_meta"] == c["scattering_meta"]
            if not dom_ok:
                dom_mismatch += 1
            if not scat_ok:
                scat_mismatch += 1
            raw["cases"].append({
                "case": case,
                "our_before": our,
                "c_before": c,
                "before_domain_match": dom_ok,
                "before_scattering_match": scat_ok,
            })
            rows.append(
                "| {case} | {dom} | {scat} | `{od}` | `{cd}` | `{os}` | `{cs}` |".format(
                    case=case,
                    dom="yes" if dom_ok else "no",
                    scat="yes" if scat_ok else "no",
                    od="; ".join(our["domain_meta"]),
                    cd="; ".join(c["domain_meta"]),
                    os="; ".join(our["scattering_meta"]),
                    cs="; ".join(c["scattering_meta"]),
                )
            )

    pathlib.Path(args.output_json).write_text(json.dumps(raw, indent=2, sort_keys=True) + "\n")
    pathlib.Path(args.output_md).write_text("\n".join([
        "# Strengthened Before Comparison",
        "",
        "Date: 2026-03-08",
        "",
        "Comparison method:",
        "- our path: `polopt --debug-scheduler` and slice `== Debug Extracted OpenScop ==`",
        "- c path: `tests/pluto-all/<case>/<case>.c` -> `pluto` with README flags",
        "- compare source `before.scop` only",
        "",
        f"- cases compared: `{len(cases)}`",
        f"- before domain mismatches: `{dom_mismatch}`",
        f"- before scattering mismatches: `{scat_mismatch}`",
        "",
        "| case | before domain | before scattering | our before domain | c before domain | our before scattering | c before scattering |",
        "| --- | --- | --- | --- | --- | --- | --- |",
        *rows,
        "",
    ]) + "\n")


if __name__ == "__main__":
    main()
