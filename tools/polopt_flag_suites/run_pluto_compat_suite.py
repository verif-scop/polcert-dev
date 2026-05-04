#!/usr/bin/env python3
from __future__ import annotations

import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DRIVER = ROOT / "tools" / "polopt_flag_suites" / "pluto_compat_driver.py"
POLOPT = ROOT / "polopt"


@dataclass(frozen=True)
class Check:
    name: str
    args: list[str]
    fixture: Path
    success: bool
    needle: str
    normalized: str | None = None


FLAGS = ["--tile", "--smartfuse", "--nointratileopt", "--noprevector", "--nounrolljam", "--rar"]
MATMUL = ROOT / "tests" / "polopt-generated" / "inputs" / "matmul.loop"
JACOBI_1D = ROOT / "tests" / "polopt-generated" / "inputs" / "jacobi-1d-imper.loop"
MATMUL_INIT = ROOT / "tools" / "second_level_tiling" / "fixtures" / "matmul-init.loop"


CHECKS = [
    Check("ordinary-tiled", [*FLAGS, "--nodiamond-tile", "--noparallel"], MATMUL, True, "== Optimized Loop ==", "polopt args: <default>"),
    Check(
        "affine-only",
        ["--notile", "--smartfuse", "--nointratileopt", "--nodiamond-tile", "--noprevector", "--nounrolljam", "--noparallel", "--rar"],
        MATMUL,
        True,
        "== Optimized Loop ==",
        "polopt args: --notile",
    ),
    Check("identity-notile", ["--identity", "--notile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, True, "== Optimized Loop ==", "polopt args: --identity"),
    Check("second-level", [*FLAGS, "--nodiamond-tile", "--noparallel", "--second-level-tile"], MATMUL_INIT, True, "== Optimized Loop ==", "polopt args: --second-level-tile"),
    Check("parallel", [*FLAGS, "--nodiamond-tile", "--parallel", "--innerpar"], MATMUL, True, "== Optimized Loop ==", "polopt args: --parallel"),
    Check("diamond", [*FLAGS, "--diamond-tile", "--noparallel"], JACOBI_1D, True, "== Optimized Loop ==", "polopt args: --diamond-tile"),
    Check("full-diamond", [*FLAGS, "--full-diamond-tile", "--noparallel"], JACOBI_1D, True, "== Optimized Loop ==", "polopt args: --full-diamond-tile"),
    Check("reject-bare-default", [], MATMUL, False, "Pluto enables --intratileopt by default"),
    Check("reject-diamond-parallel", [*FLAGS, "--diamond-tile", "--parallel"], JACOBI_1D, False, "--diamond-tile is not yet supported with --parallel"),
    Check("reject-diamond-iss", [*FLAGS, "--diamond-tile", "--noparallel", "--iss"], JACOBI_1D, False, "--diamond-tile is not yet supported with --iss"),
    Check("reject-diamond-second-level", [*FLAGS, "--diamond-tile", "--noparallel", "--second-level-tile"], JACOBI_1D, False, "--diamond-tile is not yet supported with --second-level-tile"),
    Check("reject-prevector", ["--tile", "--prevector", "--nodiamond-tile", "--noparallel"], MATMUL, False, "prevectorization is a Pluto codegen/post-transform effect"),
    Check("reject-unrolljam", ["--tile", "--unrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "unroll-jam is a Pluto post-codegen transform"),
    Check("reject-intratileopt", ["--tile", "--intratileopt", "--nodiamond-tile", "--noparallel"], MATMUL, False, "Pluto intra-tile schedule rewriting is not exposed"),
    Check("reject-pet", ["--pet", *FLAGS, "--nodiamond-tile", "--noparallel"], MATMUL, False, "frontend is polopt's verified loop extractor"),
    Check("reject-typedfuse", ["--tile", "--typedfuse", "--nodiamond-tile", "--noparallel"], MATMUL, False, "typed fusion depends on DFP"),
    Check("reject-bare-identity", ["--identity", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "use --identity --notile"),
    Check("reject-identity-tile", ["--identity", "--tile", "--nointratileopt", "--noprevector", "--nounrolljam", "--nodiamond-tile", "--noparallel"], MATMUL, False, "use --identity --notile"),
    Check("reject-multipar", [*FLAGS, "--parallel", "--multipar", "--nodiamond-tile"], MATMUL, False, "multi-degree Pluto parallel extraction is not exposed"),
    Check("reject-tile-notile", [*FLAGS, "--tile", "--notile", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--tile and --notile are both present"),
    Check("reject-diamond-nodiamond", [*FLAGS, "--diamond-tile", "--nodiamond-tile", "--noparallel"], MATMUL, False, "--diamond-tile/--full-diamond-tile and --nodiamond-tile are both present"),
]


def run_check(check: Check, timeout: int) -> str | None:
    cmd = [
        sys.executable,
        str(DRIVER),
        "--explain",
        "--polopt",
        str(POLOPT),
        "--timeout",
        str(timeout),
        *check.args,
        str(check.fixture),
    ]
    try:
        proc = subprocess.run(cmd, cwd=str(ROOT), text=True, capture_output=True, timeout=timeout + 5, check=False)
    except subprocess.TimeoutExpired:
        return f"{check.name}: wrapper timed out"
    output = proc.stdout + proc.stderr
    if check.success:
        if proc.returncode != 0:
            return f"{check.name}: expected success, got exit {proc.returncode}\n{output}"
        if check.needle not in output:
            return f"{check.name}: missing {check.needle!r}\n{output}"
        if check.normalized is not None and check.normalized not in output:
            return f"{check.name}: missing normalized mapping {check.normalized!r}\n{output}"
    else:
        if proc.returncode == 0:
            return f"{check.name}: expected rejection, but command succeeded\n{output}"
        if check.needle not in output:
            return f"{check.name}: missing rejection reason {check.needle!r}\n{output}"
    return None


def main(argv: list[str]) -> int:
    timeout = 30
    if argv:
        if len(argv) == 2 and argv[0] == "--timeout":
            timeout = int(argv[1])
        else:
            print("Usage: run_pluto_compat_suite.py [--timeout SECONDS]", file=sys.stderr)
            return 2

    failures = []
    if not POLOPT.exists():
        print(f"[pluto-compat-suite] missing polopt: {POLOPT}", file=sys.stderr)
        return 2
    missing = [check.fixture for check in CHECKS if not check.fixture.exists()]
    if missing:
        print("[pluto-compat-suite] missing fixtures:", file=sys.stderr)
        for path in missing:
            print(path, file=sys.stderr)
        return 2
    for check in CHECKS:
        failure = run_check(check, timeout)
        print(f"[pluto-compat-suite] {check.name}: {'PASS' if failure is None else 'FAIL'}")
        if failure is not None:
            failures.append(failure)

    if failures:
        print("[pluto-compat-suite] FAIL")
        for failure in failures:
            print(failure)
        return 1
    print(f"[pluto-compat-suite] OK ({len(CHECKS)} checks)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
