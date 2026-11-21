#!/usr/bin/env python3
"""Replay the miscompilations that the paper adds to the five recorded bugs.

Each case runs polopt with the historical Pluto (bug present) and with the
fixed Pluto (bug repaired). A case passes when PolCert rejects the historical
proposal and, with the fixed producer, either compiles to a program whose final
state matches the C source at 1, 4 and 8 OpenMP threads or the fixed producer
itself refuses the input.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

CASES = (
    {
        "name": "diamond-jacobi1d",
        "loop": "diamond_jacobi1d.loop",
        "c": "diamond_jacobi1d.c",
        "flags": ["--pluto-compat", "--tile", "--diamond-tile", "--intratileopt",
                  "--noprevector", "--nounrolljam", "--noparallel",
                  "--tile-sizes-file", "{inputs}/tile4.sizes"],
        "dfp": False,
    },
    {
        "name": "diamond-fdtd1d",
        "loop": "diamond_fdtd1d.loop",
        "c": "diamond_fdtd1d.c",
        "flags": ["--pluto-compat", "--tile", "--diamond-tile", "--intratileopt",
                  "--noprevector", "--nounrolljam", "--noparallel",
                  "--tile-sizes-file", "{inputs}/tile2.sizes"],
        "dfp": False,
    },
    {
        "name": "identity-tile-scalar-row",
        "loop": "scalar_phase_reverse.loop",
        "c": "scalar_phase_reverse.c",
        "flags": ["--pluto-compat", "--noprevector", "--nounrolljam",
                  "--nodiamond-tile", "--nointratileopt", "--identity", "--tile",
                  "--noparallel"],
        "dfp": False,
    },
    {
        "name": "dfp-skew",
        "loop": "dfp-skew.loop",
        "c": "dfp-skew.c",
        "flags": ["--notile"],
        "dfp": True,
    },
)

MACROS = (
    "#include <limits.h>\n#include <stdlib.h>\n#include <stdio.h>\n"
    "#define max(x,y) ((x)>(y)?(x):(y))\n#define min(x,y) ((x)<(y)?(x):(y))\n"
    "#define floord(n,d) (((n)<0)?-((-(n)+(d)-1)/(d)):(n)/(d))\n"
    "#define ceild(n,d) (((n)<0)?-((-(n))/(d)):((n)+(d)-1)/(d))\n"
)
DECLS = "  int t0,t1,t2,t3,t4,t5,t6,t7,t8,t9;\n"


def load_loop_to_c(root):
    path = root / "tools/end_to_end_c/loop_to_c.py"
    spec = importlib.util.spec_from_file_location("loop_to_c", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return path, module


def producer_wrapper(pluto, dfp, work):
    if not dfp:
        return pluto
    wrapper = work / ("dfp-" + pluto.parent.parent.name + ".sh")
    wrapper.write_text('#!/bin/bash\nexec "%s" --dfp "$@"\n' % pluto)
    wrapper.chmod(0o755)
    return wrapper


def state_check(root, case, inputs, optimized, work, loop_to_c):
    l2c_path, l2c = loop_to_c
    body = work / "opt.body.c"
    loop = work / "opt.loop"
    lines, keep = [], False
    for line in optimized.splitlines():
        if line.startswith("== Optimized Loop =="):
            keep = True
            continue
        if line.startswith("== "):
            keep = False
        if keep:
            lines.append(line)
    loop.write_text("\n".join(lines) + "\n")
    proc = subprocess.run([sys.executable, str(l2c_path), str(loop), str(body)],
                          capture_output=True, text=True)
    if proc.returncode != 0:
        return "transpile-failed"
    source = (inputs / case["c"]).read_text()
    pre, rest = source.split("#pragma scop", 1)
    _, post = rest.split("#pragma endscop", 1)
    spliced = work / "spliced.c"
    spliced.write_text(MACROS + l2c.INTEGER_HELPERS_C + pre + "{\n" + DECLS
                       + body.read_text() + "}\n" + post)
    original = work / "orig"
    candidate = work / "candidate"
    for args in (["gcc", "-O0", "-o", str(original), str(inputs / case["c"])],
                 ["gcc", "-O0", "-fopenmp", "-o", str(candidate), str(spliced), "-lm"]):
        if subprocess.run(args, capture_output=True).returncode != 0:
            return "compile-failed"
    expected = subprocess.run([str(original)], capture_output=True).stdout
    for threads in ("1", "4", "8"):
        env = dict(os.environ, OMP_NUM_THREADS=threads)
        if subprocess.run([str(candidate)], capture_output=True, env=env).stdout != expected:
            return "mismatch-%s-threads" % threads
    return "match"


def run_case(root, case, producer_label, pluto, inputs, out, loop_to_c):
    work = Path(tempfile.mkdtemp(prefix=case["name"] + "-" + producer_label + "-", dir=out))
    producer = producer_wrapper(pluto, case["dfp"], work)
    flags = [flag.format(inputs=inputs) for flag in case["flags"]]
    env = dict(os.environ, POLCERT_PLUTO=str(producer),
               COMPCERT_CONFIG=str(root / "polcert.ini"))
    command = [str(root / "polopt")] + flags + [str(inputs / case["loop"])]
    proc = subprocess.run(command, cwd=work, capture_output=True, text=True,
                          env=env, timeout=600)
    (work / "stdout.txt").write_text(proc.stdout)
    (work / "stderr.txt").write_text(proc.stderr)
    alarm = "[alarm]" in proc.stderr
    last = [line for line in proc.stderr.splitlines() if line.strip()][-1:] or [""]
    record = {"case": case["name"], "producer": producer_label,
              "command": command, "returncode": proc.returncode,
              "alarm": alarm, "last_diagnostic": last[0]}
    if proc.returncode == 0:
        record["state"] = state_check(root, case, inputs, proc.stdout, work, loop_to_c)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--historical-pluto", type=Path, required=True)
    parser.add_argument("--fixed-pluto", type=Path, required=True)
    parser.add_argument("--inputs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = args.source_root.resolve()
    inputs = args.inputs.resolve()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if shutil.which("gcc") is None:
        print("gcc is required", file=sys.stderr)
        return 2
    loop_to_c = load_loop_to_c(root)
    rows, ok = [], True
    for case in CASES:
        historical = run_case(root, case, "historical", args.historical_pluto.resolve(),
                              inputs, out, loop_to_c)
        fixed = run_case(root, case, "fixed", args.fixed_pluto.resolve(),
                         inputs, out, loop_to_c)
        rejected = historical["returncode"] != 0 and historical["alarm"]
        repaired = (fixed["returncode"] == 0 and fixed.get("state") == "match") or (
            fixed["returncode"] != 0 and "scheduler failed" in fixed["last_diagnostic"])
        row = {"case": case["name"], "historical": historical, "fixed": fixed,
               "historical_rejected": rejected, "fixed_outcome_ok": repaired}
        ok = ok and rejected and repaired
        rows.append(row)
        print(json.dumps({"case": case["name"], "historical_rejected": rejected,
                          "historical_diagnostic": historical["last_diagnostic"],
                          "fixed_returncode": fixed["returncode"],
                          "fixed_state": fixed.get("state", "-")}), flush=True)
    (out / "summary.json").write_text(json.dumps({"rows": rows, "passed": ok}, indent=2) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
