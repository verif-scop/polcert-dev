#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
POLOPT = ROOT / "polopt"
PLUTO = Path("/pluto/tool/pluto")


def run_bridge_checker(bridge: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [str(POLOPT), "--validate-iss-bridge", str(bridge)],
        capture_output=True,
        text=True,
    )
    output = proc.stdout.strip()
    if proc.stderr.strip():
        output = (output + "\n" + proc.stderr.strip()).strip()
    return proc.returncode, output


def emit_pluto_bridge(src: Path, dst: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [
            str(PLUTO),
            "--pet",
            "--iss",
            "--identity",
            "--dump-iss-bridge",
            "--silent",
            str(src),
        ],
        capture_output=True,
        text=True,
    )
    dst.write_text(proc.stdout)
    output = proc.stdout.strip()
    if proc.stderr.strip():
        output = (output + "\n" + proc.stderr.strip()).strip()
    return proc.returncode, output


def mutate_bad_cut(src: Path, dst: Path) -> None:
    text = src.read_text()
    for line in text.splitlines():
        if line.startswith("CUT "):
            payload = line[len("CUT ") :]
            coeffs, const = payload.split("|", 1)
            bad = f"CUT {coeffs}|{int(const) + 1}"
            dst.write_text(text.replace(line, bad, 1))
            return
    raise ValueError("bridge did not contain any CUT row to corrupt")


def main() -> int:
    positives = [
        Path("/pluto/test/jacobi-2d-periodic.c"),
        Path("/pluto/test/multi-stmt-periodic.c"),
        Path("/pluto/test/heat-2dp.c"),
    ]
    failures: list[str] = []

    with tempfile.TemporaryDirectory(prefix="iss-live-suite-") as tmpdir:
        tmp = Path(tmpdir)
        emitted: list[Path] = []

        for src in positives:
            bridge = tmp / f"{src.stem}.bridge.txt"
            code, output = emit_pluto_bridge(src, bridge)
            print(f"[ISS-LIVE-EMIT] {src.name}: exit={code}")
            print(output)
            if code != 0 or "VAR_ORDER" not in bridge.read_text():
                failures.append(f"bridge emission failed: {src.name}")
                continue
            emitted.append(bridge)
            code, output = run_bridge_checker(bridge)
            print(f"[ISS-LIVE-POS] {src.name}: exit={code}")
            print(output)
            if code != 0:
                failures.append(f"live positive case failed: {src.name}")

        if emitted:
            bad_bridge = tmp / "bad_cut.bridge.txt"
            mutate_bad_cut(emitted[0], bad_bridge)
            code, output = run_bridge_checker(bad_bridge)
            print(f"[ISS-LIVE-NEG] {bad_bridge.name}: exit={code}")
            print(output)
            if code == 0:
                failures.append("live negative bridge unexpectedly validated")

    if failures:
        print("[ISS-LIVE-SUITE] FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print("[ISS-LIVE-SUITE] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
