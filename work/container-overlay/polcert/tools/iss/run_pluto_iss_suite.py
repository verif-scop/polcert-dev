#!/usr/bin/env python3

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "tests" / "iss-pluto-dumps"
POLOPT = ROOT / "polopt"


def run_checker(before: Path, after: Path) -> tuple[int, str]:
    proc = subprocess.run(
        [str(POLOPT), "--validate-iss-debug-dumps", str(before), str(after)],
        capture_output=True,
        text=True,
    )
    output = proc.stdout.strip()
    if proc.stderr.strip():
        output = (output + "\n" + proc.stderr.strip()).strip()
    return proc.returncode, output


def mutate_bad_halfspace(src: Path, dst: Path) -> None:
    text = src.read_text()
    if "-2i+N-1 >= 0" in text:
        text = text.replace("-2i+N-1 >= 0", "-2i+N-2 >= 0", 1)
    elif "2i-N >= 0" in text:
        text = text.replace("2i-N >= 0", "2i-N-1 >= 0", 1)
    else:
        raise ValueError("could not find a known ISS halfspace to corrupt")
    dst.write_text(text)


def mutate_bad_payload(src: Path, dst: Path) -> None:
    text = src.read_text()
    if 'a[i] = 2 * a[N - 1 - i];' in text:
        text = text.replace('a[i] = 2 * a[N - 1 - i];', 'a[i] = 3 * a[N - 1 - i];', 1)
    else:
        text = text.replace('a[i][j] = (a[i][j] + ', 'a[i][j] = (a[i][j] - ', 1)
    dst.write_text(text)


def main() -> int:
    positives = [
        ("reverse_before.txt", "reverse_after.txt"),
        ("multi_stmt_periodic_before.txt", "multi_stmt_periodic_after.txt"),
        ("jacobi_2d_periodic_before.txt", "jacobi_2d_periodic_after.txt"),
        ("heat_2dp_before.txt", "heat_2dp_after.txt"),
    ]
    failures: list[str] = []

    for before_name, after_name in positives:
        before = DATA / before_name
        after = DATA / after_name
        code, output = run_checker(before, after)
        print(f"[ISS-POS] {before_name} -> {after_name}: exit={code}")
        print(output)
        if code != 0:
            failures.append(f"positive case failed: {before_name} -> {after_name}")

    negative_fixed = DATA / "iss_name_collision.txt"
    code, output = run_checker(DATA / "reverse_before.txt", negative_fixed)
    print(f"[ISS-NEG] reverse_before.txt -> iss_name_collision.txt: exit={code}")
    print(output)
    if code == 0:
        failures.append("negative fixed fixture unexpectedly validated")

    with tempfile.TemporaryDirectory(prefix="iss-suite-") as tmpdir:
        tmp = Path(tmpdir)
        bad_halfspace = tmp / "reverse_bad_halfspace.txt"
        bad_payload = tmp / "reverse_bad_payload.txt"
        mutate_bad_halfspace(DATA / "reverse_after.txt", bad_halfspace)
        mutate_bad_payload(DATA / "reverse_after.txt", bad_payload)

        for label, after in [
            ("reverse_bad_halfspace", bad_halfspace),
            ("reverse_bad_payload", bad_payload),
        ]:
            code, output = run_checker(DATA / "reverse_before.txt", after)
            print(f"[ISS-NEG] reverse_before.txt -> {label}: exit={code}")
            print(output)
            if code == 0:
                failures.append(f"negative mutated fixture unexpectedly validated: {label}")

    if failures:
        print("[ISS-SUITE] FAIL")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print("[ISS-SUITE] OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
