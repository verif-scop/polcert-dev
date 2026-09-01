#!/usr/bin/env python3
"""Run the test-only rejecting Pluto wrapper and retain its exact phase pair."""

from __future__ import annotations

import os
import json
from pathlib import Path
import shutil
import subprocess
import sys


def generated_output(args: list[str], suffix: str) -> tuple[Path, Path] | None:
    inputs = [Path(arg).resolve() for arg in args if arg.endswith(".scop")]
    if not inputs:
        return None
    source = inputs[-1]
    candidates = (
        source.with_name(source.name + suffix),
        Path.cwd() / (source.name + suffix),
    )
    output = next((path for path in candidates if path.is_file()), None)
    return (source, output) if output is not None else None


def main() -> int:
    base = os.environ.get("POLCERT_REJECTING_PLUTO_BASE")
    capture = os.environ.get("POLCERT_REJECTING_CAPTURE")
    label = os.environ.get("POLCERT_REJECTING_CAPTURE_LABEL")
    if not base or not capture or not label:
        print("missing rejecting-Pluto capture configuration", file=sys.stderr)
        return 74

    args = sys.argv[1:]
    proc = subprocess.run([base, *args], check=False)
    if proc.returncode != 0:
        return proc.returncode

    mode = os.environ.get("POLCERT_REJECTING_PLUTO_MODE", "tiling")
    if mode == "final-affine":
        pair = generated_output(args, ".afterscheduling.scop")
    else:
        suffix = (
            ".posttile.scop"
            if "--diamond-tile" in args or "--full-diamond-tile" in args
            else ".afterscheduling.scop"
        )
        pair = generated_output(args, suffix)
    if pair is None:
        print("cannot locate the rejected phase pair", file=sys.stderr)
        return 75

    case_dir = Path(capture) / label
    case_dir.mkdir(parents=True, exist_ok=True)
    invocation = len([path for path in case_dir.iterdir() if path.is_dir()])
    invocation_dir = case_dir / f"{invocation:02d}"
    invocation_dir.mkdir()
    source, candidate = pair
    shutil.copy2(source, invocation_dir / "before.scop")
    shutil.copy2(candidate, invocation_dir / "candidate.scop")
    (invocation_dir / "command.json").write_text(
        json.dumps(args, indent=2) + "\n", encoding="utf-8"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
