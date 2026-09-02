#!/usr/bin/env python3
"""Capture the before/after Loop programs selected by the performance search."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


OPT_MARKER = "== Optimized Loop ==\n"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def extract_optimized_loop(stdout: str) -> str:
    start = stdout.find(OPT_MARKER)
    if start < 0:
        raise RuntimeError("polopt output does not contain an optimized Loop program")
    start += len(OPT_MARKER)
    end = stdout.find("\n== ", start)
    if end < 0:
        end = len(stdout)
    return stdout[start:end].strip() + "\n"


def capture(source: Path, destination: Path, polopt: Path, jobs: int) -> None:
    config_path = source / "tests/end-to-end-generated/best_pipelines.json"
    cases_root = source / "tests/polopt-generated/cases"
    config = json.loads(config_path.read_text(encoding="utf-8"))
    pipelines = {item["name"]: item for item in config["pipelines"]}

    with tempfile.TemporaryDirectory(
        prefix="polcert-performance-programs-", dir=destination.parent
    ) as temporary:
        staged = Path(temporary) / destination.name
        staged.mkdir()

        def capture_case(item: tuple[str, str]) -> dict[str, object]:
            case, pipeline_name = item
            case_source = cases_root / case
            before_source = case_source / "input.loop"
            if not before_source.is_file():
                raise RuntimeError(f"missing input program for {case}: {before_source}")

            spec = pipelines[pipeline_name]
            source_kind = spec.get("source", "cached_default_no_iss_affine_tiling")
            before_text = before_source.read_text(encoding="utf-8")
            if source_kind == "cached_default_no_iss_affine_tiling":
                after_source = case_source / "optimized.loop"
                if not after_source.is_file():
                    raise RuntimeError(
                        f"missing cached output for {case}: {after_source}"
                    )
                after_text = after_source.read_text(encoding="utf-8")
            elif source_kind == "input":
                after_text = before_text
            elif source_kind == "polopt":
                environment = os.environ.copy()
                environment.setdefault(
                    "COMPCERT_CONFIG", str(source / "tests/pluto/polcert.ini")
                )
                command = [
                    str(polopt),
                    *spec.get("polopt_args", []),
                    str(before_source),
                ]
                result = subprocess.run(
                    command,
                    cwd=case_source,
                    env=environment,
                    text=True,
                    capture_output=True,
                    timeout=300,
                    check=False,
                )
                if result.returncode != 0:
                    raise RuntimeError(
                        f"polopt failed for {case}/{pipeline_name}:\n{result.stderr}"
                    )
                after_text = extract_optimized_loop(result.stdout)
            else:
                raise RuntimeError(
                    f"unknown output source for {case}/{pipeline_name}: {source_kind}"
                )

            case_destination = staged / case
            case_destination.mkdir()
            before_path = case_destination / "before.loop"
            after_path = case_destination / "after.loop"
            before_path.write_text(before_text, encoding="utf-8")
            after_path.write_text(after_text, encoding="utf-8")
            return {
                "case": case,
                "pipeline": pipeline_name,
                "polopt_args": spec.get("polopt_args", []),
                "source": source_kind,
                "before_sha256": sha256(before_path),
                "after_sha256": sha256(after_path),
            }

        selected = sorted(config["cases"].items())
        if len(selected) != 62:
            raise RuntimeError(f"expected 62 selected cases, found {len(selected)}")
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            records = list(executor.map(capture_case, selected))

        (staged / "manifest.json").write_text(
            json.dumps({"cases": records}, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        if destination.exists():
            shutil.rmtree(destination)
        shutil.move(staged, destination)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    parser.add_argument("--polopt", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()

    source = args.source.resolve()
    destination = args.destination.resolve()
    destination.parent.mkdir(parents=True, exist_ok=True)
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")
    capture(source, destination, args.polopt.resolve(), args.jobs)
    print(f"captured {len(list(destination.glob('*/before.loop')))} program pairs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
