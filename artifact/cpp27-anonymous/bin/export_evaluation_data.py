#!/usr/bin/env python3
"""Export aggregate evaluation data from the PolCert artifact.

The exporter keeps raw, per-case observations and derives the compact tables
used to evaluate three questions: whether checked compilation retains requested
optimizations, how much checked compilation costs, and whether the validators
reject confirmed optimizer defects.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import math
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


PROFILE_RE = re.compile(
    r"^\[profile\]\s+([A-Za-z0-9_.-]+)\s+([0-9]+(?:\.[0-9]+)?)(s)?$"
)
TILING_ROUTE_RE = re.compile(r"^\[tiling-validation\]\s+route=([^\s]+)", re.MULTILINE)
COMPAT_RESULT_RE = re.compile(
    r"^\[pluto-compat-suite\]\s+(PASS|FAIL)\s+case=([^\s]+).*?"
    r"\scoverage=([^\s]+)\s+actual=([^\s]+)",
    re.MULTILINE,
)
ISS_BRIDGE_COUNT_RE = re.compile(r"^(BEFORE_STMTS|AFTER_STMTS|CUTS)\s+(\d+)$", re.MULTILINE)
INPUT_MARKER = "== Input Loop ==\n"
OUTPUT_MARKER = "== Optimized Loop ==\n"
PURE_PLUTO_FLAGS = [
    "--tile",
    "--smartfuse",
    "--nointratileopt",
    "--noprevector",
    "--nounrolljam",
    "--rar",
    "--nodiamond-tile",
    "--noparallel",
]
VALIDATION_STAGE_NAMES = {
    "affine_validate",
    "affine_validate_reschedule",
    "checked_tiling_validate",
}

EFFECT_FAMILY_ORDER = [
    "affine scheduling",
    "rectangular tiling",
    "two-level tiling",
    "diamond tiling",
    "parallelization",
    "loop unrolling",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def machine_metadata() -> dict[str, Any]:
    cpu_model = None
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.is_file():
        for line in cpuinfo.read_text(errors="replace").splitlines():
            if line.lower().startswith("model name") and ":" in line:
                cpu_model = line.split(":", 1)[1].strip()
                break
    memory_kib = None
    meminfo = Path("/proc/meminfo")
    if meminfo.is_file():
        for line in meminfo.read_text(errors="replace").splitlines():
            if line.startswith("MemTotal:"):
                memory_kib = int(line.split()[1])
                break
    return {
        "cpu_model": cpu_model,
        "logical_cpus": os.cpu_count(),
        "memory_kib": memory_kib,
    }


def text_or_empty(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def run_command(
    command: list[str],
    *,
    cwd: Path,
    timeout: int,
    env: dict[str, str] | None = None,
) -> dict[str, Any]:
    started = time.perf_counter()
    try:
        proc = subprocess.run(
            command,
            cwd=str(cwd),
            env=env,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
        return {
            "command": command,
            "returncode": proc.returncode,
            "timed_out": False,
            "wall_seconds": time.perf_counter() - started,
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
    except subprocess.TimeoutExpired as exc:
        return {
            "command": command,
            "returncode": 124,
            "timed_out": True,
            "wall_seconds": time.perf_counter() - started,
            "stdout": text_or_empty(exc.stdout),
            "stderr": text_or_empty(exc.stderr),
        }


def parse_profile(stderr: str) -> tuple[dict[str, float], dict[str, int]]:
    stages: dict[str, float] = {}
    metrics: dict[str, int] = {}
    for line in stderr.splitlines():
        match = PROFILE_RE.match(line.strip())
        if match is None:
            continue
        name, raw_value, seconds_suffix = match.groups()
        if seconds_suffix:
            stages[name] = float(raw_value)
        else:
            metrics[name] = int(raw_value)
    return stages, metrics


def extract_section(stdout: str, marker: str) -> str | None:
    start = stdout.find(marker)
    if start < 0:
        return None
    start += len(marker)
    end = stdout.find("\n== ", start)
    if end < 0:
        end = len(stdout)
    return stdout[start:end].strip()


def percentile(values: Iterable[float], p: float) -> float | None:
    ordered = sorted(values)
    if not ordered:
        return None
    if len(ordered) == 1:
        return ordered[0]
    position = (len(ordered) - 1) * p
    lower = math.floor(position)
    upper = math.ceil(position)
    if lower == upper:
        return ordered[lower]
    weight = position - lower
    return ordered[lower] * (1.0 - weight) + ordered[upper] * weight


def distribution(values: Iterable[float]) -> dict[str, float | int | None]:
    data = list(values)
    return {
        "count": len(data),
        "sum": sum(data) if data else None,
        "mean": statistics.fmean(data) if data else None,
        "median": statistics.median(data) if data else None,
        "p95": percentile(data, 0.95),
        "max": max(data) if data else None,
    }


def median_or_none(values: Iterable[float | None]) -> float | None:
    data = [value for value in values if value is not None]
    return statistics.median(data) if data else None


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def write_raw_log(root: Path, name: str, result: dict[str, Any]) -> None:
    target = root / name
    target.parent.mkdir(parents=True, exist_ok=True)
    Path(str(target) + ".stdout.txt").write_text(result["stdout"])
    Path(str(target) + ".stderr.txt").write_text(result["stderr"])


def load_manifest(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise SystemExit(f"evaluation manifest must be a JSON object: {path}")
    return data


def load_existing_result(path: Path) -> dict[str, Any] | None:
    if not path.is_file():
        return None
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise SystemExit(f"existing result must be a JSON object: {path}")
    return data


def select_cases(input_dir: Path, requested: list[str]) -> list[Path]:
    if requested:
        cases = []
        for name in requested:
            filename = name if name.endswith(".loop") else f"{name}.loop"
            path = input_dir / filename
            if not path.is_file():
                raise SystemExit(f"unknown timing case: {path}")
            cases.append(path)
        return sorted(cases)
    return sorted(input_dir.glob("*.loop"))


def polcert_environment(source_root: Path) -> dict[str, str]:
    env = os.environ.copy()
    env.setdefault("COMPCERT_CONFIG", str(source_root / "tests/pluto/polcert.ini"))
    return env


def find_c_source(source_root: Path, pluto_test_dir: Path, case: str) -> Path | None:
    candidates = [
        source_root / "tests/pluto-all" / case / f"{case}.c",
        pluto_test_dir / f"{case}.c",
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    return None


def profile_polcert_case(
    polopt: Path,
    source_root: Path,
    loop_input: Path,
    repeat: int,
    timeout: int,
    raw_root: Path,
) -> dict[str, Any]:
    command = [str(polopt), "--profile-stages", str(loop_input)]
    result = run_command(
        command,
        cwd=source_root,
        timeout=timeout,
        env=polcert_environment(source_root),
    )
    stages, metrics = parse_profile(result["stderr"])
    total = stages.get("total")
    optimizer = stages.get("pluto_phase_pipeline")
    validation = sum(stages.get(name, 0.0) for name in VALIDATION_STAGE_NAMES)
    checked_remainder = (
        total - optimizer if total is not None and optimizer is not None else None
    )
    status = (
        "timeout"
        if result["timed_out"]
        else "ok"
        if result["returncode"] == 0 and total is not None
        else "error"
    )
    write_raw_log(raw_root, f"timing/{loop_input.stem}.repeat-{repeat}", result)
    return {
        "case": loop_input.stem,
        "repeat": repeat,
        "status": status,
        "returncode": result["returncode"],
        "timed_out": result["timed_out"],
        "profile_harness_wall_seconds": result["wall_seconds"],
        "optimizer_seconds": optimizer,
        "validation_seconds": validation if total is not None else None,
        "checked_remainder_seconds": checked_remainder,
        "profile_total_seconds": total,
        "stages": stages,
        "metrics": metrics,
    }


def measure_polcert_wall(
    polopt: Path,
    source_root: Path,
    loop_input: Path,
    repeat: int,
    timeout: int,
    raw_root: Path,
) -> dict[str, Any]:
    result = run_command(
        [str(polopt), str(loop_input)],
        cwd=source_root,
        timeout=timeout,
        env=polcert_environment(source_root),
    )
    write_raw_log(raw_root, f"polcert-wall/{loop_input.stem}.repeat-{repeat}", result)
    return {
        "status": (
            "timeout"
            if result["timed_out"]
            else "ok"
            if result["returncode"] == 0 and OUTPUT_MARKER.strip() in result["stdout"]
            else "error"
        ),
        "returncode": result["returncode"],
        "timed_out": result["timed_out"],
        "wall_seconds": result["wall_seconds"],
    }


def run_pure_pluto_case(
    polycc: Path,
    source: Path | None,
    case: str,
    repeat: int,
    timeout: int,
    raw_root: Path,
) -> dict[str, Any]:
    if source is None:
        return {
            "case": case,
            "repeat": repeat,
            "status": "missing-source",
            "returncode": None,
            "timed_out": False,
            "process_wall_seconds": None,
            "source": None,
        }
    with tempfile.TemporaryDirectory(prefix=f"pure-pluto-{case}-") as tmp:
        work = Path(tmp)
        local_source = work / source.name
        shutil.copy2(source, local_source)
        command = [str(polycc), *PURE_PLUTO_FLAGS, local_source.name]
        result = run_command(command, cwd=work, timeout=timeout)
        generated = work / f"{local_source.stem}.pluto.c"
        status = (
            "timeout"
            if result["timed_out"]
            else "ok"
            if result["returncode"] == 0 and generated.is_file()
            else "error"
        )
        write_raw_log(raw_root, f"pure-pluto/{case}.repeat-{repeat}", result)
        return {
            "case": case,
            "repeat": repeat,
            "status": status,
            "returncode": result["returncode"],
            "timed_out": result["timed_out"],
            "process_wall_seconds": result["wall_seconds"],
            "source": str(source),
            "generated": generated.is_file(),
        }


def summarize_timing_runs(
    polcert_runs: list[dict[str, Any]], pure_runs: list[dict[str, Any]]
) -> dict[str, Any]:
    case_names = sorted({row["case"] for row in polcert_runs})
    case_rows: list[dict[str, Any]] = []
    for name in case_names:
        runs = [row for row in polcert_runs if row["case"] == name and row["status"] == "ok"]
        pure = [row for row in pure_runs if row["case"] == name and row["status"] == "ok"]
        stage_names = sorted({stage for row in runs for stage in row["stages"]})
        median_stages = {
            stage: median_or_none(row["stages"].get(stage) for row in runs)
            for stage in stage_names
        }
        total = median_or_none(row["profile_total_seconds"] for row in runs)
        optimizer = median_or_none(row["optimizer_seconds"] for row in runs)
        remainder = median_or_none(row["checked_remainder_seconds"] for row in runs)
        validation = median_or_none(row["validation_seconds"] for row in runs)
        nonoptimizer_stages = {
            key: value
            for key, value in median_stages.items()
            if key not in {"total", "pluto_phase_pipeline"} and value is not None
        }
        dominant_stage = max(nonoptimizer_stages, key=nonoptimizer_stages.get) if nonoptimizer_stages else None
        polcert_wall = median_or_none(row.get("polcert_wall_seconds") for row in runs)
        pure_pluto_wall = median_or_none(row["process_wall_seconds"] for row in pure)
        case_rows.append(
            {
                "case": name,
                "successful_repeats": len(runs),
                "profile_total_seconds": total,
                "optimizer_seconds": optimizer,
                "validation_seconds": validation,
                "checked_remainder_seconds": remainder,
                "polcert_wall_seconds": polcert_wall,
                "profile_harness_wall_seconds": median_or_none(
                    row.get("profile_harness_wall_seconds") for row in runs
                ),
                "pure_pluto_wall_seconds": pure_pluto_wall,
                "polcert_minus_pure_pluto_wall_seconds": (
                    polcert_wall - pure_pluto_wall
                    if polcert_wall is not None and pure_pluto_wall is not None
                    else None
                ),
                "profile_to_optimizer_ratio": (
                    total / optimizer if total is not None and optimizer not in (None, 0.0) else None
                ),
                "dominant_nonoptimizer_stage": dominant_stage,
                "dominant_nonoptimizer_seconds": nonoptimizer_stages.get(dominant_stage) if dominant_stage else None,
                "stages": median_stages,
            }
        )

    def values(field: str) -> list[float]:
        return [row[field] for row in case_rows if row[field] is not None]

    paired = [
        row
        for row in case_rows
        if row["profile_total_seconds"] is not None and row["optimizer_seconds"] not in (None, 0.0)
    ]
    sum_profile = sum(row["profile_total_seconds"] for row in paired)
    sum_optimizer = sum(row["optimizer_seconds"] for row in paired)
    aggregate_ratio = sum_profile / sum_optimizer if sum_optimizer else None
    wall_paired = [
        row
        for row in case_rows
        if row["polcert_wall_seconds"] is not None
        and row["pure_pluto_wall_seconds"] not in (None, 0.0)
    ]
    sum_polcert_wall = sum(row["polcert_wall_seconds"] for row in wall_paired)
    sum_pure_wall = sum(row["pure_pluto_wall_seconds"] for row in wall_paired)
    outliers = sorted(
        [row for row in case_rows if row["checked_remainder_seconds"] is not None],
        key=lambda row: row["checked_remainder_seconds"],
        reverse=True,
    )[:5]
    return {
        "per_case": case_rows,
        "aggregate": {
            "requested_cases": len(case_names),
            "successful_cases": sum(row["successful_repeats"] > 0 for row in case_rows),
            "requested_runs": len(polcert_runs),
            "successful_runs": sum(row["status"] == "ok" for row in polcert_runs),
            "pure_pluto_requested_runs": len(pure_runs),
            "pure_pluto_successful_runs": sum(row["status"] == "ok" for row in pure_runs),
            "cases_with_optimizer_timing": len(paired),
            "profile_total_seconds": distribution(values("profile_total_seconds")),
            "optimizer_seconds": distribution(values("optimizer_seconds")),
            "validation_seconds": distribution(values("validation_seconds")),
            "checked_remainder_seconds": distribution(values("checked_remainder_seconds")),
            "polcert_wall_seconds": distribution(values("polcert_wall_seconds")),
            "profile_harness_wall_seconds": distribution(values("profile_harness_wall_seconds")),
            "pure_pluto_wall_seconds": distribution(values("pure_pluto_wall_seconds")),
            "polcert_minus_pure_pluto_wall_seconds": distribution(
                values("polcert_minus_pure_pluto_wall_seconds")
            ),
            "profile_to_optimizer_ratio": distribution(values("profile_to_optimizer_ratio")),
            "checked_pipeline_to_optimizer_ratio_of_sums": aggregate_ratio,
            "polcert_to_pure_pluto_wall_ratio_of_sums": (
                sum_polcert_wall / sum_pure_wall if sum_pure_wall else None
            ),
            "checked_remainder_sum_seconds": sum_profile - sum_optimizer if paired else None,
        },
        "outliers": outliers,
    }


def run_timing(
    args: argparse.Namespace,
    manifest: dict[str, Any],
    output_root: Path,
) -> dict[str, Any]:
    source_root = args.source_root
    benchmark = manifest["benchmark"]
    input_dir = source_root / benchmark["input_dir"]
    cases = select_cases(input_dir, args.cases)
    if not args.cases and len(cases) != benchmark["expected_cases"]:
        raise SystemExit(
            f"expected {benchmark['expected_cases']} benchmark cases, found {len(cases)}"
        )
    raw_root = output_root / "raw"
    existing_timing = load_existing_result(output_root / "timing-results.json")
    if (
        args.reuse_profile_results
        or args.summarize_existing_timing
        or args.repair_failed_profiles
    ):
        if existing_timing is None:
            raise SystemExit("reusing timing data requires an existing timing-results.json")
        polcert_runs = existing_timing.get("runs", [])
        pure_runs = existing_timing.get("pure_pluto_runs", [])
        expected = {(case.stem, repeat) for repeat in range(1, args.repeats + 1) for case in cases}
        actual = {(row.get("case"), row.get("repeat")) for row in polcert_runs}
        if expected != actual:
            raise SystemExit(
                "existing profile results do not match the requested cases and repetitions"
            )
    else:
        polcert_runs = []
        pure_runs = []
    pluto_test_dir = args.pluto_test_dir

    if args.warmups and not (
        args.reuse_profile_results
        or args.summarize_existing_timing
        or args.repair_failed_profiles
    ):
        warmup = next((case for case in cases if case.stem == "matmul"), cases[0])
        for index in range(args.warmups):
            print(f"[timing] warmup {index + 1}/{args.warmups}: {warmup.stem}", flush=True)
            profile_polcert_case(
                args.polopt, source_root, warmup, -(index + 1), args.timeout_seconds, raw_root
            )

    if args.repair_failed_profiles:
        for index, old_row in enumerate(polcert_runs):
            if old_row["status"] == "ok":
                continue
            loop_input = input_dir / f"{old_row['case']}.loop"
            print(
                f"[timing] repair: {old_row['case']} repeat={old_row['repeat']}",
                flush=True,
            )
            replacement = profile_polcert_case(
                args.polopt,
                source_root,
                loop_input,
                old_row["repeat"],
                args.timeout_seconds,
                raw_root,
            )
            replacement["polcert_wall_seconds"] = old_row.get("polcert_wall_seconds")
            replacement["polcert_wall_status"] = old_row.get("polcert_wall_status")
            if replacement["status"] != "ok":
                raise SystemExit(
                    f"profile repair failed: {old_row['case']} repeat={old_row['repeat']}"
                )
            polcert_runs[index] = replacement
    elif not args.summarize_existing_timing:
        total_runs = len(cases) * args.repeats
        run_index = 0
        for repeat in range(1, args.repeats + 1):
            for loop_input in cases:
                run_index += 1
                print(
                    f"[timing] {run_index}/{total_runs}: {loop_input.stem} repeat={repeat}",
                    flush=True,
                )
                if args.reuse_profile_results:
                    row = next(
                        row
                        for row in polcert_runs
                        if row["case"] == loop_input.stem and row["repeat"] == repeat
                    )
                    if "profile_harness_wall_seconds" not in row and "process_wall_seconds" in row:
                        row["profile_harness_wall_seconds"] = row.pop("process_wall_seconds")
                else:
                    row = profile_polcert_case(
                        args.polopt,
                        source_root,
                        loop_input,
                        repeat,
                        args.timeout_seconds,
                        raw_root,
                    )
                    polcert_runs.append(row)
                wall = measure_polcert_wall(
                    args.polopt,
                    source_root,
                    loop_input,
                    repeat,
                    args.timeout_seconds,
                    raw_root,
                )
                row["polcert_wall_seconds"] = wall["wall_seconds"]
                row["polcert_wall_status"] = wall["status"]
                if wall["status"] != "ok":
                    row["status"] = wall["status"]
                if args.run_pure_pluto and not args.reuse_profile_results:
                    c_source = find_c_source(source_root, pluto_test_dir, loop_input.stem)
                    pure_runs.append(
                        run_pure_pluto_case(
                            args.polycc,
                            c_source,
                            loop_input.stem,
                            repeat,
                            args.timeout_seconds,
                            raw_root,
                        )
                    )

    summary = summarize_timing_runs(polcert_runs, pure_runs)
    payload = {
        "method": {
            "repeats": args.repeats,
            "warmups": args.warmups,
            "per_case_estimator": "median",
            "optimizer_baseline": "pluto_phase_pipeline measured inside the same polopt invocation",
            "validation_time": "sum of affine_validate, affine_validate_reschedule, and checked_tiling_validate",
            "checked_remainder": "profile total minus pluto_phase_pipeline; includes extraction, validation, normalization, code generation, and cleanup",
            "pure_pluto_reference": "polycc process wall time on the matching C source; includes a different frontend and code generator and is reported separately",
            "polcert_wall_time": "a separate uninstrumented polopt invocation; the profiling harness itself compiles twice and is not used as PolCert wall time",
        },
        "runs": polcert_runs,
        "pure_pluto_runs": pure_runs,
        **summary,
    }
    write_json(output_root / "timing-results.json", payload)
    write_csv(
        output_root / "timing-runs.csv",
        polcert_runs,
        [
            "case",
            "repeat",
            "status",
            "returncode",
            "timed_out",
            "optimizer_seconds",
            "validation_seconds",
            "checked_remainder_seconds",
            "profile_total_seconds",
            "profile_harness_wall_seconds",
            "polcert_wall_seconds",
            "polcert_wall_status",
        ],
    )
    write_csv(
        output_root / "timing-cases.csv",
        payload["per_case"],
        [
            "case",
            "successful_repeats",
            "optimizer_seconds",
            "validation_seconds",
            "checked_remainder_seconds",
            "profile_total_seconds",
            "polcert_wall_seconds",
            "profile_harness_wall_seconds",
            "pure_pluto_wall_seconds",
            "polcert_minus_pure_pluto_wall_seconds",
            "profile_to_optimizer_ratio",
            "dominant_nonoptimizer_stage",
            "dominant_nonoptimizer_seconds",
        ],
    )
    return payload


def classify_default_case(result: dict[str, Any], case: str) -> dict[str, Any]:
    source_loop = extract_section(result["stdout"], INPUT_MARKER)
    optimized_loop = extract_section(result["stdout"], OUTPUT_MARKER)
    accepted = result["returncode"] == 0 and optimized_loop is not None
    changed = accepted and source_loop is not None and source_loop != optimized_loop
    route_match = TILING_ROUTE_RE.search(result["stdout"] + "\n" + result["stderr"])
    status = (
        "timeout"
        if result["timed_out"]
        else "accepted-changed"
        if changed
        else "accepted-noop"
        if accepted
        else "rejected"
    )
    return {
        "case": case,
        "status": status,
        "accepted": accepted,
        "changed": changed,
        "returncode": result["returncode"],
        "wall_seconds": result["wall_seconds"],
        "tiling_route": route_match.group(1) if route_match else None,
    }


def load_compatibility_suite(source_root: Path) -> Any:
    script = source_root / "tools/polopt_flag_suites/run_pluto_compat_suite.py"
    suite_dir = str(script.parent)
    sys.path.insert(0, suite_dir)
    try:
        spec = importlib.util.spec_from_file_location("polcert_eval_compat_suite", script)
        if spec is None or spec.loader is None:
            raise SystemExit(f"cannot import compatibility suite: {script}")
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        return module
    finally:
        sys.path.remove(suite_dir)


def check_has_arg(check: Any, *args: str) -> bool:
    return any(arg in check.args for arg in args)


def check_has_effect_text(check: Any, text: str) -> bool:
    return any(text in needle for needle in check.effect_needles)


def check_has_tiling_marker(check: Any) -> bool:
    markers = [*check.effect_needles, *(check.second_level_markers or ())]
    return any(
        re.search(r"(?:^|[^A-Za-z])(8|16|32|63|64|256|1024|2048) \*|/ (8|16|32|256)", marker)
        for marker in markers
    )


def check_has_diamond_marker(check: Any) -> bool:
    return any(
        marker in {"i4 + (-1 * i5)", "(-2 * i11)"}
        for marker in check.effect_needles
    )


def effect_families(check: Any) -> list[str]:
    families = []
    parallel_effect = check_has_effect_text(check, "parallel for")
    vector_effect = check_has_effect_text(check, "vector for")
    if (
        not check.native
        and check_has_arg(check, "--notile")
        and not check_has_arg(check, "--identity", "--unrolljam", "--const-unroll")
        and not parallel_effect
        and not vector_effect
    ):
        families.append("affine scheduling")
    if (
        not check.native
        and check_has_arg(check, "--tile")
        and not check_has_arg(check, "--diamond-tile", "--full-diamond-tile")
        and check_has_tiling_marker(check)
    ):
        families.append("rectangular tiling")
    if (
        not check.native
        and check_has_arg(check, "--second-level-tile")
        and check_has_tiling_marker(check)
    ):
        families.append("two-level tiling")
    if (
        not check.native
        and check_has_arg(check, "--diamond-tile", "--full-diamond-tile")
        and check_has_diamond_marker(check)
    ):
        families.append("diamond tiling")
    if not check.native and parallel_effect:
        families.append("parallelization")
    if check_has_arg(check, "--unrolljam", "--const-unroll"):
        families.append("loop unrolling")
    return families


def run_compatibility_effect_grid(
    source_root: Path,
    timeout: int,
    raw_root: Path,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    suite = load_compatibility_suite(source_root)
    checks = {
        check.name: check
        for check in suite.active_checks()
        if check.success and suite.effect_contract_count(check) > 0
    }
    script = source_root / "tools/polopt_flag_suites/run_pluto_compat_suite.py"
    result = run_command(
        [sys.executable, str(script), "--timeout", str(timeout)],
        cwd=source_root,
        timeout=timeout * max(4, len(suite.active_checks())),
    )
    write_raw_log(raw_root, "effects/pluto-compat-full", result)
    if result["returncode"] != 0 or result["timed_out"]:
        raise SystemExit(
            "the full Pluto compatibility suite failed; see "
            f"{raw_root / 'effects/pluto-compat-full.log'}"
        )
    suite_results = {
        match.group(2): {
            "passed": match.group(1) == "PASS",
            "coverage": match.group(3),
            "actual": match.group(4),
            "line": match.group(0),
        }
        for match in COMPAT_RESULT_RE.finditer(result["stdout"])
    }

    effect_rows = []
    for name, check in checks.items():
        families = effect_families(check)
        if not families:
            continue
        observed = suite_results.get(name)
        suite_passed = observed is not None and observed["passed"]
        retained = (
            suite_passed
            and observed["coverage"] == "effect"
            and "effect-contracts-matched" in observed["actual"]
        )
        produced = True
        for family in families:
            row_producer = "PolCert postpass" if family == "loop unrolling" else "Pluto"
            effect_rows.append(
                {
                    "family": family,
                    "producer": row_producer,
                    "name": name,
                    "fixture": check.fixture.stem,
                    "variant": " ".join(check.args),
                    "status": (
                        "accepted-effect-retained"
                        if produced and retained
                        else "producer-effect-not-retained"
                        if produced
                        else "producer-effect-not-observed"
                    ),
                    "candidate_produced": produced,
                    "accepted": suite_passed,
                    "checked_effect_observed": produced and retained,
                    "returncode": result["returncode"],
                    "timed_out": result["timed_out"],
                    "wall_seconds": result["wall_seconds"],
                    "suite_line": observed["line"] if observed else "",
                    "diagnostic_tail": "",
                }
            )

    group_summaries = []
    for family in EFFECT_FAMILY_ORDER:
        rows = [row for row in effect_rows if row["family"] == family]
        if not rows:
            continue
        producer = "PolCert postpass" if family == "loop unrolling" else "Pluto"
        produced = sum(row["candidate_produced"] for row in rows)
        retained = sum(row["checked_effect_observed"] for row in rows)
        group_summaries.append(
            {
                "family": family,
                "producer": producer,
                "positive_configurations": len(rows),
                "unique_fixtures": len({row["fixture"] for row in rows}),
                "candidates_produced": produced,
                "accepted": sum(row["accepted"] for row in rows),
                "checked_effects_observed": retained,
                "rejected_or_failed": produced - retained,
            }
        )
    return effect_rows, group_summaries


def parse_iss_bridge_counts(text: str) -> dict[str, int]:
    return {match.group(1): int(match.group(2)) for match in ISS_BRIDGE_COUNT_RE.finditer(text)}


def run_live_iss_grid(
    args: argparse.Namespace,
    manifest: dict[str, Any],
    raw_root: Path,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    iss = manifest["iss_live_grid"]
    converter = args.source_root / "tools/iss/pluto_iss_check.py"
    rows = []
    for input_name in iss["inputs"]:
        source = args.pluto_test_dir / input_name
        for config in iss["configurations"]:
            name = f"{source.stem}-{config['name']}"
            print(f"[completeness] index-set splitting: {name}", flush=True)
            pluto_result = run_command(
                [
                    str(args.pluto),
                    "--pet",
                    "--iss",
                    *config["args"],
                    "--moredebug",
                    "--silent",
                    str(source),
                ],
                cwd=args.source_root,
                timeout=args.timeout_seconds,
            )
            write_raw_log(raw_root, f"effects/index-set-splitting/{name}.pluto", pluto_result)
            with tempfile.TemporaryDirectory(prefix="polcert-eval-iss-") as tmp:
                combined = Path(tmp) / "combined.txt"
                bridge = Path(tmp) / "bridge.txt"
                combined.write_text(pluto_result["stdout"])
                bridge_result = run_command(
                    [sys.executable, str(converter), "--emit-bridge-from-combined", str(combined)],
                    cwd=args.source_root,
                    timeout=args.timeout_seconds,
                )
                bridge.write_text(bridge_result["stdout"])
                write_raw_log(raw_root, f"effects/index-set-splitting/{name}.bridge", bridge_result)
                counts = parse_iss_bridge_counts(bridge_result["stdout"])
                produced = (
                    pluto_result["returncode"] == 0
                    and bridge_result["returncode"] == 0
                    and counts.get("CUTS", 0) > 0
                    and counts.get("AFTER_STMTS", 0) > counts.get("BEFORE_STMTS", 0)
                )
                validation_result = run_command(
                    [str(args.polopt), "--validate-iss-bridge", str(bridge)],
                    cwd=args.source_root,
                    timeout=args.timeout_seconds,
                    env=polcert_environment(args.source_root),
                )
                write_raw_log(raw_root, f"effects/index-set-splitting/{name}.validate", validation_result)
                retained = produced and validation_result["returncode"] == 0
            rows.append(
                {
                    "family": "index-set splitting",
                    "producer": "Pluto",
                    "name": name,
                    "fixture": source.stem,
                    "variant": " ".join(config["args"]),
                    "status": (
                        "accepted-effect-retained"
                        if retained
                        else "producer-effect-not-retained"
                        if produced
                        else "producer-effect-not-observed"
                    ),
                    "candidate_produced": produced,
                    "accepted": validation_result["returncode"] == 0,
                    "checked_effect_observed": retained,
                    "returncode": validation_result["returncode"],
                    "timed_out": (
                        pluto_result["timed_out"]
                        or bridge_result["timed_out"]
                        or validation_result["timed_out"]
                    ),
                    "wall_seconds": (
                        pluto_result["wall_seconds"]
                        + bridge_result["wall_seconds"]
                        + validation_result["wall_seconds"]
                    ),
                    "suite_line": "",
                    "diagnostic_tail": "",
                }
            )
    produced = sum(row["candidate_produced"] for row in rows)
    retained = sum(row["checked_effect_observed"] for row in rows)
    return rows, {
        "family": "index-set splitting",
        "producer": "Pluto",
        "positive_configurations": len(rows),
        "unique_fixtures": len({row["fixture"] for row in rows}),
        "candidates_produced": produced,
        "accepted": sum(row["accepted"] for row in rows),
        "checked_effects_observed": retained,
        "rejected_or_failed": produced - retained,
    }


def run_completeness(
    args: argparse.Namespace,
    manifest: dict[str, Any],
    output_root: Path,
) -> dict[str, Any]:
    source_root = args.source_root
    benchmark = manifest["benchmark"]
    input_dir = source_root / benchmark["input_dir"]
    cases = select_cases(input_dir, args.cases)
    if not args.cases and len(cases) != benchmark["expected_cases"]:
        raise SystemExit(
            f"expected {benchmark['expected_cases']} benchmark cases, found {len(cases)}"
        )
    raw_root = output_root / "raw"
    corpus_rows: list[dict[str, Any]] = []
    for index, loop_input in enumerate(cases, start=1):
        print(f"[completeness] corpus {index}/{len(cases)}: {loop_input.stem}", flush=True)
        result = run_command(
            [str(args.polopt), "--dump-input", str(loop_input)],
            cwd=source_root,
            timeout=args.timeout_seconds,
            env=polcert_environment(source_root),
        )
        write_raw_log(raw_root, f"corpus/{loop_input.stem}", result)
        corpus_rows.append(classify_default_case(result, loop_input.stem))

    print("[completeness] full optimization-effect grid", flush=True)
    effect_rows, group_summaries = run_compatibility_effect_grid(
        source_root, args.timeout_seconds, raw_root
    )
    if not args.cases:
        iss_rows, iss_summary = run_live_iss_grid(args, manifest, raw_root)
        effect_rows.extend(iss_rows)
        group_summaries.insert(1, iss_summary)

    aggregate = {
        "corpus_cases": len(corpus_rows),
        "accepted": sum(row["accepted"] for row in corpus_rows),
        "changed": sum(row["changed"] for row in corpus_rows),
        "accepted_noop": sum(row["accepted"] and not row["changed"] for row in corpus_rows),
        "rejected_or_failed": sum(not row["accepted"] for row in corpus_rows),
    }
    payload = {
        "benchmark": benchmark,
        "method": {
            "corpus": "default checked affine-scheduling and tiling route over every loop input",
            "changed": "the pretty-printed checked result differs from the pretty-printed source loop",
            "positive_configurations": "all successful compatibility-suite configurations with an explicit structural effect contract; rows may overlap when one configuration exercises several transformations",
            "candidate_produced": "the input/configuration pair has an explicit structural effect contract; for index-set splitting, the live Pluto bridge must contain a nonempty cut set and more target statements",
            "checked_effect_observed": "the checked final output satisfied the transformation-specific structural contract; successful no-ops are not counted",
            "comparison_scope": "the comparison follows each producer proposal into the checked final output; it does not compare raw generated code because Pluto and PolCert use different code generators",
        },
        "corpus": corpus_rows,
        "corpus_aggregate": aggregate,
        "effects": effect_rows,
        "effect_groups": group_summaries,
    }
    write_json(output_root / "completeness-results.json", payload)
    write_csv(
        output_root / "completeness-corpus.csv",
        corpus_rows,
        ["case", "status", "accepted", "changed", "returncode", "wall_seconds", "tiling_route"],
    )
    write_csv(
        output_root / "completeness-effects.csv",
        effect_rows,
        [
            "family",
            "producer",
            "name",
            "fixture",
            "variant",
            "status",
            "candidate_produced",
            "accepted",
            "checked_effect_observed",
            "returncode",
            "timed_out",
            "wall_seconds",
        ],
    )
    return payload


def run_bug_cases(
    args: argparse.Namespace,
    manifest: dict[str, Any],
    output_root: Path,
) -> dict[str, Any]:
    rows = []
    raw_root = output_root / "raw"
    for index, case in enumerate(manifest["miscompilation_cases"], start=1):
        print(
            f"[case-studies] {index}/{len(manifest['miscompilation_cases'])}: {case['name']}",
            flush=True,
        )
        result = run_command(
            [sys.executable, str(args.source_root / case["script"])],
            cwd=args.source_root,
            timeout=args.bug_timeout_seconds,
            env=polcert_environment(args.source_root),
        )
        combined = result["stdout"] + "\n" + result["stderr"]
        passed = result["returncode"] == 0 and "FAIL:" not in combined
        row = {
            **case,
            "status": "pass" if passed else "fail",
            "rejection_confirmed": passed,
            "returncode": result["returncode"],
            "timed_out": result["timed_out"],
            "wall_seconds": result["wall_seconds"],
            "evidence_lines": [
                line
                for line in combined.splitlines()
                if "expected=" in line or line.endswith(" OK") or " OK (" in line
            ][-8:],
        }
        rows.append(row)
        write_raw_log(raw_root, f"bugs/{case['name']}", result)
    payload = {
        "cases": rows,
        "aggregate": {
            "confirmed_miscompilations": len(rows),
            "rejections_confirmed": sum(row["rejection_confirmed"] for row in rows),
            "failed": sum(not row["rejection_confirmed"] for row in rows),
        },
    }
    write_json(output_root / "case-studies.json", payload)
    write_csv(
        output_root / "case-studies.csv",
        rows,
        [
            "name",
            "target",
            "expected",
            "status",
            "rejection_confirmed",
            "returncode",
            "timed_out",
            "wall_seconds",
        ],
    )
    return payload


def milliseconds(value: float | None) -> str:
    return "--" if value is None else f"{1000.0 * value:.1f}"


def ratio(value: float | None) -> str:
    return "--" if value is None else f"{value:.2f}x"


def render_summary(
    metadata: dict[str, Any],
    completeness: dict[str, Any] | None,
    timing: dict[str, Any] | None,
    bugs: dict[str, Any] | None,
) -> str:
    lines = [
        "# PolCert Evaluation Summary",
        "",
        f"Generated: `{metadata['generated_at']}`",
        "",
    ]
    if completeness is not None:
        corpus = completeness["corpus_aggregate"]
        lines.extend(
            [
                "## Optimization retention",
                "",
                "| Corpus cases | Accepted | Changed | Accepted no-op | Rejected/failed |",
                "| ---: | ---: | ---: | ---: | ---: |",
                f"| {corpus['corpus_cases']} | {corpus['accepted']} | {corpus['changed']} | {corpus['accepted_noop']} | {corpus['rejected_or_failed']} |",
                "",
                "A no-op is reported separately and is not counted as a retained optimization effect.",
                "",
                "| Transformation family | Producer | Inputs | Producer effects | Retained by PolOpt |",
                "| --- | --- | ---: | ---: | ---: |",
            ]
        )
        for row in completeness["effect_groups"]:
            lines.append(
                f"| {row['family']} | {row['producer']} | {row['unique_fixtures']} | {row['candidates_produced']} | {row['checked_effects_observed']} |"
            )
        lines.extend(
            [
                "",
                "Each count is an input/configuration pair with a declared structural effect; "
                "rows overlap when one configuration exercises several transformations. "
                "The retained column checks the corresponding effect after validation.",
                "",
            ]
        )

    if timing is not None:
        aggregate = timing["aggregate"]
        lines.extend(
            [
                "## Compilation time",
                "",
                "Each entry below is computed from the per-case median; the columns then aggregate across cases.",
                "",
                "| Metric | Mean (ms) | Median (ms) | P95 (ms) | Max (ms) |",
                "| --- | ---: | ---: | ---: | ---: |",
            ]
        )
        timing_rows = [
            ("Pluto proposal phase", "optimizer_seconds"),
            ("Validators only", "validation_seconds"),
            ("Checked pipeline excluding Pluto", "checked_remainder_seconds"),
            ("Checked pipeline total", "profile_total_seconds"),
            ("PolCert process wall time", "polcert_wall_seconds"),
            ("Pure Pluto `polycc` wall time", "pure_pluto_wall_seconds"),
            ("PolCert minus pure Pluto wall time", "polcert_minus_pure_pluto_wall_seconds"),
        ]
        for label, key in timing_rows:
            stats = aggregate[key]
            lines.append(
                f"| {label} | {milliseconds(stats['mean'])} | {milliseconds(stats['median'])} | {milliseconds(stats['p95'])} | {milliseconds(stats['max'])} |"
            )
        lines.extend(
            [
                "",
                f"Across the {aggregate['cases_with_optimizer_timing']} cases with a Pluto phase, the ratio of summed checked-pipeline time to summed Pluto-proposal time is **{ratio(aggregate['checked_pipeline_to_optimizer_ratio_of_sums'])}**.",
                f"The ratio of summed PolCert wall time to summed pure-Pluto `polycc` wall time is **{ratio(aggregate['polcert_to_pure_pluto_wall_ratio_of_sums'])}**.",
                "",
                "The internal Pluto-phase measurement isolates proposal generation within PolCert. The separate `polycc` wall time includes a C frontend and a different code generator, so it is an end-to-end reference rather than an apples-to-apples overhead ratio.",
                "",
                "Largest checked-pipeline remainders:",
                "",
                "| Case | Remainder (ms) | Dominant stage | Stage time (ms) |",
                "| --- | ---: | --- | ---: |",
            ]
        )
        for row in timing["outliers"]:
            lines.append(
                f"| {row['case']} | {milliseconds(row['checked_remainder_seconds'])} | {row['dominant_nonoptimizer_stage'] or '--'} | {milliseconds(row['dominant_nonoptimizer_seconds'])} |"
            )
        lines.append("")

    if bugs is not None:
        aggregate = bugs["aggregate"]
        lines.extend(
            [
                "## Confirmed miscompilations",
                "",
                "| Confirmed bugs | Rejections reproduced | Failed checks |",
                "| ---: | ---: | ---: |",
                f"| {aggregate['confirmed_miscompilations']} | {aggregate['rejections_confirmed']} | {aggregate['failed']} |",
                "",
            ]
        )
        for row in bugs["cases"]:
            lines.append(f"- `{row['name']}`: {row['status']} — {row['expected']}.")
        lines.append("")
    return "\n".join(lines)


def self_test() -> None:
    stages, metrics = parse_profile(
        "\n".join(
            [
                "[profile] stage timings",
                "[profile]   pluto_phase_pipeline     0.125000s",
                "[profile]   affine_validate          0.025000s",
                "[profile]   total                    0.250000s",
                "[profile] structural metrics",
                "[profile]   codegen_input.pis        3",
            ]
        )
    )
    assert stages == {
        "pluto_phase_pipeline": 0.125,
        "affine_validate": 0.025,
        "total": 0.25,
    }
    assert metrics == {"codegen_input.pis": 3}
    assert percentile([1.0, 2.0, 3.0], 0.5) == 2.0
    sample = "== Input Loop ==\na\n== Optimized Loop ==\nb\n"
    assert extract_section(sample, INPUT_MARKER) == "a"
    assert extract_section(sample, OUTPUT_MARKER) == "b"
    print("[self-test] PASS")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--mode",
        choices=["all", "completeness", "timing", "case-studies"],
        default="all",
    )
    parser.add_argument("--source-root", type=Path, default=Path("/polcert"))
    parser.add_argument("--output-dir", type=Path, default=Path("/results"))
    parser.add_argument(
        "--manifest",
        type=Path,
        default=Path("/usr/local/share/polcert-artifact/completeness_manifest.json"),
    )
    parser.add_argument("--polopt", type=Path, default=Path("/polcert/polopt"))
    parser.add_argument("--polycc", type=Path, default=Path("/pluto/polycc"))
    parser.add_argument("--pluto", type=Path, default=Path("/pluto/tool/pluto"))
    parser.add_argument("--pluto-test-dir", type=Path, default=Path("/pluto/test"))
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--warmups", type=int, default=1)
    parser.add_argument("--timeout-seconds", type=int, default=900)
    parser.add_argument("--bug-timeout-seconds", type=int, default=900)
    parser.add_argument("--no-pure-pluto", dest="run_pure_pluto", action="store_false")
    parser.add_argument(
        "--reuse-profile-results",
        action="store_true",
        help="reuse existing stage profiles and pure-Pluto runs, measuring only normal PolCert wall time",
    )
    parser.add_argument(
        "--summarize-existing-timing",
        action="store_true",
        help="regenerate timing aggregates from existing per-run data without executing compilers",
    )
    parser.add_argument(
        "--repair-failed-profiles",
        action="store_true",
        help="rerun only invalid stage profiles in an existing timing-results.json",
    )
    parser.add_argument("--case", dest="cases", action="append", default=[])
    parser.add_argument("--self-test", action="store_true")
    parser.set_defaults(run_pure_pluto=True)
    args = parser.parse_args()
    if args.repeats <= 0 or args.warmups < 0:
        parser.error("--repeats must be positive and --warmups must be nonnegative")
    if args.timeout_seconds <= 0 or args.bug_timeout_seconds <= 0:
        parser.error("timeouts must be positive")
    if args.summarize_existing_timing and args.mode != "timing":
        parser.error("--summarize-existing-timing requires --mode timing")
    if args.repair_failed_profiles and args.mode != "timing":
        parser.error("--repair-failed-profiles requires --mode timing")
    if args.repair_failed_profiles and (
        args.reuse_profile_results or args.summarize_existing_timing
    ):
        parser.error("--repair-failed-profiles cannot be combined with timing reuse modes")
    return args


def main() -> int:
    args = parse_args()
    if args.self_test:
        self_test()
        return 0
    args.source_root = args.source_root.resolve()
    args.output_dir = args.output_dir.resolve()
    args.manifest = args.manifest.resolve()
    args.polopt = args.polopt.resolve()
    args.polycc = args.polycc.resolve()
    args.pluto = args.pluto.resolve()
    args.pluto_test_dir = args.pluto_test_dir.resolve()
    for required in (
        args.source_root,
        args.manifest,
        args.polopt,
        args.pluto,
        args.pluto_test_dir,
    ):
        if not required.exists():
            raise SystemExit(f"required path not found: {required}")
    if args.run_pure_pluto and not args.polycc.exists():
        raise SystemExit(f"pure Pluto executable not found: {args.polycc}")

    manifest = load_manifest(args.manifest)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    metadata = {
        "schema_version": 1,
        "generated_at": utc_now(),
        "hostname": platform.node(),
        "platform": platform.platform(),
        "python": sys.version.split()[0],
        "source_root": str(args.source_root),
        "mode": args.mode,
        "machine": machine_metadata(),
        "executables": {
            "polopt_sha256": sha256_file(args.polopt),
            "polycc_sha256": sha256_file(args.polycc) if args.polycc.is_file() else None,
            "pluto_sha256": sha256_file(args.pluto),
        },
    }
    write_json(args.output_dir / "run-metadata.json", metadata)

    completeness = load_existing_result(args.output_dir / "completeness-results.json")
    timing = load_existing_result(args.output_dir / "timing-results.json")
    bugs = load_existing_result(args.output_dir / "case-studies.json")
    if args.mode in {"all", "completeness"}:
        completeness = run_completeness(args, manifest, args.output_dir)
    if args.mode in {"all", "timing"}:
        timing = run_timing(args, manifest, args.output_dir)
    if args.mode in {"all", "case-studies"}:
        bugs = run_bug_cases(args, manifest, args.output_dir)

    metadata["completed_at"] = utc_now()
    write_json(args.output_dir / "run-metadata.json", metadata)

    summary = {
        "metadata": metadata,
        "completeness": completeness,
        "timing": timing,
        "case_studies": bugs,
    }
    write_json(args.output_dir / "evaluation-results.json", summary)
    (args.output_dir / "evaluation-summary.md").write_text(
        render_summary(metadata, completeness, timing, bugs)
    )
    failures = 0
    if completeness is not None:
        failures += completeness["corpus_aggregate"]["rejected_or_failed"]
        failures += sum(row["rejected_or_failed"] for row in completeness["effect_groups"])
    if timing is not None:
        failures += timing["aggregate"]["requested_runs"] - timing["aggregate"]["successful_runs"]
        failures += (
            timing["aggregate"]["pure_pluto_requested_runs"]
            - timing["aggregate"]["pure_pluto_successful_runs"]
        )
    if bugs is not None:
        failures += bugs["aggregate"]["failed"]
    print(f"[evaluation] wrote {args.output_dir}", flush=True)
    print(f"[evaluation] {'PASS' if failures == 0 else 'FAIL'} failures={failures}", flush=True)
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
