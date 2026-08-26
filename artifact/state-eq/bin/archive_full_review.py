#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
from claim_evidence import (
    ClaimEvidenceError,
    claim_contract_summary,
    claim_json_assertion_equals,
    expected_artifact_routes,
    expected_outer_routes,
    verify_claim_evidence,
)


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "manifest.json"
DEFAULT_LOCK = ROOT / "locks" / "dependency-lock.json"
DEFAULT_BUILD_METADATA = ROOT / "build" / "build-metadata.json"
IMAGE_ID_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")

EXPECTED_OUTER_GATES = expected_outer_routes("full")
EXPECTED_ARTIFACT_CHECKS = expected_artifact_routes("full")
EXPECTED_TILING_ROUTE_SUMMARY = {
    "schema_version": 1,
    "verified": True,
    "zero_tiling_validation_fallbacks": True,
    "required_runtime_checks": {
        "direct-only-tiling-route-smoke": "pass",
        "non-second-level-tiling-routes": "pass",
        "second-level-suite": "pass",
        "pluto-compat-suite": "pass",
        "scalar-interleaved-tiling-route": "pass",
    },
    "direct_route_smoke": {
        "cases": 20,
        "zero_fallbacks": True,
    },
    "non_second_level": {
        "cases": 90,
        "permutable_band": 84,
        "validation_fallback": 0,
        "explicit_vector_rejection": 6,
    },
    "second_level_manifest": {
        "manifest_checks": 58,
        "successful": 53,
        "permutable_band": 53,
        "validation_fallback": 0,
        "negative": 5,
    },
    "second_level_additional_runtime_matrix": {
        "standalone_phase_aligned": "permutable-band",
        "standalone_source_like": "permutable-band",
        "standalone_trailing_zero_normalized": "permutable-band",
        "diamond_permutable_band": 16,
        "diamond_explicit_vector_rejection": 4,
        "verified": True,
    },
    "strict_loop_corpus": {
        "run": True,
        "permutable_band": 61,
        "not_applicable_no_loop": 1,
        "validation_fallback": 0,
        "verified": True,
    },
}

STATIC_RESULT_FILES = (
    "manifest.json",
    "claims.json",
    "dependency-lock-audit.json",
    "dependency-lock.json",
    "apt-packages.lock",
    "opam-packages.lock",
    "opam-switch-full.export",
)

STRUCTURED_RESULT_FILES = (
    "claim-results.json",
    "claim-evidence.json",
    "environment.json",
    "artifact-check/artifact-results.json",
    "artifact-check/proof-report.json",
    "artifact-check/capability-matrix.json",
    "artifact-check/tiling-route-summary.json",
    "artifact-check/unrolljam-effect-corpus/summary.json",
    "artifact-check/strict-loop-suite.stdout.txt",
    "logs/dependency-lock.stdout.txt",
    "logs/dependency-lock.stderr.txt",
)


class EvidenceError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise EvidenceError(f"cannot read JSON {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise EvidenceError(f"JSON root must be an object: {path}")
    return value


def require_file(path: Path) -> bytes:
    try:
        if not path.is_file():
            raise EvidenceError(f"required review result is missing: {path}")
        return path.read_bytes()
    except OSError as exc:
        raise EvidenceError(f"cannot read review result {path}: {exc}") from exc


def result_tree_digest(root: Path) -> dict[str, Any]:
    entries = list(root.rglob("*"))
    symlinks = [path for path in entries if path.is_symlink()]
    if symlinks:
        raise EvidenceError(f"raw review results must not contain symlinks: {symlinks[0]}")
    files = sorted(path for path in entries if path.is_file())
    if not files:
        raise EvidenceError(f"review result directory is empty: {root}")
    digest = hashlib.sha256()
    total_bytes = 0
    for path in files:
        relative = path.relative_to(root).as_posix().encode()
        data = require_file(path)
        total_bytes += len(data)
        for field in (relative, len(data).to_bytes(8, "big"), hashlib.sha256(data).digest()):
            digest.update(len(field).to_bytes(8, "big"))
            digest.update(field)
    return {
        "file_count": len(files),
        "bytes": total_bytes,
        "tree_sha256": digest.hexdigest(),
    }


def result_path(root: Path, recorded: Any, label: str) -> Path:
    if not isinstance(recorded, str) or not recorded.startswith("/artifact-results/"):
        raise EvidenceError(f"{label} has invalid archived path: {recorded!r}")
    prefix = "/artifact-results/"
    relative = recorded[len(prefix) :]
    path = root / relative
    try:
        path.resolve().relative_to(root.resolve())
    except ValueError as exc:
        raise EvidenceError(f"{label} escapes the raw result directory") from exc
    require_file(path)
    return path


def validate_result_list(
    results: Any,
    expected_names: tuple[str, ...],
    root: Path,
    label: str,
) -> list[dict[str, Any]]:
    if not isinstance(results, list):
        raise EvidenceError(f"{label} results must be a list")
    names = [item.get("name") if isinstance(item, dict) else None for item in results]
    if names != list(expected_names):
        raise EvidenceError(
            f"{label} gate names/order mismatch: expected {list(expected_names)}, got {names}"
        )
    for item in results:
        name = item["name"]
        if item.get("ok") is not True or item.get("returncode") != 0:
            raise EvidenceError(f"{label} gate did not pass with returncode=0: {name}")
        elapsed = item.get("elapsed_seconds")
        if not isinstance(elapsed, (int, float)) or elapsed < 0:
            raise EvidenceError(f"{label} gate has invalid elapsed time: {name}")
        result_path(root, item.get("stdout_path"), f"{label} {name} stdout")
        result_path(root, item.get("stderr_path"), f"{label} {name} stderr")
    return results


def parse_strict_loop_summary(path: Path) -> dict[str, int]:
    values: dict[str, int] = {}
    for line in require_file(path).decode(errors="replace").splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        if key in {"total", "ok", "changed", "detected_tiled"}:
            try:
                values[key] = int(value)
            except ValueError as exc:
                raise EvidenceError(f"invalid strict-loop summary line: {line!r}") from exc
    expected = {"total": 62, "ok": 62, "changed": 59, "detected_tiled": 46}
    if values != expected:
        raise EvidenceError(f"strict-loop summary mismatch: expected {expected}, got {values}")
    return {
        "total": values["total"],
        "passed": values["ok"],
        "changed": values["changed"],
        "detected_tiled": values["detected_tiled"],
    }


def parse_strict_case_seconds(path: Path, case: str) -> float:
    pattern = re.compile(
        rf"^\[\d+/\d+\] {re.escape(case)}: ok .* time=([0-9]+(?:\.[0-9]+)?)s$"
    )
    matches = []
    for line in require_file(path).decode(errors="replace").splitlines():
        match = pattern.fullmatch(line)
        if match:
            matches.append(float(match.group(1)))
    if len(matches) != 1:
        raise EvidenceError(
            f"strict-loop timing requires exactly one successful {case} result"
        )
    return matches[0]


def validate_proof_report(proof: dict[str, Any]) -> dict[str, int]:
    fields = (
        "coq_file_count",
        "admitted_count",
        "abort_count",
        "extraction_axiom_count",
        "missing_route_theorem_count",
    )
    result: dict[str, int] = {}
    for field in fields:
        value = proof.get(field)
        if not isinstance(value, int):
            raise EvidenceError(f"proof report has invalid {field}")
        result[field] = value
    if result["coq_file_count"] <= 0:
        raise EvidenceError("proof report requires a positive coq_file_count")
    for field in fields[1:]:
        if result[field] != 0:
            raise EvidenceError(f"proof report requires {field}=0")
    return result


def validate_zero_tiling_fallbacks(summary: dict[str, Any]) -> None:
    """Require every accepted tiling route to use direct band validation."""

    if summary != EXPECTED_TILING_ROUTE_SUMMARY:
        raise EvidenceError(
            "tiling route summary does not match the exact direct-only schema"
        )


def required_file_hashes(results_dir: Path) -> dict[str, str]:
    paths = (*STATIC_RESULT_FILES, *STRUCTURED_RESULT_FILES)
    return {name: sha256(require_file(results_dir / name)) for name in paths}


def repository_static_hashes(manifest_path: Path, lock_path: Path) -> dict[str, str]:
    artifact_root = manifest_path.resolve().parent
    result: dict[str, str] = {}
    for name in STATIC_RESULT_FILES:
        source = lock_path if name == "dependency-lock.json" else artifact_root / name
        if name in {"apt-packages.lock", "opam-packages.lock", "opam-switch-full.export"}:
            source = lock_path.parent / name
        result[name] = sha256(require_file(source))
    return result


def inspect_image_id(docker_bin: str, image: str) -> str:
    try:
        result = subprocess.run(
            [docker_bin, "image", "inspect", image],
            text=True,
            capture_output=True,
            check=False,
        )
    except OSError as exc:
        raise EvidenceError(f"cannot execute Docker: {exc}") from exc
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise EvidenceError(f"cannot inspect candidate image {image}: {detail}")
    try:
        image_id = json.loads(result.stdout)[0]["Id"]
    except (json.JSONDecodeError, IndexError, KeyError, TypeError) as exc:
        raise EvidenceError("Docker inspect returned invalid candidate image data") from exc
    if not isinstance(image_id, str) or not IMAGE_ID_RE.fullmatch(image_id):
        raise EvidenceError("Docker inspect returned invalid candidate image ID")
    return image_id


def validate_compact_v2(
    evidence: dict[str, Any],
    manifest: dict[str, Any],
    lock_sha256: str,
    static_hashes: dict[str, str] | None = None,
    claims: dict[str, Any] | None = None,
) -> None:
    if evidence.get("schema_version") != 2:
        raise EvidenceError("candidate review evidence must use schema_version=2")
    review = evidence.get("review", {})
    if review.get("profile") != "full" or review.get("network") != "none":
        raise EvidenceError("schema-v2 evidence requires full offline review")
    if review.get("ok") is not True:
        raise EvidenceError("schema-v2 evidence does not record a successful review")
    if not isinstance(review.get("recorded_at"), str) or not review["recorded_at"]:
        raise EvidenceError("schema-v2 evidence has no review timestamp")

    results = evidence.get("top_level_results")
    if not isinstance(results, list):
        raise EvidenceError("schema-v2 top_level_results must be a list")
    names = [item.get("name") if isinstance(item, dict) else None for item in results]
    if names != list(EXPECTED_OUTER_GATES):
        raise EvidenceError("schema-v2 evidence must record the exact 13 outer gates in order")
    for item in results:
        if item.get("ok") is not True or item.get("returncode") != 0:
            raise EvidenceError(f"schema-v2 outer gate is not PASS/0: {item.get('name')}")
        elapsed = item.get("elapsed_seconds")
        if not isinstance(elapsed, (int, float)) or elapsed < 0:
            raise EvidenceError(
                f"schema-v2 outer gate has invalid elapsed time: {item.get('name')}"
            )

    candidate = manifest.get("images", {}).get("default_candidate", {}).get("reference")
    image = evidence.get("images", {}).get("artifact", {})
    executed_image_id = review.get("executed_image_id")
    if not isinstance(executed_image_id, str) or not IMAGE_ID_RE.fullmatch(
        executed_image_id
    ):
        raise EvidenceError("schema-v2 review has no valid executed image ID")
    if executed_image_id != image.get("id"):
        raise EvidenceError("schema-v2 executed image ID differs from artifact image ID")
    environment = evidence.get("environment", {})
    if environment.get("artifact_image_id") != executed_image_id:
        raise EvidenceError("schema-v2 environment image ID differs from executed image ID")
    if image.get("reference") != candidate:
        raise EvidenceError("schema-v2 evidence artifact reference is not the manifest candidate")
    if not isinstance(image.get("id"), str) or not IMAGE_ID_RE.fullmatch(image["id"]):
        raise EvidenceError("schema-v2 evidence has invalid candidate image ID")
    dependency_origin = evidence.get("images", {}).get("dependency_origin", {})
    expected_dependency_origin = manifest.get("images", {}).get(
        "dependency_lock_origin", {}
    )
    if dependency_origin != {
        "reference": expected_dependency_origin.get("reference"),
        "id": expected_dependency_origin.get("local_image_id"),
    }:
        raise EvidenceError("schema-v2 dependency origin differs from manifest")
    if evidence.get("packaging_revision") != manifest.get("artifact", {}).get(
        "packaging_revision"
    ):
        raise EvidenceError("schema-v2 packaging revision does not match manifest")

    source = evidence.get("source", {})
    source_manifest = manifest.get("polcert", {})
    expected_source = {
        field: source_manifest.get(field)
        for field in ("tag", "tag_object", "commit", "tree", "archive_sha256")
    }
    if not isinstance(source, dict) or {
        field: source.get(field) for field in expected_source
    } != expected_source:
        raise EvidenceError(
            "schema-v2 source identity or archive differs from manifest"
        )

    environment = evidence.get("environment", {})
    toolchain = manifest.get("toolchain", {})
    if environment.get("opam") != toolchain.get("opam"):
        raise EvidenceError("schema-v2 environment opam version does not match manifest")
    if environment.get("ocaml") != toolchain.get("ocaml"):
        raise EvidenceError("schema-v2 environment OCaml version does not match manifest")
    if str(toolchain.get("coq")) not in str(environment.get("coq")):
        raise EvidenceError("schema-v2 environment Coq version does not match manifest")
    pluto_commit = manifest.get("pluto", {}).get("commit")
    if not isinstance(pluto_commit, str) or pluto_commit[:7] not in str(
        environment.get("pluto")
    ):
        raise EvidenceError("schema-v2 environment Pluto version does not match manifest")
    if environment.get("network_contract") != "review command is run with Docker --network none":
        raise EvidenceError("schema-v2 environment does not record the offline contract")

    dependency_lock = evidence.get("dependency_lock", {})
    if dependency_lock.get("sha256") != lock_sha256:
        raise EvidenceError("schema-v2 dependency lock SHA-256 does not match repository lock")
    if dependency_lock.get("gate") != "dependency-lock" or dependency_lock.get("ok") is not True:
        raise EvidenceError("schema-v2 dependency-lock gate is not recorded as successful")

    raw = review.get("raw_results", {})
    for field in ("tree_sha256",):
        if not isinstance(raw.get(field), str) or not SHA256_RE.fullmatch(raw[field]):
            raise EvidenceError(f"schema-v2 raw results have invalid {field}")
    for field in ("file_count", "bytes"):
        if not isinstance(raw.get(field), int) or raw[field] <= 0:
            raise EvidenceError(f"schema-v2 raw results have invalid {field}")
    files = raw.get("required_files")
    required = set((*STATIC_RESULT_FILES, *STRUCTURED_RESULT_FILES))
    if not isinstance(files, dict) or set(files) != required:
        raise EvidenceError("schema-v2 raw results do not list every required file")
    if any(
        not isinstance(value, str) or not SHA256_RE.fullmatch(value)
        for value in files.values()
    ):
        raise EvidenceError("schema-v2 raw result file has an invalid SHA-256")
    if files["dependency-lock.json"] != lock_sha256:
        raise EvidenceError("schema-v2 raw dependency-lock copy has the wrong SHA-256")
    if static_hashes is not None:
        for name, expected in static_hashes.items():
            if files.get(name) != expected:
                raise EvidenceError(f"schema-v2 raw {name} does not match repository input")

    tiling_validation = evidence.get("tiling_validation", {})
    expected_tiling_validation = {
        "gate_version": 2,
        "exact_direct_only_schema_gate": True,
        "recursive_zero_fallback_gate": True,
        "all_accepted_tilings_direct_permutable_band": True,
        "summary_sha256": files.get("artifact-check/tiling-route-summary.json"),
    }
    if tiling_validation != expected_tiling_validation:
        raise EvidenceError(
            "schema-v2 tiling validation does not certify the recursive "
            "direct-permutable-band gate"
        )

    claim_evidence = evidence.get("claim_evidence", {})
    for field in ("claims_sha256", "report_sha256"):
        if not isinstance(claim_evidence.get(field), str) or not SHA256_RE.fullmatch(
            claim_evidence[field]
        ):
            raise EvidenceError(f"schema-v2 claim evidence has invalid {field}")
    if claim_evidence.get("report_sha256") != files.get("claim-evidence.json"):
        raise EvidenceError("schema-v2 claim evidence report SHA-256 differs from raw results")
    if claim_evidence.get("claims_sha256") != files.get("claims.json"):
        raise EvidenceError("schema-v2 claim evidence claims SHA-256 differs from raw results")
    if claims is None:
        raise EvidenceError("schema-v2 compact validation requires the claims contract")
    try:
        expected_claims = claim_contract_summary(claims, "full")
    except ClaimEvidenceError as exc:
        raise EvidenceError(f"invalid claims contract: {exc}") from exc
    if claim_evidence.get("claim_ids") != expected_claims["claim_ids"]:
        raise EvidenceError("schema-v2 claim evidence IDs differ from the claims contract")
    for field in (
        "claim_count",
        "verified_claims",
        "required_evidence_references",
        "resolved_evidence_references",
        "supplemental_evidence_references",
        "resolved_supplemental_evidence_references",
        "theorem_surface_entries",
        "resolved_theorem_surface_entries",
    ):
        if type(claim_evidence.get(field)) is not int or claim_evidence[field] < 0:
            raise EvidenceError(f"schema-v2 claim evidence has invalid {field}")
    for field in (
        "claim_count",
        "required_evidence_references",
        "supplemental_evidence_references",
        "theorem_surface_entries",
    ):
        if claim_evidence[field] != expected_claims[field]:
            raise EvidenceError(
                f"schema-v2 claim evidence {field} differs from the claims contract"
            )
    if claim_evidence["claim_count"] <= 0:
        raise EvidenceError("schema-v2 claim evidence requires at least one claim")
    if claim_evidence["verified_claims"] != expected_claims["claim_count"]:
        raise EvidenceError("schema-v2 claim evidence does not verify every claim")
    if (
        claim_evidence["resolved_evidence_references"]
        != expected_claims["required_evidence_references"]
    ):
        raise EvidenceError("schema-v2 claim evidence did not resolve every required reference")
    if (
        claim_evidence["resolved_supplemental_evidence_references"]
        != expected_claims["supplemental_evidence_references"]
    ):
        raise EvidenceError(
            "schema-v2 claim evidence did not resolve every applicable supplemental reference"
        )
    if (
        claim_evidence["resolved_theorem_surface_entries"]
        != expected_claims["theorem_surface_entries"]
    ):
        raise EvidenceError("schema-v2 claim evidence did not resolve every theorem entry")

    validate_proof_report(evidence.get("proof_report", {}))
    capability = evidence.get("capability_results", {})
    try:
        expected_compatibility_checks = claim_json_assertion_equals(
            claims,
            "artifact-check/capability-matrix",
            "artifact-check/capability-matrix.json",
            "/summary/compatibility_checks",
        )
    except ClaimEvidenceError as exc:
        raise EvidenceError(f"invalid capability claim contract: {exc}") from exc
    expected_capability = {
        "artifact_subchecks": len(EXPECTED_ARTIFACT_CHECKS),
        "artifact_subchecks_passed": len(EXPECTED_ARTIFACT_CHECKS),
        "pluto_compat_checks": expected_compatibility_checks,
        "iss_suite": "PASS",
        "parallel_current_suite": "PASS",
        "vector_current_suite": "PASS",
        "second_level_suite": "PASS",
        "diamond_suite": "PASS",
    }
    for field, expected in expected_capability.items():
        if capability.get(field) != expected:
            raise EvidenceError(f"schema-v2 capability result requires {field}={expected}")
    strict = capability.get("strict_loop_suite", {})
    expected_strict = {
        "total": 62,
        "passed": 62,
        "changed": 59,
        "detected_tiled": 46,
    }
    if any(strict.get(field) != expected for field, expected in expected_strict.items()):
        raise EvidenceError(
            "schema-v2 strict-loop result requires "
            "total=62, passed=62, changed=59, detected_tiled=46"
        )

    timing = evidence.get("timing", {})
    if timing.get("make_jobs") != 1:
        raise EvidenceError("schema-v2 timing requires make_jobs=1")
    if timing.get("parallel_make_requested") is not False:
        raise EvidenceError(
            "schema-v2 timing must record that parallel make was not requested"
        )
    for field in (
        "full_review_seconds",
        "proof_build_seconds",
        "artifact_check_seconds",
        "strict_loop_suite_seconds",
        "advect3d_seconds",
    ):
        value = timing.get(field)
        if not isinstance(value, (int, float)) or value < 0:
            raise EvidenceError(f"schema-v2 timing has invalid {field}")
    results_by_name = {item["name"]: item for item in results}
    expected_timing = {
        "full_review_seconds": review.get("elapsed_seconds"),
        "proof_build_seconds": results_by_name["proof-build"]["elapsed_seconds"],
        "artifact_check_seconds": results_by_name["artifact-check"]["elapsed_seconds"],
    }
    for field, expected in expected_timing.items():
        if timing[field] != expected:
            raise EvidenceError(f"schema-v2 timing {field} differs from the gate ledger")


def build_evidence(
    results_dir: Path,
    manifest_path: Path,
    lock_path: Path,
    build_metadata_path: Path,
    image_reference: str,
    image_id: str,
) -> dict[str, Any]:
    results_dir = results_dir.resolve()
    if not results_dir.is_dir():
        raise EvidenceError(f"review result directory does not exist: {results_dir}")
    manifest = load_json(manifest_path)
    lock_bytes = require_file(lock_path)
    lock_sha = sha256(lock_bytes)
    build = load_json(build_metadata_path)

    artifact_root = manifest_path.resolve().parent
    for name in STATIC_RESULT_FILES:
        source = lock_path if name == "dependency-lock.json" else artifact_root / name
        if name in {"apt-packages.lock", "opam-packages.lock", "opam-switch-full.export"}:
            source = lock_path.parent / name
        if require_file(results_dir / name) != require_file(source):
            raise EvidenceError(f"raw review copy differs from repository input: {name}")
    if build.get("manifest") != manifest:
        raise EvidenceError("build metadata manifest differs from repository manifest")

    claim = load_json(results_dir / "claim-results.json")
    if claim.get("mode") != "full" or claim.get("ok") is not True:
        raise EvidenceError("claim-results.json is not a successful full review")
    if claim.get("artifact_id") != manifest.get("artifact", {}).get("id"):
        raise EvidenceError("claim-results artifact ID differs from manifest")
    if claim.get("artifact_image_id") != image_id:
        raise EvidenceError("claim-results image ID differs from reviewed image ID")
    outer = validate_result_list(
        claim.get("results"), EXPECTED_OUTER_GATES, results_dir, "outer review"
    )
    outer_by_name = {item["name"]: item for item in outer}

    artifact = load_json(results_dir / "artifact-check" / "artifact-results.json")
    if artifact.get("mode") != "full" or artifact.get("ok") is not True:
        raise EvidenceError("artifact-results.json is not a successful full check")
    inner = validate_result_list(
        artifact.get("results"), EXPECTED_ARTIFACT_CHECKS, results_dir, "artifact"
    )
    inner_by_name = {item["name"]: item for item in inner}

    claims_bytes = require_file(results_dir / "claims.json")
    claims = load_json(results_dir / "claims.json")
    try:
        computed_claim_evidence = verify_claim_evidence(
            claims=claims,
            profile="full",
            results_root=results_dir,
            outer_results=claim.get("results"),
            artifact_results=artifact.get("results"),
            claims_sha256=sha256(claims_bytes),
        )
    except ClaimEvidenceError as exc:
        raise EvidenceError(f"claim-to-evidence verification failed: {exc}") from exc
    recorded_claim_evidence = load_json(results_dir / "claim-evidence.json")
    if recorded_claim_evidence != computed_claim_evidence:
        raise EvidenceError(
            "claim-evidence.json differs from independent claim-to-evidence verification"
        )
    if computed_claim_evidence.get("ok") is not True:
        raise EvidenceError("claim-to-evidence report is not successful")

    environment = load_json(results_dir / "environment.json")
    source_manifest = manifest.get("polcert", {})
    for environment_field, manifest_field in (
        ("polcert_source_tag", "tag"),
        ("polcert_source_commit", "commit"),
        ("polcert_source_tree", "tree"),
    ):
        if environment.get(environment_field) != source_manifest.get(manifest_field):
            raise EvidenceError(f"environment {environment_field} differs from manifest")
    if environment.get("network_contract") != "review command is run with Docker --network none":
        raise EvidenceError("environment does not record the offline review contract")
    if environment.get("artifact_image_id") != image_id:
        raise EvidenceError("environment image ID differs from reviewed image ID")

    proof = validate_proof_report(
        load_json(results_dir / "artifact-check" / "proof-report.json")
    )
    tiling_summary_path = (
        results_dir / "artifact-check" / "tiling-route-summary.json"
    )
    tiling_summary = load_json(tiling_summary_path)
    validate_zero_tiling_fallbacks(tiling_summary)
    capability_matrix = load_json(
        results_dir / "artifact-check" / "capability-matrix.json"
    )
    compatibility_checks = capability_matrix.get("summary", {}).get("compatibility_checks")
    try:
        expected_compatibility_checks = claim_json_assertion_equals(
            claims,
            "artifact-check/capability-matrix",
            "artifact-check/capability-matrix.json",
            "/summary/compatibility_checks",
        )
    except ClaimEvidenceError as exc:
        raise EvidenceError(f"invalid capability claim contract: {exc}") from exc
    if compatibility_checks != expected_compatibility_checks:
        raise EvidenceError(
            "capability matrix compatibility count differs from the claims contract"
        )
    strict = parse_strict_loop_summary(
        results_dir / "artifact-check" / "strict-loop-suite.stdout.txt"
    )
    advect3d_seconds = parse_strict_case_seconds(
        results_dir / "artifact-check" / "strict-loop-suite.stdout.txt",
        "advect3d",
    )

    candidate_reference = manifest.get("images", {}).get("default_candidate", {}).get(
        "reference"
    )
    if image_reference != candidate_reference:
        raise EvidenceError("requested image is not the manifest candidate")
    if not IMAGE_ID_RE.fullmatch(image_id):
        raise EvidenceError("candidate image ID is invalid")
    built_artifact = build.get("artifact_image", {})
    if built_artifact.get("reference") != image_reference or built_artifact.get("id") != image_id:
        raise EvidenceError("build metadata does not match candidate image reference and ID")
    labels = built_artifact.get("labels", {})
    if not isinstance(labels, dict):
        raise EvidenceError("candidate build metadata has invalid labels")
    if labels.get("io.polcert.packaging.revision") != manifest.get("artifact", {}).get(
        "packaging_revision"
    ):
        raise EvidenceError("candidate packaging label differs from manifest")
    dependency_origin = manifest.get("images", {}).get("dependency_lock_origin", {})
    built_dependency_origin = build.get("dependency_origin_image", {})
    if (
        built_dependency_origin.get("reference") != dependency_origin.get("reference")
        or built_dependency_origin.get("id") != dependency_origin.get("local_image_id")
    ):
        raise EvidenceError("build metadata dependency origin differs from manifest")
    source_archive_sha256 = build.get("source_archive_sha256")
    if not isinstance(source_archive_sha256, str) or not SHA256_RE.fullmatch(
        source_archive_sha256
    ):
        raise EvidenceError("build metadata has invalid source archive SHA-256")
    if source_archive_sha256 != source_manifest.get("archive_sha256"):
        raise EvidenceError("build metadata source archive differs from manifest")
    for label, expected in (
        ("org.opencontainers.image.version", source_manifest.get("tag")),
        ("org.opencontainers.image.revision", source_manifest.get("commit")),
        ("io.polcert.source.tree", source_manifest.get("tree")),
        ("io.polcert.source.archive.sha256", source_archive_sha256),
    ):
        if labels.get(label) != expected:
            raise EvidenceError(f"candidate image label {label} differs from build identity")

    tree = result_tree_digest(results_dir)
    evidence = {
        "schema_version": 2,
        "packaging_revision": manifest["artifact"]["packaging_revision"],
        "review": {
            "profile": "full",
            "network": "none",
            "ok": True,
            "executed_image_id": image_id,
            "recorded_at": environment.get("recorded_at"),
            "elapsed_seconds": sum(item["elapsed_seconds"] for item in outer),
            "raw_results": {
                **tree,
                "required_files": required_file_hashes(results_dir),
            },
        },
        "source": {
            "tag": source_manifest["tag"],
            "tag_object": source_manifest["tag_object"],
            "commit": source_manifest["commit"],
            "tree": source_manifest["tree"],
            "archive_sha256": source_archive_sha256,
        },
        "images": {
            "pluto_base": {
                "reference": build.get("pluto_base_image", {}).get("reference"),
                "digest": manifest.get("pluto", {}).get("base_image_digest"),
            },
            "source": {
                "reference": build.get("source_image", {}).get("reference"),
                "id": build.get("source_image", {}).get("id"),
            },
            "dependency_origin": {
                "reference": built_dependency_origin.get("reference"),
                "id": built_dependency_origin.get("id"),
            },
            "artifact": {"reference": image_reference, "id": image_id},
        },
        "environment": environment,
        "top_level_results": [
            {
                "name": item["name"],
                "ok": item["ok"],
                "returncode": item["returncode"],
                "elapsed_seconds": item["elapsed_seconds"],
            }
            for item in outer
        ],
        "dependency_lock": {
            "gate": "dependency-lock",
            "ok": True,
            "sha256": lock_sha,
            "origin_review_evidence_sha256": load_json(lock_path)
            .get("origin", {})
            .get("review_evidence_sha256"),
        },
        "claim_evidence": {
            "claims_sha256": computed_claim_evidence["claims_sha256"],
            "report_sha256": sha256(require_file(results_dir / "claim-evidence.json")),
            **computed_claim_evidence["summary"],
        },
        "tiling_validation": {
            "gate_version": 2,
            "exact_direct_only_schema_gate": True,
            "recursive_zero_fallback_gate": True,
            "all_accepted_tilings_direct_permutable_band": True,
            "summary_sha256": sha256(require_file(tiling_summary_path)),
        },
        "proof_report": proof,
        "capability_results": {
            "artifact_subchecks": len(inner),
            "artifact_subchecks_passed": sum(item["ok"] for item in inner),
            "pluto_compat_checks": compatibility_checks,
            "strict_loop_suite": strict,
            "iss_suite": "PASS" if inner_by_name["iss-suite"]["ok"] else "FAIL",
            "parallel_current_suite": (
                "PASS" if inner_by_name["parallel-current-suite"]["ok"] else "FAIL"
            ),
            "vector_current_suite": (
                "PASS" if outer_by_name["vector-current-suite"]["ok"] else "FAIL"
            ),
            "second_level_suite": (
                "PASS" if inner_by_name["second-level-suite"]["ok"] else "FAIL"
            ),
            "diamond_suite": "PASS" if inner_by_name["diamond-suite"]["ok"] else "FAIL",
        },
        "timing": {
            "make_jobs": 1,
            "parallel_make_requested": False,
            "full_review_seconds": sum(item["elapsed_seconds"] for item in outer),
            "proof_build_seconds": outer_by_name["proof-build"]["elapsed_seconds"],
            "artifact_check_seconds": outer_by_name["artifact-check"]["elapsed_seconds"],
            "strict_loop_suite_seconds": inner_by_name["strict-loop-suite"][
                "elapsed_seconds"
            ],
            "advect3d_seconds": advect3d_seconds,
        },
        "build": {
            "metadata_sha256": sha256(require_file(build_metadata_path)),
            "recorded_at": build.get("recorded_at"),
        },
    }
    validate_compact_v2(
        evidence,
        manifest,
        lock_sha,
        repository_static_hashes(manifest_path, lock_path),
        claims,
    )
    return evidence


def atomic_write_json(path: Path, value: dict[str, Any]) -> None:
    path = path.resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        raise EvidenceError(f"review evidence already exists: {path}")
    fd, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "w") as handle:
            json.dump(value, handle, indent=2, sort_keys=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        os.link(temporary, path)
        temporary.unlink()
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def validate_evidence_against_raw(
    evidence: dict[str, Any],
    results_dir: Path,
    manifest_path: Path,
    lock_path: Path,
    build_metadata_path: Path,
    image_reference: str,
    image_id: str,
) -> None:
    expected = build_evidence(
        results_dir,
        manifest_path,
        lock_path,
        build_metadata_path,
        image_reference,
        image_id,
    )
    if evidence != expected:
        raise EvidenceError("review evidence differs from the raw result bundle")


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Create or validate schema-v2 evidence from a complete State.eq "
            "full-review directory."
        )
    )
    parser.add_argument("command", choices=("create", "validate"))
    parser.add_argument("--results-dir", type=Path, required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument("--build-metadata", type=Path, default=DEFAULT_BUILD_METADATA)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--lock", type=Path, default=DEFAULT_LOCK)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--docker-bin", default="docker", help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        image_id = inspect_image_id(args.docker_bin, args.image)
        expected = build_evidence(
            args.results_dir,
            args.manifest,
            args.lock,
            args.build_metadata,
            args.image,
            image_id,
        )
        if args.command == "create":
            atomic_write_json(args.evidence, expected)
            print(f"schema-v2 review evidence created: {args.evidence}")
            return 0
        actual = load_json(args.evidence)
        if actual != expected:
            raise EvidenceError("review evidence differs from the raw result bundle")
        print(f"schema-v2 review evidence verified: {args.evidence}")
        return 0
    except EvidenceError as exc:
        print(f"review evidence failure: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
