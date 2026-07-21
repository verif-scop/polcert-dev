#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import math
import re
from pathlib import Path
from typing import Any


PROFILES = ("smoke", "full", "extended")
VERIFICATION_PROFILES = ("full", "extended")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")

BOOTSTRAP_OUTER_ROUTES = (
    "dependency-lock",
    "pluto-baseline",
    "clean",
    "depend",
    "proof-build",
    "check-admitted",
    "extraction",
    "build-polopt",
    "build-polcert-ini",
    "build-polcert",
)
SMOKE_OUTER_ROUTES = BOOTSTRAP_OUTER_ROUTES + ("artifact-check",)
FULL_OUTER_ROUTES = BOOTSTRAP_OUTER_ROUTES + (
    "core-regression",
    "artifact-check",
    "vector-current-suite",
)
EXTENDED_OUTER_ROUTES = FULL_OUTER_ROUTES + ("iss-live-suite",)

BASE_ARTIFACT_ROUTES = (
    "py-compile-artifact-tools",
    "proof-report",
    "capability-matrix",
    "codegen-gap-exploration",
    "unrolljam-effect-corpus",
    "identity-composition-exploration",
    "direct-band-differential",
    "non-second-level-tiling-routes",
    "pluto-compat-suite",
    "end-to-end-c-const-unroll",
    "end-to-end-c-unrolljam-block-variable",
    "end-to-end-c-unrolljam-dependent-guard",
    "end-to-end-c-stride-even",
    "end-to-end-c-stride-down",
    "second-level-scheduler-forwarding",
    "second-level-suite",
    "diamond-suite",
)
FULL_ARTIFACT_ROUTES = BASE_ARTIFACT_ROUTES + (
    "check-admitted",
    "strict-loop-suite",
    "iss-suite",
    "parallel-current-suite",
    "vector-current-suite",
)


class ClaimEvidenceError(RuntimeError):
    pass


def canonical_route_profiles() -> dict[str, tuple[str, ...]]:
    routes: dict[str, tuple[str, ...]] = {}
    for name in SMOKE_OUTER_ROUTES:
        routes[f"outer/{name}"] = PROFILES
    for name in ("core-regression", "vector-current-suite"):
        routes[f"outer/{name}"] = ("full", "extended")
    routes["outer/iss-live-suite"] = ("extended",)
    for name in BASE_ARTIFACT_ROUTES:
        routes[f"artifact-check/{name}"] = PROFILES
    for name in set(FULL_ARTIFACT_ROUTES) - set(BASE_ARTIFACT_ROUTES):
        routes[f"artifact-check/{name}"] = ("full", "extended")
    return routes


def expected_outer_routes(profile: str) -> tuple[str, ...]:
    if profile == "smoke":
        return SMOKE_OUTER_ROUTES
    if profile == "full":
        return FULL_OUTER_ROUTES
    if profile == "extended":
        return EXTENDED_OUTER_ROUTES
    raise ClaimEvidenceError(f"unsupported review profile: {profile}")


def expected_artifact_routes(profile: str) -> tuple[str, ...]:
    if profile == "smoke":
        return BASE_ARTIFACT_ROUTES
    if profile in VERIFICATION_PROFILES:
        return FULL_ARTIFACT_ROUTES
    raise ClaimEvidenceError(f"unsupported review profile: {profile}")


def _require_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ClaimEvidenceError(f"{label} must be an object")
    return value


def _require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise ClaimEvidenceError(f"{label} must be a non-empty string")
    return value


def _bundle_path(root: Path, relative: Any, label: str) -> Path:
    relative = _require_string(relative, label)
    candidate = root / relative
    try:
        candidate.resolve().relative_to(root.resolve())
    except ValueError as exc:
        raise ClaimEvidenceError(f"{label} escapes the result bundle: {relative}") from exc
    if not candidate.is_file():
        raise ClaimEvidenceError(f"{label} is missing: {relative}")
    return candidate


def _recorded_path(root: Path, recorded: Any, label: str) -> str:
    recorded = _require_string(recorded, label)
    prefix = "/artifact-results/"
    if not recorded.startswith(prefix):
        raise ClaimEvidenceError(f"{label} has invalid result path: {recorded}")
    relative = recorded.removeprefix(prefix)
    _bundle_path(root, relative, label)
    return relative


def _result_index(results: Any, ledger: str) -> dict[str, dict[str, Any]]:
    if not isinstance(results, list):
        raise ClaimEvidenceError(f"{ledger} result ledger must be a list")
    index: dict[str, dict[str, Any]] = {}
    for position, raw in enumerate(results):
        item = _require_object(raw, f"{ledger} result {position}")
        name = _require_string(item.get("name"), f"{ledger} result {position} name")
        if name in index:
            raise ClaimEvidenceError(f"{ledger} result ledger repeats route {name}")
        index[name] = item
    return index


def _json_pointer(document: Any, pointer: Any, label: str) -> Any:
    pointer = _require_string(pointer, label)
    if pointer == "/":
        return document
    if not pointer.startswith("/"):
        raise ClaimEvidenceError(f"{label} must start with '/': {pointer}")
    current = document
    for raw_token in pointer[1:].split("/"):
        token = raw_token.replace("~1", "/").replace("~0", "~")
        if isinstance(current, dict) and token in current:
            current = current[token]
        elif isinstance(current, list) and token.isdigit() and int(token) < len(current):
            current = current[int(token)]
        else:
            raise ClaimEvidenceError(f"{label} does not resolve: {pointer}")
    return current


def _validate_assertion(value: Any, assertion: dict[str, Any], label: str) -> None:
    operators = [name for name in ("equals", "minimum", "nonempty") if name in assertion]
    if len(operators) != 1:
        raise ClaimEvidenceError(f"{label} must declare exactly one assertion operator")
    operator = operators[0]
    expected = assertion[operator]
    if operator == "equals" and (
        type(value) is not type(expected) or value != expected
    ):
        raise ClaimEvidenceError(f"{label} expected {expected!r}, got {value!r}")
    if operator == "minimum":
        if not isinstance(expected, (int, float)) or isinstance(expected, bool):
            raise ClaimEvidenceError(f"{label} minimum must be numeric")
        if (
            not isinstance(value, (int, float))
            or isinstance(value, bool)
            or (isinstance(value, float) and not math.isfinite(value))
            or value < expected
        ):
            raise ClaimEvidenceError(f"{label} expected at least {expected!r}, got {value!r}")
    if operator == "nonempty":
        if expected is not True:
            raise ClaimEvidenceError(f"{label} nonempty operator must be true")
        if not isinstance(value, (str, list, dict)) or not value:
            raise ClaimEvidenceError(f"{label} expected a non-empty value")


def _validate_artifacts(root: Path, artifacts: Any, evidence_id: str) -> list[dict[str, Any]]:
    if artifacts is None:
        return []
    if not isinstance(artifacts, list) or not artifacts:
        raise ClaimEvidenceError(f"evidence {evidence_id} artifacts must be a non-empty list")
    resolved: list[dict[str, Any]] = []
    for position, raw in enumerate(artifacts):
        artifact = _require_object(raw, f"evidence {evidence_id} artifact {position}")
        relative = _require_string(
            artifact.get("path"), f"evidence {evidence_id} artifact {position} path"
        )
        path = _bundle_path(root, relative, f"evidence {evidence_id} artifact")
        assertions = artifact.get("json_assertions", [])
        if not isinstance(assertions, list):
            raise ClaimEvidenceError(
                f"evidence {evidence_id} artifact {relative} assertions must be a list"
            )
        assertion_results: list[dict[str, Any]] = []
        collection_assertions = artifact.get("collection_assertions", [])
        if not isinstance(collection_assertions, list):
            raise ClaimEvidenceError(
                f"evidence {evidence_id} artifact {relative} collection assertions "
                "must be a list"
            )
        document: Any = None
        if assertions or collection_assertions:
            try:
                document = json.loads(path.read_text())
            except (OSError, json.JSONDecodeError) as exc:
                raise ClaimEvidenceError(
                    f"evidence {evidence_id} artifact is not valid JSON: {relative}: {exc}"
                ) from exc
        if assertions:
            for assertion_position, raw_assertion in enumerate(assertions):
                assertion = _require_object(
                    raw_assertion,
                    f"evidence {evidence_id} artifact {relative} assertion {assertion_position}",
                )
                pointer = assertion.get("pointer")
                value = _json_pointer(
                    document,
                    pointer,
                    f"evidence {evidence_id} artifact {relative} assertion pointer",
                )
                _validate_assertion(
                    value,
                    assertion,
                    f"evidence {evidence_id} artifact {relative} {pointer}",
                )
                assertion_results.append({"pointer": pointer, "ok": True})
        collection_assertion_results: list[dict[str, Any]] = []
        for assertion_position, raw_assertion in enumerate(collection_assertions):
            assertion = _require_object(
                raw_assertion,
                f"evidence {evidence_id} artifact {relative} collection assertion "
                f"{assertion_position}",
            )
            pointer = assertion.get("pointer")
            collection = _json_pointer(
                document,
                pointer,
                f"evidence {evidence_id} artifact {relative} collection pointer",
            )
            if not isinstance(collection, list):
                raise ClaimEvidenceError(
                    f"evidence {evidence_id} artifact {relative} {pointer} must be an array"
                )
            length_equals = assertion.get("length_equals")
            has_count = any(
                name in assertion
                for name in ("item_pointer", "item_equals", "count_equals")
            )
            if length_equals is not None and has_count:
                raise ClaimEvidenceError(
                    f"evidence {evidence_id} artifact {relative} collection assertion "
                    "cannot combine length and item-count operators"
                )
            if length_equals is not None:
                if type(length_equals) is not int or length_equals < 0:
                    raise ClaimEvidenceError(
                        f"evidence {evidence_id} artifact {relative} length_equals "
                        "must be a nonnegative integer"
                    )
                if len(collection) != length_equals:
                    raise ClaimEvidenceError(
                        f"evidence {evidence_id} artifact {relative} {pointer} expected "
                        f"length {length_equals}, got {len(collection)}"
                    )
                collection_assertion_results.append(
                    {"pointer": pointer, "length_equals": length_equals, "actual": len(collection)}
                )
                continue
            if not all(
                name in assertion
                for name in ("item_pointer", "item_equals", "count_equals")
            ):
                raise ClaimEvidenceError(
                    f"evidence {evidence_id} artifact {relative} collection assertion "
                    "must declare length_equals or item_pointer/item_equals/count_equals"
                )
            item_pointer = assertion["item_pointer"]
            count_equals = assertion["count_equals"]
            if type(count_equals) is not int or count_equals < 0:
                raise ClaimEvidenceError(
                    f"evidence {evidence_id} artifact {relative} count_equals must be a "
                    "nonnegative integer"
                )
            actual = 0
            for item_position, item in enumerate(collection):
                value = _json_pointer(
                    item,
                    item_pointer,
                    f"evidence {evidence_id} artifact {relative} {pointer} item "
                    f"{item_position}",
                )
                if (
                    type(value) is type(assertion["item_equals"])
                    and value == assertion["item_equals"]
                ):
                    actual += 1
            if actual != count_equals:
                raise ClaimEvidenceError(
                    f"evidence {evidence_id} artifact {relative} {pointer} expected "
                    f"{count_equals} items with {item_pointer}={assertion['item_equals']!r}, "
                    f"got {actual}"
                )
            collection_assertion_results.append(
                {
                    "pointer": pointer,
                    "item_pointer": item_pointer,
                    "item_equals": assertion["item_equals"],
                    "count_equals": count_equals,
                    "actual": actual,
                }
            )
        text_assertions = artifact.get("text_assertions", [])
        if not isinstance(text_assertions, list):
            raise ClaimEvidenceError(
                f"evidence {evidence_id} artifact {relative} text assertions must be a list"
            )
        text_assertion_results: list[dict[str, Any]] = []
        if text_assertions:
            try:
                text = path.read_text()
            except OSError as exc:
                raise ClaimEvidenceError(
                    f"cannot read evidence {evidence_id} artifact {relative}: {exc}"
                ) from exc
            for assertion_position, raw_assertion in enumerate(text_assertions):
                assertion = _require_object(
                    raw_assertion,
                    f"evidence {evidence_id} artifact {relative} text assertion {assertion_position}",
                )
                needle = _require_string(
                    assertion.get("contains"),
                    f"evidence {evidence_id} artifact {relative} text assertion contains",
                )
                minimum = assertion.get("minimum_occurrences", 1)
                if type(minimum) is not int or minimum <= 0:
                    raise ClaimEvidenceError(
                        f"evidence {evidence_id} artifact {relative} minimum_occurrences "
                        "must be a positive integer"
                    )
                actual = text.count(needle)
                if actual < minimum:
                    raise ClaimEvidenceError(
                        f"evidence {evidence_id} artifact {relative} expected at least "
                        f"{minimum} occurrences of {needle!r}, got {actual}"
                    )
                text_assertion_results.append(
                    {"contains": needle, "minimum_occurrences": minimum, "actual": actual}
                )
        resolved.append(
            {
                "path": relative,
                "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                "json_assertions": assertion_results,
                "collection_assertions": collection_assertion_results,
                "text_assertions": text_assertion_results,
            }
        )
    return resolved


def _resolve_active_evidence(
    evidence_id: str,
    definition: dict[str, Any],
    root: Path,
    ledgers: dict[str, dict[str, dict[str, Any]]],
) -> dict[str, Any]:
    route = _require_string(definition.get("route"), f"evidence {evidence_id} route")
    ledger_name, separator, route_name = route.partition("/")
    if not separator or ledger_name not in ledgers or not route_name:
        raise ClaimEvidenceError(f"evidence {evidence_id} has invalid route: {route}")
    item = ledgers[ledger_name].get(route_name)
    if item is None:
        raise ClaimEvidenceError(f"evidence {evidence_id} route was not produced: {route}")
    if item.get("ok") is not True or item.get("returncode") != 0:
        raise ClaimEvidenceError(f"evidence {evidence_id} route did not pass: {route}")
    stdout = _recorded_path(root, item.get("stdout_path"), f"evidence {evidence_id} stdout")
    stderr = _recorded_path(root, item.get("stderr_path"), f"evidence {evidence_id} stderr")
    return {
        "id": evidence_id,
        "route": route,
        "status": "resolved",
        "stdout": stdout,
        "stderr": stderr,
        "artifacts": _validate_artifacts(root, definition.get("artifacts"), evidence_id),
    }


def _validated_claim_contract(
    claims: dict[str, Any],
) -> tuple[
    str,
    dict[str, dict[str, Any]],
    list[tuple[str, list[str], list[str], list[str]]],
    dict[str, tuple[str, ...]],
]:
    if claims.get("schema_version") != 2:
        raise ClaimEvidenceError("claims.json must use schema_version=2")
    claim_set = _require_string(claims.get("claim_set"), "claim_set")
    if claims.get("verification_profiles") != list(VERIFICATION_PROFILES):
        raise ClaimEvidenceError(
            "claims.json verification_profiles must be ['full', 'extended']"
        )
    catalog = _require_object(claims.get("evidence_catalog"), "evidence_catalog")
    raw_claims = claims.get("claims")
    if not isinstance(raw_claims, list) or not raw_claims:
        raise ClaimEvidenceError("claims must be a non-empty list")

    canonical = canonical_route_profiles()
    referenced: set[str] = set()
    normalized_claims: list[tuple[str, list[str], list[str], list[str]]] = []
    claim_ids: set[str] = set()
    for position, raw_claim in enumerate(raw_claims):
        claim = _require_object(raw_claim, f"claim {position}")
        claim_id = _require_string(claim.get("id"), f"claim {position} id")
        if claim_id in claim_ids:
            raise ClaimEvidenceError(f"duplicate claim ID: {claim_id}")
        claim_ids.add(claim_id)
        _require_string(claim.get("claim"), f"claim {claim_id} text")
        refs = claim.get("evidence")
        if not isinstance(refs, list) or not refs:
            raise ClaimEvidenceError(f"claim {claim_id} must declare evidence references")
        if any(not isinstance(ref, str) or not ref for ref in refs):
            raise ClaimEvidenceError(f"claim {claim_id} has an invalid evidence reference")
        if len(set(refs)) != len(refs):
            raise ClaimEvidenceError(f"claim {claim_id} repeats an evidence reference")
        missing = [ref for ref in refs if ref not in catalog]
        if missing:
            raise ClaimEvidenceError(
                f"claim {claim_id} references unknown evidence: {', '.join(missing)}"
            )
        supplemental_refs = claim.get("supplemental_evidence", [])
        if not isinstance(supplemental_refs, list) or any(
            not isinstance(ref, str) or not ref for ref in supplemental_refs
        ):
            raise ClaimEvidenceError(
                f"claim {claim_id} supplemental_evidence must be a string list"
            )
        if len(set(supplemental_refs)) != len(supplemental_refs):
            raise ClaimEvidenceError(
                f"claim {claim_id} repeats a supplemental evidence reference"
            )
        overlap = sorted(set(refs) & set(supplemental_refs))
        if overlap:
            raise ClaimEvidenceError(
                f"claim {claim_id} evidence is both required and supplemental: "
                f"{', '.join(overlap)}"
            )
        missing_supplemental = [ref for ref in supplemental_refs if ref not in catalog]
        if missing_supplemental:
            raise ClaimEvidenceError(
                f"claim {claim_id} references unknown supplemental evidence: "
                f"{', '.join(missing_supplemental)}"
            )
        referenced.update(refs)
        referenced.update(supplemental_refs)
        theorem_surface = claim.get("theorem_surface", [])
        if not isinstance(theorem_surface, list) or any(
            not isinstance(name, str) or not name for name in theorem_surface
        ):
            raise ClaimEvidenceError(f"claim {claim_id} theorem_surface must be a string list")
        if len(set(theorem_surface)) != len(theorem_surface):
            raise ClaimEvidenceError(f"claim {claim_id} repeats a theorem_surface entry")
        references_proof_report = False
        for ref in refs:
            artifacts = _require_object(catalog[ref], f"evidence {ref}").get(
                "artifacts", []
            )
            if not isinstance(artifacts, list):
                raise ClaimEvidenceError(f"evidence {ref} artifacts must be a list")
            for position, artifact in enumerate(artifacts):
                artifact_object = _require_object(
                    artifact, f"evidence {ref} artifact {position}"
                )
                references_proof_report = references_proof_report or (
                    artifact_object.get("path")
                    == "artifact-check/proof-report.json"
                )
        if references_proof_report and not theorem_surface:
            raise ClaimEvidenceError(
                f"claim {claim_id} references proof-report evidence without theorem_surface"
            )
        normalized_claims.append((claim_id, refs, supplemental_refs, theorem_surface))

    unreferenced = sorted(set(catalog) - referenced)
    if unreferenced:
        raise ClaimEvidenceError(
            f"evidence catalog contains unreferenced entries: {', '.join(unreferenced)}"
        )
    typed_catalog: dict[str, dict[str, Any]] = {}
    for evidence_id, raw_definition in catalog.items():
        definition = _require_object(raw_definition, f"evidence {evidence_id}")
        typed_catalog[evidence_id] = definition
        route = _require_string(definition.get("route"), f"evidence {evidence_id} route")
        if route not in canonical:
            raise ClaimEvidenceError(
                f"evidence {evidence_id} references stale or unknown route: {route}"
            )
        required_profiles = definition.get("required_profiles")
        if not isinstance(required_profiles, list) or not required_profiles:
            raise ClaimEvidenceError(
                f"evidence {evidence_id} must declare non-empty required_profiles"
            )
        if any(profile_name not in VERIFICATION_PROFILES for profile_name in required_profiles):
            raise ClaimEvidenceError(f"evidence {evidence_id} has invalid required_profiles")
        if len(set(required_profiles)) != len(required_profiles):
            raise ClaimEvidenceError(f"evidence {evidence_id} repeats a required profile")
        unavailable = set(required_profiles) - set(canonical[route])
        if unavailable:
            raise ClaimEvidenceError(
                f"evidence {evidence_id} is required where route {route} is unavailable"
            )
    return claim_set, typed_catalog, normalized_claims, canonical


def claim_contract_summary(claims: dict[str, Any], profile: str) -> dict[str, Any]:
    if profile not in PROFILES:
        raise ClaimEvidenceError(f"unsupported review profile: {profile}")
    _, catalog, normalized_claims, _ = _validated_claim_contract(claims)
    return {
        "claim_count": len(normalized_claims),
        "claim_ids": [claim_id for claim_id, _, _, _ in normalized_claims],
        "required_evidence_references": sum(
            profile in catalog[evidence_id]["required_profiles"]
            for _, refs, _, _ in normalized_claims
            for evidence_id in refs
        ),
        "supplemental_evidence_references": sum(
            profile in catalog[evidence_id]["required_profiles"]
            for _, _, supplemental_refs, _ in normalized_claims
            for evidence_id in supplemental_refs
        ),
        "theorem_surface_entries": sum(
            len(theorem_surface) for _, _, _, theorem_surface in normalized_claims
        ),
    }


def claim_json_assertion_equals(
    claims: dict[str, Any], evidence_id: str, artifact_path: str, pointer: str
) -> Any:
    _, catalog, _, _ = _validated_claim_contract(claims)
    if evidence_id not in catalog:
        raise ClaimEvidenceError(f"unknown evidence entry: {evidence_id}")
    matches = [
        assertion["equals"]
        for artifact in catalog[evidence_id].get("artifacts", [])
        if artifact.get("path") == artifact_path
        for assertion in artifact.get("json_assertions", [])
        if assertion.get("pointer") == pointer and "equals" in assertion
    ]
    if len(matches) != 1:
        raise ClaimEvidenceError(
            f"evidence {evidence_id} must declare exactly one equals assertion for "
            f"{artifact_path} {pointer}"
        )
    return matches[0]


def verify_claim_evidence(
    claims: dict[str, Any],
    profile: str,
    results_root: Path,
    outer_results: Any,
    artifact_results: Any,
    claims_sha256: str,
) -> dict[str, Any]:
    if profile not in PROFILES:
        raise ClaimEvidenceError(f"unsupported review profile: {profile}")
    if not isinstance(claims_sha256, str) or not SHA256_RE.fullmatch(claims_sha256):
        raise ClaimEvidenceError("claims SHA-256 is invalid")
    claim_set, catalog, normalized_claims, _ = _validated_claim_contract(claims)

    outer_index = _result_index(outer_results, "outer")
    artifact_index = _result_index(artifact_results, "artifact-check")
    outer_names = list(outer_index)
    expected_outer = list(expected_outer_routes(profile))
    if outer_names != expected_outer:
        raise ClaimEvidenceError(
            f"outer route plan mismatch: expected {expected_outer}, got {outer_names}"
        )
    artifact_names = list(artifact_index)
    expected_artifact = list(expected_artifact_routes(profile))
    if artifact_names != expected_artifact:
        raise ClaimEvidenceError(
            f"artifact-check route plan mismatch: expected {expected_artifact}, "
            f"got {artifact_names}"
        )
    ledgers = {"outer": outer_index, "artifact-check": artifact_index}
    resolution_cache: dict[str, dict[str, Any]] = {}
    report_claims: list[dict[str, Any]] = []
    resolved_reference_count = 0
    resolved_supplemental_reference_count = 0
    proof_report_cache: dict[str, Any] | None = None
    for claim_id, refs, supplemental_refs, theorem_surface in normalized_claims:
        evidence_results: list[dict[str, Any]] = []
        for evidence_id in refs:
            definition = catalog[evidence_id]
            route = definition["route"]
            required_profiles = definition["required_profiles"]
            if profile not in required_profiles:
                evidence_results.append(
                    {
                        "id": evidence_id,
                        "route": route,
                        "status": "not-required-in-profile",
                        "required_profiles": list(required_profiles),
                    }
                )
                continue
            if evidence_id not in resolution_cache:
                resolution_cache[evidence_id] = _resolve_active_evidence(
                    evidence_id, definition, results_root, ledgers
                )
            evidence_results.append(resolution_cache[evidence_id])
            resolved_reference_count += 1
        supplemental_results: list[dict[str, Any]] = []
        for evidence_id in supplemental_refs:
            definition = catalog[evidence_id]
            route = definition["route"]
            required_profiles = definition["required_profiles"]
            if profile not in required_profiles:
                supplemental_results.append(
                    {
                        "id": evidence_id,
                        "route": route,
                        "status": "not-run-in-profile",
                        "available_profiles": list(required_profiles),
                    }
                )
                continue
            if evidence_id not in resolution_cache:
                resolution_cache[evidence_id] = _resolve_active_evidence(
                    evidence_id, definition, results_root, ledgers
                )
            supplemental_results.append(resolution_cache[evidence_id])
            resolved_supplemental_reference_count += 1
        active = [item for item in evidence_results if item["status"] == "resolved"]
        if profile in VERIFICATION_PROFILES and not active:
            raise ClaimEvidenceError(
                f"claim {claim_id} has no evidence available in {profile} profile"
            )
        status = "verified" if profile in VERIFICATION_PROFILES else (
            "partial" if active else "not-evaluated"
        )
        theorem_results: list[dict[str, str]] = []
        if theorem_surface:
            proof_refs = [
                ref
                for ref in refs
                if any(
                    artifact.get("path") == "artifact-check/proof-report.json"
                    for artifact in catalog[ref].get("artifacts", [])
                )
            ]
            if not proof_refs:
                raise ClaimEvidenceError(
                    f"claim {claim_id} declares theorem_surface without proof-report evidence"
                )
            if proof_report_cache is None:
                proof_path = _bundle_path(
                    results_root, "artifact-check/proof-report.json", "proof report"
                )
                try:
                    proof_document = json.loads(proof_path.read_text())
                except (OSError, json.JSONDecodeError) as exc:
                    raise ClaimEvidenceError(f"cannot read proof report: {exc}") from exc
                proof_report_cache = _require_object(proof_document, "proof report")
            theorem_index = _require_object(
                proof_report_cache.get("theorem_index"), "proof report theorem_index"
            )
            for qualified_name in theorem_surface:
                module_name, separator, theorem_name = qualified_name.rpartition(".")
                if not separator or not module_name or not theorem_name:
                    raise ClaimEvidenceError(
                        f"claim {claim_id} has invalid qualified theorem name: {qualified_name}"
                    )
                matching_files = [
                    file_name
                    for file_name, names in theorem_index.items()
                    if Path(file_name).stem == module_name
                    and isinstance(names, list)
                    and theorem_name in names
                ]
                if len(matching_files) != 1:
                    raise ClaimEvidenceError(
                        f"claim {claim_id} theorem does not resolve uniquely: {qualified_name}"
                    )
                theorem_results.append(
                    {"name": qualified_name, "file": matching_files[0], "status": "resolved"}
                )
        report_claims.append(
            {
                "id": claim_id,
                "status": status,
                "theorem_surface": theorem_results,
                "evidence": evidence_results,
                "supplemental_evidence": supplemental_results,
            }
        )

    verified_count = sum(item["status"] == "verified" for item in report_claims)
    contract = claim_contract_summary(claims, profile)
    return {
        "schema_version": 1,
        "claim_set": claim_set,
        "claims_sha256": claims_sha256,
        "profile": profile,
        "ok": profile not in VERIFICATION_PROFILES or verified_count == len(report_claims),
        "summary": {
            **contract,
            "verified_claims": verified_count,
            "resolved_evidence_references": resolved_reference_count,
            "resolved_supplemental_evidence_references": (
                resolved_supplemental_reference_count
            ),
            "resolved_theorem_surface_entries": sum(
                len(item["theorem_surface"]) for item in report_claims
            ),
        },
        "claims": report_claims,
    }
