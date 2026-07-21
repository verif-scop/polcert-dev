#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import secrets
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from archive_full_review import (
    EvidenceError,
    EXPECTED_ARTIFACT_CHECKS,
    DEFAULT_BUILD_METADATA,
    DEFAULT_LOCK,
    DEFAULT_MANIFEST,
    repository_static_hashes,
    sha256,
    validate_compact_v2,
    validate_evidence_against_raw,
)
from claim_evidence import ClaimEvidenceError, claim_json_assertion_equals


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVIDENCE = ROOT / "evidence" / "2026-07-21-v3-full-review.json"
DEFAULT_RECORD = ROOT / "publication" / "publication-record.json"
MANIFEST = ROOT / "manifest.json"
IMAGE_ID_RE = re.compile(r"^sha256:[0-9a-f]{64}$")
REGISTRY_RE = re.compile(r"^(?:localhost|[a-z0-9][a-z0-9.-]*(?::[0-9]+)?)$")
REPOSITORY_SEGMENT_RE = re.compile(r"^[a-z0-9]+(?:[._-][a-z0-9]+)*$")
TAG_RE = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.-]{0,127}$")
MOVING_TAGS = {"latest", "dev", "edge", "main", "master", "nightly", "snapshot", "stable"}


class PublicationError(RuntimeError):
    pass


def parse_registry_reference(reference: str) -> tuple[str, str, str]:
    if not reference:
        raise PublicationError("--registry-ref is required; no default registry is used")
    if "@" in reference:
        raise PublicationError(
            "--registry-ref must be an explicit versioned tag; the immutable digest is recorded after push"
        )
    slash = reference.find("/")
    colon = reference.rfind(":")
    if slash <= 0 or colon <= slash:
        raise PublicationError(
            "registry reference must include an explicit registry host, repository, and versioned tag"
        )
    registry = reference[:slash]
    repository_path = reference[slash + 1 : colon]
    tag = reference[colon + 1 :]
    if not REGISTRY_RE.fullmatch(registry) or (
        registry != "localhost" and "." not in registry and ":" not in registry
    ):
        raise PublicationError("registry host must be explicit, such as ghcr.io or registry.example.org:5000")
    segments = repository_path.split("/")
    if not segments or any(not REPOSITORY_SEGMENT_RE.fullmatch(segment) for segment in segments):
        raise PublicationError("repository path must be nonempty and lowercase")
    if not TAG_RE.fullmatch(tag):
        raise PublicationError("registry tag has invalid Docker reference syntax")
    if tag.lower() in MOVING_TAGS:
        raise PublicationError(f"moving registry tag is not allowed: {tag}")
    return registry, f"{registry}/{repository_path}", tag


def load_review_evidence(path: Path) -> tuple[dict[str, Any], str]:
    try:
        raw = path.read_bytes()
        evidence = json.loads(raw)
    except (OSError, json.JSONDecodeError) as exc:
        raise PublicationError(f"cannot read review evidence {path}: {exc}") from exc
    schema_version = evidence.get("schema_version")
    if schema_version not in (1, 2):
        raise PublicationError("review evidence schema_version must be 1 or 2")
    review = evidence.get("review", {})
    if review.get("ok") is not True:
        raise PublicationError("review evidence does not record a successful review")
    if review.get("profile") != "full":
        raise PublicationError("review evidence must record the full profile")
    if review.get("network") != "none":
        raise PublicationError("review evidence must record an offline network=none run")
    try:
        manifest = json.loads(MANIFEST.read_text())
        claims = json.loads((ROOT / "claims.json").read_text())
        lock = json.loads((ROOT / "locks" / "dependency-lock.json").read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise PublicationError(f"cannot read artifact publication inputs: {exc}") from exc
    expected_source = (
        lock.get("source", {}) if schema_version == 1 else manifest.get("polcert", {})
    )
    source = evidence.get("source", {})
    for field in ("tag", "commit", "tree"):
        if source.get(field) != expected_source.get(field):
            raise PublicationError(
                f"review evidence source {field} does not match the State.eq manifest"
            )

    proof_report = evidence.get("proof_report", {})
    proof_hole_counts = (
        "admitted_count",
        "abort_count",
        "extraction_axiom_count",
        "missing_route_theorem_count",
    )
    for field in proof_hole_counts:
        if proof_report.get(field) != 0:
            raise PublicationError(f"review evidence proof report requires {field}=0")

    capability = evidence.get("capability_results", {})
    expected_artifact_subchecks = (
        18 if schema_version == 1 else len(EXPECTED_ARTIFACT_CHECKS)
    )
    if capability.get("artifact_subchecks") != expected_artifact_subchecks:
        raise PublicationError(
            f"review evidence must record artifact_subchecks={expected_artifact_subchecks}"
        )
    if capability.get("artifact_subchecks_passed") != expected_artifact_subchecks:
        raise PublicationError(
            "review evidence must record "
            f"artifact_subchecks_passed={expected_artifact_subchecks}"
        )
    if schema_version == 1:
        expected_compatibility_checks = 114
    else:
        try:
            expected_compatibility_checks = claim_json_assertion_equals(
                claims,
                "artifact-check/capability-matrix",
                "artifact-check/capability-matrix.json",
                "/summary/compatibility_checks",
            )
        except ClaimEvidenceError as exc:
            raise PublicationError(f"invalid capability claim contract: {exc}") from exc
    if capability.get("pluto_compat_checks") != expected_compatibility_checks:
        raise PublicationError(
            "review evidence must record "
            f"pluto_compat_checks={expected_compatibility_checks}"
        )
    strict = capability.get("strict_loop_suite", {})
    if strict.get("total") != 62 or strict.get("passed") != 62:
        raise PublicationError("review evidence must record strict_loop_suite passed=total=62")
    required_suites = (
        "iss_suite",
        "parallel_current_suite",
        "vector_current_suite",
        "second_level_suite",
        "diamond_suite",
    )
    for suite in required_suites:
        if capability.get(suite) != "PASS":
            raise PublicationError(f"review evidence must record {suite}=PASS")

    image = evidence.get("images", {}).get("artifact", {})
    image_id = image.get("id")
    if not isinstance(image_id, str) or not IMAGE_ID_RE.fullmatch(image_id):
        raise PublicationError("review evidence has no valid artifact image ID")
    local_reference = image.get("reference")
    if not isinstance(local_reference, str) or not local_reference:
        raise PublicationError("review evidence has no local artifact image reference")
    candidate_reference = manifest.get("images", {}).get("default_candidate", {}).get("reference")
    if local_reference == candidate_reference and schema_version != 2:
        raise PublicationError("candidate review evidence must use schema_version=2")
    expected_reference = (
        manifest.get("images", {}).get("dependency_lock_origin", {}).get("reference")
        if schema_version == 1
        else candidate_reference
    )
    if local_reference != expected_reference:
        raise PublicationError(
            "review evidence image reference does not match its manifest role"
        )
    if schema_version == 2:
        try:
            validate_compact_v2(
                evidence,
                manifest,
                sha256((ROOT / "locks" / "dependency-lock.json").read_bytes()),
                repository_static_hashes(
                    ROOT / "manifest.json", ROOT / "locks" / "dependency-lock.json"
                ),
                claims,
            )
        except (EvidenceError, OSError) as exc:
            raise PublicationError(str(exc)) from exc
    return evidence, hashlib.sha256(raw).hexdigest()


def run_docker(docker_bin: str, arguments: list[str], *, capture: bool) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            [docker_bin, *arguments],
            text=True,
            capture_output=capture,
            check=False,
        )
    except OSError as exc:
        raise PublicationError(f"cannot execute Docker command: {exc}") from exc


def inspect_image(docker_bin: str, reference: str) -> dict[str, Any]:
    result = run_docker(docker_bin, ["image", "inspect", reference], capture=True)
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise PublicationError(f"cannot inspect image {reference}: {detail or f'exit {result.returncode}'}")
    try:
        payload = json.loads(result.stdout)
        image = payload[0]
    except (json.JSONDecodeError, IndexError, TypeError) as exc:
        raise PublicationError(f"Docker inspect returned invalid JSON for {reference}") from exc
    image_id = image.get("Id")
    repo_digests = image.get("RepoDigests") or []
    if not isinstance(image_id, str) or not IMAGE_ID_RE.fullmatch(image_id):
        raise PublicationError(f"Docker inspect returned an invalid image ID for {reference}")
    if not isinstance(repo_digests, list) or any(not isinstance(item, str) for item in repo_digests):
        raise PublicationError(f"Docker inspect returned invalid RepoDigests for {reference}")
    return {"id": image_id, "repo_digests": repo_digests}



def push_digest(output: str, repository: str) -> tuple[str, str]:
    matches = set(
        re.findall(r"(?m)^digest:\s*(sha256:[0-9a-f]{64})(?:\s|$)", output)
    )
    if not matches:
        raise PublicationError(f"docker push returned no manifest digest for {repository}")
    if len(matches) != 1:
        raise PublicationError(f"docker push returned conflicting digests for {repository}")
    digest = next(iter(matches))
    return digest, f"{repository}@{digest}"


def inspect_remote_digest(docker_bin: str, reference: str) -> str:
    result = run_docker(
        docker_bin,
        ["buildx", "imagetools", "inspect", reference],
        capture=True,
    )
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        raise PublicationError(
            f"cannot inspect registry manifest {reference}: "
            f"{detail or f'exit {result.returncode}'}"
        )
    matches = set(
        re.findall(r"(?m)^Digest:\s*(sha256:[0-9a-f]{64})\s*$", result.stdout)
    )
    if len(matches) != 1:
        raise PublicationError(
            f"registry inspection returned no unique digest for {reference}"
        )
    return next(iter(matches))


def atomic_write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        raise PublicationError(f"publication record already exists: {path}")
    fd, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "w") as handle:
            json.dump(value, handle, indent=2, sort_keys=True)
            handle.write("\n")
            handle.flush()
            os.fsync(handle.fileno())
        try:
            os.link(temporary, path)
        except FileExistsError as exc:
            raise PublicationError(f"publication record already exists: {path}") from exc
        temporary.unlink()
        directory_fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def publication_record(
    evidence: dict[str, Any],
    evidence_path: Path,
    evidence_sha256: str,
    local_reference: str,
    local_image_id: str,
    registry_reference: str,
    registry_repository: str,
    registry_tag: str,
    digest: str,
    immutable_reference: str,
    staging_reference: str,
) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "published_at": datetime.now(timezone.utc).isoformat(),
        "review": {
            "evidence": str(evidence_path.resolve()),
            "evidence_sha256": evidence_sha256,
            "profile": evidence["review"]["profile"],
            "network": evidence["review"]["network"],
            "ok": evidence["review"]["ok"],
        },
        "source": evidence.get("source", {}),
        "local_image": {
            "reference": local_reference,
            "id": local_image_id,
        },
        "registry": {
            "tag_reference": registry_reference,
            "repository": registry_repository,
            "tag": registry_tag,
            "digest": digest,
            "immutable_reference": immutable_reference,
            "staging_reference": staging_reference,
            "staging_digest": digest,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Publish only a Docker image whose ID matches successful archived full-review evidence."
    )
    parser.add_argument("--registry-ref", required=True)
    parser.add_argument("--review-evidence", type=Path, default=DEFAULT_EVIDENCE)
    parser.add_argument(
        "--review-results",
        type=Path,
        help="Untouched raw full-review directory; mandatory for schema-v2 publication",
    )
    parser.add_argument(
        "--build-metadata", type=Path, default=DEFAULT_BUILD_METADATA
    )
    parser.add_argument("--local-image", help="Override the evidence's local reference; the image ID must still match")
    parser.add_argument("--record", type=Path, default=DEFAULT_RECORD)
    parser.add_argument("--docker-bin", default="docker", help=argparse.SUPPRESS)
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    try:
        _, repository, tag = parse_registry_reference(args.registry_ref)
        evidence, evidence_sha256 = load_review_evidence(args.review_evidence)
        if evidence.get("schema_version") == 2 and args.review_results is None:
            raise PublicationError(
                "schema-v2 publication requires --review-results so compact evidence "
                "is recomputed from the raw bundle"
            )
        reviewed = evidence["images"]["artifact"]
        reviewed_id = reviewed["id"]
        reviewed_hex = reviewed_id[len("sha256:") :]
        if evidence.get("schema_version") == 2 and not tag.endswith(reviewed_hex):
            raise PublicationError(
                "schema-v2 registry tag must end with the complete reviewed image ID"
            )
        local_reference = args.local_image or reviewed["reference"]
        if args.record.exists():
            raise PublicationError(f"publication record already exists: {args.record}")
        local = inspect_image(args.docker_bin, local_reference)
        if local["id"] != reviewed_id:
            raise PublicationError(
                "local image ID does not match review evidence: "
                f"expected {reviewed_id}, got {local['id']}"
            )
        if evidence.get("schema_version") == 2:
            try:
                validate_evidence_against_raw(
                    evidence,
                    args.review_results,
                    DEFAULT_MANIFEST,
                    DEFAULT_LOCK,
                    args.build_metadata,
                    reviewed["reference"],
                    reviewed_id,
                )
            except (EvidenceError, OSError) as exc:
                raise PublicationError(
                    f"raw review bundle validation failed: {exc}"
                ) from exc

        staging_reference = (
            f"{repository}:polcert-stage-{reviewed_hex[:16]}-"
            f"{os.getpid()}-{secrets.token_hex(8)}"
        )
        immutable_placeholder = f"{repository}@<digest-from-staging-push>"
        plan = {
            "dry_run": args.dry_run,
            "review_evidence": str(args.review_evidence.resolve()),
            "review_evidence_sha256": evidence_sha256,
            "review_results": (
                str(args.review_results.resolve()) if args.review_results else None
            ),
            "local_reference": local_reference,
            "reviewed_image_id": reviewed_id,
            "registry_tag_reference": args.registry_ref,
            "staging_reference": staging_reference,
            "record": str(args.record.resolve()),
            "commands": [
                [args.docker_bin, "tag", reviewed_id, staging_reference],
                [args.docker_bin, "push", staging_reference],
                [args.docker_bin, "pull", immutable_placeholder],
                [
                    args.docker_bin,
                    "buildx",
                    "imagetools",
                    "create",
                    "--prefer-index=false",
                    "--tag",
                    args.registry_ref,
                    immutable_placeholder,
                ],
                [
                    args.docker_bin,
                    "buildx",
                    "imagetools",
                    "inspect",
                    args.registry_ref,
                ],
            ],
        }
        if args.dry_run:
            print(json.dumps(plan, indent=2, sort_keys=True))
            return 0

        tagged = run_docker(
            args.docker_bin, ["tag", reviewed_id, staging_reference], capture=True
        )
        if tagged.returncode != 0:
            detail = (tagged.stderr or tagged.stdout).strip()
            raise PublicationError(f"docker tag failed: {detail or f'exit {tagged.returncode}'}")
        tagged_image = inspect_image(args.docker_bin, staging_reference)
        if tagged_image["id"] != reviewed_id:
            raise PublicationError("tagged image ID changed before push")

        pushed = run_docker(
            args.docker_bin, ["push", staging_reference], capture=True
        )
        if pushed.returncode != 0:
            raise PublicationError(f"docker push failed with exit {pushed.returncode}")
        digest, immutable_reference = push_digest(
            (pushed.stdout or "") + "\n" + (pushed.stderr or ""), repository
        )
        pulled = run_docker(
            args.docker_bin, ["pull", immutable_reference], capture=True
        )
        if pulled.returncode != 0:
            detail = (pulled.stderr or pulled.stdout).strip()
            raise PublicationError(
                f"docker pull of pushed immutable digest failed: "
                f"{detail or f'exit {pulled.returncode}'}"
            )
        immutable = inspect_image(args.docker_bin, immutable_reference)
        if immutable["id"] != reviewed_id:
            raise PublicationError(
                "pushed immutable digest does not resolve to reviewed image ID"
            )
        promoted = run_docker(
            args.docker_bin,
            [
                "buildx",
                "imagetools",
                "create",
                "--prefer-index=false",
                "--tag",
                args.registry_ref,
                immutable_reference,
            ],
            capture=True,
        )
        if promoted.returncode != 0:
            detail = (promoted.stderr or promoted.stdout).strip()
            raise PublicationError(
                f"registry digest promotion failed: "
                f"{detail or f'exit {promoted.returncode}'}"
            )
        published_digest = inspect_remote_digest(args.docker_bin, args.registry_ref)
        if published_digest != digest:
            raise PublicationError(
                "published tag digest differs from the reviewed staging digest"
            )
        record = publication_record(
            evidence,
            args.review_evidence,
            evidence_sha256,
            local_reference,
            reviewed_id,
            args.registry_ref,
            repository,
            tag,
            digest,
            immutable_reference,
            staging_reference,
        )
        atomic_write_json(args.record, record)
        print(json.dumps(record, indent=2, sort_keys=True))
        return 0
    except PublicationError as exc:
        print(f"publication refused: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
