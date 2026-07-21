#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Protocol


ARTIFACT_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EVIDENCE = ARTIFACT_ROOT / "evidence" / "2026-07-18-full-review.json"
DEFAULT_MANIFEST = ARTIFACT_ROOT / "manifest.json"
DEFAULT_LOCK_DIR = ARTIFACT_ROOT / "locks"
APT_LOCK = "apt-packages.lock"
OPAM_PACKAGES_LOCK = "opam-packages.lock"
OPAM_EXPORT_LOCK = "opam-switch-full.export"
LOCK_JSON = "dependency-lock.json"

TREE_DIGEST_SCRIPT = r'''
import glob
import hashlib
import json
import os
import stat
import sys


def add_tree(paths, root):
    root = os.fsencode(root)
    paths.add(root)
    if not os.path.isdir(root) or os.path.islink(root):
        return
    for current, directories, files in os.walk(root, followlinks=False):
        current = os.fsencode(current)
        for name in directories:
            paths.add(os.path.join(current, os.fsencode(name)))
        for name in files:
            paths.add(os.path.join(current, os.fsencode(name)))


def add_field(digest, value):
    digest.update(len(value).to_bytes(8, "big"))
    digest.update(value)


mode = sys.argv[1]
paths = set()
if mode == "apt":
    add_tree(paths, "/var/lib/dpkg")
    for package_list in glob.glob("/var/lib/dpkg/info/*.list"):
        with open(package_list, "rb") as handle:
            for path in handle.read().splitlines():
                if path:
                    paths.add(path)
elif mode == "opam":
    add_tree(paths, "/root/.opam/polcert")
else:
    raise SystemExit(f"unknown tree digest mode: {mode}")

digest = hashlib.sha256()
for path in sorted(paths):
    add_field(digest, path)
    try:
        metadata = os.lstat(path)
    except FileNotFoundError:
        add_field(digest, b"missing")
        continue
    add_field(digest, stat.filemode(metadata.st_mode).encode())
    add_field(digest, str(metadata.st_uid).encode())
    add_field(digest, str(metadata.st_gid).encode())
    if stat.S_ISREG(metadata.st_mode):
        contents = hashlib.sha256()
        with open(path, "rb") as handle:
            while chunk := handle.read(1024 * 1024):
                contents.update(chunk)
        add_field(digest, b"file")
        add_field(digest, contents.digest())
    elif stat.S_ISLNK(metadata.st_mode):
        add_field(digest, b"symlink")
        add_field(digest, os.readlink(path))
    elif stat.S_ISDIR(metadata.st_mode):
        add_field(digest, b"directory")
    else:
        add_field(digest, b"other")
        add_field(digest, str(metadata.st_rdev).encode())

print(json.dumps({"entries": len(paths), "sha256": digest.hexdigest()}, sort_keys=True))
'''


class LockError(RuntimeError):
    pass


class Runner(Protocol):
    def run(self, arguments: list[str]) -> bytes: ...


@dataclass(frozen=True)
class DependencyState:
    apt_packages: bytes
    apt_filesystem_entries: int
    apt_filesystem_sha256: str
    opam_packages: bytes
    opam_switch_export: bytes
    opam_switch_tree_entries: int
    opam_switch_tree_sha256: str
    opam_binary_sha256: str
    os_release: bytes


class LocalRunner:
    def run(self, arguments: list[str]) -> bytes:
        return checked_command(arguments)


class DockerRunner:
    def __init__(self, docker_bin: str, image: str) -> None:
        self.docker_bin = docker_bin
        self.image = image

    def run(self, arguments: list[str]) -> bytes:
        return checked_command(
            [
                self.docker_bin,
                "run",
                "--rm",
                "--network",
                "none",
                "--entrypoint",
                arguments[0],
                self.image,
                *arguments[1:],
            ]
        )


def checked_command(arguments: list[str]) -> bytes:
    try:
        completed = subprocess.run(arguments, capture_output=True, check=False)
    except OSError as exc:
        raise LockError(f"cannot execute {arguments[0]}: {exc}") from exc
    if completed.returncode != 0:
        detail = completed.stderr.decode(errors="replace").strip()
        raise LockError(
            f"command failed ({completed.returncode}): {' '.join(arguments)}"
            + (f"\n{detail}" if detail else "")
        )
    return completed.stdout


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_lines(lines: list[str]) -> bytes:
    return ("\n".join(sorted(set(lines))) + "\n").encode()


def canonical_apt(raw: bytes) -> bytes:
    lines: list[str] = []
    for line in raw.decode().splitlines():
        parts = line.split("\t")
        if len(parts) != 3:
            raise LockError(f"invalid dpkg-query line: {line!r}")
        name, version, status = parts
        if status.startswith("ii "):
            if not name or not version:
                raise LockError(f"invalid installed dpkg package: {line!r}")
            lines.append(f"{name}\t{version}")
    if not lines:
        raise LockError("dpkg-query returned no installed packages")
    return canonical_lines(lines)


def canonical_opam_packages(raw: bytes) -> bytes:
    lines: list[str] = []
    for line in raw.decode().splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        parts = stripped.split()
        if len(parts) != 2:
            raise LockError(f"invalid opam package line: {line!r}")
        lines.append(f"{parts[0]}\t{parts[1]}")
    if not lines:
        raise LockError("opam list returned no installed packages")
    return canonical_lines(lines)


def parse_sha256sum(raw: bytes, expected_path: str) -> str:
    fields = raw.decode().strip().split()
    if len(fields) != 2 or fields[1] != expected_path or len(fields[0]) != 64:
        raise LockError("invalid sha256sum output for opam executable")
    try:
        int(fields[0], 16)
    except ValueError as exc:
        raise LockError("invalid opam executable SHA-256") from exc
    return fields[0]


def parse_tree_digest(raw: bytes, name: str) -> tuple[int, str]:
    try:
        result = json.loads(raw)
        entries = result["entries"]
        digest = result["sha256"]
    except (json.JSONDecodeError, KeyError, TypeError) as exc:
        raise LockError(f"invalid {name} tree digest output") from exc
    if not isinstance(entries, int) or entries <= 0:
        raise LockError(f"invalid {name} tree entry count")
    if not isinstance(digest, str) or len(digest) != 64:
        raise LockError(f"invalid {name} tree SHA-256")
    try:
        int(digest, 16)
    except ValueError as exc:
        raise LockError(f"invalid {name} tree SHA-256") from exc
    return entries, digest


def capture_state(runner: Runner) -> DependencyState:
    apt_raw = runner.run(
        [
            "dpkg-query",
            "-W",
            "-f=${binary:Package}\\t${Version}\\t${db:Status-Abbrev}\\n",
        ]
    )
    opam_raw = runner.run(
        ["opam", "list", "--switch=polcert", "--installed", "--columns=name,version"]
    )
    export_raw = runner.run(
        [
            "bash",
            "-lc",
            "set -euo pipefail; tmp=$(mktemp); trap 'rm -f \"$tmp\"' EXIT; "
            "opam switch export \"$tmp\" --switch=polcert --full >/dev/null; cat \"$tmp\"",
        ]
    )
    if not export_raw.startswith(b'opam-version: "2.0"'):
        raise LockError("opam full switch export has an unexpected header")
    opam_hash = parse_sha256sum(
        runner.run(["sha256sum", "/usr/local/bin/opam"]), "/usr/local/bin/opam"
    )
    os_release = runner.run(["cat", "/etc/os-release"])
    if b'ID=ubuntu' not in os_release or b'VERSION_ID="20.04"' not in os_release:
        raise LockError("unexpected operating system release")
    apt_entries, apt_digest = parse_tree_digest(
        runner.run(["python3", "-c", TREE_DIGEST_SCRIPT, "apt"]), "apt filesystem"
    )
    opam_entries, opam_digest = parse_tree_digest(
        runner.run(["python3", "-c", TREE_DIGEST_SCRIPT, "opam"]), "opam switch"
    )
    return DependencyState(
        apt_packages=canonical_apt(apt_raw),
        apt_filesystem_entries=apt_entries,
        apt_filesystem_sha256=apt_digest,
        opam_packages=canonical_opam_packages(opam_raw),
        opam_switch_export=export_raw,
        opam_switch_tree_entries=opam_entries,
        opam_switch_tree_sha256=opam_digest,
        opam_binary_sha256=opam_hash,
        os_release=os_release,
    )


def load_json(path: Path) -> dict[str, Any]:
    try:
        return json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise LockError(f"cannot read JSON {path}: {exc}") from exc


def inspect_image_id(docker_bin: str, image: str) -> str:
    raw = checked_command([docker_bin, "image", "inspect", image])
    try:
        value = json.loads(raw)[0]["Id"]
    except (json.JSONDecodeError, IndexError, KeyError, TypeError) as exc:
        raise LockError(f"invalid Docker inspect output for {image}") from exc
    if not isinstance(value, str) or not value.startswith("sha256:") or len(value) != 71:
        raise LockError(f"invalid Docker image ID for {image}")
    return value


def strict_review_evidence(path: Path) -> tuple[dict[str, Any], str]:
    sys.path.insert(0, str(ARTIFACT_ROOT / "bin"))
    try:
        from publish_reviewed_image import load_review_evidence
    except ImportError as exc:
        raise LockError("cannot import strict review evidence validator") from exc
    try:
        return load_review_evidence(path)
    except RuntimeError as exc:
        raise LockError(str(exc)) from exc


def file_entry(name: str, data: bytes) -> dict[str, Any]:
    return {"path": name, "sha256": sha256(data), "bytes": len(data)}


def create_lock(
    state: DependencyState,
    evidence: dict[str, Any],
    evidence_path: Path,
    evidence_sha256: str,
    image: str,
    image_id: str,
    manifest: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, bytes]]:
    try:
        evidence_reference = str(evidence_path.resolve().relative_to(ARTIFACT_ROOT))
    except ValueError:
        evidence_reference = str(evidence_path.resolve())
    files = {
        APT_LOCK: state.apt_packages,
        OPAM_PACKAGES_LOCK: state.opam_packages,
        OPAM_EXPORT_LOCK: state.opam_switch_export,
    }
    lock = {
        "schema_version": 1,
        "captured_at": datetime.now(timezone.utc).isoformat(),
        "purpose": "Fail-closed dependency state lock captured from the offline full-reviewed image",
        "origin": {
            "review_evidence": evidence_reference,
            "review_evidence_sha256": evidence_sha256,
            "reviewed_image_reference": image,
            "reviewed_image_id": image_id,
        },
        "source": {
            "tag": evidence["source"]["tag"],
            "commit": evidence["source"]["commit"],
            "tree": evidence["source"]["tree"],
        },
        "base_image": {
            "reference": manifest["pluto"]["base_image"],
            "registry_digest": manifest["pluto"]["base_image_digest"],
        },
        "state": {
            "apt_packages": {
                **file_entry(APT_LOCK, state.apt_packages),
                "count": len(state.apt_packages.decode().splitlines()),
            },
            "apt_filesystem": {
                "coverage": "dpkg database and all paths recorded by installed package lists",
                "entries": state.apt_filesystem_entries,
                "sha256": state.apt_filesystem_sha256,
            },
            "opam_packages": {
                **file_entry(OPAM_PACKAGES_LOCK, state.opam_packages),
                "count": len(state.opam_packages.decode().splitlines()),
            },
            "opam_switch_export": file_entry(OPAM_EXPORT_LOCK, state.opam_switch_export),
            "opam_switch_tree": {
                "coverage": "/root/.opam/polcert filesystem tree",
                "entries": state.opam_switch_tree_entries,
                "sha256": state.opam_switch_tree_sha256,
            },
            "opam_binary": {
                "path": "/usr/local/bin/opam",
                "sha256": state.opam_binary_sha256,
            },
            "os_release": {
                "path": "/etc/os-release",
                "sha256": sha256(state.os_release),
            },
        },
        "enforcement": {
            "fresh_build": "verify-image runs after the frozen source Dockerfile and before the reviewer wrapper image is built",
            "offline_review": "verify-local is the first reviewer gate",
            "resolution": "Package repositories remain external; drift is rejected after resolution rather than prevented before download",
        },
    }
    return lock, files


def atomic_write_lock_dir(output: Path, lock: dict[str, Any], files: dict[str, bytes]) -> None:
    output = output.resolve()
    if output.exists():
        raise LockError(f"lock output already exists: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{output.name}.", dir=output.parent))
    try:
        for name, data in files.items():
            (temporary / name).write_bytes(data)
        (temporary / LOCK_JSON).write_text(json.dumps(lock, indent=2, sort_keys=True) + "\n")
        for path in temporary.iterdir():
            with path.open("rb") as handle:
                os.fsync(handle.fileno())
        os.replace(temporary, output)
    except BaseException:
        shutil.rmtree(temporary, ignore_errors=True)
        raise


def compare_bytes(name: str, expected: bytes, actual: bytes) -> None:
    if expected == actual:
        return
    expected_lines = expected.decode(errors="replace").splitlines()
    actual_lines = actual.decode(errors="replace").splitlines()
    first = 0
    for first, pair in enumerate(zip(expected_lines, actual_lines), start=1):
        if pair[0] != pair[1]:
            break
    else:
        first = min(len(expected_lines), len(actual_lines)) + 1
    expected_line = expected_lines[first - 1] if first <= len(expected_lines) else "<missing>"
    actual_line = actual_lines[first - 1] if first <= len(actual_lines) else "<missing>"
    raise LockError(
        f"{name} differs at line {first}: expected {expected_line!r}, got {actual_line!r}"
    )


def validate_lock_context(lock: dict[str, Any], lock_path: Path, manifest_path: Path) -> None:
    manifest = load_json(manifest_path)
    manifest_origin = manifest.get("images", {}).get("dependency_lock_origin", {})
    lock_origin = lock.get("origin", {})
    if lock_origin.get("reviewed_image_reference") != manifest_origin.get("reference"):
        raise LockError("dependency lock origin image does not match manifest")
    if lock_origin.get("review_evidence") != manifest_origin.get("review_evidence"):
        raise LockError("dependency lock origin evidence does not match manifest")
    if lock.get("base_image", {}).get("reference") != manifest["pluto"]["base_image"]:
        raise LockError("dependency lock base image reference does not match manifest")
    if lock.get("base_image", {}).get("registry_digest") != manifest["pluto"]["base_image_digest"]:
        raise LockError("dependency lock base image digest does not match manifest")
    evidence_reference = lock.get("origin", {}).get("review_evidence")
    if not isinstance(evidence_reference, str) or not evidence_reference:
        raise LockError("dependency lock has no review evidence reference")
    evidence_path = Path(evidence_reference)
    if not evidence_path.is_absolute():
        evidence_path = manifest_path.parent / evidence_path
    if not evidence_path.is_file():
        raise LockError(f"dependency lock review evidence missing: {evidence_path}")
    if sha256(evidence_path.read_bytes()) != lock.get("origin", {}).get("review_evidence_sha256"):
        raise LockError("dependency lock review evidence checksum mismatch")
    evidence = load_json(evidence_path)
    for field in ("tag", "commit", "tree"):
        if lock.get("source", {}).get(field) != evidence.get("source", {}).get(field):
            raise LockError(
                f"dependency lock source {field} does not match origin evidence"
            )
    artifact_image = evidence.get("images", {}).get("artifact", {})
    if artifact_image.get("reference") != lock_origin.get("reviewed_image_reference"):
        raise LockError("dependency lock origin image differs from review evidence")
    if artifact_image.get("id") != lock_origin.get("reviewed_image_id"):
        raise LockError("dependency lock origin image ID differs from review evidence")
    for key in ("apt_packages", "opam_packages", "opam_switch_export"):
        entry = lock.get("state", {}).get(key, {})
        path = lock_path.parent / entry.get("path", "")
        if not path.is_file():
            raise LockError(f"dependency lock companion file missing: {path}")
        data = path.read_bytes()
        if sha256(data) != entry.get("sha256") or len(data) != entry.get("bytes"):
            raise LockError(f"dependency lock companion checksum mismatch: {path}")


def verify_state(state: DependencyState, lock_path: Path, manifest_path: Path) -> None:
    lock = load_json(lock_path)
    validate_lock_context(lock, lock_path, manifest_path)
    expected = lock["state"]
    compare_bytes(
        "apt package closure",
        (lock_path.parent / expected["apt_packages"]["path"]).read_bytes(),
        state.apt_packages,
    )
    compare_bytes(
        "opam package closure",
        (lock_path.parent / expected["opam_packages"]["path"]).read_bytes(),
        state.opam_packages,
    )
    compare_bytes(
        "opam full switch export",
        (lock_path.parent / expected["opam_switch_export"]["path"]).read_bytes(),
        state.opam_switch_export,
    )
    if (
        state.apt_filesystem_entries != expected["apt_filesystem"]["entries"]
        or state.apt_filesystem_sha256 != expected["apt_filesystem"]["sha256"]
    ):
        raise LockError("apt installed filesystem tree differs from dependency lock")
    if (
        state.opam_switch_tree_entries != expected["opam_switch_tree"]["entries"]
        or state.opam_switch_tree_sha256 != expected["opam_switch_tree"]["sha256"]
    ):
        raise LockError("opam switch filesystem tree differs from dependency lock")
    if state.opam_binary_sha256 != expected["opam_binary"]["sha256"]:
        raise LockError("opam executable SHA-256 differs from dependency lock")
    if sha256(state.os_release) != expected["os_release"]["sha256"]:
        raise LockError("operating system release differs from dependency lock")


def main() -> int:
    parser = argparse.ArgumentParser(description="Capture and verify the State.eq image dependency state lock.")
    subparsers = parser.add_subparsers(dest="command", required=True)

    capture = subparsers.add_parser("capture-image")
    capture.add_argument("--image", required=True)
    capture.add_argument("--review-evidence", type=Path, default=DEFAULT_EVIDENCE)
    capture.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    capture.add_argument("--output-dir", type=Path, default=DEFAULT_LOCK_DIR)
    capture.add_argument("--docker-bin", default="docker", help=argparse.SUPPRESS)

    verify_image = subparsers.add_parser("verify-image")
    verify_image.add_argument("--image", required=True)
    verify_image.add_argument("--lock", type=Path, default=DEFAULT_LOCK_DIR / LOCK_JSON)
    verify_image.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    verify_image.add_argument("--docker-bin", default="docker", help=argparse.SUPPRESS)

    verify_local = subparsers.add_parser("verify-local")
    verify_local.add_argument("--lock", type=Path, required=True)
    verify_local.add_argument("--manifest", type=Path, required=True)

    args = parser.parse_args()
    try:
        if args.command == "capture-image":
            evidence, evidence_sha256 = strict_review_evidence(args.review_evidence)
            image_id = inspect_image_id(args.docker_bin, args.image)
            expected_id = evidence["images"]["artifact"]["id"]
            if image_id != expected_id:
                raise LockError(
                    f"capture image ID does not match full-review evidence: expected {expected_id}, got {image_id}"
                )
            state = capture_state(DockerRunner(args.docker_bin, args.image))
            lock, files = create_lock(
                state,
                evidence,
                args.review_evidence,
                evidence_sha256,
                args.image,
                image_id,
                load_json(args.manifest),
            )
            atomic_write_lock_dir(args.output_dir, lock, files)
            print(f"dependency lock captured: {args.output_dir / LOCK_JSON}")
            return 0
        if args.command == "verify-image":
            inspect_image_id(args.docker_bin, args.image)
            verify_state(
                capture_state(DockerRunner(args.docker_bin, args.image)),
                args.lock,
                args.manifest,
            )
            print(f"dependency lock verified for image: {args.image}")
            return 0
        verify_state(capture_state(LocalRunner()), args.lock, args.manifest)
        print("dependency lock verified for local image state")
        return 0
    except LockError as exc:
        print(f"dependency lock failure: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
