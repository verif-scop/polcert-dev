#!/usr/bin/env python3
"""Build the small, reviewer-facing Zenodo upload from a frozen release tree."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import sys
import zipfile


SCRIPT_DIR = Path(__file__).resolve().parent
PACKAGE_DIR = SCRIPT_DIR.parent
REPO_ROOT = PACKAGE_DIR.parents[1]
DEFAULT_RELEASE_DIR = (
    REPO_ROOT
    / "output/releases/state-eq-polyhedral-verification-complete-2026-08-29-v10/final"
)
ZIP_TIMESTAMP = (2026, 8, 29, 0, 0, 0)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def verify_release(release_dir: Path, release: dict) -> None:
    require(release_dir.is_dir(), f"release directory is missing: {release_dir}")

    polcert = release["polcert"]
    docker = release["docker"]
    source_path = release_dir / polcert["source_archive"]
    docker_path = release_dir / docker["archive"]
    require(source_path.is_file(), f"source archive is missing: {source_path}")
    require(docker_path.is_file(), f"Docker archive is missing: {docker_path}")
    require(
        sha256(source_path) == polcert["source_archive_sha256"],
        "source archive SHA-256 does not match RELEASE.json",
    )
    require(
        sha256(docker_path) == docker["archive_sha256"],
        "Docker archive SHA-256 does not match RELEASE.json",
    )

    provenance = load_json(release_dir / "BUILD_PROVENANCE.json")
    expected_provenance = {
        "polcert_git_commit": polcert["commit"],
        "polcert_release_tag": polcert["tag"],
        "polcert_source_archive_sha256": polcert["source_archive_sha256"],
        "pluto_git_commit": release["pluto"]["validated_commit"],
        "pluto_buggy_git_commit": release["pluto"]["bug_witness_commit"],
    }
    require(
        provenance == expected_provenance,
        "BUILD_PROVENANCE.json does not match RELEASE.json",
    )

    inspect = load_json(release_dir / "docker-image-inspect.json")
    require(len(inspect) == 1, "docker-image-inspect.json must contain one image")
    require(inspect[0].get("Id") == docker["image_id"], "Docker image ID mismatch")
    require(docker["image"] in inspect[0].get("RepoTags", []), "Docker tag mismatch")

    ci = load_json(release_dir / f"github-actions-{release['ci']['run_id']}-metadata.json")
    require(ci.get("databaseId") == release["ci"]["run_id"], "CI run ID mismatch")
    require(ci.get("headSha") == polcert["commit"], "CI commit mismatch")
    require(ci.get("conclusion") == "success", "CI did not succeed")
    require(
        all(job.get("conclusion") == "success" for job in ci.get("jobs", [])),
        "at least one recorded CI job did not succeed",
    )

    results = load_json(release_dir / "polcert-artifact-check/artifact-results.json")
    checks = results.get("results", [])
    require(results.get("mode") == "full", "artifact result is not a full run")
    require(results.get("ok") is True, "artifact result reports failure")
    require(
        len(checks) == release["artifact_check"]["total"],
        "artifact result count does not match RELEASE.json",
    )
    require(all(check.get("ok") is True for check in checks), "an artifact check failed")
    require(
        len(checks) == release["artifact_check"]["passed"],
        "artifact passing count does not match RELEASE.json",
    )


def gzip_source(source: Path, destination: Path) -> None:
    with source.open("rb") as src, destination.open("wb") as raw_dst:
        with gzip.GzipFile(
            filename="", mode="wb", fileobj=raw_dst, compresslevel=9, mtime=0
        ) as dst:
            shutil.copyfileobj(src, dst, length=8 * 1024 * 1024)


def copy_or_link(source: Path, destination: Path, force_copy: bool) -> str:
    if not force_copy:
        try:
            os.link(source, destination)
            return "hard link"
        except OSError:
            pass
    shutil.copy2(source, destination)
    return "copy"


def zip_info(name: str, executable: bool = False) -> zipfile.ZipInfo:
    info = zipfile.ZipInfo(name, ZIP_TIMESTAMP)
    info.compress_type = zipfile.ZIP_DEFLATED
    mode = 0o100755 if executable else 0o100644
    info.external_attr = mode << 16
    info.create_system = 3
    return info


def add_file(archive: zipfile.ZipFile, source: Path, name: str) -> None:
    with source.open("rb") as src, archive.open(zip_info(name), "w") as dst:
        shutil.copyfileobj(src, dst, length=1024 * 1024)


def add_tree(archive: zipfile.ZipFile, source: Path, prefix: str) -> None:
    require(source.is_dir(), f"evidence directory is missing: {source}")
    for path in sorted(source.rglob("*")):
        if path.is_file():
            add_file(archive, path, f"{prefix}/{path.relative_to(source).as_posix()}")


def build_evidence_zip(release_dir: Path, destination: Path, release: dict) -> None:
    evidence_readme = """# PolCert v10 Frozen Evidence

`artifact-check/` is the complete 30-check result tree. `transformation-examples/`
contains the 62 strict-suite inputs, outputs, and diffs. `ci/` records the
exact-commit GitHub Actions run. The remaining files record local release
validation, image provenance, and hashes of the expanded pre-Zenodo tree.

Start with `artifact-check/artifact-results.json`, then follow each result's
stdout and stderr paths. The paths recorded by the container begin with
`/tmp/polcert-artifact-check`; the corresponding files are under
`artifact-check/` in this ZIP.
"""
    run_id = release["ci"]["run_id"]
    with zipfile.ZipFile(destination, "w", allowZip64=True) as archive:
        archive.writestr(zip_info("README.md"), evidence_readme.encode("utf-8"))
        for name in (
            "BUILD_PROVENANCE.json",
            "RELEASE_MANIFEST.md",
            "docker-image-inspect.json",
            "local-release-validation.log",
        ):
            add_file(archive, release_dir / name, name)
        add_file(
            archive,
            release_dir / "SHA256SUMS",
            "EXPANDED_RELEASE_SHA256SUMS",
        )
        add_file(
            archive,
            release_dir / f"github-actions-{run_id}-metadata.json",
            f"ci/github-actions-{run_id}-metadata.json",
        )
        add_file(
            archive,
            release_dir / f"github-actions-{run_id}.log",
            f"ci/github-actions-{run_id}.log",
        )
        add_tree(
            archive,
            release_dir / "polcert-artifact-check",
            "artifact-check",
        )
        add_tree(
            archive,
            release_dir / "polopt-generated-cases",
            "transformation-examples",
        )


def prepare_output(path: Path, force: bool) -> None:
    if path.exists():
        require(force, f"output already exists: {path} (use --force to replace it)")
        shutil.rmtree(path)
    path.mkdir(parents=True)


def write_checksums(output_dir: Path) -> None:
    entries = []
    for path in sorted(output_dir.iterdir()):
        if path.is_file() and path.name != "SHA256SUMS":
            entries.append(f"{sha256(path)}  {path.name}\n")
    (output_dir / "SHA256SUMS").write_text("".join(entries), encoding="ascii")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--release-dir", type=Path, default=DEFAULT_RELEASE_DIR)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--force", action="store_true")
    parser.add_argument(
        "--copy-docker",
        action="store_true",
        help="copy the 2.43 GB Docker tar instead of hard-linking when possible",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    release_dir = args.release_dir.resolve()
    output_dir = (
        args.output_dir.resolve()
        if args.output_dir
        else release_dir.parent / "zenodo-upload"
    )
    release = load_json(PACKAGE_DIR / "RELEASE.json")

    print(f"verifying frozen release: {release_dir}")
    verify_release(release_dir, release)
    print("release identity and acceptance records: PASS")

    prepare_output(output_dir, args.force)
    shutil.copy2(PACKAGE_DIR / "README.md", output_dir / "README.md")
    shutil.copy2(PACKAGE_DIR / "RELEASE.json", output_dir / "RELEASE.json")
    shutil.copy2(PACKAGE_DIR / "verify.sh", output_dir / "verify.sh")
    (output_dir / "verify.sh").chmod(
        (output_dir / "verify.sh").stat().st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH
    )
    shutil.copy2(REPO_ROOT / "work/verified-compilation-v10-driver/LICENSE", output_dir / "LICENSE")

    source_name = release["upload_files"]["source"]
    gzip_source(
        release_dir / release["polcert"]["source_archive"],
        output_dir / source_name,
    )

    docker_name = release["upload_files"]["docker"]
    docker_mode = copy_or_link(
        release_dir / release["docker"]["archive"],
        output_dir / docker_name,
        args.copy_docker,
    )

    evidence_name = release["upload_files"]["evidence"]
    build_evidence_zip(release_dir, output_dir / evidence_name, release)
    write_checksums(output_dir)

    files = sorted(path for path in output_dir.iterdir() if path.is_file())
    require(len(files) == 8, f"expected 8 upload files, found {len(files)}")
    print(f"Docker archive materialized as: {docker_mode}")
    print(f"Zenodo upload directory: {output_dir}")
    for path in files:
        print(f"  {path.name:44} {path.stat().st_size:12d} bytes")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"prepare_zenodo.py: {error}", file=sys.stderr)
        raise SystemExit(1)
