#!/usr/bin/env python3
"""Build and validate the single CPP supplementary-material ZIP."""

from __future__ import annotations

import argparse
import difflib
import hashlib
from html import escape, unescape
from html.parser import HTMLParser
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import sys
import tarfile
import tempfile
from urllib.parse import unquote, urlsplit
import zipfile


SCRIPT_DIR = Path(__file__).resolve().parent
PACKAGE_DIR = SCRIPT_DIR.parent
REPO_ROOT = PACKAGE_DIR.parents[1]
RELEASE_ROOT = (
    REPO_ROOT
    / "output/releases/state-eq-polyhedral-verification-complete-2026-08-29-v10"
)
DEFAULT_RELEASE_DIR = RELEASE_ROOT / "final"
DEFAULT_PROOF_HTML_DIR = RELEASE_ROOT / "anonymous-proof-html"
DEFAULT_OUTPUT = RELEASE_ROOT / "cpp27-anonymous/polcert-cpp27-supplement.zip"

SOURCE_ARCHIVE = "polcert-9d612d02ac8f27d46c5ec632f912f8a67939e748.tar"
SOURCE_SHA256 = "ed4a1cce93b3332bf2b2b80fdb01d7203dddc887f249fff95503d0205c31928c"
PLUTO_SOURCE_ARCHIVES = {
    "fixed": (
        "pluto-fixed-source.tar.xz",
        "5d04579f13add5ba6838fd8a8e617eec63d46186a8756e2946abbf471e6e3eb0",
    ),
    "historical": (
        "pluto-historical-source.tar.xz",
        "76f78f578e37aa4d2c229b268f7888522fb0414d66c7c7151908e3fbc485167b",
    ),
}
PLUTO_RECURSIVE_COMPONENTS = (
    "candl",
    "candl/osl",
    "candl/piplib",
    "clan",
    "clan/osl",
    "cloog-isl",
    "cloog-isl/isl",
    "cloog-isl/isl/imath",
    "cloog-isl/osl",
    "isl",
    "isl/imath",
    "openscop",
    "pet",
    "pet/isl",
    "pet/isl/imath",
    "piplib",
    "polylib",
)
ARCHIVE_ROOT = "polcert"
MAX_ARCHIVE_PATH_CHARS = 160
ZIP_TIMESTAMP = (2026, 8, 29, 0, 0, 0)

E2E_RECORDED_LOOP_CASES = {
    "const_unroll": "Constant-trip-count unrolling",
    "stride_down": "Affine bound and stride reconstruction",
    "stride_even": "Affine bound and stride reconstruction",
    "unrolljam_block_variable": "Block unrolling and validated loop jamming",
    "unrolljam_dependent_guard": "Block unrolling and validated loop jamming",
}

REPLACEMENTS = {
    "9d612d02ac8f27d46c5ec632f912f8a67939e748": "validated-source-snapshot",
    "state-eq-polyhedral-verification-complete-2026-08-29-v10": "validated-source-snapshot",
    "artifact/verified-compilation-v10-driver-finalization": "validated-source-snapshot",
    "9d612d0": "validated-source-snapshot",
    "8c43c210c9c08c5958198f22db4b54000380925e": "ordinary-fixed-pluto-snapshot",
    "8c43c210": "ordinary-fixed-pluto-snapshot",
    "8c43c21": "ordinary-fixed-pluto-snapshot",
    "6f43860b6c4cddeeca09189bf3073f05b78b14a5": "historical-bug-witness-pluto-snapshot",
    "6f43860b": "historical-bug-witness-pluto-snapshot",
    "6f43860": "historical-bug-witness-pluto-snapshot",
    "7d6fae8": "diamond-regression-introduction-snapshot",
    "488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02": "diamond-regression-snapshot",
    "488ea2f": "diamond-regression-snapshot",
    "56b66690edeed1ef17ddc018bbf67666795a3fd4": "diamond-fix-snapshot",
    "56b6669": "diamond-fix-snapshot",
    "fix/polcert-known-miscompilations": "fixed-regression-branch",
    "fix/diamond-reschedule-with-nointratileopt": "diamond-fix-branch",
    "https://github.com/verif-scop/pluto.git": "phase-dump-pluto-fork",
    "https://github.com/verif-scop/pluto": "phase-dump-pluto-fork",
    "verif-scop/pluto": "phase-dump-pluto-fork",
    "verif-scop/master": "historical-phase-dump-branch",
    "verif-scop/": "phase-dump-fork/",
    "verif-scop": "phase-dump-fork",
    "hughshine/pluto-verif": "pluto-build",
    "hughshine/polcert": "polcert-build",
    "Hughshine/PolCert": "PolCert",
    "/home/hugh": "/build",
}

DENYLIST = (
    "hughshine",
    "hugh",
    "/home/hugh",
    "xuyang",
    "li5274",
    "li5274@purdue.edu",
    "purdue",
    "lxy10",
    "github.com/verif-scop",
    "verif-scop/",
    "verif-scop",
    "9d612d02ac8f27d46c5ec632f912f8a67939e748",
    "9d612d0",
    "8c43c210c9c08c5958198f22db4b54000380925e",
    "8c43c210",
    "6f43860b6c4cddeeca09189bf3073f05b78b14a5",
    "6f43860b",
    "7d6fae8",
    "488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02",
    "488ea2f",
    "56b66690edeed1ef17ddc018bbf67666795a3fd4",
    "56b6669",
    "fix/polcert-known-miscompilations",
    "fix/diamond-reschedule-with-nointratileopt",
    "0661fe0a",
    "6404668840fdac7333abf47f8784b5514e7ca94baa7d47d48fc6e6c6b7d9510a",
    "ed4a1cce93b3332bf2b2b80fdb01d7203dddc887f249fff95503d0205c31928c",
    "state-eq-polyhedral-verification",
    "artifact/verified-compilation",
    "33243898549",
)

BROWSER_TEXT_SUFFIXES = {
    ".c",
    ".cloog",
    ".fst",
    ".h",
    ".json",
    ".log",
    ".loop",
    ".md",
    ".ml",
    ".mli",
    ".patch",
    ".py",
    ".scop",
    ".sh",
    ".txt",
    ".v",
}


class LinkCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.links: list[str] = []
        self.anchors: set[str] = set()

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        values = dict(attrs)
        if values.get("id"):
            self.anchors.add(values["id"] or "")
        if tag == "a" and values.get("name"):
            self.anchors.add(values["name"] or "")
        if tag in {"a", "link", "script", "img"}:
            key = "href" if tag in {"a", "link"} else "src"
            if values.get(key):
                self.links.append(values[key] or "")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def validate_tar_member(member: tarfile.TarInfo) -> None:
    path = PurePosixPath(member.name)
    require(not path.is_absolute(), f"absolute source archive path: {member.name}")
    require(".." not in path.parts, f"parent traversal in source archive: {member.name}")
    if member.issym() or member.islnk():
        link = PurePosixPath(member.linkname)
        require(not link.is_absolute(), f"absolute source symlink: {member.name}")
        require(".." not in link.parts, f"parent traversal in source symlink: {member.name}")


def extract_source(archive_path: Path, destination: Path) -> None:
    with tarfile.open(archive_path, "r:*") as archive:
        for member in archive.getmembers():
            validate_tar_member(member)
        archive.extractall(destination)


def prepare_pluto_sources(destination: Path) -> dict[str, object]:
    destination.mkdir(parents=True)
    snapshots = {}
    for role, (filename, expected_sha256) in PLUTO_SOURCE_ARCHIVES.items():
        archive_path = PACKAGE_DIR / "vendor" / filename
        require(archive_path.is_file(), f"missing Pluto source archive: {archive_path}")
        require(
            sha256(archive_path) == expected_sha256,
            f"Pluto source archive hash mismatch: {filename}",
        )
        with tempfile.TemporaryDirectory(prefix=f"polcert-pluto-{role}-") as temporary:
            snapshot = Path(temporary)
            extract_source(archive_path, snapshot)
            require((snapshot / "LICENSE").is_file(), f"missing Pluto license: {role}")
            require((snapshot / "autogen.sh").is_file(), f"missing Pluto build script: {role}")
            missing_components = [
                component
                for component in PLUTO_RECURSIVE_COMPONENTS
                if not (snapshot / component).is_dir()
                or not any(path.is_file() for path in (snapshot / component).rglob("*"))
            ]
            require(
                not missing_components,
                f"incomplete recursive Pluto source snapshot {role}: "
                + ", ".join(missing_components),
            )
            require(
                not any(path.name == ".git" for path in snapshot.rglob("*")),
                f"Pluto snapshot retains Git metadata: {role}",
            )
            elf_files = []
            for path in snapshot.rglob("*"):
                if path.is_file():
                    with path.open("rb") as handle:
                        if handle.read(4) == b"\x7fELF":
                            elf_files.append(path.relative_to(snapshot).as_posix())
            require(
                not elf_files,
                f"Pluto snapshot contains prebuilt ELF files {role}: "
                + ", ".join(elf_files),
            )
            check_denylist(snapshot)
            hashes = all_file_hashes(snapshot)
        packaged_name = f"{role}.tar.xz"
        shutil.copy2(archive_path, destination / packaged_name)
        snapshots[role] = {
            "archive": f"third_party/pluto/{packaged_name}",
            "files": len(hashes),
            "tree_sha256": tree_hash(hashes),
            "packaging_archive_sha256": expected_sha256,
        }
    shutil.copy2(PACKAGE_DIR / "PLUTO_SOURCES_README.md", destination / "README.md")
    return snapshots


def file_hashes(root: Path, suffix: str) -> dict[str, str]:
    return {
        path.relative_to(root).as_posix(): sha256(path)
        for path in sorted(root.rglob(f"*{suffix}"))
        if path.is_file()
    }


def all_file_hashes(root: Path) -> dict[str, str]:
    return {
        path.relative_to(root).as_posix(): sha256(path)
        for path in sorted(root.rglob("*"))
        if path.is_file()
    }


def tree_hash(hashes: dict[str, str]) -> str:
    digest = hashlib.sha256()
    for name, value in sorted(hashes.items()):
        digest.update(name.encode("utf-8"))
        digest.update(b"\0")
        digest.update(value.encode("ascii"))
        digest.update(b"\n")
    return digest.hexdigest()


def prune_source(source: Path) -> None:
    for relative in (
        ".github",
        ".dockerignore",
        "Dockerfile",
        "ENVIRONMENT.md",
        "tools/coq2html",
        "samples/README.md",
        "POLCERT.md",
        "POLOPT.md",
        "doc",
        "tests/end-to-end-generated/BEST_PIPELINES.md",
        "tests/pluto-all/README.md",
        "tests/polopt-regression/README.md",
        "tools/perf/README.md",
    ):
        path = source / relative
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
        elif path.exists() or path.is_symlink():
            path.unlink()

    shutil.copy2(PACKAGE_DIR / "SOURCE_README.md", source / "README.md")
    shutil.copy2(
        PACKAGE_DIR / "SOURCE_E2E_C_README.md",
        source / "tests/end-to-end-c/README.md",
    )
    shutil.copy2(
        PACKAGE_DIR / "SOURCE_E2E_GENERATED_README.md",
        source / "tests/end-to-end-generated/README.md",
    )
    (source / "doc").mkdir()
    shutil.copy2(PACKAGE_DIR / "SOURCE_DOC_README.md", source / "doc/README.md")
    ci_tools = source / "tools/ci"
    for path in list(ci_tools.iterdir()):
        if path.name in {
            "check_legacy_failure_exit.sh",
            "check_open_proofs.py",
            "ci_resources.sh",
            "run_ci_shard.sh",
            "run_legacy_tests.sh",
            "test_check_open_proofs.py",
        }:
            continue
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
        else:
            path.unlink()
    shutil.copy2(
        PACKAGE_DIR / "SOURCE_PLUTO_BUGS_README.md",
        source / "tests/pluto-bugs/README.md",
    )


def patch_anonymous_artifact_runner(source: Path) -> None:
    path = source / "tools/artifact/run_artifact_check.py"
    text = path.read_text(encoding="utf-8")
    replacements = (
        (
            "    provenance_errors = check_build_provenance(environment, provenance)\n"
            "    if provenance_errors:\n",
            "    provenance_errors = check_build_provenance(environment, provenance)\n"
            "    provenance_required = environment[\"POLCERT_REQUIRE_PROVENANCE\"] == \"1\"\n"
            "    if provenance_errors:\n",
        ),
        (
            '            "build_provenance": {\n'
            '                "manifest": provenance,\n'
            '                "verified": False,\n'
            '                "errors": provenance_errors,\n'
            "            },\n",
            '            "build_provenance": {\n'
            '                "required": provenance_required,\n'
            '                "manifest_present": provenance is not None,\n'
            '                "manifest": provenance,\n'
            '                "verified": False,\n'
            '                "errors": provenance_errors,\n'
            "            },\n",
        ),
        (
            '        "build_provenance": {\n'
            '            "manifest": provenance,\n'
            '            "verified": not provenance_errors,\n'
            '            "errors": provenance_errors,\n'
            "        },\n",
            '        "build_provenance": {\n'
            '            "required": provenance_required,\n'
            '            "manifest_present": provenance is not None,\n'
            '            "manifest": provenance,\n'
            '            "verified": provenance_required and not provenance_errors,\n'
            '            "errors": provenance_errors,\n'
            "        },\n",
        ),
    )
    for old, new in replacements:
        require(text.count(old) == 1, "unexpected artifact-runner source shape")
        text = text.replace(old, new)
    path.write_text(text, encoding="utf-8")


def sanitize_file(path: Path) -> None:
    if path.suffix == ".v":
        return
    data = path.read_bytes()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return
    updated = text
    for old, new in REPLACEMENTS.items():
        updated = updated.replace(old, new)
    if updated != text:
        path.write_text(updated, encoding="utf-8")


def sanitize_tree(root: Path) -> None:
    for path in sorted(root.rglob("*")):
        if path.is_file() and not path.is_symlink():
            sanitize_file(path)


def verify_release(release_dir: Path) -> tuple[dict, dict]:
    source_archive = release_dir / SOURCE_ARCHIVE
    require(source_archive.is_file(), f"missing source archive: {source_archive}")
    require(sha256(source_archive) == SOURCE_SHA256, "source archive hash mismatch")

    artifact_results = load_json(release_dir / "polcert-artifact-check/artifact-results.json")
    checks = artifact_results.get("results", [])
    require(artifact_results.get("mode") == "full", "artifact result is not full mode")
    require(artifact_results.get("ok") is True, "artifact result reports failure")
    require(len(checks) == 30, f"expected 30 artifact checks, found {len(checks)}")
    require(all(check.get("ok") is True for check in checks), "an artifact check failed")

    proof_report = load_json(release_dir / "polcert-artifact-check/proof-report.json")
    for field in (
        "admitted_count",
        "abort_count",
        "extraction_axiom_count",
        "missing_route_theorem_count",
    ):
        require(proof_report.get(field) == 0, f"proof report has nonzero {field}")
    return artifact_results, proof_report


def add_proof_navigation(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    if "../index.html" in text or "artifact-handbook-link" in text:
        return
    banner = (
        '<div id="artifact-handbook-link" style="padding:8px 12px;'
        'border-bottom:1px solid #cbd3d8;background:#f4f6f7;'
        'font:14px system-ui,sans-serif">'
        '<a href="../index.html">Plain-language guide</a> &middot; '
        '<a href="toc.html">Modules</a> &middot; '
        '<a href="declarations.html">Declarations</a></div>'
    )
    require("<body>" in text, f"generated proof page has no body: {path.name}")
    path.write_text(text.replace("<body>", f"<body>\n{banner}", 1), encoding="utf-8")


def prepare_docs(proof_html_dir: Path, destination: Path) -> None:
    require((proof_html_dir / "toc.html").is_file(), "generated proof toc is missing")
    require(
        (proof_html_dir / "declarations.html").is_file(),
        "generated proof declaration index is missing",
    )
    shutil.copytree(proof_html_dir, destination / "proof")
    (destination / "proof/proof.glob").unlink(missing_ok=True)
    shutil.copy2(PACKAGE_DIR / "docs/index.html", destination / "index.html")
    shutil.copy2(PACKAGE_DIR / "docs/artifact.css", destination / "artifact.css")
    shutil.copy2(PACKAGE_DIR / "docs/proof-index.html", destination / "proof/index.html")
    for path in sorted((destination / "proof").glob("*.html")):
        if path.name != "index.html":
            add_proof_navigation(path)


def normalize_artifact_results(path: Path) -> None:
    """Turn the raw run record into a self-contained packaged record."""
    record = load_json(path)
    original_provenance = record.get("build_provenance", {})
    environment = record.get("environment", {})
    record["record"] = {
        "schema": "polcert-packaged-validation-record-v1",
        "derived_from_completed_validation_run": True,
    }
    record["build_provenance"] = {
        "formal_source_unchanged_during_packaging": True,
        "validation_run_provenance_checked": bool(original_provenance.get("verified")),
    }
    record["environment"] = {
        key: environment[key]
        for key in ("coq_version", "ocaml_version")
        if key in environment
    }
    record["output_root"] = "results"
    for result in record.get("results", []):
        for field in ("stdout_path", "stderr_path"):
            if result.get(field):
                result[field] = f"raw/{Path(result[field]).name}"
    path.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def remove_elf_outputs(root: Path) -> int:
    removed = 0
    for path in sorted(root.rglob("*")):
        if path.is_file() and not path.is_symlink() and path.read_bytes()[:4] == b"\x7fELF":
            path.unlink()
            removed += 1
    return removed


def parse_key_values(payload: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for token in payload.split()[2:]:
        if "=" in token:
            key, value = token.split("=", 1)
            fields[key] = value
    return fields


def prepare_executable_checks(release_dir: Path, destination: Path) -> dict:
    ci_log = release_dir / "github-actions-33243898549.log"
    require(ci_log.is_file(), "generated executable-check log is missing")
    payloads = []
    for line in ci_log.read_text(encoding="utf-8").splitlines():
        position = line.find("[E2E-GEN")
        if position >= 0:
            payloads.append(line[position:])

    suite_names = (
        "default-corpus",
        "parallel-effect",
        "second-level-effect",
        "intratile-effect",
    )
    expected_counts = (62, 3, 1, 1)
    suites = []
    current = []
    log_lines = []
    for payload in payloads:
        log_lines.append(payload)
        if payload.startswith("[E2E-GEN] "):
            fields = parse_key_values(payload)
            require(payload.split()[1] == "PASS", f"failed generated check: {payload}")
            current.append(
                {
                    "actual": fields["actual"],
                    "case": fields["case"],
                    "coverage": fields["coverage"],
                    "executions": int(fields["executions"]),
                    "expected": fields["expected"],
                    "interpretation": fields["interpretation"],
                    "status": "PASS",
                }
            )
        elif payload.startswith("[E2E-GEN-SUITE] "):
            fields = parse_key_values(payload)
            index = len(suites)
            require(index < len(suite_names), "unexpected generated-check suite")
            require(payload.split()[1] == "PASS", f"failed generated suite: {payload}")
            require(int(fields["expected"]) == expected_counts[index], "suite size mismatch")
            require(int(fields["actual"]) == len(current), "suite result count mismatch")
            suites.append(
                {
                    "cases": current,
                    "coverage": fields["coverage"],
                    "expected": expected_counts[index],
                    "name": suite_names[index],
                    "passed": len(current),
                    "status": "PASS",
                }
            )
            current = []

    require(not current, "generated checks ended without a suite summary")
    require(len(suites) == 4, f"expected four generated suites, found {len(suites)}")
    require(
        [suite["passed"] for suite in suites] == list(expected_counts),
        "generated suite coverage mismatch",
    )

    destination.mkdir()
    shutil.copy2(PACKAGE_DIR / "EXECUTABLE_CHECKS_README.md", destination / "README.md")
    (destination / "validation.log").write_text("\n".join(log_lines) + "\n", encoding="utf-8")
    results = {
        "baseline_vs_optimized": {"passed": 62, "total": 62},
        "effect_focused_additional_runs": {"passed": 5, "total": 5},
        "suites": suites,
    }
    (destination / "results.json").write_text(
        json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return results


def copy_recorded_e2e_loops(release_dir: Path, destination: Path) -> None:
    source_root = release_dir / "polcert-artifact-check/end-to-end-c"
    for case in E2E_RECORDED_LOOP_CASES:
        source = source_root / case
        require(source.is_dir(), f"missing recorded end-to-end output: {case}")
        target = destination / f"e2e-{case.replace('_', '-')}"
        target.mkdir()
        input_text = (source / "input.loop").read_text(encoding="utf-8")
        output_text = (source / "optimized.loop").read_text(encoding="utf-8")
        (target / "input.pretty.loop").write_text(input_text, encoding="utf-8")
        (target / "optimized.loop").write_text(output_text, encoding="utf-8")
        (target / "diff.patch").write_text(
            "".join(
                difflib.unified_diff(
                    input_text.splitlines(keepends=True),
                    output_text.splitlines(keepends=True),
                    fromfile="before.loop",
                    tofile="after.loop",
                )
            ),
            encoding="utf-8",
        )
        shutil.copy2(source / "status.txt", target / "status.txt")


def prepare_transformation_index(destination: Path) -> dict:
    examples = sorted(path for path in destination.iterdir() if path.is_dir())
    records = []
    rows = []
    for path in examples:
        changed = (path / "diff.patch").is_file() and (path / "diff.patch").stat().st_size > 0
        input_text = (path / "input.pretty.loop").read_text(encoding="utf-8")
        output_text = (path / "optimized.loop").read_text(encoding="utf-8")
        tiled = any(
            marker in output_text
            for marker in ("32 *", "/ 32", "64 *", "/ 64", "313")
        )
        transformations = []
        recorded_e2e_case = (
            path.name.removeprefix("e2e-").replace("-", "_")
            if path.name.startswith("e2e-")
            else None
        )
        if recorded_e2e_case in E2E_RECORDED_LOOP_CASES:
            transformations.append(E2E_RECORDED_LOOP_CASES[recorded_e2e_case])
        elif not changed:
            transformations.append("No loop-structure change")
        elif path.name == "seq":
            transformations.append("Domain guard insertion")
        else:
            if path.name.startswith("fusion") or path.name == "multi-stmt-stencil-seq":
                transformations.append("Loop fusion")
            if path.name == "tricky2":
                transformations.extend(("Loop fusion", "Domain splitting"))
            elif path.name == "tricky3":
                transformations.extend(("Inner-loop fusion", "Domain splitting"))
            if tiled:
                transformations.append("Ordinary tiling")
            if not transformations:
                transformations.append("Affine scheduling and loop-bound reconstruction")
        transformation = "; ".join(dict.fromkeys(transformations))
        recorded_e2e = recorded_e2e_case in E2E_RECORDED_LOOP_CASES
        records.append(
            {
                "case": path.name,
                "changed": changed,
                "observed_transformation": transformation,
            }
        )
        name = escape(path.name)
        if recorded_e2e:
            diff_text = (path / "diff.patch").read_text(encoding="utf-8")
            supporting = f"""
  <details>
    <summary>Unified Diff</summary>
    <pre>{escape(diff_text)}</pre>
  </details>"""
            file_links = (
                f'<strong><a href="{name}/comparison.html">before/after</a></strong>'
            )
        else:
            supporting = """
  <p>
    <a href="diff.patch">Unified diff</a> &middot;
    <a href="status.txt">Compiler log</a>
  </p>"""
            file_links = (
                f'<strong><a href="{name}/comparison.html">before/after</a></strong> &middot; '
                f'<a href="{name}/input.pretty.loop">before</a> &middot; '
                f'<a href="{name}/optimized.loop">after</a> &middot; '
                f'<a href="{name}/diff.patch">diff</a> &middot; '
                f'<a href="{name}/status.txt">log</a>'
            )
        comparison = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{name}: Before and After</title>
  <link rel="stylesheet" href="../../../docs/artifact.css">
</head>
<body>
<main>
  <p><a href="../index.html">All optimized loop examples</a></p>
  <h1><code>{name}</code>: Before and After</h1>
  <p class="lede">Observed transformation: {escape(transformation)}.</p>
  <div class="loop-comparison">
    <section id="before">
      <h2>Before</h2>
      <pre>{escape(input_text)}</pre>
    </section>
    <section id="after">
      <h2>Accepted Output</h2>
      <pre>{escape(output_text)}</pre>
    </section>
  </div>
{supporting}
</main>
</body>
</html>
"""
        (path / "comparison.html").write_text(comparison, encoding="utf-8")
        rows.append(
            "<tr>"
            f"<td><code>{name}</code></td>"
            f"<td>{escape(transformation)}</td>"
            f"<td>{file_links}</td>"
            "</tr>"
        )
    transformation_counts: dict[str, int] = {}
    for record in records:
        label = record["observed_transformation"]
        transformation_counts[label] = transformation_counts.get(label, 0) + 1
    summary = {
        "total": len(records),
        "changed": sum(record["changed"] for record in records),
        "unchanged": sum(not record["changed"] for record in records),
        "transformation_counts": transformation_counts,
        "cases": records,
    }
    (destination / "index.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    count_rows = "\n".join(
        f"<tr><td>{escape(label)}</td><td>{count}</td></tr>"
        for label, count in sorted(
            transformation_counts.items(), key=lambda item: (-item[1], item[0])
        )
    )
    case_rows = "\n".join(rows)
    page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Optimized Loop Examples</title>
  <link rel="stylesheet" href="../../docs/artifact.css">
</head>
<body>
<main>
  <h1>Optimized Loop Examples</h1>
  <p class="lede">
    Open a case to compare the source Loop program with the accepted output.
    Diffs and compiler logs are supporting records.
  </p>
  <table>
    <thead>
      <tr><th>Case</th><th>Observed loop transformation</th><th>Files</th></tr>
    </thead>
    <tbody>
{case_rows}
    </tbody>
  </table>
  <h2>Summary</h2>
  <p>
    These labels describe visible loop-structure changes. They do not claim a
    performance improvement.
  </p>
  <table>
    <thead><tr><th>Observed transformation</th><th>Cases</th></tr></thead>
    <tbody>
{count_rows}
    </tbody>
  </table>
</main>
</body>
</html>
"""
    (destination / "index.html").write_text(page, encoding="utf-8")
    return summary


def prepare_witness_results(destination: Path) -> dict:
    log = (destination / "validation.log").read_text(encoding="utf-8")
    cases = (
        {
            "case": "auto-affine-lp-cc-scaling",
            "log_marker": "[pluto-auto-affine-lp] OK",
            "kind": "Confirmed official Pluto miscompilation",
            "reason_not_accepted": (
                "A real S3-to-S1 dependence is reversed after connected-component "
                "relabeling lets LP integerization scale its endpoints differently."
            ),
            "polcert_outcome": (
                "The affine checker rejects the before/after schedule; the complete "
                "default no-RAR route emits no optimized loop."
            ),
            "pluto_location": "lib/pluto.c:1983-2015; lib/framework.cpp:1374-1413",
            "draft_section": "P1",
        },
        {
            "case": "affine-fst-reversed",
            "log_marker": "[pluto-affine-bug] OK",
            "kind": "Unsafe Pluto control interface",
            "reason_not_accepted": (
                "The supplied .fst grouping places a consumer before its producer, "
                "but Pluto accepts the complete lexicographically illegal schedule."
            ),
            "polcert_outcome": (
                "The affine checker rejects the schedule and the complete route emits "
                "no optimized loop."
            ),
            "pluto_location": "lib/pluto.c:873-940",
            "draft_section": "C1",
        },
        {
            "case": "vanished-outer-parallel",
            "log_marker": "[pluto-miscompile] OK",
            "kind": "Confirmed official Pluto miscompilation",
            "reason_not_accepted": (
                "After a one-trip outer coordinate disappears, an off-by-one band "
                "test transfers its parallel annotation to a dependent inner recurrence."
            ),
            "polcert_outcome": (
                "Strict hint mapping rejects the vanished loop, and a direct check also "
                "rejects the dependent inner loop."
            ),
            "pluto_location": "tool/ast_transform.c:75-95",
            "draft_section": "P2",
        },
        {
            "case": "notile-unrolljam-nonpermutable",
            "log_marker": "[pluto-unrolljam-bug] OK",
            "kind": "Confirmed official Pluto miscompilation",
            "reason_not_accepted": (
                "Under --notile, candidate discovery assumes one tiled level and crosses "
                "the real permutable-band boundary, jamming a dependence-carrying loop."
            ),
            "polcert_outcome": (
                "Proved block unrolling is retained, but the unsafe local jam is refused."
            ),
            "pluto_location": "lib/polyloop.c:575-605",
            "draft_section": "P3",
        },
        {
            "case": "tiling-innerpar-satvec",
            "log_marker": "[pluto-tiling-bug] OK",
            "kind": "Confirmed official Pluto miscompilation",
            "reason_not_accepted": (
                "Pluto moves dependence-satisfaction bits to a tile dimension without "
                "constructing the schedule that would satisfy those dependences."
            ),
            "polcert_outcome": (
                "The legal rectangular tiling is accepted; the unsafe parallel loop is "
                "removed or rejected in strict mode."
            ),
            "pluto_location": "lib/tile.c:433-478",
            "draft_section": "P4",
        },
        {
            "case": "diamond-nointratile-reschedule",
            "log_marker": "[pluto-diamond-nointra] OK",
            "kind": "Fork-specific regression, fixed in the ordinary artifact Pluto",
            "reason_not_accepted": (
                "A phase-dump patch made a mandatory diamond-schedule restore depend on "
                "the optional intra-tile pass, producing a wrong execution order."
            ),
            "polcert_outcome": (
                "The corresponding mixed-scalar candidate is conservatively rejected; "
                "a separate pure-diamond case is accepted."
            ),
            "pluto_location": "diamond reschedule call in the phase-dump fork",
            "draft_section": "F1",
        },
        {
            "case": "matmul-parallel-hint",
            "log_marker": "[pluto-bug] explicit-RAR matmul parallel-hint case reproduced",
            "kind": "Non-certifiable hint, not a demonstrated Pluto miscompilation",
            "reason_not_accepted": (
                "The hinted coordinate cannot be certified as a safe generated parallel "
                "loop for this matrix-multiplication schedule."
            ),
            "polcert_outcome": (
                "Strict mode rejects with no output; permissive mode chooses a different "
                "certified dimension."
            ),
            "pluto_location": "No Pluto defect claimed",
            "draft_section": "not in the upstream bug draft",
        },
    )
    results = []
    rows = []
    for case in cases:
        require(
            case["log_marker"] in log,
            f"missing witness result marker: {case['case']}",
        )
        result = {
            **case,
            "status": "PASS",
            "validation_log": "validation.log",
            "case_explanation": f"{case['case']}/README.md",
        }
        results.append(result)
        name = escape(case["case"])
        rows.append(
            "<tr>"
            f'<td><a href="{name}/README.md"><code>{name}</code></a><br>'
            f'{escape(case["kind"])}</td>'
            f'<td>{escape(case["reason_not_accepted"])}</td>'
            f'<td>{escape(case["polcert_outcome"])}</td>'
            f'<td><code>{escape(case["pluto_location"])}</code><br>'
            f'Draft: {escape(case["draft_section"])}</td>'
            "</tr>"
        )
    summary = {"passed": len(results), "total": len(cases), "results": results}
    (destination / "results.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    result_rows = "\n".join(rows)
    page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Rejected or Replaced Optimizer Effects</title>
  <link rel="stylesheet" href="../../docs/artifact.css">
</head>
<body>
<main>
  <h1>Rejected or Replaced Optimizer Effects</h1>
  <p>
    Each row states either the violated condition or the missing certificate,
    followed by the observed PolCert response. The
    <a href="BUG_REPORT_DRAFT.md">upstream bug-report draft</a> gives
    reproduction commands, wrong results, root causes, and official-version
    checks for P1-P4 and C1; F1 belongs only to the development fork.
  </p>
  <table>
    <thead>
      <tr>
        <th>Case</th>
        <th>Why PolCert cannot accept it</th>
        <th>PolCert result</th>
        <th>Pluto source or status</th>
      </tr>
    </thead>
    <tbody>
{result_rows}
    </tbody>
  </table>
</main>
</body>
</html>
"""
    (destination / "index.html").write_text(page, encoding="utf-8")
    return summary


def copy_bug_witnesses(
    source: Path,
    destination: Path,
    release_dir: Path,
    bug_report_draft: str,
) -> None:
    shutil.copytree(source / "tests/pluto-bugs", destination)
    shutil.copy2(PACKAGE_DIR / "PLUTO_WITNESSES_README.md", destination / "README.md")
    matmul = destination / "matmul-parallel-hint"
    matmul.mkdir()
    shutil.copy2(source / "tests/polopt-generated/inputs/matmul.loop", matmul / "matmul.loop")
    shutil.copy2(source / "tools/pluto_bugs/run_matmul_parallel_hint.py", matmul / "run.py")
    shutil.copy2(PACKAGE_DIR / "MATMUL_WITNESS_README.md", matmul / "README.md")
    (destination / "BUG_REPORT_DRAFT.md").write_text(
        bug_report_draft
        .replace(
            "parallel and innermost-vector annotations require a fresh check of the",
            "parallel annotations require a fresh check of the",
        )
        .replace(
            "SIMD instructions, scalar privatization, storage expansion, state-changing",
            "Machine-level vector lowering, scalar privatization, storage expansion, "
            "state-changing",
        ),
        encoding="utf-8",
    )

    runners = destination / "runners"
    runners.mkdir()
    for path in sorted((source / "tools/pluto_bugs").glob("*.py")):
        shutil.copy2(path, runners / path.name)

    log = (release_dir / "local-release-validation.log").read_text(encoding="utf-8")
    marker = "python3 tools/pluto_bugs/run_matmul_parallel_hint.py"
    require(marker in log, "Pluto witness section is missing from local validation log")
    witness_log = log[log.index(marker):]
    (destination / "validation.log").write_text(witness_log, encoding="utf-8")


def validate_test_evidence(source: Path, raw_output: Path) -> None:
    markers = {
        "pluto-compat-suite.stdout.txt": "PASS expected=189 actual=189",
        "strict-loop-suite.stdout.txt": "total=62",
        "second-level-suite.stdout.txt": "PASS expected=58 actual=58",
        "non-second-level-tiling-routes.stdout.txt": (
            "PASS expected=permutable-band:84,fallbacks:0,vector-rejections:6 "
            "actual=permutable-band:84,fallbacks:0,vector-rejections:6"
        ),
        "diamond-suite.stdout.txt": "PASS expected=19 actual=19",
        "parallel-current-suite.stdout.txt": "PASS expected=9 actual=9",
        "vector-current-suite.stdout.txt": "PASS expected=12 actual=12",
        "iss-suite.stdout.txt": (
            "[ISS-SUITE] PASS expected=accepted:4,rejected:3 "
            "actual=accepted:4,rejected:3"
        ),
        "unrolljam-effect-corpus.stdout.txt": '"cases": 11',
        "typed-c-pipeline.stdout.txt": "PASS expected=6 actual=6",
    }
    for filename, marker in markers.items():
        text = (raw_output / filename).read_text(encoding="utf-8")
        require(marker in text, f"test evidence marker is missing from {filename}")
    iss_log = (raw_output / "iss-suite.stdout.txt").read_text(encoding="utf-8")
    require(
        "[ISS-MULTICUT] PASS expected=accepted:1,rejected:2 "
        "actual=accepted:1,rejected:2" in iss_log,
        "ISS multicut summary is missing",
    )
    typed_cases = [
        path for path in (source / "tests/end-to-end-c/cases").iterdir()
        if path.is_dir()
    ]
    require(len(typed_cases) == 10, f"expected 10 handwritten C cases, found {len(typed_cases)}")


def copy_typed_pipeline_ci_result(release_dir: Path, raw_output: Path) -> None:
    ci_logs = sorted(release_dir.glob("github-actions-*.log"))
    require(len(ci_logs) == 1, f"expected one GitHub Actions log, found {len(ci_logs)}")
    lines = []
    for line in ci_logs[0].read_text(encoding="utf-8").splitlines():
        marker = line.find("[typed-c-pipeline]")
        if marker >= 0:
            lines.append(line[marker:])
    require(len(lines) == 7, f"expected seven typed-C result lines, found {len(lines)}")
    require(
        "PASS expected=6 actual=6" in lines[-1],
        "typed-C pipeline did not finish with its six-case summary",
    )
    (raw_output / "typed-c-pipeline.stdout.txt").write_text(
        "\n".join(lines) + "\n",
        encoding="utf-8",
    )


def copy_remote_ci_test_results(release_dir: Path, raw_output: Path) -> list[dict]:
    """Copy concise result lines and recover every timed remote-CI phase."""
    ci_logs = sorted(release_dir.glob("github-actions-*.log"))
    require(len(ci_logs) == 1, f"expected one GitHub Actions log, found {len(ci_logs)}")
    payloads = []
    starts: list[str] = []
    elapsed: dict[str, str] = {}
    result_pattern = re.compile(
        r"\[[A-Za-z0-9_./-]+\] (?:PASS|OK)\b.*"
        r"|\[pluto-bug\] explicit-RAR matmul parallel-hint case reproduced"
    )
    for line in ci_logs[0].read_text(encoding="utf-8").splitlines():
        timing = line.find("[ci-timing]")
        result = result_pattern.search(line)
        if timing >= 0:
            payload = line[timing:]
            payloads.append(payload)
            start = re.match(r"\[ci-timing\] START ([^ ]+)$", payload)
            end = re.match(r"\[ci-timing\] END ([^ ]+) wall=([^ ]+)$", payload)
            if start:
                starts.append(start.group(1))
            if end:
                elapsed[end.group(1)] = end.group(2)
        elif result:
            payloads.append(result.group(0))
    require(len(starts) == 45, f"expected 45 timed CI phases, found {len(starts)}")
    require(set(starts) == set(elapsed), "remote CI timing start/end mismatch")
    require(
        "[pluto-bug] explicit-RAR matmul parallel-hint case reproduced" in payloads,
        "remote CI output is missing the matmul parallel-hint witness",
    )
    (raw_output / "remote-ci-test-results.stdout.txt").write_text(
        "\n".join(payloads) + "\n",
        encoding="utf-8",
    )
    return [
        {
            "name": name,
            "elapsed": elapsed[name],
            "status": "PASS",
            "evidence": "raw/remote-ci-test-results.stdout.txt",
        }
        for name in starts
    ]


def result_fields(line: str) -> dict[str, str]:
    """Parse space-separated key/value fields while preserving values verbatim."""
    matches = list(re.finditer(r"(?:^| )([A-Za-z][A-Za-z0-9_-]*)=", line))
    fields: dict[str, str] = {}
    for index, match in enumerate(matches):
        start = match.end()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(line)
        fields[match.group(1)] = line[start:end].strip()
    return fields


def is_expected_rejection(expected: str, actual: str, coverage: str) -> bool:
    text = f"{expected} {actual} {coverage}".lower()
    return (
        "rejection-contract" in text
        or expected.lower().startswith(
            ("reject", "failure", "result=failure", "result:reject")
        )
        or "expected=rejection" in text
        or "route:rejected" in expected.lower()
        or "status:" in expected.lower() and "rejected" in expected.lower()
    )


def observed_transformation(
    suite: str,
    case: str,
    expected: str,
    actual: str,
    coverage: str,
    transformation_by_case: dict[str, str],
) -> str:
    """Name the loop effect checked by a case, rather than saying only changed."""
    lower_suite = suite.lower()
    lower_case = case.lower()
    lower_actual = actual.lower()
    lower_expected = expected.lower()

    if is_expected_rejection(expected, actual, coverage):
        rejected_effects = {
            "auto-affine-lp-cc-scaling": "Affine rescheduling reversed a dependence",
            "affine-fst-reversed": "External grouping placed a consumer before its producer",
            "vanished-outer-parallel": "A parallel annotation moved to a dependent inner loop",
            "notile-unrolljam-nonpermutable": "Loop jamming crossed a permutable-band boundary",
            "tiling-innerpar-satvec": "Tiling was legal, but the parallel annotation was unsafe",
            "diamond-nointratile-reschedule": "Diamond schedule restoration was omitted",
            "matmul-parallel-hint": "The requested parallel dimension was not certifiable",
        }
        if lower_case in rejected_effects:
            return rejected_effects[lower_case]
        if "final-affine" in lower_case:
            return "No program emitted; post-tiling affine rescheduling was rejected"
        if "consumer" in lower_case:
            return "No program emitted; an invalid parallel-loop consumer was rejected"
        return "Candidate rejected; no unchecked program emitted"

    if lower_suite == "legacy/pluto-all":
        return "Original and optimized affine schedules mutually refine"
    if lower_suite == "legacy/readscop":
        return "OpenScop parse/print round trip (no optimization)"
    if lower_suite == "legacy/cpol-openscop":
        return "CPoly-to-OpenScop conversion (no optimization)"
    if lower_suite == "legacy/pluto":
        return "Affine schedule generation and conversion"
    if lower_suite.startswith("legacy/csample"):
        return "Typed C-instruction schedules mutually refine"
    if lower_suite in {"unit", "proof gate", "build gate"}:
        return "Artifact infrastructure or proof-build check"
    if lower_suite == "identity-iss-sensitive-search":
        return "ISS sensitivity comparison"
    if lower_suite == "direct-route" and lower_case == "frozen-diamond-phase-pair":
        return "Diamond tiling certificate accepted; no optimized program emitted"
    if lower_suite == "identity-diamond-sensitive-search":
        if "export-failed" in lower_actual:
            return "Search skipped because the input could not be exported"
        return "Ordinary tiling; diamond tiling produced the same generated C"
    if lower_suite == "unroll-and-jam exploration":
        if "effect=true" in lower_actual:
            return "Block unrolling and validated loop jamming"
        return "No checked unroll-and-jam transformation observed"
    if lower_suite == "scalar-interleaved tiling":
        return (
            "Ordinary tiling certificate accepted"
            if case == "frozen-positive"
            else "Mutated tiling certificate rejected"
        )
    if lower_suite == "generated execution: parallel-effect":
        return "Parallelization"
    if lower_suite == "generated execution: second-level-effect":
        return "Two-level tiling"
    if lower_suite == "generated execution: intratile-effect":
        return "Intra-tile affine rescheduling"

    if lower_suite == "pluto-compat-suite" and "acceptance-only" in coverage.lower():
        if lower_case == "sequential-iss-notile":
            return "ISS route accepted; no loop transformation asserted"
        if lower_case == "optimizer-forceparallel-pass-through":
            return "Option accepted; this test makes no parallel-effect claim"
        return "Route accepted; this test makes no structural-effect claim"

    if lower_suite in {"strict-effect", "generated execution: default-corpus"}:
        mapped = transformation_by_case.get(case)
        if mapped:
            return mapped

    transformations = []
    if (
        "iss" in lower_case
        or "iss" in lower_expected
        or lower_suite in {"iss", "iss-multicut", "iss-live"}
    ):
        transformations.append("Index-set splitting (ISS)")
    has_diamond_effect = (
        "full-diamond" in lower_case
        or "diamond" in lower_case
        or "effect:diamond" in lower_expected
        or "effect:diamond" in lower_actual
    )
    if has_diamond_effect:
        transformations.append("Diamond tiling")
    if "second-level" in lower_case or "two-level" in lower_case:
        transformations.append("Two-level tiling")
    elif not has_diamond_effect and (
        "tiled" in lower_case
        or "tiling" in lower_case
        or "tiling:true" in lower_actual
        or "tiling-route=permutable-band" in lower_expected
        or lower_suite in {
            "direct-route",
            "non-second-level-routes",
            "second-level-routes",
            "second-level-tile",
        }
    ):
        transformations.append("Ordinary tiling")
    if "intratile" in lower_case:
        transformations.append("Intra-tile affine rescheduling")
    if "multipar" in lower_case:
        transformations.append("Parallelization of multiple loop dimensions")
    elif (
        "parallel" in lower_case
        or "parallel=true" in lower_actual
        or "par:1" in lower_actual
    ):
        transformations.append("Parallelization")
    if "vector" in lower_case or "vector=true" in lower_actual or "vec:1" in lower_actual:
        if "skipped" in lower_actual or "skip" in lower_case:
            transformations.append("No innermost parallel annotation; eligibility check skipped it")
        else:
            transformations.append("Parallelization restricted to the innermost loop")
    if lower_suite == "parallel-current":
        transformations.append("Parallelization")
    if lower_suite == "vector-current":
        transformations.append("Parallelization restricted to the innermost loop")
    if "unrolljam" in lower_case or "unroll-jam" in lower_case:
        if "dependent" in lower_case:
            transformations.append("Block unrolling; unsafe loop jamming rejected")
        else:
            transformations.append("Block unrolling and validated loop jamming")
    elif "const_unroll" in lower_case or "const-unroll" in lower_case:
        if "unrolled:false" in lower_actual:
            transformations.append("Constant-bound unrolling not applied on this parallel loop")
        else:
            transformations.append("Constant-bound loop unrolling")
    if "nofuse" in lower_case or "no-fuse" in lower_case:
        transformations.append("Loop fission/distribution relative to the fused schedule")
    elif "fusion" in lower_case or "fuse" in lower_case:
        transformations.append("Loop fusion")
    if "fission" in lower_case or "distribution" in lower_case:
        transformations.append("Loop fission/distribution")
    if "affine" in lower_case:
        transformations.append("Affine rescheduling")
    if "stride" in lower_case:
        transformations.append("Stride-preserving loop generation")
    if lower_suite == "typed-c-pipeline":
        typed = {
            "ordinary-tiling-pointwise": "Ordinary tiling",
            "two-level-tiling-matmul": "Two-level tiling",
            "iss-reverse-index": "Index-set splitting (ISS)",
            "diamond-stencil": "Diamond tiling and post-tiling affine rescheduling",
            "parallel-pointwise": "Ordinary tiling and parallelization",
            "vector-pointwise": (
                "Ordinary tiling and parallelization restricted to the innermost loop"
            ),
        }
        return typed.get(case, "; ".join(dict.fromkeys(transformations)))
    if lower_suite == "e2e" and case == "matmul [innermost-parallel]":
        return "Ordinary tiling and parallelization restricted to the innermost loop"
    if lower_suite == "e2e" and case == "matmul [parallel]":
        return "Ordinary tiling and parallelization"
    if lower_suite == "e2e" and case == "matmul [sequential]":
        return "Ordinary tiling"
    if lower_suite == "e2e" and case == "reverse_iss":
        return "ISS route executed; this test asserts output equality, not a structural effect"
    if not transformations:
        if lower_suite == "pluto-compat-suite" and "effect-contracts-matched" in lower_actual:
            if "noop" in lower_case:
                return "Affine rescheduling; the named option adds no loop transformation"
            return "Affine rescheduling"
        if "changed:true" in lower_actual or "effects-matched" in lower_actual:
            return "Affine scheduling and loop reconstruction"
        if "unchanged" in lower_expected or "changed:false" in lower_actual:
            return "No loop-structure change"
        return "No loop transformation asserted by this test"
    return "; ".join(dict.fromkeys(transformations))


def second_level_rejection_records() -> list[dict]:
    """Expand the 116 generated negative cases summarized by the CI log."""
    records = []

    def add(case: str, reason: str, observed: str | None = None) -> None:
        records.append(
            {
                "suite": "second-level rejection",
                "case": case,
                "expected": reason,
                "actual": "PASS; the declared failure point was preserved",
                "coverage": "rejection-contract",
                "observed_transformation": observed,
                "evidence": [
                    "raw/remote-ci-test-results.stdout.txt",
                    "../../source/tools/second_level_tiling/check_rejected_tiling_route.py",
                ],
                "source": ["remote CI"],
            }
        )

    malformed_bases = (
        "ordinary",
        "identity-mixed-depth",
        "second-level",
        "second-level-identity-mixed-depth",
        "diamond",
        "full-diamond",
        "second-level-diamond",
        "second-level-full-diamond",
    )
    malformed = []
    for base in malformed_bases:
        malformed.extend((base, f"{base}-iss"))
    for name in malformed:
        add(f"malformed-{name}", "reject a corrupted tiling relation")

    add("scalar-only", "reject tiling when no non-scalar statement exists")
    add("nonpermutable-band", "reject a non-permutable band")

    for second_level in (False, True):
        for use_iss in (False, True):
            name = "identity-vector-strict"
            if second_level:
                name = f"second-level-{name}"
            if use_iss:
                name = f"{name}-iss"
            observed = (
                "Two-level tiling; no innermost parallel annotation because the hint "
                "was not certifiable"
                if second_level
                else (
                    "Ordinary tiling; no innermost parallel annotation because the hint "
                    "was not certifiable"
                )
            )
            add(name, "keep verified tiling and skip the optional annotation", observed)

    consumer_producers = (
        "ordinary",
        "second-level-iss",
        "identity-mixed-depth",
        "second-level-identity-mixed-depth-iss",
        "diamond",
        "full-diamond-iss",
    )
    for producer in consumer_producers:
        for consumer in ("parallel-current", "vector-current"):
            add(
                f"consumer-{producer}-{consumer}",
                "reject an out-of-range explicit parallel-loop consumer",
            )

    explicit_producers = (
        "ordinary",
        "identity-mixed-depth-iss",
        "second-level",
        "second-level-identity-mixed-depth-iss",
        "diamond",
        "full-diamond-iss",
        "second-level-diamond",
        "second-level-full-diamond-iss",
    )
    for producer in explicit_producers:
        for consumer in ("parallel-current", "vector-current"):
            add(
                f"malformed-{producer}-with-{consumer}",
                "reject the malformed tiling before checking the explicit consumer",
            )

    hinted_producers = ("ordinary", "diamond", "second-level-full-diamond-iss")
    hinted_consumers = (
        "parallel",
        "parallel-strict",
        "multipar",
        "multipar-strict",
        "vector",
        "vector-strict",
    )
    for producer in hinted_producers:
        for consumer in hinted_consumers:
            add(
                f"malformed-{producer}-with-hinted-{consumer}",
                "reject the malformed tiling before adopting a hinted parallel loop",
            )

    affine_producers = (
        "diamond",
        "diamond-iss",
        "full-diamond",
        "full-diamond-iss",
        "second-level-diamond",
        "second-level-diamond-iss",
        "second-level-full-diamond",
        "second-level-full-diamond-iss",
    )
    affine_consumers = (
        "sequential",
        "parallel-current",
        "vector-current",
        "parallel-hint-strict",
        "multipar-hint-strict",
        "vector-hint-strict",
    )
    for producer in affine_producers:
        for consumer in affine_consumers:
            add(
                f"final-affine-{producer}-with-{consumer}",
                "accept the tiling leg, then reject an invalid post-tiling affine schedule",
            )
    require(len(records) == 116, f"expected 116 second-level rejections, found {len(records)}")
    return records


def unit_test_records() -> list[dict]:
    """List subcases hidden behind concise unit-test summaries."""
    groups = {
        "artifact runner timeout": ("tools/artifact/test_artifact_runner_timeout.py", (
            "timeout-preserves-partial-output",
        )),
        "tiling route summary": ("tools/artifact/test_tiling_route_summary.py", (
            "matching-counts-accepted",
            "mismatched-counts-rejected",
        )),
        "release provenance": ("tools/artifact/test_release_provenance.py", (
            "plain-image-digest",
            "registry-qualified-image-digest",
            "empty-image-digest-rejected",
            "unknown-image-digest-rejected",
            "garbage-image-digest-rejected",
            "short-image-digest-rejected",
            "pluto-revision-mismatch-rejected",
            "bug-witness-pluto-revision-mismatch-rejected",
            "invalid-release-tag-rejected",
            "provenance-check-explicitly-disabled",
        )),
        "manifest runner": ("tools/polopt_flag_suites/test_manifest_runner.py", (
            "ordinary-failed-command-accepted-as-rejection",
            "failed-command-with-stale-output-rejected",
        )),
        "tiling route telemetry": ("tools/tiling_routes/test_route_telemetry.py", (
            "direct_band_is_the_only_accepted_route",
            "no_loop_is_the_only_not_applicable_status",
            "extra_route_is_rejected",
            "alarm_is_rejected",
            "fallback_marker_is_case_insensitively_rejected",
            "exact_direct_phase_route_is_accepted",
            "exact_rejected_phase_route_is_accepted",
            "extra_phase_route_is_rejected",
            "fallback_marker_outside_route_is_rejected",
        )),
        "unroll-and-jam route guard": ("tools/artifact/test_unrolljam_route_guard.py", (
            "checks_complete_stderr_not_only_tail",
            "accepts_stderr_without_tiling_route",
            "missing_stderr_fails_closed",
        )),
        "proof report": ("tools/artifact/test_proof_report.py", (
            "clean_report_passes",
            "open_proofs_fail_but_comments_do_not",
            "unrealized_extraction_axiom_fails",
            "missing_listed_route_theorem_fails",
        )),
        "open-proof scanner": ("tools/ci/test_check_open_proofs.py", (
            "rejects_unfinished_commands",
            "ignores_comments_strings_and_identifiers",
            "preserves_line_numbers_across_nested_comments",
            "gate_exit_statuses",
        )),
        "strict transformation effects": (
            "tests/polopt-generated/tools/test_check_polopt_cases.py",
            (
                "changed-case-satisfies-all-effects",
                "unchanged-case-satisfies-all-effects",
                "missing-nontrivial-and-tiling-effects-rejected",
                "unexpected-change-rejected",
            ),
        ),
        "generated C harness": ("tools/end_to_end_c/test_generated_harness.py", (
            "positive-stride-range",
            "negative-stride-range",
            "signed-division-candidate",
            "multidimensional-checksum-indexing",
        )),
        "legacy failure gate": ("tools/ci/check_legacy_failure_exit.sh", (
            "declared-nonzero-exit-accepted",
            "unexpected-nonzero-exit-rejected",
            "unexpected-zero-exit-rejected",
            "missing-command-rejected",
        )),
    }
    records = []
    for group, (source_path, cases) in groups.items():
        for case in cases:
            records.append(
                {
                    "suite": "unit",
                    "case": f"{group}: {case}",
                    "expected": "the declared unit-test condition",
                    "actual": "PASS",
                    "coverage": "unit",
                    "evidence": [
                        "raw/remote-ci-test-results.stdout.txt",
                        f"../../source/{source_path}",
                    ],
                    "source": ["remote CI"],
                }
            )

    zero_fallback = (
        "SBandTilingOpt.reject_tiling",
        "SBandTilingOpt.Rejected selector",
        "SBandTilingOpt post-tiling affine rejection",
        "SParallelPolOpt.reject_tiling",
        "SParallelPolOpt.Rejected selector",
        "SParallelPolOpt post-tiling affine rejection",
    )
    for case in zero_fallback:
        records.append(
            {
                "suite": "unit",
                "case": f"extracted zero fallback: {case}",
                "expected": "raise CertCheckerFailure and return no unchecked program",
                "actual": "PASS",
                "coverage": "unit",
                "evidence": [
                    "raw/extracted-zero-fallback-gate.stdout.txt",
                    "raw/remote-ci-test-results.stdout.txt",
                    "../../source/tests/extracted-zero-fallback/test.ml",
                ],
                "source": ["local artifact run", "remote CI"],
                "occurrences": 2,
            }
        )
    return records


def display_case_name(suite: str, case: str, expected: str) -> str:
    if suite == "E2E" and case == "matmul":
        if "parallel=true" in expected:
            return "matmul [parallel]"
        if "vector=true" in expected:
            return "matmul [innermost-parallel]"
        return "matmul [sequential]"
    return case


def catalog_suite_name(suite: str) -> str:
    return {
        "pluto-compat-suite": "driver option configurations",
        "non-second-level-routes": "one-level tiling configurations",
        "SECOND-LEVEL-TILE": "two-level tiling configurations",
        "second-level-routes": "two-level tiling route checks",
        "direct-route": "direct tiling-validator routes",
        "PARALLEL-CURRENT": "parallel-loop validation",
        "VECTOR-CURRENT": "innermost parallel-loop validation",
        "ISS": "ISS validator",
        "ISS-LIVE": "ISS from live Pluto output",
        "ISS-MULTICUT": "ISS multi-cut validation",
        "strict-effect": "default optimization structural effects",
        "E2E": "handwritten C execution",
        "diamond-suite": "diamond tiling",
        "typed-c-pipeline": "typed C instruction pipelines",
        "legacy/pluto-all": "affine schedule refinement",
        "legacy/readscop": "OpenScop round trips",
        "legacy-failure-gate": "legacy failure propagation",
        "legacy/cpol-openscop": "CPoly-to-OpenScop conversion",
        "legacy/pluto": "scheduler conversion smoke test",
        "legacy/csample1": "typed C refinement: matrix multiplication",
        "legacy/csample2": "typed C refinement: covariance",
        "legacy/csample3": "typed C refinement: GEMVER",
    }.get(suite, suite)


CATALOG_HIERARCHY = (
    (
        "Verified Transformations",
        "Validator and effect checks for individual loop transformations.",
        (
            ("Affine Schedule Validation", ("affine schedule refinement",)),
            (
                "Index-Set Splitting (ISS)",
                (
                    "ISS validator",
                    "ISS from live Pluto output",
                    "ISS multi-cut validation",
                    "identity-iss-sensitive-search",
                ),
            ),
            (
                "One-Level and Direct Tiling Validation",
                (
                    "one-level tiling configurations",
                    "direct tiling-validator routes",
                    "scalar-interleaved tiling",
                ),
            ),
            (
                "Two-Level Tiling",
                ("two-level tiling configurations", "two-level tiling route checks"),
            ),
            (
                "Diamond Tiling",
                ("diamond tiling", "identity-diamond-sensitive-search"),
            ),
            (
                "Parallel Loops",
                ("parallel-loop validation", "innermost parallel-loop validation"),
            ),
            (
                "Unroll and Jam",
                ("unroll-and-jam exploration", "code-generation gap exploration"),
            ),
        ),
    ),
    (
        "End-to-End Checks",
        "Generated programs, executable comparisons, and typed instruction examples.",
        (
            (
                "Observed Loop-Structure Effects",
                ("default optimization structural effects",),
            ),
            (
                "Executable Loop Comparisons",
                (
                    "generated execution: default-corpus",
                    "generated execution: parallel-effect",
                    "generated execution: second-level-effect",
                    "generated execution: intratile-effect",
                ),
            ),
            (
                "Typed Instruction Programs",
                (
                    "handwritten C execution",
                    "typed C instruction pipelines",
                    "typed C refinement: matrix multiplication",
                    "typed C refinement: covariance",
                    "typed C refinement: GEMVER",
                ),
            ),
        ),
    ),
    (
        "Compiler Interface",
        "Driver options, composition routes, and format adapters.",
        (
            ("Driver Options", ("driver option configurations",)),
            ("Composition Routes", ("identity composition",)),
            (
                "Formats and Scheduler Adapter",
                (
                    "OpenScop round trips",
                    "CPoly-to-OpenScop conversion",
                    "scheduler conversion smoke test",
                ),
            ),
        ),
    ),
    (
        "Rejected Candidates",
        "Candidates that PolCert rejects without emitting unchecked code.",
        (
            ("Tiling and Consumer Rejections", ("second-level rejection",)),
            ("Invalid and Non-Certifiable Proposals", ("optimizer-output rejection",)),
        ),
    ),
    (
        "Test Harness",
        "Unit checks and failure propagation for the artifact tooling.",
        (
            ("Unit Checks", ("unit",)),
            ("Failure Propagation", ("legacy failure propagation",)),
        ),
    ),
)


SUITE_NOTES = {
    "identity-iss-sensitive-search": (
        "The search log contains only the totals: 42 equal outputs and 29 paired "
        "failures. It does not identify the outcome for each input."
    ),
}


def catalog_location(suite: str) -> tuple[str, str]:
    for category, _description, families in CATALOG_HIERARCHY:
        for family, suites in families:
            if suite in suites:
                return category, family
    raise ValueError(f"unclassified test suite: {suite}")


def prepare_program_comparisons(destination: Path, source: Path) -> dict:
    """Materialize exact program pairs that belong to catalog configurations."""
    raw = destination / "raw"
    output = destination / "program-comparisons"
    output.mkdir()
    pairs: dict[tuple[str, str], dict] = {}
    producer: dict[str, str] = {}

    def add_text(
        suite: str,
        case: str,
        before: str,
        after: str,
        *,
        left_label: str = "Before Program",
        right_label: str = "Accepted Program",
        extension: str = "loop",
        kind: str = "accepted-program-pair",
        note: str | None = None,
    ) -> None:
        key = (suite, case)
        require(key not in pairs, f"duplicate program comparison: {suite}/{case}")
        digest = hashlib.sha256(f"{suite}\0{case}".encode()).hexdigest()[:14]
        pair_dir = output / digest
        pair_dir.mkdir()
        before_path = pair_dir / f"before.{extension}"
        after_path = pair_dir / f"after.{extension}"
        before_path.write_text(before.rstrip() + "\n", encoding="utf-8")
        after_path.write_text(after.rstrip() + "\n", encoding="utf-8")
        pair = {
            "suite": suite,
            "case": case,
            "before": before_path.relative_to(destination).as_posix(),
            "after": after_path.relative_to(destination).as_posix(),
            "left_label": left_label,
            "right_label": right_label,
            "kind": kind,
        }
        if note:
            pair["note"] = note
        pairs[key] = pair

    def add_files(
        suite: str,
        case: str,
        before: Path,
        after: Path,
        **kwargs: object,
    ) -> None:
        require(before.is_file(), f"missing before program: {before}")
        require(after.is_file(), f"missing after program: {after}")
        add_text(
            suite,
            case,
            before.read_text(encoding="utf-8"),
            after.read_text(encoding="utf-8"),
            **kwargs,
        )

    def split_iss_bridge(path: Path) -> tuple[str, str]:
        lines = path.read_text(encoding="utf-8").splitlines()
        before_start = next(
            index for index, line in enumerate(lines) if line.startswith("BEFORE_STMTS ")
        )
        after_start = next(
            index for index, line in enumerate(lines) if line.startswith("AFTER_STMTS ")
        )
        header = lines[:before_start]
        before = "\n".join([*header, *lines[before_start:after_start]]) + "\n"
        after = "\n".join([*header, *lines[after_start:]]) + "\n"
        return before, after

    collected = raw / "program-comparisons/index.json"
    require(
        collected.is_file(),
        "missing exact program comparisons; run collect_program_comparisons.py "
        "with the frozen Release image before packaging",
    )
    collected_root = collected.parent
    collected_data = load_json(collected)
    producer = collected_data.get("producer", {})
    require(
        collected_data.get("producer", {}).get("polopt_sha256")
        == "030245cf9741692a0dc29b000aef82e50620396f756a0ea8af0163aa05f49eaf",
        "program comparisons were not collected by the frozen Release binary",
    )
    require(
        collected_data.get("producer", {}).get("fixed_pluto_sha256")
        == "60e6c714f9b804257aae52844b93b203a6ee4d8336bbb70235f000669005d980",
        "program comparisons were not collected with the frozen fixed Pluto",
    )
    require(
        collected_data.get("producer", {}).get("historical_polycc_sha256")
        == "9b42e43485e3ebaf81fa96add84235f6f70745d8bd1093a2acb5f1a14e31991d",
        "rejection comparisons were not collected with the frozen historical Pluto",
    )
    for pair in collected_data["pairs"]:
        add_files(
            pair["suite"],
            pair["case"],
            collected_root / pair["before"],
            collected_root / pair["after"],
            left_label=pair["left_label"],
            right_label=pair["right_label"],
            extension=Path(pair["before"]).suffix.lstrip(".") or "txt",
            kind=pair.get("kind", "accepted-program-pair"),
            note=pair.get("note"),
        )
    shutil.rmtree(collected_root)

    typed = raw / "typed-program-comparisons"
    if typed.is_dir():
        for case_dir in sorted(path for path in typed.iterdir() if path.is_dir()):
            add_files(
                "typed C instruction pipelines",
                case_dir.name,
                case_dir / "before.loop",
                case_dir / "after.loop",
                left_label="Typed Input Program",
                right_label="Accepted Verified Program",
            )
        shutil.rmtree(typed)

    refinement = raw / "typed-refinement-comparisons"
    if refinement.is_dir():
        refinement_suites = {
            "csample1": "typed C refinement: matrix multiplication",
            "csample2": "typed C refinement: covariance",
            "csample3": "typed C refinement: GEMVER",
        }
        for directory, suite in refinement_suites.items():
            before = refinement / directory / "orig.cpol"
            after = refinement / directory / "opt.cpol"
            for case in ("orig-to-opt", "opt-to-orig"):
                left, right = (before, after) if case == "orig-to-opt" else (after, before)
                add_files(
                    suite,
                    case,
                    left,
                    right,
                    extension="cpol",
                    left_label=(
                        "Original Typed Polyhedral Program"
                        if case == "orig-to-opt"
                        else "Optimizer-Proposed Typed Polyhedral Program"
                    ),
                    right_label=(
                        "Optimizer-Proposed Typed Polyhedral Program"
                        if case == "orig-to-opt"
                        else "Original Typed Polyhedral Program"
                    ),
                    note=(
                        "The test checks refinement in both directions between "
                        "these two typed polyhedral programs."
                    ),
                )
        shutil.rmtree(refinement)

    unroll_root = raw / "unrolljam"
    unroll_summary = unroll_root / "summary.json"
    if unroll_summary.is_file():
        for item in load_json(unroll_summary)["cases"]:
            fixture = Path(item["fixture"])
            case = fixture.stem
            case_dir = unroll_root / item["case_dir"] if "case_dir" in item else None
            if case_dir is None or not case_dir.is_dir():
                encoded = fixture.as_posix().replace("/", "__")
                case_dir = unroll_root / encoded
            stdout = (case_dir / "polopt.stdout.txt").read_text(encoding="utf-8")
            marker = "== Optimized Loop =="
            require(marker in stdout, f"missing optimized Loop for unroll/jam {case}")
            add_text(
                "unroll-and-jam exploration",
                case,
                (source / fixture).read_text(encoding="utf-8"),
                stdout.split(marker, 1)[1].lstrip(),
            )

    diamond_root = raw / "diamond-suite"
    diamond_summary = diamond_root / "summary.json"
    if diamond_summary.is_file():
        for item in load_json(diamond_summary)["results"]:
            if item["status"] not in {"diamond", "no_effect"}:
                continue
            case = item["case"]
            stem = Path(case).stem
            run = diamond_root / stem / "diamond"
            add_files(
                "diamond tiling",
                case,
                run / case,
                run / f"{stem}.pluto.c",
                extension="c",
                left_label="Input C Program",
                right_label="Diamond-Tiled C Program",
            )

    identity_diamond = raw / "identity/diamond"
    if identity_diamond.is_dir():
        for case_dir in sorted(path for path in identity_diamond.iterdir() if path.is_dir()):
            case = case_dir.name
            ordinary = case_dir / f"{case}.identity.tile.scop.pluto.c"
            diamond = case_dir / f"{case}.identity.diamond.scop.pluto.c"
            if ordinary.is_file() and diamond.is_file():
                add_files(
                    "identity-diamond-sensitive-search",
                    case,
                    ordinary,
                    diamond,
                    extension="c",
                    left_label="Identity-Tiled C Program",
                    right_label="Identity Diamond-Tiled C Program",
                    note=(
                        "This search compares two generated programs; it is not a "
                        "source-to-target compilation count."
                    ),
                )

    gap = raw / "codegen-gaps"
    if gap.is_dir():
        add_files(
            "code-generation gap exploration",
            "matmul-unroll-and-jam",
            gap / "nounrolljam/matmul.scop.pluto.c",
            gap / "unrolljam/matmul.scop.pluto.c",
            extension="c",
            left_label="Pluto C without Unroll-and-Jam",
            right_label="Pluto C with Unroll-and-Jam",
        )

    identity_summary = raw / "identity-composition-exploration.stdout.txt"
    if identity_summary.is_file():
        identity = load_json(identity_summary)
        second = identity["results"][0]
        stdout = second["polopt_identity_second_level"]["stdout"]
        marker = "== Optimized Loop =="
        require(marker in stdout, "missing identity second-level optimized Loop")
        add_text(
            "identity composition",
            f"{second['case']} [identity second-level]",
            (source / "tests/polopt-regression/inputs/fusion7.loop").read_text(
                encoding="utf-8"
            ),
            stdout.split(marker, 1)[1].lstrip(),
        )

    iss_pairs = {
        "reverse_before.txt-to-reverse_after.txt": (
            "reverse_before.txt",
            "reverse_after.txt",
        ),
        "multi_stmt_periodic_before.txt-to-multi_stmt_periodic_after.txt": (
            "multi_stmt_periodic_before.txt",
            "multi_stmt_periodic_after.txt",
        ),
        "jacobi_2d_periodic_before.txt-to-jacobi_2d_periodic_after.txt": (
            "jacobi_2d_periodic_before.txt",
            "jacobi_2d_periodic_after.txt",
        ),
        "heat_2dp_before.txt-to-heat_2dp_after.txt": (
            "heat_2dp_before.txt",
            "heat_2dp_after.txt",
        ),
    }
    iss_root = source / "tests/iss-pluto-dumps"
    for case, (before, after) in iss_pairs.items():
        add_files(
            "ISS validator",
            case,
            iss_root / before,
            iss_root / after,
            extension="txt",
            left_label="Before ISS Proposal",
            right_label="Accepted Split Proposal",
        )

    tiling_fixtures = source / "tools/tiling_routes/fixtures"
    add_files(
        "scalar-interleaved tiling",
        "frozen-positive",
        tiling_fixtures / "fusion5-scalar-interleaved.midtransform.scop",
        tiling_fixtures / "fusion5-scalar-interleaved.posttile.scop",
        extension="scop",
        left_label="Before Tiling SCoP",
        right_label="Accepted Tiled SCoP",
    )
    add_files(
        "direct tiling-validator routes",
        "frozen-diamond-phase-pair",
        tiling_fixtures / "diamond-tile-example.midtransform.scop",
        tiling_fixtures / "diamond-tile-example.posttile.scop",
        extension="scop",
        left_label="Before Tiling SCoP",
        right_label="Accepted Tiled SCoP",
    )
    add_files(
        "direct tiling-validator routes",
        "frozen-nonpermutable-band",
        tiling_fixtures / "nonpermutable-band.midtransform.scop",
        tiling_fixtures / "nonpermutable-band.posttile.scop",
        extension="scop",
        left_label="Input Polyhedral Program",
        right_label="Rejected Non-Permutable Tiling Candidate",
        kind="rejected-candidate-pair",
    )
    second_fixtures = source / "tools/second_level_tiling/fixtures"
    add_files(
        "two-level tiling route checks",
        "trailing-zero-normalized-standalone-formal-validation",
        second_fixtures / "fusion7-second-level-zero-normalized.mid.openscop",
        second_fixtures / "fusion7-second-level-zero-normalized.post.openscop",
        extension="scop",
        left_label="Before Two-Level Tiling SCoP",
        right_label="Accepted Two-Level Tiled SCoP",
    )

    iss_root = source / "tests/iss-pluto-dumps"
    for case, filename in (
        ("pluto-three-cut-four-piece-mismatch", "multicut_native_mismatch.bridge"),
        ("two-cut-missing-piece", "multicut_missing_piece.bridge"),
    ):
        before, after = split_iss_bridge(iss_root / filename)
        add_text(
            "ISS multi-cut validation",
            case,
            before,
            after,
            left_label="Original Statement Domain",
            right_label="Rejected Split-Domain Candidate",
            extension="bridge",
            kind="rejected-candidate-pair",
        )

    identity_wavefront = raw / "identity/diamond/wavefront"
    add_files(
        "identity composition",
        "wavefront [identity diamond]",
        identity_wavefront
        / "wavefront.identity.diamond.scop.midtransform.scop",
        identity_wavefront
        / "wavefront.identity.diamond.scop.posttile.scop",
        extension="scop",
        left_label="Before Diamond Tiling SCoP",
        right_label="Rejected Diamond-Tiling Candidate",
        kind="rejected-candidate-pair",
        note=(
            "The tiling validator rejects this identity-plus-diamond proposal; "
            "the pipeline emits no target Loop program."
        ),
    )

    manifest = {
        "producer": producer,
        "pairs": sorted(pairs.values(), key=lambda item: (item["suite"], item["case"])),
    }
    (output / "index.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return pairs


def prepare_test_catalog(
    destination: Path,
    source: Path,
    artifact_results: dict,
    remote_commands: list[dict],
    transformation_summary: dict,
    executable_summary: dict,
    witness_summary: dict,
    program_pairs: dict[tuple[str, str], dict],
) -> dict:
    """Generate a reviewer-facing inventory of every recorded test case."""
    raw_output = destination / "raw"
    transformation_by_case = {
        item["case"]: item["observed_transformation"]
        for item in transformation_summary["cases"]
    }
    records: list[dict] = []
    by_key: dict[tuple[str, str, str, str], dict] = {}

    def add(record: dict) -> None:
        raw_suite = record["suite"]
        raw_case = record["case"]
        suite = catalog_suite_name(raw_suite)
        category, family = catalog_location(suite)
        case = display_case_name(raw_suite, raw_case, record.get("expected", ""))
        expected = record.get("expected", "not separately recorded")
        actual = record.get("actual", "PASS")
        coverage = record.get("coverage", "recorded result")
        observed = record.get("observed_transformation") or observed_transformation(
            raw_suite,
            case,
            expected,
            actual,
            coverage,
            transformation_by_case,
        )
        program_evidence = list(record.get("program_evidence", []))
        if (
            raw_suite.lower() in {"strict-effect", "generated execution: default-corpus"}
            and case in transformation_by_case
        ):
            example = f"../optimized-loop-examples/{case}"
            program_evidence = list(
                dict.fromkeys(
                    [
                        f"{example}/comparison.html",
                        f"{example}/input.pretty.loop",
                        f"{example}/optimized.loop",
                        f"{example}/diff.patch",
                        *program_evidence,
                    ]
                )
            )
        elif raw_suite == "E2E" and raw_case in E2E_RECORDED_LOOP_CASES:
            example_case = f"e2e-{raw_case.replace('_', '-')}"
            example = f"../optimized-loop-examples/{example_case}"
            program_evidence = [f"{example}/comparison.html"]
        program_pair = program_pairs.get((suite, case))
        if program_pair:
            program_evidence = [program_pair["before"], program_pair["after"]]
        key = (suite, case, expected, actual)
        if key in by_key:
            current = by_key[key]
            current["occurrences"] += record.get("occurrences", 1)
            current["program_evidence"] = list(
                dict.fromkeys([*current["program_evidence"], *program_evidence])
            )
            current["evidence"] = list(
                dict.fromkeys([*current["evidence"], *record.get("evidence", [])])
            )
            current["source"] = list(
                dict.fromkeys([*current["source"], *record.get("source", [])])
            )
            if program_pair:
                require(
                    current.get("program_pair", program_pair) == program_pair,
                    f"conflicting program pairs for {suite}/{case}",
                )
                current["program_pair"] = program_pair
            return
        current = {
            "category": category,
            "family": family,
            "suite": suite,
            "case": case,
            "expected": expected,
            "observed_transformation": observed,
            "actual": actual,
            "coverage": coverage,
            "status": record.get("status", "PASS"),
            "occurrences": record.get("occurrences", 1),
            "source": record.get("source", []),
            "program_evidence": program_evidence,
            "evidence": record.get("evidence", []),
        }
        if program_pair:
            current["program_pair"] = program_pair
        if suite == "optimizer-output rejection" and case == "matmul-parallel-hint":
            current["input_program"] = {
                "path": "../../source/tests/polopt-generated/inputs/matmul.loop",
                "label": "Input Loop Program",
            }
            current["program_evidence"] = list(
                dict.fromkeys(
                    [
                        "../../source/tests/polopt-generated/inputs/matmul.loop",
                        *current["program_evidence"],
                    ]
                )
            )
        by_key[key] = current
        records.append(current)

    case_line = re.compile(r"\[([^]]+)\] PASS case=([^ ]+)(.*)$")
    scalar_line = re.compile(r"\[scalar-interleaved\] ([^:]+): PASS$")
    for result in artifact_results["results"]:
        filename = Path(result["stdout_path"]).name
        text = (raw_output / filename).read_text(encoding="utf-8")
        for line in text.splitlines():
            match = case_line.search(line)
            if match:
                fields = result_fields(match.group(3))
                add(
                    {
                        "suite": match.group(1),
                        "case": match.group(2),
                        "expected": fields.get("expected", "PASS"),
                        "actual": fields.get("actual", "PASS"),
                        "coverage": fields.get("coverage", "recorded result"),
                        "source": ["local artifact run"],
                        "evidence": [f"raw/{filename}"],
                    }
                )
                continue
            scalar = scalar_line.search(line)
            if scalar:
                positive = scalar.group(1) == "frozen-positive"
                add(
                    {
                        "suite": "scalar-interleaved tiling",
                        "case": scalar.group(1),
                        "expected": "accept exact tiling" if positive else "reject mutated tiling",
                        "actual": "accepted" if positive else "rejected",
                        "coverage": "effect" if positive else "rejection-contract",
                        "source": ["local artifact run"],
                        "evidence": [f"raw/{filename}"],
                    }
                )

    remote_text = (raw_output / "remote-ci-test-results.stdout.txt").read_text(
        encoding="utf-8"
    )
    for line in remote_text.splitlines():
        match = case_line.search(line)
        if match and match.group(1) != "E2E-GEN":
            fields = result_fields(match.group(3))
            add(
                {
                    "suite": match.group(1),
                    "case": match.group(2),
                    "expected": fields.get("expected", "PASS"),
                    "actual": fields.get("actual", "PASS"),
                    "coverage": fields.get("coverage", "recorded result"),
                    "source": ["remote CI"],
                    "evidence": ["raw/remote-ci-test-results.stdout.txt"],
                }
            )
            continue
        csample = re.search(r"\[(legacy/csample[123])\] PASS check=([^ ]+)(.*)$", line)
        if csample:
            fields = result_fields(csample.group(3))
            add(
                {
                    "suite": csample.group(1),
                    "case": csample.group(2),
                    "expected": fields.get("expected", "refinement succeeds"),
                    "actual": fields.get("actual", "PASS"),
                    "coverage": "refinement",
                    "source": ["remote CI"],
                    "evidence": ["raw/remote-ci-test-results.stdout.txt"],
                }
            )
    for suite, case, expected, actual in (
        (
            "legacy/cpol-openscop",
            "both-conversions",
            "both conversions succeed",
            "both conversions succeeded",
        ),
        ("legacy/pluto", "scheduler-smoke", "scheduler succeeds", "scheduler succeeded"),
    ):
        add(
            {
                "suite": suite,
                "case": case,
                "expected": expected,
                "actual": actual,
                "coverage": "smoke",
                "source": ["remote CI"],
                "evidence": ["raw/remote-ci-test-results.stdout.txt"],
            }
        )

    for record in unit_test_records():
        add(record)
    for record in second_level_rejection_records():
        add(record)

    unroll = load_json(raw_output / "unrolljam/summary.json")
    for case in unroll["cases"]:
        effect = bool(case["polopt_checked_effect"])
        add(
            {
                "suite": "unroll-and-jam exploration",
                "case": Path(case["fixture"]).stem,
                "expected": case["note"],
                "actual": f"checked-effect={str(effect).lower()}",
                "coverage": "effect",
                "source": ["local artifact run"],
                "evidence": [
                    "raw/unrolljam/summary.json",
                    f"../../source/{case['fixture']}",
                ],
            }
        )

    codegen_gap = load_json(raw_output / "codegen-gap-exploration.stdout.txt")
    add(
        {
            "suite": "code-generation gap exploration",
            "case": "matmul-unroll-and-jam",
            "expected": "checked block unrolling, local jam validation, and remainder loop",
            "actual": "all checked markers present; optimized program accepted",
            "coverage": "effect",
            "observed_transformation": "Block unrolling and validated loop jamming",
            "source": ["local artifact run"],
            "evidence": ["raw/codegen-gap-exploration.stdout.txt"],
        }
    )

    identity = load_json(raw_output / "identity-composition-exploration.stdout.txt")
    direct_second, direct_diamond, diamond_search, iss_search = identity["results"]
    add(
        {
            "suite": "identity composition",
            "case": f"{direct_second['case']} [identity second-level]",
            "expected": "two-level tiling remains effective with identity affine scheduling",
            "actual": "accepted; first- and second-level tile markers observed",
            "coverage": "effect",
            "observed_transformation": "Two-level tiling",
            "source": ["local artifact run"],
            "evidence": ["raw/identity-composition-exploration.stdout.txt"],
        }
    )
    add(
        {
            "suite": "identity composition",
            "case": f"{direct_diamond['case']} [identity diamond]",
            "expected": "reject an unsupported identity-plus-diamond route",
            "actual": "rejected; no optimized loop emitted",
            "coverage": "rejection-contract",
            "source": ["local artifact run"],
            "evidence": ["raw/identity-composition-exploration.stdout.txt"],
        }
    )
    diamond_root = raw_output / "identity/diamond"
    fixture_names = sorted(
        path.stem
        for path in (source / "tests/polopt-regression/inputs").glob("*.loop")
    )
    require(
        len(fixture_names) == diamond_search["fixtures_checked"] == 71,
        "identity search size mismatch",
    )
    for name in fixture_names:
        case_root = diamond_root / name
        exported = any(case_root.glob("*.scop"))
        add(
            {
                "suite": "identity-diamond-sensitive-search",
                "case": name,
                "expected": "compare identity tiling with identity diamond tiling",
                "actual": (
                    "same generated C; no distinct diamond effect"
                    if exported
                    else "export-failed; recorded as one of two aggregate export failures"
                ),
                "coverage": "effect search",
                "source": ["local artifact run"],
                "evidence": [
                    "raw/identity-composition-exploration.stdout.txt",
                    f"../../source/tests/polopt-regression/inputs/{name}.loop",
                ],
            }
        )
        add(
            {
                "suite": "identity-iss-sensitive-search",
                "case": name,
                "expected": "compare identity tiling with and without ISS",
                "actual": "included in the suite-level result",
                "coverage": "effect search",
                "status": "SUITE RESULT",
                "source": ["local artifact run"],
                "evidence": [
                    "raw/identity-composition-exploration.stdout.txt",
                    f"../../source/tests/polopt-regression/inputs/{name}.loop",
                ],
            }
        )

    for suite in executable_summary["suites"]:
        for case in suite["cases"]:
            add(
                {
                    "suite": f"generated execution: {suite['name']}",
                    "case": case["case"],
                    "expected": case["expected"],
                    "actual": case["actual"],
                    "coverage": case["coverage"],
                    "source": ["remote CI"],
                    "evidence": ["../execution-comparisons/validation.log"],
                }
            )

    for witness in witness_summary["results"]:
        add(
            {
                "suite": "optimizer-output rejection",
                "case": witness["case"],
                "expected": witness["reason_not_accepted"],
                "actual": witness["polcert_outcome"],
                "coverage": "rejection-contract",
                "source": ["local release validation", "remote CI"],
                "evidence": [
                    "../rejected-optimizer-outputs/index.html",
                    "raw/remote-ci-test-results.stdout.txt",
                ],
                "occurrences": 2,
            }
        )

    suite_order = {}
    for category_index, (_category, _description, families) in enumerate(
        CATALOG_HIERARCHY
    ):
        for family_index, (_family, suites) in enumerate(families):
            for suite_index, suite in enumerate(suites):
                suite_order[suite] = (category_index, family_index, suite_index)
    records.sort(
        key=lambda item: (
            *suite_order[item["suite"]],
            item["case"].lower(),
            item["expected"],
        )
    )
    expected_suite_counts = {
        "driver option configurations": 189,
        "second-level rejection": 116,
        "one-level tiling configurations": 90,
        "identity-diamond-sensitive-search": 71,
        "identity-iss-sensitive-search": 71,
        "generated execution: default-corpus": 62,
        "affine schedule refinement": 62,
        "default optimization structural effects": 62,
        "two-level tiling configurations": 58,
        "unit": 53,
        "two-level tiling route checks": 23,
        "direct tiling-validator routes": 20,
        "diamond tiling": 19,
        "handwritten C execution": 15,
        "innermost parallel-loop validation": 12,
        "unroll-and-jam exploration": 11,
        "parallel-loop validation": 9,
        "ISS validator": 7,
        "ISS from live Pluto output": 7,
        "optimizer-output rejection": 7,
        "OpenScop round trips": 6,
        "typed C instruction pipelines": 6,
        "scalar-interleaved tiling": 5,
        "ISS multi-cut validation": 3,
        "generated execution: parallel-effect": 3,
        "legacy failure propagation": 3,
        "identity composition": 2,
        "typed C refinement: matrix multiplication": 2,
        "typed C refinement: covariance": 2,
        "typed C refinement: GEMVER": 2,
        "CPoly-to-OpenScop conversion": 1,
        "code-generation gap exploration": 1,
        "generated execution: intratile-effect": 1,
        "generated execution: second-level-effect": 1,
        "scheduler conversion smoke test": 1,
    }
    actual_suite_counts: dict[str, int] = {}
    for record in records:
        actual_suite_counts[record["suite"]] = actual_suite_counts.get(record["suite"], 0) + 1
    require(
        actual_suite_counts == expected_suite_counts,
        "complete test-catalog count mismatch:\n"
        f"expected={expected_suite_counts}\nactual={actual_suite_counts}",
    )
    require(
        set(suite_order) == set(actual_suite_counts),
        "test-catalog hierarchy does not match the recorded suites",
    )
    require(len(records) == 1003, f"expected 1003 test configurations, found {len(records)}")
    local_commands = []
    for result in artifact_results["results"]:
        local_commands.append(
            {
                "name": result["name"],
                "command": " ".join(result["command"]),
                "elapsed_seconds": result["elapsed_seconds"],
                "status": "PASS" if result["ok"] else "FAIL",
                "evidence": f"raw/{Path(result['stdout_path']).name}",
            }
        )

    recorded_results = sum(item["occurrences"] for item in records)
    require(recorded_results == 1508, f"expected 1508 recorded results, found {recorded_results}")
    hierarchy = []
    for category, description, families in CATALOG_HIERARCHY:
        family_entries = []
        for family, suites in families:
            suite_entries = [
                {
                    "name": suite,
                    "configurations": actual_suite_counts[suite],
                    **({"note": SUITE_NOTES[suite]} if suite in SUITE_NOTES else {}),
                }
                for suite in suites
            ]
            family_entries.append(
                {
                    "name": family,
                    "configurations": sum(
                        entry["configurations"] for entry in suite_entries
                    ),
                    "suites": suite_entries,
                }
            )
        hierarchy.append(
            {
                "name": category,
                "description": description,
                "configurations": sum(
                    entry["configurations"] for entry in family_entries
                ),
                "families": family_entries,
            }
        )
    family_count = sum(len(category["families"]) for category in hierarchy)
    require(len(hierarchy) == 5, f"expected 5 catalog categories, found {len(hierarchy)}")
    require(family_count == 17, f"expected 17 catalog families, found {family_count}")

    def evidence_label(item: str) -> str:
        filename = Path(urlsplit(item).path).name
        if item.endswith("docs/index.html#typed-loop-examples"):
            return "input/accepted shapes"
        return {
            "comparison.html": "before/after",
            "input.pretty.loop": "before",
            "optimized.loop": "after",
            "diff.patch": "diff",
            "validation.log": "validation log",
            "status.txt": "compiler log",
            "strict-loop-suite.stdout.txt": "local log",
            "remote-ci-test-results.stdout.txt": "CI log",
        }.get(
            filename,
            "test log" if filename.endswith(".stdout.txt") else filename or item,
        )

    def case_links(items: list[str]) -> str:
        ordered = sorted(
            items,
            key=lambda item: evidence_label(item).endswith("log"),
        )
        return " &middot; ".join(
            f'<a href="../{escape(item, quote=True)}">'
            f'{escape(evidence_label(item))}</a>'
            for item in ordered
        )

    def resolve_program_file(record: dict, filename: str) -> Path | None:
        for item in record["program_evidence"]:
            link = urlsplit(item)
            if Path(link.path).name == filename:
                target = (destination / unquote(link.path)).resolve()
                if target.is_file():
                    return target
        for item in record["program_evidence"]:
            link = urlsplit(item)
            if Path(link.path).name == "comparison.html":
                target = (destination / unquote(link.path)).resolve().parent / filename
                if target.is_file():
                    return target
        return None

    cases_dir = destination / "cases"
    cases_dir.mkdir()
    for index, record in enumerate(records):
        pair = record.get("program_pair")
        before = resolve_program_file(record, "input.pretty.loop")
        after = resolve_program_file(record, "optimized.loop")
        exact_loop_pair = before is not None and after is not None
        if pair:
            before = destination / pair["before"]
            after = destination / pair["after"]
            require(before.is_file(), f"missing catalog before program: {before}")
            require(after.is_file(), f"missing catalog after program: {after}")
            record["view_kind"] = pair["kind"]
            note = (
                f'<p class="comparison-note">{escape(pair["note"])}</p>'
                if pair.get("note")
                else ""
            )
            comparison = f"""
  <div class="loop-comparison">
    <section>
      <h2>{escape(pair["left_label"])}</h2>
      <pre>{escape(before.read_text(encoding="utf-8"))}</pre>
    </section>
    <section>
      <h2>{escape(pair["right_label"])}</h2>
      <pre>{escape(after.read_text(encoding="utf-8"))}</pre>
    </section>
  </div>
  {note}
  <section class="comparison-result">
    <h2>Validation Result</h2>
    <dl>
      <dt>Expected</dt><dd>{escape(record["expected"])}</dd>
      <dt>Observed effect</dt><dd>{escape(record["observed_transformation"])}</dd>
      <dt>Actual</dt><dd>{escape(record["actual"])}</dd>
      <dt>Status</dt><dd>{escape(record["status"])}</dd>
    </dl>
  </section>"""
        elif exact_loop_pair:
            record["view_kind"] = "loop-before-after"
            comparison = f"""
  <div class="loop-comparison">
    <section>
      <h2>Before</h2>
      <pre>{escape(before.read_text(encoding="utf-8"))}</pre>
    </section>
    <section>
      <h2>Accepted Output</h2>
      <pre>{escape(after.read_text(encoding="utf-8"))}</pre>
    </section>
  </div>
  <section class="comparison-result">
    <h2>Validation Result</h2>
    <dl>
      <dt>Expected</dt><dd>{escape(record["expected"])}</dd>
      <dt>Observed effect</dt><dd>{escape(record["observed_transformation"])}</dd>
      <dt>Actual</dt><dd>{escape(record["actual"])}</dd>
      <dt>Status</dt><dd>{escape(record["status"])}</dd>
    </dl>
  </section>"""
        else:
            input_program = record.get("input_program")
            record["view_kind"] = (
                "input-no-target" if input_program else "result-summary"
            )
            input_section = ""
            if input_program:
                input_path = (destination / input_program["path"]).resolve()
                require(input_path.is_file(), f"missing catalog input program: {input_path}")
                input_section = f"""
  <section class="single-program">
    <h2>{escape(input_program["label"])}</h2>
    <pre>{escape(input_path.read_text(encoding="utf-8"))}</pre>
  </section>
  <p class="comparison-note">
    Strict validation stops before code generation, so this case has no target
    or rejected candidate program to display.
  </p>"""
            expected_label = (
                "Test"
                if record["expected"] == "the declared unit-test condition"
                else "Expected"
            )
            expected_value = (
                record["case"]
                if record["expected"] == "the declared unit-test condition"
                else record["expected"]
            )
            coverage = (
                f'<dt>Coverage</dt><dd>{escape(record["coverage"])}</dd>'
                if record["coverage"] not in {"recorded result", "unit"}
                else ""
            )
            comparison = f"""
  {input_section}
  <section class="result-summary">
    <h2>Result</h2>
    <dl>
      <dt>{expected_label}</dt><dd>{escape(expected_value)}</dd>
      {coverage}
      <dt>Observed effect</dt><dd>{escape(record["observed_transformation"])}</dd>
      <dt>Actual</dt><dd>{escape(record["actual"])}</dd>
      <dt>Status</dt><dd>{escape(record["status"])}</dd>
    </dl>
  </section>"""

        program_links = case_links(record["program_evidence"])
        supporting_links = case_links(record["evidence"])
        link_blocks = []
        if program_links:
            link_blocks.append(
                f"<p><strong>Program files:</strong> {program_links}</p>"
            )
        if supporting_links:
            link_blocks.append(
                "<details class=\"supporting-files\"><summary>Supporting files</summary>"
                f"<p>{supporting_links}</p></details>"
            )
        case_path = cases_dir / f"{index:04d}.html"
        record["case_view"] = f"cases/{case_path.name}"
        page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{escape(record["case"])}: Test Case</title>
  <link rel="stylesheet" href="../../../docs/artifact.css">
</head>
<body>
<main>
  <p><a href="../test-catalog.html">Test catalog</a></p>
  <h1><code>{escape(record["case"])}</code></h1>
  <p class="lede">{escape(record["suite"])}. {escape(record["family"])}.</p>
{comparison}
  <div class="case-links">
    {chr(10).join(link_blocks)}
  </div>
</main>
</body>
</html>
"""
        case_path.write_text(page, encoding="utf-8")

    actual_view_counts: dict[str, int] = {}
    for record in records:
        view_kind = record["view_kind"]
        actual_view_counts[view_kind] = actual_view_counts.get(view_kind, 0) + 1
    program_view_count = sum(
        count
        for kind, count in actual_view_counts.items()
        if kind in {"accepted-program-pair", "loop-before-after"}
    )
    rejected_view_count = actual_view_counts.get("rejected-candidate-pair", 0)
    result_view_count = (
        actual_view_counts.get("result-summary", 0)
        + actual_view_counts.get("input-no-target", 0)
    )
    require(
        (program_view_count, rejected_view_count, result_view_count)
        == (691, 117, 195),
        "reviewer-view coverage mismatch: expected accepted/rejected/result "
        f"691/117/195, got {program_view_count}/{rejected_view_count}/"
        f"{result_view_count}",
    )
    attached_pair_keys = {
        (record["suite"], record["case"])
        for record in records
        if "program_pair" in record
    }
    require(
        attached_pair_keys == set(program_pairs),
        "program comparison keys not consumed by the catalog: "
        f"missing={sorted(set(program_pairs) - attached_pair_keys)}, "
        f"unexpected={sorted(attached_pair_keys - set(program_pairs))}",
    )
    require(
        len(list(cases_dir.glob("*.html"))) == len(records),
        "not every test configuration has a case page",
    )

    catalog = {
        "counts": {
            "listed_test_configurations": len(records),
            "distinct_suite_cases": len(
                {(record["suite"], record["case"]) for record in records}
            ),
            "recorded_test_case_results": recorded_results,
            "local_artifact_commands": len(local_commands),
            "remote_ci_phases": len(remote_commands),
            "suites": len({item["suite"] for item in records}),
            "categories": len(hierarchy),
            "families": family_count,
            "before_after_programs": program_view_count,
            "input_rejected_candidates": rejected_view_count,
            "result_summaries": result_view_count,
        },
        "hierarchy": hierarchy,
        "suite_notes": SUITE_NOTES,
        "local_artifact_commands": local_commands,
        "remote_ci_phases": remote_commands,
        "cases": records,
    }
    (destination / "test-catalog.json").write_text(
        json.dumps(catalog, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    command_rows = []
    for command in local_commands:
        command_rows.append(
            "<tr>"
            f"<td><code>{escape(command['name'])}</code></td>"
            f"<td><code>{escape(command['command'])}</code></td>"
            f"<td>{command['elapsed_seconds']:.2f} s</td>"
            f"<td class=\"status-pass\">{command['status']}</td>"
            f"<td><a href=\"{escape(command['evidence'], quote=True)}\">output</a></td>"
            "</tr>"
        )
    remote_rows = []
    for command in remote_commands:
        remote_rows.append(
            "<tr>"
            f"<td><code>{escape(command['name'])}</code></td>"
            f"<td>{escape(command['elapsed'])}</td>"
            f"<td class=\"status-pass\">{command['status']}</td>"
            f"<td><a href=\"{escape(command['evidence'], quote=True)}\">CI results</a></td>"
            "</tr>"
        )
    records_by_suite: dict[str, list[dict]] = {}
    for record in records:
        records_by_suite.setdefault(record["suite"], []).append(record)

    def case_row(record: dict, compact: bool = False) -> str:
        search = " ".join(
            str(record[field])
            for field in (
                "category",
                "family",
                "suite",
                "case",
                "expected",
                "observed_transformation",
                "actual",
            )
        ).lower()
        status_class = "status-pass" if record["status"] == "PASS" else "status-note"
        if record["view_kind"] in {"accepted-program-pair", "loop-before-after"}:
            view_label = "before/after programs"
        elif record["view_kind"] == "rejected-candidate-pair":
            view_label = "input/rejected candidate"
        elif record["view_kind"] == "input-no-target":
            view_label = "input/no target"
        else:
            view_label = "result"
        if compact:
            return (
                f'<tr data-search="{escape(search, quote=True)}">'
                f"<td><code>{escape(record['case'])}</code></td>"
                f'<td><a href="{escape(record["case_view"], quote=True)}">'
                f"{view_label}</a></td>"
                "</tr>"
            )
        return (
            f'<tr data-search="{escape(search, quote=True)}">'
            f"<td><code>{escape(record['case'])}</code></td>"
            f"<td>{escape(record['expected'])}</td>"
            f"<td>{escape(record['observed_transformation'])}</td>"
            f"<td>{escape(record['actual'])}</td>"
            f"<td class=\"{status_class}\">{escape(record['status'])}</td>"
            f'<td><a href="{escape(record["case_view"], quote=True)}">'
            f"{view_label}</a></td>"
            "</tr>"
        )

    def html_slug(value: str) -> str:
        return re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")

    category_links = []
    category_sections = []
    for category in hierarchy:
        category_id = html_slug(category["name"])
        category_links.append(
            f'<li><a href="#{category_id}">{escape(category["name"])}</a>'
            f'<span>{category["configurations"]} records</span></li>'
        )
        family_blocks = []
        for family in category["families"]:
            family_id = html_slug(family["name"])
            suite_blocks = []
            for suite in family["suites"]:
                suite_name = suite["name"]
                note = (
                    f'<p class="catalog-suite-note">{escape(suite["note"])}</p>'
                    if "note" in suite
                    else ""
                )
                compact = suite_name == "identity-iss-sensitive-search"
                rows = "\n".join(
                    case_row(record, compact) for record in records_by_suite[suite_name]
                )
                if compact:
                    table_class = "compact-table"
                    table_head = (
                        "<thead><tr><th>Input</th>"
                        "<th>Program or result</th></tr></thead>"
                    )
                else:
                    table_class = ""
                    table_head = (
                        "<thead><tr><th>Case</th><th>Expected result</th>"
                        "<th>Observed effect</th><th>Actual result</th>"
                        "<th>Status</th><th>Program or result</th></tr></thead>"
                    )
                suite_blocks.append(
                    '<details class="catalog-suite" data-catalog-suite>'
                    '<summary><code>'
                    f'{escape(suite_name)}</code>'
                    f'<span>{suite["configurations"]} records</span>'
                    f'</summary>{note}<div class="wide-table"><table class="{table_class}">'
                    f'{table_head}<tbody>'
                    f'{rows}</tbody></table></div></details>'
                )
            family_blocks.append(
                f'<details id="{family_id}" class="catalog-family" data-catalog-family>'
                f'<summary><span>{escape(family["name"])}</span>'
                f'<span>{family["configurations"]} records</span></summary>'
                f'{chr(10).join(suite_blocks)}</details>'
            )
        category_sections.append(
            f'<section id="{category_id}" class="catalog-section" data-catalog-section>'
            f'<h2>{escape(category["name"])} '
            f'<span>{category["configurations"]}</span></h2>'
            f'<p>{escape(category["description"])}</p>'
            f'{chr(10).join(family_blocks)}</section>'
        )
    counts = catalog["counts"]
    page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Test Catalog</title>
  <link rel="stylesheet" href="../../docs/artifact.css">
</head>
<body>
<main>
<h1>Test Catalog</h1>
<p class="lede">
  Use the categories to find tests for a transformation or compiler interface.
  Accepted transformations show the exact input and output. Rejection cases
  show the input and rejected candidate when one was produced. Tests without
  two program objects open a concise result page.
</p>
<p>
  <strong>{counts['listed_test_configurations']} recorded results</strong> for
  <strong>{counts['distinct_suite_cases']} named cases</strong>:
  <strong>{counts['before_after_programs']} accepted-program pages</strong>,
  <strong>{counts['input_rejected_candidates']} rejected-candidate pages</strong>,
  and <strong>{counts['result_summaries']} no-target or non-program results</strong>.
</p>
<ul class="catalog-index">{chr(10).join(category_links)}</ul>
<label for="test-filter"><strong>Filter cases</strong></label>
<input
  id="test-filter"
  type="search"
  placeholder="ISS, diamond, parallel, fusion, case name..."
  aria-controls="catalog-groups"
>
<p id="visible-count" aria-live="polite">
  {counts['listed_test_configurations']} records.
</p>
<div id="catalog-groups">{chr(10).join(category_sections)}</div>
<details class="run-metadata">
<summary>Recorded Commands</summary>
<h2>Local Artifact Commands</h2>
<table>
  <thead>
    <tr><th>Check</th><th>Command</th><th>Time</th><th>Status</th><th>Evidence</th></tr>
  </thead>
  <tbody>{chr(10).join(command_rows)}</tbody>
</table>
<h2>Remote CI Phases</h2>
<table>
  <thead>
    <tr><th>Phase</th><th>Time</th><th>Status</th><th>Evidence</th></tr>
  </thead>
  <tbody>{chr(10).join(remote_rows)}</tbody>
</table>
</details>
</main>
<script>
const input = document.getElementById('test-filter');
const rows = [...document.querySelectorAll('#catalog-groups tbody tr')];
const suites = [...document.querySelectorAll('[data-catalog-suite]')];
const families = [...document.querySelectorAll('[data-catalog-family]')];
const sections = [...document.querySelectorAll('[data-catalog-section]')];
const count = document.getElementById('visible-count');
input.addEventListener('input', () => {{
  const query = input.value.trim().toLowerCase();
  let visible = 0;
  for (const row of rows) {{
    const show = !query || row.dataset.search.includes(query);
    row.hidden = !show;
    if (show) visible += 1;
  }}
  for (const suite of suites) {{
    const show = [...suite.querySelectorAll('tbody tr')].some(row => !row.hidden);
    suite.hidden = !show;
    if (query && show) suite.open = true;
  }}
  for (const family of families) {{
    const show = [...family.querySelectorAll('[data-catalog-suite]')]
      .some(suite => !suite.hidden);
    family.hidden = !show;
    if (query && show) family.open = true;
  }}
  for (const section of sections) {{
    section.hidden = ![...section.querySelectorAll('[data-catalog-family]')]
      .some(family => !family.hidden);
  }}
  count.textContent = query
    ? `Showing ${{visible}} of ${{rows.length}} records.`
    : `${{rows.length}} records.`;
}});
</script>
</body>
</html>
"""
    (destination / "test-catalog.html").write_text(page, encoding="utf-8")
    return catalog


def prepare_evidence(
    release_dir: Path,
    source: Path,
    destination: Path,
    artifact_results: dict,
    proof_report: dict,
    bug_report_draft: str,
) -> dict:
    details = destination / "results"
    shutil.copytree(release_dir / "polcert-artifact-check", details)
    (details / "artifact-results.json").rename(details / "run-results.json")
    (details / "capability-matrix.md").rename(details / "tested-configurations.md")
    (details / "capability-matrix.json").rename(details / "tested-configurations.json")
    (details / "tiling-route-summary.json").rename(details / "tiling-tests.json")
    tested_configurations = details / "tested-configurations.md"
    tested_text = tested_configurations.read_text(encoding="utf-8")
    require(
        tested_text.startswith("# Pluto/PolOpt Capability Matrix"),
        "tested configuration report has an unexpected heading",
    )
    tested_configurations.write_text(
        tested_text.replace(
            "# Pluto/PolOpt Capability Matrix",
            "# Tested Compiler Configurations",
            1,
        )
        .replace(
            "- Pluto-style filtered entry: `./polopt --pluto-compat`",
            "This report covers the `./polopt --pluto-compat` command-line interface.",
            1,
        )
        .replace("## Capability Surface", "## Supported Options", 1),
        encoding="utf-8",
    )
    supported_start = "## Supported Options"
    supported_end = "## Remaining Semantic Gaps"
    tested_text = tested_configurations.read_text(encoding="utf-8")
    before, supported = tested_text.split(supported_start, 1)
    supported, after = supported.split(supported_end, 1)
    supported_lines = []
    for line in supported.splitlines():
        if line.startswith("|"):
            cells = line.split("|")
            require(len(cells) == 7, "unexpected supported-options table row")
            line = "|".join(cells[:-2]) + "|"
        supported_lines.append(line)
    tested_configurations.write_text(
        before
        + supported_start
        + "\n\nThis table records the supported, limited, and rejected command-line options.\n"
        + "Each row identifies the corresponding test or theorem.\n"
        + "\n".join(supported_lines[1:])
        + "\n"
        + supported_end
        + after,
        encoding="utf-8",
    )
    raw_output = details / "raw"
    raw_output.mkdir()
    summaries = {
        "proof-report.json",
        "proof-report.md",
        "run-results.json",
        "tested-configurations.json",
        "tested-configurations.md",
        "tiling-tests.json",
    }
    for path in list(details.iterdir()):
        if path.name not in summaries and path != raw_output:
            shutil.move(path, raw_output / path.name)
    identity = raw_output / "identity-compositions"
    if identity.is_dir():
        identity.rename(raw_output / "identity")
        diamond = raw_output / "identity/identity-diamond-search"
        if diamond.is_dir():
            diamond.rename(raw_output / "identity/diamond")
    unrolljam = raw_output / "unrolljam-effect-corpus"
    if unrolljam.is_dir():
        unrolljam.rename(raw_output / "unrolljam")
    shutil.copy2(PACKAGE_DIR / "PROOF_TEST_RESULTS_README.md", details / "README.md")
    normalize_artifact_results(details / "run-results.json")
    remove_elf_outputs(details)
    copy_typed_pipeline_ci_result(release_dir, raw_output)
    remote_commands = copy_remote_ci_test_results(release_dir, raw_output)
    validate_test_evidence(source, raw_output)
    shutil.copytree(
        release_dir / "polopt-generated-cases",
        destination / "optimized-loop-examples",
    )
    copy_recorded_e2e_loops(
        release_dir,
        destination / "optimized-loop-examples",
    )
    transformation_summary = prepare_transformation_index(
        destination / "optimized-loop-examples"
    )
    executable_summary = prepare_executable_checks(
        release_dir,
        destination / "execution-comparisons",
    )
    rejected = destination / "rejected-optimizer-outputs"
    copy_bug_witnesses(source, rejected, release_dir, bug_report_draft)
    witness_summary = prepare_witness_results(rejected)
    program_pairs = prepare_program_comparisons(details, source)
    test_catalog = prepare_test_catalog(
        details,
        source,
        artifact_results,
        remote_commands,
        transformation_summary,
        executable_summary,
        witness_summary,
        program_pairs,
    )
    shutil.copy2(PACKAGE_DIR / "EVIDENCE_README.md", destination / "README.md")

    checks = artifact_results["results"]
    summary = {
        "proof_and_test_run": {
            "mode": "full",
            "passed": sum(bool(check.get("ok")) for check in checks),
            "total": len(checks),
            "elapsed_seconds": sum(float(check.get("elapsed_seconds", 0)) for check in checks),
        },
        "proof_inventory": {
            "scanned_rocq_files": proof_report["coq_file_count"],
            "admitted": proof_report["admitted_count"],
            "aborted": proof_report["abort_count"],
            "extraction_axioms": proof_report["extraction_axiom_count"],
            "missing_route_theorems": proof_report["missing_route_theorem_count"],
        },
        "optimized_loop_examples": {
            **{
                key: transformation_summary[key]
                for key in ("total", "changed", "unchanged")
            },
            "observed_transformations": transformation_summary["transformation_counts"],
        },
        "execution_comparisons": {
            "baseline_vs_optimized": executable_summary["baseline_vs_optimized"],
            "effect_focused_additional_runs": executable_summary[
                "effect_focused_additional_runs"
            ],
        },
        "rejected_optimizer_outputs": {
            "passed": witness_summary["passed"],
            "total": witness_summary["total"],
        },
        "test_catalog": test_catalog["counts"],
        "toolchain": {"ocaml": "4.13.1", "rocq_coq": "8.13.2"},
    }
    (destination / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return summary


def parse_html(path: Path) -> LinkCollector:
    parser = LinkCollector()
    parser.feed(path.read_text(encoding="utf-8"))
    return parser


def prepare_browser_text_views(package: Path) -> int:
    """Replace linked UTF-8 text files with stable, shallow HTML views.

    The sorted two-pass mapping keeps the ``v/NNNN.html`` paths deterministic
    and short enough for local ``file://`` and WSL UNC browsing.
    """
    package_root = package.resolve()
    href_pattern = re.compile(
        r'(?P<prefix>\bhref\s*=\s*)(?P<quote>["\'])(?P<value>.*?)(?P=quote)',
        re.IGNORECASE,
    )

    def text_target(html_path: Path, raw_href: str) -> Path | None:
        link = urlsplit(raw_href)
        if link.scheme or link.netloc or not link.path:
            return None
        target = (html_path.parent / unquote(link.path)).resolve()
        try:
            target.relative_to(package_root)
        except ValueError:
            return None
        if target.suffix.lower() not in BROWSER_TEXT_SUFFIXES or not target.is_file():
            return None
        try:
            target.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            return None
        return target

    targets: set[Path] = set()
    for html_path in sorted(package.rglob("*.html")):
        original = html_path.read_text(encoding="utf-8")

        for match in href_pattern.finditer(original):
            target = text_target(html_path, unescape(match.group("value")))
            if target is not None:
                targets.add(target)

    views_dir = package / "docs/files"
    views_dir.mkdir()
    views = {
        target: views_dir / f"{index:04d}.html"
        for index, target in enumerate(sorted(targets))
    }

    for html_path in sorted(package.rglob("*.html")):
        original = html_path.read_text(encoding="utf-8")

        def replace_href(match: re.Match[str]) -> str:
            raw_href = unescape(match.group("value"))
            link = urlsplit(raw_href)
            target = text_target(html_path, raw_href)
            if target is None:
                return match.group(0)
            replacement = os.path.relpath(views[target], html_path.parent).replace(
                os.sep, "/"
            )
            if link.query:
                replacement += f"?{link.query}"
            if link.fragment:
                replacement += f"#{link.fragment}"
            quote = match.group("quote")
            return (
                f"{match.group('prefix')}{quote}"
                f"{escape(replacement, quote=True)}{quote}"
            )

        updated = href_pattern.sub(replace_href, original)
        if updated != original:
            html_path.write_text(updated, encoding="utf-8")

    for target, view in views.items():
        css_href = os.path.relpath(package / "docs/artifact.css", view.parent).replace(
            os.sep, "/"
        )
        guide_href = os.path.relpath(package / "docs/index.html", view.parent).replace(
            os.sep, "/"
        )
        label = target.relative_to(package_root).as_posix()
        payload = target.read_text(encoding="utf-8")
        page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{escape(target.name)}</title>
  <link rel="stylesheet" href="{escape(css_href, quote=True)}">
</head>
<body>
<main>
  <p><a href="{escape(guide_href, quote=True)}">Supplement guide</a></p>
  <h1><code>{escape(label)}</code></h1>
  <pre>{escape(payload)}</pre>
</main>
</body>
</html>
"""
        view.write_text(page, encoding="utf-8")
    return len(views)


def check_html_links(root: Path) -> int:
    parsed: dict[Path, LinkCollector] = {}
    html_files = sorted(root.rglob("*.html"))
    for path in html_files:
        parsed[path.resolve()] = parse_html(path)

    errors = []
    for path in html_files:
        for raw_link in parsed[path.resolve()].links:
            link = urlsplit(raw_link)
            if link.scheme or link.netloc or raw_link.startswith(("mailto:", "javascript:")):
                continue
            target_path = path if not link.path else path.parent / unquote(link.path)
            target_path = target_path.resolve()
            if not target_path.exists():
                errors.append(f"{path.relative_to(root)}: missing target {raw_link}")
                continue
            if link.fragment and target_path.suffix.lower() == ".html":
                target_parser = parsed.get(target_path)
                if target_parser is None:
                    target_parser = parse_html(target_path)
                    parsed[target_path] = target_parser
                fragment = unquote(link.fragment)
                if fragment not in target_parser.anchors:
                    errors.append(
                        f"{path.relative_to(root)}: missing fragment {fragment} in "
                        f"{target_path.relative_to(root)}"
                    )
    require(not errors, "HTML link errors:\n" + "\n".join(errors[:40]))
    return len(html_files)


def check_json(root: Path) -> int:
    paths = sorted(root.rglob("*.json"))
    for path in paths:
        load_json(path)
    return len(paths)


def check_denylist(root: Path) -> None:
    errors = []
    needles = [(item, item.lower().encode("utf-8")) for item in DENYLIST]
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root).as_posix()
        lower_name = relative.lower()
        for label, needle in needles:
            if label.lower() in lower_name:
                errors.append(f"path contains {label!r}: {relative}")
        if not path.is_file() or path.is_symlink():
            continue
        data = path.read_bytes().lower()
        for label, needle in needles:
            if needle in data:
                errors.append(f"file contains {label!r}: {relative}")
    require(not errors, "submission-coordinate scan failed:\n" + "\n".join(errors[:60]))


def check_portable_archive_paths(root: Path) -> int:
    invalid = '<>:"/\\|?*'
    reserved = {
        "CON", "PRN", "AUX", "NUL",
        *(f"COM{index}" for index in range(1, 10)),
        *(f"LPT{index}" for index in range(1, 10)),
    }
    longest = 0
    errors = []
    for path in sorted(root.rglob("*")):
        if not (path.is_file() or path.is_symlink()):
            continue
        relative = path.relative_to(root).as_posix()
        archive_path = f"{ARCHIVE_ROOT}/{relative}"
        longest = max(longest, len(archive_path))
        if len(archive_path) > MAX_ARCHIVE_PATH_CHARS:
            errors.append(f"path has {len(archive_path)} characters: {archive_path}")
        for component in PurePosixPath(archive_path).parts:
            stem = component.split(".", 1)[0].upper()
            if any(character in invalid for character in component):
                errors.append(f"Windows-invalid character in path: {archive_path}")
            if component.rstrip(" .") != component or stem in reserved:
                errors.append(f"Windows-invalid path component: {archive_path}")
    require(not errors, "non-portable archive paths:\n" + "\n".join(errors[:40]))
    return longest


def zip_info(path: Path, relative: str) -> zipfile.ZipInfo:
    info = zipfile.ZipInfo(f"{ARCHIVE_ROOT}/{relative}", ZIP_TIMESTAMP)
    info.create_system = 3
    if path.is_symlink():
        info.external_attr = (stat.S_IFLNK | 0o777) << 16
        info.compress_type = zipfile.ZIP_STORED
    else:
        mode = 0o755 if os.access(path, os.X_OK) else 0o644
        info.external_attr = (stat.S_IFREG | mode) << 16
        info.compress_type = zipfile.ZIP_DEFLATED
    return info


def build_zip(root: Path, destination: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(
        destination,
        "w",
        compression=zipfile.ZIP_DEFLATED,
        compresslevel=9,
        allowZip64=True,
    ) as archive:
        for path in sorted(root.rglob("*")):
            if not (path.is_file() or path.is_symlink()):
                continue
            relative = path.relative_to(root).as_posix()
            info = zip_info(path, relative)
            if path.is_symlink():
                archive.writestr(info, os.readlink(path).encode("utf-8"))
            else:
                with path.open("rb") as src, archive.open(info, "w") as dst:
                    shutil.copyfileobj(src, dst, length=1024 * 1024)

    with zipfile.ZipFile(destination) as archive:
        require(archive.testzip() is None, "ZIP integrity test failed")
        names = archive.namelist()
        require(names, "ZIP is empty")
        require(all(name.startswith(f"{ARCHIVE_ROOT}/") for name in names), "ZIP root mismatch")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--release-dir", type=Path, default=DEFAULT_RELEASE_DIR)
    parser.add_argument("--proof-html-dir", type=Path, default=DEFAULT_PROOF_HTML_DIR)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--force", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    release_dir = args.release_dir.resolve()
    proof_html_dir = args.proof_html_dir.resolve()
    output = args.output.resolve()
    if output.exists():
        require(args.force, f"output exists: {output} (use --force to replace it)")
        output.unlink()

    print(f"verifying release inputs: {release_dir}")
    artifact_results, proof_report = verify_release(release_dir)

    with tempfile.TemporaryDirectory(prefix="polcert-cpp27-") as temporary:
        package = Path(temporary) / ARCHIVE_ROOT
        source = package / "source"
        docs = package / "docs"
        evidence = package / "evidence"
        package.mkdir()

        extract_source(release_dir / SOURCE_ARCHIVE, source)
        bug_report_draft = (
            source / "doc/pluto-upstream-miscompilation-report-draft.md"
        ).read_text(encoding="utf-8")
        formal_before = file_hashes(source, ".v")
        prune_source(source)
        sanitize_tree(source)
        patch_anonymous_artifact_runner(source)
        formal_after = file_hashes(source, ".v")
        require(formal_after == formal_before, "formal source changed during packaging")

        pluto_sources = prepare_pluto_sources(package / "third_party/pluto")

        docs.mkdir()
        prepare_docs(proof_html_dir, docs)
        evidence.mkdir()
        summary = prepare_evidence(
            release_dir,
            source,
            evidence,
            artifact_results,
            proof_report,
            bug_report_draft,
        )
        sanitize_tree(evidence)

        shutil.copy2(PACKAGE_DIR / "README.md", package / "README.md")
        shutil.copy2(PACKAGE_DIR / "THIRD_PARTY.md", package / "THIRD_PARTY.md")
        shutil.copy2(source / "LICENSE", package / "LICENSE")
        licenses = package / "licenses"
        licenses.mkdir()
        shutil.copy2(source / "VPL/LICENSE", licenses / "LGPL-3.0.txt")
        shutil.copy2(PACKAGE_DIR / "PLUTO_MIT_LICENSE.txt", licenses / "Pluto-MIT.txt")
        environment = package / "environment"
        shutil.copytree(PACKAGE_DIR / "environment", environment)
        shutil.copy2(PACKAGE_DIR / "DOCKERIGNORE", package / ".dockerignore")
        manifest = {
            "snapshot": "cpp-supplement-r3",
            "formal_source": {
                "files": len(formal_after),
                "packaging_check": "byte-identical-to-validated-snapshot",
            },
            "proof_documentation": {
                "generated_pages": len(list((docs / "proof").glob("*.html"))),
            },
            "pluto_sources": pluto_sources,
            "validation": summary,
        }
        (package / "MANIFEST.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

        browser_text_views = prepare_browser_text_views(package)
        json_count = check_json(package)
        html_count = check_html_links(package)
        check_denylist(package)
        longest_archive_path = check_portable_archive_paths(package)
        build_zip(package, output)

    print(f"wrote: {output}")
    print(f"size: {output.stat().st_size} bytes")
    print(f"SHA-256: {sha256(output)}")
    print(f"validated JSON files: {json_count}")
    print(f"validated HTML files: {html_count}")
    print(f"browser-readable linked text files: {browser_text_views}")
    print(f"longest archive path: {longest_archive_path} characters")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, json.JSONDecodeError, tarfile.TarError) as error:
        print(f"prepare_anonymous.py: {error}", file=sys.stderr)
        raise SystemExit(1)
