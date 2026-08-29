#!/usr/bin/env python3
"""Build and validate the single CPP supplementary-material ZIP."""

from __future__ import annotations

import argparse
import hashlib
from html import escape
from html.parser import HTMLParser
import json
import os
from pathlib import Path, PurePosixPath
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
ARCHIVE_ROOT = "polcert-cpp27-supplement"
ZIP_TIMESTAMP = (2026, 8, 29, 0, 0, 0)

REPLACEMENTS = {
    "9d612d02ac8f27d46c5ec632f912f8a67939e748": "validated-source-snapshot",
    "state-eq-polyhedral-verification-complete-2026-08-29-v10": "validated-source-snapshot",
    "artifact/verified-compilation-v10-driver-finalization": "validated-source-snapshot",
    "9d612d0": "validated-source-snapshot",
    "8c43c210c9c08c5958198f22db4b54000380925e": "fixed-pluto-snapshot",
    "8c43c210": "fixed-pluto-snapshot",
    "8c43c21": "fixed-pluto-snapshot",
    "6f43860b6c4cddeeca09189bf3073f05b78b14a5": "bug-witness-pluto-snapshot",
    "6f43860b": "bug-witness-pluto-snapshot",
    "6f43860": "bug-witness-pluto-snapshot",
    "7d6fae8": "historical diamond snapshot",
    "488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02": "validated Pluto snapshot",
    "488ea2f": "validated Pluto snapshot",
    "56b66690edeed1ef17ddc018bbf67666795a3fd4": "fixed diamond snapshot",
    "56b6669": "fixed diamond snapshot",
    "fix/diamond-reschedule-with-nointratileopt": "fixed diamond snapshot",
    "https://github.com/verif-scop/pluto.git": "bundled Pluto snapshot",
    "https://github.com/verif-scop/pluto": "bundled Pluto snapshot",
    "verif-scop/pluto": "bundled Pluto snapshot",
    "verif-scop/master": "the fixed Pluto snapshot",
    "verif-scop/": "Pluto snapshot/",
    "hughshine/pluto-verif": "pluto-build",
    "hughshine/polcert": "polcert-build",
    "Hughshine/PolCert": "PolCert",
    "/home/hugh": "/build",
}

DENYLIST = (
    "hughshine",
    "/home/hugh",
    "li5274@purdue.edu",
    "github.com/verif-scop",
    "verif-scop/",
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
    "fix/diamond-reschedule-with-nointratileopt",
    "0661fe0a",
    "6404668840fdac7333abf47f8784b5514e7ca94baa7d47d48fc6e6c6b7d9510a",
    "ed4a1cce93b3332bf2b2b80fdb01d7203dddc887f249fff95503d0205c31928c",
    "state-eq-polyhedral-verification",
    "artifact/verified-compilation",
    "33243898549",
)


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
    with tarfile.open(archive_path, "r:") as archive:
        for member in archive.getmembers():
            validate_tar_member(member)
        archive.extractall(destination)


def file_hashes(root: Path, suffix: str) -> dict[str, str]:
    return {
        path.relative_to(root).as_posix(): sha256(path)
        for path in sorted(root.rglob(f"*{suffix}"))
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
        if path.name in {"check_open_proofs.py", "test_check_open_proofs.py"}:
            continue
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path)
        else:
            path.unlink()
    shutil.copy2(
        PACKAGE_DIR / "DIAMOND_WITNESS_README.md",
        source / "tests/pluto-bugs/diamond-nointratile-reschedule/README.md",
    )
    shutil.copy2(
        PACKAGE_DIR / "PLUTO_WITNESSES_README.md",
        source / "tests/pluto-bugs/README.md",
    )


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
        '<a href="../index.html">Artifact handbook</a> &middot; '
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
    shutil.copy2(
        PACKAGE_DIR / "docs/reading-budget.json",
        destination / "reading-budget.json",
    )
    shutil.copy2(PACKAGE_DIR / "docs/proof-index.html", destination / "proof/index.html")
    for path in sorted((destination / "proof").glob("*.html")):
        if path.name != "index.html":
            add_proof_navigation(path)


def normalize_artifact_results(path: Path, formal_manifest_sha256: str) -> None:
    """Turn the raw run record into a self-contained packaged record."""
    record = load_json(path)
    original_provenance = record.get("build_provenance", {})
    environment = record.get("environment", {})
    record["record"] = {
        "schema": "polcert-packaged-validation-record-v1",
        "derived_from_completed_validation_run": True,
    }
    record["build_provenance"] = {
        "formal_source_hash_manifest_sha256": formal_manifest_sha256,
        "validation_run_provenance_checked": bool(original_provenance.get("verified")),
        "formal_source_hash_manifest": "../../FORMAL_SOURCE_SHA256SUMS",
    }
    record["environment"] = {
        key: environment[key]
        for key in ("coq_version", "ocaml_version")
        if key in environment
    }
    record["output_root"] = "artifact-check"
    for result in record.get("results", []):
        for field in ("stdout_path", "stderr_path"):
            if result.get(field):
                result[field] = Path(result[field]).name
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
    require([suite["passed"] for suite in suites] == list(expected_counts), "generated suite coverage mismatch")

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


def prepare_transformation_index(destination: Path) -> dict:
    examples = sorted(path for path in destination.iterdir() if path.is_dir())
    records = []
    rows = []
    for path in examples:
        changed = (path / "diff.patch").is_file() and (path / "diff.patch").stat().st_size > 0
        records.append({"case": path.name, "changed": changed})
        name = escape(path.name)
        rows.append(
            "<tr>"
            f"<td><code>{name}</code></td>"
            f"<td>{'changed' if changed else 'unchanged'}</td>"
            f'<td><a href="{name}/input.pretty.loop">input</a> &middot; '
            f'<a href="{name}/optimized.loop">output</a> &middot; '
            f'<a href="{name}/diff.patch">diff</a> &middot; '
            f'<a href="{name}/status.txt">status</a></td>'
            "</tr>"
        )
    summary = {
        "total": len(records),
        "changed": sum(record["changed"] for record in records),
        "unchanged": sum(not record["changed"] for record in records),
        "cases": records,
    }
    (destination / "index.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    page = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Transformation Examples</title><link rel="stylesheet" href="../../docs/artifact.css"></head>
<body><main><h1>Transformation Examples</h1>
<p>Each row links the strict-suite input, checked output, structural diff, and route status.</p>
<table><thead><tr><th>Case</th><th>Effect</th><th>Files</th></tr></thead><tbody>
""" + "\n".join(rows) + "\n</tbody></table></main></body></html>\n"
    (destination / "index.html").write_text(page, encoding="utf-8")
    return summary


def prepare_witness_results(destination: Path) -> dict:
    log = (destination / "validation.log").read_text(encoding="utf-8")
    expected = (
        ("matmul-parallel-hint", "[pluto-bug] explicit-RAR matmul parallel-hint case reproduced"),
        ("auto-affine-lp-cc-scaling", "[pluto-auto-affine-lp] OK"),
        ("affine-fst-reversed", "[pluto-affine-bug] OK"),
        ("tiling-innerpar-satvec", "[pluto-tiling-bug] OK"),
        ("diamond-nointratile-reschedule", "[pluto-diamond-nointra] OK"),
        ("vanished-outer-parallel", "[pluto-miscompile] OK"),
        ("notile-unrolljam-nonpermutable", "[pluto-unrolljam-bug] OK"),
    )
    results = []
    for name, marker in expected:
        require(marker in log, f"missing witness result marker: {name}")
        results.append(
            {
                "case": name,
                "log_marker": marker,
                "status": "PASS",
                "validation_log": "validation.log",
            }
        )
    summary = {"passed": len(results), "total": len(expected), "results": results}
    (destination / "witness-results.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return summary


def copy_bug_witnesses(source: Path, destination: Path, release_dir: Path) -> None:
    shutil.copytree(source / "tests/pluto-bugs", destination)
    shutil.copy2(PACKAGE_DIR / "PLUTO_WITNESSES_README.md", destination / "README.md")
    matmul = destination / "matmul-parallel-hint"
    matmul.mkdir()
    shutil.copy2(source / "tests/polopt-generated/inputs/matmul.loop", matmul / "matmul.loop")
    shutil.copy2(source / "tools/pluto_bugs/run_matmul_parallel_hint.py", matmul / "run.py")
    shutil.copy2(PACKAGE_DIR / "MATMUL_WITNESS_README.md", matmul / "README.md")
    shutil.copy2(
        PACKAGE_DIR / "DIAMOND_WITNESS_README.md",
        destination / "diamond-nointratile-reschedule/README.md",
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


def prepare_evidence(
    release_dir: Path,
    source: Path,
    destination: Path,
    artifact_results: dict,
    proof_report: dict,
    formal_manifest_sha256: str,
) -> dict:
    shutil.copytree(release_dir / "polcert-artifact-check", destination / "artifact-check")
    normalize_artifact_results(
        destination / "artifact-check/artifact-results.json",
        formal_manifest_sha256,
    )
    remove_elf_outputs(destination / "artifact-check")
    shutil.copytree(
        release_dir / "polopt-generated-cases",
        destination / "transformation-examples",
    )
    transformation_summary = prepare_transformation_index(
        destination / "transformation-examples"
    )
    executable_summary = prepare_executable_checks(
        release_dir,
        destination / "executable-checks",
    )
    copy_bug_witnesses(source, destination / "pluto-bug-witnesses", release_dir)
    witness_summary = prepare_witness_results(destination / "pluto-bug-witnesses")
    shutil.copy2(PACKAGE_DIR / "EVIDENCE_README.md", destination / "README.md")

    checks = artifact_results["results"]
    summary = {
        "artifact_check": {
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
        "transformation_examples": {
            key: transformation_summary[key]
            for key in ("total", "changed", "unchanged")
        },
        "executable_checks": {
            "baseline_vs_optimized": executable_summary["baseline_vs_optimized"],
            "effect_focused_additional_runs": executable_summary[
                "effect_focused_additional_runs"
            ],
        },
        "pluto_bug_witnesses": {
            "passed": witness_summary["passed"],
            "total": witness_summary["total"],
        },
        "toolchain": {"ocaml": "4.13.1", "rocq_coq": "8.13.2"},
    }
    (destination / "validation-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return summary


def parse_html(path: Path) -> LinkCollector:
    parser = LinkCollector()
    parser.feed(path.read_text(encoding="utf-8"))
    return parser


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


def write_checksums(root: Path) -> int:
    entries = []
    for path in sorted(root.rglob("*")):
        if path.is_file() and path.name != "SHA256SUMS":
            entries.append(f"{sha256(path)}  {path.relative_to(root).as_posix()}\n")
    (root / "SHA256SUMS").write_text("".join(entries), encoding="ascii")
    return len(entries)


def verify_checksums(root: Path) -> None:
    for line in (root / "SHA256SUMS").read_text(encoding="ascii").splitlines():
        expected, relative = line.split("  ", 1)
        path = root / relative
        require(path.is_file(), f"checksummed file is missing: {relative}")
        require(sha256(path) == expected, f"checksum mismatch: {relative}")


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
        formal_before = file_hashes(source, ".v")
        prune_source(source)
        sanitize_tree(source)
        formal_after = file_hashes(source, ".v")
        require(formal_after == formal_before, "formal source changed during packaging")
        formal_hash_lines = [
            f"{value}  source/{name}\n" for name, value in sorted(formal_after.items())
        ]
        formal_hash_manifest = package / "FORMAL_SOURCE_SHA256SUMS"
        formal_hash_manifest.write_text("".join(formal_hash_lines), encoding="ascii")
        formal_manifest_sha256 = sha256(formal_hash_manifest)

        docs.mkdir()
        prepare_docs(proof_html_dir, docs)
        evidence.mkdir()
        summary = prepare_evidence(
            release_dir,
            source,
            evidence,
            artifact_results,
            proof_report,
            formal_manifest_sha256,
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
        manifest = {
            "snapshot": "cpp-supplement-r1",
            "formal_source": {
                "files": len(formal_after),
                "file_hash_manifest": "FORMAL_SOURCE_SHA256SUMS",
                "file_hash_manifest_sha256": formal_manifest_sha256,
            },
            "proof_documentation": {
                "generated_pages": len(list((docs / "proof").glob("*.html"))),
            },
            "validation": summary,
        }
        (package / "MANIFEST.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

        json_count = check_json(package)
        html_count = check_html_links(package)
        check_denylist(package)
        checksummed = write_checksums(package)
        verify_checksums(package)
        build_zip(package, output)

    print(f"wrote: {output}")
    print(f"size: {output.stat().st_size} bytes")
    print(f"SHA-256: {sha256(output)}")
    print(f"validated JSON files: {json_count}")
    print(f"validated HTML files: {html_count}")
    print(f"checksummed files: {checksummed}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, json.JSONDecodeError, tarfile.TarError) as error:
        print(f"prepare_anonymous.py: {error}", file=sys.stderr)
        raise SystemExit(1)
