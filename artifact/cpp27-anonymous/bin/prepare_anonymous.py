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
    "/home/hugh",
    "li5274@purdue.edu",
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
        PACKAGE_DIR / "SOURCE_PLUTO_BUGS_README.md",
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
    record["output_root"] = "proof-and-test-results"
    for result in record.get("results", []):
        for field in ("stdout_path", "stderr_path"):
            if result.get(field):
                result[field] = f"raw-output/{Path(result[field]).name}"
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
        input_text = (path / "input.pretty.loop").read_text(encoding="utf-8")
        output_text = (path / "optimized.loop").read_text(encoding="utf-8")
        source_loop_count = sum(line.startswith("for ") for line in input_text.splitlines())
        if not changed:
            transformation = "No loop transformation; output is identical"
        elif path.name == "seq":
            transformation = "Domain guard inserted; loop order is unchanged"
        elif path.name in {"fusion1", "fusion6", "multi-stmt-stencil-seq"}:
            transformation = "Producer-consumer loop fusion and pipelining"
        elif path.name == "tricky2":
            transformation = "Loop fusion with parameter-dependent domain splitting"
        elif path.name == "tricky3":
            transformation = "Inner-loop fusion and splitting with parameter guards"
        elif any(
            marker in output_text
            for marker in ("32 *", "/ 32", "64 *", "/ 64", "313")
        ):
            if source_loop_count > 1:
                transformation = (
                    "Tiling or strip-mining in a program with multiple source loops"
                )
            else:
                transformation = "Tiling or strip-mining of the loop nest"
        else:
            transformation = "Affine loop reordering and bound reconstruction"
        records.append(
            {
                "case": path.name,
                "changed": changed,
                "observed_transformation": transformation,
            }
        )
        name = escape(path.name)
        rows.append(
            "<tr>"
            f"<td><code>{name}</code></td>"
            f"<td>{escape(transformation)}</td>"
            f'<td><a href="{name}/input.pretty.loop">input</a> &middot; '
            f'<a href="{name}/optimized.loop">optimized loop</a> &middot; '
            f'<a href="{name}/diff.patch">diff</a> &middot; '
            f'<a href="{name}/status.txt">compiler result</a></td>'
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
    page = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Optimized Loop Examples</title><link rel="stylesheet" href="../../docs/artifact.css"></head>
<body><main><h1>Optimized Loop Examples</h1>
<p>The classification describes loop-structure changes visible in the generated Loop program. It does not infer a performance improvement.</p>
<table><thead><tr><th>Observed transformation</th><th>Cases</th></tr></thead><tbody>
""" + count_rows + """
</tbody></table>
<table><thead><tr><th>Case</th><th>Observed loop transformation</th><th>Files</th></tr></thead><tbody>
""" + "\n".join(rows) + "\n</tbody></table></main></body></html>\n"
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
    page = """<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Rejected Optimizer Outputs</title><link rel="stylesheet" href="../../docs/artifact.css"></head>
<body><main><h1>Rejected Optimizer Outputs</h1>
<p>Each row states either the violated condition or the missing certificate, followed by the observed PolCert response. The <a href="BUG_REPORT_DRAFT.md">upstream bug-report draft</a> gives reproduction commands, wrong results, root causes, and official-version checks for P1-P4 and C1; F1 belongs only to the development fork.</p>
<table><thead><tr><th>Case</th><th>Why PolCert cannot accept it</th><th>PolCert result</th><th>Pluto source or status</th></tr></thead><tbody>
""" + "\n".join(rows) + "\n</tbody></table></main></body></html>\n"
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
            "Machine-level vector lowering, scalar privatization, storage expansion, state-changing",
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


def validate_test_overview(source: Path, raw_output: Path) -> None:
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
        require(marker in text, f"test overview marker is missing from {filename}")
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


def prepare_evidence(
    release_dir: Path,
    source: Path,
    destination: Path,
    artifact_results: dict,
    proof_report: dict,
    formal_manifest_sha256: str,
    bug_report_draft: str,
) -> dict:
    details = destination / "proof-and-test-results"
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
    raw_output = details / "raw-output"
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
    shutil.copy2(PACKAGE_DIR / "PROOF_TEST_RESULTS_README.md", details / "README.md")
    normalize_artifact_results(
        details / "run-results.json",
        formal_manifest_sha256,
    )
    remove_elf_outputs(details)
    copy_typed_pipeline_ci_result(release_dir, raw_output)
    validate_test_overview(source, raw_output)
    shutil.copy2(PACKAGE_DIR / "TEST_OVERVIEW.md", details / "test-overview.md")
    shutil.copytree(
        release_dir / "polopt-generated-cases",
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
        bug_report_draft = (
            source / "doc/pluto-upstream-miscompilation-report-draft.md"
        ).read_text(encoding="utf-8")
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
