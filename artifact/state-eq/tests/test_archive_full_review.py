#!/usr/bin/env python3
from __future__ import annotations

import copy
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "bin" / "archive_full_review.py"
FAKE_DOCKER = ROOT / "tests" / "fixtures" / "fake_docker.py"
SPEC = importlib.util.spec_from_file_location("archive_full_review", SCRIPT)
assert SPEC and SPEC.loader
ARCHIVE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ARCHIVE
SPEC.loader.exec_module(ARCHIVE)

CANDIDATE = "polcert-artifact:state-eq-lock-v1-candidate"
IMAGE_ID = "sha256:" + "a" * 64


class ArchiveFullReviewTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.results = self.directory / "results"
        self.results.mkdir()
        self.manifest = ROOT / "manifest.json"
        self.lock = ROOT / "locks" / "dependency-lock.json"
        manifest = json.loads(self.manifest.read_text())

        for name in ARCHIVE.STATIC_RESULT_FILES:
            if name == "dependency-lock.json":
                source = self.lock
            elif name in {
                "apt-packages.lock",
                "opam-packages.lock",
                "opam-switch-full.export",
            }:
                source = self.lock.parent / name
            else:
                source = ROOT / name
            shutil.copy2(source, self.results / name)

        environment = {
            "recorded_at": "2026-07-18T12:00:00+00:00",
            "artifact_id": manifest["artifact"]["id"],
            "polcert_source_tag": manifest["polcert"]["tag"],
            "polcert_source_commit": manifest["polcert"]["commit"],
            "polcert_source_tree": manifest["polcert"]["tree"],
            "opam": "2.0.8",
            "ocaml": "4.13.1",
            "coq": "The Coq Proof Assistant, version 8.13.2",
            "python": "3.8.10",
            "pluto": "PLUTO version 6f43860",
            "network_contract": "review command is run with Docker --network none",
        }
        self.write_json("environment.json", environment)

        outer = [self.result(name, "logs") for name in ARCHIVE.EXPECTED_OUTER_GATES]
        self.write_json(
            "claim-results.json",
            {
                "artifact_id": manifest["artifact"]["id"],
                "mode": "full",
                "ok": True,
                "results": outer,
            },
        )

        inner = [
            self.result(name, "artifact-check")
            for name in ARCHIVE.EXPECTED_ARTIFACT_CHECKS
        ]
        self.write_json(
            "artifact-check/artifact-results.json",
            {"mode": "full", "ok": True, "results": inner},
        )
        self.write_json(
            "artifact-check/proof-report.json",
            {
                "coq_file_count": 178,
                "admitted_count": 0,
                "abort_count": 0,
                "extraction_axiom_count": 0,
                "missing_route_theorem_count": 0,
            },
        )
        self.write_json(
            "artifact-check/capability-matrix.json",
            {"summary": {"compatibility_checks": 114}},
        )
        (self.results / "artifact-check/strict-loop-suite.stdout.txt").write_text(
            "total=62\nok=62\nchanged=59\ndetected_tiled=39\n"
        )

        self.build_metadata = self.directory / "build-metadata.json"
        self.build_metadata.write_text(
            json.dumps(
                {
                    "recorded_at": "2026-07-18T11:55:00+00:00",
                    "manifest": manifest,
                    "source_archive_sha256": "b" * 64,
                    "pluto_base_image": {
                        "reference": manifest["pluto"]["base_image"],
                        "id": manifest["pluto"]["base_image_digest"],
                    },
                    "source_image": {
                        "reference": "polcert-artifact-source:13295e741ad6",
                        "id": "sha256:" + "c" * 64,
                    },
                    "artifact_image": {
                        "reference": CANDIDATE,
                        "id": IMAGE_ID,
                        "labels": {
                            "io.polcert.packaging.revision": manifest["artifact"][
                                "packaging_revision"
                            ],
                            "org.opencontainers.image.revision": manifest["polcert"][
                                "commit"
                            ],
                            "io.polcert.source.tree": manifest["polcert"]["tree"],
                            "io.polcert.source.archive.sha256": "b" * 64,
                        },
                    },
                }
            )
        )

    def result(self, name: str, directory: str) -> dict[str, object]:
        base = self.results / directory
        base.mkdir(parents=True, exist_ok=True)
        stdout = base / f"{name}.stdout.txt"
        stderr = base / f"{name}.stderr.txt"
        stdout.write_text(f"{name}: PASS\n")
        stderr.write_text("")
        return {
            "name": name,
            "ok": True,
            "returncode": 0,
            "elapsed_seconds": 1.0,
            "stdout_path": f"/artifact-results/{directory}/{name}.stdout.txt",
            "stderr_path": f"/artifact-results/{directory}/{name}.stderr.txt",
        }

    def write_json(self, relative: str, value: object) -> None:
        path = self.results / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))

    def claim(self) -> dict[str, object]:
        return json.loads((self.results / "claim-results.json").read_text())

    def write_claim(self, claim: dict[str, object]) -> None:
        self.write_json("claim-results.json", claim)

    def build(self) -> dict[str, object]:
        return ARCHIVE.build_evidence(
            self.results,
            self.manifest,
            self.lock,
            self.build_metadata,
            CANDIDATE,
            IMAGE_ID,
        )

    def test_builds_deterministic_schema_v2_evidence(self) -> None:
        first = self.build()
        second = self.build()
        self.assertEqual(first, second)
        self.assertEqual(first["schema_version"], 2)
        self.assertEqual(
            [item["name"] for item in first["top_level_results"]],
            list(ARCHIVE.EXPECTED_OUTER_GATES),
        )
        self.assertEqual(first["dependency_lock"]["sha256"], ARCHIVE.sha256(self.lock.read_bytes()))
        ARCHIVE.validate_compact_v2(
            first,
            json.loads(self.manifest.read_text()),
            ARCHIVE.sha256(self.lock.read_bytes()),
        )

    def test_refuses_missing_or_reordered_dependency_lock_gate(self) -> None:
        original = self.claim()
        mutations = (
            lambda results: results.pop(0),
            lambda results: results.__setitem__(slice(0, 2), reversed(results[:2])),
        )
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                claim = copy.deepcopy(original)
                mutate(claim["results"])
                self.write_claim(claim)
                with self.assertRaisesRegex(ARCHIVE.EvidenceError, "names/order mismatch"):
                    self.build()

    def test_refuses_nonzero_outer_gate(self) -> None:
        claim = self.claim()
        claim["results"][0]["returncode"] = 2
        claim["results"][0]["ok"] = False
        self.write_claim(claim)
        with self.assertRaisesRegex(ARCHIVE.EvidenceError, "returncode=0"):
            self.build()

    def test_refuses_raw_dependency_lock_drift(self) -> None:
        (self.results / "dependency-lock.json").write_text("{}\n")
        with self.assertRaisesRegex(ARCHIVE.EvidenceError, "differs from repository input"):
            self.build()

    def test_refuses_proof_inventory_or_strict_summary_drift(self) -> None:
        proof_path = self.results / "artifact-check/proof-report.json"
        proof = json.loads(proof_path.read_text())
        proof["coq_file_count"] = 177
        proof_path.write_text(json.dumps(proof))
        with self.assertRaisesRegex(ARCHIVE.EvidenceError, "coq_file_count=178"):
            self.build()

        proof["coq_file_count"] = 178
        proof_path.write_text(json.dumps(proof))
        (self.results / "artifact-check/strict-loop-suite.stdout.txt").write_text(
            "total=62\nok=62\nchanged=58\ndetected_tiled=39\n"
        )
        with self.assertRaisesRegex(ARCHIVE.EvidenceError, "strict-loop summary mismatch"):
            self.build()

    def test_validation_detects_raw_bundle_mutation(self) -> None:
        evidence = self.build()
        (self.results / "logs/dependency-lock.stdout.txt").write_text("tampered\n")
        with self.assertRaisesRegex(ARCHIVE.EvidenceError, "differs from the raw result bundle"):
            ARCHIVE.validate_evidence_against_raw(
                evidence,
                self.results,
                self.manifest,
                self.lock,
                self.build_metadata,
                CANDIDATE,
                IMAGE_ID,
            )

    def test_cli_create_validate_and_refuse_overwrite(self) -> None:
        evidence = self.directory / "evidence.json"
        environment = os.environ.copy()
        environment["FAKE_DOCKER_LOCAL_ID"] = IMAGE_ID

        def invoke(command: str) -> subprocess.CompletedProcess[str]:
            return subprocess.run(
                [
                    sys.executable,
                    str(SCRIPT),
                    command,
                    "--results-dir",
                    str(self.results),
                    "--image",
                    CANDIDATE,
                    "--build-metadata",
                    str(self.build_metadata),
                    "--manifest",
                    str(self.manifest),
                    "--lock",
                    str(self.lock),
                    "--evidence",
                    str(evidence),
                    "--docker-bin",
                    str(FAKE_DOCKER),
                ],
                text=True,
                capture_output=True,
                check=False,
                env=environment,
            )

        created = invoke("create")
        self.assertEqual(created.returncode, 0, created.stderr)
        validated = invoke("validate")
        self.assertEqual(validated.returncode, 0, validated.stderr)
        refused = invoke("create")
        self.assertEqual(refused.returncode, 2)
        self.assertIn("already exists", refused.stderr)


if __name__ == "__main__":
    unittest.main()
