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
sys.path.insert(0, str(ROOT / "tests"))
from claim_fixture import materialize_declared_artifacts  # noqa: E402

SCRIPT = ROOT / "bin" / "archive_full_review.py"
FAKE_DOCKER = ROOT / "tests" / "fixtures" / "fake_docker.py"
SPEC = importlib.util.spec_from_file_location("archive_full_review", SCRIPT)
assert SPEC and SPEC.loader
ARCHIVE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = ARCHIVE
SPEC.loader.exec_module(ARCHIVE)

CANDIDATE = "polcert-artifact:state-eq-2026-07-21-v3-candidate"
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
            "artifact_image_id": IMAGE_ID,
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
                "artifact_image_id": IMAGE_ID,
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
        materialize_declared_artifacts(
            self.results, json.loads((self.results / "claims.json").read_text())
        )
        self.write_json(
            "artifact-check/proof-report.json",
            {
                "coq_file_count": 185,
                "admitted_count": 0,
                "abort_count": 0,
                "extraction_axiom_count": 0,
                "missing_route_theorem_count": 0,
                "theorem_index": {
                    "driver/VerifiedParallelCompilerConfig.v": [
                        "compile_correct",
                        "compile_verified_correct",
                        "compile_unsupported_no_result",
                    ],
                    "src/Extractor.v": ["extractor_correct"],
                    "src/PrepareCodegen.v": [
                        "prepared_codegen_correct_general",
                    ],
                    "src/TilingBandDirectRuntime.v": [
                        "checked_second_level_direct_band_check_correct",
                        "checked_tiling_sourceb_first_direct_band_check_outer_correct",
                        "checked_tiling_schedule_sourceb_first_direct_runtime_validate_route_correct"
                    ],
                    "src/TilingBandScheduleValidator.v": [
                        "validate_two_instrs_pluto_band_component_direct_sound",
                        "check_pprog_pluto_permutable_tiling_bands_direct_sound_with_env_len",
                        "check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound",
                        "pprog_pluto_permutable_tiling_bands_strong_implies_reordering_safe_wf_with_env_len",
                        "pprog_pluto_componentwise_permutable_bands_implies_reordering_safe_if_local_bridge",
                        "second_level_local_reversal_bridge_by_layout_wf_with_env_len",
                    ],
                    "driver/PolOptBandTiling.v": [
                        "Opt_band_with_iss_correct",
                        "Opt_identity_tiled_band_with_iss_correct",
                        "Opt_diamond_band_with_iss_correct",
                        "try_verified_diamond_after_phase_mid_band_correct",
                        "Opt_diamond_band_correct",
                    ],
                    "driver/ParallelPolOptCorrect.v": [
                        "Opt_parallel_current_correct",
                        "Opt_parallel_current_with_iss_correct",
                        "Opt_parallel_current_many_correct",
                        "Opt_parallel_current_many_with_iss_correct",
                        "Opt_vector_current_correct",
                        "Opt_vector_current_with_iss_correct",
                    ],
                    "src/ParallelCodegen.v": [
                        "checked_annotated_codegen_many_correct_general",
                        "checked_vector_annotated_codegen_correct_general"
                    ],
                    "driver/ExtractedPipelineCorrect.v": [
                        "extracted_parallel_compile_correct"
                    ],
                    "polygen/LoopStride.v": [
                        "stride_loop_stmt_semantics",
                        "down_stride_loop_stmt_semantics",
                    ],
                    "polygen/LoopUnroll.v": [
                        "const_unroll_correct",
                        "block_unroll_correct",
                    ],
                    "src/LoopJamValidator.v": [
                        "checked_loop_jam_pair_at_depth_sound"
                    ],
                    "src/LoopJamLower.v": ["try_jam_pair_exact_sound"],
                },
            },
        )
        (self.results / "artifact-check/strict-loop-suite.stdout.txt").write_text(
            "[3/62] advect3d: ok changed=true time=148.80s\n"
            "total=62\nok=62\nchanged=59\ndetected_tiled=39\n"
        )
        claims_bytes = (self.results / "claims.json").read_bytes()
        claim_evidence = ARCHIVE.verify_claim_evidence(
            claims=json.loads(claims_bytes),
            profile="full",
            results_root=self.results,
            outer_results=outer,
            artifact_results=inner,
            claims_sha256=ARCHIVE.sha256(claims_bytes),
        )
        self.write_json("claim-evidence.json", claim_evidence)

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
                        "reference": f"polcert-artifact-source:{manifest['polcert']['commit'][:12]}",
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

    def refresh_claim_evidence(self) -> None:
        claims_bytes = (self.results / "claims.json").read_bytes()
        outer = json.loads((self.results / "claim-results.json").read_text())["results"]
        inner = json.loads(
            (self.results / "artifact-check/artifact-results.json").read_text()
        )["results"]
        report = ARCHIVE.verify_claim_evidence(
            claims=json.loads(claims_bytes),
            profile="full",
            results_root=self.results,
            outer_results=outer,
            artifact_results=inner,
            claims_sha256=ARCHIVE.sha256(claims_bytes),
        )
        self.write_json("claim-evidence.json", report)

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
        self.assertEqual(first["review"]["executed_image_id"], IMAGE_ID)
        self.assertEqual(first["environment"]["artifact_image_id"], IMAGE_ID)
        self.assertEqual(
            [item["name"] for item in first["top_level_results"]],
            list(ARCHIVE.EXPECTED_OUTER_GATES),
        )
        self.assertEqual(first["dependency_lock"]["sha256"], ARCHIVE.sha256(self.lock.read_bytes()))
        self.assertEqual(first["timing"]["make_jobs"], 1)
        self.assertFalse(first["timing"]["parallel_make_requested"])
        self.assertEqual(first["timing"]["advect3d_seconds"], 148.8)
        self.assertEqual(first["claim_evidence"]["claim_count"], 6)
        self.assertEqual(first["claim_evidence"]["verified_claims"], 6)
        ARCHIVE.validate_compact_v2(
            first,
            json.loads(self.manifest.read_text()),
            ARCHIVE.sha256(self.lock.read_bytes()),
            claims=json.loads((ROOT / "claims.json").read_text()),
        )

    def test_refuses_raw_image_id_mismatch(self) -> None:
        other = "sha256:" + "d" * 64
        for relative, field in (
            ("environment.json", "artifact_image_id"),
            ("claim-results.json", "artifact_image_id"),
        ):
            with self.subTest(relative=relative):
                path = self.results / relative
                original = json.loads(path.read_text())
                mutated = copy.deepcopy(original)
                mutated[field] = other
                self.write_json(relative, mutated)
                with self.assertRaisesRegex(ARCHIVE.EvidenceError, "image ID"):
                    self.build()
                self.write_json(relative, original)

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
        proof["coq_file_count"] = 0
        proof_path.write_text(json.dumps(proof))
        with self.assertRaisesRegex(
            ARCHIVE.EvidenceError, "coq_file_count.*expected at least 1"
        ):
            self.build()

        proof["coq_file_count"] = 185
        proof_path.write_text(json.dumps(proof))
        self.refresh_claim_evidence()
        (self.results / "artifact-check/strict-loop-suite.stdout.txt").write_text(
            "[3/62] advect3d: ok changed=true time=148.80s\n"
            "total=62\nok=62\nchanged=58\ndetected_tiled=39\n"
        )
        with self.assertRaisesRegex(
            ARCHIVE.EvidenceError, "strict-loop-suite.*changed=59.*got 0"
        ):
            self.build()

    def test_refuses_missing_advect3d_timing(self) -> None:
        (self.results / "artifact-check/strict-loop-suite.stdout.txt").write_text(
            "total=62\nok=62\nchanged=59\ndetected_tiled=39\n"
        )
        self.refresh_claim_evidence()
        with self.assertRaisesRegex(ARCHIVE.EvidenceError, "advect3d"):
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

    def test_refuses_claim_evidence_report_mutation(self) -> None:
        report_path = self.results / "claim-evidence.json"
        report = json.loads(report_path.read_text())
        report["claims"][0]["status"] = "not-evaluated"
        report_path.write_text(json.dumps(report))
        with self.assertRaisesRegex(
            ARCHIVE.EvidenceError, "independent claim-to-evidence verification"
        ):
            self.build()

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
