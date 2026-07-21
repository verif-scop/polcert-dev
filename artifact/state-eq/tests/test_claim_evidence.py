#!/usr/bin/env python3
from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tests"))
from claim_fixture import materialize_declared_artifacts  # noqa: E402

SCRIPT = ROOT / "bin" / "claim_evidence.py"
SPEC = importlib.util.spec_from_file_location("claim_evidence", SCRIPT)
assert SPEC and SPEC.loader
CLAIM_EVIDENCE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CLAIM_EVIDENCE
SPEC.loader.exec_module(CLAIM_EVIDENCE)


class ClaimEvidenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.results = Path(self.temp.name)
        self.claims_bytes = (ROOT / "claims.json").read_bytes()
        self.claims = json.loads(self.claims_bytes)
        self.outer: list[dict[str, object]] = []
        self.artifact: list[dict[str, object]] = []

        for name in CLAIM_EVIDENCE.expected_outer_routes("full"):
            self.outer.append(self.result("outer", name))
        for name in CLAIM_EVIDENCE.expected_artifact_routes("full"):
            self.artifact.append(self.result("artifact-check", name))

        materialize_declared_artifacts(self.results, self.claims)
        proof_path = self.results / "artifact-check/proof-report.json"
        proof = json.loads(proof_path.read_text())
        proof["theorem_index"] = {
            "driver/VerifiedParallelCompilerConfig.v": [
                "compile_correct",
                "compile_verified_correct",
            ],
            "src/TilingBandDirectRuntime.v": [
                "checked_second_level_direct_band_check_correct",
                "checked_tiling_schedule_sourceb_first_direct_runtime_validate_route_correct"
            ],
            "src/TilingBandScheduleValidator.v": [
                "validate_two_instrs_pluto_band_component_direct_sound",
                "check_pprog_pluto_permutable_tiling_bands_direct_sound_with_env_len",
                "check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound",
                "second_level_local_reversal_bridge_by_layout_wf_with_env_len",
            ],
            "driver/PolOptBandTiling.v": ["Opt_band_with_iss_correct"],
            "driver/ParallelPolOptCorrect.v": [
                "Opt_parallel_current_correct",
                "Opt_parallel_current_many_correct",
            ],
            "src/ParallelCodegen.v": [
                "checked_vector_annotated_codegen_correct_general"
            ],
            "polygen/LoopStride.v": [
                "stride_loop_stmt_semantics",
                "down_stride_loop_stmt_semantics",
            ],
            "polygen/LoopUnroll.v": ["const_unroll_correct", "block_unroll_correct"],
            "src/LoopJamValidator.v": ["checked_loop_jam_pair_at_depth_sound"],
            "src/LoopJamLower.v": ["try_jam_pair_exact_sound"],
        }
        proof_path.write_text(json.dumps(proof))

    def result(self, ledger: str, name: str) -> dict[str, object]:
        directory = "logs" if ledger == "outer" else "artifact-check"
        stdout = self.results / directory / f"{name}.stdout.txt"
        stderr = self.results / directory / f"{name}.stderr.txt"
        stdout.parent.mkdir(parents=True, exist_ok=True)
        stdout.write_text(f"{name}: PASS\n")
        stderr.write_text("")
        return {
            "name": name,
            "ok": True,
            "returncode": 0,
            "stdout_path": f"/artifact-results/{stdout.relative_to(self.results)}",
            "stderr_path": f"/artifact-results/{stderr.relative_to(self.results)}",
        }

    def write_json(self, relative: str, value: object) -> None:
        path = self.results / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))

    def verify(
        self, claims: dict[str, object] | None = None, profile: str = "full"
    ) -> dict[str, object]:
        return CLAIM_EVIDENCE.verify_claim_evidence(
            claims=self.claims if claims is None else claims,
            profile=profile,
            results_root=self.results,
            outer_results=self.outer,
            artifact_results=self.artifact,
            claims_sha256=hashlib.sha256(self.claims_bytes).hexdigest(),
        )

    def test_resolves_every_full_profile_claim_to_files_and_routes(self) -> None:
        report = self.verify()
        self.assertTrue(report["ok"])
        self.assertEqual(report["summary"]["claim_count"], 6)
        self.assertEqual(report["summary"]["verified_claims"], 6)
        self.assertGreater(report["summary"]["resolved_evidence_references"], 6)
        extended = [
            item
            for claim in report["claims"]
            for item in claim["supplemental_evidence"]
            if item["id"] == "extended/iss-live-suite"
        ]
        self.assertEqual(extended[0]["status"], "not-run-in-profile")

    def test_shared_outer_route_catalog_matches_producer_plan(self) -> None:
        suite_script = ROOT / "in-image" / "run_claim_suite.py"
        suite_spec = importlib.util.spec_from_file_location("run_claim_suite", suite_script)
        assert suite_spec and suite_spec.loader
        suite = importlib.util.module_from_spec(suite_spec)
        sys.modules[suite_spec.name] = suite
        suite_spec.loader.exec_module(suite)
        for profile in CLAIM_EVIDENCE.PROFILES:
            produced = tuple(
                name for name, _, _ in suite.checks(profile, self.results / profile)
            )
            self.assertEqual(
                produced, CLAIM_EVIDENCE.expected_outer_routes(profile), profile
            )

    def test_extended_profile_requires_and_resolves_live_iss_route(self) -> None:
        with self.assertRaisesRegex(CLAIM_EVIDENCE.ClaimEvidenceError, "route plan mismatch"):
            self.verify(profile="extended")
        self.outer.append(self.result("outer", "iss-live-suite"))
        report = self.verify(profile="extended")
        extended = [
            item
            for claim in report["claims"]
            for item in claim["supplemental_evidence"]
            if item["id"] == "extended/iss-live-suite"
        ]
        self.assertEqual(extended[0]["status"], "resolved")

    def test_full_profile_cannot_verify_c3_when_required_iss_suite_failed(self) -> None:
        iss = next(item for item in self.artifact if item["name"] == "iss-suite")
        iss["ok"] = False
        iss["returncode"] = 1
        with self.assertRaisesRegex(
            CLAIM_EVIDENCE.ClaimEvidenceError,
            "artifact-check/iss-suite route did not pass",
        ):
            self.verify()

    def test_rejects_claim_without_declared_evidence(self) -> None:
        claims = copy.deepcopy(self.claims)
        claims["claims"][0]["evidence"] = []
        with self.assertRaisesRegex(
            CLAIM_EVIDENCE.ClaimEvidenceError, "must declare evidence"
        ):
            self.verify(claims)

    def test_rejects_unknown_evidence_reference(self) -> None:
        claims = copy.deepcopy(self.claims)
        claims["claims"][0]["evidence"].append("missing-evidence")
        with self.assertRaisesRegex(CLAIM_EVIDENCE.ClaimEvidenceError, "unknown evidence"):
            self.verify(claims)

    def test_rejects_stale_route_even_when_it_is_extended_only(self) -> None:
        claims = copy.deepcopy(self.claims)
        claims["evidence_catalog"]["extended/iss-live-suite"]["route"] = (
            "outer/iss-live-sutie"
        )
        with self.assertRaisesRegex(
            CLAIM_EVIDENCE.ClaimEvidenceError, "stale or unknown route"
        ):
            self.verify(claims)

    def test_rejects_missing_or_failed_produced_route(self) -> None:
        original = copy.deepcopy(self.outer)
        self.outer = [item for item in original if item["name"] != "proof-build"]
        with self.assertRaisesRegex(CLAIM_EVIDENCE.ClaimEvidenceError, "route plan mismatch"):
            self.verify()
        self.outer = original
        proof = next(item for item in self.outer if item["name"] == "proof-build")
        proof["ok"] = False
        proof["returncode"] = 1
        with self.assertRaisesRegex(CLAIM_EVIDENCE.ClaimEvidenceError, "did not pass"):
            self.verify()

    def test_rejects_missing_log_file(self) -> None:
        proof = next(item for item in self.outer if item["name"] == "proof-build")
        (self.results / str(proof["stdout_path"]).removeprefix("/artifact-results/")).unlink()
        with self.assertRaisesRegex(CLAIM_EVIDENCE.ClaimEvidenceError, "is missing"):
            self.verify()

    def test_rejects_failed_structured_assertion(self) -> None:
        proof = json.loads((self.results / "artifact-check/proof-report.json").read_text())
        proof["admitted_count"] = 1
        self.write_json("artifact-check/proof-report.json", proof)
        with self.assertRaisesRegex(CLAIM_EVIDENCE.ClaimEvidenceError, "expected 0, got 1"):
            self.verify()

    def test_structured_equals_is_type_strict(self) -> None:
        proof = json.loads((self.results / "artifact-check/proof-report.json").read_text())
        proof["admitted_count"] = False
        self.write_json("artifact-check/proof-report.json", proof)
        with self.assertRaisesRegex(
            CLAIM_EVIDENCE.ClaimEvidenceError, "expected 0, got False"
        ):
            self.verify()

    def test_structured_minimum_rejects_nonfinite_number(self) -> None:
        proof = json.loads((self.results / "artifact-check/proof-report.json").read_text())
        proof["coq_file_count"] = float("nan")
        self.write_json("artifact-check/proof-report.json", proof)
        with self.assertRaisesRegex(
            CLAIM_EVIDENCE.ClaimEvidenceError, "expected at least 1, got nan"
        ):
            self.verify()

    def test_rejects_nonexistent_theorem_surface(self) -> None:
        claims = copy.deepcopy(self.claims)
        claims["claims"][0]["theorem_surface"][0] = (
            "VerifiedParallelCompilerConfig.not_a_theorem"
        )
        with self.assertRaisesRegex(
            CLAIM_EVIDENCE.ClaimEvidenceError, "theorem does not resolve uniquely"
        ):
            self.verify(claims)

    def test_rejects_zero_case_suite_output_even_when_route_passes(self) -> None:
        (self.results / "artifact-check/second-level-suite.stdout.txt").write_text("")
        with self.assertRaisesRegex(
            CLAIM_EVIDENCE.ClaimEvidenceError, "SECOND-LEVEL-TILE.*got 0"
        ):
            self.verify()

    def test_rejects_unreferenced_catalog_entry(self) -> None:
        claims = copy.deepcopy(self.claims)
        claims["evidence_catalog"]["unused"] = {"route": "outer/proof-build"}
        with self.assertRaisesRegex(
            CLAIM_EVIDENCE.ClaimEvidenceError, "unreferenced entries"
        ):
            self.verify(claims)


if __name__ == "__main__":
    unittest.main()
