#!/usr/bin/env python3
from __future__ import annotations

import json
import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CANDIDATE = "polcert-artifact:state-eq-2026-08-26-v9-candidate"
CURRENT_EVIDENCE = "evidence/2026-08-26-v9-full-review.json"
REVIEWED = "polcert-artifact:state-eq-2026-05-25-v2"
EVIDENCE = "evidence/2026-07-18-full-review.json"
LOCK_CAPTURE_CANDIDATE = "polcert-artifact:state-eq-lock-v1-candidate"


class CandidateBoundaryTests(unittest.TestCase):
    def test_build_and_run_defaults_use_candidate_reference(self) -> None:
        makefile = (ROOT / "Makefile").read_text()
        self.assertRegex(
            makefile,
            rf"(?m)^POLCERT_ARTIFACT_IMAGE \?= {re.escape(CANDIDATE)}$",
        )
        for name in ("build-image.sh", "run-image.sh"):
            with self.subTest(name=name):
                script = (ROOT / "bin" / name).read_text()
                self.assertIn(
                    f"POLCERT_ARTIFACT_IMAGE:-{CANDIDATE}",
                    script,
                )
                self.assertNotIn(
                    f"POLCERT_ARTIFACT_IMAGE:-{REVIEWED}",
                    script,
                )
        self.assertRegex(
            makefile,
            rf"(?m)^POLCERT_REVIEW_EVIDENCE \?= \$\(CURDIR\)/{re.escape(CURRENT_EVIDENCE)}$",
        )
        self.assertRegex(
            makefile,
            rf"(?m)^POLCERT_REVIEW_EVIDENCE_OUTPUT \?= \$\(CURDIR\)/{re.escape(CURRENT_EVIDENCE)}$",
        )
        publisher = (ROOT / "bin" / "publish_reviewed_image.py").read_text()
        self.assertIn(f'"evidence" / "{Path(CURRENT_EVIDENCE).name}"', publisher)

    def test_reviewed_image_is_only_the_dependency_lock_origin(self) -> None:
        makefile = (ROOT / "Makefile").read_text()
        manifest = json.loads((ROOT / "manifest.json").read_text())
        lock = json.loads((ROOT / "locks" / "dependency-lock.json").read_text())
        evidence = json.loads((ROOT / EVIDENCE).read_text())
        audit = json.loads((ROOT / "dependency-lock-audit.json").read_text())

        self.assertRegex(
            makefile,
            rf"(?m)^POLCERT_DEPENDENCY_LOCK_ORIGIN_IMAGE \?= {re.escape(REVIEWED)}$",
        )
        self.assertIn('--image "$(POLCERT_DEPENDENCY_LOCK_ORIGIN_IMAGE)"', makefile)
        self.assertRegex(
            makefile,
            rf"(?m)^POLCERT_DEPENDENCY_LOCK_ORIGIN_EVIDENCE \?= \$\(CURDIR\)/{re.escape(EVIDENCE)}$",
        )
        self.assertIn(
            '--review-evidence "$(POLCERT_DEPENDENCY_LOCK_ORIGIN_EVIDENCE)"',
            makefile,
        )
        self.assertEqual(manifest["images"]["default_candidate"]["reference"], CANDIDATE)
        origin = manifest["images"]["dependency_lock_origin"]
        self.assertEqual(origin["reference"], REVIEWED)
        self.assertEqual(origin["review_evidence"], EVIDENCE)
        self.assertEqual(lock["origin"]["reviewed_image_reference"], REVIEWED)
        self.assertEqual(lock["origin"]["review_evidence"], EVIDENCE)
        self.assertEqual(evidence["images"]["artifact"]["reference"], REVIEWED)
        self.assertEqual(
            audit["candidate_wrapper"]["default_reference"], LOCK_CAPTURE_CANDIDATE
        )
        self.assertIsNone(audit["candidate_wrapper"]["review_evidence"])
        self.assertNotEqual(LOCK_CAPTURE_CANDIDATE, CANDIDATE)
        self.assertNotEqual(CANDIDATE, REVIEWED)

    def test_v9_source_identity_is_finalized_together(self) -> None:
        manifest = json.loads((ROOT / "manifest.json").read_text())
        self.assertEqual(
            manifest["polcert"]["tag"],
            "state-eq-polyhedral-verification-complete-2026-08-26-v9",
        )
        self.assertEqual(
            {
                field: manifest["polcert"][field]
                for field in ("tag_object", "commit", "tree")
            },
            {
                "tag_object": "66a632f44b231d4e210d115529619d8f761a7840",
                "commit": "604587ecfec9ff3bf6be655dd66e25af6178d604",
                "tree": "3e1daad0f8d05ac0b41c5cb0d50094d45662c121",
            },
        )
        self.assertEqual(
            manifest["polcert"]["archive_sha256"],
            "d53b7232a707d33a0af9404b201b9ab1cf35a49ca0a45d7b02460d53c5d253ca",
        )

    def test_lock_origin_evidence_is_not_candidate_review_evidence(self) -> None:
        dockerfile = (ROOT / "Dockerfile").read_text().replace("\n# ", " ")
        self.assertIn("authenticates the dependency-lock origin only", dockerfile)
        self.assertIn("not review evidence for the candidate wrapper", dockerfile)
        self.assertIn('io.polcert.publication.status="candidate"', dockerfile)
        self.assertNotIn("io.polcert.review.network", dockerfile)

    def test_source_context_includes_tracked_tiling_route_fixtures(self) -> None:
        manifest = json.loads((ROOT / "manifest.json").read_text())
        paths = manifest["reproducibility"]["source_context_required_files"]
        self.assertEqual(len(paths), 4)
        self.assertEqual(len(set(paths)), 4)
        self.assertTrue(all(path.startswith("tools/tiling_routes/fixtures/") for path in paths))
        self.assertTrue(all(path.endswith(".scop") for path in paths))

        builder = (ROOT / "bin" / "build-image.sh").read_text()
        source_dockerfile = (ROOT / "source-image.Dockerfile").read_text()
        self.assertIn("rm -rf /opt/polcert-artifact /artifact-results", source_dockerfile)
        self.assertIn("Dockerfile.dockerignore", builder)
        self.assertIn('source-image.Dockerfile', builder)
        self.assertIn("--target development", builder)
        self.assertIn('POLCERT_DEPENDENCY_IMAGE=$dependency_image', builder)
        self.assertIn('actual_dependency_image_id', builder)
        self.assertIn('--build-arg "POLCERT_GIT_COMMIT=$source_commit"', builder)
        self.assertIn('--label "com.plutoverif.commit=$pluto_commit"', builder)
        self.assertIn('--label "io.polcert.artifact.id=$artifact_id"', builder)
        self.assertIn('--label "io.polcert.publication.status=source-stage"', builder)
        self.assertIn("validate_route_contract.py", builder)
        self.assertIn("required_source_files", builder)
        self.assertIn("test -f /polcert/$path", builder)
        self.assertIn("test ! -e /polcert/ArtifactSource.Dockerfile", builder)
        self.assertIn(
            "test ! -e /polcert/ArtifactSource.Dockerfile.dockerignore", builder
        )
        self.assertIn("reviewer Python compatibility passed", builder)
        self.assertIn("import claim_evidence as c", builder)

        runner = (ROOT / "bin" / "run-image.sh").read_text()
        self.assertIn("docker image inspect", runner)
        self.assertIn('POLCERT_ARTIFACT_IMAGE_ID=$image_id', runner)
        self.assertIn('"$image_id" "$mode"', runner)

    def test_zero_fallback_claim_contract_uses_current_routes(self) -> None:
        claims = json.loads((ROOT / "claims.json").read_text())
        catalog = claims["evidence_catalog"]
        self.assertIn("artifact-check/direct-only-tiling-route-smoke", catalog)
        self.assertNotIn("artifact-check/direct-band-differential", catalog)
        summary = next(
            artifact
            for artifact in catalog[
                "artifact-check/direct-only-tiling-route-smoke"
            ]["artifacts"]
            if artifact["path"] == "artifact-check/tiling-route-summary.json"
        )
        assertions = {
            item["pointer"]: item["equals"] for item in summary["json_assertions"]
        }
        self.assertIs(assertions["/zero_tiling_validation_fallbacks"], True)
        self.assertEqual(assertions["/direct_route_smoke/cases"], 20)
        self.assertEqual(assertions["/non_second_level/permutable_band"], 84)
        self.assertEqual(assertions["/non_second_level/validation_fallback"], 0)
        self.assertEqual(assertions["/second_level_manifest/permutable_band"], 53)
        self.assertEqual(assertions["/second_level_manifest/validation_fallback"], 0)

    def test_unrolljam_claim_uses_generated_summary_schema(self) -> None:
        claims = json.loads((ROOT / "claims.json").read_text())
        artifact = claims["evidence_catalog"][
            "artifact-check/unrolljam-effect-corpus"
        ]["artifacts"][0]
        self.assertEqual(
            [assertion["pointer"] for assertion in artifact["json_assertions"]],
            [
                "/summary/native_codegen_effects",
                "/summary/native_effects_covered",
                "/summary/native_effects_uncovered",
                "/summary/extract_failures",
                "/summary/pluto_failures",
                "/summary/polopt_tiling_route_reports",
            ],
        )


if __name__ == "__main__":
    unittest.main()
