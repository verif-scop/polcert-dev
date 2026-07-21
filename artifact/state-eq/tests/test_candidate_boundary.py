#!/usr/bin/env python3
from __future__ import annotations

import json
import re
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
CANDIDATE = "polcert-artifact:state-eq-2026-07-21-v3-candidate"
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

    def test_lock_origin_evidence_is_not_candidate_review_evidence(self) -> None:
        dockerfile = (ROOT / "Dockerfile").read_text().replace("\n# ", " ")
        self.assertIn("authenticates the dependency-lock origin only", dockerfile)
        self.assertIn("not review evidence for the candidate wrapper", dockerfile)
        self.assertIn('io.polcert.publication.status="candidate"', dockerfile)
        self.assertNotIn("io.polcert.review.network", dockerfile)

    def test_source_context_includes_tracked_differential_fixtures(self) -> None:
        manifest = json.loads((ROOT / "manifest.json").read_text())
        paths = manifest["reproducibility"]["source_context_required_files"]
        self.assertEqual(len(paths), 4)
        self.assertEqual(len(set(paths)), 4)
        self.assertTrue(all(path.startswith("tools/tiling_routes/fixtures/") for path in paths))
        self.assertTrue(all(path.endswith(".scop") for path in paths))

        builder = (ROOT / "bin" / "build-image.sh").read_text()
        self.assertIn("Dockerfile.dockerignore", builder)
        self.assertIn("required_source_files", builder)
        self.assertIn("test -f /polcert/$path", builder)
        self.assertIn("test ! -e /polcert/Dockerfile.dockerignore", builder)


if __name__ == "__main__":
    unittest.main()
