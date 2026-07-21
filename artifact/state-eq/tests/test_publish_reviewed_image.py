#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "bin"))
from archive_full_review import (  # noqa: E402
    EXPECTED_ARTIFACT_CHECKS,
    EXPECTED_OUTER_GATES,
    STATIC_RESULT_FILES,
    STRUCTURED_RESULT_FILES,
    repository_static_hashes,
    sha256,
)
from claim_evidence import claim_contract_summary  # noqa: E402


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "bin" / "publish_reviewed_image.py"
FAKE_DOCKER = ROOT / "tests" / "fixtures" / "fake_docker.py"
EVIDENCE = ROOT / "evidence" / "2026-07-18-full-review.json"
REVIEWED_ID = "sha256:573831494258848d553801ee244b9d49ee8f84c2d39716255637b2c8970bfd6f"
REGISTRY_DIGEST = "sha256:" + "a" * 64
DESTINATION = "registry.example.test/polcert/state-eq:state-eq-2026-05-25-v2"
CANDIDATE = "polcert-artifact:state-eq-2026-07-21-v3-candidate"


class PublishReviewedImageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.log = self.directory / "docker.log"
        self.record = self.directory / "publication.json"
        self.environment = os.environ.copy()
        self.environment.update(
            {
                "FAKE_DOCKER_LOG": str(self.log),
                "FAKE_DOCKER_LOCAL_ID": REVIEWED_ID,
                "FAKE_DOCKER_DEST_REF": DESTINATION,
                "FAKE_DOCKER_REGISTRY_DIGEST": REGISTRY_DIGEST,
            }
        )

    def invoke(self, *extra: str, evidence: Path = EVIDENCE) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--registry-ref",
                DESTINATION,
                "--review-evidence",
                str(evidence),
                "--record",
                str(self.record),
                "--docker-bin",
                str(FAKE_DOCKER),
                *extra,
            ],
            text=True,
            capture_output=True,
            check=False,
            env=self.environment,
        )

    def docker_log(self) -> list[list[str]]:
        if not self.log.exists():
            return []
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def schema_v2_evidence(self, image_id: str) -> dict[str, object]:
        evidence = json.loads(EVIDENCE.read_text())
        manifest = json.loads((ROOT / "manifest.json").read_text())
        claims = json.loads((ROOT / "claims.json").read_text())
        evidence["schema_version"] = 2
        evidence["artifact_id"] = manifest["artifact"]["id"]
        evidence["packaging_revision"] = manifest["artifact"]["packaging_revision"]
        evidence["source"] = manifest["polcert"]
        evidence["review"]["recorded_at"] = "2026-07-18T12:00:00+00:00"
        evidence["review"]["elapsed_seconds"] = 13.0
        evidence["images"]["artifact"] = {"reference": CANDIDATE, "id": image_id}
        evidence["environment"]["artifact_id"] = manifest["artifact"]["id"]
        evidence["environment"]["polcert_source_tag"] = manifest["polcert"]["tag"]
        evidence["environment"]["polcert_source_commit"] = manifest["polcert"]["commit"]
        evidence["environment"]["polcert_source_tree"] = manifest["polcert"]["tree"]
        evidence["environment"][
            "network_contract"
        ] = "review command is run with Docker --network none"
        evidence["top_level_results"] = [
            {
                "name": name,
                "ok": True,
                "returncode": 0,
                "elapsed_seconds": 1.0,
            }
            for name in EXPECTED_OUTER_GATES
        ]
        evidence["dependency_lock"] = {
            "gate": "dependency-lock",
            "ok": True,
            "sha256": sha256((ROOT / "locks" / "dependency-lock.json").read_bytes()),
        }
        evidence["review"]["raw_results"] = {
            "file_count": 100,
            "bytes": 1000,
            "tree_sha256": "e" * 64,
            "required_files": {
                **repository_static_hashes(
                    ROOT / "manifest.json", ROOT / "locks" / "dependency-lock.json"
                ),
                **{name: "f" * 64 for name in STRUCTURED_RESULT_FILES},
            },
        }
        evidence["claim_evidence"] = {
            "claims_sha256": sha256((ROOT / "claims.json").read_bytes()),
            "report_sha256": "f" * 64,
            **claim_contract_summary(claims, "full"),
        }
        evidence["claim_evidence"]["verified_claims"] = evidence["claim_evidence"][
            "claim_count"
        ]
        evidence["claim_evidence"]["resolved_evidence_references"] = evidence[
            "claim_evidence"
        ]["required_evidence_references"]
        evidence["claim_evidence"]["resolved_supplemental_evidence_references"] = evidence[
            "claim_evidence"
        ]["supplemental_evidence_references"]
        evidence["claim_evidence"]["resolved_theorem_surface_entries"] = evidence[
            "claim_evidence"
        ]["theorem_surface_entries"]
        evidence["capability_results"]["artifact_subchecks"] = len(
            EXPECTED_ARTIFACT_CHECKS
        )
        evidence["capability_results"]["artifact_subchecks_passed"] = len(
            EXPECTED_ARTIFACT_CHECKS
        )
        evidence["capability_results"]["pluto_compat_checks"] = 138
        evidence["timing"] = {
            "make_jobs": 1,
            "parallel_make_requested": False,
            "full_review_seconds": 13.0,
            "proof_build_seconds": 1.0,
            "artifact_check_seconds": 1.0,
            "strict_loop_suite_seconds": 1.0,
            "advect3d_seconds": 1.0,
        }
        return evidence

    def test_dry_run_only_inspects_local_reviewed_image(self) -> None:
        result = self.invoke("--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        plan = json.loads(result.stdout)
        self.assertTrue(plan["dry_run"])
        self.assertEqual(plan["reviewed_image_id"], REVIEWED_ID)
        self.assertEqual(self.docker_log(), [["image", "inspect", "polcert-artifact:state-eq-2026-05-25-v2"]])
        self.assertFalse(self.record.exists())

    def test_valid_fake_publication_writes_digest_record_atomically(self) -> None:
        result = self.invoke()
        self.assertEqual(result.returncode, 0, result.stderr)
        record = json.loads(self.record.read_text())
        self.assertEqual(record["local_image"]["id"], REVIEWED_ID)
        self.assertEqual(record["registry"]["digest"], REGISTRY_DIGEST)
        self.assertEqual(
            record["registry"]["immutable_reference"],
            f"registry.example.test/polcert/state-eq@{REGISTRY_DIGEST}",
        )
        self.assertFalse(any(self.record.parent.glob(f".{self.record.name}.*.tmp")))

    def test_refuses_local_image_id_mismatch(self) -> None:
        self.environment["FAKE_DOCKER_LOCAL_ID"] = "sha256:" + "b" * 64
        result = self.invoke("--dry-run")
        self.assertEqual(result.returncode, 2)
        self.assertIn("does not match review evidence", result.stderr)

    def test_refuses_candidate_with_old_review_evidence(self) -> None:
        self.environment["FAKE_DOCKER_LOCAL_ID"] = "sha256:" + "c" * 64
        result = self.invoke("--dry-run", "--local-image", CANDIDATE)
        self.assertEqual(result.returncode, 2)
        self.assertIn("does not match review evidence", result.stderr)
        self.assertEqual(self.docker_log(), [["image", "inspect", CANDIDATE]])

    def test_explicit_new_review_evidence_selects_its_own_image_id(self) -> None:
        new_id = "sha256:" + "d" * 64
        evidence = json.loads(EVIDENCE.read_text())
        evidence["images"]["artifact"]["id"] = new_id
        path = self.directory / "new-full-review.json"
        path.write_text(json.dumps(evidence))
        self.environment["FAKE_DOCKER_LOCAL_ID"] = new_id
        result = self.invoke("--dry-run", evidence=path)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["reviewed_image_id"], new_id)

    def test_schema_v2_candidate_compact_only_is_refused(self) -> None:
        new_id = "sha256:" + "d" * 64
        path = self.directory / "lock-v1-full-review.json"
        path.write_text(json.dumps(self.schema_v2_evidence(new_id)))
        self.environment["FAKE_DOCKER_LOCAL_ID"] = new_id
        result = self.invoke("--dry-run", evidence=path)
        self.assertEqual(result.returncode, 2)
        self.assertIn("requires --review-results", result.stderr)
        self.assertEqual(self.docker_log(), [])

    def test_refuses_schema_v1_candidate_even_when_image_id_matches(self) -> None:
        new_id = "sha256:" + "d" * 64
        evidence = json.loads(EVIDENCE.read_text())
        evidence["images"]["artifact"] = {"reference": CANDIDATE, "id": new_id}
        path = self.directory / "candidate-schema-v1.json"
        path.write_text(json.dumps(evidence))
        self.environment["FAKE_DOCKER_LOCAL_ID"] = new_id
        result = self.invoke("--dry-run", evidence=path)
        self.assertEqual(result.returncode, 2)
        self.assertIn("must use schema_version=2", result.stderr)
        self.assertEqual(self.docker_log(), [])

    def test_refuses_incomplete_or_wrong_lock_schema_v2_evidence(self) -> None:
        new_id = "sha256:" + "d" * 64
        mutations = (
            lambda item: item["top_level_results"].pop(0),
            lambda item: item["top_level_results"][0].update(returncode=2, ok=False),
            lambda item: item["dependency_lock"].update(sha256="0" * 64),
            lambda item: item["proof_report"].update(coq_file_count=0),
            lambda item: item["capability_results"]["strict_loop_suite"].update(
                changed=58
            ),
            lambda item: item["capability_results"]["strict_loop_suite"].update(
                detected_tiled=38
            ),
            lambda item: item["timing"].update(proof_build_seconds=2.0),
            lambda item: item["claim_evidence"].update(verified_claims=5),
            lambda item: item["claim_evidence"].update(
                claim_count=1,
                claim_ids=["C1"],
                verified_claims=1,
                required_evidence_references=1,
                resolved_evidence_references=1,
            ),
            lambda item: item["claim_evidence"].update(verified_claims=True),
            lambda item: item["claim_evidence"].update(claims_sha256="0" * 64),
            lambda item: item["review"]["raw_results"]["required_files"].update(
                {"manifest.json": "0" * 64}
            ),
        )
        for index, mutate in enumerate(mutations):
            with self.subTest(index=index):
                evidence = self.schema_v2_evidence(new_id)
                mutate(evidence)
                path = self.directory / f"bad-v2-{index}.json"
                path.write_text(json.dumps(evidence))
                result = self.invoke("--dry-run", evidence=path)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(self.docker_log(), [])

    def test_refuses_unsuccessful_or_nonfull_evidence(self) -> None:
        for field, value, message in (
            ("ok", False, "successful review"),
            ("profile", "smoke", "full profile"),
            ("network", "default", "network=none"),
        ):
            with self.subTest(field=field):
                evidence = json.loads(EVIDENCE.read_text())
                evidence["review"][field] = value
                path = self.directory / f"bad-{field}.json"
                path.write_text(json.dumps(evidence))
                result = self.invoke("--dry-run", evidence=path)
                self.assertEqual(result.returncode, 2)
                self.assertIn(message, result.stderr)

    def test_refuses_source_identity_mismatch(self) -> None:
        replacements = {
            "tag": "state-eq-wrong-tag",
            "commit": "0" * 40,
            "tree": "1" * 40,
        }
        for field, value in replacements.items():
            with self.subTest(field=field):
                evidence = json.loads(EVIDENCE.read_text())
                evidence["source"][field] = value
                path = self.directory / f"wrong-source-{field}.json"
                path.write_text(json.dumps(evidence))
                result = self.invoke("--dry-run", evidence=path)
                self.assertEqual(result.returncode, 2)
                self.assertIn(f"source {field}", result.stderr)

    def test_refuses_nonzero_or_missing_proof_hole_counts(self) -> None:
        fields = (
            "admitted_count",
            "abort_count",
            "extraction_axiom_count",
            "missing_route_theorem_count",
        )
        for index, field in enumerate(fields):
            for value in (1, None):
                with self.subTest(field=field, value=value):
                    evidence = json.loads(EVIDENCE.read_text())
                    if value is None:
                        del evidence["proof_report"][field]
                    else:
                        evidence["proof_report"][field] = value
                    path = self.directory / f"bad-proof-{index}-{value}.json"
                    path.write_text(json.dumps(evidence))
                    result = self.invoke("--dry-run", evidence=path)
                    self.assertEqual(result.returncode, 2)
                    self.assertIn(field, result.stderr)

    def test_refuses_incomplete_capability_evidence(self) -> None:
        mutations = (
            ("artifact-subchecks-total", lambda item: item.update(artifact_subchecks=17)),
            ("artifact-subchecks-passed", lambda item: item.update(artifact_subchecks_passed=17)),
            ("pluto-compat", lambda item: item.update(pluto_compat_checks=113)),
            ("strict-total", lambda item: item["strict_loop_suite"].update(total=61)),
            ("strict-passed", lambda item: item["strict_loop_suite"].update(passed=61)),
            ("iss", lambda item: item.update(iss_suite="FAIL")),
            ("parallel", lambda item: item.update(parallel_current_suite="FAIL")),
            ("vector", lambda item: item.update(vector_current_suite="FAIL")),
            ("second-level", lambda item: item.update(second_level_suite="FAIL")),
            ("diamond", lambda item: item.update(diamond_suite="FAIL")),
        )
        for name, mutate in mutations:
            with self.subTest(name=name):
                evidence = json.loads(EVIDENCE.read_text())
                mutate(evidence["capability_results"])
                path = self.directory / f"bad-capability-{name}.json"
                path.write_text(json.dumps(evidence))
                result = self.invoke("--dry-run", evidence=path)
                self.assertEqual(result.returncode, 2)
                self.assertIn("review evidence must record", result.stderr)

    def test_refuses_missing_digest_after_push_without_record(self) -> None:
        del self.environment["FAKE_DOCKER_REGISTRY_DIGEST"]
        result = self.invoke()
        self.assertEqual(result.returncode, 2)
        self.assertIn("no RepoDigest", result.stderr)
        self.assertFalse(self.record.exists())

    def test_refuses_conflicting_or_malformed_registry_digests(self) -> None:
        repository = DESTINATION.rsplit(":", 1)[0]
        bad_sets = (
            [f"{repository}@sha256:not-a-digest"],
            [f"{repository}@{REGISTRY_DIGEST}", f"{repository}@{'sha256:' + 'b' * 64}"],
        )
        for index, values in enumerate(bad_sets):
            with self.subTest(values=values):
                self.environment["FAKE_DOCKER_REPO_DIGESTS_JSON"] = json.dumps(values)
                self.record = self.directory / f"bad-digest-{index}.json"
                result = self.invoke()
                self.assertEqual(result.returncode, 2)
                self.assertFalse(self.record.exists())

    def test_refuses_tag_push_and_inspect_failures_without_record(self) -> None:
        for variable, message in (
            ("FAKE_DOCKER_TAG_EXIT", "docker tag failed"),
            ("FAKE_DOCKER_PUSH_EXIT", "docker push failed"),
            ("FAKE_DOCKER_INSPECT_EXIT", "cannot inspect image"),
        ):
            with self.subTest(variable=variable):
                self.environment[variable] = "9"
                self.record = self.directory / f"{variable}.json"
                result = self.invoke()
                self.assertEqual(result.returncode, 2)
                self.assertIn(message, result.stderr)
                self.assertFalse(self.record.exists())
                del self.environment[variable]

    def test_refuses_existing_publication_record_before_docker(self) -> None:
        self.record.write_text("{}\n")
        result = self.invoke()
        self.assertEqual(result.returncode, 2)
        self.assertIn("already exists", result.stderr)
        self.assertEqual(self.docker_log(), [])

    def test_refuses_implicit_mutable_or_digest_references(self) -> None:
        bad_references = (
            "",
            "polcert:state-eq-v2",
            "ghcr.io/example/polcert",
            "ghcr.io/example/polcert:latest",
            "ghcr.io/example/polcert:main",
            "ghcr.io/Example/polcert:state-eq-v2",
            "ghcr.io/example/polcert@sha256:" + "c" * 64,
        )
        for index, reference in enumerate(bad_references):
            with self.subTest(reference=reference):
                record = self.directory / f"bad-ref-{index}.json"
                result = subprocess.run(
                    [
                        sys.executable,
                        str(SCRIPT),
                        "--registry-ref",
                        reference,
                        "--review-evidence",
                        str(EVIDENCE),
                        "--record",
                        str(record),
                        "--docker-bin",
                        str(FAKE_DOCKER),
                        "--dry-run",
                    ],
                    text=True,
                    capture_output=True,
                    check=False,
                    env=self.environment,
                )
                self.assertEqual(result.returncode, 2)
                self.assertFalse(record.exists())

    def test_accepts_explicit_registry_host_with_port_in_dry_run(self) -> None:
        result = subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--registry-ref",
                "registry.example.test:5000/team/polcert:state-eq-v2",
                "--review-evidence",
                str(EVIDENCE),
                "--record",
                str(self.record),
                "--docker-bin",
                str(FAKE_DOCKER),
                "--dry-run",
            ],
            text=True,
            capture_output=True,
            check=False,
            env=self.environment,
        )
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
