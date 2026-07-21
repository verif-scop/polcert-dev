#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "bin" / "dependency_lock.py"
SPEC = importlib.util.spec_from_file_location("dependency_lock", SCRIPT)
assert SPEC and SPEC.loader
LOCK = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = LOCK
SPEC.loader.exec_module(LOCK)


class DependencyLockTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.lock_dir = self.root / "locks"
        self.manifest = self.root / "manifest.json"
        self.evidence = self.root / "review-evidence.json"
        origin_image = "local:image"
        origin_image_id = "sha256:" + "i" * 64
        self.manifest.write_text(
            json.dumps(
                {
                    "polcert": {"tag": "tag", "commit": "c" * 40, "tree": "t" * 40},
                    "pluto": {"base_image": "registry/base:v1", "base_image_digest": "sha256:" + "b" * 64},
                    "images": {
                        "dependency_lock_origin": {
                            "reference": origin_image,
                            "review_evidence": str(self.evidence),
                        }
                    },
                }
            )
        )
        self.state = LOCK.DependencyState(
            apt_packages=b"a\t1\nb\t2\n",
            apt_filesystem_entries=20,
            apt_filesystem_sha256="1" * 64,
            opam_packages=b"coq\t8.13.2\nzarith\t1.14\n",
            opam_switch_export=b'opam-version: "2.0"\ninstalled: [ "coq.8.13.2" ]\n',
            opam_switch_tree_entries=30,
            opam_switch_tree_sha256="2" * 64,
            opam_binary_sha256="a" * 64,
            os_release=b'ID=ubuntu\nVERSION_ID="20.04"\n',
        )
        evidence = {
            "source": {"tag": "tag", "commit": "c" * 40, "tree": "t" * 40},
            "images": {
                "artifact": {"reference": origin_image, "id": origin_image_id}
            },
        }
        self.evidence.write_text(json.dumps(evidence))
        lock, files = LOCK.create_lock(
            self.state,
            evidence,
            self.evidence,
            LOCK.sha256(self.evidence.read_bytes()),
            origin_image,
            origin_image_id,
            json.loads(self.manifest.read_text()),
        )
        LOCK.atomic_write_lock_dir(self.lock_dir, lock, files)
        self.lock_path = self.lock_dir / "dependency-lock.json"

    def test_matching_state_verifies(self) -> None:
        LOCK.verify_state(self.state, self.lock_path, self.manifest)

    def test_each_dependency_surface_fails_closed(self) -> None:
        mutations = {
            "apt": {"apt_packages": b"a\t9\nb\t2\n"},
            "apt-filesystem": {"apt_filesystem_sha256": "9" * 64},
            "opam-packages": {"opam_packages": b"coq\t8.13.2\n"},
            "opam-export": {"opam_switch_export": b'opam-version: "2.0"\nchanged\n'},
            "opam-tree": {"opam_switch_tree_entries": 31},
            "opam-binary": {"opam_binary_sha256": "f" * 64},
            "os-release": {"os_release": b'ID=ubuntu\nVERSION_ID="22.04"\n'},
        }
        for name, changes in mutations.items():
            with self.subTest(name=name):
                values = self.state.__dict__.copy()
                values.update(changes)
                with self.assertRaises(LOCK.LockError):
                    LOCK.verify_state(LOCK.DependencyState(**values), self.lock_path, self.manifest)

    def test_companion_file_checksum_fails_closed(self) -> None:
        (self.lock_dir / "apt-packages.lock").write_text("tampered\n")
        with self.assertRaisesRegex(LOCK.LockError, "companion checksum mismatch"):
            LOCK.verify_state(self.state, self.lock_path, self.manifest)

    def test_review_evidence_checksum_fails_closed(self) -> None:
        self.evidence.write_text("tampered evidence\n")
        with self.assertRaisesRegex(LOCK.LockError, "review evidence checksum mismatch"):
            LOCK.verify_state(self.state, self.lock_path, self.manifest)

    def test_current_source_may_differ_from_lock_capture_source(self) -> None:
        manifest = json.loads(self.manifest.read_text())
        manifest["polcert"] = {
            "tag": "new-tag",
            "commit": "n" * 40,
            "tree": "u" * 40,
        }
        path = self.root / "new-source.json"
        path.write_text(json.dumps(manifest))
        LOCK.verify_state(self.state, self.lock_path, path)

    def test_manifest_origin_and_base_mismatches_fail_closed(self) -> None:
        for section, field, value in (
            ("images", "dependency_lock_origin", {"reference": "wrong:image", "review_evidence": str(self.evidence)}),
            ("pluto", "base_image_digest", "sha256:" + "x" * 64),
        ):
            with self.subTest(section=section, field=field):
                manifest = json.loads(self.manifest.read_text())
                manifest[section][field] = value
                path = self.root / f"bad-{field}.json"
                path.write_text(json.dumps(manifest))
                with self.assertRaises(LOCK.LockError):
                    LOCK.verify_state(self.state, self.lock_path, path)

    def test_lock_source_must_match_origin_evidence(self) -> None:
        lock = json.loads(self.lock_path.read_text())
        lock["source"]["commit"] = "x" * 40
        self.lock_path.write_text(json.dumps(lock))
        with self.assertRaisesRegex(LOCK.LockError, "origin evidence"):
            LOCK.verify_state(self.state, self.lock_path, self.manifest)

    def test_lock_capture_refuses_existing_output(self) -> None:
        lock = json.loads(self.lock_path.read_text())
        files = {
            name: (self.lock_dir / name).read_bytes()
            for name in ("apt-packages.lock", "opam-packages.lock", "opam-switch-full.export")
        }
        with self.assertRaisesRegex(LOCK.LockError, "already exists"):
            LOCK.atomic_write_lock_dir(self.lock_dir, lock, files)


if __name__ == "__main__":
    unittest.main()
