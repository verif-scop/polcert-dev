#!/usr/bin/env python3
from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "bin" / "validate_route_contract.py"
SPEC = importlib.util.spec_from_file_location("validate_route_contract", SCRIPT)
assert SPEC and SPEC.loader
VALIDATOR = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = VALIDATOR
SPEC.loader.exec_module(VALIDATOR)


SOURCE = '''
def base_checks(out_dir, timeout, limits):
    return [("base-a", ["a"], 1), ("base-b", ["b"], None)]

def full_checks():
    return [("full-a", ["full"], None)]

def extended_checks(out_dir):
    return [("extended-a", ["extended"], 2)]
'''


class ValidateRouteContractTests(unittest.TestCase):
    def test_extracts_profile_plans_in_execution_order(self) -> None:
        self.assertEqual(
            VALIDATOR.extract_route_plans(SOURCE),
            {
                "smoke": ("base-a", "base-b"),
                "full": ("base-a", "base-b", "full-a"),
                "extended": ("base-a", "base-b", "full-a", "extended-a"),
            },
        )

    def test_rejects_computed_route_name(self) -> None:
        source = SOURCE.replace('("base-a", ["a"], 1)', '(name, ["a"], 1)')
        with self.assertRaisesRegex(ValueError, "literal name"):
            VALIDATOR.extract_route_plans(source)

    def test_rejects_duplicate_route_name(self) -> None:
        source = SOURCE.replace('"base-b"', '"base-a"')
        with self.assertRaisesRegex(ValueError, "duplicate route names"):
            VALIDATOR.extract_route_plans(source)

    def test_indexes_and_resolves_exact_theorem_surface(self) -> None:
        index = VALIDATOR.theorem_index_from_files(
            {
                "src/Foo.v": "Lemma kept : True.\nProof. exact I. Qed.\n",
                "src/Bar.v": "Definition ignored := 0.\nTheorem other : True.\n",
            }
        )
        checks = VALIDATOR.check_theorem_surface(
            {"claims": [{"id": "C1", "theorem_surface": ["Foo.kept"]}]},
            index,
        )
        self.assertEqual(checks[0]["matches"], ["src/Foo.v"])
        self.assertTrue(checks[0]["ok"])

    def test_reports_missing_theorem_surface(self) -> None:
        checks = VALIDATOR.check_theorem_surface(
            {"claims": [{"id": "C1", "theorem_surface": ["Foo.missing"]}]},
            {"src/Foo.v": ("kept",)},
        )
        self.assertFalse(checks[0]["ok"])


if __name__ == "__main__":
    unittest.main()
