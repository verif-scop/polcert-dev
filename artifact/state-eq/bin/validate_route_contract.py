#!/usr/bin/env python3
from __future__ import annotations

import argparse
import ast
import io
import importlib.util
import json
import re
import subprocess
import sys
import tarfile
from pathlib import Path


ARTIFACT_ROOT = Path(__file__).resolve().parents[1]
CLAIM_EVIDENCE_PATH = ARTIFACT_ROOT / "bin" / "claim_evidence.py"
ROUTE_SOURCE_PATH = "tools/artifact/run_artifact_check.py"
ROUTE_FUNCTIONS = ("base_checks", "full_checks", "extended_checks")
THEOREM_SCAN_DIRS = (
    "src",
    "driver",
    "polygen",
    "syntax",
    "common",
    "cfrontend",
    "cparser",
    "lib",
    "VPL/coq",
)
THEOREM_RE = re.compile(
    r"^\s*(Theorem|Lemma|Corollary|Proposition)\s+([A-Za-z0-9_']+)"
)


def load_claim_evidence():
    spec = importlib.util.spec_from_file_location("claim_evidence", CLAIM_EVIDENCE_PATH)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {CLAIM_EVIDENCE_PATH}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def extract_function_routes(tree: ast.Module, function_name: str) -> tuple[str, ...]:
    functions = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name == function_name
    ]
    if len(functions) != 1:
        raise ValueError(f"expected one {function_name} definition")
    returns = [node for node in functions[0].body if isinstance(node, ast.Return)]
    if len(returns) != 1 or not isinstance(returns[0].value, (ast.List, ast.Tuple)):
        raise ValueError(f"{function_name} must directly return one route list")

    names: list[str] = []
    for position, route in enumerate(returns[0].value.elts):
        if (
            not isinstance(route, (ast.List, ast.Tuple))
            or not route.elts
            or not isinstance(route.elts[0], ast.Constant)
            or not isinstance(route.elts[0].value, str)
        ):
            raise ValueError(
                f"{function_name} route {position} must start with a literal name"
            )
        names.append(route.elts[0].value)
    if len(names) != len(set(names)):
        raise ValueError(f"{function_name} contains duplicate route names")
    return tuple(names)


def extract_route_plans(source: str) -> dict[str, tuple[str, ...]]:
    tree = ast.parse(source, filename=ROUTE_SOURCE_PATH)
    functions = {
        name: extract_function_routes(tree, name) for name in ROUTE_FUNCTIONS
    }
    return {
        "smoke": functions["base_checks"],
        "full": functions["base_checks"] + functions["full_checks"],
        "extended": (
            functions["base_checks"]
            + functions["full_checks"]
            + functions["extended_checks"]
        ),
    }


def theorem_index_from_files(files: dict[str, str]) -> dict[str, tuple[str, ...]]:
    index: dict[str, tuple[str, ...]] = {}
    for path, source in sorted(files.items()):
        names = tuple(
            match.group(2)
            for line in source.splitlines()
            if (match := THEOREM_RE.match(line)) is not None
        )
        if names:
            index[path] = names
    return index


def read_commit_coq_files(source: Path, commit: str) -> dict[str, str]:
    archive = subprocess.check_output(
        ["git", "-C", str(source), "archive", "--format=tar", commit, *THEOREM_SCAN_DIRS]
    )
    files: dict[str, str] = {}
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:") as bundle:
        for member in bundle.getmembers():
            if not member.isfile() or not member.name.endswith(".v"):
                continue
            handle = bundle.extractfile(member)
            if handle is None:
                raise ValueError(f"cannot read archived proof source: {member.name}")
            files[member.name] = handle.read().decode("utf-8", errors="replace")
    return files


def check_theorem_surface(
    claims: dict[str, object], index: dict[str, tuple[str, ...]]
) -> list[dict[str, object]]:
    checks: list[dict[str, object]] = []
    raw_claims = claims.get("claims")
    if not isinstance(raw_claims, list):
        raise ValueError("claims.json claims must be a list")
    for claim in raw_claims:
        if not isinstance(claim, dict) or not isinstance(claim.get("id"), str):
            raise ValueError("each claim must have a string id")
        surface = claim.get("theorem_surface", [])
        if not isinstance(surface, list):
            raise ValueError(f"claim {claim['id']} theorem_surface must be a list")
        for qualified_name in surface:
            if not isinstance(qualified_name, str):
                raise ValueError(
                    f"claim {claim['id']} theorem_surface entries must be strings"
                )
            module, separator, theorem = qualified_name.rpartition(".")
            if not separator or not module or not theorem:
                raise ValueError(
                    f"claim {claim['id']} has invalid theorem name: {qualified_name}"
                )
            matches = [
                path
                for path, names in index.items()
                if Path(path).stem == module and theorem in names
            ]
            checks.append(
                {
                    "claim": claim["id"],
                    "theorem": qualified_name,
                    "matches": matches,
                    "ok": len(matches) == 1,
                }
            )
    if not checks:
        raise ValueError("claims.json declares no theorem surface")
    return checks


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--commit", required=True)
    args = parser.parse_args()

    source = subprocess.check_output(
        ["git", "-C", str(args.source), "show", f"{args.commit}:{ROUTE_SOURCE_PATH}"],
        text=True,
    )
    actual = extract_route_plans(source)
    claim_evidence = load_claim_evidence()
    expected = {
        profile: claim_evidence.expected_artifact_routes(profile)
        for profile in ("smoke", "full", "extended")
    }
    route_checks = []
    for profile in ("smoke", "full", "extended"):
        ok = actual[profile] == expected[profile]
        route_checks.append(
            {
                "profile": profile,
                "ok": ok,
                "source_routes": list(actual[profile]),
                "contract_routes": list(expected[profile]),
            }
        )
    claims = json.loads((ARTIFACT_ROOT / "claims.json").read_text())
    theorem_index = theorem_index_from_files(read_commit_coq_files(args.source, args.commit))
    theorem_checks = check_theorem_surface(claims, theorem_index)
    report = {
        "commit": args.commit,
        "source_path": ROUTE_SOURCE_PATH,
        "route_checks": route_checks,
        "theorem_surface_checks": theorem_checks,
        "theorem_file_count": len(theorem_index),
        "ok": all(check["ok"] for check in route_checks)
        and all(check["ok"] for check in theorem_checks),
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
