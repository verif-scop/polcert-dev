#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path

from claim_evidence import ClaimEvidenceError, expected_outer_routes, verify_claim_evidence


ROOT = Path("/polcert")
ARTIFACT_ROOT = Path("/opt/polcert-artifact")


@dataclass
class Result:
    name: str
    command: list[str]
    returncode: int
    elapsed_seconds: float
    stdout_path: str
    stderr_path: str

    @property
    def ok(self) -> bool:
        return self.returncode == 0


def run(name: str, command: list[str], output: Path, timeout: int) -> Result:
    logs = output / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    stdout_path = logs / f"{name}.stdout.txt"
    stderr_path = logs / f"{name}.stderr.txt"
    start = time.monotonic()
    try:
        completed = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
            timeout=timeout,
        )
        stdout = completed.stdout
        stderr = completed.stderr
        returncode = completed.returncode
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = (exc.stderr or "") + f"\n[claim-suite] timeout after {timeout}s\n"
        returncode = 124
    stdout_path.write_text(stdout)
    stderr_path.write_text(stderr)
    return Result(
        name=name,
        command=command,
        returncode=returncode,
        elapsed_seconds=time.monotonic() - start,
        stdout_path=str(stdout_path),
        stderr_path=str(stderr_path),
    )


def command_version(command: list[str]) -> str:
    try:
        result = subprocess.run(
            command,
            text=True,
            capture_output=True,
            check=False,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return f"unavailable: {exc}"
    text = (result.stdout or result.stderr).strip().splitlines()
    return text[0] if text else f"exit {result.returncode} with no output"


def checks(mode: str, output: Path) -> list[tuple[str, list[str], int]]:
    bootstrap = [
        (
            "dependency-lock",
            [
                "python3",
                "/opt/polcert-artifact/dependency_lock.py",
                "verify-local",
                "--lock",
                "/opt/polcert-artifact/locks/dependency-lock.json",
                "--manifest",
                "/opt/polcert-artifact/manifest.json",
            ],
            300,
        ),
        ("pluto-baseline", ["bash", "tools/ci/check_pluto_baseline.sh"], 300),
        ("clean", ["make", "clean"], 600),
        # A clean git archive has no generated .depend files. This step is
        # required before either the proof build or artifact-check-full.
        ("depend", ["opam", "exec", "--", "make", "depend"], 1200),
        ("proof-build", ["opam", "exec", "--", "make", "proof"], 14400),
        ("check-admitted", ["opam", "exec", "--", "make", "-s", "check-admitted"], 600),
        ("extraction", ["opam", "exec", "--", "make", "extraction"], 3600),
        ("build-polopt", ["opam", "exec", "--", "make", "polopt"], 3600),
        ("build-polcert-ini", ["opam", "exec", "--", "make", "polcert.ini"], 1200),
        ("build-polcert", ["opam", "exec", "--", "make", "polcert"], 3600),
    ]
    if mode == "smoke":
        return bootstrap + [
            (
                "artifact-check",
                [
                    "python3",
                    "tools/artifact/run_artifact_check.py",
                    "--mode",
                    "smoke",
                    "--output-root",
                    str(output / "artifact-check"),
                ],
                14400,
            )
        ]
    full = bootstrap + [
        ("core-regression", ["opam", "exec", "--", "make", "test"], 7200),
        (
            "artifact-check",
            [
                "python3",
                "tools/artifact/run_artifact_check.py",
                "--mode",
                "full",
                "--output-root",
                str(output / "artifact-check"),
            ],
            28800,
        ),
        ("vector-current-suite", ["opam", "exec", "--", "make", "test-vector-current-suite"], 3600),
    ]
    if mode == "extended":
        full.append(
            ("iss-live-suite", ["opam", "exec", "--", "make", "test-iss-pluto-live-suite"], 7200)
        )
    return full


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run the PolCert State.eq claim-oriented reproduction suite."
    )
    parser.add_argument(
        "mode", nargs="?", choices=("smoke", "full", "extended"), default="full"
    )
    parser.add_argument(
        "--output",
        default=os.environ.get("POLCERT_ARTIFACT_OUTPUT", "/artifact-results"),
    )
    parser.add_argument("--fail-fast", action="store_true")
    args = parser.parse_args()

    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        print(
            f"[claim-suite] output directory must be empty: {output}",
            file=sys.stderr,
        )
        return 2
    planned_checks = checks(args.mode, output)
    planned_names = tuple(name for name, _, _ in planned_checks)
    expected_names = expected_outer_routes(args.mode)
    if planned_names != expected_names:
        print(
            "[claim-suite] outer route plan drift: "
            f"expected {list(expected_names)}, got {list(planned_names)}",
            file=sys.stderr,
        )
        return 2
    for name in ("manifest.json", "claims.json", "dependency-lock-audit.json"):
        shutil.copy2(ARTIFACT_ROOT / name, output / name)
    shutil.copy2(
        ARTIFACT_ROOT / "locks" / "dependency-lock.json",
        output / "dependency-lock.json",
    )
    for name in (
        "apt-packages.lock",
        "opam-packages.lock",
        "opam-switch-full.export",
    ):
        shutil.copy2(ARTIFACT_ROOT / "locks" / name, output / name)

    environment = {
        "recorded_at": datetime.now(timezone.utc).isoformat(),
        "artifact_id": os.environ.get("POLCERT_ARTIFACT_ID"),
        "polcert_source_tag": os.environ.get("POLCERT_SOURCE_TAG"),
        "polcert_source_commit": os.environ.get("POLCERT_SOURCE_COMMIT"),
        "polcert_source_tree": os.environ.get("POLCERT_SOURCE_TREE"),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "opam": command_version(["opam", "--version"]),
        "ocaml": command_version(["ocamlc", "-version"]),
        "coq": command_version(["coqc", "--version"]),
        "pluto": command_version(["/pluto/tool/pluto", "--version"]),
        "network_contract": "review command is run with Docker --network none",
    }
    (output / "environment.json").write_text(
        json.dumps(environment, indent=2, sort_keys=True) + "\n"
    )

    results: list[Result] = []
    for name, command, timeout in planned_checks:
        print(f"[claim-suite] {name}: running", flush=True)
        result = run(name, command, output, timeout)
        results.append(result)
        status = "PASS" if result.ok else f"FAIL exit={result.returncode}"
        print(f"[claim-suite] {name}: {status} ({result.elapsed_seconds:.1f}s)", flush=True)
        if args.fail_fast and not result.ok:
            break

    summary = {
        "artifact_id": os.environ.get("POLCERT_ARTIFACT_ID"),
        "mode": args.mode,
        "output": str(output),
        "ok": all(result.ok for result in results),
        "claim_evidence_path": str(output / "claim-evidence.json"),
        "results": [dict(asdict(result), ok=result.ok) for result in results],
    }
    summary_path = output / "claim-results.json"
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    if summary["ok"]:
        try:
            claims_path = output / "claims.json"
            claims_bytes = claims_path.read_bytes()
            claims = json.loads(claims_bytes)
            artifact_results = json.loads(
                (output / "artifact-check" / "artifact-results.json").read_text()
            )
            claim_evidence = verify_claim_evidence(
                claims=claims,
                profile=args.mode,
                results_root=output,
                outer_results=summary["results"],
                artifact_results=artifact_results.get("results"),
                claims_sha256=hashlib.sha256(claims_bytes).hexdigest(),
            )
            (output / "claim-evidence.json").write_text(
                json.dumps(claim_evidence, indent=2, sort_keys=True) + "\n"
            )
            print(
                "[claim-suite] claim evidence: "
                f"{claim_evidence['summary']['verified_claims']}/"
                f"{claim_evidence['summary']['claim_count']} verified",
                flush=True,
            )
        except (ClaimEvidenceError, OSError, json.JSONDecodeError) as exc:
            summary["ok"] = False
            summary["claim_evidence_error"] = str(exc)
            summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
            print(f"[claim-suite] claim evidence: FAIL: {exc}", file=sys.stderr)
    print(f"[claim-suite] summary: {summary_path}", flush=True)
    return 0 if summary["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
