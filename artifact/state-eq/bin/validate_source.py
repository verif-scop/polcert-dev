#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path


def git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], text=True, stderr=subprocess.STDOUT
    ).strip()


def parse_env(text: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#") or "=" not in line:
            continue
        key, value = line.split("=", 1)
        values[key] = value
    return values


def docker_arg(text: str, name: str) -> str | None:
    match = re.search(rf"^ARG\s+{re.escape(name)}=(.+)$", text, re.MULTILINE)
    return match.group(1).strip() if match else None


def main() -> int:
    parser = argparse.ArgumentParser(description="Validate a PolCert source repository against the State.eq manifest.")
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--json-out", type=Path)
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    source = args.source.resolve()
    expected = manifest["polcert"]
    pluto = manifest["pluto"]

    checks: list[dict[str, object]] = []

    def check(name: str, actual: str, wanted: str) -> None:
        checks.append({"name": name, "expected": wanted, "actual": actual, "ok": actual == wanted})

    check("tag commit", git(source, "rev-parse", f"{expected['tag']}^{{commit}}"), expected["commit"])
    check("tag object", git(source, "rev-parse", f"{expected['tag']}^{{tag}}"), expected["tag_object"])
    check("commit tree", git(source, "rev-parse", f"{expected['commit']}^{{tree}}"), expected["tree"])

    baseline_text = git(source, "show", f"{expected['commit']}:tools/ci/pluto-baseline.env")
    baseline = parse_env(baseline_text)
    check("Pluto baseline remote", baseline.get("PLUTO_GIT_REMOTE", ""), pluto["repository"])
    check("Pluto baseline commit", baseline.get("PLUTO_GIT_COMMIT", ""), pluto["commit"])
    check("Pluto baseline image", baseline.get("PLUTO_IMAGE", ""), pluto["base_image"])

    dockerfile = git(source, "show", f"{expected['commit']}:Dockerfile")
    check("Dockerfile Pluto remote", docker_arg(dockerfile, "PLUTO_GIT_REMOTE") or "", pluto["repository"])
    check("Dockerfile Pluto commit", docker_arg(dockerfile, "PLUTO_GIT_COMMIT") or "", pluto["commit"])
    check("Dockerfile Pluto image", docker_arg(dockerfile, "PLUTO_IMAGE") or "", pluto["base_image"])

    report = {
        "source": str(source),
        "manifest": str(args.manifest.resolve()),
        "ok": all(item["ok"] for item in checks),
        "checks": checks,
    }
    if args.json_out:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
