#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path


def inspect(image: str) -> dict[str, object]:
    raw = subprocess.check_output(["docker", "image", "inspect", image], text=True)
    item = json.loads(raw)[0]
    return {
        "reference": image,
        "id": item["Id"],
        "repo_digests": item.get("RepoDigests", []),
        "created": item.get("Created"),
        "labels": item.get("Config", {}).get("Labels", {}),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--image", required=True)
    parser.add_argument("--source-image", required=True)
    parser.add_argument("--pluto-base-image", required=True)
    parser.add_argument("--dependency-origin-image", required=True)
    parser.add_argument("--source-archive-sha256", required=True)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    report = {
        "recorded_at": datetime.now(timezone.utc).isoformat(),
        "manifest": json.loads(args.manifest.read_text()),
        "source_archive_sha256": args.source_archive_sha256,
        "pluto_base_image": inspect(args.pluto_base_image),
        "dependency_origin_image": inspect(args.dependency_origin_image),
        "source_image": inspect(args.source_image),
        "artifact_image": inspect(args.image),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
