#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import sys
from pathlib import Path


def append_log(arguments: list[str]) -> None:
    path = os.environ.get("FAKE_DOCKER_LOG")
    if path:
        with Path(path).open("a") as handle:
            handle.write(json.dumps(arguments) + "\n")


def push_seen() -> bool:
    path = os.environ.get("FAKE_DOCKER_LOG")
    if not path or not Path(path).exists():
        return False
    return any(json.loads(line)[0] == "push" for line in Path(path).read_text().splitlines())


def main() -> int:
    arguments = sys.argv[1:]
    append_log(arguments)
    if arguments[:2] == ["image", "inspect"] and len(arguments) == 3:
        inspect_exit = int(os.environ.get("FAKE_DOCKER_INSPECT_EXIT", "0"))
        if inspect_exit:
            print("fixture inspect failure", file=sys.stderr)
            return inspect_exit
        reference = arguments[2]
        digests: list[str] = []
        destination = os.environ.get("FAKE_DOCKER_DEST_REF", "")
        if reference == destination and push_seen():
            explicit_digests = os.environ.get("FAKE_DOCKER_REPO_DIGESTS_JSON")
            if explicit_digests:
                digests = json.loads(explicit_digests)
            else:
                repository = destination.rsplit(":", 1)[0]
                digest = os.environ.get("FAKE_DOCKER_REGISTRY_DIGEST")
                if digest:
                    digests.append(f"{repository}@{digest}")
        print(
            json.dumps(
                [
                    {
                        "Id": os.environ["FAKE_DOCKER_LOCAL_ID"],
                        "RepoDigests": digests,
                    }
                ]
            )
        )
        return 0
    if arguments and arguments[0] == "tag":
        return int(os.environ.get("FAKE_DOCKER_TAG_EXIT", "0"))
    if arguments and arguments[0] == "push":
        exit_code = int(os.environ.get("FAKE_DOCKER_PUSH_EXIT", "0"))
        if exit_code:
            return exit_code
        explicit_digests = os.environ.get("FAKE_DOCKER_REPO_DIGESTS_JSON")
        if explicit_digests:
            for digest in json.loads(explicit_digests):
                value = digest.rsplit("@", 1)[-1]
                print(f"fixture-tag: digest: {value} size: 123")
        else:
            digest = os.environ.get("FAKE_DOCKER_REGISTRY_DIGEST")
            if digest:
                print(f"fixture-tag: digest: {digest} size: 123")
        return 0
    if arguments and arguments[0] == "pull":
        return int(os.environ.get("FAKE_DOCKER_PULL_EXIT", "0"))
    if arguments[:3] == ["buildx", "imagetools", "create"]:
        return int(os.environ.get("FAKE_DOCKER_PROMOTE_EXIT", "0"))
    if arguments[:3] == ["buildx", "imagetools", "inspect"]:
        inspect_exit = int(os.environ.get("FAKE_DOCKER_REMOTE_INSPECT_EXIT", "0"))
        if inspect_exit:
            print("fixture remote inspect failure", file=sys.stderr)
            return inspect_exit
        digest = os.environ.get("FAKE_DOCKER_PROMOTED_DIGEST") or os.environ.get(
            "FAKE_DOCKER_REGISTRY_DIGEST"
        )
        if digest:
            print(f"Name: {arguments[3]}")
            print("MediaType: application/vnd.oci.image.index.v1+json")
            print(f"Digest: {digest}")
        return 0
    print(f"unsupported fake Docker command: {arguments}", file=sys.stderr)
    return 64


if __name__ == "__main__":
    raise SystemExit(main())
