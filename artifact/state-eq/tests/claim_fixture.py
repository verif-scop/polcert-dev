from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def _set_pointer(document: dict[str, Any], pointer: str, value: Any) -> None:
    tokens = pointer.removeprefix("/").split("/")
    current = document
    for token in tokens[:-1]:
        current = current.setdefault(token, {})
    current[tokens[-1]] = value


def materialize_declared_artifacts(root: Path, claims: dict[str, Any]) -> None:
    documents: dict[str, dict[str, Any]] = {}
    texts: dict[str, list[str]] = {}
    for definition in claims["evidence_catalog"].values():
        for artifact in definition.get("artifacts", []):
            relative = artifact["path"]
            if artifact.get("json_assertions"):
                document = documents.setdefault(relative, {})
                for assertion in artifact["json_assertions"]:
                    if "equals" in assertion:
                        value = assertion["equals"]
                    elif "minimum" in assertion:
                        value = assertion["minimum"]
                    elif "nonempty" in assertion:
                        value = "present"
                    else:
                        raise AssertionError(f"unsupported fixture assertion: {assertion}")
                    _set_pointer(document, assertion["pointer"], value)
            if artifact.get("text_assertions"):
                lines = texts.setdefault(relative, [])
                for assertion in artifact["text_assertions"]:
                    lines.extend(
                        [assertion["contains"]]
                        * assertion.get("minimum_occurrences", 1)
                    )
    for relative, document in documents.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(document))
    for relative, lines in texts.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(lines) + "\n")
