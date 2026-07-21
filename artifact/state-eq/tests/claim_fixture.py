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
    collection_items: dict[tuple[str, str], list[dict[str, Any]]] = {}
    collection_lengths: dict[tuple[str, str], int] = {}
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
            for assertion in artifact.get("collection_assertions", []):
                key = (relative, assertion["pointer"])
                if "length_equals" in assertion:
                    collection_lengths[key] = assertion["length_equals"]
                    continue
                item: dict[str, Any] = {}
                _set_pointer(item, assertion["item_pointer"], assertion["item_equals"])
                collection_items.setdefault(key, []).extend(
                    [json.loads(json.dumps(item)) for _ in range(assertion["count_equals"])]
                )
            if artifact.get("text_assertions"):
                lines = texts.setdefault(relative, [])
                for assertion in artifact["text_assertions"]:
                    lines.extend(
                        [assertion["contains"]]
                        * assertion.get("minimum_occurrences", 1)
                    )
    for (relative, pointer), items in collection_items.items():
        document = documents.setdefault(relative, {})
        expected_length = collection_lengths.get((relative, pointer), len(items))
        if len(items) > expected_length:
            raise AssertionError(
                f"collection fixture exceeds expected length: {relative} {pointer}"
            )
        items.extend({} for _ in range(expected_length - len(items)))
        _set_pointer(document, pointer, items)
    for (relative, pointer), expected_length in collection_lengths.items():
        if (relative, pointer) not in collection_items:
            document = documents.setdefault(relative, {})
            _set_pointer(document, pointer, [{} for _ in range(expected_length)])
    for relative, document in documents.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(document))
    for relative, lines in texts.items():
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("\n".join(lines) + "\n")
