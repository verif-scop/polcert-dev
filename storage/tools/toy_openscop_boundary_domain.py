#!/usr/bin/env python3
"""Generate toy OpenScop evidence for boundary/domain survey entries.

Covered cases:

- source_no_alias_abstraction
- contextual_frame_preservation
- index_set_splitting

These entries are not storage rewrites.  They are validator boundary conditions
or domain/schedule transformations that the storage theorem depends on.  The
.scop files show access/domain shape; the JSON sidecar records the
validator-facing witness.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def relation_1d(kind: str, array: str, index_comment: str = "i", row: str = "0    0   -1    1    0    0") -> str:
    return "\n".join(
        [
            kind,
            "2 6 2 1 0 1",
            "# e/i| Arr [1]| iterator | 1",
            f"   0   -1    0    0    0    0    ## Arr == {array}",
            f"   {row}    ## [1] == {index_comment}",
            "",
        ]
    )


def no_alias_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop source no-alias abstraction skeleton",
            "# A[i] = B[i] + 1 under distinct logical variable footprints.",
            "<arrays>",
            "1 A",
            "2 B",
            "</arrays>",
            "<body>",
            "# Statement S(i)",
            relation_1d("READ", "B"),
            relation_1d("WRITE", "A"),
            "</body>",
            "",
        ]
    )


def no_alias_target() -> str:
    return no_alias_source().replace("source no-alias abstraction", "target no-alias abstraction")


def frame_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop contextual frame source skeleton",
            "# B is updated; protected frame C is not written.",
            "<arrays>",
            "1 A",
            "2 B",
            "3 C",
            "</arrays>",
            "<body>",
            "# Statement S_compute(i)",
            relation_1d("READ", "A"),
            relation_1d("WRITE", "B"),
            "# Frame C has read-only/protected footprint metadata in JSON.",
            "</body>",
            "",
        ]
    )


def frame_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop contextual frame target skeleton",
            "# tmp is private; B is updated; protected frame C is not written.",
            "<arrays>",
            "1 A",
            "2 B",
            "3 C",
            "4 tmp",
            "</arrays>",
            "<body>",
            "# Statement S_private_compute(i)",
            relation_1d("READ", "A"),
            relation_1d("WRITE", "tmp"),
            "# Statement S_commit(i)",
            relation_1d("READ", "tmp"),
            relation_1d("WRITE", "B"),
            "# Frame C has no target WRITE relation.",
            "</body>",
            "",
        ]
    )


def split_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop index-set splitting source skeleton",
            "# One source statement has two guarded expressions.",
            "<arrays>",
            "1 A",
            "2 B",
            "</arrays>",
            "<body>",
            "# Statement S(i), domain 0 <= i < N",
            relation_1d("READ", "A"),
            relation_1d("WRITE", "B"),
            "</body>",
            "",
        ]
    )


def split_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop index-set splitting target skeleton",
            "# Domain is split into [0,K) and [K,N).",
            "<arrays>",
            "1 A",
            "2 B",
            "</arrays>",
            "<body>",
            "# Statement S_then(i), domain 0 <= i < K",
            relation_1d("READ", "A"),
            relation_1d("WRITE", "B"),
            "# Statement S_else(i), domain K <= i < N",
            relation_1d("READ", "A"),
            relation_1d("WRITE", "B"),
            "</body>",
            "",
        ]
    )


def witness() -> dict[str, object]:
    return {
        "schema_version": 1,
        "cases": {
            "source_no_alias_abstraction": {
                "source_scop": "toy_no_alias_source.scop",
                "target_scop": "toy_no_alias_target.scop",
                "public_logical_interface": {"inputs": ["B"], "outputs": ["A"]},
                "statement_roles": [{"statement": "S", "role": "same_accesses_under_no_alias"}],
                "representation_witness": {
                    "kind": "SourceNoAlias",
                    "var_footprints": {
                        "A": "A[0..N)",
                        "B": "B[0..N)",
                    },
                    "distinct_logical_blocks": [["A", "B"]],
                    "in_bounds_accesses": ["A[i]", "B[i] for 0 <= i < N"],
                    "alias_boundary": "validator rejects if A and B may share a physical base",
                },
                "checked_obligations": [
                    "declared source variables have distinct logical footprints",
                    "all accesses are inside declared footprints",
                    "unknown objects are rejected",
                ],
                "negative_cases": [
                    "A and B may alias",
                    "source access object has no declared footprint",
                    "source access falls outside declared footprint",
                ],
                "endpoint": "public_output_view_eq is only meaningful after source variable footprints are well-defined",
            },
            "contextual_frame_preservation": {
                "source_scop": "toy_frame_source.scop",
                "target_scop": "toy_frame_target.scop",
                "public_logical_interface": {"inputs": ["A", "C"], "outputs": ["B", "C"]},
                "private_target_storage": ["tmp"],
                "statement_roles": [
                    {"statement": "S_compute", "role": "source_fragment_write"},
                    {"statement": "S_private_compute", "role": "target_private_compute"},
                    {"statement": "S_commit", "role": "target_allowed_write"},
                ],
                "representation_witness": {
                    "kind": "ContextualFrame",
                    "allowed_writes": ["B"],
                    "protected_frame_vars": ["C"],
                    "frame_snapshots": "C before fragment equals C after fragment",
                    "target_private_storage": "tmp is hidden and not a context-owned frame variable",
                },
                "checked_obligations": [
                    "all target writes are in allowed_writes or private storage",
                    "allowed_writes are disjoint from protected frame variables",
                    "frame snapshots agree before and after the fragment",
                    "private storage does not escape as frame state",
                ],
                "negative_cases": [
                    "target writes protected frame C",
                    "allowed write set overlaps frame",
                    "frame snapshot value changes",
                    "private temp escapes into frame observation",
                ],
                "endpoint": "public_output_view_eq includes preserved frame C and transformed output B",
            },
            "index_set_splitting": {
                "source_scop": "toy_index_split_source.scop",
                "target_scop": "toy_index_split_target.scop",
                "public_logical_interface": {"inputs": ["A"], "outputs": ["B"]},
                "statement_roles": [
                    {"statement": "S", "role": "source_domain"},
                    {"statement": "S_then", "role": "target_subdomain"},
                    {"statement": "S_else", "role": "target_subdomain"},
                ],
                "representation_witness": {
                    "kind": "DomainPartition",
                    "source_domain": "0 <= i < N",
                    "target_subdomains": ["0 <= i < K", "K <= i < N"],
                    "projection": "S_then(i) and S_else(i) project to S(i)",
                    "exact_cover": "[0,K) union [K,N) = [0,N)",
                    "disjointness": "[0,K) and [K,N) are disjoint",
                },
                "checked_obligations": [
                    "target subdomains are disjoint",
                    "target subdomains exactly cover the source domain",
                    "each target substatement projects to exactly one source instance",
                    "storage accesses are unchanged under projection",
                ],
                "negative_cases": [
                    "subdomains overlap",
                    "subdomains miss part of source domain",
                    "target instance projects to no source instance",
                    "target changes storage access while claiming pure domain split",
                ],
                "endpoint": "public_output_view_eq is unchanged because the split preserves instances and storage accesses",
            },
        },
        "caveat": "These are boundary/domain witnesses, not storage rewrites and not Pluto support.",
    }


def write(out_dir: Path, name: str, text: str) -> None:
    path = out_dir / name
    path.write_text(text)
    print(f"wrote {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate toy OpenScop boundary/domain evidence.")
    parser.add_argument("--out-dir", type=Path, default=Path("storage/evidence"))
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    write(args.out_dir, "toy_no_alias_source.scop", no_alias_source())
    write(args.out_dir, "toy_no_alias_target.scop", no_alias_target())
    write(args.out_dir, "toy_frame_source.scop", frame_source())
    write(args.out_dir, "toy_frame_target.scop", frame_target())
    write(args.out_dir, "toy_index_split_source.scop", split_source())
    write(args.out_dir, "toy_index_split_target.scop", split_target())
    witness_path = args.out_dir / "toy_boundary_domain_witness.json"
    witness_path.write_text(json.dumps(witness(), indent=2, sort_keys=True) + "\n")
    print(f"wrote {witness_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
