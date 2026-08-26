#!/usr/bin/env python3
"""Generate toy OpenScop evidence for private protocol transformations.

Covered cases:

- private_copy_boundary
- private_access_local_instantiation
- scalar_promotion

The generated .scop files show the access shape.  The JSON sidecar carries the
validator-facing protocol evidence: copy boundaries, private cell declarations,
symbolic access instantiation, scalar load/update/store-back, alias exclusion,
and malformed-witness cases.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def relation_1d(kind: str, array: str, index_comment: str, row: str = "0    0   -1    1    0    0") -> str:
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


def relation_scalar(kind: str, array: str) -> str:
    return "\n".join(
        [
            kind,
            "1 4 1 1 0 1",
            "# e/i| Arr | iterator | 1",
            f"   0   -1    0    0    ## Arr == {array}",
            "",
        ]
    )


ROW_FI = "0    0   -1    2    0    1"


def private_copy_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop private copy-boundary source skeleton",
            "# B[i] = A[i] + 1",
            "<arrays>",
            "1 A",
            "2 B",
            "</arrays>",
            "<body>",
            "# Statement S_compute(i)",
            relation_1d("READ", "A", "i"),
            relation_1d("WRITE", "B", "i"),
            "</body>",
            "",
        ]
    )


def private_copy_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop private copy-boundary target skeleton",
            "# local[i] = A[i]; local[i] = local[i] + 1; B[i] = local[i]",
            "<arrays>",
            "1 A",
            "2 B",
            "3 local",
            "</arrays>",
            "<body>",
            "# Statement S_copy_in(i)",
            relation_1d("READ", "A", "i"),
            relation_1d("WRITE", "local", "i"),
            "# Statement S_private_compute(i)",
            relation_1d("READ", "local", "i"),
            relation_1d("WRITE", "local", "i"),
            "# Statement S_copy_out(i)",
            relation_1d("READ", "local", "i"),
            relation_1d("WRITE", "B", "i"),
            "</body>",
            "",
        ]
    )


def private_access_source() -> str:
    return private_copy_source().replace("private copy-boundary", "private access instantiation")


def private_access_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop private access-local-instantiation target skeleton",
            "# local[f(i)] = A[i] + 1; B[i] = local[f(i)]",
            "<arrays>",
            "1 A",
            "2 B",
            "3 local",
            "</arrays>",
            "<body>",
            "# Statement S_private_write(i)",
            relation_1d("READ", "A", "i"),
            relation_1d("WRITE", "local", "f(i)", ROW_FI),
            "# Statement S_private_read(i)",
            relation_1d("READ", "local", "f(i)", ROW_FI),
            relation_1d("WRITE", "B", "i"),
            "</body>",
            "",
        ]
    )


def scalar_promotion_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop scalar promotion source skeleton",
            "# A[i] = A[i] + 1; B[i] = A[i] * 2",
            "<arrays>",
            "1 A",
            "2 B",
            "</arrays>",
            "<body>",
            "# Statement S_update(i)",
            relation_1d("READ", "A", "i"),
            relation_1d("WRITE", "A", "i"),
            "# Statement S_use(i)",
            relation_1d("READ", "A", "i"),
            relation_1d("WRITE", "B", "i"),
            "</body>",
            "",
        ]
    )


def scalar_promotion_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop scalar promotion target skeleton",
            "# s = A[i]; s = s + 1; A[i] = s; B[i] = s * 2",
            "<arrays>",
            "1 A",
            "2 B",
            "3 s",
            "</arrays>",
            "<body>",
            "# Statement S_load(i)",
            relation_1d("READ", "A", "i"),
            relation_scalar("WRITE", "s"),
            "# Statement S_update_scalar(i)",
            relation_scalar("READ", "s"),
            relation_scalar("WRITE", "s"),
            "# Statement S_store_back(i)",
            relation_scalar("READ", "s"),
            relation_1d("WRITE", "A", "i"),
            "# Statement S_use_scalar(i)",
            relation_scalar("READ", "s"),
            relation_1d("WRITE", "B", "i"),
            "</body>",
            "",
        ]
    )


def witness() -> dict[str, object]:
    return {
        "schema_version": 1,
        "cases": {
            "private_copy_boundary": {
                "source_scop": "toy_private_copy_boundary_source.scop",
                "target_scop": "toy_private_copy_boundary_target.scop",
                "public_logical_interface": {"inputs": ["A"], "outputs": ["B"]},
                "private_target_storage": ["local"],
                "storage_declarations": [
                    {"var": "A", "shape": "array[N]", "element_type": "int"},
                    {"var": "B", "shape": "array[N]", "element_type": "int"},
                    {"var": "local", "shape": "array[N]", "element_type": "int", "visibility": "private"},
                ],
                "statement_roles": [
                    {"statement": "S_compute", "role": "source_compute"},
                    {"statement": "S_copy_in", "role": "copy_in"},
                    {"statement": "S_private_compute", "role": "private_compute"},
                    {"statement": "S_copy_out", "role": "copy_out"},
                ],
                "representation_witness": {
                    "kind": "CopyBoundary",
                    "copy_in_pairs": [
                        {
                            "public_cell": "A[i]",
                            "private_cell": "local[i]",
                            "copy_event": "S_copy_in(i)",
                            "phase": "before private use",
                            "value_relation": "local[i] == A[i]",
                        }
                    ],
                    "private_compute": "local[i] carries the value A[i] + 1",
                    "copy_out_pairs": [
                        {
                            "private_cell": "local[i]",
                            "public_cell": "B[i]",
                            "copy_event": "S_copy_out(i)",
                            "phase": "after private update",
                            "value_relation": "B[i] == local[i]",
                        }
                    ],
                    "private_storage_spec": {"target_var": "local", "bounds": "0 <= i < N", "element_type": "same as B"},
                    "compatibility": "A[i], local[i], and B[i] have compatible element representation",
                },
                "boundary_protocol": {
                    "copy_in_coverage": "required public live-ins are exactly covered by copy_in_pairs",
                    "private_use_order": "S_copy_in(i) dominates S_private_compute(i)",
                    "copy_out_coverage": "required public live-outs are exactly covered by copy_out_pairs",
                    "commit_uniqueness": "S_copy_out(i) commits B[i] exactly once",
                },
                "checked_obligations": [
                    "copy-in initializes every private read that depends on public input",
                    "copy-out covers every public live-out exactly once",
                    "private trace accesses only declared private cells",
                    "private cells are in bounds and hidden from final public view",
                    "boundary values and storage specs are compatible",
                ],
                "negative_cases": [
                    "missing copy-in before private read",
                    "missing live-out copy-out",
                    "duplicate copy-out for one public cell",
                    "copy-in aliases two public values into one private cell",
                    "private trace uses undeclared cell",
                    "private cell out of bounds",
                    "private/public type or extent mismatch",
                    "copy-out value mismatch",
                    "copy-out uses stale private value",
                ],
                "endpoint": "public_output_view_eq observes B; local is hidden after copy-out",
            },
            "private_access_local_instantiation": {
                "source_scop": "toy_private_access_source.scop",
                "target_scop": "toy_private_access_target.scop",
                "public_logical_interface": {"inputs": ["A"], "outputs": ["B"]},
                "private_target_storage": ["local"],
                "storage_declarations": [
                    {"var": "A", "shape": "array[N]", "element_type": "int"},
                    {"var": "B", "shape": "array[N]", "element_type": "int"},
                    {"var": "local", "shape": "array[M]", "element_type": "int", "visibility": "private"},
                ],
                "statement_roles": [
                    {"statement": "S_private_write", "role": "private_access_write"},
                    {"statement": "S_private_read", "role": "private_access_read"},
                ],
                "representation_witness": {
                    "kind": "PrivateAccessInstantiation",
                    "symbolic_private_accesses": [
                        {
                            "access_id": "local_tmp(i)",
                            "symbolic_cell": "local[f(i)]",
                            "instantiation": "f(i) = 2*i + 1",
                            "domain": "0 <= i < N and 0 <= 2*i+1 < M",
                            "target_cell": "local[2*i+1]",
                            "roles": ["write", "read"],
                        }
                    ],
                    "private_cell_declarations": [
                        {"var": "local", "bounds": "0 <= k < M", "element_type": "int"}
                    ],
                    "use_def": "S_private_read(i) reads the cell written by S_private_write(i)",
                    "private_storage_spec": {"target_var": "local", "bounds": "0 <= 2*i+1 < M", "element_type": "same as B"},
                    "hidden_cells": "all local[f(i)] cells are excluded from public_output_view_eq",
                },
                "alias_clobber_exclusion": "instantiated local cells cannot alias public A or B cells",
                "checked_obligations": [
                    "symbolic private access trace is use-def well formed",
                    "finite domain points instantiate to declared private cells",
                    "instantiation map is deterministic and supported by the validator",
                    "instantiated private cells are in bounds",
                    "instantiated private cells are hidden from public view",
                    "if two private accesses instantiate to the same cell, their live intervals are compatible",
                ],
                "negative_cases": [
                    "private read before matching private write",
                    "instantiated private cell undeclared",
                    "instantiated private cell out of bounds",
                    "two live symbolic accesses alias when freshness is required",
                    "partial-tile domain guard missing",
                    "symbolic map is unsupported or non-affine for the validator fragment",
                ],
                "endpoint": "public_output_view_eq observes B; local[f(i)] is internal evidence only",
            },
            "scalar_promotion": {
                "source_scop": "toy_scalar_promotion_source.scop",
                "target_scop": "toy_scalar_promotion_target.scop",
                "public_logical_interface": {"inputs": ["A"], "outputs": ["A", "B"]},
                "private_target_storage": ["s"],
                "storage_declarations": [
                    {"var": "A", "shape": "array[N]", "element_type": "int"},
                    {"var": "B", "shape": "array[N]", "element_type": "int"},
                    {"var": "s", "shape": "scalar", "element_type": "int", "visibility": "private"},
                ],
                "statement_roles": [
                    {"statement": "S_update", "role": "source_update"},
                    {"statement": "S_use", "role": "source_use"},
                    {"statement": "S_load", "role": "load"},
                    {"statement": "S_update_scalar", "role": "scalar_update"},
                    {"statement": "S_store_back", "role": "store_back"},
                    {"statement": "S_use_scalar", "role": "scalar_use"},
                ],
                "representation_witness": {
                    "kind": "ScalarPromotion",
                    "promotion_protocols": [
                        {
                            "logical_cell": "A[i]",
                            "private_scalar": "s",
                            "load_event": "S_load(i)",
                            "update_events": ["S_update_scalar(i)"],
                            "store_back_event": "S_store_back(i)",
                            "valid_interval": ["after S_load(i)", "before S_store_back(i)"],
                            "public_live_out": True,
                        }
                    ],
                    "public_uses": ["S_use_scalar(i) uses s for B[i] after S_update_scalar(i)"],
                    "alias_clobber_exclusion": "no write to A[i] or alias of A[i] occurs between load and store-back except the checked store-back",
                    "storage_compatibility": "s has same element type/representation as A[i]",
                },
                "alias_clobber_exclusion": [
                    {
                        "interval": "between S_load(i) and S_store_back(i)",
                        "forbidden_writes": ["A[i]", "may_alias(A[i])"],
                        "calls": "no unknown side effect on A[i]",
                    }
                ],
                "boundary_protocol": {
                    "load": "S_load(i) initializes s from A[i]",
                    "updates": "S_update_scalar(i) follows the source update expression",
                    "store_back": "S_store_back(i) commits s to A[i] before final public observation",
                    "per_iteration": "s is a per-iteration private scalar, not loop-carried state",
                },
                "checked_obligations": [
                    "load initializes the scalar before scalar reads",
                    "scalar update simulates the source public-cell update",
                    "store-back commits the updated scalar before public observation of A[i]",
                    "store-back targets the same public cell that was promoted",
                    "public uses after promotion read the current scalar value",
                    "alias/clobber exclusion protects the cached value",
                    "scalar storage is hidden from final public view",
                ],
                "negative_cases": [
                    "missing load",
                    "scalar read before load",
                    "missing store-back",
                    "intervening alias write clobbers A[i]",
                    "unknown call may clobber A[i]",
                    "public use reads stale A[i] instead of promoted scalar",
                    "store-back targets the wrong public index",
                    "two logical cells share one scalar over overlapping intervals",
                    "promoted scalar escapes as public output",
                    "scalar storage incompatible with promoted cell",
                ],
                "endpoint": "public_output_view_eq observes final A and B; scalar s is hidden",
            },
        },
        "caveat": "The .scop skeleton shows protocol access shape; JSON sidecar supplies roles and validator obligations.",
    }


def write(out_dir: Path, name: str, text: str) -> None:
    path = out_dir / name
    path.write_text(text)
    print(f"wrote {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate toy OpenScop private protocol evidence.")
    parser.add_argument("--out-dir", type=Path, default=Path("storage/evidence"))
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    write(args.out_dir, "toy_private_copy_boundary_source.scop", private_copy_source())
    write(args.out_dir, "toy_private_copy_boundary_target.scop", private_copy_target())
    write(args.out_dir, "toy_private_access_source.scop", private_access_source())
    write(args.out_dir, "toy_private_access_target.scop", private_access_target())
    write(args.out_dir, "toy_scalar_promotion_source.scop", scalar_promotion_source())
    write(args.out_dir, "toy_scalar_promotion_target.scop", scalar_promotion_target())
    witness_path = args.out_dir / "toy_private_protocols_witness.json"
    witness_path.write_text(json.dumps(witness(), indent=2, sort_keys=True) + "\n")
    print(f"wrote {witness_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
