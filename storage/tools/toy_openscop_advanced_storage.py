#!/usr/bin/env python3
"""Generate toy OpenScop evidence for advanced storage transformations.

Covered cases:

- array_expansion_versioning
- reduction_privatization
- overlapped_tiling
- storage_view_composition

The .scop files are intentionally lightweight skeletons.  They show the
storage-access shape, while the JSON sidecar records the validator-facing
correctness witness: version selectors, merge trees, commit covers, and view
composition interfaces.
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


def relation_2d(kind: str, array: str, index1: str, row1: str, index2: str, row2: str) -> str:
    return "\n".join(
        [
            kind,
            "3 8 3 2 0 1",
            "# e/i| Arr [1] [2]| t i | 1",
            f"   0   -1    0    0    0    0    0    0    ## Arr == {array}",
            f"   {row1}    ## [1] == {index1}",
            f"   {row2}    ## [2] == {index2}",
            "",
        ]
    )


ROW_T = "0    0   -1    1    0    0    0    0"
ROW_I_2D = "0    0    0   -1    0    1    0    0"
ROW_T_MINUS_1 = "0    0   -1    0    1    0    0    0"
ROW_K = "0    0   -1    0    1    0"


def version_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop array expansion/versioning source skeleton",
            "# X[i] is overwritten at each t; Y[t][i] observes the current X[i].",
            "<arrays>",
            "1 X",
            "2 Y",
            "</arrays>",
            "<body>",
            "# Statement S_write_x(t,i)",
            relation_1d("WRITE", "X", "i"),
            "# Statement S_read_x_to_y(t,i)",
            relation_1d("READ", "X", "i"),
            relation_2d("WRITE", "Y", "t", ROW_T, "i", ROW_I_2D),
            "</body>",
            "",
        ]
    )


def version_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop array expansion/versioning target skeleton",
            "# Each source definition of X[i] is stored as X_exp[t][i].",
            "<arrays>",
            "1 X",
            "2 X_exp",
            "3 Y",
            "</arrays>",
            "<body>",
            "# Statement S_write_version(t,i)",
            relation_2d("WRITE", "X_exp", "t", ROW_T, "i", ROW_I_2D),
            "# Statement S_read_version_to_y(t,i)",
            relation_2d("READ", "X_exp", "t", ROW_T, "i", ROW_I_2D),
            relation_2d("WRITE", "Y", "t", ROW_T, "i", ROW_I_2D),
            "# Statement S_final_copy(i)",
            relation_2d("READ", "X_exp", "T - 1", ROW_T_MINUS_1, "i", ROW_I_2D),
            relation_1d("WRITE", "X", "i"),
            "</body>",
            "",
        ]
    )


def reduction_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop reduction privatization source skeleton",
            "# sum = fold_plus(A[i])",
            "<arrays>",
            "1 A",
            "2 sum",
            "</arrays>",
            "<body>",
            "# Statement S_reduce(i)",
            relation_1d("READ", "A", "i"),
            relation_1d("READ", "sum", "scalar", "0   -1    0    0    0    0"),
            relation_1d("WRITE", "sum", "scalar", "0   -1    0    0    0    0"),
            "</body>",
            "",
        ]
    )


def reduction_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop reduction privatization target skeleton",
            "# local[p] reduces chunk p; merge consumes every local[p].",
            "<arrays>",
            "1 A",
            "2 local",
            "3 sum",
            "</arrays>",
            "<body>",
            "# Statement S_chunk_reduce(p,i)",
            relation_1d("READ", "A", "chunk(p,i)", "0    0   -1    1    1    0"),
            relation_1d("READ", "local", "p", ROW_K),
            relation_1d("WRITE", "local", "p", ROW_K),
            "# Statement S_merge(p)",
            relation_1d("READ", "local", "p", ROW_K),
            relation_1d("READ", "sum", "scalar", "0   -1    0    0    0    0"),
            relation_1d("WRITE", "sum", "scalar", "0   -1    0    0    0    0"),
            "</body>",
            "",
        ]
    )


def overlap_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop overlapped tiling source skeleton",
            "# B[i] depends on A[i-1], A[i], A[i+1].",
            "<arrays>",
            "1 A",
            "2 B",
            "</arrays>",
            "<body>",
            "# Statement S_stencil(i)",
            relation_1d("READ", "A", "i - 1", "0    0   -1    1    0   -1"),
            relation_1d("READ", "A", "i"),
            relation_1d("READ", "A", "i + 1", "0    0   -1    1    0    1"),
            relation_1d("WRITE", "B", "i"),
            "</body>",
            "",
        ]
    )


def overlap_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop overlapped tiling target skeleton",
            "# Tiles compute halo/private duplicates; only owner commits public B[i].",
            "<arrays>",
            "1 A",
            "2 B",
            "3 B_tile",
            "</arrays>",
            "<body>",
            "# Statement S_tile_compute(tile,k)",
            relation_1d("READ", "A", "tile_base + k - 1", "0    0   -1    1    1   -1"),
            relation_1d("READ", "A", "tile_base + k", "0    0   -1    1    1    0"),
            relation_1d("READ", "A", "tile_base + k + 1", "0    0   -1    1    1    1"),
            relation_1d("WRITE", "B_tile", "k", ROW_K),
            "# Statement S_tile_commit(tile,k)",
            relation_1d("READ", "B_tile", "k", ROW_K),
            relation_1d("WRITE", "B", "tile_base + k", "0    0   -1    1    1    0"),
            "</body>",
            "",
        ]
    )


def composition_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop storage view composition source skeleton",
            "# Logical A is updated directly.",
            "<arrays>",
            "1 A",
            "</arrays>",
            "<body>",
            "# Statement S_update(i)",
            relation_1d("READ", "A", "i"),
            relation_1d("WRITE", "A", "i"),
            "</body>",
            "",
        ]
    )


def composition_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop storage view composition target skeleton",
            "# A_pad represents logical A; tmp is private and erased from public view.",
            "<arrays>",
            "1 A_pad",
            "2 tmp",
            "</arrays>",
            "<body>",
            "# Statement S_load_private(i)",
            relation_1d("READ", "A_pad", "2*i", "0    0   -1    2    0    0"),
            relation_1d("WRITE", "tmp", "i"),
            "# Statement S_store_layout(i)",
            relation_1d("READ", "tmp", "i"),
            relation_1d("WRITE", "A_pad", "2*i", "0    0   -1    2    0    0"),
            "</body>",
            "",
        ]
    )


def witness() -> dict[str, object]:
    return {
        "schema_version": 1,
        "cases": {
            "array_expansion_versioning": {
                "source_scop": "toy_versioning_source.scop",
                "target_scop": "toy_versioning_target.scop",
                "public_logical_interface": {"inputs": ["X initial"], "outputs": ["X final", "Y"]},
                "private_target_storage": ["X_exp"],
                "statement_roles": [
                    {"statement": "S_write_x", "role": "source_def"},
                    {"statement": "S_write_version", "role": "version_write"},
                    {"statement": "S_read_version_to_y", "role": "version_read"},
                    {"statement": "S_final_copy", "role": "copy_out"},
                ],
                "representation_witness": {
                    "kind": "VersionSelect",
                    "definition_to_version_map": "X@S_write_x(t,i) -> X_exp[t,i]",
                    "version_storage_spec": {
                        "target_var": "X_exp",
                        "version_dimension": "t",
                        "logical_index_map": ["t", "i"],
                        "bounds": "0 <= t < T, 0 <= i < N",
                        "element_type": "same as X",
                    },
                    "produced_versions": ["X_exp[t,i] produced by S_write_version(t,i)"],
                    "read_version_selectors": ["S_read_version_to_y(t,i) selects X_exp[t,i]"],
                    "final_selector": "public X[i] is copied from X_exp[T-1,i]",
                    "copy_out_or_projection": "copy_out",
                    "version_bounds": "requires T > 0 or an explicit initial-version rule for T = 0",
                },
                "versions": [
                    {
                        "logical_definition": "X@S_write_x(t,i)",
                        "physical_version": "X_exp[t,i]",
                        "producer_event": "S_write_version(t,i)",
                        "read_selectors": ["S_read_version_to_y(t,i) selects X_exp[t,i]"],
                    }
                ],
                "checked_obligations": [
                    "every read selects a produced version",
                    "selected versions are unique when committed to public X",
                    "final selector chooses the source-final definition",
                    "version storage is in bounds and storage-compatible",
                ],
                "negative_cases": [
                    "final selector chooses an old version",
                    "read selector chooses an unproduced version",
                    "version index is out of bounds",
                    "two inconsistent versions commit to one public cell",
                    "T = 0 without an initial-version rule",
                ],
                "endpoint": "public_output_view_eq observes logical X final and Y; X_exp is hidden except through final copy-out",
            },
            "reduction_privatization": {
                "source_scop": "toy_reduction_source.scop",
                "target_scop": "toy_reduction_target.scop",
                "public_logical_interface": {"inputs": ["A"], "outputs": ["sum"]},
                "private_target_storage": ["local[p]"],
                "statement_roles": [
                    {"statement": "S_reduce", "role": "source_reduction_update"},
                    {"statement": "S_chunk_reduce", "role": "reduction_update"},
                    {"statement": "S_merge", "role": "merge"},
                ],
                "representation_witness": {
                    "kind": "ReductionMerge",
                    "reduction_id": "sum_plus_A",
                    "carrier_type": "int-like finite carrier",
                    "operator": "plus",
                    "identity": "0",
                    "source_reduction_semantics": "mathematical finite fold over i in [0,N)",
                    "chunk_partition": "chunks(p) are disjoint and exactly cover i in [0,N)",
                    "accumulator_storage": {"target_var": "local", "index": "p", "bounds": "0 <= p < P", "type": "same as sum"},
                    "accumulator_init": "each local[p] is initialized to identity before S_chunk_reduce(p,*)",
                    "contribution_map": "source contribution A[i] belongs to exactly one chunk p",
                    "local_fold_order": "source order inside each chunk",
                    "merge_tree": "sum = plus(local[0], plus(local[1], ... local[P-1]))",
                    "operator_laws": ["closed", "identity", "associative", "commutative if chunks are reordered"],
                },
                "checked_obligations": [
                    "each source contribution appears in exactly one private accumulator",
                    "merge consumes every private accumulator exactly once",
                    "private accumulators do not escape as public state",
                    "operator laws justify regrouping and reordering",
                ],
                "negative_cases": [
                    "chunk overlap or missing contribution",
                    "private accumulator not initialized",
                    "merge omits or duplicates an accumulator",
                    "operator laws are insufficient",
                    "private accumulator escapes",
                    "public sum is not committed from merge root",
                ],
                "endpoint": "public_output_view_eq observes sum only after the merge root; local[p] is hidden",
            },
            "overlapped_tiling": {
                "source_scop": "toy_overlap_source.scop",
                "target_scop": "toy_overlap_target.scop",
                "public_logical_interface": {"inputs": ["A"], "outputs": ["B"]},
                "private_target_storage": ["B_tile"],
                "statement_roles": [
                    {"statement": "S_stencil", "role": "source_compute"},
                    {"statement": "S_tile_compute", "role": "halo_compute"},
                    {"statement": "S_tile_commit", "role": "commit"},
                ],
                "representation_witness": {
                    "kind": "CommitSet",
                    "source_instance_domain": "S_stencil(i), 0 <= i < N",
                    "target_duplicate_domain": "S_tile_compute(tile,k), k includes interior plus halo",
                    "duplicate_projection": "target tile computation (tile,k) projects to source S_stencil(tile_base+k)",
                    "halo_region": "one-cell halo around each committed tile interior",
                    "halo_closure": "tile-local reads include producer/copy-in/public live-in evidence for A[i-1], A[i], A[i+1]",
                    "commit_set": "S_tile_commit(tile,k) where tile owns tile_base+k",
                    "commit_map": "S_tile_commit(tile,k) -> public B[tile_base+k]",
                    "commit_exact_cover": "committed target writes cover every source public B[i] exactly once",
                    "private_duplicate_storage": "B_tile[k] stores duplicate/halo values not in public view",
                    "boundary_guards": "partial tiles and edge cells are guarded by in-domain checks",
                },
                "checked_obligations": [
                    "duplicate halo computations stay private",
                    "every committed point has local producers for its dependencies",
                    "commit writes are public and unique",
                    "private halo writes are in bounds and hidden",
                ],
                "negative_cases": [
                    "missing halo producer",
                    "duplicate target computations write public output directly",
                    "two commits for one public output",
                    "commit set misses a public output",
                    "partial tile accesses out of bounds",
                    "private halo write is observed as final output",
                ],
                "endpoint": "public_output_view_eq observes committed B only; B_tile duplicates are hidden",
            },
            "storage_view_composition": {
                "source_scop": "toy_view_composition_source.scop",
                "target_scop": "toy_view_composition_target.scop",
                "public_logical_interface": {"inputs": ["A"], "outputs": ["A"]},
                "private_target_storage": ["tmp"],
                "physical_target_storage": ["A_pad"],
                "statement_roles": [
                    {"statement": "S_update", "role": "source_compute"},
                    {"statement": "S_load_private", "role": "composition_mid"},
                    {"statement": "S_store_layout", "role": "composition_export"},
                ],
                "representation_witness": {
                    "kind": "ViewComposition",
                    "stages": ["private erasure", "layout projection"],
                    "source_to_mid_view": "logical A[i] maps to mid A_pad[2*i]",
                    "mid_to_target_view": "target tmp is erased; target A_pad remains observable in mid",
                    "intermediate_interface": {
                        "public_vars": ["A_pad even cells"],
                        "private_vars": ["tmp", "padding cells"],
                        "footprint": "A_pad[2*i] for logical i in bounds",
                    },
                    "stage_witness_refs": ["DirectLayout(A -> A_pad[2*i])", "PrivateErasure(tmp)"],
                    "composed_output_view": "logical A[i] is exported from target A_pad[2*i]",
                    "compatibility": "mid footprint/type equals source logical A footprint/type under layout projection",
                    "private_monotonicity": "tmp stays private unless an explicit export witness is present",
                },
                "intermediate_observables": ["A_pad[2*i] values agree with logical A[i]", "padding cells are unobserved"],
                "checked_obligations": [
                    "private erasure ignores only hidden fresh storage",
                    "layout projection covers exactly the public logical footprint",
                    "both views agree on the intermediate observable cells",
                    "composed view exports public_output_view_eq",
                ],
                "negative_cases": [
                    "mid observable footprint mismatches next-stage input",
                    "private var leaks into composed public view",
                    "composed access remap differs from stagewise remap",
                    "stage endpoints hold but intermediate interfaces are incompatible",
                ],
                "endpoint": "public_output_view_eq is the composed logical view; mid is not a concrete program endpoint",
            },
        },
        "caveat": "The .scop skeleton shows access shape only; correctness roles are in this JSON sidecar.",
    }


def write(out_dir: Path, name: str, text: str) -> None:
    path = out_dir / name
    path.write_text(text)
    print(f"wrote {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate toy OpenScop advanced storage evidence.")
    parser.add_argument("--out-dir", type=Path, default=Path("storage/evidence"))
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    write(args.out_dir, "toy_versioning_source.scop", version_source())
    write(args.out_dir, "toy_versioning_target.scop", version_target())
    write(args.out_dir, "toy_reduction_source.scop", reduction_source())
    write(args.out_dir, "toy_reduction_target.scop", reduction_target())
    write(args.out_dir, "toy_overlap_source.scop", overlap_source())
    write(args.out_dir, "toy_overlap_target.scop", overlap_target())
    write(args.out_dir, "toy_view_composition_source.scop", composition_source())
    write(args.out_dir, "toy_view_composition_target.scop", composition_target())
    witness_path = args.out_dir / "toy_advanced_storage_witness.json"
    witness_path.write_text(json.dumps(witness(), indent=2, sort_keys=True) + "\n")
    print(f"wrote {witness_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
