#!/usr/bin/env python3
"""Generate a toy OpenScop scratchpad/copy boundary witness.

This is a narrow survey generator, not a full OpenScop optimizer.  It emits
source/target access skeletons for two scratchpad patterns:

  scratchpad_packing:
    source: C[i] = A[i] + B[i]

    target:
      Bp[k] = B[kk + k]          // copy-in
      C[kk + k] = A[kk + k] + Bp[k]

  scratchpad_copy_out:
    source: A[i] = A[i] + 1

    target:
      Al[k] = A[kk + k]          // copy-in
      Al[k] = Al[k] + 1          // local update
      A[kk + k] = Al[k]          // copy-out

The generated .scop files are intentionally simple text artifacts that use the
same access-relation comments consumed by openscop_storage_diff.py.  The JSON
witness is the important validation artifact: it states the public logical
interface, private local buffers, and copy-in/copy-out boundary maps.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def relation(kind: str, array: str, index_comment: str, row: str) -> str:
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


def build_packing_source_scop() -> str:
    return "\n".join(
        [
            "# Toy OpenScop scratchpad packing source skeleton",
            "# Logical program: C[i] = A[i] + B[i]",
            "<arrays>",
            "1 A",
            "2 B",
            "3 C",
            "</arrays>",
            "<body>",
            "# Statement S_compute(i)",
            relation("READ", "A", "i", "0    0   -1    1    0    0"),
            relation("READ", "B", "i", "0    0   -1    1    0    0"),
            relation("WRITE", "C", "i", "0    0   -1    1    0    0"),
            "</body>",
            "",
        ]
    )


def build_packing_target_scop() -> str:
    return "\n".join(
        [
            "# Toy OpenScop scratchpad packing target skeleton",
            "# Target program:",
            "#   Bp[k] = B[kk + k]",
            "#   C[kk + k] = A[kk + k] + Bp[k]",
            "<arrays>",
            "1 A",
            "2 B",
            "3 C",
            "4 Bp",
            "</arrays>",
            "<body>",
            "# Statement S_copy_in(kk,k)",
            relation("READ", "B", "kk + k", "0    0   -1    1    1    0"),
            relation("WRITE", "Bp", "k", "0    0   -1    0    1    0"),
            "# Statement S_compute_local(kk,k)",
            relation("READ", "A", "kk + k", "0    0   -1    1    1    0"),
            relation("READ", "Bp", "k", "0    0   -1    0    1    0"),
            relation("WRITE", "C", "kk + k", "0    0   -1    1    1    0"),
            "</body>",
            "",
        ]
    )


def build_copyout_source_scop() -> str:
    return "\n".join(
        [
            "# Toy OpenScop scratchpad copy-out source skeleton",
            "# Logical program: A[i] = A[i] + 1",
            "<arrays>",
            "1 A",
            "</arrays>",
            "<body>",
            "# Statement S_update(i)",
            relation("READ", "A", "i", "0    0   -1    1    0    0"),
            relation("WRITE", "A", "i", "0    0   -1    1    0    0"),
            "</body>",
            "",
        ]
    )


def build_copyout_target_scop() -> str:
    return "\n".join(
        [
            "# Toy OpenScop scratchpad copy-out target skeleton",
            "# Target program:",
            "#   Al[k] = A[kk + k]",
            "#   Al[k] = Al[k] + 1",
            "#   A[kk + k] = Al[k]",
            "<arrays>",
            "1 A",
            "2 Al",
            "</arrays>",
            "<body>",
            "# Statement S_copy_in(kk,k)",
            relation("READ", "A", "kk + k", "0    0   -1    1    1    0"),
            relation("WRITE", "Al", "k", "0    0   -1    0    1    0"),
            "# Statement S_update_local(kk,k)",
            relation("READ", "Al", "k", "0    0   -1    0    1    0"),
            relation("WRITE", "Al", "k", "0    0   -1    0    1    0"),
            "# Statement S_copy_out(kk,k)",
            relation("READ", "Al", "k", "0    0   -1    0    1    0"),
            relation("WRITE", "A", "kk + k", "0    0   -1    1    1    0"),
            "</body>",
            "",
        ]
    )


def build_witness(tile_size: str) -> dict[str, object]:
    return {
        "cases": {
            "scratchpad_packing": {
                "public_logical_interface": {
                    "inputs": ["A", "B"],
                    "outputs": ["C"],
                },
                "private_target_storage": ["Bp"],
                "copy_in": [
                    {
                        "public": "B[kk + k]",
                        "private": "Bp[k]",
                        "phase": "before local compute",
                    }
                ],
                "local_compute": [
                    {
                        "source_read": "B[kk + k]",
                        "target_read": "Bp[k]",
                        "justification": "copy_in",
                    },
                    {
                        "source_write": "C[kk + k]",
                        "target_write": "C[kk + k]",
                        "justification": "public write uses private live-in cache",
                    },
                ],
                "copy_out": [],
                "endpoint": "public_output_view_eq observes A, B, C logically; Bp is hidden",
            },
            "scratchpad_copy_out": {
                "public_logical_interface": {
                    "inputs": ["A"],
                    "outputs": ["A"],
                },
                "private_target_storage": ["Al"],
                "copy_in": [
                    {
                        "public": "A[kk + k]",
                        "private": "Al[k]",
                        "phase": "before local update",
                    }
                ],
                "local_compute": [
                    {
                        "source_read": "A[kk + k]",
                        "target_read": "Al[k]",
                        "justification": "copy_in",
                    },
                    {
                        "source_write": "A[kk + k]",
                        "target_write": "Al[k]",
                        "justification": "private local update before copy_out",
                    },
                ],
                "copy_out": [
                    {
                        "private": "Al[k]",
                        "public": "A[kk + k]",
                        "phase": "after local update",
                    }
                ],
                "endpoint": "public_output_view_eq observes logical A after copy-out; Al is hidden",
            },
        },
        "tile_domain": {
            "outer": "kk",
            "inner": "k",
            "bounds": f"0 <= k < {tile_size}, kk <= kk + k < N",
        },
        "required_obligations": [
            "copy-in covers every local read that depends on a public live-in",
            "local buffers are private target storage",
            "copy-out covers every public live-out when copy-out is required",
            "copy-out commits each public live-out exactly once when copy-out is required",
            "tile domains exactly cover the source public output footprint",
            "local accesses are in bounds for the declared tile size",
            "partial boundary tiles are guarded or have a checked exact domain",
        ],
        "caveat": "OpenScop access relations show reads/writes; copy-in/copy-out roles come from this structured witness sidecar",
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate toy OpenScop scratchpad evidence.")
    parser.add_argument("--out-dir", type=Path, default=Path("storage/evidence"))
    parser.add_argument("--tile-size", default="T")
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    packing_source = args.out_dir / "toy_scratchpad_packing_source.scop"
    packing_target = args.out_dir / "toy_scratchpad_packing_target.scop"
    copyout_source = args.out_dir / "toy_scratchpad_copyout_source.scop"
    copyout_target = args.out_dir / "toy_scratchpad_copyout_target.scop"
    witness = args.out_dir / "toy_scratchpad_witness.json"

    packing_source.write_text(build_packing_source_scop())
    packing_target.write_text(build_packing_target_scop())
    copyout_source.write_text(build_copyout_source_scop())
    copyout_target.write_text(build_copyout_target_scop())
    witness.write_text(json.dumps(build_witness(args.tile_size), indent=2, sort_keys=True) + "\n")

    print(f"wrote {packing_source}")
    print(f"wrote {packing_target}")
    print(f"wrote {copyout_source}")
    print(f"wrote {copyout_target}")
    print(f"wrote {witness}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
