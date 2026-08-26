#!/usr/bin/env python3
"""Generate toy OpenScop reuse/folding evidence.

This generator emits OpenScop-shaped skeletons plus a structured JSON witness
for three storage-reuse families:

- array_contraction: logical A[t][i] is represented by physical A2[t mod 2][i]
- inter_array_reuse: logical T1[i] and T2[i] share physical Buf[i] in disjoint
  phases
- double_buffering: logical A[t][i] is represented by Buf[cur/next][i] under a
  phase projection

The .scop files are intentionally lightweight.  OpenScop access relations can
show that the target uses folded/private physical arrays, but the semantic facts
that make reuse correct live in the JSON sidecar: valid intervals,
producer/consumer events, kill/reuse events, and boundary projection.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def relation_1d(kind: str, array: str, index_comment: str, row: str) -> str:
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


def contraction_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop array contraction source skeleton",
            "# Logical program: A[t][i] = A[t-1][i] + 1",
            "<arrays>",
            "1 A",
            "</arrays>",
            "<body>",
            "# Statement S_update(t,i)",
            relation_2d("READ", "A", "t - 1", "0    0   -1    0    1    0    0    0", "i", "0    0    0   -1    0    1    0    0"),
            relation_2d("WRITE", "A", "t", "0    0   -1    1    0    0    0    0", "i", "0    0    0   -1    0    1    0    0"),
            "</body>",
            "",
        ]
    )


def contraction_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop array contraction target skeleton",
            "# Target program: A2[t mod 2][i] = A2[(t-1) mod 2][i] + 1",
            "# The modulo/phase projection is represented in the JSON witness.",
            "<arrays>",
            "1 A2",
            "</arrays>",
            "<body>",
            "# Statement S_update_folded(t,i)",
            relation_2d("READ", "A2", "(t - 1) mod 2", "0    0   -1    0    1    0    0    0", "i", "0    0    0   -1    0    1    0    0"),
            relation_2d("WRITE", "A2", "t mod 2", "0    0   -1    1    0    0    0    0", "i", "0    0    0   -1    0    1    0    0"),
            "</body>",
            "",
        ]
    )


def inter_array_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop inter-array reuse source skeleton",
            "# T1 and T2 are separate logical temporaries.",
            "<arrays>",
            "1 A",
            "2 B",
            "3 C",
            "4 D",
            "5 T1",
            "6 T2",
            "</arrays>",
            "<body>",
            "# Phase P1",
            relation_1d("READ", "A", "i", "0    0   -1    1    0    0"),
            relation_1d("WRITE", "T1", "i", "0    0   -1    1    0    0"),
            relation_1d("READ", "T1", "i", "0    0   -1    1    0    0"),
            relation_1d("WRITE", "C", "i", "0    0   -1    1    0    0"),
            "# Phase P2",
            relation_1d("READ", "B", "i", "0    0   -1    1    0    0"),
            relation_1d("WRITE", "T2", "i", "0    0   -1    1    0    0"),
            relation_1d("READ", "T2", "i", "0    0   -1    1    0    0"),
            relation_1d("WRITE", "D", "i", "0    0   -1    1    0    0"),
            "</body>",
            "",
        ]
    )


def inter_array_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop inter-array reuse target skeleton",
            "# T1 and T2 are both represented by private Buf in disjoint phases.",
            "<arrays>",
            "1 A",
            "2 B",
            "3 C",
            "4 D",
            "5 Buf",
            "</arrays>",
            "<body>",
            "# Phase P1",
            relation_1d("READ", "A", "i", "0    0   -1    1    0    0"),
            relation_1d("WRITE", "Buf", "i", "0    0   -1    1    0    0"),
            relation_1d("READ", "Buf", "i", "0    0   -1    1    0    0"),
            relation_1d("WRITE", "C", "i", "0    0   -1    1    0    0"),
            "# Phase P2; Buf is reused after T1's last consumer.",
            relation_1d("READ", "B", "i", "0    0   -1    1    0    0"),
            relation_1d("WRITE", "Buf", "i", "0    0   -1    1    0    0"),
            relation_1d("READ", "Buf", "i", "0    0   -1    1    0    0"),
            relation_1d("WRITE", "D", "i", "0    0   -1    1    0    0"),
            "</body>",
            "",
        ]
    )


def double_buffer_source() -> str:
    return "\n".join(
        [
            "# Toy OpenScop double buffering source skeleton",
            "# Logical program: A[t][i] = A[t-1][i] + 1",
            "<arrays>",
            "1 A",
            "</arrays>",
            "<body>",
            "# Statement S_step(t,i)",
            relation_2d("READ", "A", "t - 1", "0    0   -1    0    1    0    0    0", "i", "0    0    0   -1    0    1    0    0"),
            relation_2d("WRITE", "A", "t", "0    0   -1    1    0    0    0    0", "i", "0    0    0   -1    0    1    0    0"),
            "</body>",
            "",
        ]
    )


def double_buffer_target() -> str:
    return "\n".join(
        [
            "# Toy OpenScop double buffering target skeleton",
            "# Target program: next[i] = cur[i] + 1; swap(cur,next)",
            "# cur/next phase projection is represented in the JSON witness.",
            "<arrays>",
            "1 Buf",
            "</arrays>",
            "<body>",
            "# Statement S_step_buffered(t,i)",
            relation_2d("READ", "Buf", "cur(t)", "0    0   -1    0    1    0    0    0", "i", "0    0    0   -1    0    1    0    0"),
            relation_2d("WRITE", "Buf", "next(t)", "0    0   -1    1    0    0    0    0", "i", "0    0    0   -1    0    1    0    0"),
            "</body>",
            "",
        ]
    )


def witness() -> dict[str, object]:
    return {
        "cases": {
            "array_contraction": {
                "public_logical_interface": {"inputs": ["A[0][:]"], "outputs": ["A[T][:]"]},
                "private_target_storage": ["A2[0][:]", "A2[1][:]"],
                "logical_values": [
                    {
                        "logical_value_id": "A[t,i]",
                        "logical_var": "A",
                        "logical_index": ["t", "i"],
                        "physical_region": "A2[t mod 2, i]",
                        "producer_event": "S_update(t,i)",
                        "consumer_events": ["S_update(t+1,i) when t < T"],
                        "valid_interval": ["after S_update(t,i)", "before S_update(t+2,i)"],
                        "kill_or_reuse_event": "S_update(t+2,i) may overwrite A2[t mod 2,i]",
                        "boundary_projection": "if t == T then public A[T,i] is exported from A2[T mod 2,i]",
                    }
                ],
                "collision_rule": "A[t,i] and A[t+2,i] share a physical region but are not simultaneously live",
            },
            "inter_array_reuse": {
                "public_logical_interface": {"inputs": ["A", "B"], "outputs": ["C", "D"]},
                "private_target_storage": ["Buf"],
                "logical_values": [
                    {
                        "logical_value_id": "T1[i]",
                        "logical_var": "T1",
                        "logical_index": ["i"],
                        "physical_region": "Buf[i]",
                        "producer_event": "P1_write_Buf(i)",
                        "consumer_events": ["P1_read_Buf_for_C(i)"],
                        "valid_interval": ["after P1_write_Buf(i)", "before P2_write_Buf(i)"],
                        "kill_or_reuse_event": "P2_write_Buf(i)",
                        "boundary_projection": "public C[i] is committed before Buf[i] is reused",
                    },
                    {
                        "logical_value_id": "T2[i]",
                        "logical_var": "T2",
                        "logical_index": ["i"],
                        "physical_region": "Buf[i]",
                        "producer_event": "P2_write_Buf(i)",
                        "consumer_events": ["P2_read_Buf_for_D(i)"],
                        "valid_interval": ["after P2_write_Buf(i)", "through P2_read_Buf_for_D(i)"],
                        "kill_or_reuse_event": "none inside fragment",
                        "boundary_projection": "public D[i] is committed after reading Buf[i]",
                    },
                ],
                "storage_compatibility": "T1[i], T2[i], and Buf[i] have identical element layout and extent",
                "collision_rule": "T1[i] and T2[i] share Buf[i] only across disjoint phase intervals",
            },
            "double_buffering": {
                "public_logical_interface": {"inputs": ["A[0][:]"], "outputs": ["A[T][:]"]},
                "private_target_storage": ["Buf[0][:]", "Buf[1][:]"],
                "phase_projection": {
                    "init": "Buf[0][i] represents A[0][i] before the first step",
                    "cur(t)": "(t - 1) mod 2",
                    "next(t)": "t mod 2",
                },
                "logical_values": [
                    {
                        "logical_value_id": "A[t,i]",
                        "logical_var": "A",
                        "logical_index": ["t", "i"],
                        "physical_region": "Buf[t mod 2, i]",
                        "producer_event": "S_step_buffered(t,i) writes Buf[next(t),i]",
                        "consumer_events": ["S_step_buffered(t+1,i) reads Buf[cur(t+1),i] when t < T"],
                        "valid_interval": ["after S_step_buffered(t,i)", "before S_step_buffered(t+2,i)"],
                        "kill_or_reuse_event": "S_step_buffered(t+2,i) may overwrite Buf[t mod 2,i]",
                        "boundary_projection": "if t == T then public A[T,i] is exported from Buf[T mod 2,i]",
                    }
                ],
                "swap_obligation": "after each step, next(t) becomes cur(t+1) and cur(t) becomes reusable",
                "read_write_role_obligation": "each step reads cur(t) and writes next(t), never the reverse",
            },
        },
        "required_obligations": [
            "physical reuse is allowed only when logical valid intervals are disjoint",
            "every read is linked to a producer whose value is still valid",
            "each kill or reuse event is after the old logical value's last consumer",
            "final public outputs are projected or copied before reused private storage is hidden",
            "all physical regions have compatible element layout, extent, and bounds",
            "phase projections such as modulo or cur/next are supplied by the witness sidecar, not by raw OpenScop access rows",
        ],
        "caveat": "The .scop skeleton shows folded physical storage; lifetime and phase correctness is in this JSON witness.",
    }


def write(out_dir: Path, name: str, text: str) -> None:
    path = out_dir / name
    path.write_text(text)
    print(f"wrote {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate toy OpenScop reuse/folding evidence.")
    parser.add_argument("--out-dir", type=Path, default=Path("storage/evidence"))
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    write(args.out_dir, "toy_array_contraction_source.scop", contraction_source())
    write(args.out_dir, "toy_array_contraction_target.scop", contraction_target())
    write(args.out_dir, "toy_inter_array_reuse_source.scop", inter_array_source())
    write(args.out_dir, "toy_inter_array_reuse_target.scop", inter_array_target())
    write(args.out_dir, "toy_double_buffering_source.scop", double_buffer_source())
    write(args.out_dir, "toy_double_buffering_target.scop", double_buffer_target())
    witness_path = args.out_dir / "toy_reuse_folding_witness.json"
    witness_path.write_text(json.dumps(witness(), indent=2, sort_keys=True) + "\n")
    print(f"wrote {witness_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
