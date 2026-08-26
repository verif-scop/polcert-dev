#!/usr/bin/env python3
"""Build a storage transformation manifest from coverage logs and examples."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from summarize_standalone import parse_negative, parse_positive


HAND_CLASSIFICATION = {
    "source_no_alias_abstraction": {
        "survey_group": "precondition",
        "external_evidence": "toy OpenScop boundary/domain generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop source-footprint/no-alias witness; precondition rather than storage rewrite",
        "acceptance_reason": "logical source variables have distinct footprints, so storage reasoning over variables is sound",
    },
    "contextual_frame_preservation": {
        "survey_group": "context",
        "external_evidence": "toy OpenScop boundary/domain generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop contextual-frame witness; boundary condition rather than storage rewrite",
        "acceptance_reason": "writes stay inside the allowed fragment footprint and protected frame variables keep their values",
    },
    "affine_interchange": {
        "survey_group": "schedule_only",
        "external_evidence": "polopt/pluto schedule validation, standalone",
        "tool_backed": True,
        "artifact_status": "real schedule tooling; storage-preserving rather than storage rewrite",
        "acceptance_reason": "instances and storage accesses are unchanged; only legal schedule order changes",
    },
    "index_set_splitting": {
        "survey_group": "schedule_domain",
        "external_evidence": "toy OpenScop boundary/domain generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop domain-partition witness; storage-preserving",
        "acceptance_reason": "target subdomains disjointly and exactly cover the source domain",
    },
    "ordinary_tiling": {
        "survey_group": "schedule_domain",
        "external_evidence": "polopt/pluto tiling validation, standalone",
        "tool_backed": True,
        "artifact_status": "real schedule/tiling tooling; storage-preserving",
        "acceptance_reason": "tile projection covers source instances and storage accesses are unchanged",
    },
    "scalar_privatization_expansion": {
        "survey_group": "storage_expansion",
        "external_evidence": "candl -scalexp OpenScop access rewrite, standalone",
        "tool_backed": True,
        "artifact_status": "real Candl OpenScop storage access rewrite",
        "acceptance_reason": "each source temporary live range is represented by a fresh per-instance private cell before public use",
    },
    "private_copy_boundary": {
        "survey_group": "private_boundary",
        "external_evidence": "toy OpenScop private-protocol generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop copy-boundary witness; no current Pluto/OpenScop pass observed",
        "acceptance_reason": "copy-in initializes private live-ins and unique copy-out commits private live-outs to public variables",
    },
    "private_access_local_instantiation": {
        "survey_group": "private_access",
        "external_evidence": "toy OpenScop private-protocol generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop symbolic-private-access witness; no current Pluto/OpenScop pass observed",
        "acceptance_reason": "symbolic private accesses instantiate to declared, in-bounds, hidden private cells",
    },
    "layout_remap_padding": {
        "survey_group": "layout",
        "external_evidence": "toy OpenScop layout remap probe, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop access rewrite; no current Pluto/OpenScop layout pass observed",
        "acceptance_reason": "logical public cells are represented by an injective in-bounds physical layout map",
    },
    "scratchpad_packing": {
        "survey_group": "scratchpad",
        "external_evidence": "toy OpenScop scratchpad generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop copy-in/local-buffer witness; no current Pluto/OpenScop scratchpad pass observed",
        "acceptance_reason": "copy-in covers local reads and local buffer cells consistently represent a public tile",
    },
    "scratchpad_copy_out": {
        "survey_group": "scratchpad",
        "external_evidence": "toy OpenScop scratchpad generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop copy-out witness; no current Pluto/OpenScop scratchpad copy-out pass observed",
        "acceptance_reason": "local updates are private until every updated public cell is committed exactly once",
    },
    "scalar_promotion": {
        "survey_group": "promotion",
        "external_evidence": "toy OpenScop private-protocol generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop scalar-promotion protocol witness; standalone negatives still thin",
        "acceptance_reason": "entry load, scalar updates, and exit store implement the same public cell value",
    },
    "array_contraction": {
        "survey_group": "reuse_folding",
        "external_evidence": "toy OpenScop reuse/folding generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop folded-storage witness; no current Pluto/OpenScop contraction pass observed",
        "acceptance_reason": "non-injective physical reuse is allowed only for non-overlapping logical lifetimes",
    },
    "inter_array_reuse": {
        "survey_group": "reuse_folding",
        "external_evidence": "toy OpenScop reuse/folding generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop shared-buffer witness; no current Pluto/OpenScop inter-array reuse pass observed",
        "acceptance_reason": "arrays share a buffer only across disjoint lifetime intervals with compatible storage",
    },
    "array_expansion_versioning": {
        "survey_group": "versioning",
        "external_evidence": "toy OpenScop advanced-storage generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop version-selection witness; no current Pluto/OpenScop versioning pass observed",
        "acceptance_reason": "reads select produced versions and final copy-out selects the source-final version",
    },
    "overlapped_tiling": {
        "survey_group": "overlap_halo",
        "external_evidence": "toy OpenScop advanced-storage generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop duplicate/commit witness; related to overlapped/diamond tiling but not Pluto-backed here",
        "acceptance_reason": "extra computations are private; commit instances exactly cover public live-outs",
    },
    "reduction_privatization": {
        "survey_group": "reduction",
        "external_evidence": "toy OpenScop advanced-storage generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop reduction-merge witness; no current Pluto/OpenScop reduction privatization pass observed",
        "acceptance_reason": "private accumulators cover source contributions and merge under checked algebraic laws",
    },
    "double_buffering": {
        "survey_group": "versioning",
        "external_evidence": "toy OpenScop reuse/folding generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop phase-projection witness; no current Pluto/OpenScop double-buffering pass observed",
        "acceptance_reason": "phase projection identifies the current physical buffer and final projection covers public live-outs",
    },
    "storage_view_composition": {
        "survey_group": "composition",
        "external_evidence": "toy OpenScop advanced-storage generator, standalone",
        "tool_backed": True,
        "artifact_status": "toy OpenScop view-composition witness",
        "acceptance_reason": "target-mid and mid-source public views agree on intermediate observables and compose",
    },
}


WITNESS_FIELDS = {
    "source_no_alias_abstraction": [
        "source variable footprints",
        "non-overlap proof for distinct variables",
        "in-bounds source accesses",
    ],
    "contextual_frame_preservation": [
        "allowed write set",
        "protected frame variables",
        "pre/post frame snapshots",
    ],
    "affine_interchange": [
        "instance bijection",
        "legal schedule order",
        "unchanged storage accesses",
    ],
    "index_set_splitting": [
        "source domain",
        "target subdomains",
        "disjoint exact-cover proof",
    ],
    "ordinary_tiling": [
        "tile projection",
        "exact domain cover",
        "unchanged storage accesses",
    ],
    "scalar_privatization_expansion": [
        "logical temporary live range",
        "fresh private cell per instance",
        "write-before-read evidence",
        "optional live-out copy",
    ],
    "private_copy_boundary": [
        "copy-in map",
        "copy-out map",
        "private live-in/live-out sets",
        "unique public commits",
    ],
    "private_access_local_instantiation": [
        "symbolic private access",
        "instantiated target private cell",
        "hidden/private declaration",
        "in-bounds proof",
    ],
    "layout_remap_padding": [
        "logical public index",
        "physical layout map",
        "injectivity over live logical cells",
        "padding exclusion from public view",
    ],
    "scratchpad_packing": [
        "tile footprint",
        "public-to-local copy map",
        "local buffer shape",
        "local read coverage",
    ],
    "scratchpad_copy_out": [
        "updated local cells",
        "copy-out commit map",
        "public live-out set",
        "unique commit proof",
    ],
    "scalar_promotion": [
        "entry load event",
        "private scalar interval",
        "alias/clobber exclusion",
        "exit store-back event",
    ],
    "array_contraction": [
        "logical value ids",
        "physical reuse map",
        "valid intervals",
        "producer/consumer events",
        "kill or reuse events",
        "boundary projection",
    ],
    "inter_array_reuse": [
        "logical arrays sharing one region",
        "disjoint lifetime intervals",
        "physical region compatibility",
        "copy-out before reuse",
    ],
    "array_expansion_versioning": [
        "definition-to-version map",
        "read version selectors",
        "produced-version proof",
        "final version selector",
    ],
    "overlapped_tiling": [
        "source-to-target duplicate projection",
        "halo closure",
        "commit set",
        "exact cover of public live-outs",
    ],
    "reduction_privatization": [
        "chunk partition",
        "private accumulator initialization",
        "contribution coverage",
        "merge tree",
        "operator laws",
    ],
    "double_buffering": [
        "phase projection",
        "current/next buffer map",
        "swap transition proof",
        "final boundary projection",
    ],
    "storage_view_composition": [
        "source-to-mid public view",
        "mid-to-target public view",
        "compatible intermediate interface",
        "composed output view equality",
    ],
}


def main() -> int:
    parser = argparse.ArgumentParser(description="Build storage transformation manifest.")
    parser.add_argument("--positive", type=Path, default=Path("storage/evidence/standalone_positive.log"))
    parser.add_argument("--negative", type=Path, default=Path("storage/evidence/standalone_negative.log"))
    parser.add_argument("--examples", type=Path, default=Path("storage/examples/standalone"))
    parser.add_argument("--format", choices=["json", "markdown"], default="json")
    args = parser.parse_args()

    positives = parse_positive(args.positive)
    negatives = parse_negative(args.negative)
    neg_by_case: dict[str, list[dict[str, str]]] = {}
    for neg in negatives:
        neg_by_case.setdefault(neg.case, []).append({"name": neg.name, "reason": neg.reason})

    entries = []
    for case in positives:
        source = args.examples / f"{case.name}.source.c"
        target = args.examples / f"{case.name}.target.c"
        extra = HAND_CLASSIFICATION.get(case.name, {})
        entries.append(
            {
                "name": case.name,
                "classification": case.classification,
                "survey_group": extra.get("survey_group", "uncategorized"),
                "source_example": str(source) if source.exists() else None,
                "target_example": str(target) if target.exists() else None,
                "obligations": case.obligations,
                "negative_checks": neg_by_case.get(case.name, []),
                "external_evidence": extra.get("external_evidence", "unknown"),
                "tool_backed": extra.get("tool_backed", False),
                "artifact_status": extra.get("artifact_status", "unknown"),
                "acceptance_reason": extra.get("acceptance_reason", ""),
                "witness_fields": WITNESS_FIELDS.get(case.name, []),
            }
        )

    if args.format == "json":
        print(json.dumps({"entries": entries}, indent=2, sort_keys=True))
        return 0

    print("# Storage Transformation Manifest")
    print()
    print("| Case | Group | Tool-backed | Examples | Obligations | Negatives | Evidence status |")
    print("|---|---|---|---|---:|---:|---|")
    for entry in entries:
        examples = "yes" if entry["source_example"] and entry["target_example"] else "missing"
        print(
            f"| `{entry['name']}` | {entry['survey_group']} | "
            f"{'yes' if entry['tool_backed'] else 'no'} | {examples} | "
            f"{len(entry['obligations'])} | {len(entry['negative_checks'])} | "
            f"{entry['artifact_status']} |"
        )
    print()
    print("## Acceptance Reasons")
    print()
    for entry in entries:
        print(f"### `{entry['name']}`")
        print()
        print(entry["acceptance_reason"] or "TODO")
        print()

    print("## Required Witness Fields")
    print()
    for entry in entries:
        print(f"### `{entry['name']}`")
        print()
        fields = entry["witness_fields"]
        if not fields:
            print("TODO")
        else:
            for field in fields:
                print(f"- {field}")
        print()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
