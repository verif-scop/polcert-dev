#!/usr/bin/env python3
"""Build a comprehensive example catalog for storage transformations."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from build_manifest import HAND_CLASSIFICATION, WITNESS_FIELDS
from summarize_standalone import parse_negative, parse_positive


EXAMPLE_VARIANTS = {
    "source_no_alias_abstraction": [
        {
            "name": "distinct arrays",
            "source": "C[i] = A[i] + B[i]",
            "target": "same storage accesses under distinct logical blocks A, B, C",
            "purpose": "establishes variable-footprint reasoning before any storage rewrite",
        },
        {
            "name": "unknown object rejected",
            "source": "C[i] = P[i]",
            "target": "no declared footprint for P",
            "purpose": "shows why public vars need declared shapes/footprints",
        },
    ],
    "contextual_frame_preservation": [
        {
            "name": "protected frame",
            "source": "B[i] = A[i] + 1; F[j] unchanged",
            "target": "rewrites B only; F is protected frame",
            "purpose": "fragment-local storage changes cannot alter context-owned vars",
        },
        {
            "name": "forbidden context write",
            "source": "F[j] is outside the fragment write set",
            "target": "target writes F[j]",
            "purpose": "negative shape for frame preservation",
        },
    ],
    "affine_interchange": [
        {
            "name": "loop interchange",
            "source": "for i for j S(i,j)",
            "target": "for j for i S(i,j)",
            "purpose": "schedule-only baseline with identical storage accesses",
        },
        {
            "name": "dependence-blocked interchange",
            "source": "A[i][j] = A[i][j-1] + 1",
            "target": "interchange would reverse dependence",
            "purpose": "why schedule legality is still required",
        },
    ],
    "index_set_splitting": [
        {
            "name": "even/odd split",
            "source": "for i in [0,N) S(i)",
            "target": "for even i S(i); for odd i S(i)",
            "purpose": "domain partition without storage rewrite",
        },
        {
            "name": "prefix/suffix split",
            "source": "for i in [0,N) S(i)",
            "target": "for i < K S(i); for K <= i < N S(i)",
            "purpose": "exact-cover obligation independent of schedule shape",
        },
    ],
    "ordinary_tiling": [
        {
            "name": "strip-mined tile",
            "source": "for i in [0,N) S(i)",
            "target": "for ii step T for i in tile(ii) S(i)",
            "purpose": "storage-preserving grouped schedule",
        },
        {
            "name": "rectangular 2D tile",
            "source": "for i for j S(i,j)",
            "target": "for ii,jj tiles; for i,j inside tile S(i,j)",
            "purpose": "tile projection and exact cover in multiple dimensions",
        },
    ],
    "scalar_privatization_expansion": [
        {
            "name": "per-iteration scalar expansion",
            "source": "tmp = A[i] + 1; B[i] = tmp * 2",
            "target": "tmp_exp[i] = A[i] + 1; B[i] = tmp_exp[i] * 2",
            "purpose": "fresh private cell per live temporary",
        },
        {
            "name": "read-before-fill rejected",
            "source": "B[i] reads tmp after source write",
            "target": "B[i] reads tmp_exp[i] before target fill",
            "purpose": "dominance/use-def obligation",
        },
    ],
    "private_copy_boundary": [
        {
            "name": "copy-in and copy-out",
            "source": "A tile is read and updated",
            "target": "local tile gets copy-in, local updates, then copy-out",
            "purpose": "boundary protocol for private storage",
        },
        {
            "name": "live-out missing",
            "source": "updated public A tile is observable",
            "target": "local tile is updated but never committed",
            "purpose": "why final public view needs copy-out coverage",
        },
    ],
    "private_access_local_instantiation": [
        {
            "name": "symbolic private access",
            "source": "logical private temp at instance i",
            "target": "private_cell[f(i)] read/write after instantiation",
            "purpose": "finite domains instantiate symbolic private storage",
        },
        {
            "name": "out-of-bounds instantiation",
            "source": "private access declared over tile bounds",
            "target": "f(i) exceeds private array extent",
            "purpose": "bounds are part of the certificate",
        },
    ],
    "layout_remap_padding": [
        {
            "name": "padding scale",
            "source": "A[i]",
            "target": "A_pad[2*i]",
            "purpose": "logical public A represented by different physical layout",
        },
        {
            "name": "transpose/permutation",
            "source": "A[i][j]",
            "target": "A_t[j][i]",
            "purpose": "same logical array through index permutation",
        },
        {
            "name": "linearized affine layout",
            "source": "A[i][j]",
            "target": "A_lin[i*M + j]",
            "purpose": "affine layout witness, not raw variable equality",
        },
    ],
    "scratchpad_packing": [
        {
            "name": "live-in cache",
            "source": "C[kk+k] = A[kk+k] + B[kk+k]",
            "target": "Bp[k] = B[kk+k]; C[kk+k] = A[kk+k] + Bp[k]",
            "purpose": "copy-in covers local reads; Bp is private",
        },
        {
            "name": "partial tile guard",
            "source": "N may not be divisible by T",
            "target": "copy/compute guarded by kk+k < N",
            "purpose": "boundary tiles must be checked, not assumed",
        },
    ],
    "scratchpad_copy_out": [
        {
            "name": "local update then commit",
            "source": "A[i] = A[i] + 1",
            "target": "Al[k] = A[kk+k]; Al[k]++; A[kk+k] = Al[k]",
            "purpose": "copy-out is the public commit",
        },
        {
            "name": "duplicate commit rejected",
            "source": "one logical A[i] live-out",
            "target": "two copy-out events write A[i]",
            "purpose": "commit uniqueness or deterministic resolution",
        },
    ],
    "scalar_promotion": [
        {
            "name": "single-cell scalar cache",
            "source": "A[i] = A[i] + 1",
            "target": "s = A[i]; s = s + 1; A[i] = s",
            "purpose": "load/update/store-back protocol",
        },
        {
            "name": "missing store-back rejected",
            "source": "updated A[i] is public",
            "target": "s is updated but A[i] is not stored",
            "purpose": "private scalar cannot satisfy final public view",
        },
    ],
    "array_contraction": [
        {
            "name": "rolling time buffer",
            "source": "A[t][i] = A[t-1][i] + 1",
            "target": "A2[t mod 2][i] = A2[(t-1) mod 2][i] + 1",
            "purpose": "non-injective physical map with disjoint live intervals",
        },
        {
            "name": "wrong modulo rejected",
            "source": "A[t] and A[t-1] simultaneously live",
            "target": "one-slot A1[0][i] reuses too early",
            "purpose": "reuse-before-last-consumer is unsound",
        },
    ],
    "inter_array_reuse": [
        {
            "name": "two temporaries share buffer",
            "source": "T1 produces C, then T2 produces D",
            "target": "Buf represents T1 in phase 1 and T2 in phase 2",
            "purpose": "cross-array reuse under disjoint lifetimes",
        },
        {
            "name": "overlapping lifetimes rejected",
            "source": "T1 is read after T2 is produced",
            "target": "T2 overwrites Buf before T1's last read",
            "purpose": "valid intervals must not overlap",
        },
    ],
    "array_expansion_versioning": [
        {
            "name": "per-time version array",
            "source": "X overwritten each t; Y[t][i] reads current X[i]",
            "target": "X_exp[t][i] stores each version; final X copied from X_exp[T-1]",
            "purpose": "reads select produced versions and final selector commits",
        },
        {
            "name": "old version selected rejected",
            "source": "final X is last write",
            "target": "copy-out selects X_exp[T-2]",
            "purpose": "final public output needs source-final version",
        },
    ],
    "overlapped_tiling": [
        {
            "name": "halo recomputation",
            "source": "B[i] depends on neighbors",
            "target": "each tile recomputes halo privately and commits owned interior",
            "purpose": "extra computations hidden; commit set exact cover",
        },
        {
            "name": "duplicate public commit rejected",
            "source": "one public B[i] output",
            "target": "two overlapped tiles commit B[i]",
            "purpose": "halo duplicates must not escape",
        },
    ],
    "reduction_privatization": [
        {
            "name": "chunked sum",
            "source": "sum += A[i]",
            "target": "priv[c] reduces chunk c; sum = merge(priv)",
            "purpose": "private accumulators plus algebraic merge",
        },
        {
            "name": "non-associative operator rejected",
            "source": "left-fold subtraction",
            "target": "chunked/reordered merge",
            "purpose": "operator laws are required evidence",
        },
    ],
    "double_buffering": [
        {
            "name": "cur/next ping-pong",
            "source": "A[t][i] = step(A[t-1][i])",
            "target": "next[i] = step(cur[i]); swap(cur,next)",
            "purpose": "phase projection and final selector",
        },
        {
            "name": "read/write role swapped rejected",
            "source": "read old state, write new state",
            "target": "reads next or writes cur in the same phase",
            "purpose": "phase role obligations cannot be inferred from final equality",
        },
    ],
    "storage_view_composition": [
        {
            "name": "layout then private erasure",
            "source": "logical A",
            "target": "padded physical A_pad plus private temps",
            "purpose": "compose layout projection with private-storage erasure",
        },
        {
            "name": "bad intermediate rejected",
            "source": "logical A contents",
            "target": "target and mid disagree on observable cells",
            "purpose": "view composition needs compatible intermediate observables",
        },
    ],
}


SUFFICIENCY_RULES = [
    "has a source/target example file",
    "has at least two example variants in the catalog",
    "has positive standalone obligations",
    "has negative malformed-witness checks or supplemental protocol negative cases, unless it is explicitly schedule-only",
    "states required witness fields",
    "states whether evidence is real external tooling, in-repo toy OpenScop, or standalone-only",
]


SUPPLEMENTAL_NEGATIVE_CASES = {
    "scalar_promotion": [
        "missing load",
        "scalar read before load",
        "missing store-back",
        "intervening alias write clobbers promoted A[i]",
        "unknown call may clobber promoted A[i]",
        "public use reads stale A[i] instead of scalar",
        "store-back targets wrong public index",
        "two logical cells share one scalar over overlapping intervals",
        "promoted scalar escapes as public output",
    ],
    "index_set_splitting": [
        "target subdomains overlap",
        "target subdomains miss a source instance",
        "target changes storage access while claiming pure split",
    ],
}


def main() -> int:
    parser = argparse.ArgumentParser(description="Build storage example catalog.")
    parser.add_argument("--positive", type=Path, default=Path("evidence/standalone_positive.log"))
    parser.add_argument("--negative", type=Path, default=Path("evidence/standalone_negative.log"))
    parser.add_argument("--examples", type=Path, default=Path("examples/standalone"))
    parser.add_argument("--format", choices=["markdown", "json"], default="markdown")
    args = parser.parse_args()

    positives = parse_positive(args.positive)
    negatives = parse_negative(args.negative)
    neg_by_case: dict[str, list[dict[str, str]]] = {}
    for neg in negatives:
        neg_by_case.setdefault(neg.case, []).append({"name": neg.name, "reason": neg.reason})

    entries = []
    gaps = []
    for case in positives:
        source = args.examples / f"{case.name}.source.c"
        target = args.examples / f"{case.name}.target.c"
        variants = EXAMPLE_VARIANTS.get(case.name, [])
        hand = HAND_CLASSIFICATION.get(case.name, {})
        schedule_only = hand.get("survey_group") in {"schedule_only", "schedule_domain"}
        supplemental_negatives = SUPPLEMENTAL_NEGATIVE_CASES.get(case.name, [])
        total_negative_count = len(neg_by_case.get(case.name, [])) + len(supplemental_negatives)
        sufficiency = {
            "source_target_files": source.exists() and target.exists(),
            "variant_count": len(variants),
            "positive_obligations": len(case.obligations),
            "negative_count": len(neg_by_case.get(case.name, [])),
            "supplemental_negative_count": len(supplemental_negatives),
            "negative_coverage_ok": total_negative_count > 0 or schedule_only,
            "witness_fields": len(WITNESS_FIELDS.get(case.name, [])),
            "evidence_status": hand.get("artifact_status", "unknown"),
        }
        case_gaps = []
        if not sufficiency["source_target_files"]:
            case_gaps.append("missing source/target example files")
        if sufficiency["variant_count"] < 2:
            case_gaps.append("needs at least two documented example variants")
        if not sufficiency["negative_coverage_ok"]:
            case_gaps.append("needs malformed-witness negative checks")
        elif not schedule_only and total_negative_count < 2:
            case_gaps.append("negative coverage is thin")
        if sufficiency["witness_fields"] == 0:
            case_gaps.append("missing required witness fields")
        if "needs stronger" in sufficiency["evidence_status"]:
            case_gaps.append(sufficiency["evidence_status"])
        if "standalone negatives still thin" in sufficiency["evidence_status"] and not supplemental_negatives:
            case_gaps.append(sufficiency["evidence_status"])
        if "toy-only" in sufficiency["evidence_status"] and "schedule" not in hand.get("survey_group", ""):
            case_gaps.append("no OpenScop-shaped or external-tool evidence yet")
        if case_gaps:
            gaps.append({"case": case.name, "gaps": case_gaps})
        entries.append(
            {
                "name": case.name,
                "classification": case.classification,
                "source_example": str(source) if source.exists() else None,
                "target_example": str(target) if target.exists() else None,
                "variants": variants,
                "obligations": case.obligations,
                "negative_checks": neg_by_case.get(case.name, []),
                "supplemental_negative_cases": supplemental_negatives,
                "witness_fields": WITNESS_FIELDS.get(case.name, []),
                "evidence_status": hand.get("artifact_status", "unknown"),
                "external_evidence": hand.get("external_evidence", "unknown"),
                "sufficiency": sufficiency,
                "known_gaps": case_gaps,
            }
        )

    if args.format == "json":
        print(json.dumps({"sufficiency_rules": SUFFICIENCY_RULES, "known_gaps": gaps, "entries": entries}, indent=2, sort_keys=True))
        return 0

    print("# Storage Transformation Example Catalog")
    print()
    print("This catalog is generated from standalone logs, source/target example files,")
    print("hand-classified evidence status, and per-transformation example variants.")
    print()
    print("## Sufficiency Rules")
    print()
    for rule in SUFFICIENCY_RULES:
        print(f"- {rule}")
    print()
    print("## Summary")
    print()
    print("| Case | Files | Variants | Pos obligations | Neg checks | Supplemental negs | Evidence |")
    print("|---|---|---:|---:|---:|---:|---|")
    for entry in entries:
        files = "yes" if entry["source_example"] and entry["target_example"] else "missing"
        print(
            f"| `{entry['name']}` | {files} | {len(entry['variants'])} | "
            f"{len(entry['obligations'])} | {len(entry['negative_checks'])} | "
            f"{len(entry['supplemental_negative_cases'])} | "
            f"{entry['evidence_status']} |"
        )
    print()
    print("## Known Gaps")
    print()
    if not gaps:
        print("No catalog-level example gaps detected.")
    else:
        for gap in gaps:
            print(f"### `{gap['case']}`")
            print()
            for item in gap["gaps"]:
                print(f"- {item}")
            print()
    print()
    print("## Per-Transformation Examples")
    print()
    for entry in entries:
        print(f"### `{entry['name']}`")
        print()
        print(f"Classification: {entry['classification']}")
        print()
        print("Core files:")
        print(f"- source: `{entry['source_example'] or 'missing'}`")
        print(f"- target: `{entry['target_example'] or 'missing'}`")
        print()
        print("Example variants:")
        for variant in entry["variants"]:
            print(f"- {variant['name']}: {variant['purpose']}")
            print(f"  source: `{variant['source']}`")
            print(f"  target: `{variant['target']}`")
        print()
        print("Required witness fields:")
        for field in entry["witness_fields"]:
            print(f"- {field}")
        print()
        print("Rejected malformed witnesses:")
        if entry["negative_checks"]:
            for neg in entry["negative_checks"]:
                print(f"- `{neg['name']}`: {neg['reason']}")
        else:
            print("- none in standalone log; schedule-only/domain cases still need schedule legality tests elsewhere")
        if entry["supplemental_negative_cases"]:
            print()
            print("Supplemental protocol negative cases:")
            for neg in entry["supplemental_negative_cases"]:
                print(f"- {neg}")
        print()
        print(f"Evidence status: {entry['evidence_status']}")
        print()

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
