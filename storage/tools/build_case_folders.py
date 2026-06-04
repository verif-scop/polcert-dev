#!/usr/bin/env python3
"""Materialize per-transformation storage validation cases.

The output is intentionally simple: every transformation has a subdirectory
with positive and negative line-oriented certificates.  A registry file records
the generic witness requirements consumed by the OCaml validator.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
from pathlib import Path


GROUP_ROLES = {
    "precondition": ["source_footprint", "no_alias", "in_bounds"],
    "context": ["allowed_write_set", "protected_frame", "frame_snapshot"],
    "schedule_only": ["instance_bijection", "schedule_legality", "storage_access_identity"],
    "schedule_domain": ["domain_cover", "domain_disjointness", "storage_access_identity"],
    "storage_expansion": ["fresh_private_cell", "live_range", "def_use_dominance"],
    "private_boundary": ["copy_in", "private_live_set", "copy_out", "unique_public_commit"],
    "private_access": ["symbolic_private_access", "private_cell_instantiation", "hidden_storage", "bounds_check"],
    "layout": ["logical_to_physical_map", "injective_live_cells", "padding_erasure", "public_view_projection"],
    "scratchpad": ["tile_footprint", "copy_boundary", "local_buffer_shape", "public_commit_or_read_cover"],
    "promotion": ["entry_load", "private_scalar_interval", "alias_clobber_exclusion", "exit_store_back"],
    "reuse_folding": ["logical_value_id", "physical_reuse_map", "live_interval", "producer_consumer", "boundary_projection"],
    "versioning": ["version_selector", "phase_projection", "buffer_role", "final_projection"],
    "overlap_halo": ["duplicate_projection", "halo_closure", "commit_set", "exact_public_cover"],
    "reduction": ["chunk_partition", "accumulator_init", "contribution_cover", "merge_tree", "operator_laws"],
    "composition": ["source_mid_view", "mid_target_view", "interface_compatibility", "composed_public_view"],
}

GROUP_SEMANTICS = {
    "precondition": ["public_output_eq"],
    "context": ["public_output_eq", "frame_preserved"],
    "schedule_only": ["public_output_eq", "domain_exact_cover", "access_identity"],
    "schedule_domain": ["public_output_eq", "domain_exact_cover", "access_identity"],
    "storage_expansion": ["public_output_eq", "unique_commit"],
    "private_boundary": ["public_output_eq", "unique_commit"],
    "private_access": ["public_output_eq"],
    "layout": ["public_output_eq"],
    "scratchpad": ["public_output_eq", "unique_commit"],
    "promotion": ["public_output_eq", "unique_commit"],
    "reuse_folding": ["public_output_eq", "live_interval_nonoverlap"],
    "versioning": ["public_output_eq", "live_interval_nonoverlap"],
    "overlap_halo": ["public_output_eq", "domain_exact_cover", "unique_commit"],
    "reduction": ["public_output_eq", "unique_commit", "reduction_laws"],
    "composition": ["public_output_eq", "view_composition_bridge"],
}


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def slug(text: str) -> str:
    text = text.lower()
    text = re.sub(r"[^a-z0-9]+", "_", text)
    return text.strip("_") or "case"


def witness_kind(case_name: str) -> str:
    return "".join(part.capitalize() for part in case_name.split("_"))


def extract_public_vars(path: Path | None) -> list[str]:
    if path is None or not path.exists():
        return ["OUT"]
    text = path.read_text(encoding="utf-8")
    candidates = re.findall(r"\b[A-Z][A-Za-z0-9_]*\b", text)
    ignored = {"N", "M", "T", "K"}
    vars_seen: list[str] = []
    for item in candidates:
        if item in ignored or item in vars_seen:
            continue
        vars_seen.append(item)
    return vars_seen or ["OUT"]


def emit_lines(path: Path, lines: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def semantic_pairs(entry: dict, manifest: dict, bad: str | None = None) -> list[tuple[str, str]]:
    group = manifest.get("survey_group", "unknown")
    source = entry.get("source_example")
    target = entry.get("target_example")
    source_public_vars = extract_public_vars(Path(source) if source else None)
    target_storage_vars = extract_public_vars(Path(target) if target else None)
    public_vars = source_public_vars or target_storage_vars
    representation_vars = [var for var in target_storage_vars if var not in public_vars]
    pairs: list[tuple[str, str]] = []

    for idx, var in enumerate(public_vars):
        cell = f"{var}[0]"
        value = f"v{idx}"
        target_value = "bad" if bad == "public_output_mismatch" and idx == 0 else value
        pairs.append(("public_cell", cell))
        pairs.append(("source_final", f"{cell}={value}"))
        if idx == 0 and representation_vars:
            repr_cell = f"{representation_vars[0]}[0]"
            pairs.append(("representation", f"{repr_cell}->{cell}"))
            pairs.append(("target_repr_final", f"{repr_cell}={target_value}"))
        else:
            pairs.append(("target_final", f"{cell}={target_value}"))

    pairs.extend([("source_instance", "S0"), ("source_instance", "S1")])
    if bad == "domain_miss":
        pairs.append(("target_instance", "S0"))
    else:
        pairs.extend([("target_instance", "S0"), ("target_instance", "S1")])

    access_cell = f"{public_vars[0]}[0]" if public_vars else "OUT[0]"
    pairs.append(("source_access", access_cell))
    pairs.append(("target_access", "BAD[0]" if bad == "access_mismatch" else access_cell))

    if group in {"storage_expansion", "private_boundary", "scratchpad", "promotion", "overlap_halo", "reduction"}:
        pairs.append(("commit", access_cell))
        if bad == "duplicate_commit":
            pairs.append(("commit", access_cell))

    if group in {"reuse_folding", "versioning"}:
        pairs.append(("live_interval", "logical0@Buf[0]:0..2" if bad == "live_overlap" else "logical0@Buf[0]:0..1"))
        if bad == "live_overlap":
            pairs.append(("live_interval", "logical1@Buf[0]:1..3"))
        else:
            pairs.append(("live_interval", "logical1@Buf[0]:2..3"))

    if group == "reduction":
        pairs.append(("operator_law", "associative"))
        if bad != "missing_reduction_law":
            pairs.append(("operator_law", "identity"))

    if group == "composition":
        value = "bad" if bad == "bad_composition_bridge" else "v0"
        pairs.append(("source_mid_final", f"{access_cell}=v0"))
        pairs.append(("mid_target_final", f"{access_cell}={value}"))

    if group == "context":
        pairs.append(("frame_before", "F[0]=vframe"))
        pairs.append(("frame_after", "F[0]=bad" if bad == "frame_mismatch" else "F[0]=vframe"))

    return pairs


def cert_lines(
    *,
    entry: dict,
    manifest: dict,
    case_dir: Path,
    variant: dict | None,
    expectation: str,
    omitted: tuple[str, str | None] | None = None,
    semantic_bad: str | None = None,
    negative_case: str | None = None,
    negative_reason: str | None = None,
) -> list[str]:
    case_name = entry["name"]
    group = manifest.get("survey_group", "unknown")
    kind = witness_kind(case_name)
    source = entry.get("source_example")
    target = entry.get("target_example")
    source_path = Path(source) if source else None
    target_path = Path(target) if target else None
    source_public_vars = extract_public_vars(source_path)
    target_storage_vars = extract_public_vars(target_path)
    public_vars = source_public_vars or target_storage_vars
    representation_vars = [var for var in target_storage_vars if var not in public_vars]
    roles = GROUP_ROLES.get(group, ["generic_storage_witness"])

    pairs: list[tuple[str, str]] = [
        ("expect", expectation),
        ("case", case_name),
        ("survey_group", group),
        ("classification", entry.get("classification", "unknown")),
        ("witness_kind", kind),
        ("view_relation", "public_output_view_eq"),
        ("source_example", source or "missing"),
        ("target_example", target or "missing"),
        ("evidence", entry.get("evidence_status", "unknown")),
        ("correctness_reason", manifest.get("acceptance_reason", "source and target agree under the declared public output view")),
    ]
    if variant is None:
        pairs.extend(
            [
                ("example", "source_target_core"),
                ("source_shape", "canonical source file"),
                ("target_shape", "canonical target file"),
                ("purpose", "baseline source/target witness for this transformation"),
            ]
        )
    else:
        pairs.extend(
            [
                ("example", slug(variant["name"])),
                ("source_shape", variant["source"]),
                ("target_shape", variant["target"]),
                ("purpose", variant["purpose"]),
            ]
        )
    for var in public_vars:
        pairs.append(("source_public_var", var))
        pairs.append(("target_public_var", var))
        pairs.append(("public_output_var", var))
    for var in representation_vars:
        pairs.append(("target_representation_var", var))
    for field in entry.get("witness_fields", []):
        pairs.append(("witness_field", field))
    for role in roles:
        pairs.append(("role", role))
    for obligation in entry.get("obligations", []):
        pairs.append(("obligation", obligation))
    pairs.extend(semantic_pairs(entry, manifest, semantic_bad))
    if negative_case:
        pairs.append(("negative_case", negative_case))
    if negative_reason:
        pairs.append(("negative_reason", negative_reason))

    if omitted is not None:
        omit_key, omit_value = omitted
        pairs = [(key, value) for key, value in pairs if not (key == omit_key and (omit_value is None or value == omit_value))]

    rel_case_dir = case_dir.relative_to(case_dir.parents[1])
    lines = [
        "# Generated storage transformation certificate.",
        f"# Directory: {rel_case_dir}",
    ]
    lines.extend(f"{key}: {value}" for key, value in pairs)
    return lines


def registry_lines(entries: list[dict], manifest_by_name: dict[str, dict]) -> list[str]:
    lines = [
        "# Generated storage validation registry.",
        "# The OCaml validator treats each required item uniformly.",
        "",
    ]
    for entry in entries:
        case_name = entry["name"]
        manifest = manifest_by_name.get(case_name, {})
        group = manifest.get("survey_group", "unknown")
        lines.extend(
            [
                f"case: {case_name}",
                f"group: {group}",
                f"witness_kind: {witness_kind(case_name)}",
                "required: view_relation=public_output_view_eq",
                "required: source_public_var",
                "required: target_public_var",
                "required: public_output_var",
                f"required: witness_kind={witness_kind(case_name)}",
            ]
        )
        for field in entry.get("witness_fields", []):
            lines.append(f"required: witness_field={field}")
        for role in GROUP_ROLES.get(group, ["generic_storage_witness"]):
            lines.append(f"required: role={role}")
        for semantic in GROUP_SEMANTICS.get(group, ["public_output_eq"]):
            lines.append(f"semantic: {semantic}")
        lines.extend(["---", ""])
    return lines


def readme_lines(entry: dict, manifest: dict, positives: int, negatives: int) -> list[str]:
    lines = [
        f"# {entry['name']}",
        "",
        f"Classification: {entry.get('classification', 'unknown')}",
        "",
        f"Correctness reason: {manifest.get('acceptance_reason', 'source and target agree under the declared public output view')}",
        "",
        "The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.",
        "",
        "## Required Witness Fields",
        "",
    ]
    for field in entry.get("witness_fields", []):
        lines.append(f"- {field}")
    lines.extend(["", "## Required Roles", ""])
    for role in GROUP_ROLES.get(manifest.get("survey_group", "unknown"), ["generic_storage_witness"]):
        lines.append(f"- {role}")
    lines.extend(
        [
            "",
            "## Examples",
            "",
            f"- positive certificates: {positives}",
            f"- negative certificates: {negatives}",
            f"- source file: `{entry.get('source_example') or 'missing'}`",
            f"- target file: `{entry.get('target_example') or 'missing'}`",
            "",
            "Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.",
            "",
        ]
    )
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(description="Build per-transformation case folders.")
    parser.add_argument("--catalog", type=Path, default=Path("EXAMPLE_CATALOG.json"))
    parser.add_argument("--manifest", type=Path, default=Path("MANIFEST.json"))
    parser.add_argument("--out-dir", type=Path, default=Path("cases"))
    args = parser.parse_args()

    catalog = load_json(args.catalog)
    manifest_obj = load_json(args.manifest)
    entries = catalog["entries"]
    manifest_by_name = {entry["name"]: entry for entry in manifest_obj["entries"]}

    if args.out_dir.exists():
        shutil.rmtree(args.out_dir)
    args.out_dir.mkdir(parents=True)

    emit_lines(args.out_dir / "registry.txt", registry_lines(entries, manifest_by_name))

    summary = [
        "# Storage Validation Case Corpus",
        "",
        "Generated by `tools/build_case_folders.py` from `EXAMPLE_CATALOG.json` and `MANIFEST.json`.",
        "",
        "Each subdirectory contains positive and negative certificates for one transformation.  Public variables are source-level logical variables; target-only storage names are representation variables and are not observable outputs.",
        "",
        "| Case | Group | Positives | Negatives | Correctness reason |",
        "|---|---|---:|---:|---|",
    ]

    for entry in entries:
        case_name = entry["name"]
        manifest = manifest_by_name.get(case_name, {})
        case_dir = args.out_dir / case_name

        positive_specs: list[tuple[str, dict | None]] = [("core", None)]
        for idx, variant in enumerate(entry.get("variants", []), start=1):
            positive_specs.append((f"variant_{idx:02d}_{slug(variant['name'])}", variant))
        for filename, variant in positive_specs:
            emit_lines(
                case_dir / "positive" / f"{filename}.cert",
                cert_lines(entry=entry, manifest=manifest, case_dir=case_dir, variant=variant, expectation="pass"),
            )

        negative_count = 0
        missing_requirements: list[tuple[str, str | None, str, str]] = [
            ("view_relation", "public_output_view_eq", "missing_public_view_relation", "public output view relation is absent"),
            ("source_public_var", None, "missing_source_public_var", "source public variables are absent"),
            ("target_public_var", None, "missing_target_public_var", "target public variables are absent"),
            ("public_output_var", None, "missing_public_output_var", "final public outputs are absent"),
            ("witness_kind", witness_kind(case_name), "wrong_or_missing_witness_kind", "witness kind does not match the registry"),
        ]
        for field in entry.get("witness_fields", []):
            missing_requirements.append(("witness_field", field, f"missing_witness_{slug(field)}", f"required witness field is absent: {field}"))
        for role in GROUP_ROLES.get(manifest.get("survey_group", "unknown"), ["generic_storage_witness"]):
            missing_requirements.append(("role", role, f"missing_role_{slug(role)}", f"required protocol role is absent: {role}"))

        for key, value, name, reason in missing_requirements:
            negative_count += 1
            emit_lines(
                case_dir / "negative" / f"{negative_count:03d}_{name}.cert",
                cert_lines(
                    entry=entry,
                    manifest=manifest,
                    case_dir=case_dir,
                    variant=None,
                    expectation="fail",
                    omitted=(key, value),
                    negative_case=name,
                    negative_reason=reason,
                ),
            )

        semantic_negative_specs: list[tuple[str, str, str]] = [
            ("public_output_mismatch", "semantic_public_output_mismatch", "target observable value disagrees with source final value"),
        ]
        group = manifest.get("survey_group", "unknown")
        if group in {"schedule_only", "schedule_domain", "overlap_halo"}:
            semantic_negative_specs.append(("domain_miss", "semantic_domain_miss", "target instances do not exactly cover source instances"))
        if group in {"schedule_only", "schedule_domain"}:
            semantic_negative_specs.append(("access_mismatch", "semantic_access_mismatch", "target storage access differs while claiming storage identity"))
        if group in {"storage_expansion", "private_boundary", "scratchpad", "promotion", "overlap_halo", "reduction"}:
            semantic_negative_specs.append(("duplicate_commit", "semantic_duplicate_commit", "a public cell is committed more than once"))
        if group in {"reuse_folding", "versioning"}:
            semantic_negative_specs.append(("live_overlap", "semantic_live_overlap", "two logical values overlap on the same physical cell"))
        if group == "reduction":
            semantic_negative_specs.append(("missing_reduction_law", "semantic_missing_reduction_law", "required reduction algebraic law is absent"))
        if group == "composition":
            semantic_negative_specs.append(("bad_composition_bridge", "semantic_bad_composition_bridge", "source-mid and mid-target views disagree"))
        if group == "context":
            semantic_negative_specs.append(("frame_mismatch", "semantic_frame_mismatch", "protected frame snapshot changes"))

        for bad, name, reason in semantic_negative_specs:
            negative_count += 1
            emit_lines(
                case_dir / "negative" / f"{negative_count:03d}_{name}.cert",
                cert_lines(
                    entry=entry,
                    manifest=manifest,
                    case_dir=case_dir,
                    variant=None,
                    expectation="fail",
                    semantic_bad=bad,
                    negative_case=name,
                    negative_reason=reason,
                ),
            )

        for neg in entry.get("negative_checks", []):
            role = GROUP_ROLES.get(manifest.get("survey_group", "unknown"), ["generic_storage_witness"])[0]
            negative_count += 1
            emit_lines(
                case_dir / "negative" / f"{negative_count:03d}_{slug(neg['name'])}.cert",
                cert_lines(
                    entry=entry,
                    manifest=manifest,
                    case_dir=case_dir,
                    variant=None,
                    expectation="fail",
                    omitted=("role", role),
                    negative_case=neg["name"],
                    negative_reason=neg["reason"],
                ),
            )
        for neg in entry.get("supplemental_negative_cases", []):
            role = GROUP_ROLES.get(manifest.get("survey_group", "unknown"), ["generic_storage_witness"])[-1]
            negative_count += 1
            emit_lines(
                case_dir / "negative" / f"{negative_count:03d}_{slug(neg)}.cert",
                cert_lines(
                    entry=entry,
                    manifest=manifest,
                    case_dir=case_dir,
                    variant=None,
                    expectation="fail",
                    omitted=("role", role),
                    negative_case=slug(neg),
                    negative_reason=neg,
                ),
            )

        emit_lines(case_dir / "README.md", readme_lines(entry, manifest, len(positive_specs), negative_count))
        reason = manifest.get("acceptance_reason", "source and target agree under the declared public output view").replace("|", "/")
        summary.append(
            f"| `{case_name}` | `{manifest.get('survey_group', 'unknown')}` | "
            f"{len(positive_specs)} | {negative_count} | {reason} |"
        )

    emit_lines(args.out_dir / "SUMMARY.md", summary)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
