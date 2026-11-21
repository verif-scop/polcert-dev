#!/usr/bin/env python3
"""Package recorded paper evidence and separate, fresh experiment entry points.

This module never invokes a compiler. Archive hashes describe the packaged,
anonymized bytes; original content hashes remain available in the archive index.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter, defaultdict
import csv
from functools import lru_cache
import gzip
import hashlib
import html
import io
import json
import lzma
import math
from pathlib import Path
import re
import statistics
import tarfile

PRIMARY = {
    "affine": ["primary-affine"],
    "rectangular_tiling": ["primary-rectangular"],
    "two_level_tiling": ["primary-two-level"],
    "diamond_tiling": ["primary-diamond", "diamond-supplement"],
    "iss": ["primary-iss", "iss-supplement"],
    "parallelization": ["standard-parallel"],
}
RETAINED = {"sampled-retained", "sampled-source-instance-retained",
            "statically-retained", "paired-partition-retained"}
LOSSES = {"not-retained", "native-failed", "native-timeout"}
TEXT_SUFFIXES = {".json", ".txt", ".scop", ".cloog", ".loop", ".c", ".py", ".md", ".sizes"}
TOOLS = ["run_paper_evaluation.py", "package_paper_evaluation.py",
         "run_paired_retention.py", "collect_retention_data.py",
         "watch_retention_resources.py", "run_fresh_retention_review.py",
         "analyze_retention_data.py", "retention_scop.py", "retention_trace.py",
         "retention_candidate.py", "retention_baseline.py", "retention_identity.py",
         "review_parallel_recollection.py", "parallel_membership_observer.py",
         "review_parallel_retention.py", "review_paired_iss.py",
         "summarize_paired_retention.py", "build_pipeline_profiler.py",
         "build_vpl_profiler.py", "collect_pipeline_timing.py",
         "collect_monotonic_timing.py", "audit_evaluation_timing.py", "collect_vpl_profile.py"]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def encode(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode()


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(encode(value))


def read_json(path):
    return json.loads(Path(path).read_text())


def distribution(values, *, nonnegative=True):
    ordered = sorted(values)
    if not ordered or any(not math.isfinite(x) or (nonnegative and x < 0) for x in ordered):
        raise ValueError("Missing, negative, or nonfinite measured seconds")
    q = (len(ordered) - 1) * .95
    low, high = math.floor(q), math.ceil(q)
    return {"count": len(ordered), "mean_seconds": statistics.mean(ordered),
            "median_seconds": statistics.median(ordered),
            "p95_seconds": ordered[low] + (ordered[high] - ordered[low]) * (q - low),
            "max_seconds": ordered[-1]}


def aggregate_retention(rows):
    """Count distinct source bytes, with a counterexample taking precedence."""
    keys = [(r["cohort"], r["id"]) for r in rows]
    if len(keys) != len(set(keys)):
        raise ValueError("Duplicate collected pair")
    result = []
    for effect, cohorts in PRIMARY.items():
        selected = [r for r in rows if r["cohort"] in cohorts]
        if not selected:
            raise ValueError("Missing main cohort: " + effect)
        by_source = defaultdict(list)
        for row in selected:
            by_source[row["source_sha256"]].append(row)
            if row["effect"] != effect:
                raise ValueError("Target effect differs from cohort")
        counts, causes, unavailable = Counter(), Counter(), Counter()
        for pairs in by_source.values():
            observed = [r for r in pairs if r["producer_status"] == "observed"
                        and r["retention_status"] != "baseline-unavailable"]
            if observed:
                counts["pluto"] += 1
                losses = [r for r in observed if r["retention_status"] in LOSSES]
                if losses:
                    counts["not_retained"] += 1
                    for cause in {r.get("classification", r["retention_status"]) for r in losses}:
                        causes[cause] += 1
                elif all(r["retention_status"] in RETAINED for r in observed):
                    counts["retained"] += 1
                else:
                    counts["requires_review"] += 1
            elif all(r["producer_status"] == "absent" for r in pairs):
                counts["no_effect"] += 1
            elif all(r["retention_status"] == "baseline-unavailable" for r in pairs):
                counts["baseline_unavailable"] += 1
                for reason in {r["baseline_status"] for r in pairs}:
                    unavailable[reason] += 1
            else:
                counts["requires_review"] += 1
        row = {"effect": effect, "cohorts": cohorts, "pairs": len(selected),
               "distinct_sources": len(by_source), **{k: counts[k] for k in
               ("pluto", "retained", "not_retained", "no_effect", "baseline_unavailable", "requires_review")},
               "loss_causes": dict(causes), "baseline_unavailable_reasons": dict(unavailable)}
        identities = {r.get("measured_compiler_sha256") for r in selected}
        if identities != {None}:
            if None in identities or len(identities) != 1:
                raise ValueError("An effect row must identify one measured compiler")
            row["measured_compiler_sha256"] = identities.pop()
        if row["pluto"] != row["retained"] + row["not_retained"] + counts["requires_review"]:
            # An unknown producer is outside the observed denominator, but must
            # still prevent a closed-table export.
            if not counts["requires_review"]:
                raise ValueError("Inconsistent effect denominator")
        result.append(row)
    return result


def merge_recollection(original, updated, old_compiler):
    rows = {(r["cohort"], r["id"]): dict(r, measured_compiler_sha256=old_compiler)
            for r in original["rows"]}
    if len(rows) != len(original["rows"]):
        raise ValueError("Duplicate original pair")
    allowed = {"primary-rectangular", "primary-two-level"}
    for cohort, gate in updated["primary"].items():
        if cohort not in allowed or not gate["collection_complete"] or not gate["all_observed_effects_reviewed"]:
            raise ValueError("Recollection gate is not closed")
    expected = {k for k in rows if k[0] in allowed}
    received = set()
    for review in updated["rows"]:
        key = review["cohort"], review["id"]
        if key not in expected or key in received:
            raise ValueError("Unexpected or duplicate recollection pair")
        received.add(key)
        old = rows[key]
        if old["source_sha256"] != review["source_sha256"]:
            raise ValueError("Recollection source differs")
        if review["retention_status"] in RETAINED:
            if review["native_returncode"] != 0 or review["native_timeout"] or review["native_resource_events"]:
                raise ValueError("Retained recollection did not complete successfully")
            transferred = review.get("eligible_for_effect_evidence_transfer")
            if transferred:
                if not review.get("complete_loop_identical") or old["retention_status"] not in RETAINED:
                    raise ValueError("Invalid complete-output evidence transfer")
            elif not review.get("fresh_effect_evidence"):
                raise ValueError("Changed final output lacks fresh effect evidence")
        rows[key] = {**old, **{k: review[k] for k in
                     ("producer_status", "baseline_status", "retention_status", "native_returncode", "native_timeout")},
                     "measured_compiler_sha256": updated["polopt_sha256"],
                     "final_sha256": review["new_stdout"]["sha256"],
                     "original_record_compiler_sha256": old_compiler,
                     "original_result_sha256": old.get("result_sha256"),
                     "result_sha256": review.get("native_result", {}).get("sha256"),
                     "evidence_scope": "Original analysis and review paths describe the original compiler. The recollection record binds the later output and any transferred or fresh effect evidence; it transfers no timing measurements.",
                     "recollection_evidence": review}
        if review["retention_status"] in RETAINED:
            rows[key].pop("classification", None)
    if received != expected:
        raise ValueError("Recollection omitted requested pairs")
    return list(rows.values())


def aggregate_timing(per_case):
    if len({r["kernel"] for r in per_case}) != len(per_case):
        raise ValueError("Duplicate timing kernel")
    wall = [{"measurement": key, "unit": "seconds", **distribution([r[key] for r in per_case],
             nonnegative=key != "additional_wall_seconds")}
            for key in ("pluto_wall_seconds", "polcert_wall_seconds", "additional_wall_seconds")]
    stages = []
    for name in ("pluto", "affine_pre_validation", "affine_post_validation", "tiling_validation",
                 "parallel_validation", "codegen", "others"):
        values = [r["stages_seconds"][name] + (r["stages_seconds"]["extraction"] if name == "others" else 0)
                  for r in per_case]
        stages.append({"stage": name, "unit": "seconds", **distribution(values)})
    return wall, stages


def validate_timing_values(observations, per_case):
    """Recompute per-kernel medians and stages from the 372+62 raw records."""
    wall = observations["wall"]
    phases = {r["kernel"]: r for r in observations["phases"]}
    if len(phases) != len(observations["phases"]):
        raise ValueError("Duplicate raw stage record")
    keys = [(r["kernel"], r["compiler"], r["repeat"]) for r in wall]
    if len(keys) != len(set(keys)):
        raise ValueError("Duplicate raw wall record")
    expected_kernels = {r["kernel"] for r in per_case}
    if set(phases) != expected_kernels or {r["kernel"] for r in wall} != expected_kernels:
        raise ValueError("Raw timing cohort differs from the per-case table")
    for expected in per_case:
        name = expected["kernel"]
        stage = phases[name]
        runs = [r for r in wall if r["kernel"] == name]
        if len(runs) != 6 or {r["repeat"] for r in runs} != {1, 2, 3}:
            raise ValueError("Missing wall repetition")
        for record in runs + [stage]:
            if record["returncode"] or record["timed_out"] or not record["valid"]:
                raise ValueError("Raw timing run failed")
        for compiler in ("pluto", "polcert"):
            selected = [r for r in runs if r["compiler"] == compiler]
            if len(selected) != 3 or {r["repeat"] for r in selected} != {1, 2, 3}:
                raise ValueError("Missing compiler repetition")
            if statistics.median(r["wall_seconds"] for r in selected) != expected[compiler + "_wall_seconds"]:
                raise ValueError("Published median differs from raw wall repetitions")
        if expected["additional_wall_seconds"] != expected["polcert_wall_seconds"] - expected["pluto_wall_seconds"]:
            raise ValueError("Paired wall-time difference changed")
        if stage["stages_seconds"] != expected["stages_seconds"] or stage["calls"] != expected["stage_calls"]:
            raise ValueError("Published stages differ from raw stage record")
        if stage["calls"].get("affine_validation", 0):
            raise ValueError("Unclassified standalone affine measurement")
        if stage["errors"] or abs(sum(stage["stages_seconds"].values()) - stage["total_seconds"]) > 1e-6:
            raise ValueError("Invalid disjoint stage attribution")
        compiler_hashes = [r["stdout_sha256"] for r in runs if r["compiler"] == "polcert"]
        producer_hashes = [r["generated_sha256"] for r in runs if r["compiler"] == "pluto"]
        if len(set(compiler_hashes + [stage["stdout_sha256"]])) != 1 or len(set(producer_hashes)) != 1:
            raise ValueError("Compiler output changed across timing repetitions")


def load_timing_observations(root, metadata, per_case):
    from collect_pipeline_timing import parse_actual_profile
    observed = {"wall": [], "phases": []}
    for group in observed:
        for path in sorted((root / group).glob("*.json")):
            row = read_json(path)
            if row["fingerprint"] != metadata["fingerprint"]:
                raise ValueError("Raw timing record belongs to another experiment")
            for key in ("stdout", "stderr"):
                check_reference(path.with_suffix("." + key + ".txt"), row[key + "_sha256"])
            if row.get("generated_sha256"):
                check_reference(path.with_suffix(".pluto.c"), row["generated_sha256"])
            if group == "phases":
                parsed = parse_actual_profile(path.with_suffix(".stderr.txt").read_text())
                for field in ("stages_seconds", "calls", "total_seconds", "excluded_capture_io_seconds"):
                    if parsed[field] != row[field]:
                        raise ValueError("Stage record differs from emitted profile")
            observed[group].append(row)
    validate_timing_values(observed, per_case)
    return observed


class Anonymizer:
    def __init__(self, aliases=(), replacements=None, denylist=()):
        self.aliases = sorted(((str(a), b) for a, b in aliases), key=lambda x: -len(x[0]))
        self.replacements = replacements or {}
        self.denylist = denylist

    @lru_cache(maxsize=32768)
    def text(self, value):
        if re.fullmatch(r"[0-9a-f]{64}", value):
            return value
        for old, new in self.aliases:
            value = value.replace(old, new)
        for old, new in sorted(self.replacements.items(), key=lambda x: -len(x[0])):
            value = value.replace(old, new)
        # Preserve SHA-256 evidence identities, not publicly searchable source
        # revisions or personal machine locations. Remaining locations describe
        # historical commands only; fresh commands are materialized separately.
        value = re.sub(r"(?<![0-9a-fA-F])[0-9a-fA-F]{40}(?![0-9a-fA-F])", "source-revision-removed", value)
        value = re.sub(r"https?://(?:www\.)?github\.com/[^\s\"'<>)}]+", "source-location-removed", value)
        value = re.sub(r"(?<![\w])/(?:tmp|home|root|polcert|pluto|build)(?:/[^\s\"'<>)}\],;]*)?",
                       lambda m: "external-location/" + m[0].rstrip('/').split('/')[-1], value)
        value = re.sub(r"[\w.+-]+@[\w.-]+\.[A-Za-z]{2,}", "contact-removed", value)
        for needle in self.denylist:
            value = re.sub(re.escape(needle), "identity-removed", value, flags=re.IGNORECASE)
        return value

    def object(self, value):
        if isinstance(value, dict):
            return {self.text(k): self.object(v) for k, v in value.items()
                    if k not in {"hostname", "username", "git_commit", "commit", "branch", "remote"}}
        if isinstance(value, list):
            return [self.object(v) for v in value]
        return self.text(value) if isinstance(value, str) else value


def anonymity_rules(tool_root):
    """Read the maintainer's literal policy without importing its packager."""
    source = tool_root / "prepare_anonymous.py"
    values = {}
    for node in ast.parse(source.read_text()).body:
        if isinstance(node, ast.Assign):
            for name in node.targets:
                if isinstance(name, ast.Name) and name.id in ("REPLACEMENTS", "DENYLIST"):
                    values[name.id] = ast.literal_eval(node.value)
    if set(values) != {"REPLACEMENTS", "DENYLIST"}:
        raise ValueError("Missing maintainer anonymity policy")
    return values["REPLACEMENTS"], values["DENYLIST"]


def archive_text_files(destination, entries, anonymizer):
    """Deterministic archive of regular UTF-8 evidence; never package ELF."""
    index = []
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("wb") as raw, (lzma.LZMAFile(raw, mode="w", preset=6)
            if destination.suffix == ".xz" else
            gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0)) as gz:
        with tarfile.open(fileobj=gz, mode="w|", format=tarfile.PAX_FORMAT) as archive:
            for name, path in sorted(entries.items()):
                if Path(name).is_absolute() or ".." in Path(name).parts:
                    raise ValueError("Unsafe evidence archive path")
                data = path.read_bytes()
                if data.startswith(b"\x7fELF"):
                    raise ValueError("Executable selected as evidence: " + name)
                text = data.decode("utf-8", errors="replace")
                transformed = (encode(anonymizer.object(json.loads(text))) if path.suffix == ".json"
                               else anonymizer.text(text).encode())
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(transformed), 0o644, 0
                archive.addfile(info, io.BytesIO(transformed))
                index.append({"path": name, "original_sha256": hashlib.sha256(data).hexdigest(),
                              "sha256": hashlib.sha256(transformed).hexdigest(), "bytes": len(transformed),
                              "anonymized": transformed != data})
    return index


def selected_tree(root, prefix, *, reviews=False):
    selected = {}
    for path in sorted(root.rglob("*")):
        if path.is_symlink() or not path.is_file() or path.suffix not in TEXT_SUFFIXES:
            continue
        relative = path.relative_to(root)
        if "work" in relative.parts or "__pycache__" in relative.parts:
            continue
        if reviews and path.suffix not in {".json", ".py", ".md"}:
            continue
        selected[(Path(prefix) / relative).as_posix()] = path
    return selected


def select_retention_evidence(final_root, followup_root, original, updated):
    """Keep raw runs and final-table review dependencies, not review workspaces."""
    roots = [(Path(final_root).resolve(), "recorded/final"),
             (Path(followup_root).resolve(), "recorded/followup")]
    entries = {}
    pending, inspected = [], set()

    def resolve(name):
        path = Path(name)
        if ".." in path.parts:
            raise ValueError("Unsafe review evidence reference")
        for base, prefix in roots:
            candidate = path.resolve()
            if not candidate.is_relative_to(base) and base.name in path.parts:
                candidate = base.joinpath(*path.parts[path.parts.index(base.name) + 1:])
            if candidate.is_relative_to(base):
                return candidate, prefix + "/" + candidate.relative_to(base).as_posix()
        return None

    def add(name, digest=None, *, inspect=True):
        location = resolve(name)
        if location is None:
            return
        path, member = location
        if digest:
            check_reference(path, digest)
        if not path.is_file() or path.is_symlink():
            raise ValueError("Missing final review evidence: " + name)
        entries[member] = path
        if inspect and path.suffix == ".json" and path not in inspected:
            pending.append(path)

    for base, prefix, rows in (
            (roots[0][0] / "retention/raw", "recorded/final/retention/raw", original["rows"]),
            (roots[1][0] / "single-phase-retention/raw", "recorded/followup/single-phase-retention/raw", updated["rows"])):
        for row in rows:
            case = base / row["cohort"] / "cases" / row["id"]
            for name in ("source.loop", "result.json", "polcert.stdout.txt", "polcert.stderr.txt"):
                if (case / name).is_file():
                    add(str(case / name), inspect=False)
            # The independent baseline is the actual comparison partner.
            entries.update(selected_tree(case / "baseline", prefix + "/" + row["cohort"] +
                                         "/cases/" + row["id"] + "/baseline"))
            for capture in (case / "pluto").glob("*"):
                if not capture.is_dir():
                    continue
                # Keep candidate schedules and commands. The native path does
                # not consume Pluto's duplicate C/CLooG control outputs.
                for name in ("invocation.json", "input.scop", "output.afterscheduling.scop",
                             "output.midtransform.scop", "output.posttile.scop", "stdout.txt", "stderr.txt"):
                    if (capture / name).is_file():
                        add(str(capture / name), inspect=False)
        if (base / "run-provenance.json").is_file():
            add(str(base / "run-provenance.json"), inspect=False)

    def references(value):
        if isinstance(value, list):
            for child in value:
                references(child)
        elif isinstance(value, dict):
            for field in ("file", "path"):
                if isinstance(value.get(field), str) and isinstance(value.get("sha256"), str):
                    add(value[field], value["sha256"])
            for key, child in value.items():
                if key in {"dependencies_sha256", "dependency_sha256"} and isinstance(child, dict):
                    for name, digest in child.items():
                        add(name, digest)
                elif isinstance(child, str) and key.endswith(("_file", "_evidence")):
                    add(child, value.get(key.removesuffix("_file") + "_sha256"))
                elif isinstance(child, (dict, list)):
                    references(child)

    primary = {cohort for cohorts in PRIMARY.values() for cohort in cohorts}
    for row in original["rows"]:
        if row["cohort"] not in primary:
            continue
        # The initial classification is small and explains no-effect cases.
        if row.get("analysis_file"):
            add(row["analysis_file"], row.get("analysis_sha256"), inspect=False)
        for record in row.get("contributing_reviews", []) + ([row["origin_review"]] if row.get("origin_review") else []):
            add(record["file"], record["sha256"], inspect=False)
        if row.get("evidence"):
            references(row["evidence"])
        elif row.get("membership_evidence"):
            add(row["membership_evidence"])
    for row in updated["rows"]:
        if row.get("fresh_effect_evidence"):
            references(row["fresh_effect_evidence"])
    for path in (roots[0][0] / "retention/summary/summary.json",
                 roots[0][0] / "retention/summary/closed-review.json",
                 roots[1][0] / "single-phase-retention/review-final.json"):
        if path.is_file():
            add(str(path), inspect=False)
    while pending:
        path = pending.pop()
        if path in inspected:
            continue
        inspected.add(path)
        references(read_json(path))
    # Retain the analysis implementations beside selected review records.
    # These are inspectable historical scripts, not the portable entry points.
    groups = set()
    for path in list(entries.values()):
        for base, _ in roots:
            relative = path.relative_to(base) if path.is_relative_to(base) else None
            if relative and relative.parts[:2] == ("retention", "reviews") and len(relative.parts) > 2:
                groups.add(base.joinpath(*relative.parts[:3]))
    for group in groups:
        for script in group.glob("*.py"):
            add(str(script), inspect=False)
    return entries


def check_reference(path, digest):
    if not path.is_file() or sha(path) != digest:
        raise ValueError("Missing or changed evidence: " + str(path))


def validate_recorded_pairs(final_root, followup_root, original, updated):
    """Bind classification records to the complete named raw pairs, not last captures."""
    bindings = []
    for row in original["rows"]:
        case = final_root / "retention/raw" / row["cohort"] / "cases" / row["id"]
        source, native = case / "source.loop", case / "polcert.stdout.txt"
        check_reference(source, row["source_sha256"])
        if row.get("final_sha256"):
            check_reference(native, row["final_sha256"])
        record = read_json(case / "result.json")
        if record["returncode"] != row["native_returncode"] or record["timed_out"] != row["native_timeout"]:
            raise ValueError("Native outcome differs from review: " + row["id"])
        protocol_file = case / "baseline/protocol.json"
        protocol = read_json(protocol_file)
        if protocol["source_sha256"] != row["source_sha256"]:
            raise ValueError("Independent baseline uses a different source")
        producer_path = None
        for relative, digest in protocol.get("files_sha256", {}).items():
            if Path(relative).is_absolute() or ".." in Path(relative).parts:
                raise ValueError("Unsafe baseline record path")
            check_reference(case / "baseline" / relative, digest)
            if relative.endswith("output.pluto.c") and digest == row.get("producer_sha256"):
                producer_path = "recorded/final/retention/raw/" + row["cohort"] + "/cases/" + row["id"] + "/baseline/" + relative
        if row.get("producer_sha256") and producer_path is None:
            raise ValueError("Reviewed producer does not match the independent baseline")
        base = "recorded/final/retention/raw/" + row["cohort"] + "/cases/" + row["id"]
        bindings.append({"cohort": row["cohort"], "id": row["id"], "source": base + "/source.loop",
                         "source_sha256": row["source_sha256"], "producer": producer_path,
                         "producer_sha256": row.get("producer_sha256"), "final": base + "/polcert.stdout.txt",
                         "final_sha256": row.get("final_sha256")})
    mapping = {(r["cohort"], r["id"]): r for r in bindings}
    for row in updated["rows"]:
        case = followup_root / "single-phase-retention/raw" / row["cohort"] / "cases" / row["id"]
        check_reference(case / "polcert.stdout.txt", row["new_stdout"]["sha256"])
        check_reference(case / "result.json", row["native_result"]["sha256"])
        fresh = row.get("fresh_effect_evidence")
        if fresh:
            # Only named evidence beneath the supplied follow-up root is read.
            suffix = Path(fresh["path"]).parts
            marker = "matmul-production"
            if marker not in suffix:
                raise ValueError("Unrecognized fresh tiling evidence location")
            check_reference(followup_root.joinpath(*suffix[suffix.index(marker):]), fresh["sha256"])
        binding = mapping[row["cohort"], row["id"]]
        binding["final"] = "recorded/followup/single-phase-retention/raw/" + row["cohort"] + "/cases/" + row["id"] + "/polcert.stdout.txt"
        binding["final_sha256"] = row["new_stdout"]["sha256"]
    return bindings


def write_csv(path, rows, fields):
    with path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def tool_closure(tool_root):
    names, pending = set(), list(TOOLS)
    while pending:
        name = pending.pop()
        if name in names:
            continue
        source = tool_root / name
        if not source.is_file():
            raise ValueError("Missing reproduction helper: " + name)
        names.add(name)
        for node in ast.walk(ast.parse(source.read_text())):
            if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                    and node.func.attr == "with_name" and node.args
                    and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str)):
                sibling = node.args[0].value
                if sibling.endswith(".py") and (tool_root / sibling).is_file():
                    pending.append(sibling)
            modules = ([node.module] if isinstance(node, ast.ImportFrom) else
                       [v.name for v in node.names] if isinstance(node, ast.Import) else [])
            for module in modules:
                sibling = (module or "").split('.')[0] + ".py"
                if (tool_root / sibling).is_file():
                    pending.append(sibling)
    return sorted(names)


def select_timing(final_root, current_timing_root=None, expected_current_compiler_sha256=None):
    """Select complete measurements, requiring the same 62-input experiment."""
    recorded = read_json(Path(final_root) / "timing/run-metadata.json")
    root = Path(current_timing_root) if current_timing_root else Path(final_root) / "timing"
    metadata = read_json(root / "run-metadata.json")
    if current_timing_root:
        if not expected_current_compiler_sha256 or metadata["polopt_sha256"] != expected_current_compiler_sha256:
            raise ValueError("Fresh timing is not bound to the expected current compiler")
        fields = ("kernel", "source_sha256", "c_sha256", "polopt_args", "pluto_args")
        cases = lambda data: sorted([{key: row[key] for key in fields} for row in data["cases"]],
                                    key=lambda row: row["kernel"])
        if len(metadata["cases"]) != 62 or cases(metadata) != cases(recorded):
            raise ValueError("Fresh timing changed the recorded 62-input configuration")
        for key in ("repeats", "config_sha256", "pluto_sha256"):
            if metadata[key] != recorded[key]:
                raise ValueError("Fresh timing changed the recorded protocol: " + key)
    build = metadata["profiler_build"]
    if (build["original_polopt_sha256"] != metadata["polopt_sha256"] or
            build["instrumented_polopt_sha256"] != metadata["profile_polopt_sha256"]):
        raise ValueError("Timing profiler does not belong to the measured compiler")
    result = read_json(root / "timing-results.json")
    if {r["kernel"] for r in result["per_case"]} != {r["kernel"] for r in metadata["cases"]}:
        raise ValueError("Timing result cohort differs from the measured configuration")
    return root, result, metadata


def package_evaluation(destination: Path, *, final_root: Path, followup_root: Path,
                       source_root: Path, current_timing_root: Path | None = None,
                       expected_current_compiler_sha256: str | None = None) -> dict:
    """Build an anonymous evaluation directory; require a fresh destination."""
    destination, final_root, followup_root, source_root = map(Path,
        (destination, final_root, followup_root, source_root))
    if destination.exists():
        raise ValueError("Use a new evaluation destination")
    tool_root = Path(__file__).resolve().parent
    old = read_json(final_root / "retention/summary/summary.json")
    update = read_json(followup_root / "single-phase-retention/review-final.json")
    original_run = read_json(final_root / "retention/raw/run-provenance.json")
    timing_root, timing, timing_meta = select_timing(final_root, current_timing_root,
                                                    expected_current_compiler_sha256)
    timing_prefix = "recorded/current/timing" if current_timing_root else "recorded/final/timing"
    route_check = read_json(followup_root / "timing-scope/replay/review.json")
    if not old["primary_publication_ready"] or old["recorded_pairs"] != old["planned_pairs"]:
        raise ValueError("Original retention collection is not closed")
    if not timing["publishable_measurements"] or timing["failed"] or timing["pending"]:
        raise ValueError("Timing measurements are not publishable")
    if (route_check["timing_remeasurement"] or route_check["identity_passed"] != route_check["requested"]
            or route_check["completed"] != len(timing_meta["cases"])
            or len(route_check["rows"]) != len(timing_meta["cases"])
            or any(not r["all_identity_gates_pass"] or r["new_polopt_sha256"] != update["polopt_sha256"]
                   for r in route_check["rows"])):
        raise ValueError("Timing route comparison is not the expected identity-only check")
    check_reference(final_root / "retention/summary/summary.json", update["previous_summary"]["sha256"])
    pair_bindings = validate_recorded_pairs(final_root, followup_root, old, update)
    timing_observations = load_timing_observations(timing_root, timing_meta, timing["per_case"])
    rows = merge_recollection(old, update, original_run["compiler_sha256"])
    main_rows = aggregate_retention(rows)
    if any(row["requires_review"] for row in main_rows):
        raise ValueError("Main retention table still requires review")
    wall, stages = aggregate_timing(timing["per_case"])
    for row in wall:
        recorded = timing["wall_aggregates"][row["measurement"]]
        if any(not math.isclose(row[k], recorded[k], rel_tol=1e-12, abs_tol=1e-12)
               for k in ("mean_seconds", "median_seconds", "p95_seconds", "max_seconds")):
            raise ValueError("Timing aggregate differs from recorded per-case values")
    replacements, denylist = anonymity_rules(tool_root)
    aliases = [(final_root.resolve(), "recorded/final"), (followup_root.resolve(), "recorded/followup"),
               (source_root.resolve(), "compiler-source")]
    if current_timing_root:
        aliases.append((timing_root.resolve(), timing_prefix))
    # Container run roots occur in historical logs. Derive the aliases from
    # their manifests/provenance instead of encoding private temporary paths.
    plan = read_json(final_root / "retention/manifests/plan.json")
    case_root = Path(old["rows"][0]["case_directory"])
    if case_root.is_absolute():
        aliases.append((case_root.parents[3], "recorded/final/retention"))
    for source, prefix in [(original_run["compiler"], "compiler-source/polopt"),
                           (original_run["producer"], "producer/tool/pluto"),
                           (timing_meta["source_root"], "compiler-source")]:
        aliases.append((source, prefix))
    anon = Anonymizer(aliases, replacements, denylist)
    destination.mkdir(parents=True)
    results = destination / "results"
    results.mkdir()
    evidence = destination / "evidence"
    evidence.mkdir()
    manifests = destination / "manifests"
    manifests.mkdir()
    input_count, input_hashes = 0, {}
    new_plan = {k: v for k, v in plan.items() if k != "collections"}
    new_plan["collections"] = []
    for collection in plan["collections"]:
        manifest_file = final_root / "retention/manifests" / collection["manifest"]
        check_reference(manifest_file, collection["manifest_sha256"])
        original_manifest = read_json(manifest_file)
        packed = {k: v for k, v in original_manifest.items() if k not in ("cases", "source_root")}
        packed["cases"] = []
        for case in original_manifest["cases"]:
            source = final_root / "retention/raw" / collection["result_directory"] / "cases" / case["id"] / "source.loop"
            check_reference(source, case["source_sha256"])
            relative = "inputs/" + case["source_sha256"] + ".loop"
            target = destination / relative
            target.parent.mkdir(exist_ok=True)
            if not target.exists():
                target.write_bytes(source.read_bytes())
                input_count += 1
                input_hashes[relative] = sha(target)
            row = {k: v for k, v in case.items() if k not in ("loop_input", "c_source", "cwd", "env")}
            row["loop_input"] = relative
            old_c = case.get("c_source")
            candidate = None
            if old_c:
                for part in ("tests/", "tools/"):
                    if "/" + part in old_c:
                        candidate = source_root / (part + old_c.split("/" + part, 1)[1])
                        break
            if candidate and candidate.is_file():
                rel_c = "inputs/" + sha(candidate) + ".c"
                (destination / rel_c).write_bytes(candidate.read_bytes())
                input_hashes[rel_c] = sha(candidate)
                row["c_source"] = rel_c
            else:
                row["c_source"] = None
                row["c_source_note"] = "Not used by the independent strengthened-SCoP retention baseline."
            if anon.text(target.read_text()) != target.read_text():
                raise ValueError("Input requires anonymization; do not silently change its identity")
            packed["cases"].append(row)
        write_json(manifests / collection["manifest"], packed)
        new_plan["collections"].append({**collection, "manifest_sha256": sha(manifests / collection["manifest"])})
    new_plan["source_root"] = "Set by the fresh-run entry point"
    write_json(manifests / "plan.json", new_plan)
    # The timing driver selects the original common 62 by source_relative.
    timing_cases = []
    for case in timing_meta["cases"]:
        rel_c = "inputs/" + case["c_sha256"] + ".c"
        if not (destination / rel_c).is_file():
            raise ValueError("Matching original timing C input is missing")
        # The existing timing collector adds standard parallel itself. Supply
        # its original rectangular input policy, not the already-expanded
        # output metadata (which would duplicate --parallel).
        timing_cases.append({**{k: v for k, v in case.items() if k not in ("loop_input", "c_source")},
                             "pluto_args": [v for v in case["pluto_args"] if v not in ("--parallel", "--noparallel")] + ["--noparallel"],
                             "loop_input": "inputs/" + case["source_sha256"] + ".loop", "c_source": rel_c})
    write_json(manifests / "timing.json", {"cases": timing_cases})
    tool_dest = destination / "bin"
    tool_dest.mkdir()
    for name in tool_closure(tool_root):
        # Executable helper source is not rewritten. Its active entry points
        # receive all locations explicitly. Historical helper mains are unused.
        data = (tool_root / name).read_bytes()
        if any(token.lower().encode() in data.lower() for token in denylist):
            raise ValueError("Reproduction helper violates anonymity policy: " + name)
        (tool_dest / name).write_bytes(data)
    assets = destination / "assets"
    assets.mkdir()
    for name in ("PipelineMeasure.ml", "monotonic_clock_stubs.c"):
        (assets / name).write_bytes((tool_root.parent / "evaluation" / name).read_bytes())
    entries = select_retention_evidence(final_root, followup_root, old, update)
    archive_index = archive_text_files(evidence / "retention.tar.xz", entries, anon)
    timing_entries = {}
    for name in ("wall", "phases", "proposals"):
        timing_entries.update(selected_tree(timing_root / name, timing_prefix + "/" + name))
    for name in ("timing-results.json", "timing-summary.json", "run-metadata.json"):
        timing_entries[timing_prefix + "/" + name] = timing_root / name
    timing_entries.update(selected_tree(followup_root / "timing-scope/replay", "recorded/followup/timing-scope/replay"))
    timing_index = archive_text_files(evidence / "timing.tar.gz", timing_entries, anon)
    bugs_root = final_root / "vector-regressions/bug-replays"
    bugs = read_json(bugs_root / "summary.json")
    if len(bugs["rows"]) != 5 or any(r["returncode"] for r in bugs["rows"]):
        raise ValueError("The five recorded bug runners did not all pass")
    bug_index = archive_text_files(evidence / "five-bugs.tar.gz",
                                  selected_tree(bugs_root, "recorded/five-bugs"), anon)
    write_json(evidence / "archive-index.json", {"retention.tar.xz": archive_index,
                                               "timing.tar.gz": timing_index, "five-bugs.tar.gz": bug_index})
    write_json(results / "retention-records.json", anon.object(rows))
    write_json(results / "pair-bindings.json", pair_bindings)
    write_json(results / "timing-records.json", anon.object(timing["per_case"]))
    write_json(results / "timing-observations.json", anon.object(timing_observations))
    write_json(results / "timing-protocol.json", anon.object(timing_meta))
    write_json(results / "timing-route-check.json", anon.object(route_check))
    write_json(results / "five-bugs.json", anon.object(bugs))
    summary = {"schema_version": 1, "data_kind": "recorded-results-not-a-new-experiment",
               "retention": main_rows, "timing": wall, "stages": stages,
               "recorded_pairs": old["recorded_pairs"], "tiling_recollected_pairs": len(update["rows"]),
               "retention_original_compiler_sha256": original_run["compiler_sha256"],
               "tiling_recollection_compiler_sha256": update["polopt_sha256"],
               "timing_measured_compiler_sha256": timing_meta["polopt_sha256"],
               "timing_instrumented_compiler_sha256": timing_meta["profile_polopt_sha256"],
               "timing_measurement_scope": "current-compiler" if current_timing_root else "original-compiler",
               "timing_archive_prefix": timing_prefix,
               "five_bugs_compiler_sha256": bugs["binary_sha256"],
               "producer_sha256": original_run["producer_sha256"],
               "timing_route_replay": {"requested": route_check["requested"],
                                       "identity_passed": route_check["identity_passed"], "timing_remeasurement": False},
               "timing_wall_repetitions": timing_meta["repeats"],
               "additional_cohorts": anon.object(old["additional_cohorts"]),
               "notes": ["Counts are distinct source bytes within each effect, not configurations or test samples.",
                         "Only the two tiling cohorts were recollected for the later compiler; other rows retain their recorded identity.",
                         "Wall times are medians of three runs per compiler and kernel, then aggregated over 62 kernels. Stages use one separately instrumented invocation per kernel. All times are seconds.",
                         ("Timing was freshly measured on the explicitly identified current compiler. The historical route replay is retained as earlier evidence, not as a timing measurement."
                          if current_timing_root else "The later compiler passed an output/route identity replay for the 62 timing inputs. It was not formally re-timed."),
                         "The timing values describe the measured binaries only; output/route identity does not establish equal compilation cost for another build.",
                         "Additional cohorts are outside the six primary rows. Their unresolved observations establish neither retention nor a demonstrated loss.",
                         "Stored static and sampled evidence measures optimization effects, not a replacement proof of program correctness.",
                         "Fresh collection does not reuse recorded results; cases not closed by the generic observer remain subject to explicit review.",
                         "The archive retains raw runs and reviews supporting the final table; superseded analyses, progress snapshots, and unrelated investigations remain outside the submission package.",
                         "Historical case-specific review sources are evidence for inspection, not supported portable entry points. They may write output when imported; do not execute them in the recorded evidence tree."]}
    write_json(results / "summary.json", summary)
    write_csv(results / "retention.csv", main_rows, ["effect", "pairs", "distinct_sources", "pluto", "retained",
              "not_retained", "no_effect", "baseline_unavailable", "requires_review", "measured_compiler_sha256"])
    stats = ["unit", "count", "mean_seconds", "median_seconds", "p95_seconds", "max_seconds"]
    write_csv(results / "timing.csv", wall, ["measurement", *stats])
    write_csv(results / "stages.csv", stages, ["stage", *stats])
    effect_labels = {"affine": "Affine scheduling", "iss": "Index-set splitting",
                     "rectangular_tiling": "Rectangular tiling", "two_level_tiling": "Two-level tiling",
                     "diamond_tiling": "Diamond tiling", "parallelization": "Parallelization"}
    by_effect = {row["effect"]: row for row in main_rows}
    table = "".join("<tr><td>" + label + "</td><td>" + str(by_effect[key]["pluto"]) +
                    "</td><td>" + str(by_effect[key]["retained"]) + "</td></tr>"
                    for key, label in effect_labels.items())
    wall_labels = {"pluto_wall_seconds": "Pluto", "polcert_wall_seconds": "PolCert",
                   "additional_wall_seconds": "Additional time (δ)"}
    wall_table = "".join("<tr><td>" + wall_labels[r["measurement"]] + "</td>" +
                         "".join("<td>" + format(r[key], ".3f") + "</td>" for key in
                                 ("mean_seconds", "median_seconds", "p95_seconds", "max_seconds")) + "</tr>"
                         for r in wall)
    stage_labels = {"pluto": "Pluto", "affine_pre_validation": "Affine validation before tiling",
                    "affine_post_validation": "Affine validation after tiling",
                    "tiling_validation": "Tiling validation", "parallel_validation": "Parallelization validation",
                    "codegen": "Loop generation", "others": "Others"}
    stage_table = "".join("<tr><td>" + stage_labels[r["stage"]] + "</td><td>" +
                          format(r["mean_seconds"], ".3f") + "</td><td>" +
                          format(r["max_seconds"], ".3f") + "</td></tr>" for r in stages)
    timing_scope = ('These are fresh measurements of the identified current compiler. '
                    'The <a href="timing-route-check.json">historical output/route replay</a> remains separate evidence.'
                    if current_timing_root else
                    'These values describe the original recorded builds. The later compiler passed '
                    '<a href="timing-route-check.json">62 output/route checks</a> but was not re-timed; '
                    'matching outputs and routes do not establish equal compilation cost.')
    page = ('<!doctype html><html lang="en"><meta charset="utf-8"><title>Paper evaluation</title>'
            '<meta name="viewport" content="width=device-width, initial-scale=1">'
            '<link rel="stylesheet" href="../../docs/artifact.css">'
            '<main><p><a href="../../docs/evaluation.html">Evaluation guide</a></p>'
            '<h1>Recorded Results</h1>'
            '<p>These tables combine recorded experiments with explicitly different compiler identities. '
            'The retention table recollects rectangular and two-level tiling with the later compiler; '
            'the timing section states its own measurement scope.</p>'
            '<h2>Optimization Effects</h2><table><thead><tr><th>Optimization</th><th>Pluto</th><th>Retained</th></tr></thead><tbody>' + table + '</tbody></table>'
            '<p>Rectangular and two-level tiling: compiler <code>' + update['polopt_sha256'][:12] +
            '</code>. Other retention rows: compiler <code>' + original_run['compiler_sha256'][:12] + '</code>.</p>'
            '<p>Each kernel counts once per transformation when Pluto produces the effect. '
            'The six parallel differences arise from loop generation splitting a common parallel range. '
            'No-effect inputs and unavailable producer outputs are recorded separately. '
            'Supplementary configurations are excluded from these six rows; unresolved supplementary observations establish neither retention nor loss. '
            'The CSV and summary contain full compiler hashes.</p>'
            '<p><a href="retention.csv">Retention CSV</a> · <a href="retention-records.json">Per-pair records</a> · <a href="../evidence/retention.tar.xz">Raw outputs and final review evidence</a></p>'
            '<h2>Compilation Time (seconds)</h2><p>Each entry summarizes the per-kernel medians of three runs, '
            'using affine scheduling, rectangular tiling, and parallelization. Wall measurements use compiler <code>' +
            timing_meta['polopt_sha256'][:12] + '</code>; stage measurements use its instrumented build <code>' +
            timing_meta['profile_polopt_sha256'][:12] + '</code>. '
            + timing_scope + '</p>'
            '<table><thead><tr><th>Measurement</th><th>Mean</th><th>Median</th><th>95th percentile</th><th>Maximum</th></tr></thead><tbody>' + wall_table + '</tbody></table>'
            '<details><summary>Stage breakdown (seconds)</summary>'
            '<p>One separately instrumented compilation per kernel measures the actual stages, without replaying them.</p>'
            '<table><thead><tr><th>Stage</th><th>Mean</th><th>Maximum</th></tr></thead><tbody>' + stage_table + '</tbody></table></details>'
            '<p><a href="timing.csv">Wall-time CSV</a> · <a href="stages.csv">Stage CSV</a> · <a href="timing-records.json">Per-kernel measurements</a> · <a href="../evidence/timing.tar.gz">Raw measurements</a></p>'
            '<h2>Five Miscompilations</h2><p><a href="five-bugs.json">Recorded executions and check outcomes</a> · <a href="../evidence/five-bugs.tar.gz">Inputs and logs</a></p>'
            '<p>The runners check that dependent loops remain sequential and explicit unsafe requests are rejected. '
            'Singleton parallel loops are allowed. The unroll-and-jam runner checks that separate loops remain separate when fusion would be unsafe. '
            'A successful runner does not imply that the whole compiler invocation exits with rejection.</p>'
            '<h2>Reproduce</h2><pre>python3 evaluation/bin/run_paper_evaluation.py verify\n'
            'python3 evaluation/bin/run_paper_evaluation.py retention --help\n'
            'python3 evaluation/bin/run_paper_evaluation.py timing --help</pre>'
            '<p>Run from the artifact root. Fresh experiments require built compiler/producer paths and a new output directory. '
            'Subsets are supported. Generic observations can leave cases needing static review; no stored success is used to fill those cases.</p>'
            '<p><a href="summary.json">Complete summary and scope</a> · <a href="timing-protocol.json">Timing protocol</a> · <a href="../evidence/archive-index.json">Original and anonymized content hashes</a></p></main></html>')
    (results / "index.html").write_text(page)
    files = {p.relative_to(destination).as_posix(): sha(p) for p in sorted(destination.rglob("*")) if p.is_file()}
    write_json(destination / "package-index.json", {"files_sha256": files, "input_files_sha256": input_hashes,
               "format": "Anonymized text archives with separate original and packaged SHA-256 hashes.",
               "source_inputs_unchanged": True})
    return {"entry": "evaluation/results/index.html", "summary": "evaluation/results/summary.json",
            "five_bugs": "evaluation/results/five-bugs.json", "files": len(files), "loop_sources": input_count,
            "bytes": sum(p.stat().st_size for p in destination.rglob("*") if p.is_file()),
            "summary_sha256": sha(results / "summary.json")}


def verify_recorded(root):
    root = Path(root)
    index = read_json(root / "package-index.json")
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    if actual != set(index["files_sha256"]) | {"package-index.json"}:
        raise ValueError("Evaluation directory has missing or unindexed files")
    for name, digest in index["files_sha256"].items():
        if Path(name).is_absolute() or ".." in Path(name).parts:
            raise ValueError("Unsafe package member")
        check_reference(root / name, digest)
    archive_index = read_json(root / "evidence/archive-index.json")
    original_hashes = {r["path"]: r["original_sha256"] for rows in archive_index.values() for r in rows}
    archived_timing = {"wall": [], "phases": []}
    for name, expected in archive_index.items():
        wanted = {r["path"]: r for r in expected}
        seen = set()
        with tarfile.open(root / "evidence" / name, "r:*") as archive:
            for member in archive:
                if not member.isfile() or member.name not in wanted or member.name in seen:
                    raise ValueError("Unexpected evidence archive member")
                data = archive.extractfile(member).read()
                if hashlib.sha256(data).hexdigest() != wanted[member.name]["sha256"]:
                    raise ValueError("Evidence bytes changed")
                for group in archived_timing:
                    if any(member.name.startswith(prefix + "/" + group + "/") for prefix in
                           ("recorded/final/timing", "recorded/current/timing")) and member.name.endswith(".json"):
                        archived_timing[group].append(json.loads(data))
                seen.add(member.name)
        if seen != set(wanted):
            raise ValueError("Evidence archive is incomplete")
    for row in read_json(root / "results/pair-bindings.json"):
        for side in ("source", "producer", "final"):
            if row.get(side + "_sha256") is not None and original_hashes.get(row[side]) != row[side + "_sha256"]:
                raise ValueError("Recorded pair is not bound to its archived raw bytes")
    summary = read_json(root / "results/summary.json")
    if aggregate_retention(read_json(root / "results/retention-records.json")) != summary["retention"]:
        raise ValueError("Retention table differs from per-pair records")
    wall, stages = aggregate_timing(read_json(root / "results/timing-records.json"))
    validate_timing_values(archived_timing, read_json(root / "results/timing-records.json"))
    exported = read_json(root / "results/timing-observations.json")
    for group in archived_timing:
        key = lambda r: (r["kernel"], r.get("compiler", ""), r.get("repeat", 0))
        if sorted(archived_timing[group], key=key) != sorted(exported[group], key=key):
            raise ValueError("Exported timing observations differ from archived originals")
    if wall != summary["timing"] or stages != summary["stages"]:
        raise ValueError("Timing table differs from per-kernel records")
    return {"verified_recorded_files": len(index["files_sha256"]),
            "retention_rows": len(summary["retention"]), "new_experiment": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--final-root", type=Path, required=True)
    parser.add_argument("--followup-root", type=Path, required=True)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--current-timing-root", type=Path, help="Complete fresh collector measurements directory")
    parser.add_argument("--expected-current-compiler-sha256", help="SHA-256 of the current validated build")
    args = parser.parse_args()
    print(json.dumps(package_evaluation(args.destination, final_root=args.final_root,
          followup_root=args.followup_root, source_root=args.source_root,
          current_timing_root=args.current_timing_root,
          expected_current_compiler_sha256=args.expected_current_compiler_sha256), indent=2))
