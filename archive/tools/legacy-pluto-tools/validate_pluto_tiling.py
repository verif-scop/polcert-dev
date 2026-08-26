#!/usr/bin/env python3
from __future__ import annotations

import argparse
import itertools
import json
import math
import pathlib
import sys
from collections import Counter
from dataclasses import asdict, dataclass, field


@dataclass(frozen=True)
class RelationMeta:
    nrows: int
    ncols: int
    output_dims: int
    input_dims: int
    local_dims: int
    param_dims: int


@dataclass
class Relation:
    kind: str
    meta: RelationMeta
    rows: list[tuple[int, ...]]
    output_names: list[str]
    input_names: list[str]
    param_names: list[str]


@dataclass
class AccessRelation:
    kind: str
    relation: Relation


@dataclass
class Statement:
    index: int
    domain: Relation | None = None
    scattering: Relation | None = None
    accesses: list[AccessRelation] = field(default_factory=list)
    iterators: list[str] = field(default_factory=list)
    body: str = ""


@dataclass
class Scop:
    path: pathlib.Path
    params: list[str]
    statements: list[Statement]


@dataclass(frozen=True)
class AffineExpr:
    var_coeffs: tuple[tuple[str, int], ...]
    param_coeffs: tuple[tuple[str, int], ...]
    const: int = 0

    def dependencies(self) -> set[str]:
        return {name for name, coeff in self.var_coeffs if coeff != 0}

    def render(self) -> str:
        parts: list[str] = []
        for name, coeff in self.var_coeffs:
            if coeff == 0:
                continue
            if coeff == 1:
                parts.append(name)
            elif coeff == -1:
                parts.append(f"-{name}")
            else:
                parts.append(f"{coeff}*{name}")
        for name, coeff in self.param_coeffs:
            if coeff == 0:
                continue
            if coeff == 1:
                parts.append(name)
            elif coeff == -1:
                parts.append(f"-{name}")
            else:
                parts.append(f"{coeff}*{name}")
        if self.const:
            parts.append(str(self.const))
        if not parts:
            return "0"
        rendered = parts[0]
        for item in parts[1:]:
            if item.startswith("-"):
                rendered += f" - {item[1:]}"
            else:
                rendered += f" + {item}"
        return rendered


@dataclass
class TileLink:
    parent: str
    expr: AffineExpr
    tile_size: int


@dataclass
class StatementTilingWitness:
    statement: int
    original_iterators: list[str]
    tiled_iterators: list[str]
    added_iterators: list[str]
    links: list[TileLink]


@dataclass
class TilingWitness:
    before: str
    after: str
    params: list[str]
    statements: list[StatementTilingWitness]


@dataclass
class StatementValidation:
    statement: int
    original_iterators: list[str]
    tiled_iterators: list[str]
    added_iterators: list[str]
    links: list[TileLink]
    shape_ok: bool
    transformation_contract_ok: bool
    witness_match_ok: bool
    base_domain_ok: bool
    link_rows_ok: bool
    access_ok: bool
    compiled_relation_ok: bool
    schedule_sanity_ok: bool
    bounded_coverage_ok: bool | None
    notes: list[str] = field(default_factory=list)


@dataclass
class ValidationReport:
    before: str
    after: str
    params: dict[str, int]
    ok: bool
    witness_source: str
    statements: list[StatementValidation]
    limitations: list[str]


class ValidationError(RuntimeError):
    pass


def _next_nonempty(lines: list[str], start: int) -> int:
    i = start
    while i < len(lines) and not lines[i].strip():
        i += 1
    return i


def _parse_relation_names(kind: str, meta: RelationMeta, comment_line: str) -> tuple[list[str], list[str], list[str]]:
    text = comment_line.lstrip("#").strip()
    segments = [seg.strip() for seg in text.split("|")]
    groups = [seg for seg in segments[1:-1] if seg]

    def words(seg: str) -> list[str]:
        return [w for w in seg.split() if w]

    if kind == "DOMAIN":
        output = words(groups[0]) if groups else []
        params = words(groups[1]) if len(groups) >= 2 else []
        return output, [], params

    output = words(groups[0]) if groups else []
    input_names = words(groups[1]) if len(groups) >= 2 else []
    params = words(groups[2]) if len(groups) >= 3 else []
    return output, input_names, params


def _parse_relation(lines: list[str], i: int, kind: str) -> tuple[Relation, int]:
    i = _next_nonempty(lines, i)
    meta_vals = [int(x) for x in lines[i].strip().split()]
    if len(meta_vals) != 6:
        raise ValidationError(f"bad relation header after {kind}: {lines[i]!r}")
    meta = RelationMeta(*meta_vals)
    i += 1
    i = _next_nonempty(lines, i)
    comment_line = lines[i].rstrip()
    if not comment_line.lstrip().startswith("#"):
        raise ValidationError(f"missing relation names comment for {kind}")
    output_names, input_names, param_names = _parse_relation_names(kind, meta, comment_line)
    i += 1
    rows: list[tuple[int, ...]] = []
    while len(rows) < meta.nrows:
        i = _next_nonempty(lines, i)
        raw = lines[i]
        body = raw.split("##", 1)[0].strip()
        row = tuple(int(x) for x in body.split())
        if len(row) != meta.ncols:
            raise ValidationError(
                f"row width mismatch for {kind}: expected {meta.ncols}, got {len(row)} in {raw!r}"
            )
        rows.append(row)
        i += 1
    return Relation(kind, meta, rows, output_names, input_names, param_names), i


def parse_scop(path: pathlib.Path) -> Scop:
    lines = path.read_text().splitlines()
    params: list[str] = []
    statements: list[Statement] = []
    current: Statement | None = None
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if line == "<strings>" and not params:
            i += 1
            strings: list[str] = []
            while i < len(lines) and lines[i].strip() != "</strings>":
                strings.extend(lines[i].split())
                i += 1
            params = strings
        elif line.startswith("# =============================================== Statement"):
            if current is not None:
                statements.append(current)
            index = len(statements) + 1
            current = Statement(index=index)
        elif line in {"DOMAIN", "SCATTERING", "READ", "WRITE"}:
            if current is None:
                raise ValidationError(f"relation {line} outside statement in {path}")
            relation, i = _parse_relation(lines, i + 1, line)
            if line == "DOMAIN":
                current.domain = relation
            elif line == "SCATTERING":
                current.scattering = relation
            else:
                current.accesses.append(AccessRelation(line, relation))
            continue
        elif line == "<body>":
            if current is None:
                raise ValidationError(f"<body> outside statement in {path}")
            i += 1
            while i < len(lines) and lines[i].strip() != "</body>":
                if lines[i].strip() == "# List of original iterators":
                    i += 1
                    current.iterators = lines[i].split()
                elif lines[i].strip() == "# Statement body expression":
                    i += 1
                    current.body = lines[i].strip()
                i += 1
        i += 1
    if current is not None:
        statements.append(current)
    return Scop(path=path, params=params, statements=statements)


def _delete_domain_added_coeffs(row: tuple[int, ...], added_count: int, after_var_count: int, param_count: int) -> tuple[int, ...]:
    flag = row[0]
    vars_after = row[1 : 1 + after_var_count]
    params = row[1 + after_var_count : 1 + after_var_count + param_count]
    const = row[-1]
    return (flag, *vars_after[added_count:], *params, const)


def _delete_access_added_coeffs(
    row: tuple[int, ...],
    output_dims: int,
    input_dims_after: int,
    added_count: int,
    param_dims: int,
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    flag = row[0]
    outs = row[1 : 1 + output_dims]
    ins = row[1 + output_dims : 1 + output_dims + input_dims_after]
    params = row[1 + output_dims + input_dims_after : 1 + output_dims + input_dims_after + param_dims]
    const = row[-1]
    return (flag, *outs, *ins[added_count:], *params, const), tuple(ins[:added_count])


def _make_affine_expr(
    coeffs: tuple[int, ...],
    var_names: list[str],
    param_coeffs: tuple[int, ...],
    param_names: list[str],
    const: int,
) -> AffineExpr:
    return AffineExpr(
        var_coeffs=tuple((name, coeff) for name, coeff in zip(var_names, coeffs) if coeff != 0),
        param_coeffs=tuple((name, coeff) for name, coeff in zip(param_names, param_coeffs) if coeff != 0),
        const=const,
    )


def _classify_tile_link_row(
    row: tuple[int, ...],
    var_names: list[str],
    added_names: set[str],
    param_names: list[str],
) -> tuple[tuple[str, int, AffineExpr], str] | None:
    if row[0] != 1:
        return None
    coeffs = row[1 : 1 + len(var_names)]
    params = row[1 + len(var_names) : 1 + len(var_names) + len(param_names)]
    const = row[-1]
    parent_positions = [
        idx for idx, (name, coeff) in enumerate(zip(var_names, coeffs)) if name in added_names and abs(coeff) >= 2
    ]
    if len(parent_positions) != 1:
        return None
    parent_idx = parent_positions[0]
    parent_name = var_names[parent_idx]
    parent_coeff = coeffs[parent_idx]
    tile_size = abs(parent_coeff)
    residual_coeffs = list(coeffs)
    residual_coeffs[parent_idx] = 0

    if parent_coeff < 0:
        expr = _make_affine_expr(tuple(residual_coeffs), var_names, tuple(params), param_names, const)
        return (parent_name, tile_size, expr), "lb"

    expr = _make_affine_expr(
        tuple(-value for value in residual_coeffs),
        var_names,
        tuple(-value for value in params),
        param_names,
        tile_size - 1 - const,
    )
    return (parent_name, tile_size, expr), "ub"


def _expr_sort_key(expr: AffineExpr) -> tuple[tuple[tuple[str, int], ...], tuple[tuple[str, int], ...], int]:
    return expr.var_coeffs, expr.param_coeffs, expr.const


def _tile_link_sort_key(link: TileLink) -> tuple[str, int, tuple[tuple[str, int], ...], tuple[tuple[str, int], ...], int]:
    return link.parent, link.tile_size, link.expr.var_coeffs, link.expr.param_coeffs, link.expr.const


def _canonicalize_links(
    links: list[TileLink],
    original_iterators: list[str],
    added_iterators: list[str],
) -> list[TileLink]:
    pending = list(links)
    available = set(original_iterators)
    ordered: list[TileLink] = []
    while pending:
        ready = [link for link in pending if link.expr.dependencies().issubset(available)]
        if not ready:
            unresolved = ", ".join(
                f"{link.parent}=floor(({link.expr.render()})/{link.tile_size})" for link in sorted(pending, key=_tile_link_sort_key)
            )
            raise ValidationError(f"cannot topologically order tile links: {unresolved}")
        ready.sort(key=_tile_link_sort_key)
        chosen = ready[0]
        pending.remove(chosen)
        ordered.append(chosen)
        available.add(chosen.parent)

    parents = [link.parent for link in ordered]
    if sorted(parents) != sorted(added_iterators):
        raise ValidationError(
            f"ordered tile-link parents {parents} do not cover added iterators {added_iterators}"
        )
    return ordered


def _check_statement_shape(before: Statement, after: Statement) -> tuple[bool, list[str]]:
    if before.domain is None or after.domain is None:
        raise ValidationError("missing domain relation")
    before_vars = before.domain.output_names or before.iterators
    after_vars = after.domain.output_names or after.iterators
    notes: list[str] = []
    ok = True
    if len(after_vars) < len(before_vars):
        notes.append(f"statement {before.index}: after has fewer iterators than before")
        ok = False
    elif after_vars[-len(before_vars) :] != before_vars:
        notes.append(
            f"statement {before.index}: tiled iterators do not end with the original iterators "
            f"(before={before_vars}, after={after_vars})"
        )
        ok = False
    return ok, notes


def _check_transformation_contract(
    original_iterators: list[str],
    tiled_iterators: list[str],
    added_iterators: list[str],
    links: list[TileLink],
    statement: int,
) -> tuple[bool, list[str]]:
    notes: list[str] = []
    ok = True
    if tiled_iterators != [*added_iterators, *original_iterators]:
        notes.append(
            f"statement {statement}: tiled iterator order is not added_iterators ++ original_iterators"
        )
        ok = False
    parents = [link.parent for link in links]
    if parents != added_iterators:
        notes.append(
            f"statement {statement}: ordered tile-link parents {parents} do not match added iterators {added_iterators}"
        )
        ok = False
    seen = set(original_iterators)
    for link in links:
        if link.tile_size <= 0:
            notes.append(f"statement {statement}: tile size for {link.parent} is not positive")
            ok = False
        unknown = sorted(dep for dep in link.expr.dependencies() if dep not in seen)
        if unknown:
            notes.append(
                f"statement {statement}: tile link {link.parent} depends on unresolved iterators {unknown}"
            )
            ok = False
        if link.parent in seen:
            notes.append(f"statement {statement}: tile parent {link.parent} is not fresh in ordered links")
            ok = False
        seen.add(link.parent)
    return ok, notes


def _check_pinstr_shape(before: Statement, after: Statement) -> tuple[bool, list[str]]:
    return _check_statement_shape(before, after)


def _check_domain_and_infer_links(before: Statement, after: Statement) -> tuple[bool, bool, list[TileLink], list[str]]:
    if before.domain is None or after.domain is None:
        raise ValidationError("missing domain relation")
    before_vars = before.domain.output_names or before.iterators
    after_vars = after.domain.output_names or after.iterators
    if len(after_vars) < len(before_vars):
        raise ValidationError(f"statement {before.index}: after has fewer iterators than before")
    if after_vars[-len(before_vars) :] != before_vars:
        raise ValidationError(
            f"statement {before.index}: expected tiled iterators to end with original iterators; "
            f"got before={before_vars}, after={after_vars}"
        )
    added_count = len(after_vars) - len(before_vars)
    before_counter = Counter(before.domain.rows)
    after_base_counter: Counter[tuple[int, ...]] = Counter()
    link_rows: list[tuple[int, ...]] = []
    for row in after.domain.rows:
        coeffs_added = row[1 : 1 + added_count]
        if all(v == 0 for v in coeffs_added):
            after_base_counter[_delete_domain_added_coeffs(row, added_count, len(after_vars), len(before.domain.param_names))] += 1
        else:
            link_rows.append(row)
    base_ok = after_base_counter == before_counter
    notes: list[str] = []
    if not base_ok:
        notes.append(
            f"statement {before.index}: lifted base-domain rows do not match before-domain rows "
            f"(before={sum(before_counter.values())}, lifted={sum(after_base_counter.values())})"
        )

    added_names = set(after_vars[:added_count])
    pair_kinds: dict[tuple[str, int, AffineExpr], set[str]] = {}
    for row in link_rows:
        classified = _classify_tile_link_row(row, after_vars, added_names, before.domain.param_names)
        if classified is None:
            notes.append(f"statement {before.index}: unsupported non-base row in tiled domain: {row}")
            return base_ok, False, [], notes
        key, kind = classified
        pair_kinds.setdefault(key, set()).add(kind)

    links: list[TileLink] = []
    for key, kinds in sorted(pair_kinds.items(), key=lambda item: (item[0][0], item[0][1], _expr_sort_key(item[0][2]))):
        if kinds != {"lb", "ub"}:
            notes.append(f"statement {before.index}: incomplete tile-link pair for {key}: {sorted(kinds)}")
            return base_ok, False, [], notes
        parent, tile_size, expr = key
        if parent in expr.dependencies():
            notes.append(f"statement {before.index}: tile parent {parent} occurs in its own affine expression")
            return base_ok, False, [], notes
        links.append(TileLink(parent=parent, expr=expr, tile_size=tile_size))

    parent_set = {link.parent for link in links}
    if parent_set != added_names:
        notes.append(
            f"statement {before.index}: tile parents {sorted(parent_set)} do not cover all added iterators {sorted(added_names)}"
        )
        return base_ok, False, [], notes

    return base_ok, True, _canonicalize_links(links, before_vars, after_vars[:added_count]), notes


def _check_pinstr_links(before: Statement, after: Statement) -> tuple[bool, bool, list[TileLink], list[str]]:
    return _check_domain_and_infer_links(before, after)


def _evaluate_affine_expr(expr: AffineExpr, values: dict[str, int], params: dict[str, int]) -> int:
    total = expr.const
    for name, coeff in expr.var_coeffs:
        total += coeff * values[name]
    for name, coeff in expr.param_coeffs:
        total += coeff * params[name]
    return total


def _check_accesses(before: Statement, after: Statement, added_count: int) -> tuple[bool, list[str]]:
    notes: list[str] = []
    if len(before.accesses) != len(after.accesses):
        return False, [f"statement {before.index}: access count changed from {len(before.accesses)} to {len(after.accesses)}"]
    ok = True
    for idx, (b_acc, a_acc) in enumerate(zip(before.accesses, after.accesses), start=1):
        if b_acc.kind != a_acc.kind:
            notes.append(f"statement {before.index}: access {idx} kind changed from {b_acc.kind} to {a_acc.kind}")
            ok = False
            continue
        b = b_acc.relation
        a = a_acc.relation
        if a.meta.input_dims != b.meta.input_dims + added_count:
            notes.append(
                f"statement {before.index}: access {idx} expected {b.meta.input_dims + added_count} input dims, got {a.meta.input_dims}"
            )
            ok = False
            continue
        reduced_counter: Counter[tuple[int, ...]] = Counter()
        for row in a.rows:
            reduced, added = _delete_access_added_coeffs(row, a.meta.output_dims, a.meta.input_dims, added_count, a.meta.param_dims)
            if any(added):
                notes.append(
                    f"statement {before.index}: access {idx} uses added tile iterators directly, row={row}"
                )
                ok = False
            reduced_counter[reduced] += 1
        if reduced_counter != Counter(b.rows):
            notes.append(f"statement {before.index}: access {idx} rows changed after removing added tile iterators")
            ok = False
    return ok, notes


def _check_pinstr_accesses(before: Statement, after: Statement, added_count: int) -> tuple[bool, list[str]]:
    return _check_accesses(before, after, added_count)


def _check_scattering_sanity(before: Statement, after: Statement, added_count: int) -> tuple[bool, list[str]]:
    notes: list[str] = []
    if before.scattering is None or after.scattering is None:
        return False, [f"statement {before.index}: missing scattering relation"]
    b = before.scattering
    a = after.scattering
    if a.meta.input_dims != b.meta.input_dims + added_count:
        return False, [
            f"statement {before.index}: scattering input dims {a.meta.input_dims} do not match before+added "
            f"({b.meta.input_dims}+{added_count})"
        ]
    if a.meta.output_dims < a.meta.input_dims:
        notes.append(
            f"statement {before.index}: scattering output dims {a.meta.output_dims} are fewer than "
            f"scattering input dims {a.meta.input_dims}"
        )
        return False, notes
    if any(row[0] != 0 for row in a.rows):
        notes.append(f"statement {before.index}: scattering contains non-equality rows")
        return False, notes
    if a.meta.output_dims < b.meta.output_dims:
        notes.append(
            f"statement {before.index}: after scattering compresses source-style separator dimensions "
            f"({b.meta.output_dims} -> {a.meta.output_dims})"
        )
    return True, notes


def _check_pinstr_schedule_sanity(before: Statement, after: Statement, added_count: int) -> tuple[bool, list[str]]:
    return _check_scattering_sanity(before, after, added_count)


def _check_pinstr_transformation_contract(
    original_iterators: list[str],
    tiled_iterators: list[str],
    added_iterators: list[str],
    links: list[TileLink],
    statement: int,
) -> tuple[bool, list[str]]:
    return _check_transformation_contract(original_iterators, tiled_iterators, added_iterators, links, statement)


def _row_satisfied(row: tuple[int, ...], values: dict[str, int], var_names: list[str], params: dict[str, int], param_names: list[str]) -> bool:
    total = 0
    coeffs = row[1 : 1 + len(var_names)]
    for name, coeff in zip(var_names, coeffs):
        total += coeff * values[name]
    pcoeffs = row[1 + len(var_names) : 1 + len(var_names) + len(param_names)]
    for name, coeff in zip(param_names, pcoeffs):
        total += coeff * params[name]
    total += row[-1]
    if row[0] == 0:
        return total == 0
    return total >= 0


def _infer_before_bounds(statement: Statement, params: dict[str, int]) -> dict[str, tuple[int, int]]:
    if statement.domain is None:
        raise ValidationError("missing before domain")
    var_names = statement.domain.output_names or statement.iterators
    bounds = {name: [0, max(params.values(), default=16)] for name in var_names}
    for row in statement.domain.rows:
        coeffs = row[1 : 1 + len(var_names)]
        nz = [(name, coeff) for name, coeff in zip(var_names, coeffs) if coeff != 0]
        if len(nz) != 1:
            continue
        name, coeff = nz[0]
        rest = 0
        pcoeffs = row[1 + len(var_names) : 1 + len(var_names) + len(statement.domain.param_names)]
        for pname, pcoeff in zip(statement.domain.param_names, pcoeffs):
            rest += pcoeff * params[pname]
        rest += row[-1]
        if row[0] != 1:
            continue
        if coeff > 0:
            lb = math.ceil((-rest) / coeff)
            bounds[name][0] = max(bounds[name][0], lb)
        elif coeff < 0:
            ub = math.floor(rest / (-coeff))
            bounds[name][1] = min(bounds[name][1], ub)
    final: dict[str, tuple[int, int]] = {}
    for name, (lb, ub) in bounds.items():
        if lb > ub:
            raise ValidationError(f"empty inferred bound for {name}: {lb}..{ub}")
        final[name] = (lb, ub)
    return final


def _check_bounded_coverage(
    before: Statement,
    after: Statement,
    links: list[TileLink],
    params: dict[str, int],
) -> tuple[bool, list[str]]:
    notes: list[str] = []
    if before.domain is None or after.domain is None:
        raise ValidationError("missing domain in bounded coverage")
    before_vars = before.domain.output_names or before.iterators
    after_vars = after.domain.output_names or after.iterators
    bounds = _infer_before_bounds(before, params)
    count = 0
    for point in itertools.product(*(range(bounds[name][0], bounds[name][1] + 1) for name in before_vars)):
        env = dict(zip(before_vars, point))
        if not all(_row_satisfied(row, env, before_vars, params, before.domain.param_names) for row in before.domain.rows):
            continue
        tiled_env = dict(env)
        pending = list(links)
        while pending:
            progress = False
            for link in list(pending):
                if not link.expr.dependencies().issubset(tiled_env.keys()):
                    continue
                expr_value = _evaluate_affine_expr(link.expr, tiled_env, params)
                tiled_env[link.parent] = expr_value // link.tile_size
                pending.remove(link)
                progress = True
            if not progress:
                unresolved = ", ".join(
                    f"{link.parent}=floor(({link.expr.render()})/{link.tile_size})" for link in pending
                )
                raise ValidationError(f"cannot resolve tile links during bounded coverage: {unresolved}")
        if not all(_row_satisfied(row, tiled_env, after_vars, params, after.domain.param_names) for row in after.domain.rows):
            notes.append(f"statement {before.index}: tiled lift failed for point {env}")
            return False, notes
        count += 1
    notes.append(f"statement {before.index}: checked bounded coverage on {count} original points")
    return True, notes


def _require_same_program_shape(before: Scop, after: Scop) -> None:
    if len(before.statements) != len(after.statements):
        raise ValidationError(
            f"statement count mismatch: before has {len(before.statements)}, after has {len(after.statements)}"
        )
    if before.params != after.params:
        raise ValidationError(f"parameter mismatch: before={before.params}, after={after.params}")
    for b_stmt, a_stmt in zip(before.statements, after.statements):
        if b_stmt.body and a_stmt.body and b_stmt.body != a_stmt.body:
            raise ValidationError(
                f"statement body mismatch for statement {b_stmt.index}: {b_stmt.body!r} vs {a_stmt.body!r}"
            )


def _canonical_statement_links(
    original_iterators: list[str], added_iterators: list[str], links: list[TileLink]
) -> list[TileLink]:
    return _canonicalize_links(links, original_iterators, added_iterators)


def _infer_statement_witness(before: Statement, after: Statement) -> StatementTilingWitness:
    if before.domain is None or after.domain is None:
        raise ValidationError(f"statement {before.index}: missing domain relation")
    before_vars = before.domain.output_names or before.iterators
    after_vars = after.domain.output_names or after.iterators
    base_ok, links_ok, links, notes = _check_domain_and_infer_links(before, after)
    if not base_ok or not links_ok:
        detail = "; ".join(notes) if notes else "unsupported tiling shape"
        raise ValidationError(f"statement {before.index}: cannot infer tiling witness: {detail}")
    added_count = len(after_vars) - len(before_vars)
    return StatementTilingWitness(
        statement=before.index,
        original_iterators=before_vars,
        tiled_iterators=after_vars,
        added_iterators=after_vars[:added_count],
        links=_canonical_statement_links(before_vars, after_vars[:added_count], links),
    )


def infer_tiling_witness(before_path: pathlib.Path, after_path: pathlib.Path) -> TilingWitness:
    before = parse_scop(before_path)
    after = parse_scop(after_path)
    _require_same_program_shape(before, after)
    return TilingWitness(
        before=str(before_path),
        after=str(after_path),
        params=before.params,
        statements=[_infer_statement_witness(b_stmt, a_stmt) for b_stmt, a_stmt in zip(before.statements, after.statements)],
    )


def _tile_link_from_dict(data: dict[str, object]) -> TileLink:
    expr = data["expr"]
    if not isinstance(expr, dict):
        raise ValidationError(f"bad tile-link expr payload: {expr!r}")
    return TileLink(
        parent=str(data["parent"]),
        tile_size=int(data["tile_size"]),
        expr=AffineExpr(
            var_coeffs=tuple((str(name), int(coeff)) for name, coeff in expr.get("var_coeffs", [])),
            param_coeffs=tuple((str(name), int(coeff)) for name, coeff in expr.get("param_coeffs", [])),
            const=int(expr.get("const", 0)),
        ),
    )


def _statement_witness_from_dict(data: dict[str, object]) -> StatementTilingWitness:
    raw_links = data.get("links", [])
    if not isinstance(raw_links, list):
        raise ValidationError(f"bad statement witness links payload: {raw_links!r}")
    return StatementTilingWitness(
        statement=int(data["statement"]),
        original_iterators=[str(item) for item in data.get("original_iterators", [])],
        tiled_iterators=[str(item) for item in data.get("tiled_iterators", [])],
        added_iterators=[str(item) for item in data.get("added_iterators", [])],
        links=_canonical_statement_links(
            [str(item) for item in data.get("original_iterators", [])],
            [str(item) for item in data.get("added_iterators", [])],
            [_tile_link_from_dict(item) for item in raw_links],
        ),
    )


def load_tiling_witness(path: pathlib.Path) -> TilingWitness:
    payload = json.loads(path.read_text())
    raw_statements = payload.get("statements", [])
    if not isinstance(raw_statements, list):
        raise ValidationError(f"bad witness statement payload: {raw_statements!r}")
    return TilingWitness(
        before=str(payload.get("before", "")),
        after=str(payload.get("after", "")),
        params=[str(item) for item in payload.get("params", [])],
        statements=[_statement_witness_from_dict(item) for item in raw_statements],
    )


def _check_witness_matches(
    before: Statement,
    after: Statement,
    witness: StatementTilingWitness,
    actual_links: list[TileLink],
) -> tuple[bool, list[str]]:
    notes: list[str] = []
    if before.domain is None or after.domain is None:
        raise ValidationError(f"statement {before.index}: missing domain relation")
    before_vars = before.domain.output_names or before.iterators
    after_vars = after.domain.output_names or after.iterators
    added_count = len(after_vars) - len(before_vars)
    ok = True

    if witness.statement != before.index:
        notes.append(f"statement {before.index}: witness statement id is {witness.statement}")
        ok = False
    if witness.original_iterators != before_vars:
        notes.append(
            f"statement {before.index}: witness original iterators {witness.original_iterators} "
            f"do not match actual {before_vars}"
        )
        ok = False
    if witness.tiled_iterators != after_vars:
        notes.append(
            f"statement {before.index}: witness tiled iterators {witness.tiled_iterators} "
            f"do not match actual {after_vars}"
        )
        ok = False
    if witness.added_iterators != after_vars[:added_count]:
        notes.append(
            f"statement {before.index}: witness added iterators {witness.added_iterators} "
            f"do not match actual {after_vars[:added_count]}"
        )
        ok = False
    if _canonical_statement_links(before_vars, after_vars[:added_count], witness.links) != _canonical_statement_links(
        before_vars, after_vars[:added_count], actual_links
    ):
        notes.append(f"statement {before.index}: witness tile links do not match inferred tile links")
        ok = False
    return ok, notes


def _check_pinstr_tiling(
    before: Statement,
    after: Statement,
    witness: StatementTilingWitness | None,
    params: dict[str, int],
    check_bounded_coverage: bool,
) -> StatementValidation:
    if before.domain is None or after.domain is None:
        raise ValidationError(f"statement {before.index}: missing domain relation")
    before_vars = before.domain.output_names or before.iterators
    after_vars = after.domain.output_names or after.iterators
    added_count = len(after_vars) - len(before_vars)
    shape_ok, shape_notes = _check_pinstr_shape(before, after)
    base_ok, links_ok, links, notes = _check_pinstr_links(before, after) if shape_ok else (False, False, [], [])
    notes = shape_notes + notes
    access_ok, access_notes = _check_pinstr_accesses(before, after, added_count)
    notes.extend(access_notes)
    schedule_ok, schedule_notes = _check_pinstr_schedule_sanity(before, after, added_count)
    notes.extend(schedule_notes)
    witness_ok = True
    coverage_links = links
    if witness is not None:
        witness_ok, witness_notes = _check_witness_matches(before, after, witness, links)
        notes.extend(witness_notes)
        coverage_links = _canonical_statement_links(before_vars, after_vars[:added_count], witness.links)
    transformation_ok, transformation_notes = _check_pinstr_transformation_contract(
        before_vars, after_vars, after_vars[:added_count], coverage_links, before.index
    )
    notes.extend(transformation_notes)
    compiled_relation_ok = (
        shape_ok
        and transformation_ok
        and base_ok
        and links_ok
        and access_ok
        and (witness is None or witness_ok)
    )
    bounded_ok: bool | None = None
    if check_bounded_coverage and compiled_relation_ok:
        bounded_ok, coverage_notes = _check_bounded_coverage(before, after, coverage_links, params)
        notes.extend(coverage_notes)

    return StatementValidation(
        statement=before.index,
        original_iterators=before_vars,
        tiled_iterators=after_vars,
        added_iterators=after_vars[:added_count],
        links=coverage_links,
        shape_ok=shape_ok,
        transformation_contract_ok=transformation_ok,
        witness_match_ok=witness_ok,
        base_domain_ok=base_ok,
        link_rows_ok=links_ok,
        access_ok=access_ok,
        compiled_relation_ok=compiled_relation_ok,
        schedule_sanity_ok=schedule_ok,
        bounded_coverage_ok=bounded_ok,
        notes=notes,
    )


def _parse_param_assignments(raw: list[str]) -> dict[str, int]:
    params: dict[str, int] = {}
    for item in raw:
        if "=" not in item:
            raise ValidationError(f"bad parameter assignment {item!r}, expected NAME=VALUE")
        name, value = item.split("=", 1)
        params[name] = int(value)
    return params


def check_tiling_witness(
    before_path: pathlib.Path,
    after_path: pathlib.Path,
    witness: TilingWitness,
    params: dict[str, int],
    check_bounded_coverage: bool,
) -> ValidationReport:
    before = parse_scop(before_path)
    after = parse_scop(after_path)
    _require_same_program_shape(before, after)
    if witness.params != before.params:
        raise ValidationError(f"witness parameter mismatch: witness={witness.params}, program={before.params}")
    if len(witness.statements) != len(before.statements):
        raise ValidationError(
            f"witness statement count mismatch: witness has {len(witness.statements)}, program has {len(before.statements)}"
        )

    if check_bounded_coverage:
        missing = [name for name in before.params if name not in params]
        if missing:
            raise ValidationError(f"missing parameter assignments for bounded coverage: {missing}")

    results: list[StatementValidation] = []
    for b_stmt, a_stmt, w_stmt in zip(before.statements, after.statements, witness.statements):
        results.append(_check_pinstr_tiling(b_stmt, a_stmt, w_stmt, params, check_bounded_coverage))

    ok = all(
        item.compiled_relation_ok
        and item.schedule_sanity_ok
        and item.witness_match_ok
        and (item.bounded_coverage_ok in {None, True})
        for item in results
    )
    return ValidationReport(
        before=str(before_path),
        after=str(after_path),
        params=params,
        ok=ok,
        witness_source="provided",
        statements=results,
        limitations=[
            "prototype only targets Pluto-style affine floor-link tiling constraints",
            "transformation checking currently validates only the ordered-link contract needed by inserted-after-env lifting",
            "schedule checking is only a sanity check on arity growth, not a full schedule-proof",
            "ISS, statement splitting, and parallel codegen are out of scope",
            "bounded coverage uses explicit parameter assignments and deterministic tile reconstruction",
        ],
    )


def validate_tiling(before_path: pathlib.Path, after_path: pathlib.Path, params: dict[str, int], check_bounded_coverage: bool) -> ValidationReport:
    witness = infer_tiling_witness(before_path, after_path)
    report = check_tiling_witness(before_path, after_path, witness, params, check_bounded_coverage)
    report.witness_source = "inferred"
    return report


def render_tiling_witness(witness: TilingWitness) -> str:
    lines = [
        f"before: {witness.before}",
        f"after:  {witness.after}",
        f"params: {witness.params}",
    ]
    for stmt in witness.statements:
        lines.append(f"\nstatement {stmt.statement}:")
        lines.append(f"  original iterators: {stmt.original_iterators}")
        lines.append(f"  tiled iterators:    {stmt.tiled_iterators}")
        if stmt.added_iterators:
            lines.append(f"  added iterators:    {stmt.added_iterators}")
        for link in stmt.links:
            lines.append(f"  tile link: {link.parent} = floor(({link.expr.render()}) / {link.tile_size})")
    return "\n".join(lines)


def render_validation_report(report: ValidationReport) -> str:
    lines = [
        f"before: {report.before}",
        f"after:  {report.after}",
        f"overall: {'PASS' if report.ok else 'FAIL'}",
        f"witness: {report.witness_source}",
    ]
    if report.params:
        lines.append(f"params: {report.params}")
    for stmt in report.statements:
        lines.append(
            f"\nstatement {stmt.statement}: "
            f"shape={stmt.shape_ok} "
            f"transformation_contract={stmt.transformation_contract_ok} "
            f"witness_match={stmt.witness_match_ok} "
            f"base_domain={stmt.base_domain_ok} "
            f"links={stmt.link_rows_ok} "
            f"access={stmt.access_ok} "
            f"compiled_relation={stmt.compiled_relation_ok} "
            f"schedule_sanity={stmt.schedule_sanity_ok} "
            f"bounded_coverage={stmt.bounded_coverage_ok}"
        )
        lines.append(f"  original iterators: {stmt.original_iterators}")
        lines.append(f"  tiled iterators:    {stmt.tiled_iterators}")
        if stmt.added_iterators:
            lines.append(f"  added iterators:    {stmt.added_iterators}")
        for link in stmt.links:
            lines.append(f"  tile link: {link.parent} = floor(({link.expr.render()}) / {link.tile_size})")
        for note in stmt.notes:
            lines.append(f"  note: {note}")
    lines.append("\nlimitations:")
    for item in report.limitations:
        lines.append(f"  - {item}")
    return "\n".join(lines)


def _main_validate(args: argparse.Namespace) -> int:
    try:
        report = validate_tiling(
            args.before,
            args.after,
            _parse_param_assignments(args.param),
            args.check_bounded_coverage,
        )
    except ValidationError as exc:
        if args.json:
            print(json.dumps({"ok": False, "error": str(exc)}, indent=2, sort_keys=True))
        else:
            print(f"[tiling-validate] ERROR: {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(asdict(report), indent=2, sort_keys=True))
    else:
        print(render_validation_report(report))
    return 0 if report.ok else 2


def _main_extract(args: argparse.Namespace) -> int:
    try:
        witness = infer_tiling_witness(args.before, args.after)
    except ValidationError as exc:
        if args.json:
            print(json.dumps({"ok": False, "error": str(exc)}, indent=2, sort_keys=True))
        else:
            print(f"[tiling-extract] ERROR: {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(asdict(witness), indent=2, sort_keys=True))
    else:
        print(render_tiling_witness(witness))
    return 0


def _main_check(args: argparse.Namespace) -> int:
    try:
        witness = load_tiling_witness(args.witness)
        report = check_tiling_witness(
            args.before,
            args.after,
            witness,
            _parse_param_assignments(args.param),
            args.check_bounded_coverage,
        )
    except ValidationError as exc:
        if args.json:
            print(json.dumps({"ok": False, "error": str(exc)}, indent=2, sort_keys=True))
        else:
            print(f"[tiling-check] ERROR: {exc}", file=sys.stderr)
        return 1

    if args.json:
        print(json.dumps(asdict(report), indent=2, sort_keys=True))
    else:
        print(render_validation_report(report))
    return 0 if report.ok else 2


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Prototype tooling for Pluto-style tiling witnesses and validation.")
    subparsers = parser.add_subparsers(dest="command")

    validate_parser = subparsers.add_parser("validate", help="infer a tiling witness and validate it against before/after OpenScop")
    validate_parser.add_argument("before", type=pathlib.Path)
    validate_parser.add_argument("after", type=pathlib.Path)
    validate_parser.add_argument("--param", action="append", default=[])
    validate_parser.add_argument("--check-bounded-coverage", action="store_true")
    validate_parser.add_argument("--json", action="store_true")

    extract_parser = subparsers.add_parser("extract", help="extract an inferred tiling witness from before/after OpenScop")
    extract_parser.add_argument("before", type=pathlib.Path)
    extract_parser.add_argument("after", type=pathlib.Path)
    extract_parser.add_argument("--json", action="store_true")

    check_parser = subparsers.add_parser("check", help="check a provided tiling witness against before/after OpenScop")
    check_parser.add_argument("before", type=pathlib.Path)
    check_parser.add_argument("after", type=pathlib.Path)
    check_parser.add_argument("witness", type=pathlib.Path)
    check_parser.add_argument("--param", action="append", default=[])
    check_parser.add_argument("--check-bounded-coverage", action="store_true")
    check_parser.add_argument("--json", action="store_true")
    return parser


def _rewrite_legacy_args(argv: list[str]) -> list[str]:
    if not argv:
        return argv
    if argv[0] in {"validate", "extract", "check", "-h", "--help"}:
        return argv
    return ["validate", *argv]


def main(argv: list[str] | None = None) -> int:
    raw_argv = list(sys.argv[1:] if argv is None else argv)
    parser = build_arg_parser()
    args = parser.parse_args(_rewrite_legacy_args(raw_argv))
    if args.command == "extract":
        return _main_extract(args)
    if args.command == "check":
        return _main_check(args)
    return _main_validate(args)


if __name__ == "__main__":
    raise SystemExit(main())
