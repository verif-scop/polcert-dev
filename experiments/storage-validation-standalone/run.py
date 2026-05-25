#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, Iterable, List, Sequence, Tuple
import argparse
from pathlib import Path


class ValidationError(Exception):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def same_dict(lhs: Dict, rhs: Dict, name: str) -> None:
    require(lhs == rhs, f"{name} differs: {lhs!r} != {rhs!r}")


@dataclass(frozen=True)
class Case:
    name: str
    kind: str
    source: str
    target: str
    validator: Callable[[], List[str]]


@dataclass(frozen=True)
class NegativeTest:
    name: str
    related_case: str
    validator: Callable[[], None]


CASES: List[Case] = []
NEGATIVE_TESTS: List[NegativeTest] = []


def add_case(name: str, kind: str, source: str, target: str):
    def wrap(fn: Callable[[], List[str]]) -> Callable[[], List[str]]:
        CASES.append(Case(name, kind, source.strip(), target.strip(), fn))
        return fn

    return wrap


def add_negative(name: str, related_case: str):
    def wrap(fn: Callable[[], None]) -> Callable[[], None]:
        NEGATIVE_TESTS.append(NegativeTest(name, related_case, fn))
        return fn

    return wrap


@add_case(
    "source_no_alias_abstraction",
    "precondition / logical blocks distinct",
    """
for (i = 0; i < N; i++)
  A[i] = B[i] + 1;
""",
    """
for (i = 0; i < N; i++)
  A[i] = B[i] + 1;
""",
)
def validate_source_no_alias_abstraction() -> List[str]:
    n = 4
    logical_blocks = {"A": "base_A", "B": "base_B"}
    require(logical_blocks["A"] != logical_blocks["B"], "A and B may alias")

    read_cells = {("B", i) for i in range(n)}
    write_cells = {("A", i) for i in range(n)}
    require(read_cells.isdisjoint(write_cells), "logical read/write cells overlap")

    b = {i: 10 + i for i in range(n)}
    a = {i: 0 for i in range(n)}
    for i in range(n):
        a[i] = b[i] + 1
    require(a == {i: 11 + i for i in range(n)}, "logical execution mismatch")
    return [
        "distinct source names are interpreted as distinct logical blocks",
        "logical read/write footprints are computed under the no-alias abstraction",
        "validator assumptions would be unsound if A and B had the same physical base",
    ]


@add_case(
    "affine_interchange",
    "instance-preserving / storage-preserving",
    """
for (i = 0; i < N; i++)
  for (j = 0; j < M; j++)
    B[i][j] = A[i][j] + 1;
""",
    """
for (j = 0; j < M; j++)
  for (i = 0; i < N; i++)
    B[i][j] = A[i][j] + 1;
""",
)
def validate_affine_interchange() -> List[str]:
    n, m = 3, 4
    domain = {(i, j) for i in range(n) for j in range(m)}
    source_instances = list((i, j) for i in range(n) for j in range(m))
    target_instances = list((i, j) for j in range(m) for i in range(n))
    require(set(source_instances) == domain, "source domain is wrong")
    require(set(target_instances) == domain, "target domain is wrong")
    require(len(target_instances) == len(domain), "target duplicates an instance")

    a = {(i, j): 10 * i + j for i, j in domain}
    source_b: Dict[Tuple[int, int], int] = {}
    target_b: Dict[Tuple[int, int], int] = {}
    for i, j in source_instances:
        source_b[i, j] = a[i, j] + 1
    for i, j in target_instances:
        target_b[i, j] = a[i, j] + 1
    same_dict(source_b, target_b, "B")
    return [
        "bijection on statement instances",
        "read/write access functions are identical",
        "no loop-carried dependences are introduced or reordered",
    ]


@add_case(
    "index_set_splitting",
    "instance-preserving / domain partition",
    """
for (i = 0; i < N; i++)
  if (i < K) B[i] = A[i] + 1;
  else       B[i] = A[i] + 2;
""",
    """
for (i = 0; i < K; i++)
  B[i] = A[i] + 1;
for (i = K; i < N; i++)
  B[i] = A[i] + 2;
""",
)
def validate_index_set_splitting() -> List[str]:
    n, k = 7, 3
    source = set(range(n))
    low = {i for i in range(k)}
    high = {i for i in range(k, n)}
    require(low.isdisjoint(high), "ISS partitions overlap")
    require(low | high == source, "ISS partitions do not cover the domain")

    a = {i: i * 3 for i in source}
    source_b = {i: a[i] + (1 if i < k else 2) for i in source}
    target_b = {i: a[i] + 1 for i in low}
    target_b.update({i: a[i] + 2 for i in high})
    same_dict(source_b, target_b, "B")
    return [
        "target subdomains are disjoint",
        "target subdomains exactly cover the source domain",
        "each target substatement projects to exactly one source instance",
    ]


@add_case(
    "ordinary_tiling",
    "instance-preserving / grouped schedule",
    """
for (i = 0; i < N; i++)
  for (j = 0; j < M; j++)
    B[i][j] = A[i][j] + 1;
""",
    """
for (ii = 0; ii < N; ii += T)
  for (jj = 0; jj < M; jj += T)
    for (i = ii; i < min(ii + T, N); i++)
      for (j = jj; j < min(jj + T, M); j++)
        B[i][j] = A[i][j] + 1;
""",
)
def validate_ordinary_tiling() -> List[str]:
    n, m, tile = 5, 4, 2
    domain = {(i, j) for i in range(n) for j in range(m)}
    projected: List[Tuple[int, int]] = []
    for ii in range(0, n, tile):
        for jj in range(0, m, tile):
            for i in range(ii, min(ii + tile, n)):
                for j in range(jj, min(jj + tile, m)):
                    require(0 <= i < n and 0 <= j < m, "tile generates out-of-domain instance")
                    projected.append((i, j))
    require(set(projected) == domain, "tile loops do not cover source domain")
    require(len(projected) == len(domain), "tile loops duplicate source instances")
    return [
        "tile projection covers every source instance",
        "tile projection is injective for ordinary non-overlapped tiling",
        "access functions are unchanged",
    ]


@add_case(
    "scalar_privatization_expansion",
    "same instances / scalar storage expansion",
    """
for (i = 0; i < N; i++) {
  tmp = A[i] + 1;
  B[i] = tmp * 2;
}
""",
    """
for (i = 0; i < N; i++) {
  tmp_exp[i] = A[i] + 1;
  B[i] = tmp_exp[i] * 2;
}
""",
)
def validate_scalar_privatization_expansion() -> List[str]:
    n = 6
    a = {i: 7 + i for i in range(n)}

    tmp = None
    source_b: Dict[int, int] = {}
    for i in range(n):
        tmp = a[i] + 1
        source_b[i] = tmp * 2

    tmp_exp: Dict[int, int] = {}
    target_b: Dict[int, int] = {}
    writes = set()
    reads = []
    for i in range(n):
        tmp_exp[i] = a[i] + 1
        writes.add(("tmp_exp", i))
        require(("tmp_exp", i) in writes, f"tmp_exp[{i}] read before write")
        reads.append(("tmp_exp", i))
        target_b[i] = tmp_exp[i] * 2

    require(len(writes) == n, "private cells are not fresh per iteration")
    require(all(r in writes for r in reads), "a private read has no matching private write")
    same_dict(source_b, target_b, "B")
    return [
        "private storage map rho(i) = tmp_exp[i] is injective over live private classes",
        "each private read is dominated by its same-class write",
        "expanded storage is not live-out or observable except through B",
    ]


@add_case(
    "private_copy_boundary",
    "same instances / private live-in and live-out boundary copies",
    """
for (i = 0; i < N; i++) {
  B[i] = seed + A[i];  // seed is live-in to the privatized region
  tmp = A[i];          // tmp is live-out after the loop
}
C = tmp;
""",
    """
for (i = 0; i < N; i++) {
  seed_priv[i] = seed;     // copy-in
  B[i] = seed_priv[i] + A[i];
  tmp_priv[i] = A[i];
}
tmp = tmp_priv[N - 1];     // unique live-out copy-out
C = tmp;
""",
)
def validate_private_copy_boundary() -> List[str]:
    n = 5
    a = {i: 10 + i for i in range(n)}
    seed = 3

    source_b: Dict[int, int] = {}
    tmp = None
    for i in range(n):
        source_b[i] = seed + a[i]
        tmp = a[i]
    source_c = tmp

    private_cells = {("seed_priv", i) for i in range(n)}
    private_cells |= {("tmp_priv", i) for i in range(n)}
    public_liveins = {"seed"}
    public_liveouts = {"tmp"}
    copyins = [("seed", ("seed_priv", i)) for i in range(n)]
    copyouts = [("tmp", ("tmp_priv", n - 1))]

    require(public_liveins <= {public for public, _private in copyins},
            "private live-in has no copy-in")
    require(public_liveouts <= {public for public, _private in copyouts},
            "private live-out has no copy-out")
    require({private for _public, private in copyins} <= private_cells,
            "copy-in does not target declared private cells")
    require({private for _public, private in copyouts} <= private_cells,
            "copy-out does not read declared private cells")
    copyin_privates = [private for _public, private in copyins]
    copyout_privates = [private for _public, private in copyouts]
    require(len(copyin_privates) == len(set(copyin_privates)),
            "private copy-in target is not unique")
    require(len(copyout_privates) == len(set(copyout_privates)),
            "private copy-out source is not unique")
    copyout_publics = [public for public, _private in copyouts]
    require(len(copyout_publics) == len(set(copyout_publics)),
            "private live-out copy-out is not unique")
    copyin_values = [(pair, seed, seed) for pair in copyins]
    copyout_values = [(copyouts[0], a[n - 1], a[n - 1])]
    require(all(public_value == private_value
                for _pair, public_value, private_value in copyin_values),
            "copy-in boundary value mismatch")
    require(all(public_value == private_value
                for _pair, public_value, private_value in copyout_values),
            "copy-out boundary value mismatch")
    public_specs = {
        "seed": (8, 8),
        "tmp": (8, 8),
    }
    private_specs = {
        **{("seed_priv", i): (8, 8) for i in range(n)},
        **{("tmp_priv", i): (8, 8) for i in range(n)},
    }
    boundary_pairs = copyins + copyouts
    require(all(public_specs[public] == private_specs[private]
                for public, private in boundary_pairs),
            "private boundary storage spec mismatch")

    target_b: Dict[int, int] = {}
    seed_priv: Dict[int, int] = {}
    tmp_priv: Dict[int, int] = {}
    for i in range(n):
        seed_priv[i] = seed
        target_b[i] = seed_priv[i] + a[i]
        tmp_priv[i] = a[i]
    target_c = tmp_priv[n - 1]

    same_dict(source_b, target_b, "B")
    require(source_c == target_c, "private live-out copy-out commits wrong value")
    return [
        "every required public live-in has a copy-in boundary pair",
        "every required public live-out has a unique copy-out boundary pair",
        "boundary pairs use declared private storage cells",
        "boundary copy private cells are unique on the private side",
        "copy-in/copy-out boundary values match across public and private cells",
        "boundary public/private cells are storage-compatible for copy-in and copy-out",
    ]


@add_case(
    "layout_remap_padding",
    "same instances / injective physical address remap",
    """
for (i = 0; i < N; i++)
  for (j = 0; j < M; j++)
    B[i][j] = A[i][j] + 1;
""",
    """
double A_pad[N][M + 1];
#define A_LOG(i, j) A_pad[i][j]
for (i = 0; i < N; i++)
  for (j = 0; j < M; j++)
    B[i][j] = A_LOG(i, j) + 1;

/* transpose-style layout variant */
#define A_T_LOG(i, j) A_t[j][i]
for (i = 0; i < N; i++)
  for (j = 0; j < M; j++)
    B[i][j] = A_T_LOG(i, j) + 1;

/* affine linearized layout variant */
#define A_LIN_LOG(i, j) A_lin[(i) * M + (j)]
for (i = 0; i < N; i++)
  for (j = 0; j < M; j++)
    B[i][j] = A_LIN_LOG(i, j) + 1;
""",
)
def validate_layout_remap_padding() -> List[str]:
    n, m = 3, 4
    domain = {(i, j) for i in range(n) for j in range(m)}
    pad_stride = m + 1
    pad_map = {(i, j): i * pad_stride + j for i, j in domain}
    transpose_map = {(i, j): j * n + i for i, j in domain}
    linearized_map = {(i, j): i * m + j for i, j in domain}

    for name, rho, size in [
        ("padding", pad_map, n * pad_stride),
        ("transpose", transpose_map, n * m),
        ("linearized", linearized_map, n * m),
    ]:
        require(len(set(rho.values())) == len(domain), f"{name} layout map is not injective")
        require(all(0 <= p < size for p in rho.values()), f"{name} layout map is out of bounds")

    padding_cells = {i * pad_stride + m for i in range(n)}
    require(set(pad_map.values()).isdisjoint(padding_cells), "logical accesses reach padding cells")
    declared_layouts = {
        ("A_pad", "A"): ("same", None),
        ("A_t", "A"): ("permutation", (1, 0)),
        ("A_lin", "A"): ("affine", lambda source_index: (source_index[0] * m + source_index[1],)),
    }

    def declared_access_remap_ok(
        target_array: str,
        target_index: Tuple[str, ...],
        source_array: str,
        source_index: Tuple[str, ...],
    ) -> bool:
        if target_array == source_array and target_index == source_index:
            return True
        declaration = declared_layouts.get((target_array, source_array))
        if declaration is None:
            return False
        kind, payload = declaration
        if kind == "same":
            return target_index == source_index
        if kind == "affine":
            affine_layout = payload
            return target_index == affine_layout(source_index)
        require(kind == "permutation", f"unknown declared layout kind: {kind}")
        permutation = payload
        if any(index >= len(source_index) for index in permutation):
            return False
        return target_index == tuple(source_index[index] for index in permutation)

    access_pairs = [
        (("read", "A_pad", ("i", "j")), ("read", "A", ("i", "j"))),
        (("write", "B", ("i", "j")), ("write", "B", ("i", "j"))),
    ]
    transpose_access_pairs = [
        (("read", "A_t", ("j", "i")), ("read", "A", ("i", "j"))),
        (("write", "B", ("i", "j")), ("write", "B", ("i", "j"))),
    ]
    affine_access_pairs = [
        (
            ("read", "A_lin", lambda i, j: (i * m + j,)),
            ("read", "A", lambda i, j: (i, j)),
        ),
    ]
    require(all(target_kind == source_kind
                for (target_kind, _target_array, _target_index),
                    (source_kind, _source_array, _source_index) in access_pairs),
            "layout access remap changes access kind")
    require(all(declared_access_remap_ok(target_array, target_index, source_array, source_index)
                for (_target_kind, target_array, target_index),
                    (_source_kind, source_array, source_index) in access_pairs),
            "target access does not use declared layout rename")
    require(all(target_kind == source_kind
                for (target_kind, _target_array, _target_index),
                    (source_kind, _source_array, _source_index) in transpose_access_pairs),
            "permutation layout access remap changes access kind")
    require(all(declared_access_remap_ok(target_array, target_index, source_array, source_index)
                for (_target_kind, target_array, target_index),
                    (_source_kind, source_array, source_index) in transpose_access_pairs),
            "target access does not use declared index permutation")
    for (target_kind, _target_array, target_index_fn), (
        source_kind,
        _source_array,
        source_index_fn,
    ) in affine_access_pairs:
        require(target_kind == source_kind, "affine layout access remap changes access kind")
        for i, j in domain:
            source_index = source_index_fn(i, j)
            target_index = target_index_fn(i, j)
            require(declared_access_remap_ok("A_lin", target_index, "A", source_index),
                    "target access does not use declared affine layout")

    logical_a = {(i, j): 10 * i + j for i, j in domain}
    phys = {pad_map[i, j]: logical_a[i, j] for i, j in domain}
    transpose_phys = {transpose_map[i, j]: logical_a[i, j] for i, j in domain}
    linearized_phys = {linearized_map[i, j]: logical_a[i, j] for i, j in domain}
    layout_value_entries = [
        ((i, j), pad_map[i, j], logical_a[i, j], phys[pad_map[i, j]])
        for i, j in sorted(domain)
    ]
    require(all(source_value == target_value
                for _source_cell, _target_cell, source_value, target_value
                in layout_value_entries),
            "layout boundary value mismatch")
    logical_specs = {("A", i, j): (8, 8) for i, j in domain}
    physical_specs = {
        ("A_pad", pad_map[i, j]): (8, 8) for i, j in domain
    }
    physical_specs.update({
        ("A_t", transpose_map[i, j]): (8, 8) for i, j in domain
    })
    physical_specs.update({
        ("A_lin", linearized_map[i, j]): (8, 8) for i, j in domain
    })
    storage_mappings = [
        (("A", i, j), ("A_pad", pad_map[i, j]))
        for i, j in sorted(domain)
    ]
    storage_mappings.extend(
        (("A", i, j), ("A_t", transpose_map[i, j]))
        for i, j in sorted(domain)
    )
    storage_mappings.extend(
        (("A", i, j), ("A_lin", linearized_map[i, j]))
        for i, j in sorted(domain)
    )
    require(all(logical_specs[source_cell] == physical_specs[target_cell]
                for source_cell, target_cell in storage_mappings),
            "layout storage spec mismatch")
    target_b = {(i, j): phys[pad_map[i, j]] + 1 for i, j in domain}
    transpose_target_b = {
        (i, j): transpose_phys[transpose_map[i, j]] + 1 for i, j in domain
    }
    linearized_target_b = {
        (i, j): linearized_phys[linearized_map[i, j]] + 1 for i, j in domain
    }
    source_b = {(i, j): logical_a[i, j] + 1 for i, j in domain}
    same_dict(source_b, target_b, "B")
    same_dict(source_b, transpose_target_b, "B under transpose layout")
    same_dict(source_b, linearized_target_b, "B under affine linearized layout")
    return [
        "logical-to-physical address map is injective over the logical domain",
        "all rewritten addresses are within allocated physical storage",
        "padding cells are outside the observable logical image",
        "target accesses use the declared layout rename at the access-function level",
        "transpose-style accesses use a declared index-permutation layout witness",
        "linearized accesses use a declared affine layout witness",
        "one declared-layout checker covers same-index, permutation, and affine cases",
        "layout boundary values match the represented logical cells",
        "mapped physical layout cells are storage-compatible with represented logical cells",
    ]


@add_case(
    "scratchpad_packing",
    "same instances / copy-mediated local storage",
    """
for (i = 0; i < N; i++)
  C[i] = A[i] + B[i];
""",
    """
for (kk = 0; kk < N; kk += T) {
  for (k = 0; k < T; k++)
    Bp[k] = B[kk + k];
  for (k = 0; k < T; k++)
    C[kk + k] = A[kk + k] + Bp[k];
}
""",
)
def validate_scratchpad_packing() -> List[str]:
    n, tile = 8, 4
    a = {i: i for i in range(n)}
    b = {i: 100 + i for i in range(n)}
    source_c = {i: a[i] + b[i] for i in range(n)}

    target_c: Dict[int, int] = {}
    for kk in range(0, n, tile):
        bp: Dict[int, int] = {}
        local_mapping = {("Bp", k): ("B", kk + k) for k in range(tile)}
        public_specs = {("B", kk + k): (8, 8) for k in range(tile)}
        local_specs = {("Bp", k): (8, 8) for k in range(tile)}
        require(len(set(local_mapping.keys())) == len(local_mapping),
                "local buffer cells are not injective")
        require(len(set(local_mapping.values())) == len(local_mapping),
                "public cells mapped to local buffer are not injective")
        require(all(public_specs[public] == local_specs[local]
                    for local, public in local_mapping.items()),
                "scratchpad local storage spec mismatch")
        copy_events = set()
        for k in range(tile):
            require(local_mapping[("Bp", k)] == ("B", kk + k),
                    "copy-in does not match the declared local remap")
            bp[k] = b[kk + k]
            copy_events.add(k)
        for k in range(tile):
            require(k in copy_events, f"Bp[{k}] used before copy-in")
            require(local_mapping[("Bp", k)] == ("B", kk + k),
                    "local read does not match the declared local remap")
            target_c[kk + k] = a[kk + k] + bp[k]

    same_dict(source_c, target_c, "C")
    return [
        "copy-in covers every later local read",
        "local buffer address k consistently maps to source B[kk+k]",
        "public-to-local copy mapping is injective during each tile",
        "local buffer cells are storage-compatible with represented public cells",
        "local buffer lifetime is tile-scoped and fresh between tiles",
    ]


@add_case(
    "scratchpad_copy_out",
    "same instances / copy-mediated local update plus commit",
    """
for (i = 0; i < N; i++)
  A[i] = A[i] + 1;
""",
    """
for (kk = 0; kk < N; kk += T) {
  for (k = 0; k < T; k++)
    Al[k] = A[kk + k];
  for (k = 0; k < T; k++)
    Al[k] = Al[k] + 1;
  for (k = 0; k < T; k++)
    A[kk + k] = Al[k];
}
""",
)
def validate_scratchpad_copy_out() -> List[str]:
    n, tile = 8, 4
    source_a = {i: 10 + i for i in range(n)}
    for i in range(n):
        source_a[i] = source_a[i] + 1

    target_a = {i: 10 + i for i in range(n)}
    committed = set()
    copy_instance_trace: List[Tuple[str, str, int]] = []
    for kk in range(0, n, tile):
        al: Dict[int, int] = {}
        copied = set()
        for k in range(tile):
            al[k] = target_a[kk + k]
            copied.add(k)
            copy_instance_trace.append(("Internal", "CopyIn", kk + k))
        for k in range(tile):
            require(k in copied, f"Al[{k}] used before copy-in")
            al[k] = al[k] + 1
            copy_instance_trace.append(("Internal", "LocalWrite", kk + k))
        for k in range(tile):
            target_a[kk + k] = al[k]
            committed.add(kk + k)
            copy_instance_trace.append(("Commit", "CopyOut", kk + k))

    require(committed == set(range(n)), "copy-out does not commit every logical output")
    expected_role = {
        "CopyIn": "Internal",
        "LocalRead": "Internal",
        "LocalWrite": "Internal",
        "CopyOut": "Commit",
    }
    require(all(role == expected_role[event]
                for role, event, _source_instance in copy_instance_trace),
            "copy helper instance role does not match copy event")
    commit_sources = {
        source_instance
        for role, _event, source_instance in copy_instance_trace
        if role == "Commit"
    }
    require(commit_sources == set(range(n)),
            "commit-role copy helpers do not cover source live-outs")
    same_dict(source_a, target_a, "A")
    return [
        "copy-in initializes each local cell before local compute",
        "copy-out commits every updated logical cell exactly once",
        "copy helper instance roles align with copy protocol events",
        "local writes are unobservable until committed",
    ]


@add_case(
    "scalar_promotion",
    "same instances / array cell simulated by scalar",
    """
for (i = 0; i < N; i++) {
  A[i] = A[i] + 1;
  B[i] = A[i] * 2;
}
""",
    """
for (i = 0; i < N; i++) {
  s = A[i];
  s = s + 1;
  A[i] = s;
  B[i] = s * 2;
}
""",
)
def validate_scalar_promotion() -> List[str]:
    n = 5
    source_a = {i: 10 + i for i in range(n)}
    target_a = dict(source_a)
    source_b: Dict[int, int] = {}
    target_b: Dict[int, int] = {}

    for i in range(n):
        source_a[i] = source_a[i] + 1
        source_b[i] = source_a[i] * 2

    for i in range(n):
        entry = target_a[i]
        s = entry
        s = s + 1
        target_a[i] = s
        target_b[i] = s * 2
        require(target_a[i] == entry + 1, "promoted scalar does not simulate the write")

    same_dict(source_a, target_a, "A")
    same_dict(source_b, target_b, "B")
    promoted_source = ("A", "i")
    promoted_scalar = ("s",)
    logical_specs = {promoted_source: (8, 8)}
    scalar_specs = {promoted_scalar: (8, 8)}
    require(logical_specs[promoted_source] == scalar_specs[promoted_scalar],
            "promoted scalar storage spec mismatch")
    return [
        "entry load initializes the scalar from the promoted cell",
        "all reads and writes in the promoted region are simulated by the scalar",
        "promoted scalar storage is compatible with the source cell",
        "exit store commits the scalar back before the cell is observed",
    ]


@add_case(
    "array_contraction",
    "same logical values / non-injective conflict-safe storage reuse",
    """
for (t = 1; t <= T; t++)
  for (i = 0; i < N; i++)
    A[t][i] = A[t - 1][i] + 1;
""",
    """
for (t = 1; t <= T; t++)
  for (i = 0; i < N; i++)
    A2[t % 2][i] = A2[(t - 1) % 2][i] + 1;
""",
)
def validate_array_contraction() -> List[str]:
    t_max, n = 6, 4
    init = {i: i for i in range(n)}

    full: Dict[Tuple[int, int], int] = {(0, i): init[i] for i in range(n)}
    for t in range(1, t_max + 1):
        for i in range(n):
            full[t, i] = full[t - 1, i] + 1

    buf = {(0, i): init[i] for i in range(n)}
    for i in range(n):
        buf[1, i] = -999
    for t in range(1, t_max + 1):
        for i in range(n):
            buf[t % 2, i] = buf[(t - 1) % 2, i] + 1
    final = {i: buf[t_max % 2, i] for i in range(n)}
    expected = {i: full[t_max, i] for i in range(n)}
    same_dict(expected, final, "final A")

    def phys(value: Tuple[int, int]) -> Tuple[int, int]:
        t, i = value
        return (t % 2, i)

    def live_range(value: Tuple[int, int]) -> Tuple[int, int]:
        t, _ = value
        return (t, t + 1)

    values = [(t, i) for t in range(t_max + 1) for i in range(n)]
    conflicts = set()
    for idx, v1 in enumerate(values):
        for v2 in values[idx + 1 :]:
            l1, r1 = live_range(v1)
            l2, r2 = live_range(v2)
            if l1 < r2 and l2 < r1:
                conflicts.add((v1, v2))

    for idx, v1 in enumerate(values):
        for v2 in values[idx + 1 :]:
            l1, r1 = live_range(v1)
            l2, r2 = live_range(v2)
            if l1 < r2 and l2 < r1:
                require((v1, v2) in conflicts or (v2, v1) in conflicts,
                        f"live-overlap conflict missing for {v1} and {v2}")

    for v1, v2 in conflicts:
        require(phys(v1) != phys(v2),
                f"conflicting values {v1} and {v2} share {phys(v1)}")

    source_liveouts = {(t_max, i) for i in range(n)}
    boundary_mapping = {source_cell: phys(source_cell) for source_cell in source_liveouts}
    require(set(boundary_mapping.keys()) == source_liveouts,
            "reuse boundary mapping does not cover every source live-out")
    logical_specs = {source_cell: (8, 8) for source_cell in source_liveouts}
    physical_specs = {phys(source_cell): (8, 8) for source_cell in source_liveouts}
    require(all(logical_specs[source_cell] == physical_specs[target_cell]
                for source_cell, target_cell in boundary_mapping.items()),
            "reuse boundary storage spec mismatch")
    require(all(buf[target_cell] == full[source_cell]
                for source_cell, target_cell in boundary_mapping.items()),
            "reuse boundary cell value does not match source live-out")

    return [
        "non-injective map rho(t,i) = (t mod 2,i) is allowed only for non-conflicting values",
        "explicit live intervals cover every overlap conflict under the schedule",
        "reuse boundary mapping covers every observable source live-out",
        "reused physical boundary cells are storage-compatible with represented logical cells",
        "reuse boundary values match the projected physical cells",
        "final observable row projects from the correct parity buffer",
    ]


@add_case(
    "inter_array_reuse",
    "same instances / cross-array lifetime-based storage reuse",
    """
for (i = 0; i < N; i++) T1[i] = A[i] + 1;
for (i = 0; i < N; i++) C[i] = T1[i] * 2;
for (i = 0; i < N; i++) T2[i] = B[i] + 3;
for (i = 0; i < N; i++) D[i] = T2[i] * 4;
""",
    """
for (i = 0; i < N; i++) Buf[i] = A[i] + 1;
for (i = 0; i < N; i++) C[i] = Buf[i] * 2;
for (i = 0; i < N; i++) Buf[i] = B[i] + 3;
for (i = 0; i < N; i++) D[i] = Buf[i] * 4;
""",
)
def validate_inter_array_reuse() -> List[str]:
    n = 4
    a = {i: i for i in range(n)}
    b = {i: 10 + i for i in range(n)}
    t1 = {i: a[i] + 1 for i in range(n)}
    c = {i: t1[i] * 2 for i in range(n)}
    t2 = {i: b[i] + 3 for i in range(n)}
    d = {i: t2[i] * 4 for i in range(n)}

    buf = {i: a[i] + 1 for i in range(n)}
    target_c = {i: buf[i] * 2 for i in range(n)}
    buf = {i: b[i] + 3 for i in range(n)}
    target_d = {i: buf[i] * 4 for i in range(n)}

    same_dict(c, target_c, "C")
    same_dict(d, target_d, "D")

    def live_overlap(left: Tuple[int, int], right: Tuple[int, int]) -> bool:
        return left[0] < right[1] and right[0] < left[1]

    logical_lifetimes = {
        ("T1", i): (0, 2) for i in range(n)
    }
    logical_lifetimes.update({
        ("T2", i): (2, 4) for i in range(n)
    })
    shared_mapping = {
        ("T1", i): ("Buf", i) for i in range(n)
    }
    shared_mapping.update({
        ("T2", i): ("Buf", i) for i in range(n)
    })
    for left, left_physical in shared_mapping.items():
        for right, right_physical in shared_mapping.items():
            if left >= right or left_physical != right_physical:
                continue
            require(
                not live_overlap(logical_lifetimes[left], logical_lifetimes[right]),
                "shared buffer cells have overlapping live ranges",
            )

    storage_specs = {
        "T1": {"size": 8, "align": 8},
        "T2": {"size": 8, "align": 8},
        "Buf": {"size": 8, "align": 8},
    }
    for logical in ("T1", "T2"):
        require(storage_specs[logical] == storage_specs["Buf"],
                f"{logical} is not storage-compatible with Buf")
    return [
        "logical arrays mapped to one buffer have non-overlapping live ranges",
        "shared physical buffer cells are used only by non-overlapping lifetimes",
        "reused cells are size/alignment compatible with the shared buffer",
        "all accesses in each lifetime interval are rewritten consistently",
    ]


@add_case(
    "array_expansion_versioning",
    "same instances / more physical versions plus copy-out",
    """
for (t = 0; t < T; t++)
  for (i = 0; i < N; i++) {
    X[i] = t + i;
    Y[t][i] = X[i];
  }
""",
    """
for (t = 0; t < T; t++)
  for (i = 0; i < N; i++) {
    X_exp[t][i] = t + i;
    Y[t][i] = X_exp[t][i];
  }
for (i = 0; i < N; i++)
  X[i] = X_exp[T - 1][i];
""",
)
def validate_array_expansion_versioning() -> List[str]:
    t_max, n = 3, 4
    x: Dict[int, int] = {}
    y: Dict[Tuple[int, int], int] = {}
    for t in range(t_max):
        for i in range(n):
            x[i] = t + i
            y[t, i] = x[i]

    x_exp: Dict[Tuple[int, int], int] = {}
    target_y: Dict[Tuple[int, int], int] = {}
    for t in range(t_max):
        for i in range(n):
            x_exp[t, i] = t + i
            require((t, i) in x_exp, "expanded version read before write")
            target_y[t, i] = x_exp[t, i]
    target_x = {i: x_exp[t_max - 1, i] for i in range(n)}

    same_dict(y, target_y, "Y")
    same_dict(x, target_x, "final X")
    source_liveouts = {("X", i) for i in range(n)}
    selected_versions = {("X", i): ("X_exp", t_max - 1, i) for i in range(n)}
    require(set(selected_versions.keys()) == source_liveouts,
            "version commit does not cover every source live-out")
    require(len(set(selected_versions.values())) == len(selected_versions),
            "selected target versions are not unique")
    logical_specs = {source_cell: (8, 8) for source_cell in source_liveouts}
    version_specs = {version_cell: (8, 8) for version_cell in selected_versions.values()}
    require(all(logical_specs[source_cell] == version_specs[version_cell]
                for source_cell, version_cell in selected_versions.items()),
            "selected version storage spec mismatch")
    require(all(x[source_cell[1]] == x_exp[version_cell[1], version_cell[2]]
                for source_cell, version_cell in selected_versions.items()),
            "selected version value does not match source live-out")
    return [
        "each read selects the version produced by the same logical iteration",
        "extra versions project back to one source logical array",
        "selected committed versions cover source live-outs exactly once",
        "selected target versions are storage-compatible with source live-outs",
        "selected version values match represented source live-outs",
        "copy-out commits exactly the final source-observable version",
    ]


@add_case(
    "overlapped_tiling",
    "instance-count-changing / private recomputation plus unique commit",
    """
for (i = 1; i < N - 1; i++)
  T[i] = A[i - 1] + A[i] + A[i + 1];
for (i = 2; i < N - 2; i++)
  B[i] = T[i - 1] + T[i] + T[i + 1];
""",
    """
for (ii = 2; ii < N - 2; ii += Tile) {
  l = ii; r = min(ii + T, N - 1);
  for (i = max(1, l - H); i < min(N - 1, r + H); i++)
    LocalT[i] = A[i - 1] + A[i] + A[i + 1];
  for (i = l; i < r; i++)
    B[i] = LocalT[i - 1] + LocalT[i] + LocalT[i + 1];
}
""",
)
def validate_overlapped_tiling() -> List[str]:
    n, tile, halo = 10, 4, 1
    t_domain = {("T", i) for i in range(1, n - 1)}
    b_domain = {("B", i) for i in range(2, n - 2)}
    source_domain = t_domain | b_domain
    tile_ranges = [(l, min(l + tile, n - 2)) for l in range(2, n - 2, tile)]
    target_instances: List[Tuple[int, str, int, str]] = []
    commits: List[Tuple[str, int]] = []
    for tile_id, (l, r) in enumerate(tile_ranges):
        local_t_points = set(range(max(1, l - halo), min(n - 1, r + halo)))
        tile_trace: List[Tuple[str, int]] = []
        for i in sorted(local_t_points):
            role = "commit" if l <= i < r else "internal"
            target_instances.append((tile_id, "T", i, "internal"))
            tile_trace.append(("T", i))
            require(("T", i) in source_domain, "overlap computes an invalid T instance")
            require(all(0 <= q < n for q in (i - 1, i, i + 1)), "halo read out of input bounds")
        positions = {inst: pos for pos, inst in enumerate(tile_trace)}
        for i in range(l, r):
            target_instances.append((tile_id, "B", i, "commit"))
            commits.append(("B", i))
            deps = {i - 1, i, i + 1}
            require(deps.issubset(local_t_points), "tile does not locally close B dependences")
            consumer_pos = len(tile_trace)
            for dep in deps:
                require(positions[("T", dep)] < consumer_pos,
                        "tile producer does not precede consumer")
            tile_trace.append(("B", i))
            require(("B", i) in source_domain, "overlap computes an invalid B instance")

    require(set(commits) == b_domain, "commits do not cover every source output")
    require(len(commits) == len(b_domain), "more than one tile commits a source output")
    require(len(target_instances) > len(source_domain), "target did not actually duplicate work")

    a = {i: i for i in range(n)}
    source_t = {i: a[i - 1] + a[i] + a[i + 1] for i in range(1, n - 1)}
    source_b = {i: source_t[i - 1] + source_t[i] + source_t[i + 1]
                for i in range(2, n - 2)}
    target_b: Dict[int, int] = {}
    for _tile_id, (l, r) in enumerate(tile_ranges):
        local_t: Dict[int, int] = {}
        for i in range(max(1, l - halo), min(n - 1, r + halo)):
            local_t[i] = a[i - 1] + a[i] + a[i + 1]
        for i in range(l, r):
            target_b[i] = local_t[i - 1] + local_t[i] + local_t[i + 1]
    same_dict(source_b, target_b, "B")
    return [
        "projection maps every target computation to a valid source instance",
        "commit instances form an exact cover of source live-out instances",
        "tile-local dependence closure covers every committed B computation",
        "tile-local producers precede their consumers in the target trace",
        "duplicated halo/internal writes are tile-local and invisible",
    ]


@add_case(
    "reduction_privatization",
    "parallel/storage privatization plus merge",
    """
sum = 0;
for (i = 0; i < N; i++)
  sum += A[i];
""",
    """
for (p = 0; p < P; p++) {
  local[p] = 0;
  for (i in chunk(p))
    local[p] += A[i];
}
sum = 0;
for (p = 0; p < P; p++)
  sum += local[p];
""",
)
def validate_reduction_privatization() -> List[str]:
    n, parts = 9, 3
    modulus = 17
    carrier = set(range(modulus))

    def merge(x: int, y: int) -> int:
        return (x + y) % modulus

    identity = 0
    a = {i: i + 1 for i in range(n)}
    chunks = [set(range(p * (n // parts), (p + 1) * (n // parts))) for p in range(parts)]
    require(set.union(*chunks) == set(range(n)), "reduction chunks do not cover iteration space")
    for i, c1 in enumerate(chunks):
        for c2 in chunks[i + 1 :]:
            require(c1.isdisjoint(c2), "reduction chunks overlap")
    partial_accumulators = [("local", p) for p in range(parts)]
    merge_order = list(partial_accumulators)
    require(len(set(partial_accumulators)) == len(partial_accumulators),
            "private reduction accumulators are not unique")
    require(len(set(merge_order)) == len(merge_order),
            "reduction merge order reuses a private accumulator")
    require(set(merge_order) == set(partial_accumulators),
            "reduction merge order does not cover private accumulators exactly")
    public_accumulator = ("sum",)
    public_specs = {public_accumulator: (8, 8)}
    accumulator_specs = {accumulator: (8, 8) for accumulator in partial_accumulators}
    storage_mapping = {
        accumulator: public_accumulator for accumulator in partial_accumulators
    }
    require(all(public_specs[public_cell] == accumulator_specs[private_cell]
                for private_cell, public_cell in storage_mapping.items()),
            "reduction accumulator storage spec mismatch")

    require(identity in carrier, "reduction identity is outside the finite carrier")
    require(all(merge(x, y) in carrier for x in carrier for y in carrier),
            "reduction merge operator is not closed on carrier")
    require(all(merge(merge(x, y), z) == merge(x, merge(y, z))
                for x in carrier for y in carrier for z in carrier),
            "reduction merge operator is not associative on carrier")
    require(all(merge(x, y) == merge(y, x) for x in carrier for y in carrier),
            "reduction merge operator is not commutative on carrier")
    require(all(merge(identity, x) == x and merge(x, identity) == x
                for x in carrier),
            "reduction identity law does not hold on carrier")

    source_sum = identity
    for i in range(n):
        source_sum = merge(source_sum, a[i])
    locals_ = []
    for chunk in chunks:
        local = identity
        for i in sorted(chunk):
            local = merge(local, a[i])
        locals_.append(local)
    accumulator_values = dict(zip(partial_accumulators, locals_))
    ordered_values = [accumulator_values[acc] for acc in merge_order]
    target_sum = identity
    for local in ordered_values:
        target_sum = merge(target_sum, local)
    require(source_sum == target_sum, "reduction merge gives different result")

    return [
        "iteration chunks are disjoint and exactly cover the source reduction domain",
        "private accumulators are fresh per chunk",
        "private accumulators are storage-compatible with the public reduction cell",
        "merge order consumes every private accumulator exactly once",
        "merge-order accumulator values fold to the final reduction value",
        "merge operator is closed, associative, commutative, and has an identity on the finite carrier",
    ]


@add_case(
    "double_buffering",
    "same logical values / phase-separated ping-pong storage",
    """
for (t = 1; t <= T; t++)
  for (i = 0; i < N; i++)
    A[t][i] = A[t - 1][i] + 1;
""",
    """
cur[:] = A0[:];
for (t = 1; t <= T; t++) {
  for (i = 0; i < N; i++)
    next[i] = cur[i] + 1;
  swap(cur, next);
}
""",
)
def validate_double_buffering() -> List[str]:
    t_max, n = 5, 4
    init = {i: i for i in range(n)}
    full = {(0, i): init[i] for i in range(n)}
    for t in range(1, t_max + 1):
        for i in range(n):
            full[t, i] = full[t - 1, i] + 1

    cur = dict(init)
    nxt = {i: None for i in range(n)}
    for t in range(1, t_max + 1):
        entry_snapshot = dict(cur)
        writes_this_phase = set()
        write_snapshot: Dict[int, int] = {}
        for i in range(n):
            nxt[i] = cur[i] + 1
            write_snapshot[i] = nxt[i]
            writes_this_phase.add(i)
        require(writes_this_phase == set(range(n)), "next buffer is not fully defined before swap")
        for i in range(n):
            require(write_snapshot[i] == entry_snapshot[i] + 1,
                    f"next-live value {i} does not flow from phase write")
        cur, nxt = nxt, cur
        require(cur == {i: full[t, i] for i in range(n)}, "swap does not expose the current time row")

    expected = {i: full[t_max, i] for i in range(n)}
    same_dict(expected, cur, "final cur")
    source_liveouts = {("A", t_max, i) for i in range(n)}
    final_live = {("cur", i) for i in range(n)}
    final_snapshot = {("cur", i): cur[i] for i in range(n)}
    require(set(final_snapshot.keys()) == final_live,
            "final phase snapshot does not match final-live cells")
    projection = {("A", t_max, i): ("cur", i) for i in range(n)}
    require(set(projection.keys()) == source_liveouts,
            "phase projection does not cover logical live-outs")
    require(len(set(projection.values())) == len(projection),
            "phase projection reuses a physical final cell")
    require(set(projection.values()) <= final_live,
            "phase projection target is not final-live")
    projection_values = [
        (source_cell, target_cell,
         full[t_max, source_cell[2]], final_snapshot[target_cell])
        for source_cell, target_cell in projection.items()
    ]
    require(all(source_value == target_value
                for _source_cell, _target_cell, source_value, target_value in projection_values),
            "phase projection value mismatch")
    source_specs = {("A", t_max, i): (8, 8) for i in range(n)}
    final_specs = {("cur", i): (8, 8) for i in range(n)}
    require(all(source_specs[source_cell] == final_specs[target_cell]
                for source_cell, target_cell in projection.items()),
            "phase projection storage spec mismatch")
    return [
        "next buffer is written before it is read in the following phase",
        "cur buffer remains live until the phase's computation completes",
        "next-live values come from the phase write snapshot",
        "swap implements the projection from physical buffer to logical time",
        "final phase value snapshot matches the final-live physical cells",
        "final phase projection covers every logical live-out",
        "phase projection values match final physical buffer cells",
        "final phase physical cells are storage-compatible with logical live-outs",
    ]


@add_case(
    "storage_view_composition",
    "composition / layout projection followed by private erasure",
    """
for (i = 0; i < N; i++)
  A[i] = i + 10;
""",
    """
for (i = 0; i < N; i++)
  A_pad[i] = i + 10;
for (i = 0; i < N; i++) {
  tmp_private[i] = A_pad[i] * 2;
  /* tmp_private is not observable after the pass */
}
""",
)
def validate_storage_view_composition() -> List[str]:
    n = 4
    source_state = {("A", i): i + 10 for i in range(n)}
    mid_state = {("A_pad", i): source_state["A", i] for i in range(n)}
    mid_state[("A_pad_padding", 0)] = -1
    target_state = dict(mid_state)
    private_cells = {("tmp_private", i) for i in range(n)}
    for i in range(n):
        target_state["tmp_private", i] = target_state["A_pad", i] * 2

    public_mid_cells = {("A_pad", i) for i in range(n)}
    layout_projection = {("A", i): ("A_pad", i) for i in range(n)}
    source_public_cells = set(source_state.keys())
    target_public_cells = set(public_mid_cells)
    target_mid_source_observable = set(public_mid_cells)
    mid_source_target_observable = set(public_mid_cells)
    composed_projection = {
        target_cell: source_cell
        for source_cell, target_cell in layout_projection.items()
    }

    require(private_cells.isdisjoint(public_mid_cells),
            "private cells overlap composed public/layout cells")
    require(target_mid_source_observable == mid_source_target_observable,
            "cell-view composition has incompatible intermediate observables")
    require(set(composed_projection.keys()) == target_public_cells,
            "composed cell view does not cover target public cells")
    require(set(composed_projection.values()) == source_public_cells,
            "composed cell view does not cover source public cells")
    require(all(target_cell in target_public_cells and source_cell in source_public_cells
                for target_cell, source_cell in composed_projection.items()),
            "composed cell relation mentions an unobservable endpoint cell")
    require(all(target_state[cell] == mid_state[cell] for cell in public_mid_cells),
            "private-erasure view cannot relate target to intermediate state")
    require(all(source_state[source_cell] == mid_state[target_cell]
                for source_cell, target_cell in layout_projection.items()),
            "layout projection view cannot relate intermediate state to source")
    require(all(source_state[source_cell] == target_state[target_cell]
                for source_cell, target_cell in layout_projection.items()),
            "composed view does not relate final target to source")

    def target_mid_cell(cell: Tuple[str, int]) -> Tuple[str, int]:
        return cell

    def mid_source_cell(cell: Tuple[str, int]) -> Tuple[str, int]:
        array, index = cell
        if array == "A_pad":
            return ("A", index)
        return cell

    source_access = {i: ("A", i) for i in range(n)}
    mid_access = {i: ("A_pad", i) for i in range(n)}
    target_access = {i: ("A_pad", i) for i in range(n)}
    require(all(target_mid_cell(target_access[i]) == mid_access[i] for i in range(n)),
            "target-to-mid access remap is invalid")
    require(all(mid_source_cell(mid_access[i]) == source_access[i] for i in range(n)),
            "mid-to-source access remap is invalid")
    require(all(mid_source_cell(target_mid_cell(target_access[i])) == source_access[i]
                for i in range(n)),
            "composed access remap is invalid")
    return [
        "target-to-mid private-erasure view ignores only fresh private cells",
        "mid-to-source layout view projects padded physical cells to logical cells",
        "the two views agree on the observable intermediate cells",
        "the composed cell view covers exactly the public source and target cells",
        "there exists an intermediate state satisfying both view relations",
        "the composed observation relates target physical cells to source logical cells",
        "access remap witnesses compose through the same intermediate cells",
    ]


@add_negative("missing_private_fill", "scalar_privatization_expansion")
def reject_missing_private_fill() -> None:
    n = 3
    tmp_exp: Dict[int, int] = {}
    for i in range(n):
        require(i in tmp_exp, f"tmp_exp[{i}] read before write")


@add_negative("private_missing_liveout_copy", "private_copy_boundary")
def reject_private_missing_liveout_copy() -> None:
    public_liveouts = {"tmp"}
    copyouts: List[Tuple[str, Tuple[str, int]]] = []
    require(public_liveouts <= {public for public, _private in copyouts},
            "private live-out has no copy-out")


@add_negative("private_duplicate_liveout_copy", "private_copy_boundary")
def reject_private_duplicate_liveout_copy() -> None:
    copyouts = [("tmp", ("tmp_priv", 0)), ("tmp", ("tmp_priv", 1))]
    copyout_publics = [public for public, _private in copyouts]
    require(len(copyout_publics) == len(set(copyout_publics)),
            "private live-out copy-out is not unique")


@add_negative("private_aliasing_copyin_private", "private_copy_boundary")
def reject_private_aliasing_copyin_private() -> None:
    copyins = [("seed", ("tmp_priv", 0)), ("bias", ("tmp_priv", 0))]
    copyin_privates = [private for _public, private in copyins]
    require(len(copyin_privates) == len(set(copyin_privates)),
            "private copy-in target is not unique")


@add_negative("private_bad_copyout_value", "private_copy_boundary")
def reject_private_bad_copyout_value() -> None:
    copyout_values = [(("tmp", ("tmp_priv", 2)), 12, 11)]
    require(all(public_value == private_value
                for _pair, public_value, private_value in copyout_values),
            "copy-out boundary value mismatch")


@add_negative("private_incompatible_boundary_storage", "private_copy_boundary")
def reject_private_incompatible_boundary_storage() -> None:
    public_specs = {"seed": (8, 8)}
    private_specs = {("seed_priv", 0): (4, 4)}
    boundary_pairs = [("seed", ("seed_priv", 0))]
    require(all(public_specs[public] == private_specs[private]
                for public, private in boundary_pairs),
            "private boundary storage spec mismatch")


@add_negative("scalar_promotion_incompatible_storage", "scalar_promotion")
def reject_scalar_promotion_incompatible_storage() -> None:
    promoted_source = ("A", "i")
    promoted_scalar = ("s",)
    logical_specs = {promoted_source: (8, 8)}
    scalar_specs = {promoted_scalar: (4, 4)}
    require(logical_specs[promoted_source] == scalar_specs[promoted_scalar],
            "promoted scalar storage spec mismatch")


@add_negative("source_alias_violation", "source_no_alias_abstraction")
def reject_source_alias_violation() -> None:
    logical_blocks = {"A": "base_X", "B": "base_X"}
    require(logical_blocks["A"] != logical_blocks["B"], "A and B may alias")


@add_negative("aliased_layout_map", "layout_remap_padding")
def reject_aliased_layout_map() -> None:
    n, m = 2, 3
    domain = {(i, j) for i in range(n) for j in range(m)}
    rho = {(i, j): i for i, j in domain}
    require(len(set(rho.values())) == len(domain), "layout map aliases logical cells")


@add_negative("layout_bad_boundary_value", "layout_remap_padding")
def reject_layout_bad_boundary_value() -> None:
    layout_value_entries = [((0, 0), 0, 10, 11)]
    require(all(source_value == target_value
                for _source_cell, _target_cell, source_value, target_value
                in layout_value_entries),
            "layout boundary value mismatch")


@add_negative("layout_incompatible_storage", "layout_remap_padding")
def reject_layout_incompatible_storage() -> None:
    n, m = 2, 3
    domain = {(i, j) for i in range(n) for j in range(m)}
    pad_stride = m + 1
    pad_map = {(i, j): i * pad_stride + j for i, j in domain}
    logical_specs = {("A", i, j): (8, 8) for i, j in domain}
    physical_specs = {("A_pad", pad_map[i, j]): (4, 4) for i, j in domain}
    storage_mappings = [
        (("A", i, j), ("A_pad", pad_map[i, j]))
        for i, j in sorted(domain)
    ]
    require(all(logical_specs[source_cell] == physical_specs[target_cell]
                for source_cell, target_cell in storage_mappings),
            "layout storage spec mismatch")


@add_negative("layout_bad_access_remap", "layout_remap_padding")
def reject_layout_bad_access_remap() -> None:
    renames = {("A_pad", "A")}
    access_pairs = [
        (("read", "A_pad", ("i", "j")), ("read", "A", ("j", "i"))),
    ]
    require(all(target_index == source_index
                for (_target_kind, _target_array, target_index),
                    (_source_kind, _source_array, source_index) in access_pairs),
            "layout access remap changes affine index")
    require(all(target_array == source_array or (target_array, source_array) in renames
                for (_target_kind, target_array, _target_index),
                    (_source_kind, source_array, _source_index) in access_pairs),
            "target access does not use declared layout rename")


@add_negative("layout_bad_permutation_access_remap", "layout_remap_padding")
def reject_layout_bad_permutation_access_remap() -> None:
    index_permutations = {("A_t", "A"): (1, 0)}
    access_pairs = [
        (("read", "A_t", ("i", "j")), ("read", "A", ("i", "j"))),
    ]

    def access_remap_ok(
        target_array: str,
        target_index: Tuple[str, ...],
        source_array: str,
        source_index: Tuple[str, ...],
    ) -> bool:
        if target_array == source_array and target_index == source_index:
            return True
        permutation = index_permutations.get((target_array, source_array))
        if permutation is None:
            return False
        if any(index >= len(source_index) for index in permutation):
            return False
        return target_index == tuple(source_index[index] for index in permutation)

    require(all(access_remap_ok(target_array, target_index, source_array, source_index)
                for (_target_kind, target_array, target_index),
                    (_source_kind, source_array, source_index) in access_pairs),
            "target access does not use declared index permutation")


@add_negative("layout_bad_affine_access_remap", "layout_remap_padding")
def reject_layout_bad_affine_access_remap() -> None:
    n, m = 2, 3
    domain = {(i, j) for i in range(n) for j in range(m)}
    access_pairs = [
        (
            ("read", "A_lin", lambda i, j: (i * m + j + 1,)),
            ("read", "A", lambda i, j: (i, j)),
            lambda source_index: (source_index[0] * m + source_index[1],),
        ),
    ]
    for (target_kind, _target_array, target_index_fn), (
        source_kind,
        _source_array,
        source_index_fn,
    ), affine_layout_fn in access_pairs:
        require(target_kind == source_kind, "affine layout access remap changes access kind")
        for i, j in domain:
            source_index = source_index_fn(i, j)
            target_index = target_index_fn(i, j)
            require(target_index == affine_layout_fn(source_index),
                    "target access does not use declared affine layout")


@add_negative("missing_copy_in", "scratchpad_packing")
def reject_missing_copy_in() -> None:
    tile = 4
    copied = {0, 1, 2}
    for k in range(tile):
        require(k in copied, f"Bp[{k}] used before copy-in")


@add_negative("scratchpad_bad_local_remap", "scratchpad_packing")
def reject_scratchpad_bad_local_remap() -> None:
    kk, tile = 0, 4
    local_mapping = {("Bp", k): ("B", kk + k) for k in range(tile)}
    local_mapping[("Bp", 2)] = ("B", 0)
    require(len(set(local_mapping.values())) == len(local_mapping),
            "public cells mapped to local buffer are not injective")
    for k in range(tile):
        require(local_mapping[("Bp", k)] == ("B", kk + k),
                "local read does not match the declared local remap")


@add_negative("scratchpad_incompatible_local_storage", "scratchpad_packing")
def reject_scratchpad_incompatible_local_storage() -> None:
    kk, tile = 0, 4
    local_mapping = {("Bp", k): ("B", kk + k) for k in range(tile)}
    public_specs = {("B", kk + k): (8, 8) for k in range(tile)}
    local_specs = {("Bp", k): (4, 4) for k in range(tile)}
    require(all(public_specs[public] == local_specs[local]
                for local, public in local_mapping.items()),
            "scratchpad local storage spec mismatch")


@add_negative("missing_copy_out", "scratchpad_copy_out")
def reject_missing_copy_out() -> None:
    n, tile = 4, 4
    committed = set()
    for _kk in range(0, n, tile):
        committed.update({0, 1, 2})
    require(committed == set(range(n)), "copy-out does not commit every logical output")


@add_negative("scratchpad_bad_copy_instance_role", "scratchpad_copy_out")
def reject_scratchpad_bad_copy_instance_role() -> None:
    copy_instance_trace = [
        ("Internal", "CopyIn", 0),
        ("Internal", "CopyOut", 0),
    ]
    expected_role = {
        "CopyIn": "Internal",
        "LocalRead": "Internal",
        "LocalWrite": "Internal",
        "CopyOut": "Commit",
    }
    require(all(role == expected_role[event]
                for role, event, _source_instance in copy_instance_trace),
            "copy helper instance role does not match copy event")


@add_negative("missing_contraction_conflict_pair", "array_contraction")
def reject_missing_contraction_conflict_pair() -> None:
    values = [(0, 0), (1, 0)]
    live_ranges = {
        (0, 0): (0, 2),
        (1, 0): (1, 3),
    }
    conflicts = set()
    v1, v2 = values
    l1, r1 = live_ranges[v1]
    l2, r2 = live_ranges[v2]
    overlap = l1 < r2 and l2 < r1
    require(not overlap or (v1, v2) in conflicts or (v2, v1) in conflicts,
            f"live-overlap conflict missing for {v1} and {v2}")


@add_negative("mod_one_contraction_conflict", "array_contraction")
def reject_mod_one_contraction_conflict() -> None:
    t_max, n = 3, 1

    def phys(value: Tuple[int, int]) -> Tuple[int, int]:
        _t, i = value
        return (0, i)

    def live_range(value: Tuple[int, int]) -> Tuple[int, int]:
        t, _ = value
        if t < t_max:
            return (t, t + 1)
        return (t, t)

    values = [(t, i) for t in range(t_max + 1) for i in range(n)]
    for idx, v1 in enumerate(values):
        for v2 in values[idx + 1:]:
            if phys(v1) != phys(v2):
                continue
            l1, r1 = live_range(v1)
            l2, r2 = live_range(v2)
            overlap = max(l1, l2) <= min(r1, r2)
            require(not overlap, f"conflicting values {v1} and {v2} share {phys(v1)}")


@add_negative("contraction_missing_boundary_liveout", "array_contraction")
def reject_contraction_missing_boundary_liveout() -> None:
    source_liveouts = {(2, 0), (2, 1)}
    boundary_mapping = {(2, 0): (0, 0)}
    require(set(boundary_mapping.keys()) == source_liveouts,
            "reuse boundary mapping does not cover every source live-out")


@add_negative("contraction_incompatible_storage", "array_contraction")
def reject_contraction_incompatible_storage() -> None:
    source_cell = (2, 0)
    target_cell = (0, 0)
    logical_specs = {source_cell: (8, 8)}
    physical_specs = {target_cell: (4, 4)}
    require(logical_specs[source_cell] == physical_specs[target_cell],
            "reuse boundary storage spec mismatch")


@add_negative("inter_array_live_overlap", "inter_array_reuse")
def reject_inter_array_live_overlap() -> None:
    t1_live = (0, 3)
    t2_live = (2, 4)
    require(
        t1_live[1] <= t2_live[0] or t2_live[1] <= t1_live[0],
        "T1 and T2 live ranges overlap",
    )


@add_negative("inter_array_same_buffer_live_overlap", "inter_array_reuse")
def reject_inter_array_same_buffer_live_overlap() -> None:
    def live_overlap(left: Tuple[int, int], right: Tuple[int, int]) -> bool:
        return left[0] < right[1] and right[0] < left[1]

    left = ("T1", 0)
    right = ("T2", 0)
    logical_lifetimes = {
        left: (0, 3),
        right: (2, 4),
    }
    shared_mapping = {
        left: ("Buf", 0),
        right: ("Buf", 0),
    }
    require(
        shared_mapping[left] != shared_mapping[right] or
        not live_overlap(logical_lifetimes[left], logical_lifetimes[right]),
        "shared buffer cells have overlapping live ranges",
    )


@add_negative("inter_array_incompatible_storage", "inter_array_reuse")
def reject_inter_array_incompatible_storage() -> None:
    storage_specs = {
        "T1": {"size": 8, "align": 8},
        "T2": {"size": 4, "align": 4},
        "Buf": {"size": 8, "align": 8},
    }
    for logical in ("T1", "T2"):
        require(storage_specs[logical] == storage_specs["Buf"],
                f"{logical} is not storage-compatible with Buf")


@add_negative("missing_expansion_copy_out", "array_expansion_versioning")
def reject_missing_expansion_copy_out() -> None:
    t_max, n = 3, 2
    x_exp = {(t, i): t + i for t in range(t_max) for i in range(n)}
    source_final = {i: (t_max - 1) + i for i in range(n)}
    target_final = {i: 0 for i in range(n)}
    require(target_final == source_final,
            f"final X differs without copy-out: {target_final!r} != {source_final!r}")


@add_negative("duplicate_selected_version", "array_expansion_versioning")
def reject_duplicate_selected_version() -> None:
    selected_versions = {
        ("X", 0): ("X_exp", 2, 0),
        ("X", 1): ("X_exp", 2, 0),
    }
    require(len(set(selected_versions.values())) == len(selected_versions),
            "selected target versions are not unique")


@add_negative("expansion_incompatible_version_storage", "array_expansion_versioning")
def reject_expansion_incompatible_version_storage() -> None:
    source_cell = ("X", 0)
    version_cell = ("X_exp", 2, 0)
    logical_specs = {source_cell: (8, 8)}
    version_specs = {version_cell: (4, 4)}
    require(logical_specs[source_cell] == version_specs[version_cell],
            "selected version storage spec mismatch")


@add_negative("duplicate_overlap_commit", "overlapped_tiling")
def reject_duplicate_overlap_commit() -> None:
    n, tile, halo = 10, 4, 1
    source_domain = set(range(1, n - 1))
    tile_ranges = [(l, min(l + tile, n - 1)) for l in range(1, n - 1, tile)]
    commits: List[int] = []
    for l, r in tile_ranges:
        for i in range(max(1, l - halo), min(n - 1, r + halo)):
            commits.append(i)
    require(set(commits) == source_domain, "commits do not cover source outputs")
    require(len(commits) == len(source_domain), "more than one tile commits a source output")


@add_negative("overlap_missing_halo_closure", "overlapped_tiling")
def reject_overlap_missing_halo_closure() -> None:
    n, tile, halo = 10, 4, 0
    tile_ranges = [(l, min(l + tile, n - 2)) for l in range(2, n - 2, tile)]
    for l, r in tile_ranges:
        local_t_points = set(range(max(1, l - halo), min(n - 1, r + halo)))
        for i in range(l, r):
            deps = {i - 1, i, i + 1}
            require(deps.issubset(local_t_points),
                    "tile does not locally close B dependences")


@add_negative("overlap_bad_producer_order", "overlapped_tiling")
def reject_overlap_bad_producer_order() -> None:
    local_t_points = {1, 2, 3}
    tile_trace = [("B", 2)] + [("T", i) for i in sorted(local_t_points)]
    positions = {inst: pos for pos, inst in enumerate(tile_trace)}
    consumer_pos = positions[("B", 2)]
    for dep in {1, 2, 3}:
        require(positions[("T", dep)] < consumer_pos,
                "tile producer does not precede consumer")


@add_negative("overlapping_reduction_chunks", "reduction_privatization")
def reject_overlapping_reduction_chunks() -> None:
    chunks = [{0, 1, 2}, {2, 3, 4}]
    for i, c1 in enumerate(chunks):
        for c2 in chunks[i + 1:]:
            require(c1.isdisjoint(c2), "reduction chunks overlap")


@add_negative("reduction_missing_merge_accumulator", "reduction_privatization")
def reject_reduction_missing_merge_accumulator() -> None:
    partial_accumulators = [("local", 0), ("local", 1), ("local", 2)]
    merge_order = [("local", 0), ("local", 2)]
    require(set(merge_order) == set(partial_accumulators),
            "reduction merge order does not cover private accumulators exactly")


@add_negative("reduction_incompatible_accumulator_storage", "reduction_privatization")
def reject_reduction_incompatible_accumulator_storage() -> None:
    public_accumulator = ("sum",)
    partial_accumulators = [("local", 0), ("local", 1)]
    public_specs = {public_accumulator: (8, 8)}
    accumulator_specs = {accumulator: (4, 4) for accumulator in partial_accumulators}
    storage_mapping = {
        accumulator: public_accumulator for accumulator in partial_accumulators
    }
    require(all(public_specs[public_cell] == accumulator_specs[private_cell]
                for private_cell, public_cell in storage_mapping.items()),
            "reduction accumulator storage spec mismatch")


@add_negative("reduction_non_associative_law", "reduction_privatization")
def reject_reduction_non_associative_law() -> None:
    modulus = 5
    carrier = set(range(modulus))

    def merge(x: int, y: int) -> int:
        return (x - y) % modulus

    require(all(merge(merge(x, y), z) == merge(x, merge(y, z))
                for x in carrier for y in carrier for z in carrier),
            "reduction merge operator is not associative on carrier")


@add_negative("reduction_wrong_final_value", "reduction_privatization")
def reject_reduction_wrong_final_value() -> None:
    partial_accumulators = [("local", 0), ("local", 1)]
    merge_order = list(partial_accumulators)
    accumulator_values = {("local", 0): 3, ("local", 1): 4}
    claimed_final = 8
    actual_final = 0
    for acc in merge_order:
        actual_final += accumulator_values[acc]
    require(actual_final == claimed_final, "reduction merge gives different result")


@add_negative("double_buffer_without_swap", "double_buffering")
def reject_double_buffer_without_swap() -> None:
    n = 3
    init = {i: i for i in range(n)}
    cur = dict(init)
    nxt = {i: cur[i] + 1 for i in range(n)}
    expected_after_phase = {i: init[i] + 1 for i in range(n)}
    require(cur == expected_after_phase, "swap does not expose the current time row")
    require(nxt == expected_after_phase, "next was not computed")


@add_negative("double_buffer_bad_next_value", "double_buffering")
def reject_double_buffer_bad_next_value() -> None:
    entry_snapshot = {0: 7}
    write_snapshot = {0: 8}
    next_snapshot = {0: 99}
    cell = 0
    expected = write_snapshot.get(cell, entry_snapshot.get(cell))
    require(next_snapshot[cell] == expected,
            f"next-live value {cell} does not come from phase write or entry-live value")


@add_negative("double_buffer_bad_projection", "double_buffering")
def reject_double_buffer_bad_projection() -> None:
    source_liveouts = {("A", 2, 0), ("A", 2, 1)}
    final_live = {("cur", 0), ("cur", 1)}
    projection = {("A", 2, 0): ("cur", 0)}
    require(set(projection.keys()) == source_liveouts,
            "phase projection does not cover logical live-outs")
    require(set(projection.values()) <= final_live,
            "phase projection target is not final-live")


@add_negative("double_buffer_bad_final_snapshot", "double_buffering")
def reject_double_buffer_bad_final_snapshot() -> None:
    final_live = {("cur", 0), ("cur", 1)}
    final_snapshot = {("cur", 0): 3}
    require(set(final_snapshot.keys()) == final_live,
            "final phase snapshot does not match final-live cells")


@add_negative("double_buffer_bad_projection_value", "double_buffering")
def reject_double_buffer_bad_projection_value() -> None:
    projection_values = [
        (("A", 2, 0), ("cur", 0), 9, 8),
    ]
    require(all(source_value == target_value
                for _source_cell, _target_cell, source_value, target_value in projection_values),
            "phase projection value mismatch")


@add_negative("double_buffer_incompatible_projection_storage", "double_buffering")
def reject_double_buffer_incompatible_projection_storage() -> None:
    source_cell = ("A", 2, 0)
    target_cell = ("cur", 0)
    source_specs = {source_cell: (8, 8)}
    final_specs = {target_cell: (4, 4)}
    projection = {source_cell: target_cell}
    require(all(source_specs[src] == final_specs[dst]
                for src, dst in projection.items()),
            "phase projection storage spec mismatch")


@add_negative("composition_bad_intermediate_public", "storage_view_composition")
def reject_composition_bad_intermediate_public() -> None:
    source_state = {("A", 0): 10}
    mid_state = {("A_pad", 0): 10}
    target_state = {("A_pad", 0): 11, ("tmp_private", 0): 22}
    public_mid_cells = {("A_pad", 0)}
    layout_projection = {("A", 0): ("A_pad", 0)}
    require(all(target_state[cell] == mid_state[cell] for cell in public_mid_cells),
            "private-erasure view cannot relate target to intermediate state")
    require(all(source_state[source_cell] == mid_state[target_cell]
                for source_cell, target_cell in layout_projection.items()),
            "layout projection view cannot relate intermediate state to source")


@add_negative("composition_bad_access_midpoint", "storage_view_composition")
def reject_composition_bad_access_midpoint() -> None:
    n = 3

    def target_mid_cell(cell: Tuple[str, int]) -> Tuple[str, int]:
        array, index = cell
        if array == "A_pad":
            return ("A_tmp", index)
        return cell

    def mid_source_cell(cell: Tuple[str, int]) -> Tuple[str, int]:
        array, index = cell
        if array == "A_pad":
            return ("A", index)
        return cell

    source_access = {i: ("A", i) for i in range(n)}
    target_access = {i: ("A_pad", i) for i in range(n)}
    require(all(mid_source_cell(target_mid_cell(target_access[i])) == source_access[i]
                for i in range(n)),
            "composed access remap is invalid")


@add_negative("composition_bad_mid_observables", "storage_view_composition")
def reject_composition_bad_mid_observables() -> None:
    target_mid_source_observable = {("A_pad", 0), ("A_pad", 1)}
    mid_source_target_observable = {("A_pad", 0)}
    require(target_mid_source_observable == mid_source_target_observable,
            "cell-view composition should reject incompatible intermediate observables")


def run_case(case: Case, show_code: bool = False) -> bool:
    try:
        obligations = case.validator()
    except ValidationError as exc:
        print(f"FAIL {case.name}: {exc}")
        return False
    print(f"PASS {case.name} [{case.kind}]")
    for item in obligations:
        print(f"  - {item}")
    if show_code:
        print("  source:")
        print(indent(case.source, "    "))
        print("  target:")
        print(indent(case.target, "    "))
    return True


def run_negative_tests() -> bool:
    ok = True
    for test in NEGATIVE_TESTS:
        try:
            test.validator()
        except ValidationError as exc:
            print(f"PASS_NEG {test.name} [{test.related_case}]: rejected ({exc})")
            continue
        print(f"FAIL_NEG {test.name} [{test.related_case}]: invalid witness was accepted")
        ok = False
    return ok


def write_report(path: Path, selected: Sequence[Case]) -> None:
    lines = [
        "# Standalone Validation Report",
        "",
        "This report is generated from `run.py`.  It records finite executable",
        "checks over hand-modeled source/target fragments.  It is evidence that",
        "the witness shapes are non-vacuous; it is not a proof-producing",
        "validator or a universal translation-validation theorem.",
        "",
        "| Case | Semantic Difference | Checked Obligations |",
        "| --- | --- | --- |",
    ]
    for case in selected:
        obligations = case.validator()
        obligation_text = "<br>".join(obligations)
        lines.append(f"| `{case.name}` | {case.kind} | {obligation_text} |")
    lines.extend([
        "",
        "## Negative Tests",
        "",
        "| Test | Related Case | Expected Failure |",
        "| --- | --- | --- |",
    ])
    for test in NEGATIVE_TESTS:
        try:
            test.validator()
        except ValidationError as exc:
            lines.append(f"| `{test.name}` | `{test.related_case}` | {exc} |")
        else:
            lines.append(f"| `{test.name}` | `{test.related_case}` | NOT REJECTED |")
    path.write_text("\n".join(lines) + "\n")


def indent(text: str, prefix: str) -> str:
    return "\n".join(prefix + line if line else prefix for line in text.splitlines())


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=[case.name for case in CASES])
    parser.add_argument("--show-code", action="store_true")
    parser.add_argument("--dump-cases", metavar="DIR",
                        help="write each source/target snippet as standalone .c-like files")
    parser.add_argument("--negative", action="store_true",
                        help="also run intentional invalid-witness tests")
    parser.add_argument("--dump-report", metavar="FILE",
                        help="write a markdown report with obligations and negative tests")
    args = parser.parse_args(argv)

    selected = [case for case in CASES if args.case in (None, case.name)]
    if args.dump_report:
        write_report(Path(args.dump_report), selected)
        print(f"wrote report to {args.dump_report}")

    if args.dump_cases:
        dump_dir = Path(args.dump_cases)
        dump_dir.mkdir(parents=True, exist_ok=True)
        for case in selected:
            (dump_dir / f"{case.name}.source.c").write_text(case.source + "\n")
            (dump_dir / f"{case.name}.target.c").write_text(case.target + "\n")
        print(f"dumped {2 * len(selected)} files to {dump_dir}")

    ok = True
    for idx, case in enumerate(selected):
        if idx:
            print()
        ok = run_case(case, show_code=args.show_code) and ok
    if args.negative:
        if selected:
            print()
        ok = run_negative_tests() and ok
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
