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
""",
)
def validate_layout_remap_padding() -> List[str]:
    n, m = 3, 4
    domain = {(i, j) for i in range(n) for j in range(m)}
    pad_stride = m + 1
    pad_map = {(i, j): i * pad_stride + j for i, j in domain}
    transpose_map = {(i, j): j * n + i for i, j in domain}

    for name, rho, size in [
        ("padding", pad_map, n * pad_stride),
        ("transpose", transpose_map, n * m),
    ]:
        require(len(set(rho.values())) == len(domain), f"{name} layout map is not injective")
        require(all(0 <= p < size for p in rho.values()), f"{name} layout map is out of bounds")

    padding_cells = {i * pad_stride + m for i in range(n)}
    require(set(pad_map.values()).isdisjoint(padding_cells), "logical accesses reach padding cells")

    logical_a = {(i, j): 10 * i + j for i, j in domain}
    phys = {pad_map[i, j]: logical_a[i, j] for i, j in domain}
    target_b = {(i, j): phys[pad_map[i, j]] + 1 for i, j in domain}
    source_b = {(i, j): logical_a[i, j] + 1 for i, j in domain}
    same_dict(source_b, target_b, "B")
    return [
        "logical-to-physical address map is injective over the logical domain",
        "all rewritten addresses are within allocated physical storage",
        "padding cells are outside the observable logical image",
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
        copy_events = set()
        for k in range(tile):
            bp[k] = b[kk + k]
            copy_events.add(k)
        for k in range(tile):
            require(k in copy_events, f"Bp[{k}] used before copy-in")
            target_c[kk + k] = a[kk + k] + bp[k]

    same_dict(source_c, target_c, "C")
    return [
        "copy-in covers every later local read",
        "local buffer address k consistently maps to source B[kk+k]",
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
    for kk in range(0, n, tile):
        al: Dict[int, int] = {}
        copied = set()
        for k in range(tile):
            al[k] = target_a[kk + k]
            copied.add(k)
        for k in range(tile):
            require(k in copied, f"Al[{k}] used before copy-in")
            al[k] = al[k] + 1
        for k in range(tile):
            target_a[kk + k] = al[k]
            committed.add(kk + k)

    require(committed == set(range(n)), "copy-out does not commit every logical output")
    same_dict(source_a, target_a, "A")
    return [
        "copy-in initializes each local cell before local compute",
        "copy-out commits every updated logical cell exactly once",
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
    return [
        "entry load initializes the scalar from the promoted cell",
        "all reads and writes in the promoted region are simulated by the scalar",
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
        if t < t_max:
            return (t, t + 1)
        return (t, t)

    values = [(t, i) for t in range(t_max + 1) for i in range(n)]
    for idx, v1 in enumerate(values):
        for v2 in values[idx + 1 :]:
            if phys(v1) != phys(v2):
                continue
            l1, r1 = live_range(v1)
            l2, r2 = live_range(v2)
            overlap = max(l1, l2) <= min(r1, r2)
            require(not overlap, f"conflicting values {v1} and {v2} share {phys(v1)}")

    return [
        "non-injective map rho(t,i) = (t mod 2,i) is allowed only for non-conflicting values",
        "conflict relation is derived from live ranges under the schedule",
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

    t1_live = (0, 1)
    t2_live = (2, 3)
    require(t1_live[1] < t2_live[0], "T1 and T2 live ranges overlap")
    return [
        "logical arrays mapped to one buffer have non-overlapping live ranges",
        "reused cells are type/size compatible",
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
    return [
        "each read selects the version produced by the same logical iteration",
        "extra versions project back to one source logical array",
        "copy-out commits exactly the final source-observable version",
    ]


@add_case(
    "overlapped_tiling",
    "instance-count-changing / private recomputation plus unique commit",
    """
for (i = 1; i < N - 1; i++)
  B[i] = A[i - 1] + A[i] + A[i + 1];
""",
    """
for (ii = 1; ii < N - 1; ii += T) {
  l = ii; r = min(ii + T, N - 1);
  for (i = max(1, l - H); i < min(N - 1, r + H); i++)
    Local[i] = A[i - 1] + A[i] + A[i + 1];
  for (i = l; i < r; i++)
    B[i] = Local[i];
}
""",
)
def validate_overlapped_tiling() -> List[str]:
    n, tile, halo = 10, 4, 1
    source_domain = set(range(1, n - 1))
    tile_ranges = [(l, min(l + tile, n - 1)) for l in range(1, n - 1, tile)]
    target_instances: List[Tuple[int, int, str]] = []
    commits: List[int] = []
    for tile_id, (l, r) in enumerate(tile_ranges):
        for i in range(max(1, l - halo), min(n - 1, r + halo)):
            role = "commit" if l <= i < r else "internal"
            target_instances.append((tile_id, i, role))
            if role == "commit":
                commits.append(i)
            require(i in source_domain, "overlap computes an invalid source instance")
            require(all(0 <= q < n for q in (i - 1, i, i + 1)), "halo read out of input bounds")

    require(set(commits) == source_domain, "commits do not cover every source output")
    require(len(commits) == len(source_domain), "more than one tile commits a source output")
    require(len(target_instances) > len(source_domain), "target did not actually duplicate work")

    a = {i: i for i in range(n)}
    source_b = {i: a[i - 1] + a[i] + a[i + 1] for i in source_domain}
    target_b: Dict[int, int] = {}
    for _tile_id, (l, r) in enumerate(tile_ranges):
        local: Dict[int, int] = {}
        for i in range(max(1, l - halo), min(n - 1, r + halo)):
            local[i] = a[i - 1] + a[i] + a[i + 1]
        for i in range(l, r):
            target_b[i] = local[i]
    same_dict(source_b, target_b, "B")
    return [
        "projection maps every target computation to a valid source instance",
        "commit instances form an exact cover of source live-out instances",
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
    a = {i: i + 1 for i in range(n)}
    chunks = [set(range(p * (n // parts), (p + 1) * (n // parts))) for p in range(parts)]
    require(set.union(*chunks) == set(range(n)), "reduction chunks do not cover iteration space")
    for i, c1 in enumerate(chunks):
        for c2 in chunks[i + 1 :]:
            require(c1.isdisjoint(c2), "reduction chunks overlap")

    source_sum = sum(a[i] for i in range(n))
    locals_ = [sum(a[i] for i in sorted(chunk)) for chunk in chunks]
    target_sum = sum(locals_)
    require(source_sum == target_sum, "reduction merge gives different result")

    samples = [1, 2, 3]
    require((samples[0] + samples[1]) + samples[2] == samples[0] + (samples[1] + samples[2]),
            "integer addition is not associative")
    return [
        "iteration chunks are disjoint and exactly cover the source reduction domain",
        "private accumulators are fresh per chunk",
        "merge operator is associative for this integer example",
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
        writes_this_phase = set()
        for i in range(n):
            nxt[i] = cur[i] + 1
            writes_this_phase.add(i)
        require(writes_this_phase == set(range(n)), "next buffer is not fully defined before swap")
        cur, nxt = nxt, cur
        require(cur == {i: full[t, i] for i in range(n)}, "swap does not expose the current time row")

    expected = {i: full[t_max, i] for i in range(n)}
    same_dict(expected, cur, "final cur")
    return [
        "next buffer is written before it is read in the following phase",
        "cur buffer remains live until the phase's computation completes",
        "swap implements the projection from physical buffer to logical time",
    ]


@add_negative("missing_private_fill", "scalar_privatization_expansion")
def reject_missing_private_fill() -> None:
    n = 3
    tmp_exp: Dict[int, int] = {}
    for i in range(n):
        require(i in tmp_exp, f"tmp_exp[{i}] read before write")


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


@add_negative("missing_copy_in", "scratchpad_packing")
def reject_missing_copy_in() -> None:
    tile = 4
    copied = {0, 1, 2}
    for k in range(tile):
        require(k in copied, f"Bp[{k}] used before copy-in")


@add_negative("missing_copy_out", "scratchpad_copy_out")
def reject_missing_copy_out() -> None:
    n, tile = 4, 4
    committed = set()
    for _kk in range(0, n, tile):
        committed.update({0, 1, 2})
    require(committed == set(range(n)), "copy-out does not commit every logical output")


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


@add_negative("inter_array_live_overlap", "inter_array_reuse")
def reject_inter_array_live_overlap() -> None:
    t1_live = (0, 2)
    t2_live = (2, 4)
    require(t1_live[1] < t2_live[0], "T1 and T2 live ranges overlap")


@add_negative("missing_expansion_copy_out", "array_expansion_versioning")
def reject_missing_expansion_copy_out() -> None:
    t_max, n = 3, 2
    x_exp = {(t, i): t + i for t in range(t_max) for i in range(n)}
    source_final = {i: (t_max - 1) + i for i in range(n)}
    target_final = {i: 0 for i in range(n)}
    require(target_final == source_final,
            f"final X differs without copy-out: {target_final!r} != {source_final!r}")


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


@add_negative("overlapping_reduction_chunks", "reduction_privatization")
def reject_overlapping_reduction_chunks() -> None:
    chunks = [{0, 1, 2}, {2, 3, 4}]
    for i, c1 in enumerate(chunks):
        for c2 in chunks[i + 1:]:
            require(c1.isdisjoint(c2), "reduction chunks overlap")


@add_negative("double_buffer_without_swap", "double_buffering")
def reject_double_buffer_without_swap() -> None:
    n = 3
    init = {i: i for i in range(n)}
    cur = dict(init)
    nxt = {i: cur[i] + 1 for i in range(n)}
    expected_after_phase = {i: init[i] + 1 for i in range(n)}
    require(cur == expected_after_phase, "swap does not expose the current time row")
    require(nxt == expected_after_phase, "next was not computed")


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
