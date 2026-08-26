# Storage and Instance-Changing Validation Primitives Plan

本文档是 planning note, 不是当前实现状态说明。目标是梳理 `polcert`
当前尚未覆盖、但对 "full-fledged polyhedral optimization validation"
有论文价值的语义转换族。这里不把 Pluto 当成贡献中心。Pluto 只作为
evaluation 中覆盖 schedule/control transformation 的实际 optimizer
来源；storage 或 instance-changing transformation 需要从 Pluto 之外的
optimizer 和文献中补足。

## 1. Scope

当前讨论范围：

- C-like nested loops.
- affine domains and affine accesses as the base model.
- no GPU memory-space protocol.
- no OpenMP pragma semantics as core semantics.
- source and target are compared by semantic validation, not by trusting the
  optimizer that produced the target.

特别地，本文档不再把 `private(...)` pragma 作为核心对象。当前
`polopt` 的 parallel codegen 表达的是 internal `ParMode`/`parallel for`
语义，不产生也不验证 OpenMP `private` clause。将来如果有一个 C/OpenMP
backend, 那会是一个额外后端边界，不应该混进本文的 polyhedral
transformation primitive。

## 2. Pluto `priv` calibration

Pluto 里容易混淆的是两个不同层次：

1. OpenMP backend `private(...)`.
   Pluto/CLooG codegen 会给生成的 loop-bound 或 scattering temporaries
   标注 private. 这主要是 backend pretty-print/codegen correctness
   问题，不是本文要验证的 polyhedral storage transformation。

2. Candl scalar privatization / renaming / expansion.
   Pluto 的 `--scalpriv` 经 Candl dependence analysis 使用，目的是识别
   scalar storage reuse 造成的 false dependences, 从 dependence set 中
   剪掉可 privatize 的边。Pouchet 的 polyhedral compilation slides 也把
   scalar privatization, renaming, expansion 归到 Candl。

因此更准确的说法是：

```text
Pluto core:
  schedule/control optimizer.

Pluto/Candl corner:
  dependence-level scalar privatization/renaming/expansion.
  It is polyhedral/dependence-native, but Pluto does not expose it as a
  central explicit source-to-source storage rewrite pass.

Do not use:
  OpenMP private clause as the semantic primitive for this paper.
```

这也解释了为什么 current `polopt` parallel support 不需要 OpenMP private
语义：现在它验证的是同一批 logical statement instances 的安全重排和并行暴露，
不是生成线程 runtime 代码。

## 3. Current supported class

当前 `polcert` 已支持的主类可以写成：

```text
same observable logical statement instances
same observable logical storage accesses
different schedule / grouping / order / parallel exposure
```

这里的 "same instances" 指 source statement instance 的语义层面，而不是
target AST 中循环节点数量相同。tiling, ISS, diamond tiling 会引入 tile
iterators, guards, split domains, or control structure, 但每个 observable
source statement instance 仍然应当被 target 覆盖一次。

对应 validator 责任是：

```text
instance projection / exact cover
dependence order preservation
parallel independence or safe interleaving
same reads and writes for every projected instance
```

这类覆盖 Pluto 最主要的 schedule-centric 能力，也适合作为 evaluation
baseline。但它不能展示 storage-aware 或 instance-count-changing
validation primitive 的贡献。

## 4. Semantic axes for the missing space

为了系统覆盖 unsupported transformations, 建议把 source-target relation
拆成三条轴。

### 4.1 Instance relation

```text
I1. bijection / exact cover
    每个 source instance 在 target 中执行一次。

I2. split / grouped exact cover
    source domain 被 partition 或控制结构变化，但 observable instance 仍精确覆盖。

I3. duplicate and project
    target 有多个 internal instances 映射到同一个 source instance.
    典型例子是 overlapped tiling / halo recomputation.

I4. inserted communication/copy instances
    target 多了 copy-in, copy-out, pack, unpack, commit 等辅助 instance.

I5. erased or forwarded computation
    某些 target write/read 被删除、forward, 或由已有值替代。
    DeLICM operand forwarding 属于这个方向。
```

### 4.2 Storage relation

```text
S1. identity
    每个 projected instance 的 logical read/write access 不变。

S2. injective address remap
    layout transformation / padding. logical cell 到 physical cell 的映射单射。

S3. fresh private expansion
    scalar privatization, scalar expansion, thread/tile/iteration-local temporaries.

S4. copy-mediated remap
    scratchpad, local temp, packing. reads are redirected through a copied buffer.

S5. non-injective conflict-safe reuse
    array contraction, rolling buffer, inter-array reuse, DeLICM-style coalescing.

S6. merge/commit relation
    reductions, overlapped tiling commits, copy-out. 多个 internal values
    可能被投影或合并成 observable output.
```

### 4.3 Observation relation

```text
O1. full-state equality
    target final state equals source final state on all observable locations.

O2. projection equality
    target has extra physical storage; erase private/internal cells before comparing.

O3. commit equality
    only commit writes are observable; internal halo/scratch writes are invisible.

O4. relaxed merge equality
    reductions or floating-point reorderings require an explicit algebraic or
    relaxed-FP contract.
```

The missing validators should be phrased as combinations of these axes instead
of as a flat Pluto flag checklist.

## 5. Primitive catalogue

### P0. Exact-cover instance projection

Status: already the core shape for current affine scheduling, tiling, ISS,
parallelization, and non-overlapped diamond tiling.

Validator:

```text
pi : TargetInstance -> SourceInstance
exact cover:
  every source instance has exactly one observable target representative
access preservation:
  reads_T(t) = reads_S(pi(t))
  writes_T(t) = writes_S(pi(t))
order preservation:
  source dependence x -> y implies schedule_T(rep(x)) < schedule_T(rep(y))
```

Paper role: this is the Pluto evaluation baseline, not the main new storage
story.

### P1. Duplicate-and-project instances

Optimizer/literature examples:

- PolyMage overlapped tiling for image-processing pipelines.
- Flextended Tiles / overlapped tiling families.

Pattern:

```text
source:
  one stencil point (t, i) is computed once

target:
  multiple tiles may recompute halo/internal points
  only one owner commits the observable point
```

Needed validator:

```text
pi : TargetComputeInstance -> SourceInstance
role : TargetComputeInstance -> internal | commit

projection well-formed:
  every target compute instance maps to a valid source instance

commit exact cover:
  every observable source output has exactly one commit target instance

local closure:
  every committed value's dependence cone is available from
  legal external inputs or from internal instances in the same tile

internal invisibility:
  internal/halo writes do not update observable global storage

commit safety:
  committed writes across tiles are disjoint or dependence-ordered
```

Why it matters: this is the cleanest example that breaks the current "same
logical instances" assumption. It also forces the validator to reason about
which target computations are observable.

Implementation difficulty: high. Need an instance projection with multiplicity,
tile-local dependence closure, and an observation/commit boundary.

### P2. Fresh-private storage / scalar privatization and expansion

Optimizer/literature examples:

- Candl scalar privatization / renaming / expansion.
- Classic scalar expansion to remove false dependences.
- Per-iteration or per-tile private temporaries, independent of OpenMP syntax.

Pattern:

```c
for (i = 0; i < N; i++) {
  tmp = A[i] + 1;
  B[i] = tmp * 2;
}
```

Conceptual target:

```c
for (i = 0; i < N; i++) {
  tmp_priv[i] = A[i] + 1;
  B[i] = tmp_priv[i] * 2;
}
```

Needed validator:

```text
storage class map:
  original scalar cell tmp is split into private cells tmp_priv[class]

freshness:
  private cells do not alias each other or source observable cells

use-def containment:
  every private read is reached by its corresponding private write

no live-in unless copied:
  if a private value is read before local definition, a copy-in must exist

no live-out unless committed:
  if the scalar is observable after the region, a copy-out/commit must exist

true-flow preservation:
  RAW dependences that carry values are preserved inside each private class

false-dependence elimination:
  removed WAR/WAW edges are justified as storage-name reuse, not value flow
```

Why it matters: this breaks the current "same storage access" assumption while
keeping source statement instances mostly bijective. It is a good first
storage-changing target because the witness can be small.

Implementation difficulty: medium. A restricted scalar-only transformer is a
manageable first artifact.

### P3. Copy-mediated local storage / packing / scratchpad

Optimizer/literature examples:

- PolyMage tile-local scratchpads.
- Matrix/block packing in loop-nest optimizers.
- Cache-managed local temporaries in C-like code.

Pattern:

```c
for (ii = 0; ii < N; ii += B) {
  for (i = 0; i < B; i++)
    Tmp[i] = A[ii+i];       // copy-in

  for (i = 0; i < B; i++)
    C[ii+i] = f(Tmp[i]);    // local use
}
```

Needed validator:

```text
buffer freshness:
  Tmp is fresh for the dynamic tile lifetime

copy-in coverage:
  every local read Tmp[k] is dominated by a copy-in from the intended A cell

remap consistency:
  every redirected use of A maps to the corresponding Tmp cell

no stale read:
  the copied source value is not invalidated before the local read

copy-out exactness:
  if the local buffer produces observable values, copy-out commits exactly the
  intended logical cells and no others

lifetime separation:
  buffer reuse across tiles is safe because previous tile-local values are dead
```

Why it matters: this introduces auxiliary copy instances and a fresh local
allocation without needing duplicate computation.

Implementation difficulty: medium to high, depending on whether copy-out is
included. A read-only packing/copy-in case is easier.

### P4. Injective layout remapping and padding

Optimizer/literature examples:

- IMPACT 2019 data-layout transformations with layout mapping directives.
- Padding/alignment and linearized-field layouts.

Pattern:

```c
A[i][j]
```

Target physical mapping:

```c
A_phys[j * N + i]
```

or:

```c
A_pad[i][j]       // physical row length M + pad
```

Needed validator:

```text
addr : LogicalCell -> PhysicalCell

injective or bijective:
  logical cells that may be simultaneously observable map to distinct cells

consistent rewrite:
  every read and write of the logical array uses the same addr mapping

in-bounds:
  addr(logical cell) lies inside the allocated physical field

padding non-observability:
  padding cells are not source logical cells and are not read as source values

redistribution correctness:
  if the program crosses from old layout to new layout, generated copy-in,
  copy-out, or redistribution loops preserve every live logical value
```

Why it matters: this is a pure storage-address primitive with no need to change
instance count. It is likely the easiest non-current feature to validate.

Implementation difficulty: low to medium for full-region layout rewriting;
medium if layout changes mid-program and needs redistribution copies.

### P5. Non-injective conflict-safe storage reuse

Optimizer/literature examples:

- SMO / intra-array storage optimization.
- Array contraction and rolling buffers.
- Inter-array storage reuse.
- DeLICM greedy value coalescing maps scalar lifetimes into unused array zones.

Pattern:

```c
for (t = 1; t < T; t++)
  for (i = 1; i < N-1; i++)
    A[t][i] = f(A[t-1][i-1], A[t-1][i], A[t-1][i+1]);
```

Contracted target:

```c
A[t % 2][i] = ...
```

Needed validator:

```text
value identity:
  v = (array, logical index, defining instance)

liveness/conflict:
  Conf(v1, v2) holds when v1 and v2 cannot share physical storage

physical map:
  rho : LogicalValue -> PhysicalCell

conflict separation:
  Conf(v1, v2) -> rho(v1) != rho(v2)

read availability:
  every read observes the physical cell containing the reaching logical value

overwrite safety:
  a write may overwrite a physical cell only after all conflicting old values
  are dead or after the overwrite writes the same known content

live-out projection:
  final observable logical values are recoverable from the target physical state
```

This primitive is intentionally not "injective layout". The important case is
many logical values reusing fewer physical cells. For rolling buffers the map
may contain modulo arithmetic, so the witness language may need Presburger
divisibility/modulo support or a specialized finite-buffer proof rule.

Why it matters: this is the strongest storage-optimization example. It shows
why validation needs lifetime/conflict reasoning, not just dependence-order
reasoning.

Implementation difficulty: high. A narrow rolling-buffer stencil case is a
reasonable first milestone before general SMO-style contraction.

### P6. Scalar promotion / local scalar replacement

Optimizer/literature examples:

- Local scalar replacement.
- DeLICM operand tree forwarding is related, but broader because it can remove
  memory references and forward computations.

Pattern:

```c
for (i = 0; i < N; i++) {
  A[i] = A[i] + 1;
  B[i] = A[i] * 2;
}
```

Target:

```c
for (i = 0; i < N; i++) {
  s = A[i];
  s = s + 1;
  A[i] = s;
  B[i] = s * 2;
}
```

Needed validator:

```text
entry load:
  scalar starts with the current logical cell value

scalar simulation:
  all promoted reads/writes are simulated by scalar state

no interference:
  no unmodeled write can change the promoted logical cell while scalar is live

exit store:
  if the logical cell is observable after the region, store-back is exact
```

Why it matters: this is smaller than contraction but still breaks same-access
validation. It also provides a bridge to compiler-midend scalar-dependence
removal papers.

Implementation difficulty: low to medium for a single basic loop region.

### P7. Expansion and versioning

Optimizer/literature examples:

- Candl scalar expansion.
- Array expansion / single-assignment style transformations.
- Partial data expansion in layout literature.

Needed validator:

```text
version map:
  expanded cell e maps back to a source logical value v

selector correctness:
  each target read selects the version corresponding to the source reaching def

extra-storage erasure:
  expanded cells are unobservable except through committed source outputs

projection equality:
  after erasing versions, target final observable state equals source final state
```

Why it matters: expansion is the dual of contraction. It increases storage to
remove false dependences or expose parallelism.

Implementation difficulty: medium.

### P8. Reduction or merge contracts

This is not an OpenMP clause issue. It is a semantic merge primitive that may
appear in polyhedral reductions, privatized accumulators, or copy-out commits.

Needed validator:

```text
private accumulator freshness
cover of contributing instances
merge operator contract:
  associativity / commutativity / identity as required
floating-point policy:
  either bit-exact source order or explicit relaxed-FP semantics
```

Paper priority: lower unless reductions become part of the artifact. Keep this
as a classified primitive, not as a near-term claim.

## 6. Optimizer and literature map

```text
Optimizer / line of work          Transformation families       Validation primitives
------------------------------------------------------------------------------------------------
Pluto                             affine scheduling, tiling,     P0
                                  parallel exposure, diamond

Pluto + Candl --scalpriv          scalar privatization,          P2, P7
                                  renaming, expansion

PolyMage                          overlapped tiling,             P1, P3
                                  tile-local scratchpads,
                                  redundant computation

Flextended Tiles                  overlapped / flexible          P1
                                  tiling family

IMPACT 2019 data layout           layout maps, padding,          P4, and redistribution copies
                                  in/out/inout/redist

SMO / intra-array storage         array contraction,             P5
optimization                      modulo storage mappings

Inter-array reuse literature      cross-array storage reuse      P5

DeLICM                            scalar dependence removal      P5, P6, P7
                                  by value coalescing and
                                  operand forwarding
```

The key paper argument should be:

```text
Pluto exercises the schedule/control corner of the framework.
Storage-affecting and instance-count-changing transformations expose
additional semantic contracts beyond schedule legality. We validate those
contracts directly, using Pluto only as one evaluation source rather than as
the definition of the contribution.
```

## 7. Suggested implementation and paper plan

### Phase A. Write the semantic vocabulary

Deliverable:

- source-target relation with:
  - `pi` for instance projection,
  - `role` for internal/commit/copy instances,
  - `rho` or `addr` for storage mapping,
  - `Obs` for observable state projection,
  - `Conf` for lifetime/storage conflicts.

Paper value:

- cleanly separates current supported transformations from missing families.
- avoids describing the contribution as "more Pluto flags".

### Phase B. Add one injective storage remap example

Recommended first target:

- layout remap or padding for one affine array.

Why first:

- no duplicate instances.
- no non-injective reuse.
- correctness is injectivity + consistent rewrite + in-bounds.

Artifact value:

- first concrete example beyond same-access scheduling.

### Phase C. Add scalar privatization/expansion example

Recommended target:

- scalar temporary written before read inside each iteration.
- target uses an indexed private array or explicitly scoped private scalar.

Why next:

- aligns with Candl `--scalpriv`.
- demonstrates false-dependence elimination without invoking OpenMP.

Artifact value:

- directly answers the Pluto/Candl storage corner.

### Phase D. Add local copy / packing example

Recommended target:

- copy-in only, then use packed/local buffer read-only.
- copy-out can be a later extension.

Why:

- introduces auxiliary copy instances and buffer freshness.
- uses tile boundaries from ordinary tiling but validates the copy protocol
  separately.

### Phase E. Add narrow rolling-buffer contraction

Recommended target:

- 1D time-stepping stencil with `t mod 2`.

Why:

- tests non-injective storage reuse and liveness conflicts.
- gives the strongest storage-optimization story.

Risk:

- modulo and conflict proof need new support.

### Phase F. Add overlapped tiling only after P5 vocabulary is stable

Recommended target:

- small stencil where each tile recomputes halo and commits one disjoint
  interior region.

Why last:

- breaks instance-count preservation and introduces internal invisibility.
- highest proof burden, but high paper payoff.

## 8. Reading packet status

Local PDFs read or added for this planning pass:

```text
doc/pluto-comprehensive/paper-local/bib/pdfs/
  bondhugula-et-al2008-auto-transformations.pdf
  mullapudi-vasista-bondhugula2015-polymage-tr.pdf
  shirako-sarkar2019-data-layout-polyhedral.pdf
  bhaskaracharya-bondhugula-cohen2014-intra-array-storage-optimization.pdf
  pouchet2011-polyhedral-foundations-candl-privatization.pdf
  kruse-grosser2018-delicm.pdf
```

Important evidence extracted:

- PolyMage uses overlapped tiling with redundant computation and tile-local
  scratchpads; this motivates P1 and P3.
- The IMPACT 2019 layout paper models layout mappings, padding, and explicit
  copy-in/copy-out/redistribution directives; this motivates P4.
- The intra-array storage optimization paper models array contraction as a
  schedule-dependent storage mapping constrained by live-value conflicts; this
  motivates P5.
- DeLICM removes scalar dependences by polyhedral value analysis, scalar
  memory coalescing into unused array locations, and operand forwarding; this
  motivates P5/P6/P7.
- Pouchet's slides record Candl scalar privatization/renaming/expansion; this
  motivates P2/P7 as the Pluto-adjacent storage corner.

Downloaded but not mirrored:

- Flextended Tiles remains URL-only in the packet because the ACM PDF endpoint
  was access-controlled.
- A direct Springer PDF attempt for lightweight array contraction returned
  HTML rather than a PDF, so it was not kept.

These entries should remain packet/provisional until a bibliography audit is
done. The paper draft should not cite newly added packet-only material until
metadata and source URLs are checked.

