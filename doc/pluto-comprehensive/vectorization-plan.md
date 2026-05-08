# Verified Vectorization Plan

本文最初面向实现 `polopt` verified vectorization 的开发会话。当前
annotation-only 第一版已经接入，因此本文同时作为设计记录和后续扩展
TODO。过时的 "Stage" 项保留为历史路线，但当前状态以下面的 facts 为准。

## Current Facts

Pluto 有两个与 vectorization 相关、且当前默认开启的机制。它们必须分开看：

- `--prevector` 控制 backend vector annotation。在 CLAST / OpenScop loop metadata 上标 vector bit。OpenScop 中 `OSL_LOOP_DIRECTIVE_VECTOR = 4`，CLAST 中 `CLAST_PARALLEL_VEC = 4`。
- `--intratileopt` 控制 vector/locality-friendly 的 loop-order heuristic。它会用 `pluto_loop_is_vectorizable` 参与打分，并可能把候选 point loop 移到 innermost 位置。

关键事实是：Pluto 的 vector annotation 候选来自 parallel loops。`pluto_mark_vector` 和 `pluto_get_vector_loop_list` 都从 `pluto_get_parallel_loops` 的结果中挑 innermost loop，并不调用 `pluto_loop_is_vectorizable`。因此，第一版 `polopt` vectorization 用现有 parallel checker 作为检查条件是正确且符合 Pluto annotation 语义边界的：Pluto-style vector annotation 本来就是在 parallel loop 基础上加的 backend hint。

当前 `polopt` 已支持 checked vector annotation route。`--prevector`
不再是 categorical rejection：Pluto 的 vector directive 只作为候选 hint，
真正输出 `vector for` 前仍由 checked doall/parallel certificate 重新认证。
`--noprevector` 仍作为显式禁用 vector hint 的 route control。OpenScop
loop directive 是 bit field，因此 hint parser 应按 bitmask 解释
parallel bit 和 vector bit，而不是把 directive 当作单一枚举值。

## Design Choice

第一版应增加一个轻量 `VecMode`，但不要把 vectorization 直接混进 `ParMode`。

`VecMode` 的作用是区分输出 claim，而不是引入一套新的核心 schedule 语义。证明可以复用 doall/parallel safety：若某个 current dimension 通过现有 `checked_parallelize_current`，则该维度也可以被标成 vector-safe。换句话说，第一版 verified vectorization 是 conservative vector annotation support，不是 full SIMD idiom vectorizer。

保留独立 `VecMode` 有两个好处：

- 输出层能明确区分 `parallel for` 和 `vector for`，避免论文或报告把 SIMD annotation 偷换成 thread-level parallel target。
- 以后可以在同一个 `VecMode` 目标下增加多个 checker，而不破坏第一版接口。

推荐术语：

- `doall-safe dimension`: 本文中专指现有 `parallel_safe_dim` / `Permutable` checker 认证的 current-view dimension，不声称支持 fixed-width SIMD、reduction 或 backend-specific vector semantics。
- `vector-current d`: 在 current-view dimension `d` 上输出 `VecMode`。
- `pluto-hinted vector`: 从 Pluto `<loop>` directive 的 vector bit `4` 读取 hint，也就是 `directive & 4 != 0`，但只把 hint 当候选排序，不信任它。

## Checker Policy

第一版只支持一个 checker：

```text
checked_vectorize_current_doall pol d
  := checked_parallelize_current
       (current_view_pprog pol)
       (parallel_plan_of_dim d)
```

这个定义是保守的。它会拒绝一些理论上可 SIMD 化的情况，例如固定 vector width 下跨 chunk 有依赖但同 chunk 无依赖的 recurrence。不过这类支持需要把 vector width、strip-mining、lane semantics、backend pragma 合约放进形式化。当前 Pluto-style `prevector` 不需要这些能力。

将来可以在 `VecMode` 下增加更多 checker：

- `DoallVecChecker`: 第一版，复用 parallel checker。
- `ChunkedVecChecker`: 证明固定 width 的 lane 内无依赖，chunk 间按序执行。
- `ReductionVecChecker`: 支持 associative/commutative reduction vectorization。
- `BackendPragmaChecker`: 对特定 pragma 或编译器合约做更细的语义约束。

certificate 应预留 checker kind，或至少在接口文档中说明当前 cert 是 doall cert。这样未来扩展不会要求重命名 `VecMode`。

## Implementation Plan

### Stage 0: Documentation and Tests First

更新 compatibility 文档，明确：

- `--prevector` 当前支持 annotation-only checked vector route。
- 支持计划分成 vector annotation 和 vector-friendly scheduling 两类。
- 第一版 vector annotation 使用 doall/parallel checker。
- Pluto vector hint 来自 vector bit `4`，也就是 `directive & 4 != 0`，但必须重新认证。

新增或更新 regression plan。当前至少应有 passing smoke 覆盖：

- `--vector-current d` 正例：选一个现有 `--parallel-current d` 能过的 case，确认输出包含 `vector for`。
- `--vector-current d` 负例：选一个现有 parallel validator 拒绝的维度，确认 vector route 也拒绝。
- Pluto-hinted `--prevector` 正例：若 Pluto 给出 vector directive，`polopt` 优先尝试该 dim。
- hint fallback 正例：若 Pluto hint 失败但其他 dim 通过，非 strict 模式可以选择 checked dim。
- strict 负例：若 strict mode 后续存在，Pluto hinted dim 未认证则不输出 `vector for`。

### Stage 1: Add Target Annotation IR

在现有 parallel target loop IR 中把 mode 扩成：

```coq
Inductive loop_mode :=
| SeqMode
| ParMode
| VecMode.
```

新增：

```coq
vectorize_dim_stmt : nat -> stmt -> stmt
vectorize_dim : nat -> t -> t
erase_vectorize_dim_eq : erase_parallel (vectorize_dim d p) = erase_parallel p
```

如果后续重命名 `ParallelLoop` 太大，第一版可以保留模块名，只把它视为 annotated-loop IR。文档中说明命名历史即可。源码稳定后再考虑 `AnnotatedLoop` 的整理。

### Stage 2: Add Vector Codegen Entry

复用 `tagged_prepared_codegen`。新增：

```coq
annotated_vector_codegen pp vcert
checked_vector_annotated_codegen pp vcert
```

其中 `vcert` 第一版只包装 `certified_dim`，并来自 doall checker。正确性 theorem 采用与 parallel codegen 相同的形状：

```text
VecLoopSem(vloop) refines LoopSem(erased loop)
```

第一版可以把 `VecMode` 的 trace semantics 定义得比 `ParMode` 更保守，甚至先走 erasure/refinement theorem。关键是不要把 source-level affine/tiling/ISS proof 改成 vector 专属版本。

### Stage 3: Add CLI Surface

先加显式维度接口：

```text
polopt --vector-current d file.loop
```

route 形状照 `--parallel-current d`：

```text
extract/ISS/affine/tile current view
-> checked_vectorize_current_doall
-> checked_vector_annotated_codegen
-> print vector for
```

支持组合范围应先复制 `--parallel-current` 的保守集合：

- identity
- affine-only
- default full tiled
- ISS variants

`vector-current` 的组合范围应跟随 checked parallel-current 能覆盖的
state-preserving route。若某个未来组合超出 parallel-current 的 theorem-facing
wrapper，则 vector-current 也应先拒绝。

### Stage 4: Add Pluto-Hinted Vector Route

扩展 scheduler hint extraction：

- 解析 `<loop>` extension 中所有 entries。
- parallel hint: `directive & 1 != 0`。这需要替换当前 `directive = 1` 的解析，否则 combined directive 可能漏掉 parallel bit。
- vector hint: `directive & 4 != 0`。
- 用 `<scatnames>` 把 iterator 映射到 current dimension。

不要信任 hint。流程应照 parallel route：

```text
Pluto --prevector gives candidate dim
-> try checked_vectorize_current_doall on hinted dim
-> if accepted, emit VecMode
-> otherwise fallback or reject according to strict policy
```

第一版不需要支持 nested vector markers。若 Pluto 产生多个 vector directives，只选第一个或按 innermost/current depth 排序，并在 debug output 中打印候选列表。

### Stage 5: Printing and C Lowering

pretty printer 输出：

```text
vector for iN in range(lb, ub) {
  ...
}
```

C lowering 可以先选择一个统一 pragma：

```c
#pragma omp simd
for (...) { ... }
```

若目标是贴近 Pluto，也可以输出：

```c
#pragma ivdep
#pragma vector always
for (...) { ... }
```

这需要在文档中说明 backend contract。若使用 `#pragma omp simd`，第一版 proof claim 应只说 verified vector-safe annotation, not verified compiler code generation after SIMD lowering。若贴近 Pluto 的 printer，还要注意 CLooG 只在 vector bit 存在且没有 OMP/MPI bit 时打印 `#pragma ivdep` / `#pragma vector always`。

### Stage 6: Compatibility Wrapper

`--prevector` 不应变成无条件 accepted。当前路线是：

- 在 Pluto-compatible mode 中，只在能够落到 checked vector route 时接受。
- 若 `--prevector --nointratileopt --nodiamond-tile` 同时出现，可以解释为 annotation-only vector route。
- 若 `--intratileopt` 参与 loop-order choice，先继续拒绝，除非 schedule diff 已通过 affine/tiling validator。
- 若没有 `--nodiamond-tile`，需要单独处理 diamond phase。`work/pluto-pr` 中 diamond reschedule 已被 `intratileopt` gate 约束，但 `work/pluto-upstream` 的对应路径没有同样约束；跨 checkout 的保守 annotation-only oracle 应显式加 `--nodiamond-tile`。

这条边界很重要：Pluto 的 vector-friendly loop-order choice 是 schedule transformation；`VecMode` 只能验证 annotation，不负责验证 loop permutation。

## Proof Obligations

第一版证明义务应尽量小：

1. `vectorize_dim` 不改变 erased sequential loop。
2. `checked_vectorize_current_doall` 成功时，目标 dim 在 current-view 范围内。
3. `checked_vectorize_current_doall` 成功时，复用 parallel cert soundness。
4. `checked_vector_annotated_codegen` 生成的 loop trace-safe。
5. `VecLoopSem` refines erased sequential loop semantics。
6. composed route theorem 复用现有 affine/tiling/ISS theorem，再接 vector codegen theorem。

不应在第一版证明：

- fixed-width lane semantics
- recurrence vectorization
- reduction vectorization
- compiler-specific SIMD lowering correctness
- Pluto `intratileopt` 的 vector-friendly permutation，除非它已经作为 schedule transformation 被独立验证

## Expected Outcome

第一版支持的 claim 是：

```text
If polopt emits vector for on current dimension d, then d was certified
doall-safe by the checked validator, and the annotated vector loop refines the
erased sequential optimized loop.
```

这足够覆盖 Pluto-style annotation-only backend hint，因为 Pluto 的 vector marking 本身来自 parallel loop candidates。不覆盖 `intratileopt` 造成的 vector/locality-friendly loop-order choice，除非该 schedule diff 已由现有 validator 认证。未来需要更强 SIMD 表达力时，可以在 `VecMode` 下增加新的 checker，而不用推翻第一版 design。
