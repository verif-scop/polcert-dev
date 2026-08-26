# PolOpt Support Design for Second-Level and Diamond Tiling

这份文档只回答一个问题：

- 如果要把 `--second-level-tile` 和 diamond tiling 正式接进 `PolOpt`，
  应该怎么设计？

这里的主视角不是 Pluto CLI，也不是 host-side prototype，而是：

- `PolOpt.v` 当前 theorem-aligned pipeline 到底长什么样
- 现有 tiling witness / relation / validator 在 Coq 里已经能表达什么
- second-level 和 diamond 分别应该落在哪一层扩展

这份文档是对下面两份笔记的进一步收口：

- [second-level-and-diamond-design.md](./second-level-and-diamond-design.md)
- [tiling-validation-design.md](./tiling-validation-design.md)

## 1. 先把当前 `PolOpt` 骨架说清楚

从 `PolOpt.v` 看，当前 theorem-aligned 路线是：

```text
before
  -> export_for_phase_scheduler
  -> run_pluto_phase_pipeline
       returns (mid_scop, after_scop)
  -> import mid_scop as affine midpoint
  -> checked affine validation on before -> mid
  -> infer tiling witness from mid_scop -> after_scop
  -> import canonical tiled after from (mid, witness, after_scop)
  -> checked tiling validation on mid -> after
  -> current_view_pprog
  -> existing affine codegen chain
```

对应的核心入口在：

- [PolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOpt.v#L142)
- [PolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOpt.v#L167)

这个骨架非常关键，因为它直接决定了：

- second-level 不该改成一个新的 theorem family
- diamond 也不该优先改 tiling kernel

当前 checked tiling validator 的结构是：

1. 先检查 structural tiling relation
2. 再把 old schedule lift 成 `retiled_old`
3. 最后用 shared `validate_general` 比 schedule/legality

对应定义在：

- [TilingValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingValidator.v#L1033)
- [TilingRelation.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingRelation.v#L399)

所以一旦某个扩展能继续落在：

- witness-centered tiled lifting
- plus the same `retiled_old + validate_general` bridge

它就不该被设计成新的 checked validator family。

## 2. 现有 Coq witness 已经能表达什么

当前 Coq witness 最重要的定义有两个：

- `tile_link`
- `statement_tiling_witness`

见：

- [TilingWitness.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingWitness.v#L81)
- [TilingWitness.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingWitness.v#L92)

这里有三个经常被忽略、但对支持 second-level / diamond 非常关键的事实。

### 2.1 witness 本身不带 “tiling family” 标签

Coq 里没有：

- rectangular tiling witness
- second-level tiling witness
- diamond tiling witness

它只有：

- `list tile_link`

所以从对象层面讲，当前 proof core 并不把这些 Pluto feature 当作不同语义类。

### 2.2 `eval_tile_links` 已经是 prefix-based

`eval_tile_links` 的定义是：

- 逐个 link 求值
- 每次新 link 的环境是 `prefix ++ point`

见：

- [TilingWitness.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingWitness.v#L196)

这意味着：

- 后面的 link 可以依赖前面恢复出的 tile parents
- second-level 这种依赖链在语义上本来就在模型里

### 2.3 second-level 的 dependency order 在 Coq 里其实已经被编码了

`well_formed_tile_links` 不是一个随便的长度检查。它要求：

- 第 0 个 link 的 `ae_var_coeffs` 长度等于 `point_dim`
- 第 1 个 link 的长度等于 `1 + point_dim`
- 第 2 个 link 的长度等于 `2 + point_dim`
- ...

见：

- [TilingWitness.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingWitness.v#L218)
- [TilingBoolChecker.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingBoolChecker.v#L86)

这实际上已经把 “一个 link 只能依赖更早的 tile parents，而不能依赖未来的 tile parents” 编进了 witness 形状本身。

所以从 `.v` 视角看：

- second-level 的依赖顺序不是额外缺失的一块语义
- 它已经隐含在 witness 的 ordered-link discipline 里

这也是为什么 `PhaseTiling.convert_witness` 那一步非常重要：

- 一旦它把带名字的 raw witness 变成了按 prefix 编码的 Coq witness
- 后面的定理就只依赖这个有序列表，而不再关心 Pluto raw 迭代器名字

## 3. second-level 的核心问题不是“多一层”，而是“顺序”和“布局”

如果只看 Coq witness，second-level 已经能表达。

真正的问题是：

- Pluto raw `after.scop` 里的 added-dim 顺序
- Coq witness 需要的 canonical dependency order

这两个顺序可能不同。

而当前 checked tiling relation 里，`stw_links` 的顺序不是装饰，而是 proof-relevant 的。原因有三处：

1. link-domain 的编译顺序来自 `stw_links`
   - [TilingRelation.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingRelation.v#L214)
2. canonical tiled skeleton 是按 witness 顺序插入 added dims 的
   - [TilingValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingValidator.v#L857)
3. `retiled_old_pinstr` lift old schedule 时也默认 added dims 的顺序就是 witness 顺序
   - [TilingRelation.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingRelation.v#L399)

所以 second-level 真正的设计选择，不是：

- “要不要支持两层”

而是：

- 如果 raw `after.scop` 顺序和 canonical witness 顺序不一样，到底在哪里解决这个差异？

## 4. second-level 的两种设计路线

### 4.1 路线 A：把 raw/canonical 差异完全藏在现有 untrusted 常量实现里

这条路线的做法是：

- 不改 Coq 接口
- 让现有 `infer_tiling_witness_scops` 和/或 `run_pluto_phase_pipeline`
  的手写实现直接返回“已经按 canonical order 处理过”的结果

也就是说：

- `infer_tiling_witness_scops` 返回 canonical witness
- `after_scop` 也已经被 schedule-side canonicalized

优点：

- `.v` 变动最小
- `PolOpt.v`、`TilingValidator.v`、`TilingRelation.v` 基本都不用动

缺点：

- proof boundary 变得不够显式
- second-level 真正新增的 contract 被藏进了 hand-written extractor/scheduler glue
- 文档和实现很容易再次漂移

如果目标只是尽快让 `polopt` 跑通，这条路是可行的。

### 4.2 路线 B：把 second-level 新增的 phase artifact 在 `.v` 边界显式化

我更推荐这条。

具体做法不是去改 `statement_tiling_witness`，而是在 `PolOpt` orchestration
边界引入一个小 record，例如：

```coq
Record tiling_phase_artifact := {
  tpa_witness : list statement_tiling_witness;
  tpa_after_for_import : OpenScop;
}.
```

它表达的不是新的 theorem object，而是新的 untrusted phase contract：

- `tpa_witness`
  - proof-facing canonical witness
- `tpa_after_for_import`
  - 已经对齐到 witness order 的 schedule-only after artifact

这样 second-level 的设计就被明确放在：

- `PolOpt` phase boundary

而不是被错误地下沉到：

- `TilingValidator` kernel

## 5. 如果走路线 B，`.v` 应该怎么动

### 5.1 不该先动的地方

下面这些不该成为 first move：

- `statement_tiling_witness`
- `tile_link`
- `TilingRelation` 的基本 relation
- `checked_tiling_validate`

因为 second-level 并没有要求新的 tiling semantics，只是要求更明确的 phase artifact。

### 5.2 真正该动的地方

最自然的改动面是这些参数/编排点：

1. `infer_tiling_witness_scops`
   - 当前只返回 `list statement_tiling_witness`
   - 可以升级成返回 `tiling_phase_artifact`
2. `try_verified_tiling_after_phase_mid`
   - 当前直接把 raw `after_scop` 交给
     `import_canonical_tiled_after_poly`
   - 应改成吃 `tpa_after_for_import`
3. `try_tiling_prepared_from_phase_correct`
   - theorem shape仍然是 “成功 codegen 的 loop refine 到 `pol_mid`”
   - 只是 proof 中要跟着新的 artifact record 解构一次

这样做的好处是：

- checked kernel theorem 不变
- `PolOpt.v` 的 orchestration boundary 更诚实
- second-level 新增的 contract 被精确记录在应该记录的地方

## 6. 我对 second-level 的正式建议

我会这样定：

1. Coq 核心 witness 和 tiling relation 不改。
2. `PolOpt` 层把 raw witness 变 canonical witness 这一步显式化。
3. raw/canonical added-dim 的 permutation 不进入 checked tiling kernel。
4. schedule-side canonicalization 只作为 phase artifact 的一部分被传下去。

一句话：

- second-level 的正确接入点是 `PolOpt` 的 phase artifact boundary
- 不是 `TilingValidator` 的 theorem kernel

## 6.1 默认关闭、参数启用时，`polopt` 和 `polcert` 应该怎么分层

如果目标是：

- 默认不改变当前 ordinary tiling 行为
- 只有显式传参时才启用 second-level

那这个“开关”不应该先进入 checked tiling theorem。

原因很简单：

- `checked_tiling_validate` 的 theorem 并不区分 “ordinary” 和 “second-level”
- 它只关心传进来的 `(mid, after, witness)` 是否满足现有 relation

所以：

- second-level 是否启用
- 应该先是 phase producer / import policy 的选择
- 不是新的 proof mode

### `polopt`

`polopt` 走的是 `PolOpt.v` 里的 extracted theorem-aligned 主链：

```text
run_pluto_phase_pipeline
  -> infer_tiling_witness_scops
  -> import_canonical_tiled_after_poly
  -> checked_tiling_validate_poly
```

这里最关键的约束是：

- `PolOpt.v` 当前只拿到一个 `after_scop`
- 然后直接把这个 `after_scop` 交给
  `import_canonical_tiled_after_poly`

所以如果 second-level 需要：

- canonical witness order
- 以及一个与该 order 对齐过的 `after_scop`

那么在 **不改 `PolOpt.v` 签名** 的前提下，`polopt` 这一侧就不能只改
`infer_tiling_witness_scops`。

它必须保证下面两件事同步发生：

1. `infer_tiling_witness_scops` 产出 canonical witness
2. `run_pluto_phase_pipeline` 返回的 `after_scop` 也已经按 canonical order
   做过 added-dim 重排

这也是为什么在 `polopt` 里，second-level 的最小可行 opt-in 设计应该是：

- 默认 mode 维持现状
- `--second-level-tile` 只切换 hand-written scheduler/extractor glue 的行为
- checked kernel 不知道这个 flag 的存在

如果以后想把这件事在 `.v` 里写得更诚实，再把它提升成上一节说的
`tiling_phase_artifact`。

### `polcert`

`polcert` 不同。它的 tiling validator 入口是：

- 读 `before.scop`
- 读 `after.scop`
- 抽 witness
- 本地导入 canonical tiled after
- 调 `checked_tiling_validate`

这里没有 `PolOpt.v` 那种“`after_scop` 只能由 phase runner 返回”的约束。

所以在 `polcert` 里，`--second-level-tile` 的最自然语义是：

1. 先从 raw `(before.scop, after.scop)` 抽取 raw witness
2. 做 dependency-aware canonicalization
3. 在导入前，把 raw `after.scop` 重排成 canonical added-dim order
4. 再走现有 checked tiling validate

也就是说：

- `polopt` 的 opt-in 点应主要放在 phase runner / extractor glue
- `polcert` 的 opt-in 点应主要放在 standalone validator import path

它们共享的是：

- 同一套 second-level canonicalization 逻辑

它们不应该共享的是：

- 完全相同的接线位置

### 参数语义建议

我建议两个可执行入口都统一用 Pluto 风格的名字：

- `--second-level-tile`

但默认行为保持 conservative：

- `polopt file.loop`
  - 继续 ordinary tiled path
- `polopt --second-level-tile file.loop`
  - 开启 second-level scheduler mode 和对应的 witness/after canonicalization
- `polcert --tiling before.scop after.scop`
  - 继续 ordinary witness extraction/import path
- `polcert --tiling --second-level-tile before.scop after.scop`
  - 开启 second-level canonicalization/import bridge

而下面这些组合应该直接拒绝，而不是静默忽略：

- `polopt --identity --second-level-tile`
- `polopt --notile --second-level-tile`
- `polcert --affine --second-level-tile ...`

因为 second-level 只在实际 tiled path 上才有意义。

### 当前实现状态

当前仓库里的 hand-written frontends 已经按这个方向落了一版最小实现：

- `polopt --second-level-tile`
  - 默认仍走 ordinary tiling
  - 开启后，scheduler tile phase 会把 Pluto `--second-level-tile` 打开
  - `run_pluto_phase_pipeline` 会在返回前把 `after_scop` canonicalize 到
    dependency order
- `polcert --tiling --second-level-tile`
  - 会在 standalone validator 路径上做同一套 canonicalization / import
    bridge
- 默认 ordinary mode 现在会显式拒绝 link 依赖 added iterators 的 witness
  - 也就是说 second-level 已经不再是“偶然也许能过”的行为
  - 而是必须显式 opt-in

当前仍然刻意没有打开的组合是：

- `--second-level-tile` + `--parallel`
- `--second-level-tile` + `--parallel-current`
- `--second-level-tile` + `--notile`
- `--second-level-tile` + `--identity`

这和前面的设计结论一致：先把 second-level 的 canonical witness / after
alignment 这条 sequential checked path 走稳，再考虑更高层组合。

## 7. diamond 从 `.v` 的角度更简单

diamond 最容易被误判成“需要新的 tiling theorem”，但从 `.v` 看恰恰相反。

`tile_link.tl_expr` 本来就是一般 affine expr，所以这些都只是现有对象的实例：

- `floor(i / T)`
- `floor((2*t+i) / T)`
- `floor((2*t-i) / T)`

因此 diamond 不应该优先改：

- `tile_link`
- `statement_tiling_witness`
- `TilingRelation`
- `TilingValidator`

diamond 的真正问题不在 `mid -> after` 这层，而在：

- `before -> mid`

更准确地说，问题是：

- 当前 `PolOpt` 假设 `mid` 是一个普通 affine midpoint
- 但 diamond 需要的 `mid` 是一个经过 concurrent-start/skew/hyperplane replacement 的 affine midpoint

## 8. diamond 对 `PolOpt` 的真正要求

从 `.v` 看，diamond 的理想接法是：

```text
before
  -> mid_diamond
  -> after_tiled
```

其中：

- `before -> mid_diamond`
  - 仍然由 affine validator 负责
- `mid_diamond -> after_tiled`
  - 仍然由现有 checked tiling validator 负责

所以从 theorem boundary 讲，diamond 的关键根本不是“新建 diamond tiling relation”，而是：

- phase pipeline 返回的 midpoint 是什么

这里要特别避免一种容易误导的说法：

- 不是 “默认 affine + ordinary tiling”
- 而是 “diamond-aware affine midpoint + ordinary tiling”

这也是为什么当前 `PolOpt.v` 的总体骨架其实已经接近正确：

- [PolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOpt.v#L167)

它已经把：

- affine validate
- checked tiling validate

分成两段了。

只要 `run_pluto_phase_pipeline` 最终返回的是一个“diamond-aware affine midpoint”，后面的 theorem 结构本来就能复用。

这和论文是一致的：diamond 的额外 intelligence 在 hyperplane
selection / replacement，而不是 ordinary tiling kernel 本身。

## 9. diamond 可能真正需要的 `.v` 改动，不在 tiling theorem

diamond 真正可能撞上的 `.v` 限制，是 midpoint importer，而不是 tiling core。

当前 `PolOpt.v` 在 phase pipeline 成功后，先做：

- `PolyLang.from_openscop_like_source pol mid_scop`

见：

- [PolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOpt.v#L177)

如果 diamond midpoint：

- 仍然是 domain 不变、只是 schedule 变了的 affine program

那这一步大概率无需 theorem 变化。

如果 diamond midpoint：

- 在 OpenScop 呈现上已经超出了 current `from_openscop_like_source`
  能接受的“source-like affine midpoint”

那么该扩的是：

- affine midpoint import API

而不是：

- tiling theorem

也就是说，最坏情况下需要新增的是一种：

- `from_openscop_affine_phase_mid`

及其对应 preservation / well-formedness theorem，
但 checked tiling kernel 仍然不该因为 diamond 被重写。

## 10. partial diamond 和 full diamond 在 `.v` 里不该分叉

对当前 sequential correctness 目标来说：

- partial diamond
- full diamond

不应该变成两个 theorem family。

从 `.v` 角度，它们的差别最多体现在：

- midpoint hyperplanes 的选择不同

更强的 concurrent-start / load-balance 语义若以后要证，再另立目标；
不要把它和当前 sequential theorem boundary 混在一起。

而不是：

- `mid -> after` 的 witness 类型不同

所以我会把它们统一成：

- 不同的 producer mode
- 一个共享的 affine midpoint interface
- 一个共享的 checked tiling route

## 11. 推荐的正式设计结论

### second-level

- witness core 已足够表达
- 新增复杂度应落在 `PolOpt` 的 phase artifact boundary
- 推荐把 “canonical witness + canonicalized after for import” 显式化
- 不推荐把 permutation / raw names 塞进 `TilingRelation`

### diamond

- tiling core 已足够表达
- 新增复杂度应落在 affine midpoint contract
- 首选方案是让 `run_pluto_phase_pipeline` 返回 diamond-aware midpoint
- 如果 midpoint importer 太窄，就扩 affine importer，不扩 tiling theorem

## 12. 推荐实施顺序

如果目标是最终真接进 `PolOpt`，我建议按下面顺序推进：

1. 先把 second-level 的 `PolOpt` phase artifact 设计定下来
   - 这是当前最明确的 theorem/API 边界问题
2. 再决定要走路线 A 还是路线 B
   - 我推荐路线 B
3. 等 second-level 边界稳定，再接 diamond
4. diamond 先只做 sequential correctness
5. parallel / concurrent-start / load-balance 全都后放

这样做的最大好处是：

- 每一步都沿着当前 theorem 骨架推进
- 不会把 Pluto feature 名字直接抬成新的 formal object
- `PolOpt` 的 verified story 也能保持整洁

## 13. 和当前 prototype 的关系

当前 OCaml synthetic prototype 已经给了一个很好的 sanity check：

- second-level 的 raw/canonical order bridge 是真实需要的
- diamond 的 midpoint 要求也是实实在在的，而不是文档想象

但从 `PolOpt` 接入角度，它们真正对应的层次应该是：

- second-level
  - `PolOpt` phase artifact contract
- diamond
  - affine midpoint contract

而不是：

- 再发明一层新的 checked tiling kernel

这就是这份文档最核心的结论。
