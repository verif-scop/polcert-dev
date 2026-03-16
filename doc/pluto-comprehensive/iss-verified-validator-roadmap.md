# ISS Verified Validator Roadmap

本文档给出一个面向 `polcert/polopt` 的长期路线图，目标是：

- 构建一个 **Coq verified ISS validator**
- 该 validator 能验证 **Pluto 的 ISS pass**
- 并且能 **无缝融合进当前 PolCert/PolOpt 相位式工作流**

这里的 “ISS” 特指 Pluto 的 `index set splitting`，即：

- 在 scheduling 之前
- 对 statement family 做 duplication
- 对 iteration domain 做 partition
- 然后把后续优化交给现有 affine scheduling / tiling 路线

## 1. 目标与非目标

### 1.1 最终目标

最终目标不是证明 Pluto `iss.c` 的 cut 搜索算法，而是：

- Pluto 作为 **untrusted optimizer**
- Coq 侧提供 **trusted validation**

换句话说，目标是：

```text
Pluto emits P0, Piss, witness
checker validates witness
Coq proves:
  checker_sound
  -> domain_partition_refinement P0 Piss
  -> backward simulation from Piss to P0
```

在当前 `polcert` 项目的证明风格里，最终暴露给 driver 的 correctness
contract 仍然是：

```text
instance_list_semantics after st1 st2
-> exists st2',
     instance_list_semantics before st1 st2'
  /\ State.eq st2 st2'
```

也就是说，ISS validator 追随现有 affine / tiling validator 的
`after -> before` soundness 风格，而不是单独引入一个新的双向 theorem
接口。

### 1.2 明确非目标

以下内容不应成为第一阶段目标：

- 证明 `pluto_find_iss` 的 LP/Farkas/lexmin 搜索过程
- 把 ISS 硬塞进现有 `validate_general`
- 依赖 `after.scop` 单独反推所有 split 信息
- 先做通用 arbitrary polyhedral partition checker

这些方向都更重，而且不符合 Pluto 当前实现形态。

## 1.3 当前实现状态（2026-03-16）

目前已经有一批正式落地到 `polcert` 源码中的 ISS 基础模块：

- `src/ISSWitness.v`
  - Pluto-style ISS witness 的数据定义
  - `cuts / parent_stmt / piece_signs` 的严格比较函数
- `src/ISSRefinement.v`
  - `payload_eq_except_domain`
  - `stmt_partition_refinement`
  - `domain_partition_shape`
  - `domain_partition_refinement`
  - `iss_signed_cut_constraint / iss_piece_constraints`
- `src/ISSBoolChecker.v`
  - 第一版 **shape-only checker**
  - 当前检查：
    - before/after `varctxt` 一致
    - before/after `vars` 一致
    - `parent_stmt` 在范围内
    - 每个 after statement 与 parent 的 payload 相同，允许 domain 不同
- `src/ISSBoolChecker.v` / `src/ISSRefinement.v`
  - 现已额外落下一个 **cut-shape checker layer**
  - 当前还能检查：
    - `piece_signs` 长度与 `cuts` 一致
    - after domain 是否精确等于 `source_domain ++ selected_cut_constraints`
  - 并已证明：
    - `check_domain_partition_cut_shapeb_sound`
- `src/ISSBoolChecker.v` / `src/ISSRefinement.v`
  - 现已进一步落下一个 **complete-cut-shape checker layer**
  - 当前还能检查：
    - 每个 parent family 的 `piece_signs` 不重复
    - 每个 parent family 覆盖全部期望的 sign 组合
    - 因而把 `coverage / disjointness` obligations 直接下推到 Coq
  - 并已证明：
    - `check_domain_partition_complete_cut_shapeb_sound`
    - `domain_partition_refinement_from_complete_cut_shape`
- `src/ISSRefinement.v`
  - 现已新增一个更偏 top-down 的抽象层：
    - `parent_partition_properties`
    - `domain_partition_refinement_obligations`
    - `domain_partition_refinement_from_obligations`
  - 这层的作用是把后续 proof target 固定成：
    - shape / payload / domain reconstruction
    - 再加 cover/disjointness obligations
    - 推出最终 refinement
- `src/ISSValidator.v`
  - 对外暴露 ISS 结构层 API
- `src/ISSSemantics.v`
  - point-level transport helpers
  - after->before / before->after 的 statement-family rebasing 支撑引理
- `src/ISSCutSemantics.v`
  - complete-cut-shape -> `PolyLang.poly_instance_list_semantics`
  - complete-cut-shape -> `PolyLang.instance_list_semantics`
- `src/ISSValidatorCorrect.v`
  - proof-only theorem：
    `checked_iss_complete_cut_shape_validate = true`
    蕴含 backward `instance_list_semantics`
- `src/Validator.v`
  - 已经把 ISS 结构层 API 统一接进总 façade

另外，Pluto 侧现在也已经有一个原生、无损的 ISS bridge 导出路径：

- `--dump-iss-bridge`
  - 直接导出 `before domains / after domains / cuts / stmt witnesses`
  - 不再依赖 Python 从 debug dump 反推 witness

这批模块和接口已经通过：

- Coq 全量强制重编
- `make proof`
- `Validator` / `PolOpt` / `TPolValidator` 上层依赖重编
- extraction 重跑
- `polopt` 重链接
- `./polopt --validate-iss-bridge`
- `./polopt --validate-iss-pluto-live-suite`

所以当前状态不是纯文档设计，而是：

- **ISS validator 的抽象层与第一层结构 checker 已经进入主提取链**
- **cut-based domain reconstruction checker 已经进入主提取链**
- **cut-family completeness / partition checker 已经进入主提取链**
- **top-down refinement obligations theorem 也已经进入主提取链**
- **ISS 的 backward semantic correctness theorem 已经落在 proof-only 模块里**
- **Pluto 原生 bridge 已经把 live ISS validation path 从 Python witness recovery 中解耦出来**
- **当前已经形成一条可手动执行的 end-to-end Pluto ISS -> extracted Coq validator 路径**

当前尚未做成默认流水线的部分只剩工程选择，而不是 proof 空洞：

- ISS suite 还未加入默认 CI
- `driver/PolOpt.v` 的主优化流水线还没有默认接入 ISS phase
- 版本化的 Pluto base image 还未替换掉当前 CI 中的 `latest`

这一层最近已经在真实容器里重新验证过：

- `ISSRefinement / ISSBoolChecker / ISSValidator / Validator` 重新编译通过
- `ISSSemantics / ISSCutSemantics / ISSValidatorCorrect` 重新编译通过
- `opam exec -- make -j1 proof` 通过
- `opam exec -- make -j1 polopt` 通过
- `./polopt --validate-iss-debug-dumps ...reverse...` 通过，输出
  `validation: OK (coq complete-cut-shape)`
- `./polopt --validate-iss-pluto-suite` 通过
- `./polopt --validate-iss-pluto-live-suite` 通过

## 2. 当前代码库事实

### 2.1 PolCert 当前流水线

当前 `driver/PolOpt.v` 的真实路线是：

- 先提取 `PolyLang` program
- 再走 affine scheduling validator
- 然后可选地做 tiling witness 恢复和 verified tiling validate

关键入口在：

- `phase_pipeline_opt_prepared_from_poly`
- `try_verified_tiling_after_phase_mid`
- `ValidatorCore.validate`
- `ValidatorCore.checked_tiling_validate_poly`

这说明当前项目已经接受一种“phase-specific validator + shared pipeline”的结构。

### 2.2 现有 validator 的边界

`AffineValidator` / `validate_general` 的本质前提仍然是：

- before/after statement family 一一对应
- domain / accesses / transformations / witness / instr 等逐项相同
- 只允许 schedule 变化

所以 ISS 不能直接复用它。

### 2.3 PolyLang 语义层是够的

`PolyLang` 本身并不要求前后 program 有同样数量的 statements。
它的语义是：

- flatten 成 instruction points
- 再按 schedule 排序执行

因此 ISS 后程序自然可以表示成：

- 多个 `PolyInstr`
- payload 相同
- 只有 `pi_poly` 被切成多个 pieces

这意味着：

- **语义层不用重写**
- 真正要新增的是 **program-level structural relation**

### 2.4 Pluto 当前 ISS 的实际对象

Pluto 的 ISS 实际工作在：

- `PlutoProg`
- `Stmt`
- `Dep`

而不是 OpenScop，也不是 isl schedule tree。

对验证来说，Pluto 当前 ISS 真正输出的语义核心是：

- statement duplication
- domain split
- dependence remap

## 3. 顶层设计：抽象层与 Pluto 实例层分离

### 3.1 抽象层：通用 refinement 定理

最干净的主定理应该建立在一个 **通用 relation** 上：

```text
domain_partition_refinement P0 Piss
```

它只表达：

- `P0` 和 `Piss` 使用同一个 `varctxt / vars`
- `Piss` 每个 statement 都有一个 parent，指向 `P0` 中某个 statement
- 除 domain 外，payload 相同
- parent statement 的 pieces 构成原 domain 的不交覆盖

这个 relation 不提 Pluto，也不提 midpoint cut。

### 3.2 Pluto-specific 层：cut-based witness

Pluto 实例层再给一个可执行 witness：

- `parent_stmt : after_stmt -> before_stmt`
- `cuts : before_stmt -> list affine_hyperplane`
- `piece_signs : after_stmt -> list sign`

checker 只需验证：

- 每个 after domain 是否等于 `source_domain ∩ chosen_halfspaces`
- piece_signs 是否形成完整布尔组合
- payload 是否与 parent 一致

这样 coverage/disjointness 不需要做昂贵的一般 polyhedral union 证明，
因为它们由 cut schema 直接推出。

## 4. 证明路线

### 4.1 第一主定理：抽象 refinement 的语义正确性

目标 theorem：

```text
domain_partition_complete_cut_shape_to_before_correct :
  domain_partition_complete_cut_shape P0 Piss w ->
  instance_list_semantics Piss st1 st2 ->
  exists st2',
    instance_list_semantics P0 st1 st2' /\ State.eq st2 st2'
```

这条 theorem 已经在 `src/ISSCutSemantics.v` 中落地。
它和项目现有 affine / tiling validator 的 correctness contract 保持一致，
都是 backward simulation。

### 4.2 证明思路

证明主线应围绕 flattened instruction points：

1. 对于 `P0` 的每个执行点，由于 pieces 构成不交覆盖，它在 `Piss`
   中恰好属于一个 piece。
2. 对应点的：
   - instruction
   - transformation
   - access transformation
   - schedule
   - depth
   都保持不变。
3. 因此前后差别只剩 statement family bookkeeping。
4. 最终把它归约成 point-list reindexing / rebasing 不影响语义。

现有项目里与之最接近的 proof style 是：

- `Extractor` 里关于 `ip_nth` rebasing 的引理
- `TilingRelation` 里关于 point-list transport 的引理

### 4.3 第二主定理：Pluto checker soundness

目标 theorem：

```text
iss_checker_sound :
  check_iss P0 Piss w = true ->
  domain_partition_refinement P0 Piss
```

这里的 `check_iss` 是 Pluto-specific，可执行。

### 4.4 第三层：checked validator correctness

在结构 theorem 之上，再把布尔 checker 接成对外可用的 correctness theorem：

```text
checked_iss_complete_cut_shape_validate_semantics_correct :
  checked_iss_complete_cut_shape_validate P0 Piss w = true ->
  instance_list_semantics Piss st1 st2 ->
  exists st2',
    instance_list_semantics P0 st1 st2' /\ State.eq st2 st2'
```

这条 theorem 已经在 `src/ISSValidatorCorrect.v` 中落地。

如果以后要把 ISS 默认并入 `driver/PolOpt.v`，再在这一层之上叠 driver theorem 即可。

## 5. Coq 模块规划

建议新增如下模块：

### 5.1 `src/ISSWitness.v`

职责：

- 定义 Pluto-specific witness schema
- 只包含数据，不做主语义

建议内容：

- `iss_cut`
- `iss_piece_sign`
- `iss_stmt_witness`
- `iss_witness`

### 5.2 `src/ISSRefinement.v`

职责：

- 定义抽象 relation
- 给出语义主定理

建议内容：

- `payload_eq_except_domain`
- `stmt_partition_refinement`
- `domain_partition_refinement`
- `domain_partition_refinement_correct`

### 5.3 `src/ISSBoolChecker.v`

职责：

- 可执行 checker
- 贴近 Pluto witness schema

建议内容：

- `check_payload_match`
- `check_piece_domain`
- `check_parent_partition`
- `check_iss`

### 5.4 `src/ISSValidator.v`

职责：

- 把 bool checker 和 refinement theorem 接起来
- 提供 PolCert 外部 API

建议内容：

- `checked_iss_validate`
- `iss_checker_sound`
- `checked_iss_validate_correct`
- `checked_iss_validate_implies_wf_after`

### 5.5 `src/Validator.v`

对外 façade 应增加：

- `checked_iss_validate`
- `checked_iss_validate_correct`
- `checked_iss_validate_implies_wf_after`

这与当前 tiling façade 保持平行。

## 6. Driver / PolOpt 集成路线

### 6.1 不要混淆真实 phase 和 checker artifact

沿用当前清晰命名：

- `P0`: ISS 前真实程序
- `Piss`: ISS 后真实程序
- `Psched`: 调度后真实程序
- `Ptile`: tiling 后真实程序

避免引入会和 tiling internal artifact 混淆的 `mid` 名字。

### 6.2 与现有 phase pipeline 的融合方式

最自然的组合方式是：

1. `P0 -> Piss`
   - 用 ISS validator
2. `Piss -> Psched`
   - 用现有 affine validator
3. `Psched -> Ptile`
   - 用现有 tiling validator

也就是说 ISS 是一个 **独立 phase validator**，不是 affine validator 的补丁。

### 6.3 Driver 端建议新增接口

在 `PolIRs` / driver 层建议平行增加：

- `export_for_phase_iss`
- `run_pluto_iss_phase`
- `infer_iss_witness_phase`

第一阶段可以不 fully wire 进 `PolOpt.Opt` 主链；
先做一个独立入口就够：

- `checked_iss_validate_scops`
- `checked_iss_validate_poly`

之后再并入主流水线。

## 7. Pluto 侧接口规划

### 7.1 为什么不优先走 OpenScop

ISS 真正工作的对象是 `PlutoProg`。

强行走 OpenScop 有两个问题：

- PET 前端本来就不支持 `--dumpscop`
- ISS 后 statement 数量变化，现有 `pluto_populate_scop` 不稳

所以 ISS validator 的正式接口不应先押注 OpenScop。

### 7.2 推荐的 Pluto 导出格式

推荐 Pluto 增加一个新的、无损导出：

- `--dump-iss-json`
  或
- `--dump-plutoprog`

至少导出：

- before / after statement domains 的原始矩阵
- schedule / transformation / access matrices
- `parent_stmt`
- cuts
- piece sign choices

这足够支持 ISS checker。

### 7.3 正式接口不应依赖 pretty print

当前 `pluto_prog_print` 用于实验够了，但正式接口不够：

- 变量名会截断
- 结构信息是 pretty print，不是原始矩阵

所以它适合原型研究，不适合 trusted pipeline。

## 8. 测试路线

### 8.1 Pluto 正例集

ISS 正例不应主要依赖当前 62 个 PolCert loop suite。
应优先使用 Pluto 自带的 ISS 例子：

- `reverse-iss`
- `multi-stmt-periodic`
- `jacobi-2d-periodic`
- `heat-2dp`

这些例子已经实际确认会发生 ISS split。

### 8.2 负例测试

应手工构造 witness 破坏项：

- parent map 错
- cut 符号错
- 丢一个 piece
- 重复一个 piece
- 改 payload
- 改 schedule

要求 checker 明确拒绝。

### 8.3 PolCert 流水线回归

接线后至少要回归：

- `make test`
- `test-polopt-loop-suite`
- Pluto affine-only 路线
- 现有 tiling 路线

ISS validator 的引入不能影响当前非 ISS case。

## 9. 里程碑

### M0：研究基线稳定

完成条件：

- Pluto baseline 有明确 git tag
- PolCert Docker/CI 对 Pluto baseline 有显式记录和检查

当前状态：

- 已完成 git-side baseline 和 PolCert-side baseline checking
- Docker Hub 侧版本化 image tag 仍待发布

### M1：抽象证明对象冻结

完成条件：

- `domain_partition_refinement` schema 定稿
- witness schema 与 theorem 层严格分开

### M2：Coq 抽象 theorem

完成条件：

- `domain_partition_refinement_correct` 证明完成

### M3：Bool checker 原型

完成条件：

- 可执行 `check_iss`
- 正/负例测试跑通

### M4：Checker soundness

完成条件：

- `iss_checker_sound` 完成

### M5：PolCert façade 集成

完成条件：

- `Validator.v` 导出 ISS validator
- 可从 driver 层调用

### M6：Driver 相位集成

完成条件：

- `P0 -> Piss` 可作为真实 phase 被调用和验证

### M7：Pluto 真实接口闭环

完成条件：

- Pluto 导出 witness / matrices
- PolCert 直接消费 Pluto ISS 输出

## 10. 当前最优先的 auto research 任务

按优先级，我建议接下来直接做：

1. 精确定义 `payload_eq_except_domain`
2. 精确定义 `stmt_partition_refinement`
3. 精确定义 `domain_partition_refinement`
4. 列出其所需的 supporting lemmas：
   - flattened point coverage
   - uniqueness
   - reindexing invariance
5. 单独设计 Pluto witness schema
6. 再开始写 bool checker

这条顺序能保证：

- theorem 先于 implementation
- abstraction 先于 Pluto-specific heuristics
- 论文结构先于工程细节

## 11. 当前结论

我现在的稳定判断是：

- ISS validator 是值得做的，而且能自然接进当前 `polcert/polopt`
- 最好的路线不是证明 Pluto `iss.c` 算法本身
- 而是：
  - 抽象 `domain_partition_refinement`
  - 证明它的 `PolyLang` 语义正确性
  - 再用 Pluto witness/checker 实例化它

如果继续推进，下一阶段就不该再停留在“ISS intuition”层面，
而应该正式开始写 Coq-level schema 和 proof obligations。
