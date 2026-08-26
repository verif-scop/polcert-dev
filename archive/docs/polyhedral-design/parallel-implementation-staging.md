# Parallel Implementation Staging

本文不再讨论“parallel 为什么值得做”，而是把第一版实现的落地顺序压成一个执行清单。

现在它已经部分转成历史记录：

- Stage 1 到 Stage 5 的 single-dim first version 已经基本落地
- `--parallel`、`--parallel-strict`、`--parallel-current d` 已经接进前端
- default 与 `--iss` 两条路线都已支持 parallel

因此本文现在更适合作为：

- 为什么实现顺序当初这样安排
- 哪些阶段已经完成
- 哪些事情仍然只算后续扩展

它回答四个具体问题：

1. 第一版 verified `par for` 的最小目标到底是什么
2. 每个阶段应该先动哪些模块，后动哪些模块
3. 哪些文件适合在另一个 session 仍在改 ISS proof 时并行推进
4. 哪些阶段必须等到设计已经稳定后再碰共享主 pipeline

## 1. 第一版目标

第一版建议只承诺下面这个目标：

- 单一 current dimension 的 `par for`
- checked cert 落在 `current_view_pprog` 上
- Pluto 只作为 transform/search 引擎
- PolCert 自己 checked 地 cert `parallel_safe_dim`
- 最终 `par for` 的抽象并行语义本身被证明 refine 到顺序语义

当前实现已经把这个目标扩成了三个 concrete frontend 入口：

- automatic hinted route：`--parallel`
- strict hinted route：`--parallel --parallel-strict`
- manual route：`--parallel-current d`

并且三者都已覆盖：

- default route
- `--iss` route
- identity / affine-only / tiled path

第一版明确不做：

- `multipar`
- nested parallel
- `vector`
- `private` / reduction clause 的完整形式化
- 直接 trust Pluto `<loop>` extension

## 2. 推荐的实现阶段

### Stage 0：文档与 proof boundary 固化

这一阶段的产物就是当前这组 `parallel-*.md` 文档。

完成标准：

- `parallel` 不再被当成纯 printer 功能
- `par for` 语义必须 verified 这一点已经固定
- checker 放在 `current_view_pprog` 后这一点已经固定
- 第一版使用单层 single-dim cert 这一点已经固定

这一阶段不碰任何 Coq/OCaml 主文件。

状态：

- 已完成

### Stage 1：新增独立 Coq 模块骨架

先只新增文件，不改现有主 pipeline。

建议新增：

- `work/container-overlay/polcert/polygen/ParallelLoop.v`
- `work/container-overlay/polcert/src/ParallelValidator.v`
- `work/container-overlay/polcert/src/ParallelCodegen.v`

这一阶段只做：

- inductive / record / signature
- `erase_parallel`
- `parallel_plan`
- `parallel_cert`
- theorem statement inventory

这一阶段故意不做：

- `driver/PolOpt.v` integration
- `Scheduler.ml` flag plumbing
- pretty-print 到最终 SLoop/C 语法

好处是：

- 与另一个 ISS session 基本零冲突
- 可以先把 theorem dependency 和模块接口定住

状态：

- 已完成

### Stage 2：闭合 semantics 与 validator proof

仍然尽量不碰主 driver。

主要工作放在：

- `work/container-overlay/polcert/polygen/ParallelLoop.v`
- `work/container-overlay/polcert/src/ParallelValidator.v`

应完成：

- `seq_trace`
- `par_trace`
- `interleave_family`
- `parallel_semantics`
- `check_pprog_parallel_currentb`
- `checked_parallelize_current_sound`
- `parallel_semantics_refines_erased_sequential`

这一阶段结束时，应当已经能独立说清：

- 哪个 dim 被 cert 为 safe
- 为什么该 `par for` 的抽象并行语义不比顺序语义更弱

但此时还不要求主 pipeline 真正调用它。

状态：

- 已完成

### Stage 3：最小 API 接口接入

当 Stage 2 已稳定后，再碰公共 re-export 层。

建议此时只动：

- `work/container-overlay/polcert/src/Validator.v`

目的只是：

- 暴露 `checked_parallelize_current`
- 保持对外 API 风格与现有 validator 家族一致

这一阶段仍然不碰：

- `driver/PolOpt.v`
- `driver/Scheduler.ml`
- `syntax/SLoopMain.ml`

原因是：

- 一旦开始动这些文件，就进入真实产品路径，和其他 session 冲突概率显著上升

状态：

- 已完成

### Stage 4：Pluto/PolOpt plumbing

这是第一个会碰主 orchestrator 的阶段。

建议修改：

- `work/container-overlay/polcert/syntax/SLoopMain.ml`
- `work/container-overlay/polcert/driver/Scheduler.ml`
- `work/container-overlay/polcert/driver/PolOpt.v`

这一阶段的目标是：

- 用户可以传 `--parallel`
- 第二次 Pluto 调用可根据该 flag 选择 `--tile --parallel` 或 `--tile --noparallel`
- `PolOpt.v` 在 `current_view_pprog` 后插入 `checked_parallelize_current`

推荐数据流：

```text
after
-> current_view_pprog
-> choose candidate dim
-> checked_parallelize_current
-> if success then annotated_codegen
-> else prepared_codegen
```

这里的关键原则是：

- certification failure 必须安全回退到顺序 codegen
- Pluto hint 不可信时也必须安全回退

当前实现已落地：

- `--parallel`
- `--parallel-strict`
- `--parallel-current d`
- default route
- `--iss` route

状态：

- 已完成

### Stage 5：parallel codegen 与 printer 落地

这是最终把 proved parallel object 输出成程序语法的阶段。

如果第一版采用 `ParallelLoop` wrapper，则这一阶段的目标是：

- 将 `ParallelLoop` 投影到最终输出语言
- 并且保留 `ParMode` 的语法区别

可能涉及：

- `work/container-overlay/polcert/polygen/CodeGen.v`
- `work/container-overlay/polcert/src/PrepareCodegen.v`
- `work/container-overlay/polcert/syntax/SLoopPretty.ml`

但要注意：

- 不推荐一上来重写整个现有 `PrepareCodegen` / `CodeGen`
- 更推荐把新的 parallel codegen 做成桥接层，先与旧顺序 codegen 建立 `erase` 等价关系

状态：

- 已完成到第一版目标
- 当前输出对象仍然是 PolCert 的 loop-level `parallel for`
- 不包含 OpenMP/C runtime semantics

## 3. 文件冲突热区

从“与另一个 ISS session 并行工作”的角度，文件可以分成三类。

### 3.1 低冲突

这些文件最适合先推进：

- `doc/pluto-comprehensive/parallel-*.md`
- `work/container-overlay/polcert/polygen/ParallelLoop.v`
- `work/container-overlay/polcert/src/ParallelValidator.v`
- `work/container-overlay/polcert/src/ParallelCodegen.v`

原因：

- 都是新文件
- 不会直接破坏当前主 pipeline

### 3.2 中冲突

这些文件改动通常不深，但容易与别的 proof session 同时碰到：

- `work/container-overlay/polcert/src/Validator.v`
- `work/container-overlay/polcert/extraction/extraction.v`
- `work/container-overlay/polcert/Makefile.extr`

建议：

- 等新增模块结构稳定后再碰

### 3.3 高冲突

这些文件应尽量最后改：

- `work/container-overlay/polcert/driver/PolOpt.v`
- `work/container-overlay/polcert/driver/Scheduler.ml`
- `work/container-overlay/polcert/src/PrepareCodegen.v`
- `work/container-overlay/polcert/polygen/CodeGen.v`
- `work/container-overlay/polcert/syntax/SLoopMain.ml`
- `work/container-overlay/polcert/syntax/SLoopPretty.ml`

原因：

- 它们位于主 pipeline、外部工具调用、最终 codegen 或 CLI 边界
- 很容易和 ISS、tiling、printer 相关工作相互冲突

## 4. 推荐的证明与实现穿插顺序

不要按“从前到后把 pipeline 一次改完”的方式推进。  
更稳的顺序是先把证明对象做厚，再让 pipeline 消费它。

建议顺序：

1. 完成 `ParallelLoop` definitions-only skeleton
2. 完成 `ParallelValidator` definitions-only skeleton
3. 证明 `interleave_family` 基础引理
4. 证明 `checked_parallelize_current_sound`
5. 证明 `parallel_semantics_refines_erased_sequential`
6. 只在这之后再写 `annotated_codegen`
7. 最后才接 `PolOpt.v` / `Scheduler.ml`

这样做的价值是：

- 若 parallel proof 方向需要调整，返工只在新增模块里发生
- 不会过早污染主 pipeline

## 5. 失败与回退边界

parallel 这条线必须设计成“即使部分失败，也不破坏现有 verified sequential 主线”。

推荐的回退规则如下。

### 5.1 Pluto 不产生可用 hint

处理方式：

- 完全允许
- PolOpt 自己扫描 candidate dim

### 5.2 Pluto hint 与 current view 对不齐

处理方式：

- 丢弃 hint
- 不影响 transform correctness

### 5.3 `checked_parallelize_current` 失败

处理方式：

- 直接回退到顺序 `prepared_codegen`

### 5.4 parallel codegen 层尚未实现完全

处理方式：

- `--parallel` 先只驱动 Pluto transform search
- 但最终仍输出顺序程序

这不是最终目标，但在中间阶段是可以接受的工程断点。

## 6. 何时才算可以开始改共享主文件

我建议只有同时满足下面三条时，才开始动 `PolOpt.v` 和 `Scheduler.ml`：

1. `ParallelLoop` 的核心定义已经稳定
2. `checked_parallelize_current_sound` 已经成立
3. `parallel_semantics_refines_erased_sequential` 已经有明确 theorem 形状，最好已有 proof skeleton

否则过早集成只会放大返工范围。

## 7. 对当前并行协作的具体建议

这一节现在主要是历史记录。

在另一个 session 正在做 ISS pass proof 的情况下，最安全的分工是：

- 当前 parallel 这条线优先只动文档和新模块
- 暂不碰 `driver/PolOpt.v`
- 暂不碰 `driver/Scheduler.ml`
- 暂不碰 `src/PrepareCodegen.v`

等 ISS 那边收敛后，再进入 Stage 4 和 Stage 5。

如果必须提前开始实现，也建议先在独立 worktree / 独立容器源码目录中推进，并坚持下面规则：

- 只新增文件，不修改共享 driver
- 一旦要改高冲突文件，先做范围极小的接口变更
- 看到非自己引入的脏改动时立即停下重新比对

## 8. 当前剩余扩展

第一版已经完成后，剩下更适合放到后续扩展的只有：

- reduction-aware parallel
- nested / multipar
- 更系统的 regression/CI 覆盖
- 若将来需要，再讨论更具体的 backend runtime 语义

## 9. 最后的收束

parallel 的第一版实现，不应被理解成“给现有 codegen 加个 pragma”。  
它更像是在现有 verified affine+tiling 主线之后，再叠加一条新的 verified layer：

- current-view 上的 checked parallel cert
- 带抽象并行语义的 loop IR
- 与顺序语义可组合的 refinement theorem

因此最稳的执行策略是：

- 先新增模块
- 再闭证明
- 最后集成主 pipeline

而不是反过来。
