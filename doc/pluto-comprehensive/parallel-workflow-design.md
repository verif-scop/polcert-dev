# Parallel Workflow Design

本文回答一个更工程化的问题：

> 如果要把 `parallel for` 真正接进 PolOpt / PolCert 的现有 pipeline，用户选项、Pluto 调用、checked certification、codegen、以及 theorem layering 分别应该落在哪个模块上？

和 `parallel-proof-strategy.md` 的区别是：

- `parallel-proof-strategy.md` 主要谈“并发本身如何证明”
- 本文主要谈“这套证明和工程 workflow 如何对接”

## 1. 当前可观测到的事实

先把当前代码里的关键事实固定下来。

### 1.1 Pluto 的 `parallel` flag 在哪里读

Pluto 命令行的 `--parallel` / `--noparallel` 在：

- `/pluto/tool/main.cpp`

中直接写到：

- `options->parallel`

之后它会影响两个地方：

1. transform side
   - `parallel && !tile && !identity` 时，Pluto 会在 affine schedule 后调用 `pluto_create_tile_schedule`
   - `tile && parallel` 时，Pluto 会在 tile 后再次做 tile-schedule / wavefront 相关处理
2. codegen / metadata side
   - OpenMP pragma
   - OpenScop `<loop>` extension

### 1.2 当前 PolOpt phase pipeline 的 Pluto 调用是固定的

当前 `driver/Scheduler.ml` 里固定有两次 Pluto 调用：

1. affine-only call
   - 带 `--noparallel --notile`
2. tile-only call
   - 带 `--tile --noparallel`

这意味着今天的 verified mainline 根本没有让 Pluto 在 transform search 时考虑 parallel。

### 1.3 当前 phase pipeline 的 verified 骨架

当前 `driver/PolOpt.v` 的 phase pipeline 大致是：

```text
extractor
-> strengthen
-> affine mid
-> tiled after
-> checked_tiling_validate_poly mid after
-> current_view_pprog after
-> prepared_codegen
```

这条线已经闭合：

- transform correctness
- current-view bridge correctness
- sequential codegen correctness

parallel 目前不在这条 proof story 里。

## 2. 推荐的职责切分

这一块必须很明确，否则之后容易把“优化器做的事”和“证明器做的事”混掉。

### 2.1 Pluto 的职责

Pluto 负责：

- schedule / tiling / wavefront 的外部搜索
- 产出更并行友好的 `after.scop`
- 可选地产出 `<loop>` hint

Pluto 不负责成为 trusted proof object。

### 2.2 PolOpt 的职责

PolOpt 负责：

- 接受用户的 `--parallel` 请求
- 把请求传给合适的 Pluto 调用
- 选择 candidate dimension
- 组织 checked certification
- 让最终 codegen 输出 annotated `parallel for`

换句话说，PolOpt 这次同时承担：

- transform orchestration
- final loop annotation placement

### 2.3 PolCert 的职责

PolCert 负责：

- 对 `current_view_pprog` 上的 parallel candidate 做 checked certification
- 给出 soundness theorem
- 为 `par for` 的抽象并行语义提供被证明的 correctness bridge

PolCert 不负责：

- 启发式选择哪一层
- 直接相信 Pluto `<loop>`
- 直接输出最终 C/OpenMP

## 3. 推荐的 end-to-end workflow

这是我现在最推荐的工作流。

### 3.1 用户层

用户对 PolOpt 传：

- `--parallel=false`
  - 保持今天的行为
- `--parallel=true`
  - 允许 Pluto 在 tiled stage 做 parallel-aware transform
  - 并在 codegen 前尝试 checked parallelization

第一版不建议把 CLI 暴露得太复杂。  
例如先不要直接暴露：

- `--multipar`
- `--innerpar`
- `--forceparallel`

先只做一个布尔开关，把 pipeline 走通。

### 3.2 Pluto 调用层

当前 phase pipeline 仍然保持：

```text
iss -> affine -> tiling
```

但第二次 Pluto 调用不再固定 `--noparallel`，而是：

- 若 `parallel=false`，继续 `--tile --noparallel`
- 若 `parallel=true`，改成 `--tile --parallel`

第一阶段 affine-only Pluto call 建议保持：

- `--noparallel --notile`

原因是：

- 当前主 pipeline 的结构是“先得到稳定 affine mid，再做 tiling after”
- 先不要在第一阶段引入 `parallel + notile` 的额外 schedule search 复杂度

也就是说：

- `parallel` 在现阶段不是一个新主 route
- 它是一个影响第二阶段 Pluto tiling/search 行为的选项

### 3.3 OpenScop import 层

Pluto 若开启 `--parallel`，可能会在 `after.scop` 中带 `<loop>` extension。

推荐处理是：

- 可以导入为 `parallel_hint`
- 但绝不作为 trusted cert

因此 importer 层的建议是：

1. 短期：
   - 即使继续忽略 `<loop>`，主 correctness story 也能成立
2. 中期：
   - 把 `<loop>` 导入为 hint/debug metadata
   - 用于帮助 PolOpt 优先尝试某个 current dimension

### 3.4 transform validation 层

parallel 不改变现有 transform validation 的位置。

仍然是：

```text
mid -> after
```

通过：

- `checked_tiling_validate_poly`

来证明 transformed tiled program 本身语义正确。

这一步不应承担：

- parallel loop safety certification

### 3.5 current-view 层

`current_view_pprog` 之后，程序进入：

- codegen 真正消费的 current-space 视图

这一步之后再做 parallelization certification，是最干净的。

推荐 pipeline 是：

```text
... -> checked_tiling_validate_poly
-> current_view_pprog
-> choose candidate parallel dimension
-> checked_parallelize_current
-> annotated_codegen
```

### 3.6 candidate 选择层

candidate 的选择应视为 PolOpt 的 heuristic，而不是 theorem 本身的一部分。

推荐顺序：

1. 如果有 Pluto `<loop>` hint，则先尝试把 hint 对齐到 current dimension
2. hint 不可用或 cert 失败，则按内部 heuristic 选
3. 第一版 heuristic 只选一个最外层 safe dimension

因此：

- candidate selection 不需要被证明 optimal
- 只需要最终 cert 过关

### 3.7 checked certification 层

PolCert 暴露一个新 phase，例如概念上：

```text
checked_parallelize_current : pprog -> parallel_plan -> result parallel_cert
```

其语义是：

- 若返回成功，则 `parallel_cert_sound`

第一版可以把 `parallel_plan` 极度简化成：

- 一个 current-space dimension `d`

### 3.8 codegen 层

codegen 不再只生成 plain sequential loop，而是生成：

- 带 parallel annotation 的 loop representation

这里有两条实现路线：

1. 直接扩展 `Loop`
2. 新增 `ParallelLoop` wrapper

proof engineering 上，我更偏向先做第 2 条。  
无论哪条路线，codegen 都要消费：

- `current_view_pprog`
- `parallel_cert`

并把 cert 上的 current dimension 映射到最终 emitted loop 节点。

这里最终被证明的对象必须是：

- 带 `par for` 语义的 loop representation

而不只是：

- 一个会打印 pragma 的语法节点

## 4. 推荐的数据流对象

为了避免不同层说的都是“parallel 信息”但其实指的是不同东西，建议显式区分下面四类对象。

### 4.1 `parallel_request`

来自用户。

含义：

- 这次优化是否允许生成并发 loop

第一版：

```text
bool
```

### 4.2 `parallel_hint`

来自 Pluto `<loop>` extension` 或其他外部启发式信息。

含义：

- Pluto 倾向哪一层 loop 并行

第一版可以只记录：

- iterator name
- 对应 statement ids
- directive bits

### 4.3 `parallel_plan`

由 PolOpt 内部 heuristic 产出。

含义：

- 准备送给 PolCert 去 cert 的候选方案

第一版最简单可以是：

```text
{ target_dim : nat }
```

### 4.4 `parallel_cert`

由 PolCert checked 返回。

含义：

- 某个 plan 已被证明 parallel-safe

第一版可以和 plan 同构，但 theorem 上地位不同：

```text
{ certified_dim : nat }
```

重点不在数据结构多复杂，而在：

- `cert` 只能由 checker 成功产生

## 5. parallel cert 最好在什么语义对象上定义

推荐 cert 直接绑定：

- `current_view_pprog`

而不是：

- source loop AST
- raw OpenScop scattering rows
- 最终 Loop AST 节点编号

原因有三条。

### 5.1 current-space 是 codegen 真正面对的空间

最终 loop 是按 current dimensions 生成出来的。  
所以 cert 若绑定到 current dimension，映射最自然。

### 5.2 current-view 已经过现有 correctness bridge

`instance_list_semantics_current_view_iff` 已经说明：

- current-view 只改变表示，不改变语义

所以把 cert 放在这里很干净。

### 5.3 这时依赖信息仍然完整

current-view program 里仍然保留：

- domains
- schedules
- accesses
- instruction-point structure

足够做 checked certification。

## 6. 推荐的 semantics / IR 边界

### 6.1 不推荐“只在 pretty-printer 里输出 pragma”

因为那样最终输出的程序和 theorem 对象脱钩。

### 6.2 也不推荐“plain Loop codegen 后再盲 post-pass 猜哪层并行”

因为 plain Loop AST 上已经缺少稳定的 current-dimension 对应信息。

若真要 post-pass，也必须让 codegen 事先保留：

- origin dimension
- loop identity tag

这样它本质上也已经是一个 annotated IR 了。

### 6.3 推荐的第一版 IR 边界

proof engineering 上，第一版更推荐：

1. 保留现有 `Loop`
2. 新增 `ParallelLoop`
3. 定义 `erase_parallel : ParallelLoop.t -> Loop.t`

原因是：

- `prepared_codegen_correct_general` 可以原封不动保留
- 新 parallel theorem 能直接叠在旧 theorem 之上
- 与另一个 session 正在改的核心 sequential proof 栈耦合更小

等 parallel 方案稳定后，再考虑是否把 annotation 合并回 `Loop`。

但无论选择 wrapper 还是直接扩展 `Loop`，都必须新增：

- `par for` 的抽象并行语义
- 以及这份并行语义到顺序语义的 correctness theorem

## 7. 推荐的 theorem stack

下面是我当前最认可的一组 theorem 关系。

### 7.1 已有 theorem

现有主线继续保留：

1. `validate_correct`
2. `checked_tiling_validate_correct`
3. `instance_list_semantics_current_view_iff`
4. `prepared_codegen_correct_general`

### 7.2 新增 theorem：checker soundness

推荐形状：

```text
checked_parallelize_current pp_cur plan = cert
-> parallel_cert_sound pp_cur cert
```

### 7.3 新增 theorem：annotated codegen 擦除回顺序 codegen

推荐形状：

```text
erase_parallel (annotated_codegen pp_cur cert)
= prepared_codegen pp_cur
```

或者至少给出等价语义。

### 7.4 新增 theorem：并行语义 refine 到擦除顺序语义

推荐形状：

```text
parallel_cert_sound pp_cur cert
-> ParallelLoop.parallel_semantics (annotated_codegen pp_cur cert) st st'
-> Loop.semantics (erase_parallel (annotated_codegen pp_cur cert)) st st'
```

如果状态等价不是严格相等，则再带一个 `State.eq`。

这是 workflow 里最不能省的一步。  
没有这一步，就只能说“输出了 parallel syntax”，不能说“verified parallel for”。

### 7.5 合成得到最终 theorem

最终要得到：

```text
parallel_cert_sound pp_cur cert
-> ParallelLoop.parallel_semantics (annotated_codegen pp_cur cert) st st'
-> PolyLang.instance_list_semantics pp_cur st st'
```

若把 `pp_cur = current_view_pprog after` 再和现有 theorem 串起来，就回到整个 pipeline correctness。

## 8. 一个更具体的模块划分建议

为了减少和现有代码的耦合，我建议把 parallel 支持拆成四个新模块层次。

### 8.1 `ParallelHint`

职责：

- 解析/保存 Pluto `<loop>` hint
- 提供与 current dimension 的对齐辅助

可信度：

- untrusted

### 8.2 `ParallelValidator`

职责：

- 定义 `parallel_plan`
- 定义 `parallel_cert`
- 实现 `check_pprog_parallel_currentb`
- 证明 soundness

可信度：

- checked core

### 8.3 `ParallelCodegen`

职责：

- 把 `parallel_cert` 映射到 annotated loop
- 定义 `erase_parallel`
- 定义 parallel-aware codegen wrapper

可信度：

- theorem-bearing codegen layer

### 8.4 `ParallelPretty`

职责：

- 输出 `parallel for`
- 后续可加 `vector`

可信度：

- 最薄的打印层

## 9. 第一版应该明确砍掉什么

如果不主动收缩范围，parallel 设计很容易失控。

第一版建议明确不做：

- `multipar`
- vector
- `forceparallel`
- full OpenMP runtime formalization
- Pluto `<loop>` 成为 trusted object
- private var clause 的复杂生成

第一版目标只应是：

- 单层 parallel dimension
- checked certification
- 抽象并行语义 correctness
- 最终能打印 `parallel for`

## 10. 关于 private vars 的一个重要判断

Pluto 的 `<loop>` extension` 会带 private vars。  
但这不意味着 PolCert 第一版必须照抄。

当前 Loop/pretty-print 链里并没有像 Pluto CLAST 那样的大量显式临时标量界变量。  
因此第一版最合理的策略是：

- 先只支持当前 codegen 自己原生生成的 loop 结构
- 只在该结构上打印最小的 `parallel for`
- 不把 Pluto 的 `private(...)` 直接当成 proof 义务

如果未来 codegen 引入显式 temporary bound vars，再扩这个问题。

## 11. 当前最推荐的最终工作流

如果把所有层收束成一句话，我当前最推荐的工作流是：

```text
user --parallel
-> PolOpt 在第二次 Pluto 调用里开启 --tile --parallel
-> Pluto 产出更并行友好的 after.scop 和可选 hint
-> PolCert 继续按现有方式完成 tiling validation
-> current_view_pprog
-> PolOpt 选 candidate dim
-> PolCert checked 地产生 parallel_cert
-> annotated codegen 输出 parallel-aware loop
-> 新 parallel theorem 证明其抽象并行语义 refine 到顺序语义
-> 再借现有 codegen correctness 回到 PolyLang semantics
```

## 12. 当前我的推荐实现顺序

最后把最实际的顺序写清楚。

### Step 1

只维护文档，固定：

- workflow
- theorem stack
- module ownership

### Step 2

先做 `ParallelValidator` 的设计和 soundness theorem 设计，不碰共享主代码。

### Step 3

确定 `ParallelLoop` 还是 `Loop+annotation`。  
proof churn 最小化的话，我更建议先 `ParallelLoop`。

### Step 4

等另一个 session 的 ISS pass 更稳定后，再进入真正的 codegen / semantics 改动。

这可以最大程度避免和当前正在进行的 sequential proof 线互相干扰。

## 13. 文件级落点建议

最后把未来最可能涉及到的文件落点写清楚。  
这一节不是要求现在去改这些文件，而是为了后续真正实现时避免设计继续发散。

### 13.1 前端 / orchestration 层

最可能要碰的文件是：

- `syntax/SLoopMain.ml`
  - 增加用户级 `--parallel` 开关
  - 把该开关传给优化 pipeline 配置
- `driver/Scheduler.ml`
  - 第二次 Pluto 调用根据配置选择 `--tile --parallel` 或 `--tile --noparallel`
  - 第一阶段 affine-only 调用建议保持不变
- `driver/PolOpt.v`
  - 在 `current_view_pprog` 后接 `checked_parallelize_current`
  - 把 `parallel_cert` 交给新的 annotated codegen wrapper

### 13.2 checked core 层

最自然的新文件是：

- `src/ParallelValidator.v`
  - `parallel_plan`
  - `parallel_cert`
  - `check_pprog_parallel_currentb`
  - soundness theorem
- `src/ParallelValidator.ml` 或对应 extraction bridge
  - 如果布尔 checker 的执行层需要 OCaml 包装

若要保持 `Validator.v` 风格统一，还可以加：

- `src/Validator.v`
  - 只做 re-export alias

### 13.3 语义 / loop 层

如果采用 wrapper 方案，最自然的新文件是：

- `polygen/ParallelLoop.v`
  - parallel-aware AST
  - `erase_parallel`
  - abstract parallel semantics
- `polygen/ParallelLoopPretty.ml` 或在现有 printer 中增加 parallel-aware 分支

如果采用直接扩 `Loop` 的方案，则会波及：

- `polygen/Loop.v`
- `polygen/LoopCleanup.v`
- `polygen/LoopSingletonCleanup.v`
- `syntax/SLoopPretty.ml`

proof churn 会明显更大。

### 13.4 codegen bridge 层

无论 wrapper 还是 direct annotation，都大概率需要一个新 bridge：

- `src/ParallelCodegen.v`
  - `annotated_codegen`
  - `annotated_codegen_erase_eq`
  - final parallel correctness theorem

这样可以避免直接把 parallel 逻辑硬塞进：

- `src/PrepareCodegen.v`

从而尽量保住现有的 sequential theorem stack。

### 13.5 hint / importer 层

这部分应当晚一点再做。

最可能涉及：

- `lib/OpenScopParser.mly`
- `src/OpenScop.v`
- `src/PolyLang.v`

但第一版完全可以继续忽略 `<loop>` extension。  
因此这部分不应成为 blocker。

## 14. 与当前并行开发的冲突最小化建议

考虑到另一个 session 正在推进 ISS pass，parallel 这条线最好按“最少共享文件”的顺序展开。

### 14.1 文档阶段

现在这轮最安全：

- 只维护 `doc/pluto-comprehensive/parallel-*.md`

### 14.2 checker 设计阶段

优先新增文件，不优先改老文件：

- 新增 `src/ParallelValidator.v`
- 新增 `polygen/ParallelLoop.v`
- 新增 `src/ParallelCodegen.v`

### 14.3 真正接 pipeline 阶段

最后再碰共享主文件：

- `driver/PolOpt.v`
- `driver/Scheduler.ml`
- `syntax/SLoopMain.ml`

这样能把和 ISS session 的潜在冲突推到最晚。
