# Pluto Parallel Support Notes

本笔记整理两部分内容：

1. Pluto 在 `parallel` 相关选项下到底做了什么，哪些结果只是 codegen annotation，哪些结果其实已经是 schedule 变换。
2. 在当前 PolCert / PolOpt verified pipeline 上，如果要加入 parallel loop 支持，应该把它放在哪一层、依赖什么证据、如何 checked，以及证明边界应该如何组织。

本文不主张“一次性证明完整 Pluto”。目标是给出一条可以逐步落地、并且不会破坏现有 affine + tiling verified 主线的 parallel 扩展路线。

如果只想看当前已经冻结下来的第一版决策，请优先看：

- `parallel-rfc.md`

关于“parallel 本身到底如何证明，而不是只把 loop 标成并行”的专门整理，见：

- `parallel-proof-strategy.md`

关于“用户 flag、Pluto 调用、PolOpt/PolCert 分工、以及最终 workflow 如何落地”的专门整理，见：

- `parallel-workflow-design.md`

关于“`par for` 的抽象并行语义应该怎样定义”的 mini-spec，见：

- `parallel-semantics-minispec.md`

关于“`checked_parallelize_current` 应该检查什么”的 mini-spec，见：

- `parallel-validator-minispec.md`

关于“`ParallelLoop` wrapper 与 `Loop + annotation` 应如何取舍”的专门比较，见：

- `parallel-ir-choice.md`

关于“如果真正落成 Coq 文件，模块/定义/定理骨架应如何组织”的专门整理，见：

- `parallel-coq-skeleton.md`

关于“parallel 这条线到底有哪些新增证明义务、顺序如何安排、风险点在哪里”的 checklist，见：

- `parallel-proof-obligation-checklist.md`

关于“未来真正实现时应按什么阶段落地、先动哪些模块、以及如何避免和共享主 pipeline 冲突”的专门整理，见：

- `parallel-implementation-staging.md`

## 1. 当前结论摘要

当前最重要的结论有六条。

### 1.1 Pluto 的 `parallel` 不是“最后打一个 pragma”

在 Pluto 里，`parallel` 至少有两层含义：

1. transformation-time parallelization
   - 通过 skew / wavefront / tile schedule 去构造可并行的执行顺序
2. codegen-time annotation
   - 在最终 AST / OpenScop `<loop>` extension 上记录某一层 loop 可并行

对 `--parallel --notile` 来说，Pluto 可能会先改 schedule，再生成 OpenMP annotation。
对 `--tile --parallel` 来说，Pluto 可能会先 tile，再做 tile schedule / wavefront，再生成 annotation。

因此，“支持 parallel”不能被理解成“在现有 sequential codegen 上补一个 pretty-printer”。

### 1.2 当前 PolCert 的 verified 主线仍然是 sequential codegen

目前已闭合的主线是：

```text
Loop
-> extractor
-> strengthen
-> checked affine scheduling
-> checked tiling
-> current_view_pprog
-> verified sequential codegen
```

这条路线已经支持：

- sequential affine rescheduling
- checked tiling
- verified codegen after checked tiling

但还没有把 “parallel loop generation + correctness” 纳入同一个 proof story。

### 1.3 现有 validator 已经覆盖了 parallel correctness 的核心数学部分，但不是最终形态

现有 affine/general validator 的核心不是“比较两份 schedule 长得像不像”，而是：

- 找出所有可能被 target 顺序打乱的 source instance pairs
- 对这些 pairs 证明：
  - 要么不会冲突
  - 要么它们在指令语义上可交换

这和 parallel 正确性的核心非常接近。

parallel 比当前 validator 多出的关键点是：

- 现在需要验证的不是 “after schedule 把 before 中哪些 pairs 反转了”
- 而是 “某一层 loop 一旦被并行化，该层不同迭代之间哪些 pairs 可能被任意 interleave / reorder”

也就是说，parallel 需要把“可交换性”从 schedule-delta 证明提升成“某一维的 slice 内自由重排”证明。

### 1.4 并行信息当前会在 OpenScop importer 边界丢失

当前 Pluto 会在 `after.scop` 中写 `<loop>` global extension，里面包含：

- iterator 名
- statement ids
- private vars
- directive bits

其中 `directive = 1` 表示 parallel，`directive = 4` 表示 vector。

但当前 PolCert importer 的状态是：

- parser 可以跳过 `<loop> ... </loop>`
- importer 没有把它变成内部语义对象
- 最终只是把它降成 ignored comment-like extension

因此即使 Pluto 给出了 parallel loop metadata，PolCert 现在也不会把它传到 `PolyLang` 或 `Loop`。

### 1.5 如果要做 parallel，最佳策略不是“信任 Pluto 的 loop annotation”

推荐边界是：

- Pluto 负责找 candidate schedule / tiling / wavefront
- PolCert 负责 checked 地验证变换后的程序语义
- PolCert 自己负责重新计算“哪一层 loop 可以标 parallel”

也就是说：

- Pluto 的 `<loop>` extension` 可以作为 hint / regression oracle`
- 但不应该成为 trusted proof object

### 1.6 最稳的路线是把 parallel 看成一个新 checked phase，而不是塞进已有 tiling witness 里

parallel 不改变 instance space 本身。

这一点非常关键：

- tiling witness 解释的是 point-space 如何 lift 到 tile-space
- parallel annotation 解释的是某个 loop dimension 上允许更弱的执行顺序

所以 parallel 最好是一个单独的 witness / cert，不要混入 `pi_point_witness`。

## 2. Pluto 中 parallel 的真实机制

下面总结这轮直接在容器 `/pluto` 中查看源码和实验得到的事实。

### 2.1 关键源码位置

与 parallel 最相关的 Pluto 源码位置是：

- `/pluto/tool/main.cpp`
  - 顶层 pipeline
  - `if (parallel && !tile && !identity) { pluto_create_tile_schedule(...) }`
- `/pluto/lib/tile.c`
  - `pluto_tile`
  - `pluto_create_tile_schedule_band`
- `/pluto/lib/polyloop.c`
  - `pluto_loop_is_parallel`
  - `pluto_get_parallel_band`
  - `pluto_get_dom_parallel_loops`
- `/pluto/tool/ast_transform.c`
  - 在 CLAST 上真正标记 parallel loops
- `/pluto/tool/pluto_codegen_if.c`
  - 生成 OpenMP pragmas
  - 生成 OpenScop `<loop>` extension
- `/pluto/tool/osl_pluto.c`
  - `pluto_populate_scop`
  - 把 parallel/vector metadata 写回 OpenScop
- `/pluto/openscop/include/osl/extensions/loop.h`
  - `OSL_LOOP_DIRECTIVE_PARALLEL = 1`
  - `OSL_LOOP_DIRECTIVE_VECTOR = 4`

### 2.2 `parallel + notile` 的机制

当命令是：

```text
pluto ... --parallel --notile ...
```

Pluto 不只是“最后生成 `#pragma omp parallel for`”。

它的实际行为是：

1. 先完成 ordinary affine scheduling / auto-transform
2. 重新计算 dependence satisfaction
3. 对 outermost permutable bands 调用 `pluto_create_tile_schedule`
4. 如果存在 pipelined parallelism，则构造 wavefront-style schedule
5. 最后再从 resulting `PlutoProg` 里提取 dominating parallel loops
6. 用这些 loops 去标 OpenMP pragma 和 OpenScop `<loop>` extension

这意味着：

- `parallel + notile` 是一个真正的 schedule-construction pass
- 它不应被建模为纯 codegen annotation

### 2.3 `tile + parallel` 的机制

当命令是：

```text
pluto ... --tile --parallel ...
```

Pluto 的核心行为是：

1. 先 tiling，显式引入 tile iterators
2. 可选 diamond / intra-tile optimize
3. 然后对 tile bands 调用 `pluto_create_tile_schedule`
4. 最后在 tile-space 上选择并行 loop

这里的 parallel 经常不是原始 point-space 的 outer loop，而是：

- tile-space 中的 outer tile loop
- 或 wavefront 之后的某个 inner tile loop

因此：

- 对 tiled route 来说，parallel 不是 tiling 的附属注释
- 它仍然是实际 schedule 结果的一部分

### 2.4 `innerpar` / `multipar` / `forceparallel`

从源码和测试现状看：

- `innerpar`
  - 影响 Pluto 更偏向“纯 inner parallel”还是“pipelined/wavefront parallel”
  - 它不是纯 codegen flag
- `multipar`
  - 允许 Pluto 提取多个 parallel loops
  - codegen 端会开 nested OpenMP
- `forceparallel`
  - parser 中存在
  - 但当前测试覆盖很弱

对 PolCert 来说，正确的顺序应当是：

1. 先做单层 parallel
2. 再决定是否支持 Pluto 风格 `multipar`
3. 最后再看是否需要与 `innerpar` / `forceparallel` 对齐

### 2.5 `<loop>` extension 的语义地位

Pluto 写回 OpenScop 时，会生成 `<loop>` extension。

它包含的信息不是 schedule 本体，而是 codegen metadata：

- 哪个 loop iterator 被视为 parallel / vector
- 这层 loop 覆盖哪些 statements
- 还要声明哪些 private vars

这类信息对最终 C/OpenMP 输出很关键，但它不是 `domain/schedule/access` 那种核心 polyhedral carrier。

因此最自然的处理是：

- 不把 `<loop>` extension` 作为 primary proof object`
- 而把它作为：
  - hint
  - 比对对象
  - 调试信息

### 2.6 Pluto 当前测试里对 parallel 的覆盖情况

Pluto 自己是有 parallel 相关测试的，但覆盖重心要看清楚。

顶层 `test.sh` 中确实有：

- `--tile --parallel` 的回归
- PET 前端下的 `--tile --parallel` 回归
- `test_libpluto.c` 中开启 `options->parallel = 1`

但这些测试主要在检查：

- schedule / tiling / tile-schedule 的文本输出
- diamond / wavefront 结果

而不是专门检查：

- 生成的 `#pragma omp parallel for`
- OpenScop `<loop>` extension 是否正确
- `innerpar` / `multipar` / `forceparallel` 的细粒度行为

所以如果 PolCert 要接 parallel，不能假设 Pluto 已经有一套“loop annotation 级别的严格回归测试”可以直接继承。

## 3. 当前 PolCert / PolOpt pipeline 的理解

### 3.1 当前 verified 主线

当前 verified 主线可以概括成：

```text
Loop
-> Extractor.extractor
-> Strengthen.strengthen_pprog
-> checked_affine_schedule
-> try_verified_tiling_after_phase_mid
   -> export_for_pluto_phase_pipeline
   -> run_pluto_phase_pipeline
   -> checked_tiling_validate_poly
   -> current_view_pprog
-> PrepareCodegen.prepared_codegen
-> verified sequential Loop code
```

这里最关键的分层是：

1. extractor
   - 从 surface loop syntax 进入 `PolyLang`
2. checked affine schedule
   - 验证单纯 schedule 变化
3. checked tiling
   - 先 witness/structure check，再 generic validation
4. current-view normalization
   - 把 witness-centered tiled program 转成 current-space affine-style view
5. codegen
   - 复用已有 affine codegen theorem

### 3.2 当前哪些边界已经非常接近 parallel

现有系统里，已经有三块内容对 parallel 很有帮助。

#### A. `strengthen_pprog`

它把 prefix-only 的 domain facts显式化。

这对 parallel 很重要，因为 parallel checking 往往需要固定 outer prefix，再讨论 candidate loop 的不同迭代是否冲突。

#### B. `validate_general`

当前 generic validator 的结构是：

- 给定 before / after 两个 program
- 构造扩展 instruction points
- 枚举可能被 target 顺序反转的 pairs
- 对这些 pairs 验证 no-write-collision / permutability
- 用 stable permutation theorem 推回语义等价

这已经非常接近 “一层 loop 内任意 interleave 也不出错” 这种 parallel theorem。

#### C. `current_view_pprog`

对于 tiling 而言，parallel 最终应该落在 current-space loops 上，而不是 witness 内部的 source/base encoding 上。

`current_view_pprog` 正好把程序转成 codegen 也使用的 current-space affine view。

这说明：

- 并行 cert 最自然的工作对象不是 raw tiled witness program
- 而是 `current_view_pprog after`

### 3.3 当前哪些地方还不支持 parallel

主要有四个缺口。

#### A. scheduler flags

当前 driver 中实际使用的 scheduler flags 是：

- affine-only route: `--noparallel --notile`
- tiling route: `--identity --tile --noparallel`

也就是说 verified mainline 现在根本没有让 Pluto 跑 parallel mode。

#### B. OpenScop importer 丢掉 `<loop>`

parser 已经能 skip Pluto 的 loop extension，但不会把它导入语义对象。

#### C. `Loop` IR 没有 parallel 承载位

当前 `polygen/Loop.v` 只有顺序：

- `Loop lb ub body`

没有：

- parallel bit
- loop annotation
- fork-join semantics

#### D. codegen 链没有“parallel cert”接口

当前 codegen 只消费：

- domain
- schedule
- point witness
- accesses

还没有：

- 哪个 current-space dimension 被 checked 为 parallel

## 4. 如果要支持 parallel，Pluto 应该怎样使用

这一节回答两个问题：

1. Pluto 什么时候应该开 `parallel`
2. Pluto 的哪些输出应该被 trusted，哪些不应该

### 4.1 核心原则

最重要的原则是：

> Pluto 应该被用来“找变换后的程序”，而不是被用来“直接决定最终可信的 parallel annotation”。

换句话说：

- Pluto 的 schedule / tiling 结果可以导入，再 checked
- Pluto 的 `<loop>` extension 不应直接 trusted

### 4.2 何时使用 `--noparallel`

以下场景仍然应该保留 `--noparallel`：

1. 只想走当前稳定 verified affine route
2. 只想得到一个 legal mid affine schedule，给 tiling route 做 proof boundary
3. 在并行 checker 尚未接入前，需要 deterministic sequential fallback

这对应当前的：

- `checked_affine_schedule`
- affine fallback path

### 4.3 何时使用 `--parallel --notile`

当目标是让 Pluto 自己去寻找 wavefront / skewed schedule，从而创造 parallelism 时，必须真的开：

```text
--parallel --notile
```

这条路线的作用不是 annotation，而是 transformation search。

因此它适合成为一个新的 checked route：

```text
checked_parallel_schedule
```

语义上它仍然属于：

- same statements
- same domain
- richer schedule

但 proof obligation 比纯 affine reordering 更强，因为 target route 以后要允许 loop-iteration-level reordering。

### 4.4 何时在 tiled route 中开 `--parallel`

如果目标是得到 Pluto 真正的 tiled-parallel result，那么 tiled stage 必须允许 Pluto 在 tile-space 上做 schedule selection：

```text
mid
-> pluto --identity --tile --parallel ...
-> after
```

这里不建议采用“先 `--tile --noparallel`，最后内部再加 parallel pragma”作为唯一方案。

原因是：

- 对不少程序，parallel 不是已有 schedule 上的被动注释
- 而是 Pluto 在 tile-space 里重新组织 schedule 的结果

因此更合理的策略是：

1. Pluto 可以在 tiled stage 开 `parallel`
2. `checked_tiling_validate_poly` 仍然验证 `mid -> after`
3. PolCert 再内部重新导出 parallel cert

也就是说：

- trust the transformed program
- do not trust Pluto's loop annotation

### 4.5 推荐的 Pluto 使用策略

推荐分三层使用 Pluto。

#### Layer 0: 现有 sequential baseline

```text
--noparallel --notile
```

用途：

- affine-only checked baseline
- fallback

#### Layer 1: parallel schedule construction without tiling

```text
--parallel --notile
```

用途：

- wavefront / skew route
- richer schedule construction

#### Layer 2: tiled parallel route

```text
--tile --parallel
```

用途：

- tile-space schedule construction
- diamond / wavefront + tiling 的组合结果

### 4.6 对 `<loop>` extension 的推荐处理

有两种策略。

#### 策略 A：完全忽略它，只内部重算

优点：

- proof boundary 最干净
- 不依赖 importer 新增复杂度

缺点：

- 失去与 Pluto 精确 loop choice 的直接对齐

#### 策略 B：导入它，但只当 hint

优点：

- 便于调试和 regression compare
- 可以检查“PolCert internal cert 是否与 Pluto choice 一致”

缺点：

- importer 复杂度增加

推荐策略是 B：

- 保留 `<loop>` extension`
- 但只当 hint / oracle / debugging artifact`
- 最终 codegen 只吃 internal checked parallel cert

## 5. 语义层面应该如何强化

这一节回答“parallel 支持到底要改哪层语义”。

### 5.1 不要把 parallel 塞进 `pi_point_witness`

`pi_point_witness` 的职责是：

- 解释当前点如何映射回 base/source 点
- 说明 point-space 结构如何 lift / normalize

parallel annotation 不改变 point-space。

因此 parallel 不应被编码成：

- 另一种 point witness
- 或 tiled witness 的一个 flag

否则会把两种完全不同的概念混在一起：

- space transformation
- execution policy relaxation

### 5.2 推荐增加一个独立的 parallel cert

最合理的对象是一个独立的程序级证据，例如：

```text
parallel_witness
```

它至少要表达：

1. 哪些 current-space dimensions 被认为 parallel-safe
2. 这些 dimensions 采用什么 policy
   - outermost-only
   - multipar
   - inner-preferred

第一版其实可以很简单：

```text
list nat
```

含义是：

- 在 `current_view_pprog` 的 current-space dimensions 中
- 哪些维度允许在 codegen 时产生 `parallel for`

### 5.3 最小 IR 变化：给 `Loop` 增加 annotation，但先不改核心顺序语义

第一阶段最稳的做法不是立刻定义 fork-join operational semantics，而是：

1. 扩 `Loop` AST，让 loop 节点携带 annotation
2. 顺序语义先把 annotation 擦除

例如概念上：

```text
Loop kind lb ub body
```

其中：

- `kind = SeqLoop | ParLoop`

第一阶段语义：

- `SeqLoop` 和 `ParLoop` 在 `Loop.loop_semantics` 下解释相同

这样可以先完成：

- IR 贯通
- codegen / pretty-print / downstream C emission
- 与现有证明链兼容

### 5.4 第二阶段再补“parallel execution is semantics-preserving” theorem

最自然的强化不是替换原顺序语义，而是增加一个定理层：

> 如果某一维被 checked 为 parallel-safe，那么把这一层 loop 视为可任意 worksharing/interleave，其结果与顺序语义等价。

这样有三个好处：

1. 不破坏现有 sequential theorem stack
2. 可以复用现有 `StablePermut` / `Permutable_ext`
3. fork-join operational semantics 可以后补，不阻塞第一版

### 5.5 推荐的语义分阶段

#### Stage A: annotation-erasure semantics

目标：

- `ParLoop` 在顺序语义下与 `Loop` 相同

作用：

- 快速闭合 IR 与 codegen

#### Stage B: reorder-invariance theorem

目标：

- 对于 `ParLoop`，证明任意合法 parallel interleaving 都等价于顺序执行

作用：

- 真正解释 parallel annotation 的正确性

#### Stage C: explicit fork-join semantics

目标：

- 如果需要，可以再定义更 operational 的并行语义

作用：

- 面向 runtime model / OpenMP-style semantics

但这不应成为第一阶段 blocker。

## 6. validation 应该放在哪一层

parallel support 的关键设计问题不是“能不能验证”，而是“验证放在 pipeline 的哪一层”。

### 6.1 不推荐的位置

#### 不推荐放在 extractor

extractor 的职责是：

- surface syntax -> `PolyLang`

parallel 不是 source extraction 语义的一部分。

#### 不推荐放进 tiling witness checker

tiling witness checker 的职责是：

- 检查 point-space lift / tile link / access lifting / canonical import

parallel 与这些结构无关。

#### 不推荐只在 final pretty-printer 决定

那样 correctness 完全没被 checked。

### 6.2 推荐的位置：在“变换已 checked 完成之后，codegen 之前”

推荐把 parallel checking 放在：

```text
validated poly program
-> optional current_view_pprog
-> checked_parallelize
-> prepared_codegen
```

这对 affine-only 和 tiled routes 都成立。

### 6.3 affine-only / parallel-notile 路线

建议 route：

```text
Loop
-> extractor
-> strengthen
-> external Pluto with --parallel --notile
-> validate_general before -> after
-> checked_parallelize after
-> prepared_codegen
```

这里：

- `validate_general` 负责 schedule legality
- `checked_parallelize` 负责 loop-level parallel cert

### 6.4 tiled parallel 路线

建议 route：

```text
Loop
-> extractor
-> strengthen
-> affine mid
-> Pluto tiled parallel after
-> checked_tiling_validate_poly mid -> after
-> current_view_pprog after
-> checked_parallelize current_view(after)
-> prepared_codegen
```

为什么推荐在 `current_view_pprog after` 上做 parallel checking：

1. current-space 维度已经是 codegen 要看到的维度
2. 可以避免直接在 witness-centered internal shape 上定义并行 loop 语义
3. codegen 标注位和 cert 可以直接按 current-space dimension 对齐

### 6.5 与现有 `checked_tiling_validate_poly` 的关系

关系应该是：

- `checked_tiling_validate_poly`
  - 证明 transformed program 本身语义正确
- `checked_parallelize`
  - 证明在这个已验证程序上，某些 loops 可以安全失序执行

这两个 phase 是串联关系，不是替代关系。

## 7. parallel validation 的策略 / 算法

这一节给出推荐算法。

### 7.1 目标不是“验证 Pluto 说的某一层 parallel”

目标应该是：

> 给定一个已经 checked 的 `PolyLang` program，判断其中哪些 current-space dimensions 是 parallel-safe。

这样 algorithm 与 Pluto 解耦：

- Pluto 可以提供 hint
- 但 correctness 只依赖 internal program

### 7.2 candidate 的工作对象

建议 candidate 维度来自：

- `current_view_pprog` 之后的 current-space dimensions

而不是：

- raw OpenScop scattering rows
- raw `<loop>` extension iterator names

原因是 codegen 最终就是按 current-space 生成 loops。

### 7.3 candidate 判定的核心思路

对某个候选维度 `d`，parallel 的语义是：

- 固定所有 outer prefix dimensions `< d`
- 不同 `d` 迭代之间可以被任意重排 / interleave

因此 validator 需要证明：

> 对任何两个属于同一 outer-prefix slice、但 `d` 值不同的实例，它们不会形成破坏语义的 cross-iteration write/read conflict。

### 7.4 直接 polyhedral checker 的推荐形式

对任意一对 statement instructions `pi1`, `pi2`，以及它们的 access pairs，构造下面的约束：

1. 两个实例都在各自 domain 中
2. environment 相等
3. current-space prefix `< d` 相等
4. candidate dimension `d` 的值不同
5. 两个 access 指向同一 memory cell

如果上述 polyhedron 非空，则说明：

- 存在两个来自不同 `d` 迭代的实例访问同一 cell
- 如果其中涉及 WW / WR / RW，就不能把 `d` 标成 parallel

也就是说，parallel checker 可以直接复用当前 validator 的 collision-style polyhedral reasoning，但条件从：

- `old_sched_lt ∧ new_sched_ge`

换成：

- `same_prefix_before_d ∧ dim_d_neq`

### 7.5 为什么这个 checker 比当前 schedule validator 更强

当前 validator 的核心问题是：

- 某个 pair 是否被 after schedule 反转

parallel checker 的核心问题是：

- 某个 pair 是否可能在 parallel runtime 下失序

parallel 下允许的失序比“单一 after schedule 的反转”更大。

所以：

- 不能直接说 “validate_general 过了，所以 parallel 自动安全”
- 还需要一个更强的 loop-slice 级 checker

### 7.6 语义侧的目标应该是 permutability，而不是纯 dependence emptiness

在最保守的情形下，checker 可以要求：

- WW / WR / RW cross-iteration conflict polyhedron 全为空

更一般的形式则可以要求：

- 所有这类 pairs 都满足现有 `Permutable_ext`

推荐第一版先用保守版本：

- cross-iteration no-write-collision

原因：

1. 与 OpenMP `parallel for` 直觉更一致
2. 实现更直接
3. 更容易先闭合 theorem

以后再放宽到更一般的 instruction-level permutability。

### 7.7 candidate 选择策略与 Pluto heuristic 的关系

parallel correctness 和 parallel profitability 要分开。

#### Correctness side

只关心：

- 哪些维度是 safe

#### Heuristic side

决定：

- 是选 outermost safe dim
- 还是 inner safe dim
- 是否同时选多层

推荐第一版 heuristic：

1. 只选一个 outermost safe dimension
2. 暂不支持 nested `multipar`
3. 不试图精确复现 Pluto 的 band heuristic

之后再逐步接：

- `innerpar`
- `multipar`
- 与 Pluto choice 的一致性检查

## 8. validation 正确性如何证明

parallel support 的 proof story 应当尽量复用现有资产。

### 8.1 现有 affine/general validator 的证明模式

当前 affine/general validator 的证明大致是：

1. 布尔 checker 构造 polyhedral obligations
2. soundness lemma 把 `checker = true` 转成 no-write-collision / permutability facts
3. 用 `Permutable_ext` 推出 instruction-level 可交换
4. 用 `StablePermut` 与 instance-list equivalence 推出 whole-program semantics preservation

parallel checker 最好沿同一套路。

### 8.2 第一层证明：布尔 checker soundness

需要一个定理形状类似：

```text
check_pprog_parallel_currentb pp pw = true
-> parallel_rel_pprog_structure pp pw
-> parallel_safe_current_dims pp pw
```

其中 `parallel_safe_current_dims` 的含义是：

- `pw` 中列出的每个 current-space dimension
- 都满足该维的 cross-iteration no-write-collision condition

### 8.3 第二层证明：parallel-safe dim implies slice-level reorder invariance

需要把“某维 safe”转成：

- 固定 outer prefix 后
- 不同 `d` 迭代之间的任何交换
- 都不会改变 slice semantics

这一步可以直接复用项目里已经存在的：

- `StablePermut`
- `Permutable_ext`
- instance-list semantics equivalence tools

目标不是重新发明一个新的 permutation machinery，而是把现有 machinery 的“after schedule 反转 pair”推广成“parallel slice 内任意 pair”。

### 8.4 第三层证明：annotated loop code preserves sequential semantics

因为第一阶段 `ParLoop` 可以采用 erasure semantics，所以 codegen theorem 可以先保持如下形状：

```text
checked_parallelize pp = pp'
-> prepared_codegen pp' = loop
-> Loop.semantics loop st1 st2
-> PolyLang.semantics pp st1 st2
```

这里的关键点是：

- `pp'` 与 `pp` 只有 parallel annotation 差别
- 顺序语义下 annotation 不改变 meaning

### 8.5 第四层证明：parallel runtime theorem

如果以后要引入更真实的 parallel operational semantics，则还需要补：

```text
parallel_safe_current_dims pp pw
-> parallel_loop_semantics (annotated_codegen pp pw) st1 st2
-> sequential_loop_semantics (erase_parallel ...) st1 st2'
-> State.eq st2 st2'
```

但这一步不应阻塞第一版。

### 8.6 为什么这种 proof boundary 比“直接信 Pluto 的 `<loop>`”更好

如果直接信 Pluto 的 `<loop>` extension，需要证明：

- Pluto 为什么选这层
- private vars 为什么对
- AST 上找到的 loop 与 polyhedral loop 为什么对应

这会把 proof boundary 直接推到 Pluto codegen 细节里。

如果 internal re-check，则只需要证明：

- 对当前 internal `PolyLang` program
- 这个 current-space dimension safe

证明对象更稳定，也更接近现有 validator style。

## 9. 一个推荐的分阶段落地路线

### Stage 0: 只写设计，不改主线

完成内容：

- 明确 parallel cert 的数据结构
- 明确 pipeline insertion point
- 明确 proof obligations

### Stage 1: annotation-only parallel support

完成内容：

1. `Loop` IR 增加 `Seq` / `Par` annotation
2. codegen 能根据 internal cert 生成 `parallel for`
3. 顺序语义先把 annotation 擦除
4. 不信任 Pluto `<loop>`，内部只做 heuristic choice

目标：

- 先打通 end-to-end representation

### Stage 2: checked single-dimension parallel on affine / current-view programs

完成内容：

1. 定义 `parallel_witness`
2. 实现 `check_pprog_parallel_currentb`
3. 证明 soundness
4. 在 `current_view_pprog` 之后接 `checked_parallelize`

目标：

- 对 affine route 和 tiled route 都能 checked 地生成单层 parallel loop

### Stage 3: parallel-enabled Pluto route

完成内容：

1. 新增 `parallel + notile` route
2. tiled route 允许 Pluto `--parallel`
3. 变换结果仍先走 existing checked validators
4. parallel cert 仍然 internal re-check

目标：

- 让 Pluto 真正参与 parallelizing schedule search

### Stage 4: multipar / innerpar / vector

完成内容：

1. 多层 parallel cert
2. nested parallel policy
3. vector annotation support
4. 与 Pluto `<loop>` / vector directive 做一致性 compare

目标：

- 靠近 Pluto 的完整 loop metadata

## 10. 推荐的 public naming

为避免把 parallel 和 tiling 混在一起，建议使用独立 naming。

### 10.1 checker / validator side

建议名字：

- `check_pprog_parallel_currentb`
- `checked_parallelize_current`
- `checked_parallelize_poly`
- `checked_parallelize_implies_wf_after`
- `checked_parallelize_correct`

### 10.2 scheduler side

如果要引入 Pluto parallel-notile route，建议名字：

- `parallel_schedule_scop_scheduler`
- `checked_parallel_schedule`

它应当与：

- `checked_affine_schedule`
- `checked_tiling_validate_poly`

并列，而不是覆盖它们。

### 10.3 codegen bridge

建议名字：

- `checked_parallel_prepared_codegen`
- `checked_parallel_prepared_codegen_correct`

## 11. 对当前项目最重要的设计判断

最后把最关键的判断收束成几句。

### 11.1 parallel 不应作为 tiling checker 的一个小补丁

因为：

- tiling 处理的是 point-space 结构变化
- parallel 处理的是执行顺序放松

这是不同种类的义务。

### 11.2 最自然的验证位置是“validated program -> codegen”之间

因为：

- 那时程序已经 semantic-checked
- current-space 与 codegen shape 已经稳定
- parallel cert 可以直接按 current dimensions 绑定

### 11.3 Pluto 的 parallel mode 仍然值得使用

因为：

- `parallel + notile` 能真正构造 wavefront schedule
- `tile + parallel` 能真正影响 tile-space schedule

但：

- 不应直接信任它给出的 loop annotation

### 11.4 第一版最值得追求的不是完整 OpenMP 语义，而是 checked annotation

最稳的第一版目标是：

1. PolCert checked 地判定某些 loops safe
2. codegen 输出 annotated loops
3. 顺序语义不变
4. parallel-safe theorem 作为额外 correctness layer 逐步补上

### 11.5 这条路线和当前 verified pipeline 是兼容的

因为它不会破坏当前主线：

- affine scheduling correctness
- checked tiling correctness
- current_view bridge
- verified sequential codegen

相反，它把 parallel 作为一个新的、边界清楚的 checked phase 接在已有主线之后。

## 12. 当前推荐的最终 pipeline 形态

如果把 parallel support 完整纳入 verified pipeline，我当前最推荐的目标形态是：

```text
Loop
-> extractor
-> strengthen
-> choose one checked transform route
   -> affine-only checked route
   -> parallel-notile checked route
   -> phase-aligned tiled-parallel checked route
-> if witness-centered tiled:
   -> current_view_pprog
-> checked_parallelize_current
-> prepared_codegen
-> Loop-with-parallel-annotations
```

其中 proof layering 是：

1. transformation correctness
   - affine / tiling / parallelizing schedule construction
2. parallel-safety correctness
   - which loops are safe to annotate
3. codegen correctness
   - annotated loop code still refines validated `PolyLang` semantics

这比把 parallel 直接混进任何一个已有 phase 都更清晰。
