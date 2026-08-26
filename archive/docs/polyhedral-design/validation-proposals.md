# Validation Proposals

本文件讨论：如果目标是不再把 Pluto 限制在“只做 affine scheduling”的那一小部分，接下来应该怎么扩 `polcert` 的验证边界。

## 1. 先把问题分层，而不是一口吃掉“完整 Pluto”

最容易失败的做法，是把“支持完整 Pluto”理解成“把所有 CLI 选项一次性吞进当前 validator”。

更合理的方式是把 Pluto 的能力按语义负担分层：

1. affine reordering
2. richer schedule construction
3. domain augmentation
4. domain/statement splitting
5. codegen-only annotation

它们的验证义务不一样，不应该用同一种证据格式硬压。

## 2. 当前 validator 的真实边界

当前 `polcert` 路线最适合处理的是：

- 原 statements 不变
- 原 iteration domains 不变
- 只换了一套合法 affine scattering

这基本对应：

- classic Pluto scheduler
- `nofuse/maxfuse/smartfuse`
- 关闭 tiling/parallel/diamond/prevector/unroll/ISS

因此现在的成功，并不意味着 Pluto 其余能力只是“还没导入”；更准确地说，是还没给这些能力设计合适的语义对象和证明义务。

## 3. 建议的 staged roadmap

## Stage 1: 支持 `parallel + notile`

### 为什么先做它

这是 Pluto 在 schedule-only 之外、但仍不明显改 domain 的第一层能力。

动态实验表明：

- `--parallel --notile` 会调用 `pluto_create_tile_schedule()`
- 它会生成 wavefront/pipelined schedule
- 但不像 tiling 那样一定增添新的 domain iterators

### 需要新增的能力

1. validator 不再假定 source 和 target 的 schedule arity 接近。
2. validator 能表达“新 schedule 维只是更细的执行次序编码”，而不是新的语义 instance。
3. importer/exporter 要保留由 Pluto 插入的 schedule rows，而不是试图把它们强行 canonicalize 掉。

### 建议的实现路径

- 在现有 schedule validator 上先放宽 schedule row 数量限制。
- 明确区分：
  - instance identity
  - execution order encoding
- 证明目标仍然是：
  - 所有真实 dependences 保持正序
  - 新 schedule 只是对同一 instance 集的合法线性扩展

### 这是低风险扩展

这一层不需要先发明“tile iterator 语义”，也不需要处理 statement splitting。

### 示例程序

- 程序：`/pluto/test/jacobi-1d-imper.c`
- 命令：

```sh
pluto --debug --silent --notile --parallel --nounrolljam --noprevector \
  --nodiamond-tile --smartfuse test/jacobi-1d-imper.c
```

- Pluto 实际做的变换：
  - 先在 `band level 0` 找到 2 个 hyperplanes
  - 因为不开 `tile`，后面额外进入 `pluto_create_tile_schedule()`
  - 输出 warning：`pipelined parallelism exists and --tile is not used`
  - 最终 schedule 变成：

```text
T(S1): (3t+i, 2t+i, 0)
T(S2): (3t+i+1, 2t+i+1, 1)
```

- 这个例子为什么适合 Stage 1：
  - statement/domain 结构没被拆开
  - 但 schedule 已经明显 richer，出现了 wavefront/pipeline 含义
  - 它正好检验 validator 是否能处理“同一 instance 集上的新 schedule 维”

## Stage 2: 支持常规 tiling

### 核心难点

一旦 `pluto_tile()` 发生，`after.scop` 里的 statement domain 会被重写：

- 新 iterator 被加入 domain
- 原 point iterator 与新 tile iterator 之间出现 linking constraints
- access relation 输入维也会被同步扩张

所以此时要验证的不再是：

- `same domain + new schedule`

而是：

- `old point-space`
- `new tile-space x point-space`
- 两者之间的 covering / exactness / uniqueness 关系

### 最小验证义务

对每个 statement，至少要证明：

1. Projection
   - 把新 domain 投影回原 point iterators，得到的点集等于旧 domain。
2. Coverage
   - 每个旧 point instance 都能在新 domain 中找到至少一个表示。
3. Uniqueness / non-duplication
   - 每个旧 point instance 不会被多个新 instances 重复执行。
4. Access consistency
   - 去掉新增 tile iterators 后，access 语义与原 statement 一致。
5. Schedule legality
   - 在新表示上，所有 dependences 仍被保持。

### 一个非常重要的源码线索

`libpluto` 里的：

- `/pluto/lib/plutolib.c:223-257`

提供了 `normalize_domain_schedule()`。

它会把 tiling 导致的 domain 约束搬回 schedule relation，并删除新增 statement dimensions，以适配 Polly 对“domain 维度不变”的期待。

### 直接 proposal

与其一开始就在 OpenScop 的“增维 domain”上做证明，不如并行推进两条路线：

1. OpenScop 原样验证路线
   - 直接验证 Pluto CLI 输出的 mutated domain
2. Normalized schedule 路线
   - 借鉴 `normalize_domain_schedule()`，把 tiling 结果重新表示成
     - 原始 point-domain
     - richer schedule relation / schedule constraints

第二条路线的优点是：

- 可以把很多 tiling case 降回“同一个 instance space 上的次序变化”
- 更贴近现有 schedule validator 的能力

### 推荐先做的具体子任务

1. 在 `polcert` 中引入“额外 existential/tile iterators”表示。
2. 给每个 statement 增加“new-domain to old-point-domain”投影证明。
3. 做一个独立的 `tile_validator`，不要和现有 schedule validator 混在一起。

### 示例程序

- 程序：`/pluto/test/matmul.c`
- 命令：

```sh
pluto --smartfuse --tile --parallel --nointratileopt --nounrolljam \
  --noprevector test/matmul.c
```

- Pluto 实际做的变换：
  - 原始 affine schedule：

```text
T(S1): (i, j, k)
```

  - 经过常规 tiling 后：

```text
T(S1): (i/32, j/32, k/32, i, j, k)
```

- 这个例子为什么适合 Stage 2：
  - 只有一个 statement，语义简单
  - 但 tile space 已经被显式插入 schedule/domain
  - 可以专注验证“新增 tile iterators 是否只是在重编码原 point-space”

## Stage 3: 支持 diamond tiling

这部分更系统的 pipeline-facing 设计，见：

- [second-level-and-diamond-design.md](./second-level-and-diamond-design.md)

### 为什么它比普通 tiling 更难

diamond tiling 不只是：

- 先 schedule
- 再机械地加 tile iterators

它还会在 scheduler 的首个 band 中改 hyperplane，本质上涉及：

- concurrent-start face 选择
- hyperplane eviction / replacement
- skew
- 再进入 tiling / reschedule

更准确地说，这里至少有四个容易混在一起、但验证时必须分开的层面：

1. `diamond` 不是单纯“tile 形状变成菱形”。
   它的关键在于：先挑一组能保住 concurrent-start face 的 hyperplanes，再围绕这些 hyperplanes 做 tiling。
   这也是为什么“默认 affine + 普通 tiling”通常不够；真正需要的是
   `diamond-aware affine midpoint + ordinary tiling`。
2. `diamond` 不等于“tile 内执行顺序也必须是 diamond”。
   论文里明确区分了：
   - 负责 tile shape 的 diamond hyperplanes
   - 负责 tile 内 point order 的普通 Pluto hyperplanes
3. `--diamond-tile` 和 `--full-diamond-tile` 不是同一个目标强度。
   - 前者更接近 partial / lower-dimensional diamond tiling，只保住部分 concurrent-start 维度
   - 后者对应 full-dimensional diamond tiling，试图保住整个 concurrent-start face
4. “支持 diamond” 也有两个不同的验证目标：
   - 只把 diamond 作为一种已检查的 schedule+tiling 变换纳入 PolCert
   - 进一步证明论文意义上的 concurrent start / maximal tile-level parallelism / load balance

### 建议先区分两类验证目标

#### 目标 A：与当前 PolCert 形式化保持一致

如果这一步的目标只是把 diamond 纳入当前 checked tiling 管线，而不去证明 parallel / load-balance 之类更强性质，那么最自然的建模是：

- `before -> mid`
  - 继续看成 affine scheduling phase
  - diamond 特有的 concurrent-start face 选择、hyperplane replacement、skew 都落在这里
- `mid -> after`
  - 继续看成普通 tiling phase
  - 仍然用 affine floor-link witness 表达新增 tile iterators

按这个边界看，diamond 和普通 tiling 的差别主要不是“需要一套新的 tiling 语义”，而是：

- `mid` 里的 affine hyperplanes 已经不是普通 Pluto 默认那组 hyperplanes
- `mid -> after` 所 tile 的对象变成了这些 diamond-friendly hyperplanes

所以这里更准确的名字应该是：

- 不是 “ordinary affine + ordinary tiling”
- 而是 “diamond-aware affine midpoint + ordinary tiling”

这也是为什么 partial/full diamond 的区别，首先应被理解成：

- 选择多少个 hyperplanes 去满足 concurrent-start cone condition
- 而不是引入了几种完全不同的 tile witness datatype

#### 目标 B：证明论文意义上的 diamond 性质

如果目标是更强的论文语义，那么不要把 diamond tiling 当作单个“黑箱 pass”验证；应当把它拆成三段：

1. concurrent-start/skew correctness
2. tiled space correctness
3. tile schedule correctness

### 需要的 witness

这部分也要区分两种需求。

- 若只做目标 A：
  - 现有 `before/mid/after` 边界原则上就够了
  - 重点是把 diamond-specific affine 变化干净地吸收到 `before -> mid`
  - `mid -> after` 仍然走当前 witness-centered tiling 路线
- 若做目标 B：
  - 当前 `--dumpscop` 只有 before/after 两个快照，证据太粗
  - 需要更多 phase snapshot 才能单独审计 concurrent-start/skew 是否正确

对于目标 B，建议给 Pluto fork 增加可选 dump：

- `after-auto-transform.scop`
- `after-diamond-skew.scop`
- `after-tiling.scop`
- `after-tile-schedule.scop`

如果没有这些 phase snapshot，diamond tiling 的验证很难定位失败点。

### partial diamond 与 full diamond 的区别

这里建议在 TODO 中明确写出来，否则后续容易把 `--diamond-tile` 和
`--full-diamond-tile` 混成一个功能点。

- partial / lower-dimensional diamond tiling
  - 只要求前几维满足 concurrent-start cone condition
  - 通常已经能给 shared-memory stencil 足够的 tile-level parallelism
  - 但仍给剩余维度更多自由度，用来照顾 tile 内宽度、vectorization、prefetch 等目标
- full-dimensional diamond tiling
  - 要求整个 concurrent-start face 都被保住
  - 更接近论文里的 maximal tile-level parallelism
  - 但 tile geometry 更复杂，tile 内循环宽度更不规则

因此，若按工程优先级排序：

1. 先把 partial diamond 纳入现有 `before -> mid -> after` checked 管线
2. 再评估 full diamond 是否只需要更复杂的 affine band，还是还要补更强的 witness

### tile shape 与 tile 内顺序要分开

diamond 相关讨论里，另一个常见混淆是把：

- “tile 是沿哪些 hyperplanes 切出来的”
- “tile 内点按什么顺序执行”

混成一件事。

在当前 PolCert 语境下，前者更接近 tiling witness 的职责；后者如果只是 tile
内 point-loop reorder，则更接近 Stage 4 的 intra-tile optimization。

这两个义务若不拆开，后面会很难判断：

- 当前失败到底是 diamond hyperplane 选得不对
- 还是 tile 内部重排破坏了原本已经正确的 diamond decomposition

### tile size 也不是完全无关

如果目标只是“已检查地接受一种 diamond 风格 schedule+tiling 结果”，tile
size 可以继续留在普通 tiling 参数层。

但如果目标接近论文中的 concurrent-start / load-balance 语义，就还需要额外注意：

- concurrent-start cone condition 不自动保证任意 tile-size ratio 都好
- partial/full diamond 的效果也会受 tile-size ratio 影响

因此 TODO 里最好显式保留一句：

- 先验证 hyperplane-level correctness
- 更强的 tile-size / tile-size-ratio 语义另列为后续扩展，不与第一阶段混做

### 示例程序

- 程序：`/pluto/test/jacobi-1d-imper.c`
- 命令：

```sh
pluto --debug --silent --tile --parallel --smartfuse test/jacobi-1d-imper.c
```

- Pluto 实际做的变换：
  - debug 输出先进入 `pluto_diamond_tile`
  - 在 diamond 相关 skew 之前，核心 schedule 形态是：

```text
T(S1): (t, 2t+i)
T(S2): (t, 2t+i+1)
```

  - 进入 concurrent-start / diamond skew 之后，变成：

```text
T(S1): (2t-i, 2t+i)
T(S2): (2t-i+1, 2t+i+1)
```

- 这个例子为什么适合 Stage 3：
  - 同时包含多 statement stencil 和典型 wavefront/diamond 结构
  - 能直接看到 diamond pass 不是“普通 tiling 后的小修小补”，而是先改了 hyperplane，再进入后续 tiling/reschedule

## Stage 4: 支持 intra-tile optimization

### 语义上它其实没前面那么难

`pluto_intra_tile_optimize_band()` 主要做的是：

- 在 tile 内部调整 point loops 的 innermost order
- 追求 locality 和 vectorization

它不以 statement splitting 为目标，也不自己创造新的 instance 集。

### 推荐处理方式

把它建模成：

- 在固定 tile decomposition 下，对 tile 内 point-schedule 做局部 permutation

验证义务可以复用：

- 同 tile 内 dependence legality
- 不跨 tile 破坏既有 outer schedule

### 工程建议

在验证管线中，不要单独为了 `prevector`/`unrolljam` 去处理 CLAST；只验证其前面的 polyhedral reordering 即可。

### 示例程序

- 程序：`/pluto/test/matmul.c`
- 命令：

```sh
pluto --smartfuse --tile --parallel --nounrolljam --noprevector test/matmul.c
```

- Pluto 实际做的变换：
  - 仅 tiling 后的 schedule：

```text
T(S1): (i/32, j/32, k/32, i, j, k)
```

  - 开启 intra-tile optimize 后：

```text
T(S1): (i/32, j/32, k/32, i, k, j)
```

- Pluto 实际优化点：
  - 没有引入新的 statement
  - 只是把 tile 内 point-loop 顺序从 `i,j,k` 改成 `i,k,j`
  - 这是 locality/vector-friendly 的局部重排

- 这个例子为什么适合 Stage 4：
  - 变换前后差异非常干净
  - 非常适合把 “tile decomposition correctness” 和 “tile 内次序优化 correctness” 分开验证

## Stage 5: 支持 ISS

### 这是第一个真正的 statement/domain splitting 问题

ISS 的本质是把原 statement 的 domain 切开，再分别调度/生成代码。

此时验证目标不是“新 schedule 是否合法”，而是：

- 新 statements 的并集语义是否等于原 statement

### 最小验证义务

对每个被 split 的 statement：

1. Split soundness
   - 新 domain 的并集等于旧 domain
2. Split disjointness
   - 各个 split domain 互不重叠，避免重复执行
3. Body/access preservation
   - 新 statements 的 body/access 与旧 statement 对应
4. Inter-split scheduling correctness
   - split 后新增的 statement 间顺序不引入非法行为

### 推荐的语义对象

当前 validator 若还是基于“同一组 statement id 前后对应”，会很快卡死。

ISS 更适合改成：

- program equivalence over statement families

也就是允许：

- one-to-many statement mapping

### 示例程序

- 程序：`/pluto/test/reverse-iss.c`
- 命令：

```sh
pluto --debug --silent --iss --notile --noparallel --nounrolljam \
  --noprevector --nodiamond-tile test/reverse-iss.c
```

- Pluto 实际做的变换：
  - debug 输出中先打印 `After ISS`
  - 原本同一条语句体被拆成 `S1` 与 `S2`
  - 两个 split 后的 statements 都仍然对应同一条源语句：

```text
S1 "a[i] = 2 * a[N - 1 - i];"
S2 "a[i] = 2 * a[N - 1 - i];"
```

  - 在 ISS 切分后，两者再交给 scheduler；初始 schedule 仍显示为：

```text
T(S1): (0, i, 0)
T(S2): (0, i, 0)
```

- 这个例子为什么适合 Stage 5：
  - 它把“split 之后仍然是同一条源语句语义”这件事暴露得很明显
  - validator 需要证明的重点不再是 schedule，而是 split 前后 program family 的并集语义等价

## Stage 6: 覆盖 DFP / typed / hybrid fusion

### 为什么放最后

它的语义难度反而没 tiling/ISS 高，但当前 artifact 不可运行，工程优先级低。

### 验证思路

DFP 仍然是在合成 affine hyperplanes。若不与 tiling/ISS 联动，它最终输出的语义对象仍可落回：

- same statements
- same domains
- different affine schedules

因此理论上它更接近“classic scheduler 的另一种实现”，而不是一类新的 program rewrite。

### 真正新增的是什么

- 需要理解 FCG colouring witness
- 需要为“为什么选了这组颜色/维度”提供更细粒度调试和可解释性

这更像可审计性问题，而不是最核心的 correctness 问题。

### 示例程序

- 程序：`/pluto/test/multi-stmt-stencil-seq.c`
- 先看当前 artifact 上的 baseline：

```sh
pluto --notile --noparallel test/multi-stmt-stencil-seq.c
```

输出是：

```text
T(S1): (i, 0)
T(S2): (i+1, 1)
T(S3): (i+2, 2)
T(S4): (i+3, 3)
T(S5): (i+4, 4)
```

- 这说明默认 heuristic 会把五个 stencil-like statements 串成一条 shift-fused 顺序链。
- 这个程序之所以适合 Stage 6，是因为源码注释已经直接指出：默认 heuristic 会为了 locality 牺牲并行性；而 typed fusion 的目标，恰恰是“只在不损失并行性的情况下 fuse SCCs”。

当前 container build 上如果直接跑：

```sh
pluto --typedfuse --silent test/multi-stmt-stencil-seq.c
```

会立刻报错：

```text
[pluto] ERROR: Typed or hybrid fusion is available with dfp framework only
which requires an LP solver.
```

因此这个 stage 的样例目前是：

- 可以在当前 artifact 上看到 baseline
- 但 typed/hybrid/DFP 的真正对比实验，需要先重建一个带 GLPK 或 Gurobi 的 Pluto

## 4. 建议给 Pluto fork 增加的 witness / dump

如果想让验证扩展真正落地，单靠 `before.scop` / `after.scop` 太粗。建议在 fork 中补一组结构化 witness。

### 4.1 phase snapshot

建议按 pass 输出：

- after extraction
- after ISS
- after auto transform
- after diamond skew
- after tiling
- after intra-tile optimize
- after tile schedule

### 4.2 per-statement remapping metadata

建议显式输出：

- 哪些 iterators 是新增的
- 新 iterator 与旧 point iterator 的 linking constraints
- 若 statement 被 split，新旧 statement 的映射关系

### 4.3 hyperplane provenance

建议给每一行 schedule/hyperplane 打标签：

- 来自 auto-transform
- 来自 SCC cut
- 来自 diamond skew
- 来自 tile schedule
- 来自 intra-tile reorder

这会极大降低验证和 debug 成本。

## 5. 对 `polcert` 内部 IR 的建议

若继续沿 OpenScop 路线推进，`polcert` 的内部对象至少要支持下面几件事：

1. statement arity 可以变化
2. schedule arity 可以明显增加
3. domain 可以带新增 iterators
4. access relation 的输入维度可以跟着变
5. statement 映射不再要求一一对应

如果内部 IR 继续假定：

- 同一个 statement family
- 同一个 iterator 维度
- 只比 schedule

那么 tiling/ISS 基本没有进入点。

## 6. 建议的工程里程碑

下面是我认为现实可行的次序。

### Milestone A

支持 `parallel + notile`。

成功标准：

- 能验证 wavefront schedule case
- 不需要修改 domain 语义

### Milestone B

支持单层普通 tiling。

成功标准：

- 能处理新增 tile iterator
- 能证明 projection / coverage / uniqueness

### Milestone C

支持 second-level tiling 与 intra-tile optimization。

成功标准：

- 多层 tile space 仍可投影回原 point space
- raw `after.scop` 顺序与 witness dependency order 可以分开处理
- schedule-only import 能对齐 raw added-dim order 与 canonical witness order
- point-loop reorder 不破坏 tile correctness

### Milestone D

支持 diamond tiling。

成功标准：

- 明确区分 partial diamond 与 full diamond
- 外部 pipeline 能给出 pre-tiling diamond midpoint，而不是只在 tile-only 阶段开 flag
- 当前 checked 管线能把 diamond-specific affine 变化和后续 tiling 变化分开定位
- 若走更强语义路线，concurrent-start/skew 阶段可单独审计
- 失败时能定位是 affine hyperplane 问题、tiling 问题，还是 tile-schedule 问题

### Milestone E

支持 ISS。

成功标准：

- statement splitting 有正式语义
- one-to-many mapping 可验证

### Milestone F

视需要覆盖 DFP。

成功标准：

- 更换 Pluto build 后，typed/hybrid cases 可导出并被 validator 接受

## 7. 最后一个策略建议

不要把“验证 Pluto 完整功能”理解成“验证 Pluto 内部求解器一定找到了最优解”。

更现实、更有价值的目标是：

- Pluto 继续作为 optimization oracle
- validator 负责证明它给出的 program rewrite 语义保持

对 affine scheduling 这是现在已经在做的事。

对 tiling / ISS / diamond / wavefront，也建议延续同一哲学：

- 不证明 Pluto 的 heuristic 最优
- 只证明 Pluto 给出的 rewrite 是合法且语义等价的
