# Options And Capabilities

本文件把 Pluto 的选项、源码模块、当前 artifact 的可用性，以及它们对 validation 的影响放到一起。

## 1. 先定义五类 validation 影响

为了后面矩阵可读，先定义五个 effect class。

| 类别 | 含义 |
| --- | --- |
| `S0` | 只改 affine schedule/scattering，domain/statement 结构基本不变 |
| `S1` | 主要改 schedule，但会引入新的 schedule 维或 wavefront 含义 |
| `D1` | 会改 domain、增加 iterator、改 access 维度 |
| `P1` | 会 split statement 或 split domain；不再是“原 statement 上的 schedule” |
| `C1` | 主要是 codegen/AST annotation，对 polyhedral model 语义不直接增维 |

## 2. 重要提醒：`--help` 不是完整规范

当前 artifact 中，至少有下面几种偏差：

- 帮助文本中的默认值和真实默认值不一致
- parser 支持的一些选项没有完整出现在 help 中
- 有的选项能 parse，但实现上未真正使用

权威来源应当是：

- `/pluto/tool/main.cpp:198-277`
- `/pluto/lib/program.cpp:833-939`
- `/pluto/tool/main.cpp:386-543`

## 3. 前端与输入相关

| 选项 | 模块 | 当前 artifact | 效果类别 | 说明 |
| --- | --- | --- | --- | --- |
| `--pet` | `tool/main.cpp`, `tool/pet_to_pluto.cpp` | 可用 | `S0/S1/D1/P1` 取决于后续 pass | 只改变前端来源，不限定后续优化范围 |
| `--readscop` | `tool/main.cpp`, `tool/osl_pluto.c` | 可用 | 无直接变换 | 直接读取 OpenScop |
| `--dumpscop` | `tool/main.cpp`, `tool/osl_pluto.c` | 非 PET 可用 | 无直接变换 | dump before/after scheduling OpenScop；PET 路径不支持 |

### 观察

- `--readscop` 走的不是“简化模式”，而是同一条 OSL -> `PlutoProg` -> optimization -> OpenScop 回写路径。
- `--dumpscop` 是这个 fork 相对原 Pluto 的关键 artifact 能力。

## 4. 依赖分析相关

| 选项 | 模块 | 当前 artifact | 效果类别 | 说明 |
| --- | --- | --- | --- | --- |
| `--isldep` | `tool/osl_pluto.c`, `lib/program.cpp` | 可用，且归一化后默认开启 | 无直接变换 | 用 ISL 计算 flow dependences |
| `--candldep` | `tool/osl_pluto.c` | 可用 | 无直接变换 | 用 Candl 计算 dependences |
| `--lastwriter` | `lib/program.cpp:622-695` | 可用，仅 ISL | 无直接变换 | 切换 dependency representation；不是单纯的“减少边数”按钮 |
| `--rar` | `tool/osl_pluto.c`, `lib/program.cpp` | 可用 | 无直接变换 | 把 RAR 也纳入 dep 集 |
| `--isldepaccesswise` | `tool/osl_pluto.c` | 可用，默认 | 无直接变换 | 每个 dependence 尽量保留唯一 source/target access |
| `--isldepstmtwise` | `tool/osl_pluto.c` | 可用 | 无直接变换 | 对同一 statement 的 accesses 做 union，依赖可能更粗 |
| `--isldepcoalesce` | `lib/program.cpp` | 可用但默认关 | 无直接变换 | 有注释明确写了潜在 bug，默认不建议开启 |

### 对 validation 的含义

依赖选项本身不改变 schedule/domain，但它们改变了 Pluto 允许的变换空间。若以后要对“Pluto 决策过程”做更细粒度验证或重放，这些选项必须纳入 witness。

## 5. 经典 affine scheduling 与 fusion

| 选项 | 模块 | 当前 artifact | 效果类别 | 说明 |
| --- | --- | --- | --- | --- |
| `--identity` | `tool/main.cpp`, `lib/pluto.c` | 可用 | 无优化 | 跳过 auto-transform |
| `--nofuse` | `lib/pluto.c` | 可用 | `S0` | 更激进地 cut SCC，弱化 fusion |
| `--smartfuse` | `lib/pluto.c` | 可用，默认 | `S0` | 默认 heuristic，在 nofuse 与 maxfuse 之间 |
| `--maxfuse` | `lib/pluto.c` | 可用 | `S0` | 更倾向 maximal fusion |
| `.fst` / `.precut` 文件 | `lib/pluto.c` | 可用 | `S0` | 从工作目录读入用户强制 fusion/distribution 结构 |
| `--per-cc-obj` | `lib/framework.cpp` | 可用 | `S0` | 为每个 connected component 使用独立 objective |
| `--coeff-bound` | `lib/pluto.c`, `lib/program.cpp` | 可用 | `S0` | 限制 transformation coefficient 上界 |
| `--flic` / `--fast-lin-ind-check` | parser 中有 | 可用但较少暴露 | `S0` | 线性无关性检查相关的 fast path |
| `--nodepbound` | `PlutoOptions` 中有 | 可用但较少暴露 | `S0` | 开发/实验性质 |

### 注

这部分是当前 `polcert` 最适合覆盖的区域，因为 `Stmt` 集合和 `domain` 一般不需要重写。

## 6. DFP / typed / hybrid fusion

| 选项 | 模块 | 当前 artifact | 效果类别 | 说明 |
| --- | --- | --- | --- | --- |
| `--dfp` | `lib/framework-dfp.c` | 当前 binary 不可用 | `S0` | 另一套 affine hyperplane 合成框架 |
| `--typedfuse` | `main.cpp`, `framework-dfp.c` | parser 可见，但运行时报错 | `S0` | 依赖 DFP + solver |
| `--hybridfuse` | `main.cpp`, `framework-dfp.c` | parser 可见，但运行时报错 | `S0` | 外层 typed，内层 max |
| `--delayedcut` | `main.cpp`, `framework-dfp.c` | parser 可见，但运行时报错 | `S0` | DFP 中延迟切分 |
| `--lp`, `--ilp`, `--glpk`, `--gurobi`, `--lpcolor`, `--clusterscc` | `main.cpp`, `framework-dfp.c`, solver backend | 当前 binary 不可用 | `S0` | 当前构建未启用对应 solver |

### 对 validation 的含义

DFP 在语义上仍属于“找 affine hyperplane”的范畴，本身不要求 domain mutation。因此它并不是最难验证的一支。真正难的是：

- 当前 artifact 不可用
- 它引入了另一套调度搜索逻辑和 colouring witness

如果将来要覆盖 DFP，建议排在 tiling/ISS 之后。

## 7. Tiling、parallel、diamond、intra-tile

| 选项 | 模块 | 当前 artifact | 效果类别 | 说明 |
| --- | --- | --- | --- | --- |
| `--tile` / `--notile` | `lib/tile.c` | 可用，源码默认开 | `D1` | 引入 tile iterators，重写 domain 和 schedule |
| `--ft`, `--lt` | `lib/tile.c`, `include/pluto/pluto.h` | 可用但帮助文本不显眼 | `D1` | 手工指定第一层 tiling 的起止深度 |
| `--second-level-tile` | `lib/tile.c`, `lib/tile_size_selection_model.cpp` | 可用 | `D1` | 再加一层 tile space，domain 进一步增维 |
| `--determine-tile-size` | `lib/tile_size_selection_model.cpp` | 可用 | `D1` | 自动 tile size 选择，不改变 pass 类型但改变 tile 参数 |
| `--cache-size` | `tile_size_selection_model.cpp` | 可用 | `D1` | tile size selection 的模型参数 |
| `--data-element-size` | `tile_size_selection_model.cpp` | 可用 | `D1` | tile size selection 的模型参数 |
| `--parallel` / `--noparallel` | `lib/tile.c`, `tool/ast_transform.c` | 可用，源码默认开 | `S1` 或 `D1` | 不 tile 时做 wavefront schedule；tile 时做 tile schedule + OMP 标记 |
| `--multipar` | `lib/tile.c`, `tool/pluto_codegen_if.c` | 可用 | `S1` 或 `D1` | 多维 wavefront / 多层并行 |
| `--innerpar` | `lib/tile.c` | 可用 | `S1` 或 `D1` | 倾向 inner parallel，而非 pipelined parallel |
| `--diamond-tile` / `--nodiamond-tile` | `lib/pluto.c`, `lib/tile.c` | 可用，源码默认开 | `D1` | 先做 diamond-aware hyperplane 选择 / skew，再进入 ordinary tiling 和后续 reschedule |
| `--full-diamond-tile` | `lib/pluto.c` | 可用 | `D1` | 更强的 producer mode：在 concurrent-start cone complement 中放开到全维；不是另一套 checked tiling relation |
| `--intratileopt` / `--nointratileopt` | `lib/post_transform.c` | 可用，源码默认开 | `S0`、`S1` 或 `D1` 的后续重排 | 本身主要改 point-loop order，不单独引入新 statement |

### 实用分类

- `parallel + notile`
  - 主要是 `S1`
  - 它可能不改 domain，但会改变 schedule 结构
- `tile`
  - 进入 `D1`
  - 因为 Pluto 会把 tile coordinates 作为新的 iterator 填进 domain
- `diamond-tile`
  - 也是 `D1`
  - 因为它不是只在 codegen 侧加优化，而是真正改 polyhedral 变换
  - 但从当前 proof 设计看，它应被理解成 `diamond-aware affine midpoint + ordinary tiling`

## 8. ISS

| 选项 | 模块 | 当前 artifact | 效果类别 | 说明 |
| --- | --- | --- | --- | --- |
| `--iss` | `lib/iss.c`, `tool/main.cpp` | 可用 | `P1` | 在 scheduler 前对 index set 做 splitting |

ISS 是“超出当前 scheduling validator”最明显的一类能力，因为它改变的不只是 instances 的先后顺序，而是 instance 集合本身的切分方式。

## 9. codegen-only / mostly-codegen features

| 选项 | 模块 | 当前 artifact | 效果类别 | 说明 |
| --- | --- | --- | --- | --- |
| `--prevector` / `--noprevector` | `post_transform.c`, `ast_transform.c` | 可用，默认开 | `C1` | 既影响 point-loop 选择，也影响 AST vector annotation |
| `--unrolljam` / `--nounrolljam` | `polyloop.c`, `ast_transform.c` | 可用，默认开 | `C1` | 候选选择 + AST unroll/jam 标记 |
| `--ufactor` | `polyloop.c`, `ast_transform.c` | 可用 | `C1` | unroll factor |
| `--cloogsh` | `pluto_codegen_if.c` | 可用 | `C1` | CLooG 选项 |
| `--nocloogbacktrack` | `pluto_codegen_if.c` | 可用 | `C1` | CLooG 选项 |
| `--cloogf`, `--cloogl` | parser 中有 | 可用 | `C1` | 控制 CLooG 优化层次 |
| `--codegen-context` | `pluto_codegen_if.c`, `program.cpp` | 可用 | `C1` | 附加 codegen context |
| `--bee` | `pluto_codegen_if.c` | 可用 | `C1` | Bee/Cl@k pragma |

### 一个边界问题

`prevector` 不完全是纯 codegen 选项，因为它也会参与 point-loop 选择启发式；但从验证难度上看，它仍比 tiling/ISS 简单得多，因为它不会单独引入新的 instance space。

## 10. 杂项与隐藏选项

| 选项 | 当前 artifact | 备注 |
| --- | --- | --- |
| `-o` | 可用 | 自定义输出文件名 |
| `--silent` | 可用 | 只影响日志 |
| `--debug` / `--moredebug` | 可用 | 对源码研究很有用 |
| `--time` | parser 中有 | 计时统计，默认开启 |
| `--scalpriv` | parser 中有 | Candl privatization 相关 |
| `--pipsolve` / `--islsolve` | 可用 | classic Pluto 约束求解 backend |
| `--forceparallel` | parser 有，但当前看来未接线 | 需要当作“死接口”对待 |
| `--indent` | 说明里存在，但 `main.cpp` 明示“Handled in polycc” | 当前 `pluto` 本体不处理 |

## 11. 实际默认值矩阵

根据 `/pluto/lib/program.cpp:833-939` 和 `/pluto/tool/main.cpp:386-543`，在“用户完全不加这些选项”的情况下，当前 artifact 的有效默认值近似是：

| 选项族 | 有效默认值 |
| --- | --- |
| 依赖分析 | `isldep=1`, `lastwriter=0`, `rar=0`, `isldepaccesswise=1` |
| affine scheduling | `smartfuse`, `identity=0` |
| tiling | `tile=1`, `intratileopt=1`, `diamondtile=1`, `fulldiamondtile=0` |
| 并行 | `parallel=1`, `multipar=0`, `innerpar=0` |
| codegen annotation | `prevector=1`, `unrolljam=1`, `ufactor=8` |
| solver | `islsolve=1`, `pipsolve=0` |

这和 `--help` 里“tile/parallel disabled by default”的说法矛盾。实际行为以源码为准。

## 12. 对 `polcert` 的最直接分类

若目标是逐步扩验证能力，可以把 Pluto 选项先按下面四组处理：

1. 当前已覆盖或接近可覆盖
   - `smartfuse`, `nofuse`, `maxfuse`, `rar`, `readscop`, `dumpscop`
2. 下一步建议先扩
   - `parallel + notile`
3. 中期要专门设计 domain-aware validator
   - `tile`, `second-level-tile`, `diamond-tile`, `intratileopt`
4. 后期再碰
   - `iss`, `dfp`, `typedfuse`, `hybridfuse`
