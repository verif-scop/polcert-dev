# Pluto Source Map

本文件回答三个问题：

1. Pluto 这个 fork 的构建入口、主模块和核心数据结构在哪里。
2. 哪些源码文件真正决定行为。
3. 哪些选项/字段是活跃功能，哪些只是残留接口或过期帮助信息。

## 1. 构建系统和目录骨架

当前 fork 仍然是 autotools 工程，不是 CMake。

- 顶层构建入口：
  - `/pluto/autogen.sh`
  - `/pluto/configure.ac`
  - `/pluto/Makefile.am`
- 主要递归子目录：
  - `piplib`
  - `polylib`
  - `isl`
  - `openscop`
  - `cloog-isl`
  - `clan`
  - `candl`
  - `pet`
  - `lib`
  - `tool`

我在 container 里重新跑了 `cd /pluto && make -j2`，构建成功。实际递归构建顺序是：

```text
piplib -> polylib -> isl -> openscop -> cloog-isl -> clan -> candl -> pet -> lib -> tool
```

这和 `/pluto/Makefile.am` 中的 `SUBDIRS` 一致。

## 2. 两层入口

Pluto 有两个“主入口层”。

### 2.1 CLI 入口

CLI 可执行文件 `pluto` 由 `/pluto/tool/Makefile.am` 构建，主入口在：

- `/pluto/tool/main.cpp`

它负责：

- 解析命令行
- 规范化选项
- 选择前端 (`Clan` / `readscop` / `PET`)
- 构造 `PlutoProg`
- 调用 `pluto_auto_transform()`
- 调用 tiling / intra-tile / parallel tile schedule
- 回写 OpenScop
- 调用 CLooG 做 codegen

### 2.2 libpluto 入口

库入口在：

- `/pluto/lib/plutolib.c`
- `/pluto/include/pluto/pluto.h`

这里的关键 API 是：

- `pluto_transform()`
- `pluto_schedule()`
- `pluto_schedule_str()`

对验证研究来说，`libpluto` 很重要，因为它包含一个 CLI 路径没有直接暴露给 OpenScop 的“normalization”技巧：`normalize_domain_schedule()` 会把 tiling 带来的 domain 变化搬运到 schedule 侧，从而尽量保持 domain 的空间形状。这对后续设计“验证友好的 Pluto 导出格式”很有参考价值。

## 3. 文件级职责地图

下面是实际会影响 Pluto 行为的核心文件。

### 3.1 `tool/` 侧

| 文件 | 作用 |
| --- | --- |
| `/pluto/tool/main.cpp` | CLI 总控，决定 phase 顺序、选项分支、前后端衔接 |
| `/pluto/tool/osl_pluto.c` | OpenScop/OSL 到 `PlutoProg` 的转换；OSL 路径依赖分析；把结果回写到 OpenScop |
| `/pluto/tool/pet_to_pluto.cpp` | PET 前端，把 `pet_scop` 转成 `PlutoProg` |
| `/pluto/tool/pluto_codegen_if.c` | 生成 `.cloog`、调用 CLooG、驱动 codegen |
| `/pluto/tool/ast_transform.c` | 在 CLAST 上标记 parallel / vector / unroll-jam |
| `/pluto/tool/constraints_polylib.c` | 约束与 polylib/Cloog 之间的打印和桥接 |

### 3.2 `lib/` 侧

| 文件 | 作用 |
| --- | --- |
| `/pluto/lib/pluto.c` | Pluto 核心调度器；hyperplane 搜索；cut heuristic；diamond tiling 的 classic 入口 |
| `/pluto/lib/framework.cpp` | 构造 permutability constraints；Feautrier/Pluto 形式的约束拼装 |
| `/pluto/lib/framework-dfp.c` | DFP 路线：fusion conflict graph、colouring、scale/shift、skew |
| `/pluto/lib/tile.c` | tiling、tile schedule / wavefront schedule |
| `/pluto/lib/post_transform.c` | intra-tile loop order、vector/locality/unroll 相关启发式 |
| `/pluto/lib/polyloop.c` | loop 和 band 发现、parallel/unroll 候选选择 |
| `/pluto/lib/iss.c` | index set splitting |
| `/pluto/lib/program.cpp` | `PlutoProg` / `PlutoOptions` 构造、默认值、ISL 依赖分析 helper |
| `/pluto/lib/transforms.c` | 行交换、sink、loop move 等基础变换工具 |
| `/pluto/lib/ddg.c` | 数据依赖图、SCC/CC 计算 |
| `/pluto/lib/constraints.c` | 约束系统、求解入口、solver backend 分派 |
| `/pluto/lib/constraints_isl.c` | ISL 与 Pluto constraints 的相互转换 |
| `/pluto/lib/tile_size_selection_model.cpp` | tile size selection model |
| `/pluto/lib/plutolib.c` | libpluto API 层，面向 ISL/Polly 的 schedule 导出 |

## 4. 核心数据结构

核心结构定义主要在：

- `/pluto/lib/pluto.h`
- `/pluto/include/pluto/pluto.h`

### 4.1 `PlutoOptions`

用户看见的是 CLI 选项，但真正决定行为的是 `PlutoOptions`。

关键字段包括：

- `tile`
- `intratileopt`
- `diamondtile`
- `fulldiamondtile`
- `parallel`
- `innerpar`
- `unrolljam`
- `prevector`
- `fuse`
- `iss`
- `isldep` / `candldep`
- `lastwriter`
- `second_level_tile`
- `find_tile_sizes`
- `pipsolve` / `islsolve` / `glpk` / `gurobi`
- `dfp`

定义位置：

- `/pluto/include/pluto/pluto.h:48-248`

### 4.2 `Stmt`

`Stmt` 是 Pluto 内部的 statement 级语义对象，关键字段：

- `domain`
- `iterators`
- `text`
- `dim` / `dim_orig`
- `tile`
- `trans`
- `hyp_types`
- `reads` / `writes`
- `scc_id` / `cc_id`
- `first_tile_dim` / `last_tile_dim`
- `pstmt`（PET 路径时使用）

定义位置：

- `/pluto/lib/pluto.h:131-211`

对 validation 最重要的几个字段是：

- `domain`: 被 tiling/ISS 等 pass 改写
- `trans`: schedule/scattering 的内部表示
- `dim_orig`: 可以判断哪些 iterator 是优化后新增的

### 4.3 `Dep`

`Dep` 是 Pluto 的依赖对象，关键字段：

- `src` / `dest`
- `src_acc` / `dest_acc`
- `dpolytope`
- `type` (`RAW/WAR/WAW/RAR`)
- `satisfied`
- `satisfaction_level`
- `satvec`
- `cst`
- `dirvec`

定义位置：

- `/pluto/lib/pluto.h:228-295`

验证扩展时，`dpolytope` 与 `dirvec/satvec` 很关键：前者是语义基础，后者是 Pluto 内部“为什么某个变换合法”的 operational bookkeeping。

### 4.4 `HyperplaneProperties`

这是 Pluto 在每一层 schedule 维度上挂的公共属性：

- `dep_prop`：`PARALLEL` / `PIPE_PARALLEL` / `SEQ`
- `type`：`H_LOOP` / `H_TILE_SPACE_LOOP` / `H_SCALAR`
- `band_num`
- `unroll`
- `prevec`

定义位置：

- `/pluto/lib/pluto.h:307-327`

### 4.5 `PlutoProg`

`PlutoProg` 是整个程序级 IR，关键字段：

- `stmts`
- `deps`
- `transdeps`
- `params`
- `num_hyperplanes`
- `ddg`
- `fcg`
- `hProps`
- `nvar` / `npar`
- `param_context`
- `codegen_context`
- `globcst`
- `is_diamond_tiled`
- 一系列 timing/statistics 字段

定义位置：

- `/pluto/lib/pluto.h:329-420`

它是 Pluto 所有 phase 的共享状态容器。

## 5. 真正生效的默认值

默认值不以 `--help` 为准，而以 `pluto_options_alloc()` 为准：

- `/pluto/lib/program.cpp:833-939`

真正的初始默认值包括：

- `tile = 1`
- `intratileopt = 1`
- `parallel = 1`
- `diamondtile = 1`
- `unrolljam = 1`
- `prevector = 1`
- `fuse = kSmartFuse`
- `islsolve = 1`
- `readscop = 0`
- `dumpscop = 0`

然后 `main.cpp` 还会再做一轮 normalization：

- 若用户没显式选 `isldep`/`candldep`，则默认补上 `isldep = 1`
- 若 `tile = 0`，则自动关掉 `diamondtile` / `fulldiamondtile`
- 若 `multipar = 1 && parallel = 0`，会把 `parallel` 打开

对应源码：

- `/pluto/tool/main.cpp:386-543`

### 一个重要事实

`pluto --help` 中多处“默认关闭”的描述已经过期。

例如：

- `--tile` 的 help 文本说 “disabled by default”
- `--parallel` 的 help 文本说 “disabled by default”

但实际源码默认是开着的。我在 container 中直接运行不带这些选项的 `pluto --dumpscop /tmp/pluto-default-test.c`，生成的 `.pluto.c` 包含了 tiled + OpenMP 的结果，说明真实行为遵从源码默认值，而不是帮助文本。

## 6. 活跃功能、半活跃功能、死接口

### 6.1 活跃功能

这些功能在当前 artifact 中是完整可走通的：

- Clan 前端
- `--readscop`
- PET 前端
- ISL 依赖分析
- Candl 依赖分析
- classic Pluto affine scheduling
- tiling / second-level tiling
- diamond tiling
- intra-tile optimization
- wavefront / pipelined parallel scheduling
- OpenMP/vector/unroll-jam 标注
- ISS
- `--dumpscop`（仅非 PET 前端）

### 6.2 源码存在、当前 artifact 不可用

这些功能的主体源码在，但当前 binary 不可用：

- `--dfp`
- `--typedfuse`
- `--hybridfuse`
- `--delayedcut`
- `--glpk`
- `--gurobi`
- `--lp`
- `--ilp`
- `--lpcolor`
- `--clusterscc`

原因不是“源码没写”，而是当前 container 构建时没有启用 GLPK/Gurobi。`main.cpp` 中这些选项本来就放在 `#if defined GLPK || defined GUROBI` 条件编译块里。

### 6.3 半死/过期/未接线接口

这类东西在做 comprehensive audit 时很容易误判。

#### `forceparallel`

- 能被 parser 接收：`/pluto/tool/main.cpp:237`, `/pluto/tool/main.cpp:349`
- 在帮助文本里可见
- 但我没有在后续调度/代码生成路径里找到任何实际使用它的逻辑

当前结论：这是一个“parse 了但没有真正接线”的选项。

#### `dynschedule*`

`PlutoOptions` 和 `include/pluto/pluto.h` 里还有：

- `dynschedule`
- `dynschedule_graph`
- `dynschedule_graph_old`
- `dyn_trans_deps_tasks`

以及对应的一些函数声明：

- `pluto_dynschedule_graph_codegen`
- `pluto_dynschedule_codegen`
- `pluto_dynschedule_graph_parallelize`
- `pluto_dynschedule_parallelize`

但在当前源码树里我没有找到这些函数的实现，也没有在 `tool/main.cpp` 找到 CLI 暴露。

当前结论：这是遗留接口，不是当前 artifact 的活跃能力。

#### `help` 文本本身

`usage_message()` 不是源码真相，只是一个不完全同步的说明页。它至少有三类偏差：

- 默认值过期
- 一些 parser 支持的 flags 没写进 help
- 有些 flag 仍在 help 中，但实现上已弱化或未接线

所以后续研究 Pluto 时，不能把 `--help` 当权威 specification。
