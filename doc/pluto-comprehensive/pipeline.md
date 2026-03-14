# Pluto Pipeline

本文件按真实执行顺序整理 Pluto 的 pipeline。重点不是“Pluto 能做哪些优化”，而是“这些优化在哪个 phase 发生、顺序如何决定、哪些 phase 会改变什么 IR”。

## 1. CLI 版的总流程

CLI 总流程全部收敛在：

- `/pluto/tool/main.cpp:184-904`

可以压缩成下面这个伪代码：

```text
parse options
normalize options

if PET:
  extract PET scop
  convert PET -> PlutoProg
else:
  read source or .scop
  maybe dump before.scop
  convert OSL/OpenScop -> PlutoProg

if ISS:
  apply ISS

if not identity:
  pluto_auto_transform()

recompute dep directions/satisfaction

if tile:
  pluto_tile()
else if intratileopt:
  pluto_intra_tile_optimize()

if parallel && !tile && !identity:
  pluto_create_tile_schedule()

if dumpscop:
  pluto_populate_scop()
  write after.scop

emit .regtile
emit .cloog
emit code with CLooG + AST annotations
```

## 2. 选项解析与归一化

### 2.1 解析

命令行选项表在：

- `/pluto/tool/main.cpp:198-277`

这里能直接看到：

- 哪些选项一定编进当前 binary
- 哪些选项只有在 GLPK/Gurobi 打开时才编进 CLI
- 哪些选项虽然能 parse，但后面可能根本没用

### 2.2 归一化

选项归一化在：

- `/pluto/tool/main.cpp:386-543`

主要逻辑：

1. `isldep` / `candldep` 不能同时开。
2. 若两者都没指定，则自动选 `isldep`。
3. `lastwriter` 只支持 `isldep`。
4. `second-level-tile` 和 `determine-tile-size` 不能同时开。
5. `tile = 0` 时强制关掉 `diamondtile` / `fulldiamondtile`。
6. `multipar = 1 && parallel = 0` 时自动开 `parallel`。
7. typed/hybrid/delayedcut 会尝试把配置推进到 DFP 框架；若当前 binary 没有 solver 支持，则报错退出。

这一步的重要性在于：Pluto 的真实 phase 选择，不是靠用户原始命令行直接决定，而是先经过一轮“语义补全与禁用”。

## 3. 前端分叉

前端分叉点在：

- `/pluto/tool/main.cpp:552-672`

### 3.1 PET 路径

当 `options->pet` 为真时：

- `/pluto/tool/main.cpp:553-579`
- `/pluto/tool/pet_to_pluto.cpp`

流程是：

1. `pet_scop_extract_from_C_source()`
2. `pet_to_pluto_prog()`
3. 在 PET 自己的 schedule/access 上重建 `PlutoProg`

PET 路径可以做依赖分析、调度、tiling、codegen，但当前 fork 的 `--dumpscop` 不支持 PET。源码里直接打印：

```text
[Pluto] --dumpscop not support pet frontend yet
```

对应位置：

- `/pluto/tool/main.cpp:647-649`

### 3.2 Clan / readscop 路径

非 PET 路径在：

- `/pluto/tool/main.cpp:579-672`

又分两种：

- `--readscop`：`osl_scop_pread()` 直接读 OpenScop
- 默认 C 路径：`clan_scop_extract()` 先从 C 抽出 OpenScop

在这条路径上，`--dumpscop` 会先于任何调度发生，直接把提取后的输入 SCoP 写成 `.beforescheduling.scop`：

- `/pluto/tool/main.cpp:621-649`

这也是当前 PolCert/PolOpt 能拿到 “before” 和 “after” 两个 OpenScop 模型的原因。

## 4. OpenScop/PET 到 `PlutoProg`

### 4.1 OSL/OpenScop 转换

OSL 路径的入口：

- `/pluto/tool/osl_pluto.c:1605`

`osl_scop_to_pluto_prog()` 做的事情：

1. 建 `PlutoProg`
2. 导入参数和 parameter context
3. 导入数组名
4. 遍历 statements，构造 `Stmt`
5. 计算 dependences
6. 初始化 hyperplane 信息

对验证而言，这一步的关键是：Pluto 并不是只把“schedule”读进来，而是把整个 polyhedral model 读成自己的内部对象，包括：

- domain
- schedule/scattering
- accesses
- parameters
- dependences

### 4.2 `pluto_populate_scop()` 回写

回写 OpenScop 的函数是：

- `/pluto/tool/osl_pluto.c:586-715`

它会同时做以下事情：

1. 用 Pluto 内部 domain 替换原 statement domain
2. 用 Pluto 内部 `trans` 替换原 scattering
3. 如果 iterator 数量变了，则改 body 中 iterator 列表
4. 若 iterator 增多，还会给 access relation 插空白输入维
5. 重建 scatnames
6. 写 loop metadata（parallel/vector）
7. 写 `pluto_unroll` 扩展

因此，`after.scop` 不是“原始 scop 加了一个新 scattering”这么简单，而是一个经过重写的 OpenScop 对象。

## 5. 依赖分析

### 5.1 OSL 路径：ISL / Candl

OSL 路径中依赖分析发生在：

- `/pluto/tool/osl_pluto.c:1665-1693`

默认会走 ISL：

- `/pluto/tool/osl_pluto.c:1186-1457`
- `/pluto/lib/program.cpp:622-695`

Pluto 用下列输入求依赖：

- statement domains
- statement accesses
- current scattering/schedule

然后通过 `isl_union_map_compute_flow()` 分别算：

- RAW
- WAR
- WAW
- RAR（若 `--rar`）

`lastwriter` 会换一种 flow 计算方式，因此改变的不只是“数量”，而是依赖表示结构本身。

Candl 路径在：

- `/pluto/tool/osl_pluto.c:1459-1599`

### 5.2 PET 路径

PET 路径的依赖分析在：

- `/pluto/tool/pet_to_pluto.cpp:76-169`

这里和 OSL 路径的差异是：

- 先把 read/write access 编码进 domain tuple name
- 再构造 access-wise schedules
- 然后仍然落到 `compute_deps_isl()`

### 5.3 对验证的含义

Pluto 的“合法 schedule”不是只依赖源程序的纯语义，而是依赖“当前 polyhedral extraction + 当前 dependence representation + 当前 schedule encoding”。

因此在验证 Pluto 结果时，最稳妥的对象应当是：

- Pluto 送入优化的 polyhedral model
- Pluto 优化后的 polyhedral model

而不是“重新从源程序语义猜测 Pluto 应该保什么”。

## 6. ISS 在 scheduler 之前

ISS 入口在：

- `/pluto/tool/main.cpp:688-690`

对应实现：

- `/pluto/lib/iss.c`

也就是说，ISS 不是 `pluto_auto_transform()` 的一个子步骤，而是它之前的一个 program rewrite。

这点非常关键：

- classic scheduler 主要围绕已有 statements/hyperplanes 找更好的 affine order
- ISS 则可能先改变 statement/domain 组织方式，再把结果交给 scheduler

因此 ISS 的验证义务，不能并入“affine scheduling correctness”；它本质上更接近“程序分裂后语义保持”。

## 7. `pluto_auto_transform()`：经典 Pluto 核心

入口：

- `/pluto/lib/pluto.c:1492-1849`

### 7.1 初始化

前半段先做：

1. 清空 `dep->satisfied`
2. 建 DDG
3. 计算 SCC
4. 保存旧 `trans`
5. 重置 statement transformation
6. `normalize_domains()`

### 7.2 precut / 初始 cut

在第一层 band 前，会尝试：

- `.fst` / `.precut` 驱动的用户 cut：`/pluto/lib/pluto.c:874-1005`
- 若当前是 `smartfuse` 且不是 DFP，先做 `cut_scc_dim_based()`：`/pluto/lib/pluto.c:541-589`

这一步决定了后续 hyperplane 搜索的“可融合边界”。

### 7.3 经典 hyperplane 搜索循环

非 DFP 路径的主循环在：

- `/pluto/lib/pluto.c:1697-1823`

循环中每次做：

1. 计算当前还缺多少独立 hyperplanes
2. 必要时计算 connected components
3. 调 `find_permutable_hyperplanes()`
4. 若找到 hyperplane，则加入 `trans`
5. 更新 dependence satisfaction
6. 若找不到，则根据 fuse heuristic 做 cut
7. 在 EAGER/LAZY 两种模式间切换

终止条件：

- `pluto_transformations_full_ranked(prog)`
- `deps_satisfaction_check(prog)`

### 7.4 真正求解 hyperplane 的地方

`find_permutable_hyperplanes()` 在：

- `/pluto/lib/pluto.c:770-857`

核心逻辑：

1. 从 `get_permutability_constraints()` 拿 base constraints
   - `/pluto/lib/framework.cpp:348-485`
2. 再加 coefficient bound
3. 再加 non-trivial-solution constraints
4. 再加 linear independence constraints
5. 最后交给 `pluto_prog_constraints_lexmin()`
   - `/pluto/lib/pluto.c:275-409`

也就是说，classic Pluto 的“自动调度”本质上是：

- 先把依赖合法性、线性无关性、系数约束、目标函数都编成一个 ILP/LP/PIP 约束系统
- 再 lexicographic minimize 出下一条 hyperplane

### 7.5 cut heuristic

关键 cut 函数：

- `cut_scc_dim_based()`：`/pluto/lib/pluto.c:541-589`
- `cut_smart()`：`/pluto/lib/pluto.c:592-624`
- `cut_conservative()`：`/pluto/lib/pluto.c:626-652`

这类 cut 会插入 `H_SCALAR` 行，相当于显式要求 distribution / sequencing，把某些原本可尝试融合的区域拆开。

### 7.6 classic 路线中的 diamond tiling hook

在 classic 路径中，如果：

- `diamondtile = 1`
- 首个 band 找到至少 2 个 hyperplanes
- 尚未找到 concurrent start

就会调用：

- `pluto_diamond_tile()`

对应触发点：

- `/pluto/lib/pluto.c:1742-1746`

因此 diamond tiling 不是单独独立于 scheduler 的一个后处理；它会在 scheduler 的第一个可置换 band 上介入。

## 8. DFP 路线

DFP 相关代码主要在：

- `/pluto/lib/framework-dfp.c`

`pluto_auto_transform()` 里 DFP 分支入口在：

- `/pluto/lib/pluto.c:1606-1694`

大致顺序是：

1. 建 fusion conflict graph
   - `/pluto/lib/framework-dfp.c:1074-1210`
2. 做 colouring
3. `find_permutable_dimensions_scc_based()`
4. `introduce_skew()`
   - `/pluto/lib/framework-dfp.c:3260-3410`
5. 若需要，再做 diamond tiling
6. 检查 deps 是否还满足；若不满足，退回 cut-all-sccs

### 当前 artifact 的实际状态

DFP 是源码中真实存在的大模块，但当前 container binary 不可用，原因是：

- CLI 中 `--dfp` / `--glpk` / `--gurobi` 等选项本身就被条件编译保护
- `--typedfuse` 仍然能 parse，但后续会报错要求启用 GLPK/Gurobi

因此：

- 文档里要把它当成 Pluto 的“源码能力”
- 但在当前 artifact 里，它不是“可运行能力”

## 9. `pluto_tile()`：tile 之后的固定顺序

入口：

- `/pluto/lib/tile.c:214-326`

执行顺序是固定的：

1. 找 outermost / innermost permutable bands
2. 必要时补一维 tile band 给 innermost parallel loops
3. `pluto_tile_scattering_dims()`
4. 重算 dep directions/satisfaction
5. 如果开 diamond tiling，做 `pluto_diamond_tile_reschedule()`
6. 如果开 `intratileopt`，做 `pluto_intra_tile_optimize_band()`
7. 如果开 `parallel`，做 `pluto_create_tile_schedule()`

也就是说，tile 本身不是一个单步骤，而是一个小 pipeline。

## 10. 不 tile 也可能新增 schedule 维

这是当前 `polcert` 容易忽略的一点。

在：

- `/pluto/tool/main.cpp:718-737`

如果满足：

- `parallel = 1`
- `tile = 0`
- `identity = 0`

Pluto 仍会调用：

- `/pluto/lib/tile.c:473-483` 的 `pluto_create_tile_schedule()`

这会把现有可置换 band 改成 wavefront/pipelined parallel schedule。它不一定改 domain，但会改 `trans`，而且通常会增加新的 schedule 结构含义。

因此：

- `--parallel --notile` 不是“只加 OMP pragma”
- 它仍然是一个真正的 polyhedral transformation

## 11. post-transform：locality/vector/unroll 逻辑

主要在：

- `/pluto/lib/post_transform.c`
- `/pluto/lib/polyloop.c`

### 11.1 vector/locality 选择

`pluto_intra_tile_optimize_band()`：

- `/pluto/lib/post_transform.c:444-520`

它会：

1. 找当前 band 下的 loops
2. 给 loops 按 spatial reuse / temporal reuse / vectorizability 打分
3. 选最优 loop 移到 innermost

打分逻辑在：

- `/pluto/lib/post_transform.c:228-262`

### 11.2 unroll-jam 候选

候选选择在：

- `/pluto/lib/polyloop.c:576-605`

是否 profitable 的代价函数在：

- `/pluto/lib/polyloop.c:549-573`

这是一个明显的启发式路径，不是 legality proof 的核心。

## 12. codegen：`.cloog` -> CLAST -> C

主要入口：

- `/pluto/tool/pluto_codegen_if.c:62-125`：生成 `.cloog`
- `/pluto/tool/pluto_codegen_if.c:205-308`：CLooG/CLAST codegen
- `/pluto/tool/pluto_codegen_if.c:312-325`：multicore codegen 包装

CLAST annotation 在：

- `/pluto/tool/ast_transform.c:23-127`：parallel
- `/pluto/tool/ast_transform.c:131-188`：unroll-jam
- `/pluto/tool/ast_transform.c:192-243`：vector

这一步的语义边界要分清：

- parallel/vector/unroll 标注会影响最终 C 代码
- 但它们大多不再回到 polyhedral model 中
- 对 polyhedral validator 来说，这一层更接近“代码生成 correctness”而不是“schedule/domain correctness”

## 13. libpluto 路径的特殊点

`libpluto` 里的 `pluto_schedule_prog()`：

- `/pluto/lib/plutolib.c:29-101`

基本复刻了 CLI 版的 phase 顺序。

但它还有一个很关键的差异：

- `normalize_domain_schedule()`：`/pluto/lib/plutolib.c:223-257`

这个函数会把 tiling 带来的 domain 扩张信息挪到 schedule constraints 中，再把新增的 statement dimensions 去掉。

这意味着 Pluto 自己已经有一种“把 tiling 结果规约回原 domain 空间”的表示办法。

对验证扩展来说，这给了一个非常强的方向：

- 不一定非要直接在 OpenScop 的“增维 domain”表示上做证明
- 可以考虑先借鉴 libpluto 的 normalization，把某些 tiling case 降成“原始 point-domain + richer schedule relation”再验证
