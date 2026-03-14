# Experiments

本文件记录我在 container 中直接调用 Pluto 做的行为实验。目标不是 benchmark，而是确认各 phase 的真实效果、默认值、以及“哪些 pass 会越过当前 validator 的边界”。

## 1. 实验环境

- Container 内 Pluto 源码与二进制：`/pluto`，commit `7cb0892`
- `pluto --version` 输出：`PLUTO version 7cb0892`

所有实验都没有改动当前仓库本身；只是调用 container 内的 `/pluto`。

## 2. 默认值不是 help 文本说的那样

### 命令

```sh
cd /pluto
cp test/jacobi-1d-imper.c /tmp/pluto-default-test.c
pluto --silent --dumpscop /tmp/pluto-default-test.c
```

### 观察

- 生成了：
  - `pluto-default-test.beforescheduling.scop`
  - `pluto-default-test.afterscheduling.scop`
  - `pluto-default-test.pluto.c`
- 生成的 `pluto-default-test.pluto.c` 中出现了：

```c
#pragma omp parallel for
```

并且代码形态明显已经 tiled。

### 结论

当前 artifact 中：

- `tile`
- `parallel`

在默认情况下就是开启的，尽管 `pluto --help` 仍写着 “disabled by default”。

## 3. 纯 affine scheduling envelope：domain 不变，scattering 改变

### 命令

```sh
cd /pluto
pluto --dumpscop --notile --noparallel --nounrolljam --noprevector \
  --nodiamond-tile --smartfuse test/jacobi-1d-imper.c
```

### 观察

- `beforescheduling.scop` 的 domain header 保持原形状
- `afterscheduling.scop` 的 domain header 也保持同样形状
- scattering header 发生变化

### 结论

这基本就是当前 `polcert` 使用的安全 envelope：

- Pluto 主要只改 schedule/scattering
- domain/iterator/access 结构不需要扩张

## 4. `parallel` 但 `notile` 仍然会做真正的 polyhedral 变换

### 命令

```sh
cd /pluto
pluto --debug --silent --notile --parallel --nounrolljam --noprevector \
  --nodiamond-tile --smartfuse /pluto/test/jacobi-1d-imper.c
```

### 观察

debug 输出显示：

- 先完成 `pluto_auto_transform`
- 随后调用 `pluto_create_tile_schedule`
- 打印 warning：

```text
[pluto] WARNING: pipelined parallelism exists and --tile is not used.
```

- 变换结果被打印成类似：

```text
T(S1): (3t+i, 2t+i, 0)
T(S2): (3t+i+1, 2t+i+1, 1)
```

### 结论

`--parallel --notile` 不是“只在代码生成时打 OMP pragma”，而是会合成 wavefront/pipelined schedule。它对验证的意义是：

- 大概率仍可建模为 schedule-level 变换
- 但已经不再是“和原来一样维度的 schedule”

## 5. 开 tiling 后，domain 直接扩张

### 命令

```sh
cd /pluto
pluto --dumpscop --tile --parallel test/jacobi-1d-imper.c
```

### 观察

- `beforescheduling.scop` 的 domain header：

```text
6 6 2 0 0 2
```

- `afterscheduling.scop` 的 domain header：

```text
10 8 4 0 0 2
```

### 结论

tiling 不是只改 schedule。Pluto 会：

- 引入新的 iterator
- 改 statement domain
- 随后也会改 access relation 的输入维数

这已经超出当前 scheduling validator 的模型。

## 6. second-level tiling 会进一步放大 domain

### 命令

```sh
cd /pluto
cp test/matmul.c /tmp/slt.c
pluto --silent --dumpscop --tile --parallel --second-level-tile /tmp/slt.c
```

### 观察

`slt.afterscheduling.scop` 中：

- `DOMAIN` header 为：

```text
21 14 9 0 0 3
```

- `SCATTERING` header 为：

```text
9 23 9 9 0 3
```

- body 中原来的 `i j k` 前面出现了两层 tile iterator：

```text
fk0 fk1 fk2 fk3 fk4 fk5 i j k
```

并且 domain 里能看到两层 32 和 8 倍率的 linking constraints，例如：

```text
-32*fk3+i >= 0
8*fk0-fk3+7 >= 0
```

### 结论

second-level tiling 明确会让：

- domain 变成多层 tile-space + point-space 的组合
- validation 问题从“调度合法性”升级成“空间分解和覆盖等价性”

## 7. auto tile-size selection 确实在运行模型

### 命令

```sh
cd /pluto
pluto --silent --debug --tile --parallel --determine-tile-size test/matmul.c
```

### 观察

debug 输出中出现：

```text
Parallel dimension 0
Solution of the reuse polynomial: 127
Tile sizes for band
TileSize for dimension 0: 32
TileSize for dimension 1: 512
TileSize for dimension 2: 256
```

### 结论

`--determine-tile-size` 不是装饰参数，而是真正运行了 `tile_size_selection_model.cpp` 中的模型，并按 reuse polynomial 选 tile size。

## 8. diamond tiling 会在 classic scheduler 的首个 band 中插手

### 命令

```sh
cd /pluto
pluto --debug --silent --tile --parallel --smartfuse /pluto/test/jacobi-1d-imper.c
```

### 观察

debug 输出显示：

- 在 `pluto_auto_transform` 里首 band 找到两个 hyperplanes
- 之后触发 diamond tiling 路径
- 变换从普通的 `(t, 2t+i)` 形式变成 concurrent-start 友好的 skew 形式
- 后续又接着执行 `pluto_tile`、`pluto_intra_tile_optimize_band`、`pluto_create_tile_schedule`

### 结论

diamond tiling 不是独立小插件，而是会改变核心调度结果，再进入后续 tiling/post-transform/codegen。

## 9. ISS 会改 statement/domain 组织，不只是换顺序

### 命令

```sh
cd /pluto
pluto --debug --silent --iss --notile --noparallel --nounrolljam \
  --noprevector --nodiamond-tile /pluto/test/reverse-iss.c
```

### 观察

输出里能看到 ISS 之后的 statements/domain 被重组，再交给后续调度。

### 结论

ISS 明确属于“程序切分”能力，不是 affine scheduler 的一个普通选项。

## 10. PET 前端可用，但 `dumpscop` 不支持

### 命令

```sh
cd /pluto
pluto --pet --dumpscop test/matmul.c
```

### 观察

stderr 直接打印：

```text
[Pluto] --dumpscop not support pet frontend yet
```

但其余调度/tiling/codegen pipeline 仍然正常执行。

### 结论

如果以后想把 PET 路径也纳入 validation，当前 fork 还需要额外的 dump/witness 机制。

## 11. `readscop` 路径可单独工作

### 命令

```sh
cd /pluto
cp test/jacobi-1d-imper.c /tmp/readscop-test.c
pluto --silent --dumpscop --notile --noparallel /tmp/readscop-test.c
pluto --silent --readscop readscop-test.beforescheduling.scop
```

### 观察

第二条命令会产出：

- `readscop-test.beforescheduling.scop.pluto.c`
- `readscop-test.beforescheduling.scop.pluto.cloog`

说明 `--readscop` 走的是完整 pipeline，而不只是 parser smoke test。

### 结论

`readscop` 非常适合做“phase-by-phase 离线复现”和验证实验。

## 12. typed/hybrid fusion 在当前 artifact 中不可用

### 命令

```sh
cd /pluto
pluto --typedfuse --silent test/matmul.c
```

### 观察

直接报错：

```text
[pluto] ERROR: Typed or hybrid fusion is available with dfp framework only
which requires an LP solver. Configure pluto with --enable-glpk or --enable-gurobi
```

### 结论

要区分：

- “源码里存在”
- “当前 artifact 里能跑”

typed/hybrid/DFP 属于前者，不属于后者。

## 13. `lastwriter` 会改变依赖表示

### 命令

```sh
cd /pluto
pluto --isldepaccesswise --notile --noparallel test/jacobi-1d-imper.c
pluto --isldepaccesswise --lastwriter --notile --noparallel test/jacobi-1d-imper.c
```

### 观察

在这个例子上，打印出来的 dependence 数量分别是：

- 不开 `lastwriter`：`10`
- 开 `lastwriter`：`15`

### 结论

`lastwriter` 会显著改变依赖表示，但“是否让 dep 数量减少”并不是单调直觉能概括的。源码层面应把它理解为：

- 切换 flow construction 方式
- 改变 RAW/WAR/WAW 的组织方式

而不是简单的“做一遍 dep pruning”。

## 14. 这些实验对 validation 的直接结论

可以把实验结果压缩成四句话：

1. 当前 `polcert` 用的 `--notile --noparallel ...` 的确把 Pluto 约束在 schedule-only envelope 里。
2. `parallel + notile` 已经会产生 richer schedule，因此是下一个自然扩展点。
3. `tile` / `second-level-tile` / `diamond-tile` 会实打实改 domain 和 iterator，因此需要 domain-aware validator。
4. `ISS` 则要求 statement/domain splitting equivalence，难度比 tiling 更高。
