# Pluto Comprehensive Notes

这组文档记录了对 Pluto fork 的源码级整理，目标是服务两件事：

1. 搞清楚当前 artifact 里 Pluto 实际做了什么，而不是只看 README 或 `--help`。
2. 为 `polcert` 从“只验证 affine scheduling”扩展到 Pluto 的更多能力，准备一套清晰的技术地图和验证提案。

## 研究对象与来源

- 主分析对象是 container 内实际运行的 Pluto 源码树 `/pluto`，commit 是 `7cb0892`，与 `pluto --version` 一致。
- 另外在宿主机克隆了一份 fork 到 `/tmp/verif-scop-pluto`，commit 是 `3afdd71`。它更接近当前 GitHub 头，但不是当前 container 里实际跑的版本。
- 本目录中所有带行号的源码引用，默认都指向 `/pluto` 这一份源码树。

## 为什么需要这一组文档

`polcert` 当前验证 envelope 基本等价于 Pluto README 里给 artifact 推荐的那组参数：

```sh
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
  --smartfuse --nounrolljam --noparallel --notile --rar
```

在这个 envelope 里，Pluto 基本只改 scheduling/scattering，不碰 tiling、ISS、OpenMP/vector/unroll、domain 扩张等更复杂的变换。

但 Pluto 源码本身远不止这部分。它还包含：

- tiling 和 second-level tiling
- wavefront / pipelined parallel scheduling
- diamond tiling 和 full-dimensional concurrent start
- intra-tile loop reordering
- ISS (index set splitting)
- PET 前端
- codegen 时的 OpenMP/vector/unroll-jam 标注
- DFP / typed fusion / hybrid fusion 框架
- libpluto API，以及面向 Polly/ISL 的 schedule 导出路径

因此，想扩展验证，不能只继续盯着 `pluto_auto_transform()`；还得把前后两侧的 IR 变化、domain 变化、statement splitting 和 codegen-only annotation 分清楚。

## 阅读顺序

1. `source-map.md`
   作用：快速建立文件级地图、核心数据结构、默认值和“哪些功能是真活的，哪些是半死的”。
2. `pipeline.md`
   作用：从 `tool/main.cpp` 和 `lib/plutolib.c` 出发，按真实执行顺序讲完整 pipeline。
3. `options-and-capabilities.md`
   作用：把 CLI/隐藏选项、源码模块、当前 artifact 是否可用、对 validation 的影响放进一个矩阵。
4. `experiments.md`
   作用：记录在 container 中复现实验得到的行为证据。
5. `formalization-status.md`
   作用：单独记录当前形式化主线已经覆盖什么、还没覆盖什么。
6. `tiling-validation-design.md`
   作用：详细说明 tiling validation 的输入、正确性义务、以及当前 prototype 的设计。
7. `tiling-coq-bridge.md`
   作用：说明当前 Coq tiling core theorem 和 OCaml/OpenScop checker 之间还差哪几层桥接。
8. `tiling-coq-checker-interface.md`
   作用：固定 verified tiling checker 应该采用的 Coq 输入、checker 分解和 theorem 形状。
9. `tiling-transformation-bridge-plan.md`
   作用：单独收敛 `pi_transformation` 这条最关键的剩余 bridge，以及建议的 theorem 顺序。
10. `tiling-pass-architecture.md`
   作用：固定“tiling 需要独立 validation pass、现有 schedule validator 保持不动”的架构。
11. `iss-validation-design.md`
   作用：单独说明 ISS 为什么是 splitting-equivalence 问题，以及推荐的 witness 形状。
12. `validation-proposals.md`
   作用：给出从当前 `polcert` 能力向 Pluto 完整功能扩展的 staged roadmap。

## 最重要的结论

- Pluto 的唯一“核心 affine scheduler”是 `pluto_auto_transform()`，位置在 `/pluto/lib/pluto.c:1492`。其它大能力都在它之前或之后。
- `tool/main.cpp` 是 CLI 版 Pluto 的真实总控，它决定了 phase 顺序，比 README 和 `--help` 更可信。
- `pluto_populate_scop()` 不只回写 schedule，还会回写 domain、iterator、access 维度和 loop metadata；因此只要用了 tiling/ISS，就已经超出“schedule-only validation”。
- 当前 artifact 的真实默认值来自 `/pluto/lib/program.cpp:833-939`，而不是 `pluto --help`。实际默认值会开 `tile`、`parallel`、`diamondtile`、`prevector`、`unrolljam`。`--help` 里的“disabled by default”有多处是过期描述。
- DFP/typedfuse/hybridfuse 在源码里是大模块，但当前 container 的 binary 没有 GLPK/Gurobi 支持，因此这一支在 artifact 中实际上不可用。

## 和 `polcert` 的直接关系

对 `polcert` 来说，Pluto 能力大致分为五类：

1. 只改 affine schedule 的能力
   这是当前最适合验证、也已经在用的部分。
2. 只改 schedule，但会新增 schedule 维的能力
   典型例子是 `--parallel --notile` 触发的 wavefront schedule。
3. 同时改 domain 和 schedule 的能力
   典型例子是 tiling、second-level tiling、diamond tiling。
4. 会拆 statement / split domain 的能力
   典型例子是 ISS。
5. 只在 codegen AST 上做 annotation 的能力
   典型例子是 OpenMP pragma、vector pragma、unroll-jam 标记。

后续验证路线最自然的扩展顺序，不是“先碰所有新 feature”，而是按这五类从易到难推进。
