# Tiling Validation Design

这份文档讨论的不是“Pluto 怎样做 tiling”，而是“如果要验证 Pluto 的 tiling，检查器的输入应该是什么，应该证明什么，原型怎么落地”。

## 1. 问题重述

对当前 `polcert` 而言，普通 scheduling validator 的输入大致是：

- 优化前 polyhedral program
- 优化后 polyhedral program

并且默认两者：

- statement family 不变
- domain 维度不变
- 只在 schedule 上不同

Pluto 的 tiling 打破了这三点。

在 `after.scop` 里，经常会看到：

- 新的 tile iterators 被加入 statement domain
- 原 point iterators 被保留
- 额外出现 linking constraints，例如

```text
-32*fk3+i >= 0
32*fk3-i+31 >= 0
```

这编码的是：

```text
fk3 = floor(i / 32)
```

但更一般地，Pluto tile 的对象并不是“原 iterator 名字”，而是当前 band 里的 affine hyperplane。例如 `jacobi-1d-imper` 会出现：

```text
-32*fk1+2*t+i >= 0
32*fk1-2*t-i+31 >= 0
```

这编码的是：

```text
fk1 = floor((2*t + i) / 32)
```

因此 tiling validator 的目标不是“这两个 program 的 schedule 是否等价”，而是：

- after program 是否是 before program 的一个合法 tile lifting

## 2. validate 的输入到底应该是什么

## 2.1 最小输入：两份 program

理论上，最小输入仍然可以是：

- `before.scop`
- `after.scop`

因为 Pluto 把 tiling 的见证已经编码进了 `after.scop`：

- 新增 iterators
- link constraints
- access relation 的扩张
- schedule/scattering 的增维

也就是说，tiling strategy 并不是语义上必须额外信任的输入；它可以从 after program 里反推出来。

## 2.2 更现实的输入：两份 program + 一个 witness

如果目的是做 verified checker，工程上更合理的是：

- `before.scop`
- `after.scop`
- `tiling witness`

但这里的 witness 不是“额外信任的策略”，而是：

- 一个可以由优化器输出、再由 checker 重新校验的辅助证据

建议的 witness 形状：

1. statement correspondence
   - 每个 after statement 对应哪个 before statement
2. iterator lift graph
   - 哪些是新增 tile iterators
   - 每个 tile iterator 对哪个 affine hyperplane 做了 floor 关系
3. tile sizes
   - 例如 `fk3 = floor(i/32)` 或 `fk1 = floor((2*t+i)/32)`
4. statement-local offsets
   - 例如 `fk1 = floor((2*t+i+1)/32)` 里的 `+1`
5. schedule placement
   - 哪些 scattering 维是 tile-space，哪些是 point-space

这样做好处是：

- Pluto 实现可以直接把内部 band/tile 信息吐出来
- checker 不必从原始矩阵里做太多复杂猜测
- 即便 witness 是错的，checker 也能拒绝

## 2.3 当前原型的选择

这次先做的 standalone prototype 用的是“最小输入”路线：

- 输入只有 before/after 两份 OpenScop
- witness 由工具从 after domain 里自动推断

原因是先验证思路是否可行。

## 3. 正确性应该证明什么

对单个 statement 而言，最小的 tiling correctness obligations 是五条。

## 3.1 Base-domain preservation

after domain 中，去掉所有新增 tile iterators 后，必须还能找到一份与 before domain 一致的 lifted rows。

直观上就是：

- before 的原始 point-domain 约束没有丢

## 3.2 Tile-link soundness

after domain 中，所有含新增 iterator 的额外约束，都必须能解释成标准 floor-link：

```text
phi(x) - T * parent >= 0
-phi(x) + T * parent + (T - 1) >= 0
```

也就是：

```text
parent = floor(phi(x) / T)
```

这个条件一旦成立，就能推出：

- tile iterator 不是新的自由语义变量
- 它只是某个 affine hyperplane 的确定性编码

## 3.3 Coverage

对 before domain 中的每个原始 point instance，都能按这些 floor-link 唯一算出一组 tile iterator，使之落在 after domain 中。

这是“不会漏点”。

## 3.4 Uniqueness

同一个原始 point instance 不会对应多组不同的 tile iterator 值。

对标准 floor-link 来说，这可以从 link 约束本身推出。

这是“不会重复执行”。

## 3.5 Access preservation

after access relation 在去掉新增 tile iterator 输入列之后，应当与 before access relation 一致，并且 after access 不应该直接依赖新增 tile iterators。

这保证：

- tiling 没有改变 statement 对数组元素的读写语义

## 4. schedule 正确性怎么处理

这里只分两层。

### 4.1 tiling-specific correctness

上面五条义务，只负责证明：

- after program 和 before program 的 instance space 等价

### 4.2 schedule legality

光有 instance-space 等价还不够；还要证明 after schedule 仍合法。

这部分有两个可能路线：

1. 直接在增维后的 after program 上重新做 dependence preservation 检查。
2. 先把 after tiling 结果 normalize 成“原 point-domain + richer schedule constraints”，再复用现有 schedule validator。

第二条路线和 `libpluto` 里的：

- `/pluto/lib/plutolib.c:223-257`

非常一致，所以我认为更值得优先探索。

## 5. 这意味着 checker 的整体分解

一个完整的 tiling validator 更像下面这种组合：

```text
tile_validator(before, after) =
  check_statement_correspondence
  + check_domain_lifting
  + check_tile_links
  + check_access_preservation
  + check_schedule_legality
```

而不是把所有事情都硬塞进原有 scheduling validator。

## 6. 这次实现的 standalone prototype

工具路径：

- [validate_pluto_tiling.py](/home/hugh/research/polyhedral/polcert/tools/validate_pluto_tiling.py)
- [extract_pluto_tiling_witness.py](/home/hugh/research/polyhedral/polcert/tools/extract_pluto_tiling_witness.py)
- [check_pluto_tiling_witness.py](/home/hugh/research/polyhedral/polcert/tools/check_pluto_tiling_witness.py)

当前雏形已经拆成三层：

1. `validate`
   - 直接做 `extract + check`
2. `extract`
   - 从 `before/after.scop` 推断 tiling witness
3. `check`
   - 用显式 witness 去检查 `before/after.scop`

除此之外，现在还有一条 host-side 的 standalone OCaml 路径：

- [README.md](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/README.md)
- [tiling-witness-schema.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/tiling-witness-schema.md)

它不依赖 container 里的 `polopt`，而是把同一个边界单独落成：

1. `extract`
2. `check`
3. `validate = extract + check`

### 当前实现了什么

1. 解析 before/after OpenScop
2. 为每个 statement 提取 witness：
   - 原 iterators
   - tiled iterators
   - added iterators
   - affine floor-link tile links
3. 对每个 statement 检查：
   - after iterators 是否以 before iterators 为后缀
   - before domain 是否完整保留为 lifted rows
   - 额外 domain rows 是否都能配对成 affine floor-link
   - 每个新增 tile iterator 是否恰好作为一个 tile parent 出现
   - access relation 去掉新增 iterator 列之后是否与 before 一致
   - scattering 至少在 arity 上是合理扩张的
4. 如果提供显式 witness，还会检查：
   - witness 中的 iterators 和 tile links 是否与实际 after-domain 匹配
5. 在给定参数赋值时，对 before 中的所有 point instances 做 bounded coverage 检查：
   - 逐点计算 tile iterators
   - 验证 lift 后的点确实满足 after domain
6. 现在还有一个可本地编译的 standalone OCaml checker：
   - `cd tools/tiling_ocaml && dune build pluto_tiling_ocaml.exe`
   - 最小 fixture 上 `extract / validate / check` 都已跑通
   - 修改 witness 中的 `tile_size` 后会明确 `FAIL`

### 它没有实现什么

1. 没有做完整 schedule legality 证明
2. 没有支持 ISS
3. 没有支持并发语义
4. 目前只覆盖 Pluto 风格的 affine floor-link tiling 约束
5. 对 after iterators 的形状有较强假设：
   - after iterators 以 before iterators 为后缀

## 7. 原型试跑结果

我已经用 container 里的真实 Pluto 输出跑过这个 prototype，至少下面两类都能通过：

### 7.1 一级 tiling

样例：

- `/pluto/test/matmul.c`

命令：

```sh
pluto --silent --dumpscop --tile --parallel --nointratileopt \
  --nounrolljam --noprevector --nodiamond-tile /tmp/matmul.c
python3 tools/validate_pluto_tiling.py \
  /tmp/matmul.beforescheduling.scop \
  /tmp/matmul.afterscheduling.scop \
  --check-bounded-coverage \
  --param M=8 --param N=8 --param K=8
```

prototype 推断出的 tile links 是：

```text
fk0 = floor(i / 32)
fk1 = floor(j / 32)
fk2 = floor(k / 32)
```

并且：

- base-domain preservation 通过
- access preservation 通过
- bounded coverage 在 `8 x 8 x 8 = 512` 个点上通过

### 7.2 二级 tiling

样例：

- `/pluto/test/matmul.c` + `--second-level-tile`

命令：

```sh
pluto --silent --dumpscop --tile --parallel --second-level-tile \
  --nointratileopt --nounrolljam --noprevector --nodiamond-tile /tmp/matmul2.c
python3 tools/validate_pluto_tiling.py \
  /tmp/matmul2.beforescheduling.scop \
  /tmp/matmul2.afterscheduling.scop \
  --check-bounded-coverage \
  --param M=8 --param N=8 --param K=8
```

prototype 推断出的 tile links 是：

```text
fk0 = floor(fk3 / 8),  fk3 = floor(i / 32)
fk1 = floor(fk4 / 8),  fk4 = floor(j / 32)
fk2 = floor(fk5 / 8),  fk5 = floor(k / 32)
```

也就是：

```text
fk0 = floor(i / 256)
fk1 = floor(j / 256)
fk2 = floor(k / 256)
```

同样：

- base-domain preservation 通过
- access preservation 通过
- bounded coverage 在 `512` 个原始点上通过

### 7.2b `extract/check` split 已经跑通

本轮还额外跑了：

```sh
python3 tools/extract_pluto_tiling_witness.py \
  /tmp/matmul.beforescheduling.scop \
  /tmp/matmul.afterscheduling.scop \
  --json > /tmp/matmul.tiling.witness.json

python3 tools/check_pluto_tiling_witness.py \
  /tmp/matmul.beforescheduling.scop \
  /tmp/matmul.afterscheduling.scop \
  /tmp/matmul.tiling.witness.json \
  --check-bounded-coverage \
  --param M=8 --param N=8 --param K=8
```

以及一个错误 witness 负例：

```text
fk0 = floor(i / 31)
```

checker 会明确拒绝，并报告：

- `witness tile links do not match inferred tile links`

这说明当前雏形已经不是“只要 after.scop 合法就总是通过”，而是在真正校验 witness。

### 7.3 skewed / wavefront-friendly tiling

样例：

- `/pluto/test/jacobi-1d-imper.c`

命令：

```sh
pluto --silent --dumpscop --tile --parallel --nointratileopt \
  --nounrolljam --noprevector --nodiamond-tile /tmp/jac1.c
python3 tools/validate_pluto_tiling.py \
  /tmp/jac1.beforescheduling.scop \
  /tmp/jac1.afterscheduling.scop \
  --check-bounded-coverage \
  --param T=8 --param N=8
```

prototype 推断出的 tile links 是：

```text
statement 1:
fk0 = floor(t / 32)
fk1 = floor((2*t + i) / 32)

statement 2:
fk0 = floor(t / 32)
fk1 = floor((2*t + i + 1) / 32)
```

这说明 validator 不能把 tiling 理解成：

- “单个 iterator 被切成 tile iterator + point iterator”

更准确的理解应该是：

- “某个 affine schedule hyperplane 被 tile iterator 编码”

### 7.4 diamond tiling

样例：

- `/pluto/test/jacobi-1d-imper.c` + `--diamond-tile`

命令：

```sh
pluto --silent --dumpscop --tile --parallel --nointratileopt \
  --nounrolljam --noprevector --diamond-tile /tmp/jac2.c
python3 tools/validate_pluto_tiling.py \
  /tmp/jac2.beforescheduling.scop \
  /tmp/jac2.afterscheduling.scop \
  --check-bounded-coverage \
  --param T=8 --param N=8
```

prototype 推断出的 tile links 是：

```text
statement 1:
fk0 = floor((2*t - i) / 32)
fk1 = floor((2*t + i) / 32)

statement 2:
fk0 = floor((2*t - i + 1) / 32)
fk1 = floor((2*t + i + 1) / 32)
```

这进一步说明：

- diamond tiling 仍然能落在“affine floor-link witness”这个框架里
- 但被 tile 的对象已经明显是 skew 后的 hyperplane，而不是原始 loop index
- 因此这里不该被概括成“默认 affine 再 ordinary tiling”
- 更准确地说，应当是“diamond-aware affine midpoint，再 ordinary tiling”

这也是当前设计上最重要的分界：

- sequential correctness:
  - 仍然可以复用 ordinary affine floor-link tiling 关系
- stronger paper-level claims:
  - 还需要单独记录 concurrent-start face、tile schedule 方向、以及可能的
    tile-size ratio 约束

### 7.5 一个重要修正：不要把 before/after scattering arity 直接对齐

原型第一次试跑时，domain 和 access 都已经通过，但 `schedule_sanity` 失败了。原因不是 tiling 设计错，而是我一开始把下面这个假设写得太强：

- after scattering 的输出维数，至少应该是 `before scattering output dims + added tile iters`

这对 Pluto 不成立。`before.scop` 里的 scattering 往往是 source-like 的：

```text
(0, i, 0, j, 0, k, 0)
```

而 tiling 后，Pluto 可能直接把它压成：

```text
(fk0, fk1, fk2, i, j, k)
```

也就是：

- 输出维可能变少
- 但输入维会与 after-domain iterator 数对齐

所以当前原型只把 scattering 当作：

- arity / shape sanity check

而不把它当作完整 schedule correctness 证明的一部分。

## 8. 我对输入设计的结论

当前阶段，我的结论是：

- 从语义上说，tiling validation 的输入不一定需要额外“信任” tiling strategy
- 只用 before/after 两份 program，就已经足够恢复一个可检查的 tiling witness
- 这个 witness 的核心对象不应当是“哪个原 iterator 被 tiled”，而应当是“哪些 affine hyperplanes 被 tiled”

但从 verified engineering 的角度，更推荐的接口是：

```text
before_poly + after_poly + tiling_witness
```

其中：

- `before/after.scop` 只是 carrier / importer 输入
- witness 可以由 Pluto `after.scop` 恢复
- verified checker 的真实目标应当是 `PolyLang` 级别的 before/after 程序对象

也就是说，更准确的分层应当是：

```text
before.scop/after.scop
  -> untrusted importer / witness extractor
  -> before_poly/after_poly + tiling_witness
  -> verified tiling checker on PolyLang
```

这样后续做 Coq 证明时，结构才和现有 `Validator` 的真正边界一致。

## 9. OCaml `polopt` driver prototype

在 Python prototype 之后，我又把同一思路落了一版最小 OCaml 原型，并直接接进了 container 内真实的 `polopt` driver。

代码落点：

- `gifted_curie:/polcert/syntax/PlutoTilingValidator.ml`
- `gifted_curie:/polcert/syntax/SLoopMain.ml`

目前新增的实验入口是：

```sh
./polopt --extract-tiling-witness-openscop before.scop after.scop
./polopt --validate-tiling-openscop before.scop after.scop
```

现在的 OCaml 主路径已经显式拆成三层：

1. `extract_witness_from_files`
2. `check_witness_files`
3. `validate_files = extract + check`

也就是说，witness 不再只是脑中的概念；它已经是 driver 里的显式对象。

其中：

- `--extract-tiling-witness-openscop`
  - 只打印恢复出的 witness
- `--validate-tiling-openscop`
  - 先 extract witness，再 check witness

checker 当前做的是：

1. 用现有 `OpenScopReader` 读入两份 OpenScop
2. 从 statement body extension 恢复 iterator 列表
3. 用 witness 检查：
   - base-domain preservation
   - affine floor-link pairing
   - access preservation
   - scattering arity sanity
4. 打印一份 statement-level report，而不是只给布尔值

### 9.1 已经实际跑通的 tiling 家族

我在 container 里用真实 Pluto 输出跑过下面四类：

1. basic tiling
   - `matmul.c`
   - PASS
2. second-level tiling
   - `matmul.c --second-level-tile`
   - PASS
3. skewed tiling
   - `jacobi-1d-imper.c --tile --noparallel --nodiamond-tile`
   - PASS
4. diamond tiling
   - `jacobi-1d-imper.c --tile --diamond-tile --parallel`
   - PASS

代表性恢复结果：

- basic tiling:
  - `fk0 = floor(k / 32)`
  - `fk1 = floor(j / 32)`
  - `fk2 = floor(i / 32)`
- second-level tiling:
  - `fk0 = floor(fk3 / 8)`
  - `fk3 = floor(k / 32)`
- diamond tiling:
  - `fk0 = floor((2*t - i) / 32)`
  - `fk1 = floor((2*t + i) / 32)`

这里的 PASS 要小心解读。

它只说明：

- diamond case 的 sequential floor-link / witness reconstruction 可以通过

它不说明：

- concurrent start 已被验证
- load balance 已被验证
- parallel optimality 已被验证
- 论文里的 tile-size-ratio 条件已经被检查

### 9.2 过程中暴露出的一个额外缺口

要让 `polopt` 真正能读 Pluto 的 diamond-tiled `after.scop`，只加 validator 还不够。

我还需要补一个现有 parser 缺口：

- `gifted_curie:/polcert/lib/OpenScopParser.mly`

原因是当前 grammar 原本不能消费 Pluto 生成的 `<loop> ... </loop>` global extension。这个缺口在普通 tiling 上不一定暴露，但在带 diamond/parallel annotation 的输出上会直接让 `OpenScopReader` 报 syntax error。

这次原型里做的处理是：

- 让 parser 至少能跳过 `<loop>` extension
- 目前把它当作 ignored global extension 读过去

这一步虽然不是 tiling correctness 本身，但它是支持更强 tiling 结果进入 validator 的必要前置条件。

## 10. 对 Coq 落地的直接启示

今天这版 OCaml 原型进一步说明：

1. witness-first 路线是对的
   - validator 的核心不是“比较两个 schedule”
   - 而是“检查 floor-link lifting witness”
2. second-level tiling 需要 witness 支持依赖顺序
   - 例如 `fk0` 可以依赖更后面恢复出的 `fk3`
3. diamond tiling 的本质仍然是 affine hyperplane floor-link
   - 只是 `phi(x)` 变成了 `2*t-i` 或 `2*t+i`
4. 现有 `EqDom` 路线不能直接扩出这些能力
   - 因为它在接口层就要求 depth/domain/access 基本不变

如果要把这些 prototype-level 观察真正收口到当前 verified
`before -> mid -> after` 管线，后续应该以这份设计 note 为准：

- [second-level-and-diamond-design.md](./second-level-and-diamond-design.md)

它进一步固定了两件事：

- second-level 的核心是 dependency order 加 raw-order 到 canonical-order 的导入桥
- diamond 的核心是显式暴露 pre-tiling affine midpoint，而不是发明新的 tiling relation

还有一个这轮更明确的修正：

- OpenScop 不是最终 proof target
- 它只是 Pluto 结果进入 `PolyLang` 的 carrier
- 真正该被验证的是 `PolyLang.PolyInstr` 上的 tiling-induced lifting relation
- 当前 `Validator` 的 `compose_pinstr_ext` 只允许 schedule 变化，所以 tiling 需要新 validator 路线，而不是给现有 schedule-only validator 打补丁

### 10.1 当前 Coq 入口已经对齐到 checker 的哪一层

`gifted_curie:/polcert/src/TilingWitness.v` 现在已经不只是 “`floor(phi/T)` 有区间性质”。

它目前编过并覆盖了：

- affine expression evaluation
- tile-parent computation by Euclidean division
- one-link interval soundness
- ordered link traces
- lifted-point suffix property
- statement-level witness packaging
- lower/upper tile-link row semantics
- lifted base-row preservation
- lifted access-row preservation
- a packaged statement-level core soundness theorem

最关键的新点是：

- Coq 里已经定义了 tile-link 生成的 lower/upper row obligations
- 并证明了 ordered link evaluation 产生的每一步 trace 都满足这些 row obligations

这意味着当前 proof target 已经开始和 OCaml checker 对齐，但这个对齐应当落在 `PolyLang`：

- OCaml 当前通过 OpenScop 在恢复 witness 和候选 after-program
- Coq 已经能表达并证明 `PolyLang` statement 级别的 witness/lifting core
- OpenScop matrix 本身更适合作为不可信 importer glue，而不是最终证明对象

所以下一步不该再回头证明 extractor 启发式，而应该继续往：

- `PolyLang.PolyInstr` 级别的 tiling relation
- witness well-formedness 与 importer 边界对接
- schedule legality 的后接方式

推进。

## 11. 当前更清楚的 proof target

到这一步以后，tiling proof target 已经可以更明确地写成：

```text
infer_witness(before, after) : untrusted
check_witness(before, after, witness) : to be verified
```

这里的关键不是把 extractor 做小，而是：

- 不把 raw OpenScop matrix pattern inference 塞进 Coq
- 把 verifier 的证明对象固定成 witness-checking relation
- 把 Python / container OCaml / host-side OCaml 共用的 witness schema 固定住

因此后面 Coq 最应该对齐的是：

- host-side standalone checker 的 `check`
- 或 container `polopt` 里同构的 `check`

而不是 “两份 scop 直接硬判” 这个 driver-facing 外壳。
