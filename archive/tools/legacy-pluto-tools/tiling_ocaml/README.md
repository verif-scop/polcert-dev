# Standalone OCaml Tiling Checker

这个目录放的是一个独立于 container `polopt` 的 host-side prototype。

目标不是替代 container 里的真实实现，而是把 tiling validation 的接口固定成：

1. `extract`
2. `check`
3. `validate = extract + check`

这样后续 Coq 只需要对齐 `check` 这一层。

当前 executable checker core 也已经显式收口成接近 future Coq theorem 的 phase 名字：

- `check_pinstr_shape`
- `check_pinstr_links`
- `check_pinstr_accesses`
- `check_pinstr_schedule_sanity`
- `check_pinstr_transformation_contract`
- `check_pinstr_tiling`

同时，statement report 现在还显式输出一个 proof-facing 聚合位：

- `compiled_relation_ok`

它表示当前 statement 已经满足 compiled tiling relation 的结构性 contract：

- shape
- ordered-link / transformation contract
- base-domain lifting
- link-domain rows
- access lifting
- 以及有显式 witness 时的 witness match

## 构建

```sh
cd tools/tiling_ocaml
dune build pluto_tiling_ocaml.exe
```

## 用法

```sh
_build/default/pluto_tiling_ocaml.exe extract before.scop after.scop
_build/default/pluto_tiling_ocaml.exe validate before.scop after.scop
_build/default/pluto_tiling_ocaml.exe check before.scop after.scop witness.json
```

支持的额外选项：

- `--json`
- `--check-bounded-coverage`
- `--param NAME=VALUE`

当前 `--json` 行为也已经对 proof-facing 需求做了收口：

- 成功时输出完整结构化 report
- 失败时输出结构化 `{ "ok": false, "error": ... }`

而不是只给一段渲染后的字符串。

## 当前边界

这个 prototype 只覆盖 Pluto-style affine floor-link tiling：

- base-domain preservation
- tile-link pairing
- access preservation
- compiled relation contract aggregation
- scattering arity sanity
- bounded coverage

它不覆盖：

- full schedule legality proof
- ISS
- parallel semantics / parallel codegen
- 非 Pluto 风格的 tiling 编码

## 最小 smoke fixture

`fixtures/basic_before.scop` / `fixtures/basic_after.scop` 是一个最小 tiled pair：

- `before`: 单 iterator `i`
- `after`: 新增 tile iterator `ti`
- witness: `ti = floor(i / 32)`

可以用它验证 standalone checker 本身的接口和负例拒绝行为。

另外还带了一个 second-level fixture：

- [second_level_before.scop](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/second_level_before.scop)
- [second_level_after.scop](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/second_level_after.scop)

它对应：

- `f1 = floor(k / 32)`
- `f0 = floor(f1 / 8)`

这个 fixture 的作用是固定一个关键事实：

- tiling witness 的 `links` 不能只按名字排序
- second-level tiling 需要 dependency-aware 的 canonical order

还带了一个 second-level bad witness：

- [second_level_bad_witness.json](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/second_level_bad_witness.json)

它故意让一个 link 依赖不存在的 iterator，用来验证：

- witness import / canonicalization 会拒绝不可解析的 link 依赖

## Design Prototype For Second-Level And Diamond

除了上面的 OpenScop-facing checker，这个目录现在还带了一个更小、更聚焦的
design prototype：

```sh
dune build design_validator_prototype.exe
_build/default/design_validator_prototype.exe fixtures/design/second_level_positive.json
```

它不是要替代 `pluto_tiling_ocaml.exe`。它的作用更窄：

- 专门实验 second-level 的 `raw after order -> canonical witness order`
  设计是否可行
- 专门实验 diamond 的 “必须显式暴露 pre-tiling midpoint” 设计是否足够把
  diamond 继续压回普通 affine floor-link tiling

### second-level fixtures

- [second_level_positive.json](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/design/second_level_positive.json)
  - 正例
  - raw added order 是 `[f0, f1]`
  - canonical witness order 是 `[f1, f0]`
  - prototype 会：
    - 按依赖顺序 canonicalize links
    - 推导 raw/canonical 之间的 added-dim permutation
    - 验证这个 permutation 足以把 raw schedule rows 重排到 canonical schedule rows
- [second_level_bad_cycle.json](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/design/second_level_bad_cycle.json)
  - 反例
  - 两个 link 互相依赖，无法拓扑排序
- [second_level_bad_schedule.json](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/design/second_level_bad_schedule.json)
  - 反例
  - link 依赖顺序本身没问题
  - 但 raw schedule rows 经 permutation 后对不上预期 canonical schedule

### diamond fixtures

- [diamond_positive.json](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/design/diamond_positive.json)
  - 正例
  - midpoint hyperplanes 显式给出 `2*t-i` 与 `2*t+i`
  - tile links 则只需证明自己匹配这些 midpoint hyperplanes
- [diamond_bad_no_midpoint.json](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/design/diamond_bad_no_midpoint.json)
  - 反例
  - 没有 midpoint，prototype 直接拒绝
- [diamond_bad_missing_hyperplane.json](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/design/diamond_bad_missing_hyperplane.json)
  - 反例
  - 给了 midpoint，但它不足以解释所有 tile links

### 一键实验

```sh
sh design_smoke.sh
```

当前 smoke 结果会验证下面这些结论：

- second-level 正例会恢复出 canonical order `[f1, f0]`
- second-level 的 cycle 反例会被拓扑排序阶段拒绝
- second-level 的坏 schedule 反例会在 raw/canonical schedule bridge 上被拒绝
- diamond 正例会被解释成：
  - checked affine midpoint
  - 加 ordinary affine floor-link tiling
- diamond 缺少 midpoint 或 midpoint 不足时都会失败
