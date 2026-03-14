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
