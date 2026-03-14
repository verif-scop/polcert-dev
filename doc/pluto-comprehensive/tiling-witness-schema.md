# Tiling Witness Schema

这份文档固定当前 tiling witness 的接口形状。

目的不是定义最终用户 API，而是固定后续验证和 Coq 对齐的中间层。

## 1. 顶层结构

当前 Python prototype 和 host-side standalone OCaml checker 共享同一个 witness JSON 形状：

```json
{
  "before": "...",
  "after": "...",
  "params": ["N", "T"],
  "statements": [ ... ]
}
```

字段含义：

- `before`
  - witness 产生时使用的 before program 路径
- `after`
  - witness 产生时使用的 after program 路径
- `params`
  - parameter 名字，按 importer 的顺序
- `statements`
  - statement-level tiling witness 列表

其中真正应该进入 verified checker 的核心是：

- `params`
- `statements`

`before` / `after` 更像 trace/debug 信息，不是语义核心。

## 2. Statement-level witness

每个 statement 当前的 JSON 形状是：

```json
{
  "statement": 1,
  "original_iterators": ["i", "j"],
  "tiled_iterators": ["ti", "tj", "i", "j"],
  "added_iterators": ["ti", "tj"],
  "links": [ ... ]
}
```

字段含义：

- `statement`
  - before/after 对应的 statement id
- `original_iterators`
  - before statement 的 iterator 名
- `tiled_iterators`
  - after statement 的 iterator 名
- `added_iterators`
  - 新增 tile iterators
- `links`
  - floor-link 列表

## 3. Tile link

每个 link 当前形状：

```json
{
  "parent": "ti",
  "tile_size": 32,
  "expr": {
    "var_coeffs": [["i", 1], ["j", -1]],
    "param_coeffs": [["N", 1]],
    "const": 0
  }
}
```

语义是：

```text
parent = floor(expr / tile_size)
```

这里 `expr` 是 affine expression，不限于原始 iterator。

所以它能覆盖：

- basic tiling：`floor(i / 32)`
- second-level tiling：`floor(fk3 / 8)`
- skewed tiling：`floor((2*t+i) / 32)`
- diamond tiling：`floor((2*t-i) / 32)`

## 4. 当前 checker 依赖的结构性不变量

当前 checker 没有要求 witness “漂亮”，但要求它满足下面这些结构条件：

1. `tiled_iterators` 以 `original_iterators` 为后缀
2. `added_iterators` 等于 `tiled_iterators` 的前缀增量
3. `links` 的 `parent` 恰好覆盖 `added_iterators`
4. `parent` 不出现在自己的 `expr` 里
5. `links` 必须经过 dependency-aware canonicalization，而不是简单按名字排序
6. `tile_size > 0`

第 5 条很关键，因为 second-level tiling 已经说明：

- link 之间不是无依赖集合
- 它们是一个有顺序的恢复过程

当前可执行路径里，这个 canonical order 现在已经被固定成：

- 每一步只允许依赖 original iterators 和更早恢复出的 tile parents
- 多个 ready link 同时存在时，再用稳定的字典序打破平局
- `added_iterators` 的顺序必须与 canonicalized `links` 的 parent 顺序一致

如果 raw witness 中的 links 根本无法 canonicalize，例如：

- 某个 second-level link 依赖一个不存在或尚未可用的 iterator

那么当前 import/check 路径会直接拒绝，而不是带着未解析依赖继续往下跑。

## 5. 当前三个执行路径的关系

目前至少有三条执行路径共享这个 schema：

1. Python prototype
2. container `polopt` 内的 OCaml prototype
3. host-side standalone OCaml checker

其中 host-side 和 Python 已经做过交叉互认：

- Python `extract` -> OCaml `check`：PASS
- OCaml `extract` -> Python `check`：PASS
- second-level synthetic fixture 也已经互认：PASS

这说明 schema 已经足够稳定，可以作为 proof-facing interface 使用。

## 6. 与 Coq 对象的对齐

当前 Coq 里已经有：

- `tile_link`
- `statement_tiling_witness`

还新起了：

- `pinstr_tiling_witness`
- `tiling_rel_pinstr_structure`
- `tiling_rel_pprog_structure`

所以后续对齐关系更像：

```text
JSON witness
  -> untrusted decode/import
  -> Coq statement_tiling_witness / pinstr_tiling_witness
  -> verified check_witness
```

proof 的重点不应该是 JSON parser，也不应该是 raw OpenScop matrix inference，而是：

- decoded witness 是否正确解释 before/after 的 tiled lifting

## 7. 推荐的下一步收口

后面如果要继续收敛接口，我建议按这个顺序做：

1. 把 `before` / `after` 从 proof core 里降级成 metadata
2. 给 `links` 增加显式 well-formedness 约束文档
3. 把 host-side OCaml 和 container OCaml 的 witness 序列化彻底统一
4. Coq 只证明 `check_witness`
