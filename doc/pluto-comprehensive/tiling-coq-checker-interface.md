# Tiling Coq Checker Interface

这份文档不讨论 “怎么从 OpenScop 猜 witness”，只讨论 verified checker 本身应该长什么样。

它的作用是把当前已存在的：

- Python prototype
- container OCaml prototype
- host-side standalone OCaml checker
- `TilingWitness.v`
- `TilingRelation.v`

收敛成一个明确的 Coq proof-facing interface。

## 1. 总体分层

推荐的最终分层应该是：

```text
before.scop / after.scop
  -> untrusted import
  -> before_poly / after_poly / witness
  -> verified check_witness
  -> verified schedule legality (later)
```

这里故意把两件事拆开：

1. tiling lifting correctness
2. schedule legality

当前应该先证明第 1 件事。

## 2. Verified checker 的输入

proof core 的输入不该是 “两份 scop”，而该是：

```text
before_poly : PolyLang.t
after_poly  : PolyLang.t
witness     : tiling_witness
```

其中 `witness` 应当是 `PolyLang`-facing 的，不需要保留 OpenScop 路径字符串。

更细到 statement 级别时，接口应该像：

```text
before_pi : PolyLang.PolyInstr
after_pi  : PolyLang.PolyInstr
w        : pinstr_tiling_witness
```

## 3. 建议的 checker 结构

最自然的 checker 不是一个大函数，而是五个可组合的布尔检查：

```text
check_pinstr_shape
check_pinstr_links
check_pinstr_base_domain
check_pinstr_accesses
check_pinstr_transformation
```

然后组合成：

```text
check_pinstr_tiling before_pi after_pi w
```

program 级别再组合成：

```text
check_pprog_tiling before after ws
```

当前 executable 原型已经开始用这组名字对齐：

- host-side OCaml checker 里已经有：
  - `check_pinstr_shape`
  - `check_pinstr_links`
  - `check_pinstr_accesses`
  - `check_pinstr_schedule_sanity`
  - `check_pinstr_transformation_contract`
  - `check_pinstr_tiling`
- Python prototype 也已经对齐到同样的 phase 命名

另外，host-side OCaml `--json` 现在已经直接输出完整 phase report：

- `shape_ok`
- `transformation_contract_ok`
- `witness_match_ok`
- `base_domain_ok`
- `link_rows_ok`
- `access_ok`
- `compiled_relation_ok`
- `schedule_sanity_ok`
- `bounded_coverage_ok`

失败时也会输出结构化 error，而不是只打 stderr。

这里新加的 `compiled_relation_ok` 不是一个新的 primitive check，而是 proof-facing 的聚合位：

- `shape_ok`
- `transformation_contract_ok`
- `base_domain_ok`
- `link_rows_ok`
- `access_ok`
- 以及有显式 witness 时的 `witness_match_ok`

它的作用是把 executable checker 直接对齐到当前 Coq 里的 compiled relation 入口，而不是继续让上层靠手工合并多个布尔位。

## 4. 每个 statement checker 最少要检查什么

### 4.1 Shape

- `pi_instr` 不变
- `pi_depth` 正确增加
- `added_dims` 与 witness 一致

### 4.2 Link rows

- `after_pi.pi_poly` 包含 witness 诱导的 tile-link rows
- 每个 link 是标准 Pluto-style affine floor-link

这一层应该直接复用 `TilingWitness.v` 里已经存在的：

- ordered link trace
- lower/upper row soundness

### 4.3 Base-domain lifting

- `before_pi.pi_poly` 中的 source rows 在 inserted-after-env lifting 后出现在 `after_pi.pi_poly`

这一层应该对齐：

- `lift_base_row_after_env`
- `lift_base_row_after_env_sound`

### 4.4 Access lifting

- `pi_waccess / pi_raccess` 在 inserted-after-env lifting 后与 `after_pi` 一致

这一层应该对齐：

- `lift_access_row_after_env`
- `lift_access_row_after_env_sound`

### 4.5 Transformation lifting

这是当前最该继续补的地方。

当前 executable checker 已经先暴露了一个更弱、但方向正确的结构层：

- `transformation_contract_ok`

它检查的不是 `pi_transformation` 本身，而是 future theorem 需要的前提：

- `tiled_iterators = added_iterators ++ original_iterators`
- canonicalized link parent 顺序与 `added_iterators` 一致
- 每个 link 只依赖 original iterators 和更早恢复出的 tile parents

需要一个 theorem 形状大致是：

```text
lifted transformation evaluated on env ++ tiles ++ iters
= original transformation evaluated on env ++ iters
```

也就是把 `pi_transformation` 的 inserted-after-env lifting 接到真实 `Instr.instr_semantics` 入口。

## 5. 推荐的 soundness theorem 形状

statement 级 theorem 最自然的形状应当是：

```text
Theorem check_pinstr_compiled_relation_sound :
  check_pinstr_compiled_relation before_pi after_pi w = true ->
  tiling_rel_pinstr_structure_compiled before_pi after_pi w.
```

program 级 theorem 则应当是：

```text
Theorem check_pprog_compiled_relation_sound :
  check_pprog_compiled_relation before after ws = true ->
  tiling_rel_pprog_structure_compiled before after ws.
```

这里的 `tiling_rel_pinstr / tiling_rel_pprog` 应当比当前

- `tiling_rel_pinstr_structure`
- `tiling_rel_pprog_structure`

更强，但第一版 proof target 现在更适合先停在 compiled-structure relation。

## 6. 什么不应该进入第一版 theorem

第一版 theorem 不应该同时包含：

- witness extraction correctness
- OpenScop parser correctness
- schedule legality
- codegen correctness

否则 proof target 会重新膨胀回 “end-to-end from two matrices”，这正是当前架构想避免的。

## 7. 与当前 executable 原型的对应

当前 executable 世界已经有三条路径：

1. Python
2. container OCaml
3. host-side OCaml

它们现在都已经收敛到同一个核心边界：

```text
validate = infer + check
```

并且当前 `check` 已经多出一个与 transformation bridge 对齐的结构检查位：

```text
shape_ok
transformation_contract_ok
```

现在还额外多出一个与最新 Coq relation 边界对齐的聚合位：

```text
compiled_relation_ok
```

它表示：

- 当前 statement 已满足 compiled tiling relation 的结构性 contract
- 剩下未并入这一位的仍然是：
  - schedule sanity / legality
  - bounded coverage
  - 更高层的 program-wide assembly

另外，当前 executable 路径还已经固定了一个负例：

- second-level bad witness 中，如果 link 依赖不可解析
- witness import / canonicalization 会直接拒绝

这意味着当前 checker core 已经不仅能表达 “通过的形状”，也能表达 future theorem 需要排除的坏 witness 形状。

所以 Coq 最应该对齐的是：

```text
check
```

而不是：

```text
infer + check
```

## 8. 当前最自然的后续证明顺序

1. 完成 `pi_transformation` 的 inserted-after-env 语义桥
2. 把 `statement_tiling_core_sound` 接到 `tiling_rel_pinstr_structure`
3. 定义真正的 `tiling_rel_pinstr`
4. 证明 `check_pinstr_tiling_sound`
5. 再升到 `check_pprog_tiling_sound`
6. 最后才讨论 schedule legality 如何接回主线
