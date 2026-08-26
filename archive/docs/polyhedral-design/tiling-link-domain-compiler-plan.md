# Tiling Link-Domain Compiler Plan

本笔记只讨论一个非常具体的问题：

- 如何把 `statement_tiling_witness` 里的 floor-link 信息
- 编译成 `PolyLang.Domain`
- 并证明这些 rows 在 lifted index 上成立

## 1. 当前已经解决到哪里

`TilingRelation.v` 现在已经在 container 里证明了：

- inserted-after-env `pi_transformation` 保持 `affine_product`
- lifted base-domain rows 在 `in_poly` 上保持
- lifted access rows 在 `exact_cell` 上保持
- lifted instruction semantics 可以回到 before-side 的 `pi_instr` / `pi_transformation`
- witness-derived link-domain compiler
  - `compile_link_domain_after_env_from`
  - `compile_link_domain_after_env`
- compiled link-domain 在 lifted index 上成立
  - `compile_link_domain_after_env_from_sound`
  - `compile_link_domain_after_env_sound`
- 如果 `ptw_link_domain` 与 compiled link-domain 一致，则 lifted index 落在 `pi_poly after`
  - `witness_matches_compiled_link_domain`
  - `tiling_rel_pinstr_structure_domain_lifted_compiled`
- 还新增了 compiled relation 入口
  - `compiled_pinstr_tiling_witness`
  - `tiling_rel_pinstr_structure_compiled`
  - `tiling_rel_pinstr_structure_compiled_domain_lifted`
  - `tiling_rel_pinstr_structure_compiled_domain_complete`
  - `tiling_rel_pinstr_structure_compiled_index_complete`
  - `tiling_rel_pinstr_structure_compiled_domain_iff`

所以现在剩下的自由黑盒已经不是 “link rows 能不能编译”，也不再是 “reverse direction 还没落下来”，而是：

- statement-level 的 compiled characterization 怎么装配到 list / whole-program 层
- 以及 executable checker 怎么接成真正的 compiled checker theorem

## 2. OpenScop raw row 到 `PolyLang.Domain` 的现成翻译

`PolyLang.from_openscop_domain'` 对 OpenScop 的不等式行做的是：

1. 原始 OpenScop 行次序：`iters ++ params ++ const`
2. 重排成 `params ++ iters`
3. 系数整体取反
4. 常数保持为 `const`

也就是如果 raw inequality 是：

```text
sum(iter_coeffs * iters) + sum(param_coeffs * params) + c >= 0
```

那么对应 `PolyLang.Domain` 约束是：

```text
(-- (param_coeffs ++ iter_coeffs), c)
```

其语义是：

```text
dot(index, -- (param_coeffs ++ iter_coeffs)) <= c
```

这和原始 `>= 0` 形式等价。

## 3. Witness 里 floor-link 的目标形态

对一个 tile link：

```text
parent = floor(phi(vars, params) / T)
```

它对应两条 Pluto-style inequality：

```text
phi(vars, params) - T * parent >= 0
T * parent - 1 - phi(vars, params) >= 0
```

`TilingWitness.v` 已经把这两条语义化成：

- `lower_link_row_holds`
- `upper_link_row_holds`

## 4. 需要编译的 Coq 对象

下一步应当在 Coq 里显式定义两层对象：

1. affine-row layer
   - `lower_link_affine_row_after_env`
   - `upper_link_affine_row_after_env`
2. domain-constraint layer
   - `compile_ge_affine_row_to_constraint`
   - 把上面的 affine row 编进 `PolyLang.Domain`

这里必须注意变量排布：

- `PolyLang` index 顺序是 `env ++ iters`
- tiled iterator 顺序是 `added ++ original`
- 单个 link 的 `phi` 只依赖
  - 更早的 added dims
  - original dims
  - env/params

所以编译时不能只做简单前缀补零；要显式插入：

- 当前 parent 的 `-T` / `+T`
- 更晚 added dims 的 `0`

## 5. 新增的 well-formedness 义务

当前 `pinstr_tiling_witness` 还缺两条 Coq-side contract：

1. `ptw_added_dims = length stw_links`
2. 所有 link 的 `ae_param_coeffs` 长度都等于环境维度

第一条已经在 `TilingRelation.v` 里有了：

- `wf_pinstr_tiling_witness`

第二条现在刚起了一个更接近最终形态的 predicate：

- `wf_statement_tiling_witness_with_param_dim`

## 6. 下一轮 proof 应该怎么切

最自然的顺序是：

1. 先证明
   - `compile_ge_affine_row_to_constraint_sound`
   这一层已经编过
2. 再证明单条 link 的 lower/upper affine row 在 lifted index 上成立
3. 再把单条 row proof 升成整条 `link_domain`
4. 再把 compiled `link_domain` 接回 `tiling_rel_pinstr_structure`
5. 最后决定 relation 层是不是要删掉自由的 `ptw_link_domain`

这样可以避免一开始就把：

- list 级 trace
- domain concatenation
- witness well-formedness

全混到一个 theorem 里。

## 7. 本轮实际推进

container 里的 [TilingRelation.v](/polcert/src/TilingRelation.v) 现在已经新增并编过：

- `lower_link_constraint_after_env`
- `upper_link_constraint_after_env`

同时 [TilingWitness.v](/polcert/src/TilingWitness.v) 也新增并编过了两个更贴近当前阻塞点的 helper：

- `dot_product_cons_singleton`
- `dot_product_split_firstn_skipn`

也就是说，link-domain compiler 的对象层已经不是口头计划，而是已经开始落成 Coq definition。

本轮的主要变化是：

- single-link lower/upper row soundness 已经编过
- 递归 link-domain compiler theorem 已经编过
- wrapper theorem 也已经编过，但它明确暴露出一个必要接口条件：
  - `List.length point = stw_point_dim w`
- reverse theorems 现在也已经编过：
  - `compile_link_domain_after_env_from_complete`
  - `compile_link_domain_after_env_complete`
  - `tiling_rel_pinstr_structure_compiled_domain_complete`
  - `tiling_rel_pinstr_structure_compiled_index_complete`
- statement-level 上现在还有一个更适合后续引用的封装：
  - `tiling_rel_pinstr_structure_compiled_domain_iff`
- program/list 层也已经有了第一层选择接口：
  - `tiling_rel_pinstr_list_compiled_nth`
  - `tiling_rel_pprog_structure_compiled_nth`
  - `tiling_rel_pprog_structure_compiled_domain_iff_nth`
  - `tiling_rel_pprog_structure_compiled_transformation_lifted_nth`
  - `tiling_rel_pprog_structure_compiled_waccess_lifted_nth`
  - `tiling_rel_pprog_structure_compiled_raccess_lifted_nth`
  - `tiling_rel_pprog_structure_compiled_instr_semantics_lifted_iff_nth`
  - `tiling_rel_pprog_structure_compiled_effects_nth`
  - `compose_tiling_pinstr_ext`
  - `compose_tiling_instr_point_ext`
  - `tiling_rel_pinstr_structure_compiled_old_schedule_lifted`
  - `tiling_rel_pprog_structure_compiled_old_schedule_lifted_nth`
  - `tiling_rel_pprog_structure_compiled_belongs_to_ext_nth`

所以结论已经不是“卡在 lower/upper row proof”或者“卡在 reverse direction”，而是：

- compiler definitions 已经稳定
- link-domain soundness 也已经稳定
- statement-level compiled-domain characterization 已经闭合
- list / program 的 statement-selection 入口也已经落下来了
- `pprog` / `nth` 层的 statement-local effect bridge 也已经打包完成
- schedule gap 也已经收口成一个具体对象：
  - after-domain 上的 retiled old schedule vs new schedule
  - 而不是抽象的 “whole-program 还差一点”
- 现在真正的设计决策点是 schedule-aware whole-program semantics / checker theorem，而不是 list algebra

所以当前最合理的下一步仍然是：

1. 用现在这组 `pprog`/`nth` effect theorem 去隔离并处理 schedule-aware whole-program semantics gap
2. 把这层对象边界接到 OCaml checker / future extracted checker 上
3. 再决定显式 `ptw_link_domain` relation 是否还值得保留为辅助接口
