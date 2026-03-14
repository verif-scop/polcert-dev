# Formalization Status

本文件只记录当前形式化边界，不讨论将来怎么扩。

## 1. 当前主线已经覆盖什么

当前已证明主线，本质上仍然是：

- 顺序语义
- affine scheduling / reordering
- 再经现有 codegen 降成顺序 loop

更准确地说，现有证明路径擅长处理的是：

1. statements 不拆分
2. iteration domain 不扩张
3. 只更换合法 affine schedule/scattering

这与当前 `polcert` 实际使用 Pluto 的 flag 集一致：

```sh
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
  --smartfuse --nounrolljam --noparallel --notile --rar
```

## 2. 当前还没有进证明主线的三类核心能力

### 2.1 Tiling

包括：

- 普通 tiling
- second-level tiling
- diamond tiling
- 以及 tiling 后的 intra-tile 相关变换

它们的问题不只是“schedule 变了”，而是：

- domain 变了
- iterator 变多了
- access relation 输入维也跟着变

所以它们不是当前 schedule validator 能直接吃的对象。

### 2.2 ISS

ISS 的问题不是“实例顺序重排”，而是：

- statement/domain splitting

因此它需要 one-to-many statement 映射的语义，而不是一一对应的 statement validator。

### 2.3 Parallel

parallel 缺的其实是两层：

1. polyhedral 调度层
   - `parallel + notile` 会产生 wavefront/pipelined schedule
   - `tile + parallel` 会产生 tile-space parallel schedule
2. codegen 层
   - 要把这些 loop 真正降成 `#pragma omp parallel for`
   - 当前形式化里还没有并发 loop 语义

## 3. 现有语义为什么还不够

当前证明文档里能直接看到，主线仍然围绕：

- `PolyLang.instance_list_semantics`
- `PolyLang.semantics`
- `Loop.semantics`

例如：

- [FOUNDATIONS.md](/home/hugh/research/polyhedral/polcert/proof/extractor/FOUNDATIONS.md:81) 把 extractor 正确性目标写成 `poly instance-list semantics` 精化/模拟 `Loop.semantics`
- [CODEGEN_ALIGNMENT_PLAN.md](/home/hugh/research/polyhedral/polcert/proof/polopt/CODEGEN_ALIGNMENT_PLAN.md:36) 也明确把 `CodeGen.v` 的主 theorem 放在 `PolyLang.semantics` 之上

这套语义是顺序 loop 语义，不包含并发执行模型。

## 4. 所以当前分解现状可以记成一句话

当前主线已经支持：

- sequential affine rescheduling

当前主线还没有支持：

- tiling
- ISS
- parallel semantics / parallel codegen

## 5. 推荐的后续分解

如果后面要继续推进，最自然的分解是：

1. 先把 `parallel + notile` 当作 richer schedule 来处理
2. 再把 tiling 当作 domain augmentation 来处理
3. 再把 ISS 当作 splitting equivalence 来处理
4. 最后再把真正的 parallel-for codegen 接到并发语义上

## 6. 当前 tiling 进展

到现在为止，tiling 已经有了两个新的落点：

1. Python standalone prototype
   - witness extraction + checking
2. OCaml `polopt` driver prototype
   - `./polopt --extract-tiling-witness-openscop before.scop after.scop`
   - `./polopt --validate-tiling-openscop before.scop after.scop`
3. host-side standalone OCaml checker
   - [README.md](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/README.md)
   - `extract / check / validate`
   - 在最小 tiled fixture 上已经本地编译并跑通
   - 篡改 witness 后也会明确拒绝
   - Python / OCaml witness 交叉互认也已通过

第二条路径已经在 container 里用真实 Pluto 输出验证通过：

- basic tiling
- second-level tiling
- skewed tiling

## 7. 2026-03-11 新边界

这一轮把 `wf_pinstr` 的公共层和 affine-specific 层分开之后，又暴露出一个更本质的问题：

- 当前 generic `PolyLang` / `Validator` 把同一个 `pi_transformation` 同时用于
  - source instruction semantics
  - access/dependence validation

对 tiling 来说，这两种用途需要的 transformation 不是同一个对象：

- source/semantic 侧自然要的是 row-preserving lift
  - 从 `env ++ tiles ++ point`
  - 投影回 source 参数 `env ++ point`
- validator/affine 侧自然要的是 tiled-space view
  - 因为 lifted accesses 仍然生活在 tiled point-space 上

因此，这一轮已经在 [work/container-overlay/polcert/src/TilingRelation.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingRelation.v) 里把两层显式拆开了第一步：

- 现有 `tiling_rel_pinstr_structure`
  - 继续作为 checker/affine view
- 新增 `tiling_rel_pinstr_structure_source`
  - 作为 source/semantic view
- 新增 `source_view_of_tiled_pinstr`
- 新增并编过：
  - `tiling_rel_pinstr_structure_source_transformation_lifted`
  - `tiling_rel_pinstr_structure_source_instr_semantics_lifted_iff`

当前真正剩下的 blocker 不再是 row-lemma，而是：

- checked affine view
- source semantic view

之间缺一个 generic bridge。这个 bridge 目前不是 proof engineering 的小修能补上的；它已经触到 `PolyLang` / `Validator` 对 `pi_transformation` 单字段双重职责的建模边界。
- container-side Coq proof core 现在也新增了一层纯 helper file
  - [TilingList.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingList.v)
  - 目前承载 `skipn_eval_tile_links_suffix`
  - 这样把与 giant proof file 无关的 list lemma 从 [TilingRelation.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingRelation.v) 里抽了出来

## 7. 当前 left-layer 进展

`after -> retiled_old` 已经有 top-down theorem。  
`retiled_old -> before` 这层此前还是抽象 contract。

现在这层已经开始变成具体 theorem，而不是纯接口假设：

- `before_of_retiled_old_point_old_of_compose_tiling_instr_point_ext`
  已经在 container 的真实 `/polcert` 上重新证明并编过
- 新增了一个显式的 preimage theorem 雏形：
  - `tiling_rel_pprog_structure_compiled_before_point_has_retiled_old_preimage_nth`

它的作用是：

1. 从一个 before-side 合法点出发
2. 构造对应的 retiled-old point
3. 证明这个构造点确实属于 retiled-old statement
4. 再证明 `before_of_retiled_old_point` 会把它送回原来的 before point

这说明 left-layer 已经不再只是“应该能做 backward coverage”，而是已经开始落成具体的前像构造证明。
- diamond tiling

这说明 “tiling 先走 witness/lifting validator，而不是硬改当前 `EqDom`” 这条路线不仅在概念上合理，而且在现有实现栈上已经可执行。

更重要的是，主 OCaml 路径现在也已经显式拆成：

1. witness extraction
2. witness checking
3. validate = extract + check

这使得后续 Coq 目标可以更明确地对准第 2 层，而不是对准从 raw matrices 里恢复 witness 的启发式逻辑。

第三条 host-side 路径进一步加固了这个边界：

- 即使不依赖 container 里的 `polopt`
- witness-first 接口本身也已经能独立运行
- 所以后续 verified target 可以稳定收敛到 `check_witness`

## 7. 当前 Coq 入口的更具体版本

现在最合理的 Coq 顺序已经可以进一步收紧成：

1. formalize `tile_link` / `affine_expr`
2. formalize “根据 witness 计算 tile parent”
3. 证明 floor-link interval 性质
4. formalize statement-level lifting
5. 再接 domain / access preservation
6. 最后才考虑如何复用或替换现有 schedule legality validator

这比之前更具体的一点是：

- second-level tiling 已经说明 witness 需要支持 link 之间的顺序依赖
- diamond tiling 已经说明 witness 的 `phi(x)` 必须允许一般 affine hyperplane，而不是只允许原始 iterator

这也是为什么后面的设计工作应当先从 `tiling validation` 开始，而不是直接 formalize OpenMP。

最新的具体收敛点是：

- `gifted_curie:/polcert/src/TilingWitness.v` 已经编过 statement-level witness packaging
- 还额外编过了 tile-link lower/upper row semantics
- 还编过了 lifted base-row preservation
- 还编过了 lifted access-row preservation
- 还编过了 inserted-after-env lifting 版本
- 还新起了 `gifted_curie:/polcert/src/TilingRelation.v`
- 现在可以证明 ordered link trace 的每一步都满足其对应的 Pluto-style tile-link rows
- 现在也可以证明 before-domain row 前补零后，在 lifted point 上仍成立
- 现在也可以证明 access row 在 added tile inputs 处补零后，在 lifted point 上仍成立
- 现在还有一个 statement-level core theorem，把 link rows、base rows、access rows 合并到同一个 witness/lifting soundness 结果里
- 现在还有一个 PolyLang-side 结构关系入口：
  - `tiling_rel_pinstr_structure`
  - `tiling_rel_pprog_structure`
- 这些关系现在已经不只是“定义出来”：
  - `gifted_curie:/polcert/src/TilingRelation.v` 已经在 container 里编过
  - 已经证明 `pi_transformation` 的 inserted-after-env lifting 在语义上保持 `affine_product`
  - 已经证明 lifted base-domain rows 的 `in_poly` 语义保持
  - 已经证明 write/read access 的 `exact_cell` 在 inserted-after-env lifting 下保持
  - 已经证明基于 lifted index 的 `Instr.instr_semantics` 可回到 before-side 的 instruction/transformation 上
  - 已经把 `statement_tiling_witness` 编译成 witness-derived `link_domain`
    - `compile_link_domain_after_env_from`
    - `compile_link_domain_after_env`
  - 已经证明 compiled link-domain 在 lifted index 上成立
    - `compile_link_domain_after_env_from_sound`
    - `compile_link_domain_after_env_sound`
  - 已经证明如果 `ptw_link_domain` 与 compiled link-domain 一致，则 lifted index 落在 `pi_poly after`
    - `witness_matches_compiled_link_domain`
    - `tiling_rel_pinstr_structure_domain_lifted_compiled`
  - 现在还新增了 compiled witness / compiled relation 入口
    - `compiled_pinstr_tiling_witness`
    - `tiling_rel_pinstr_structure_compiled`
    - `tiling_rel_pinstr_structure_compiled_domain_lifted`
    - `tiling_rel_pinstr_structure_compiled_domain_complete`
    - `tiling_rel_pinstr_structure_compiled_index_complete`
    - `tiling_rel_pinstr_structure_compiled_domain_iff`
    - `tiling_rel_pinstr_structure_compiled_transformation_lifted`
    - `tiling_rel_pinstr_structure_compiled_waccess_lifted`
    - `tiling_rel_pinstr_structure_compiled_raccess_lifted`
    - `tiling_rel_pinstr_structure_compiled_instr_semantics_lifted_iff`
  - statement-level 的 compiled-domain 边界现在已经不是只有 forward lifting：
    - after-domain membership 可以反推出 canonical tile-link trace
    - 也可以反推出 before-domain membership
    - 现在已经有一个直接可引用的 characterization theorem：
      - `tiling_rel_pinstr_structure_compiled_domain_iff`
  - 还新增了 program-facing 的 statement selection 接口：
    - `tiling_rel_pinstr_list_compiled_nth`
    - `tiling_rel_pprog_structure_compiled_nth`
    - `tiling_rel_pprog_structure_compiled_domain_iff_nth`
    - `tiling_rel_pprog_structure_compiled_transformation_lifted_nth`
    - `tiling_rel_pprog_structure_compiled_waccess_lifted_nth`
    - `tiling_rel_pprog_structure_compiled_raccess_lifted_nth`
    - `tiling_rel_pprog_structure_compiled_instr_semantics_lifted_iff_nth`
    - `tiling_rel_pprog_structure_compiled_effects_nth`
  - 现在还把 schedule gap 收成了一个更具体的 ext-level 目标：
    - `retiled_old_pinstr`
    - `compose_tiling_pinstr_ext`
    - `compose_tiling_instr_point_ext`
    - `compose_tiling_pinstr_ext_as_compose_pinstr_ext`
    - `tiling_rel_pinstr_structure_compiled_old_schedule_lifted`
    - `tiling_rel_pprog_structure_compiled_old_schedule_lifted_nth`
    - `tiling_rel_pprog_structure_compiled_belongs_to_ext_nth`
    - `tiling_rel_pprog_structure_compiled_old_point_belongs_to_nth`
    - `tiling_rel_pprog_structure_compiled_new_point_belongs_to_nth`
  - 现在 ext-level route 又往前推进了一步：
    - 不再只停在单个 point 的 old/new membership
    - `gifted_curie:/polcert/src/TilingRelation.v` 现在已经能从 after-side flattened instance list 构造：
      - `retiled_old_ipl_from_after`
      - `compose_tiling_ipl_ext_from_after`
    - 并且这两条 list-level bridge 都已经编过：
      - `flatten_instr_nth_after_implies_flatten_instr_nth_retiled_old`
      - `flatten_instr_nth_after_implies_flatten_instr_nth_tiling_ext`
    - 这意味着 tiling proof 现在已经有一条 container-side 的 after-based route：
      - after flattened list
      - ext flattened list
      - old projection as retiled-old flattened list
    - 这条 route 很关键，因为它绕开了 “直接从 before lex index 顺序 map 到 tiled index 顺序” 的单调性问题
      - 尤其对 skewed / diamond tiling，这是更稳的 proof 入口
    - 现在还补上了 program-level list plumbing：
      - `retiled_old_pinstrs`
      - `compose_tiling_pinstrs_ext_from_after`
      - `nth_error_retiled_old_pinstrs`
      - `nth_error_compose_tiling_pinstrs_ext_from_after`
    - 这一步虽然还不是 whole-program semantics theorem，但它把后续 `flatten_instrs` 级组装需要的 list correspondence 接口先固定了
    - 现在又进一步编过了 whole-program flattened-list assembly：
      - `retiled_old_pinstrs_preserve_length`
      - `compose_tiling_pinstrs_ext_from_after_preserve_length`
      - `retiled_old_pinstrs_app_singleton`
      - `compose_tiling_pinstrs_ext_from_after_app_singleton`
      - `flatten_instrs_after_implies_tiling_ext_exists`
    - 这说明 proof 已经不只是 “某个 statement 的 lifted point 合法”
      - 而是已经能从 after-side whole-program flattened list
      - 组装出 whole-program 的 `ipl_old` 和 `ipl_ext`
      - 并保持 `old_of_ext_list` / `new_of_ext_list` 对齐
    - `tiling_rel_pprog_structure_compiled_new_point_belongs_to_nth`
  - 也就是说，在 `pprog` / `nth` 层面，除了 schedule ordering 之外的 statement-local effect 已经能统一打包：
    - domain characterization
    - transformation equality
    - write/read access preservation
    - instruction-semantics equivalence
  - 同时 schedule 缺口也不再是抽象口号：
    - 现在已经能在 after-domain 上显式构造 “retiled old schedule vs new schedule” 的 ext object
    - 也已经能把同一个 tiled point 同时解释成：
      - `retiled_old_pinstr` 的 old point
      - `after_pi` 的 new point
  - 现在还新增了一个真正编过的 top-down semantics bridge：
    - `tiling_after_to_retiled_old_poly_correct`
  - 它的证明形状已经明确是：
    - 输入 whole-program 的 `after` 语义
    - 通过 `flatten_instrs_after_implies_tiling_ext_exists` 组装整程序 ext witness
    - 再用 `stable_permut_ext_lists_are_equivalent` 把 `after` 语义送到 `retiled_old`
  - 这说明分解
    - `before <-> retiled_old <-> after`
    现在不只是设计草图，而是已经有一层真正落到 `PolyLang.poly_instance_list_semantics` 的 container-side theorem
  - 但这层 theorem 目前仍然带一个显式假设：
    - 对 assembled ext list，凡是 old-schedule 逆序而 new-schedule 非减的 pair，都满足 `Permutable_ext`
  - 所以它当前证明的是：
    - “只要 tiled schedule legality 能以这类 ext-level permutability 形式供给，`after -> retiled_old` 这层高层桥就是可证明的”
  - 现在最顶层的组合 theorem 也已经被明确对象化并编过：
    - `tiling_retiled_old_to_before_poly_layer`
    - `tiling_after_to_before_poly_correct_via_retiled_old`
    - `tiling_after_to_before_instance_correct_via_retiled_old`
  - 它们的意义不是“最终证明已经完成”，而是：
    - 最顶层 `after -> before` 已经被压成一个明确的组合接口
    - 剩下唯一没有 discharge 的大块，就是 `retiled_old -> before` 这层
    - 不再需要猜最终 theorem 应该长什么样
  - 也就是说，当前 top-level proof boundary 已经从
    - “一个模糊的 decomposition 设想”
    收紧成了
    - “一个已编译的 composed theorem，加上一个显式 left-layer contract”
  - 它还没有单独证明：
    - 这个 permutability 假设一定由某个 executable tiled-schedule checker 导出
    - `tiling_retiled_old_to_before_poly_layer` 的具体实现
    - 去掉 abstract layer 假设后的最终 end-to-end tiling correctness theorem
- `./polopt --validate-tiling-openscop` 也已在 container 里重新确认没有被这轮 Coq 工作破坏：
  - 对 `/tmp/tv_matmul.beforescheduling.scop` / `/tmp/tv_matmul.afterscheduling.scop` 仍然 `PASS`

所以当前最稳定的证明接口已经不是“裸的 division 性质”，而是：

- `before/after/witness` 中 witness 诱导出的 link rows
- lifted point / trace 满足这些 rows

这里还要加一个边界修正：

- OpenScop 更适合作为 Pluto 结果的 carrier / importer
- 真正该被验证的是 `PolyLang.PolyInstr` 上的 tiling-induced lifting relation
- 现有 `Validator.compose_pinstr_ext` 只允许 schedule 改变，所以 tiling 不会是当前 validator 的小扩展，而会是一条新的 PolyLang-side validator 路线

下一步应当继续补：

1. 处理真正剩下的 schedule / ordering gap
   - 当前 `pprog`-level theorem 已经覆盖了 statement-local effect
   - 还没有把这些结果接到 `poly_semantics` / `instance_list_semantics` 那条依赖 schedule 的整程序语义上
2. 把 executable checker 的 phase contract 接成真正的 checker soundness theorem
   - 当前 `compiled_relation_ok` 只是 executable aggregate
   - 还没有 Coq 里的 `check_* = true -> tiling_rel_*` theorem
3. 把 host-side / container-side checker 共用的 witness schema 固定下来
   - 当前文档入口：[tiling-witness-schema.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/tiling-witness-schema.md)
4. 把 witness well-formedness 跟 parser/import/export 边界对接
5. 再决定如何把 schedule legality 接回现有验证主线

而不是先去 formalize witness extraction 本身，也不是把 OpenScop matrix 直接当 proof target。

## New progress: retiled_old -> before flatten bridge

container 里的 `src/TilingRelation.v` 现在又多了一层已经编过的 whole-program bridge：

- `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm`
- `flatten_instrs_retiled_old_implies_before_exists_perm`

这两层的意义是：

- statement-level:
  - 不只是“存在一个 before chunk”
  - 还显式给出这个 chunk 与 local `before_of_retiled_old` 映射之间的 `Permutation`
- whole-program:
  - 不只是“能从 `retiled_old` 重新 flatten 出一个 `before` program”
  - 还显式给出这个 flattened `before` list 与 program-wide
    `before_ipl_from_retiled_old_pprog` 映射之间的 `Permutation`

配套补上的 proof plumbing 也已经编过：

- `Forall_nth_error`
- `Forall2_nth_error`
- `tiling_rel_pinstr_list_lengths`
- `tiling_rel_pprog_structure_compiled_lengths`
- `tiling_rel_pinstr_list_app_singleton_inv`
- `tiling_rel_pprog_structure_compiled_app_singleton_inv`
- `Forall2_app_singleton_inv`
- `instr_point_list_semantics_map_preserved`
- `HdRel_sched_map_time_stamp_preserved`
- `sorted_sched_map_time_stamp_preserved`

这改变了 left-layer 的状态：

- 之前：
  - 还缺 whole-program flatten/list assembly
- 现在：
  - flatten/list assembly 已经有 compiled theorem
  - 剩余缺口收缩成更高一层：
    - program-wide `before_of_retiled_old_pprog_point` 的 pointwise semantics bridge
    - program-wide time-stamp preservation
    - 用这两块 discharge `tiling_retiled_old_to_before_poly_layer`

所以现在离 concrete left-layer theorem 更近了，但还没结束：

- `tiling_retiled_old_to_before_poly_layer` 仍然是 abstract contract
- `tiling_after_to_before_poly_correct_via_retiled_old` 仍然依赖它
- 不过当前剩下的 proof debt 已经从“flatten assembly”上移到了“program-wide mapped semantics”上

## New progress: concrete checked tiling theorems

现在的状态已经进一步前移，不再停在上面这一节描述的边界。

新增加并已在 container 编过的层次有：

1. `src/TilingRelation.v`
   - `tiling_retiled_old_to_before_poly_correct_with_env_len`
   - `tiling_retiled_old_to_before_instance_correct`
   - `tiling_after_to_before_instance_correct_concrete`
   - `tiling_after_to_before_poly_correct_concrete`
2. `src/TilingBoolChecker.v`
   - `check_statement_tiling_witnessb_sound`
   - `check_pinstr_tiling_compiledb_sound`
   - `check_pinstr_list_tiling_compiledb_sound`
   - `check_pprog_tiling_compiledb_sound`
3. concrete driver instantiations
   - `driver/TPolOpt.v`
     - `tiling_validate_correct`
     - `tiling_checked_validate_correct`
   - `driver/CPolOpt.v`
     - `tiling_validate_correct`
     - `tiling_checked_validate_correct`

这意味着当前 tiling proof stack 已经可以表达成：

1. `check_pprog_tiling_compiledb before after ws = true`
2. `mayReturn (validate (retiled_old before after ws) after) true`
3. `after` semantics
4. 推出 `before` semantics

所以现在真正还没彻底 close 的，已经不是 top theorem 本身，而是更底层的两件事：

1. 这个 Coq bool checker 还没有证明成当前 OCaml `PlutoTilingValidator.ml` 的 soundness
2. witness extraction 仍然是 untrusted glue，而不是 verified extractor

当前边界因此已经收紧成：

- top theorem: 有
- checked theorem: 有
- Coq-side bool checker soundness: 有
- executable checker alignment: 还没有
- witness extraction verification: 还没有

## New progress: syntax-side checked pass theorem

现在不只是 `TPolOpt` / `CPolOpt` 两个具体实例有 checked theorem；实际 syntax/frontend
侧也有了同样形状的 Coq pass。

新增加并已在 container 编过：

- `syntax/STilingOpt.v`
  - `tiling_validate_correct`
  - `tiling_checked_validate_correct`
  - `checked_tiling_validate_correct`

其中 `checked_tiling_validate` 是一个真正的 executable Coq function：

1. 先跑 `check_pprog_tiling_compiledb before after ws`
2. 再跑 `Validator.validate (retiled_old before after ws) after`

因此 syntax-side 现在已经可以直接表述成：

1. `mayReturn (checked_tiling_validate before after ws) true`
2. `after` semantics
3. 推出 `before` semantics

这比之前那种“布尔 checker 定理 + validate 定理 + 顶层手动拼接”更接近最终独立 tiling
pass 的目标接口。

## New progress: concrete driver wrappers also closed

`driver/TPolOpt.v` 和 `driver/CPolOpt.v` 现在也不再只停在分离前提 theorem。

新增加并已编过：

- `driver/TPolOpt.v`
  - `checked_tiling_validate`
  - `checked_tiling_validate_correct`
- `driver/CPolOpt.v`
  - `checked_tiling_validate`
  - `checked_tiling_validate_correct`

所以当前三条 concrete instantiation 线：

- syntax / `SPolIRs`
- trace / `TPolIRs`
- C / `CPolIRs`

都已经有统一的 checked-pass theorem shape。

## New progress: modular extraction is viable, full rebuild is blocked elsewhere

为了把 Coq checker 接回真实 runtime，我额外做了 modular extraction 实验：

- `tiling_separate_extraction.v`

它已经成功生成：

- `extraction/STilingOpt.ml`
- `extraction/TilingBoolChecker.ml`
- `extraction/TilingRelation.ml`

这说明“把 proved checked pass 抽成 OCaml 模块”这条路线是通的，不需要继续依赖手写
checker 复制 Coq 逻辑。

但当前 container 里的完整 `make polopt` 重编还没有一起打通；它卡在一个更老的 extraction
兼容性问题上：

- `extraction/BinInt.ml` 导出的自定义 `Z` 模块缺少 `iter` 等 API
- `extraction/Zbits.ml`、`extraction/Initializers.ml`、`extraction/IEEE754_extra.ml`
  仍然在调用这些接口

所以当前状态应理解成：

- tiling proof core: 已经推进到 syntax-side checked pass theorem
- modular extraction: 已验证可生成
- full runtime replacement: 还差 extraction compatibility plumbing

## New progress: extraction compatibility repaired in `extraction.v`

这部分现在已经不是“还差 plumbing”，而是已经在正确层修掉了。

修复点只放在 extraction 脚本层：

- `extraction/extraction.v`
- `extraction/tiling_extraction.v`
- `tiling_separate_extraction.v`

没有去改 `extraction/*.ml` 生成物。

修复内容是给 `BinInt.Z` 显式补 extraction directives：

- `Z.pred`
- `Z.iter`
- `Z.odd`
- `Z.div2`
- `Z.log2`
- `Z.log2_up`

关键 engineering detail 是，directive 里的名字必须匹配这个项目当前 extraction
管线真正产出的 OCaml 命名：

- positive constructors:
  - `Coq_xH`
  - `Coq_xO`
  - `Coq_xI`
- positive helper module:
  - `Pos`
- booleans:
  - `true`
  - `false`

第一次修的时候，用了逻辑上自然但和当前 extraction naming 不一致的名字：

- `XH`
- `XO`
- `XI`
- `Coq_Pos`
- `True` / `False`

这会让 `make polopt` 在 OCaml 编译阶段失败。改成当前 naming 后，主构建路径已经验证通过：

- `opam exec -- make extraction`
- `opam exec -- make polopt`

并且 runtime sanity 仍然是绿的：

- `./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop`
  reports `overall: PASS`

所以现在 runtime 侧状态已经更新为：

- tiling proof core: 仍然 intact
- syntax-side checked pass theorem: intact
- modular extraction: viable
- extraction compatibility: fixed in the correct file
- full `polopt` rebuild: green again

## New progress: verified tiling gate is now wired into `polcert` / `polopt`

这一轮的关键进展不在 theorem inventory 本身，而在 **verified checker 的消费路径**。

### 1. `pi_transformation` relation 已经改成 padded 版本

runtime 上真正可工作的 tiled transformation 关系，不是最早那版：

- `lift_affine_function_after_env`

而是：

- 先做 column lift
- 再在 `env` 后插入新增 tile dims 的 identity rows

也就是现在的：

- `pad_transformation_after_env`

原因是现有 `Validator.check_wf_polyinstr` 要求：

- `length pi_transformation = env_dim + iter_dim`

row-preserving lift 在 tiled program 上不满足这一点。  
换成 padded transformation 之后，`check_pprog_tiling_compiledb` / `checked_tiling_validate`
这条 verified checker 路径才在 runtime 上真正对齐 Pluto 输出。

当前与 transformation 相关的 Coq theorem 还有一组暂时 `Admitted`：

- `tiling_rel_pinstr_structure_transformation_sound`
- `tiling_rel_pinstr_structure_transformation_lifted`
- `tiling_rel_pinstr_structure_instr_semantics_lifted_iff`
- `tiling_rel_pinstr_structure_compiled_transformation_lifted`
- `tiling_rel_pinstr_structure_compiled_instr_semantics_lifted_iff`
- `tiling_rel_pprog_structure_compiled_transformation_lifted_nth`

但定义层、checker 层、extraction 层已经切到正确形状。

### 2. `polcert` 现在已经消费 verified tiling checker

`polcert` 的 phase-aligned tiling path 现在走的是：

1. 读 `mid.scop` / `after.scop`
2. infer tiling witness
3. 用 witness 构 canonical tiled skeleton
4. 只从 raw `after.scop` 导 schedule 到 canonical skeleton
5. 跑 extracted `checked_tiling_validate`

另外还加了一步 runtime-side normalization：

- 给 `before/after` 同时补 `vars` 上界

这是为了满足现有 `Validator.check_wf_polyinstr` 的 well-formedness 上界检查：

- `env_dim + iter_dim`
- `poly_nrl`
- `schedule_nrl`

这一步不改变程序语义，只是把输入补到现有 verified checker 接受的形状。

当前已经在 container 里实际验证通过：

- `./polcert --kind tiling /tmp/matmul.mid.scop /tmp/matmul.after.scop`
- `./polcert --kind tiling /tmp/jac1.mid.scop /tmp/jac1.after.scop`
- `./polcert --kind tiling /tmp/matadd_mid.scop matadd_mid.scop.afterscheduling.scop`
- `./polcert /tmp/matadd_before.scop /tmp/matadd_mid.scop matadd_mid.scop.afterscheduling.scop`

这意味着：

- `polcert` 已经可以用 **verified tiling checker** 去验证 Pluto 实际产出的 phase-aligned `mid -> after`

### 3. `polopt` 也已经消费 verified tiling gate

`polopt` 的默认路径现在是：

1. affine-only Pluto
2. tile-only Pluto
3. affine validate(`before`, `mid`)
4. verified tiling validate(`mid`, `after`)

也就是说，它不再依赖 standalone tiling prototype 作为主 gate。

当前实测：

- `./polopt syntax/examples/matadd.loop`

已经不再触发 `checked fallback`，说明 verified tiling gate 本身已经接通。

### 4. syntax/codegen consumption 现已基本对齐

前一轮剩下的独立 runtime 问题，已经被进一步压成了一个明确的
representation split，并且当前 syntax examples 已经能生成正确的 tiled
body。

关键发现是：

- validator-side `pi_transformation`
  - 需要 padded transformation relation
  - 这是 verified tiling checker 当前真正消费的对象
- syntax/codegen-side `pi_transformation`
  - 不是 validator-side 那个对象
  - 它必须继续表示 source instruction arguments
  - 在 tiled program 上，它需要被 lift 到 tiled point space，而不是直接
    用 raw imported tiled identity rows

具体 runtime 症状曾经是：

- `matadd.loop`
  - gate 已经通过
  - 但 codegen 输出
    - `C[i0][0] = A[i0][0] + B[i0][0]`
  - 先说明 loop structure 有问题
  - 后说明 body/indexing 也在吃错 iterator

这次定位出的两个直接原因是：

1. syntax-side `vars` 上界太小

- `PrepareCodegen.prepare_codegen` 用 `cols = length vars`
- tiled syntax program 会出现：
  - `env_dim + depth = 6`
  - `length vars = 5`
- 于是 `resize_affine_list` 直接裁掉最后一列

2. codegen 不该消费 raw tiled `pi_transformation`

- raw imported `after` 在 tiled case 下给的是 tiled identity rows
- 这会让 codegen 用 tile iterators，而不是 point iterators
- 正确做法是：
  - 从 pre-tiling source transformation 出发
  - 做 row-preserving after-env lift
  - 让 transformed instruction arguments 继续保持原始的 `env ++ point`
  - 但这些值从 tiled point-space `env ++ tiles ++ point` 上读取

现在 syntax/codegen 已经做了两步修复：

- codegen 前补 syntax-side `vars`
- codegen 用 source-argument lifted transformation，而不是 raw tiled transformation

当前 container 实测：

- `./polopt syntax/examples/matadd.loop`
  - 现在输出 tiled body
    - `C[i2][i3] = (A[i2][i3] + B[i2][i3])`
- `./polopt syntax/examples/covariance.loop`
  - tiled body uses `data[i3][i4]` / `data[i3][i5]`
- `./polopt syntax/examples/covariance_outer.loop`
  - tiled body uses `data[i5][i3]` / `data[i5][i4]`

所以现在的 runtime 分层更清楚了：

- **verified tiling gate 已经接通**
- **syntax/codegen 侧也已经能在当前 syntax examples 上正确消费 validated tiled result**

当前剩下的 runtime caveat 主要是：

- `polopt` 仍然打印
  - `isl_map.c:12117: number of columns too small`
- 这个 warning 目前不阻断：
  - affine validate
  - tiling validate
  - 当前 syntax examples 的 tiled code generation
- 但它仍然值得后续单独清理

### 5. witness-centered migration 已进入真实代码

之前的 dual-transformation split 现在被明确降级成过渡状态。当前 overlay
里的真实迁移已经开始：

- [PointWitness.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PointWitness.v)
  - 现在承载 point-space witness 的等式判定和 projection helper
- [PolyLang.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PolyLang.v)
  - 已新增
    - `current_env_dim_of`
    - `current_base_point_of`
    - `current_src_args_of`
  - `poly_semantics` / `poly_semantics_k` / `poly_lex_semantics`
    已改为通过 witness 投影后的 source args 喂给
    `Instr.instr_semantics`
- [TilingRelation.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingRelation.v)
  - source-side relation 已改成 witness-centered：
    - `after.pi_point_witness = PSWTiling ...`
    - source-side transformation/access 保持 before-side 语义视图
  - source-side instruction-semantics theorem 现在围绕
    `PL.current_src_args_of`
- [TilingBoolChecker.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingBoolChecker.v)
  - 已新增 source-side checker 家族：
    - `check_pinstr_tiling_sourceb`
    - `check_pinstr_list_tiling_sourceb`
    - `check_pprog_tiling_sourceb`

这意味着当前状态已经不是“只有一个想法文档”，而是：

- 旧 compiled/padded relation 仍在，维持现有 checked path
- 新 witness-centered source relation 已经进入真实 Coq 文件
- 下一步是把 verified checked path 从旧 relation 切到新 relation，然后再
  收掉过渡性的 dual-transformation 结构

最新收紧后的 blocker 不再是单条 tiling lemma，而是 generic
`Validator` 的 ext 组合层：

- `flatten_instr_nth` 上的 `InstrPoint` 现在携带的是
  `current_transformation_of pi index`
- 但旧的 `compose_pinstr_ext` 仍把 ext-pinstr 的 transformation 固定为
  raw `pi_transformation`
- witness-centered 之后，这两者不再自然一致

因此下一步的正确重构点已经变成：

- 给 `Validator` 切换到 env-sized current-space ext composition
- 再把 ext-compose theorem chain 跟着迁过去

为此，真实代码里已经加了新的公共 helper：

- [PolyLang.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PolyLang.v)
  - `current_transformation_at`
  - `current_access_transformation_at`
  - `current_access_transformation_of`
- [Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v)
  - `compose_pinstr_ext_at`
  - `compose_pinstrs_ext_at`
## 2026-03-11: Witness-Centered Validator Boundary Clarified

- Added current-space helper lemmas in [Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v):
  - `current_env_dim_of_eq`
  - `current_transformation_of_eq_at`
  - `current_access_transformation_of_eq_at`
  - `expand_ip_instr_eq_current_tf_at`
  - `expand_ip_instr_eq_current_access_tf_at`
  - `in_compose_ipl_ext_inv`
- Re-inspected the runtime canonicalization path in [Entry.ml](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/Entry.ml) and confirmed that `build_canonical_tiled_after` is already witness-centered:
  - it keeps the source transformation,
  - sets `pi_point_witness := PSWTiling w`,
  - and lets schedule/domain live on the tiled/current point-space.
- This means the remaining `Validator.v` admits are not isolated proof gaps anymore; they expose a model mismatch:
  - source semantics/flattening use `current_transformation_of`,
  - old ext composition still assumes raw stored transformations are already the ext/current-space view.
- The next required step is therefore the more fundamental repair:
  - weaken the generic/wf side so stored transformations can live on the base/source point-space,
  - and weaken the affine-validator side to the transformation properties it actually consumes, instead of the older row-count coincidence.

## 2026-03-11: Dedicated Tiling Validator Path Started

- The overlay Coq model now has explicit tiling-side well-formedness predicates:
  - [PolyLang.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PolyLang.v)
    - `wf_pinstr_tiling`
    - `wf_pprog_tiling`
    - `wf_pinstr_ext_tiling`
- The overlay validator now has a tiling-side executable/checker entry point:
  - [Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v)
    - `check_wf_polyinstr_tiling`
    - `check_wf_polyprog_tiling`
    - `validate_tiling`
- The checked tiling path in
  [STilingOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/syntax/STilingOpt.v),
  [TPolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/TPolOpt.v),
  and [CPolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/CPolOpt.v)
  now targets `TilingVal.validate_tiling`, not the old affine-only
  `TilingVal.validate`.
- A first current-space wf bridge was added in
  [Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v):
  - `wf_pinstr_tiling_implies_wf_pinstr_ext_tiling_at`
- The current OCaml/debug path in
  [Entry.ml](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/Entry.ml)
  was switched to `validate_tiling` as well, and its expected statement-level
  relation was updated from the old padded/compiled view to the
  witness-centered source relation.

Current status after this refactor:

- the checked tiling pipeline is now structurally routed through a dedicated
  validator entry point;
- the remaining proof debt is no longer “prove the two old admits”, but:
  - finish porting the dependence/permutability layer to `validate_tiling`,
  - specifically weaken the `validate_two_accesses...` proof obligations from
    affine row-count coincidence to the transformation/access properties
    actually needed by `matrix_product` and `make_poly_eq`;
- `validate_tiling_correct` is still admitted at this point.

## 2026-03-13: Tiling Proof And Runtime Closure

The tiling path is now closed end-to-end in the container build.

What changed:

- The witness-aware well-formedness layer was generalized and renamed to the
  more accurate `wf_pinstr_general` / `wf_pprog_general` (compatibility aliases
  for the older `*_tiling` names remain).
- Instead of trying to make the old codegen theorems reason directly about
  arbitrary witness-centered programs, the proof now goes through
  `current_view_pprog`.
- `PrepareCodegen` gained/uses a top-down bridge theorem:
  - `prepared_codegen_correct_general`
- The tiling-side drivers now instantiate `PrepareCodegen` on `TilingPolIRs`,
  so their final theorem chain is:
  - checked tiling validate
  - `current_view_pprog`
  - old affine codegen correctness on the current-view program

Most important resulting theorems:

- `src/PrepareCodegen.v`
  - `prepared_codegen_correct_general`
- `driver/TPolOpt.v`
  - `checked_tiling_prepared_codegen_correct`
- `driver/CPolOpt.v`
  - `checked_tiling_prepared_codegen_correct`

Container build status:

- rebuilt successfully:
  - `src/PolyLang.vo`
  - `src/PrepareCodegen.vo`
  - `src/Validator.vo`
  - `src/TilingRelation.vo`
  - `src/TilingBoolChecker.vo`
  - `syntax/STilingOpt.vo`
  - `driver/TPolOpt.vo`
  - `driver/CPolOpt.vo`
  - `polopt`
  - `polcert`
- checked that there are no remaining `Admitted.` occurrences under:
  - `src`
  - `driver`
  - `syntax`
  - `polygen`

Runtime validation status:

- `polopt` now runs through the verified tiling path and produces tiled loops
  on real examples such as `syntax/examples/matadd.loop`.
- `polcert --kind tiling` validates real Pluto phase-2 tiling output.
- `polcert` three-input phase-aligned validation succeeds on:
  - `before -> mid` affine scheduling
  - `mid -> after` tiling

Residual note:

- Pluto still emits `isl_map.c:12117: number of columns too small` warnings on
  some tiling runs. These do not currently block:
  - phase-aligned `polcert`
  - `polcert --kind tiling`
  - `polopt` tiled code generation
  but they remain a Pluto/runtime cleanliness issue worth isolating later.
