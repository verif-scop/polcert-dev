# Tiling Coq Bridge

## Goal

把当前已经编过的 `gifted_curie:/polcert/src/TilingWitness.v` 和真正的验证边界压成一个明确的 bridge。

这里真正的目标不是 OpenScop 本身，而是：

- `PolyLang.t`
- `PolyLang.PolyInstr`
- `Validator` 最终会消费的 PolyLang 语义对象

OpenScop 在这里更像：

- 外部 Pluto 的 witness carrier
- importer/exporter 的不可信交换格式

而不是 proof target。

## 当前两边各自已经有什么

### OCaml checker 已经有

`PlutoTilingValidator.ml` 现在已经显式分成：

1. witness extraction
2. witness checking
3. `validate = extract + check`

核心检查点是：

1. `check_witness_shape`
   - statement id / iterator lists / added iterators / parents coverage
2. `check_domain_with_witness`
   - `base_domain_ok`
   - `link_rows_ok`
3. `check_accesses`
   - 删除 added tile inputs 之后必须和 before access rows 一致
4. `check_scattering_sanity`
   - 只是 shape sanity，不是 dependence proof

### Coq witness layer 已经有

`TilingWitness.v` 现在已经编过：

1. affine expression evaluation
2. tile-parent by division
3. lower/upper tile-link row semantics
4. ordered link trace soundness
5. base-row zero-prefix lifting
6. access-row zero-prefix lifting
7. `statement_tiling_core_sound`

也就是说，Coq 侧已经有：

- `link_rows_ok` 的语义核心
- `base_domain_ok` 的语义核心
- access preservation 的语义核心

还没有的是：

- 和 `PolyLang` 里真实 `pi_poly / pi_waccess / pi_raccess` 变化的直接对接
- witness extraction 的可信接口
- schedule legality

## 现在真正剩下的 bridge 是什么

我现在把 gap 分成 4 层。

### 1. PolyLang field bridge

对 tiling 来说，真正需要解释的是 `PolyInstr` 的哪些字段怎么变：

- `pi_depth`
- `pi_poly`
- `pi_waccess`
- `pi_raccess`
- `pi_transformation`
- `pi_schedule`

其中：

- `pi_depth` 不能继续假定不变；tiling 会引入新的 iterators
- 当前 Coq core theorem 已经覆盖了 `pi_poly` 的 link/base row 语义核心
- 也已经覆盖了 `pi_waccess / pi_raccess` 的 zero-prefix lifting 语义核心
- `pi_transformation` 也不能被忽略，因为它直接进入 `Instr.instr_semantics`
- 还没覆盖的是如何把这些抽象对象装配成新的 `PolyInstr`

还有一个更具体的实现点：

- `PolyLang` 的列顺序是 `env ++ iters`
- 所以真正该做的不是“简单前缀补零”
- 而是像现有 `insert_zeros_constraint d env_size` 那样，在 `env_size` 之后插入新 iterator 维

这对下面三个字段都成立：

- `pi_transformation`
- `pi_poly`
- `pi_waccess / pi_raccess`

所以真正该接的桥是：

- `before_pi : PolyInstr`
- `tiling_witness`
- `after_pi : PolyInstr`

并检查 `after_pi` 是否正是 witness 诱导出的 lifted PolyLang instruction。

一个更接近现有代码的候选形状已经能写出来了：

- `after_pi.pi_depth = before_pi.pi_depth + added_dims`
- `after_pi.pi_transformation = map (insert_zeros_constraint added_dims env_size) before_pi.pi_transformation`
- `after_pi.pi_poly = link_rows ++ map (insert_zeros_constraint added_dims env_size) before_pi.pi_poly`
- `after_pi.pi_waccess / pi_raccess` 也做对应的 inserted-zero lifting

其中真正还需要单独解释的是：

- `link_rows` 如何嵌入 `env ++ tile_iters ++ old_iters`
- `pi_schedule` 如何交给后续 legality checker

这个候选形状现在已经落成了一个可编译的 Coq 入口：

- `gifted_curie:/polcert/src/TilingRelation.v`

当前文件里已经有：

- `tiling_rel_pinstr_structure`
- `tiling_rel_pprog_structure`

它们现在还是“结构关系”，不是最终的 semantic theorem，但已经把独立 tiling pass 的 proof target 固定到了 `PolyLang` 上。

这里还有一个重要现实约束：

- 当前 `Validator` 的 `compose_pinstr_ext` 固定把 `pi_depth`、`pi_poly`、`pi_transformation`、`pi_waccess`、`pi_raccess` 都从 old `pi` 直接拿过去
- 它本质上只允许 `pi_schedule` 变化

所以 tiling 不应该被理解成“给现有 validator 多加几条检查”，而应该被理解成：

- 新建一条 `PolyLang`-side validator 路线
- schedule-only validator 继续只负责当前 envelope

### 2. Importer / carrier bridge

`PolyLang` 现在已经有：

- `from_openscop_schedule_only`
- `from_openscop`

这说明 OpenScop 本来就只是进出 `PolyLang` 的 carrier。

对 tiling 来说更合理的分层是：

1. 从 Pluto `after.scop` 提取 witness，或导入成一个候选 `after_poly`
2. verified checker 在 `PolyLang` 上检查 `before_poly + witness + after_poly`
3. OpenScop parser / importer 只提供不可信输入

也就是说，OpenScop row matrix 本身不是最终证明对象，只是 witness/import glue 的一部分。

### 3. Witness well-formedness bridge

当前 Coq 里有 `well_formed_statement_tiling_witness`，但还很弱。

真正需要跟 OCaml extractor 对齐的还有：

- added iterators count
- ordered link dependency discipline
- parent coverage
- positive tile sizes
- no parent self-dependence

也就是把现在 `check_witness_shape` 里的结构性条件，抽成一个 Coq predicate。

这一步的目的不是验证 OpenScop importer，而是给 PolyLang-side checker 一个清晰的 trusted input contract。

### 4. Statement-to-program bridge

当前 Coq core theorem 还是 statement-level。

后面还需要：

- statement correspondence
- `PolyLang.t` 上的 whole-program lifting soundness
- 再后面才是 schedule legality

这里最重要的纪律是：

- 先把 lifting correctness 做完整
- 不要过早把 schedule legality 塞进来

## 我现在认为最合适的下一步

下一步不该再写新的 arithmetic lemma，也不该把 OpenScop matrix 直接当 proof target。

更合适的是：

1. 在 `PolyLang.PolyInstr` 级别定义一个 witness-induced tiling relation
2. 证明 `statement_tiling_core_sound` 足够支撑这个 relation
3. 把 OCaml checker 重新理解成：
   - OpenScop -> witness / candidate `after_poly` 的不可信前端
   - PolyLang-side verified checker 的外壳

一旦这一步打通，就能开始说：

- 当前 OCaml checker 哪一部分只是 importer glue
- 哪一部分对应真正的 PolyLang proof target

## 对当前 OCaml checker 的直接解释

如果按 “未来可证明性” 重排，`PlutoTilingValidator.ml` 里的部分应该分成：

### 未来可证明 checker core

- `before_poly + after_poly + witness` 的 PolyLang relation
- `check_domain_with_witness` 背后的 link/base lifting relation
- `check_accesses` 背后的 access lifting relation

### 未来继续保持 untrusted 的部分

- raw witness extraction from `after.scop`
- parser/import details
- concrete row normalization / sorting glue

### 目前故意不纳入 tiling proof core 的部分

- `check_scattering_sanity`
- whole-program schedule legality

## 当前结论

tiling 的 lifting correctness 已经不再是“没有入口”的问题，但它的正确目标不是 OpenScop。

它现在已经有：

- executable OCaml prototype
- explicit witness split
- compiled Coq statement-level core theorem

剩下的关键工作不是再证明 `floor(phi/T)`，也不是先证明 OpenScop matrix 本身，而是把：

- Coq 的 statement-level lifting theorem
- `PolyLang.PolyInstr` / `PolyLang.t` 的真实变换关系

桥接起来。
