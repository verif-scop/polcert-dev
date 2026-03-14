# Tiling Pass Architecture

## 结论先说

是的，tiling 需要一个**额外的 validation pass**，并且它应该和当前的 `Validator` 独立。

原因不是风格问题，而是当前 `Validator` 的建模边界决定的：

- `compose_pinstr_ext` 固定保留 old program 的
  - `pi_depth`
  - `pi_poly`
  - `pi_transformation`
  - `pi_waccess`
  - `pi_raccess`
- 它本质上只允许 `pi_schedule` 变化

这正好覆盖 affine scheduling，但不覆盖 tiling。

## 当前 validator 为什么不该硬扩

当前 `Validator.validate` 的核心假设是：

- before / after 的实例空间是同一个 family
- access / transformation 不变
- 只检查旧 schedule 与新 schedule 的依赖合法性

而 tiling 的真实变化至少包括：

- `pi_depth` 增加
- `pi_poly` 扩成 “lifted base rows + tile-link rows”
- `pi_transformation` 需要插入新 tile iterators
- `pi_waccess / pi_raccess` 输入维要扩张

所以如果直接硬改当前 validator，会同时破坏：

- 组合方式
- 证明结构
- 现有 schedule-only envelope

更稳的做法是新开一条 pass。

## 推荐结构

我现在建议把 tiling 支持拆成两层。

### 1. 新的 tiling structural validator

模块上可以叫：

- `TilingValidator`

它的职责不是依赖合法性，而是**lifting correctness**：

- 给定 `before_poly`
- 给定 `after_poly`
- 给定 `tiling_witness`
- 检查 `after_poly` 是否是 witness 诱导出来的正确 tiled program

这个 pass 主要检查：

1. statement correspondence
2. `pi_depth` 增量
3. `pi_transformation` 的 inserted-zero lifting
4. `pi_poly` 的
   - lifted base rows
   - tile-link rows
5. `pi_waccess / pi_raccess` 的 inserted-zero lifting

这里的 proof target 应当是 `PolyLang.PolyInstr` / `PolyLang.t`。

### 2. 现有 schedule validator 保持独立

当前 `Validator` 继续只负责：

- schedule legality

也就是：

- 在 domain/access/transformation 已经固定的情况下
- 验证 schedule change 是否保依赖

这条路线不应该被 tiling 改坏。

## 两条 pass 怎么组合

我目前认为最清晰的组合方式是：

```text
Pluto after.scop
  -> untrusted importer / witness extractor
  -> after_poly + tiling_witness

before_poly + after_poly + tiling_witness
  -> TilingValidator.validate_structure

(optional later)
  -> schedule legality check on a suitable tiled PolyLang intermediate
```

这里先故意把 schedule legality 和 tiling lifting correctness 分开。

这个边界现在已经有两条可执行原型支撑：

1. container `polopt` 内的 OCaml prototype
2. host-side standalone OCaml checker

两者都显式采用：

- `extract`
- `check`
- `validate = extract + check`

因此下一阶段的 Coq 目标可以稳定地钉在 `check`，而不需要把 driver-facing 的 raw OpenScop witness recovery 一并证明掉。

## 输入接口

最终 verified 接口更适合是：

```text
validate_tiling : before_poly -> after_poly -> tiling_witness -> bool
```

而不是：

```text
validate_tiling : before.scop -> after.scop -> bool
```

后者可以保留成 driver-facing 接口，但内部应当分成：

```text
before.scop / after.scop
  -> untrusted import
  -> before_poly / after_poly / tiling_witness
  -> verified tiling validator
```

## 现有 Coq 进展怎么接进来

现在 `TilingWitness.v` 已经给了一个 statement-level core：

- tile-link row soundness
- lifted base-row preservation
- lifted access-row preservation
- `statement_tiling_core_sound`

下一步不该再补 schedule 定理，而应该把这个 core theorem 接成：

- `tiling_rel_pinstr`
- `tiling_rel_pprog`

其中 `tiling_rel_pinstr before_pi after_pi w` 至少应当包含：

- 相同 `pi_instr`
- `after_pi.pi_depth = before_pi.pi_depth + added_dims`
- `after_pi.pi_transformation = map (insert_zeros_constraint added_dims env_size) before_pi.pi_transformation`
- `after_pi.pi_poly = link_rows ++ map (insert_zeros_constraint added_dims env_size) before_pi.pi_poly`
- `after_pi.pi_waccess / pi_raccess` 做同样 inserted-zero lifting

## 这里最关键的技术点

真正的 embedding 不是“在最前面补零”，而是：

- `PolyLang` 的列顺序是 `env ++ iters`
- 所以要在 `env_size` 之后插入 tile iterators
- 现有代码里这个形状已经有名字：
  - `insert_zeros_constraint`

这意味着当前 `TilingWitness.v` 里“前缀补零”的简化版本是对的，但后续必须推广到 PolyLang 的真实列布局。

## 当前建议

接下来 tiling 工作应该按这个顺序继续：

1. 定义独立的 `tiling_rel_pinstr`
2. 把 `statement_tiling_core_sound` 推广到 `insert_zeros_constraint` 形状
3. 做 `tiling_rel_pprog`
4. 保持现有 `Validator` 不动
5. 最后再考虑 schedule legality 如何组合

## 当前已经落下来的 Coq 入口

这个架构现在不只是纸面设计了。

我已经加了一个新的 Coq 入口：

- `gifted_curie:/polcert/src/TilingRelation.v`

它当前是一个**结构关系**，还不是最终正确性定理，但已经把独立 pass 的 proof target 固定下来了：

- `tiling_rel_pinstr_structure`
- `tiling_rel_pprog_structure`

它明确建模了：

- `pi_depth`
- `pi_transformation`
- `pi_poly`
- `pi_waccess`
- `pi_raccess`

而且故意**不**把 `pi_schedule` 塞进去，因为 schedule legality 仍然应当作为后续独立层处理。

这一步的价值是：

- 旧 validator 继续保持 schedule-only
- 新 tiling pass 已经有了 Coq 层的对象边界
