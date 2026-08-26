# Tiling Transformation Bridge Plan

这份文档只讨论一件事：

- `pi_transformation` 怎么接到 tiling validator 的 Coq theorem 上

它是当前最该继续补的桥，因为：

- `pi_transformation` 直接进入 `Instr.instr_semantics`
- base-domain 和 access 现在都已经有了相对清楚的 witness-side preservation story
- transformation 如果不接上，`tiling_rel_pinstr` 还只能停在结构关系

## 1. 问题形状

tiling 之后，`pi_transformation` 不能继续假装不变。

对 `PolyLang` 来说，它的真实 lifting 不是：

- 在最前面补零

而是：

- 在 `env_size` 之后插入新增 tile iterators

也就是当前已经识别出来的 inserted-after-env 形状。

## 2. 候选 theorem 形状

最小需要的 theorem 可以先压成 affine-function 级别：

```text
lift_affine_function_after_env_eval :
  affine_product (lift f) (env ++ tiles ++ iters) =
  affine_product f (env ++ iters)
```

前提至少包括：

- `length env = env_size`
- `length tiles = added_dims`

然后再升成 transformation list：

```text
map affine_product (lift_transformation tf) [env ++ tiles ++ iters]
= map affine_product tf [env ++ iters]
```

或者等价的 pointwise 版本。

## 3. 为什么这条 bridge 是够用的

如果这条 theorem 成立，那么就能把：

- `after_pi.pi_transformation`

重新解释成：

- before instruction semantics 在原 point 上的同一组 transformed coordinates

这样 `tiling_rel_pinstr` 才能不只是“row 结构像”，而是开始接触真正的 instruction semantics。

## 4. 现有可复用对象

当前已经明确可以复用的名字有：

- `insert_zeros_constraint`
- `affine_product_skipn`
- `resize_app`
- `skipn_app_le`
- `skipn_app`

而且 overlay 里的 `TilingRelation.v` 已经有一个很接近最终需要的 lemma 形状：

- `lift_affine_function_after_env_eval`

所以这一步不是从零开始，而是把已有 helper 收成 proof plan。

## 5. 建议的证明顺序

1. affine function 单行求值
2. affine function 列表求值
3. transformation evaluation preservation
4. `check_pinstr_transformation_sound`
5. 并入更强的 `tiling_rel_pinstr`

## 6. 到这里还不该做什么

这一步之后，仍然不应该马上把 schedule legality 一起塞进 theorem。

顺序应该保持：

1. transformation bridge
2. stronger tiling relation
3. checker soundness
4. schedule legality composition

