# Parallel Validator Minispec

本文给出 `checked_parallelize_current` 的更具体规格。

目标是把“parallel-safe 到底是什么意思、checker 检查什么、soundness theorem 应该长什么样”固定下来，使后续实现不再停留在概念描述层面。

## 1. checker 的位置

checker 的工作对象应是：

```text
pp_cur := current_view_pprog pol_after
```

也就是：

- 已经过 affine / tiling transform correctness 验证
- 已经经过 `current_view_pprog`
- 且即将进入 codegen 的 current-space program

它不应直接工作在：

- source loop AST
- raw OpenScop scattering rows
- 最终 Loop AST

## 2. checker 的输入与输出

### 2.1 `parallel_plan`

第一版建议非常简单：

```text
Record parallel_plan := {
  target_dim : nat
}.
```

其含义是：

- 尝试把 current-space 第 `target_dim` 维并行化

### 2.2 `parallel_cert`

第一版可以和 plan 同构，但 theorem 上要明确区分：

```text
Record parallel_cert := {
  certified_dim : nat
}.
```

它只能在 checker 成功时产生。

### 2.3 checker 接口

概念上建议：

```text
check_pprog_parallel_currentb : pprog -> parallel_plan -> bool

checked_parallelize_current :
  pprog -> parallel_plan -> result parallel_cert
```

其中：

- `check_pprog_parallel_currentb`
  - 纯布尔 checker
- `checked_parallelize_current`
  - 负责 well-formedness 检查、维度范围检查、以及返回 cert

## 3. candidate dimension 的直观含义

设 candidate 为 `d`。

其并行语义直观上表示：

- 固定所有 outer prefix dimensions `< d`
- 第 `d` 维不同的各次迭代可以交错执行

因此 checker 真正要排除的不是“程序中有没有任何 dependence”，而是：

- 在同一个 outer-prefix slice 内
- 不同 `d` 值的实例之间
- 是否会出现破坏语义的跨迭代冲突

## 4. 推荐的核心谓词

### 4.1 同 slice

概念上定义：

```text
same_prefix_before d p1 p2
```

含义：

- 两个 current points 在前 `d` 个维度上相同

### 4.2 不同 parallel iteration

概念上定义：

```text
different_dim_at d p1 p2
```

含义：

- 第 `d` 维不同

### 4.3 cross-iteration related pair

把这两个条件合起来：

```text
same_parallel_slice d p1 p2 :=
  same_prefix_before d p1 p2 /\
  different_dim_at d p1 p2.
```

其含义是：

- 这两个实例恰好属于同一个并行 region 下、不同 `d`-iteration 的一对点

### 4.4 推荐的 quasi-Coq helper 形状

真正落 Coq 时，我建议不要一开始就把所有细节写死在一个定义里。  
更稳的是先引入几个 helper accessor / predicate，再在其上定义 `parallel_safe_dim`。

概念上可写成：

```text
current_coords_of : InstrPoint_ext -> list Z
same_env_of : InstrPoint_ext -> InstrPoint_ext -> Prop
```

然后：

```text
Definition same_prefix_before (d : nat) (ip1 ip2 : InstrPoint_ext) : Prop :=
  firstn d (current_coords_of ip1) = firstn d (current_coords_of ip2).

Definition different_dim_at (d : nat) (ip1 ip2 : InstrPoint_ext) : Prop :=
  nth_error (current_coords_of ip1) d <>
  nth_error (current_coords_of ip2) d.

Definition same_parallel_slice (d : nat) (ip1 ip2 : InstrPoint_ext) : Prop :=
  same_env_of ip1 ip2 /\
  same_prefix_before d ip1 ip2 /\
  different_dim_at d ip1 ip2.
```

这里的关键点有两个：

- `same_env_of`
  - 把参数环境相同这个条件显式写出来
- `current_coords_of`
  - 明确谓词工作在 current-view 坐标上，不是在 old/source schedule 上

## 5. 第一版建议的 safety 定义：保守版

为了尽快闭合 theorem，第一版建议使用保守的 safety 定义，而不是一开始就接最强的 `Permutable_ext`。

### 5.1 destructive conflict

对于一对访问，若：

- 指向同一 memory location
- 且访问类型属于 `WW / WR / RW`

则称之为 destructive conflict。

`RAR` 不算冲突。

### 5.2 `parallel_safe_dim` 的保守定义

概念上：

```text
parallel_safe_dim pp d :=
  对任意两个属于 same_parallel_slice d 的实例，
  任意 destructive access pair 都不可能落到同一 memory cell。
```

也就是说，第一版要求：

- 同一个并行 slice 内，不允许跨迭代 destructive conflict

推荐进一步压成下面这种 quasi-Coq 形状：

```text
exec_points_ext_of : pprog -> list InstrPoint_ext

destructive_conflict_ext : InstrPoint_ext -> InstrPoint_ext -> Prop

Definition parallel_safe_dim (pp : pprog) (d : nat) : Prop :=
  forall tau1 tau2,
    In tau1 (exec_points_ext_of pp) ->
    In tau2 (exec_points_ext_of pp) ->
    same_parallel_slice d tau1 tau2 ->
    destructive_conflict_ext tau1 tau2 ->
    False.
```

如果后面要更贴近现有 `StablePermut` 证明栈，也可以把结论加强成：

```text
Definition parallel_swap_ok (pp : pprog) (d : nat) : Prop :=
  forall tau1 tau2,
    In tau1 (exec_points_ext_of pp) ->
    In tau2 (exec_points_ext_of pp) ->
    same_parallel_slice d tau1 tau2 ->
    Permutable_ext tau1 tau2.
```

然后把第一版 checker 证明成：

- `parallel_safe_dim pp d -> parallel_swap_ok pp d`

这样后面 bridge 到 `stable_permut_ext_lists_are_equivalent` 时会更顺。

这是明显强于“某些 pairs 可以交换”的，但实现和证明都更直接。

## 6. checker 的 polyhedral 约束构造

这部分是最接近现有 validator 实现的地方。

对每个 statement pair / access pair，构造一个 polyhedron，表示“存在一个坏的 cross-iteration conflict”。

### 6.1 变量

每个坏例子都涉及：

- 一个来自 `stmt1` 的实例点 `p1`
- 一个来自 `stmt2` 的实例点 `p2`
- 相同参数环境

### 6.2 约束

推荐约束集合：

1. `p1` 在 `stmt1` 的 domain 中
2. `p2` 在 `stmt2` 的 domain 中
3. 两边环境参数相同
4. `same_prefix_before d p1 p2`
5. `different_dim_at d p1 p2`
6. 两个 access 落到同一 memory cell
7. 该 access pair 属于 `WW / WR / RW`

若这组约束可满足，就找到一个反例，说明 `d` 不 safe。

若所有此类 polyhedra 都为空，则 `d` safe。

## 7. checker 的执行策略

第一版建议完全按“存在坏例子则失败”的风格实现。

### 7.1 维度检查

先检查：

- `d < pprog_current_dim pp_cur`

否则直接失败。

### 7.2 枚举

枚举：

- statement pairs
- write/write pairs
- write/read pairs
- read/write pairs

不需要枚举：

- read/read pairs

### 7.3 emptiness checks

对每个坏例子 polyhedron 做 emptiness 检查。

布尔 checker 返回：

- `true`
  - 所有坏例子均不可满足
- `false`
  - 存在至少一个坏例子

## 8. soundness theorem 的推荐形状

推荐 theorem 形状：

```text
check_pprog_parallel_currentb pp_cur plan = true
-> wf_pprog_general pp_cur
-> parallel_safe_dim pp_cur plan.(target_dim)
```

若使用 `checked_parallelize_current`，则推荐：

```text
checked_parallelize_current pp_cur plan = Okk cert
-> wf_pprog_general pp_cur
-> parallel_cert_sound pp_cur cert
```

其中：

```text
parallel_cert_sound pp_cur cert :=
  parallel_safe_dim pp_cur cert.(certified_dim)
```

第一版直接这样定义即可。

如果准备更直接地对接 codegen theorem，我建议再预留一条 bridge lemma：

```text
parallel_cert_sound pp_cur cert
-> parallel_swap_ok pp_cur cert.(certified_dim)
```

这条 lemma 的职责非常明确：

- checker 给出的是 poly/current-view 上的 safety 结论
- 而 parallel semantics refinement 最终需要的是“允许的跨迭代 swap 都是安全的”

也就是说，这里是 validator 与 semantics theorem 的接口层。

## 9. 为什么第一版先用保守版是合理的

第一版如果直接用最强定义：

- “所有可失序 pairs 都满足 `Permutable_ext`”

会马上遇到两个工程问题：

1. 现有 `Permutable_ext` machinery 强绑定在 affine validator 的 before/after ext-point 框架上
2. 需要先把单程序版的 pairwise-permutability 抽出来

因此第一版先用保守 no-destructive-conflict 定义更现实。

### 9.1 它足够支持抽象 `parallel for`

只要：

- 同一并行 slice 内没有 destructive conflict

那么任意保序 interleaving 都有希望被证明安全。

### 9.2 它与 OpenMP `parallel for` 直觉一致

第一版只接受最明显的“各迭代互不干扰”情况，用户心智也更清楚。

## 10. 第二版的放宽方向

后续更强版本可以把 safety 定义从：

- no destructive conflict

放宽到：

- pairwise `Permutable_ext`

到那时 checker 可改成：

1. 对 destructive pair 先尝试判空
2. 若非空，再尝试证明这些 pair 可交换
3. 最终只要所有可能坏例子都被“判空或可交换”覆盖即可

这会更贴近现有 affine validator 的真正数学形态。

## 11. `parallel_safe_dim` 与 `par_trace` 的关系

checker 并不是在直接证明 codegen loop 正确。  
它证明的是一个 program-level safety predicate。

然后这个 predicate 应当在 semantics theorem 中被使用：

- `parallel_safe_dim pp d`
  - 蕴含 `parallel_swap_ok d`
- `parallel_swap_ok d`
  - 蕴含 `par_trace` 中所需的局部 swap 全部语义安全

因此 theorem layering 应是：

```text
checker soundness
-> parallel_safe_dim
-> allowed swap soundness
-> par_trace stable permutation soundness
-> parallel semantics refines sequential semantics
```

## 12. 与 Pluto hint 的关系

Pluto `<loop>` extension` 最多帮助：

- 生成一个 `parallel_plan`

例如：

- Pluto 说 `t2` parallel
- PolOpt 把它对齐到 current dimension `d=1`
- 然后构造 `plan = { target_dim = 1 }`

但真正的 correctness 完全不应依赖 hint。

也就是说：

- hint 只影响“先试哪层”
- cert 决定“能不能真的输出 `par for`”

## 13. 推荐的定理与定义名

如果要开始进入实现，我建议先固定下面这些名字。

### 13.1 定义

- `parallel_plan`
- `parallel_cert`
- `same_prefix_before`
- `different_dim_at`
- `same_parallel_slice`
- `parallel_safe_dim`
- `parallel_cert_sound`
- `check_pprog_parallel_currentb`
- `checked_parallelize_current`

### 13.2 定理

- `check_pprog_parallel_currentb_sound`
- `checked_parallelize_current_sound`
- `parallel_cert_sound_implies_parallel_safe_dim`

## 14. 最后的收束

这份 minispec 的核心判断是：

> `checked_parallelize_current` 第一版应当是一个在 `current_view_pprog` 上工作的、保守的、基于 cross-iteration destructive-conflict emptiness 的 checker。它不负责启发式选层，只负责把某个 candidate dimension checked 地升级成 `parallel_cert`，供后续 `par for` 语义正确性 theorem 使用。

它和 `parallel-semantics-minispec.md` 正好对应两半：

- 这份文档定义“证什么”
- 另一份文档定义“被证的 `par for` 语义是什么”
