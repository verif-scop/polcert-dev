# Parallel Semantics Minispec

本文给出一个更接近 Coq 形式化的 `par for` 语义设计草案。

目标不是现在就把完整定义写成可编译代码，而是把下面四件事固定下来：

1. `par for` 的语义对象到底是什么
2. 为什么它最好定义在 instruction-point trace 层
3. 它和顺序 `Loop` 语义的关系是什么
4. 它如何接到 `parallel_cert_sound` 上

## 1. 设计目标

如果最终支持的是 verified `parallel for`，那么语义层至少要满足：

1. `par for` 允许真正的非顺序 interleaving
2. 这种 interleaving 不需要一开始就形式化成完整 OpenMP runtime
3. 最终 theorem 能说：
   - 所有 `par for` 语义允许的行为
   - 都 refine 到顺序 `for` 的语义

因此第一版最合理的目标是：

- 定义抽象的 parallel semantics
- 它覆盖 loop-iteration-level 的交错执行
- 但不建模线程 API、调度器、runtime clause 细节

## 2. 为什么 trace-level 是最自然的切入点

当前系统已经有两条很重要的现成桥：

1. `polygen/Loop.v`
   - `loop_instance_list_semantics`
2. `polygen/InstanceListSema.v`
   - `instr_point_list_semantics`

后者的含义是：

- 给定一串 `InstrPoint`
- 就有一套独立的“按该顺序执行这串 instruction points” 的状态语义

这非常适合并行语义，因为并发的本质就是：

- 顺序执行时会产生一串 canonical trace
- 并行执行允许这串 trace 出现更多合法重排 / 交错

所以并行语义最自然的表示不是：

- 直接定义线程级 operational semantics

而是：

- 先定义哪些 `InstrPoint` traces 是并行语义允许的
- 再交给已有的 `instr_point_list_semantics` 去解释状态变化

## 3. 推荐的表示层：`ParallelLoop`

proof engineering 上，第一版最推荐保留现有 `Loop`，并新增一个 wrapper 层：

```text
ParallelLoop.stmt
```

概念上可写成：

```text
Inductive loop_mode := SeqMode | ParMode.

Inductive stmt :=
| Loop  : loop_mode -> option nat -> expr -> expr -> stmt -> stmt
| Instr : instr -> list expr -> stmt
| Seq   : stmt_list -> stmt
| Guard : test -> stmt -> stmt.
```

其中：

- `loop_mode`
  - `SeqMode`
  - `ParMode`
- 第二个 `option nat`
  - 记录这层 loop 对应的 current-space dimension

这里的 current-dimension tag 很重要，因为：

- `parallel_cert` 也是按 current-space dimension 发证
- 最终 theorem 必须把 cert 和 emitted `par for` 节点精确对应起来

### 3.1 `erase_parallel`

然后定义：

```text
erase_parallel : ParallelLoop.stmt -> Loop.stmt
```

做法是：

- 抹掉 `SeqMode/ParMode`
- 抹掉 origin dimension tag
- 保留普通 loop 结构

它的地位只是辅助 theorem，不是最终并发 correctness 本身。

## 4. 两种 trace 关系

推荐把 `ParallelLoop` 的语义拆成两种纯结构关系。

### 4.1 `seq_trace`

定义：

```text
seq_trace : ParallelLoop.stmt -> list Z -> list InstrPoint -> Prop
```

含义：

- 这就是把所有 loop 都按顺序解释时产生的 canonical trace

其结构规则和当前 `Loop` 的 instance-list 结构一致：

- `Instr` 产生 singleton trace
- `Seq` 产生拼接
- `Guard` 根据 `eval_test env` 产生 body trace 或空 trace
- `Loop SeqMode d lb ub body`
  - 产生按 `Zrange` 顺序拼接的各次迭代 body traces
- `Loop ParMode ...`
  - 在 `seq_trace` 下仍然按顺序拼接

也就是说：

- `seq_trace` 本质上对应 `erase_parallel` 的 canonical trace

### 4.2 `par_trace`

再定义：

```text
par_trace : ParallelLoop.stmt -> list Z -> list InstrPoint -> Prop
```

含义：

- 这是 abstract parallel semantics 允许的 trace

它与 `seq_trace` 的唯一关键差别出现在 `ParMode`：

- `Instr` / `Seq` / `Guard` / `SeqMode` 规则与顺序一样
- `ParMode` 不再按 range 顺序直接拼接 body traces
- 而是允许把各次迭代 trace 做合法 interleaving

## 5. `ParMode` 的核心：合法 interleaving

这一节是最关键的。

### 5.1 先为每次迭代生成子 trace

对：

```text
Loop ParMode d lb ub body
```

固定环境 `env` 后，先取：

```text
zs := Zrange (eval_expr env lb) (eval_expr env ub)
```

然后对每个 `x in zs`，递归地得到：

```text
seq_trace body (x :: env) il_x
```

第一版建议故意使用 `seq_trace` 而不是递归 `par_trace`。

原因是：

- 第一版不做 nested parallel
- 这能把 `ParMode` 的证明目标收缩成“单层 parallel region 的合法 interleaving”
- 也更贴近当前 single-dim checked cert 的设计

等 single-dim `par for` 稳定以后，再考虑把这里推广成递归 `par_trace`。

### 5.2 再定义 family interleaving

需要一个纯 list 关系，例如概念上：

```text
interleave_family : list (list InstrPoint) -> list InstrPoint -> Prop
```

含义：

- `il` 是这组子 traces 的一个 interleaving

它至少要满足：

1. 每个子 list 中的相对顺序被保留
2. 所有元素都出现且只出现一次
3. 不要求不同 iteration 之间保持顺序

也就是说：

- within one iteration: order preserved
- across different iterations: arbitrary merge allowed

推荐第一版直接写成下面这种 quasi-Coq 形状：

```text
Inductive interleave_family : list (list InstrPoint) -> list InstrPoint -> Prop :=
| IF_nil :
    interleave_family [] []
| IF_skip_nil :
    forall trs out,
      interleave_family trs out ->
      interleave_family ([] :: trs) out
| IF_take :
    forall pre x xs post out,
      interleave_family (pre ++ xs :: post) out ->
      interleave_family (pre ++ (x :: xs) :: post) (x :: out).
```

这个定义的好处是：

- 结构归纳直接按输出 trace 长度下降
- 比较容易先证 membership / subtrace-order 之类的结构引理
- 后续做 `stable permutation` 的归纳也比较自然

### 5.3 `ParMode` 的 trace 规则

于是 `ParMode` 规则可以写成：

```text
For all x in zs, seq_trace body (x :: env) il_x
interleave_family [il_x | x in zs] il
--------------------------------------
par_trace (Loop ParMode d lb ub body) env il
```

这就是抽象的 worksharing semantics。

更接近 Coq 的推荐 theorem 头可写成：

```text
Inductive par_trace : ParallelLoop.stmt -> list Z -> list InstrPoint -> Prop :=
| PT_Instr : ...
| PT_Seq : ...
| PT_GuardTrue : ...
| PT_GuardFalse : ...
| PT_LoopSeq : ...
| PT_LoopPar :
    forall d lb ub body env zs trs tr,
      zs = Zrange (eval_expr env lb) (eval_expr env ub) ->
      Forall2 (fun z tri => seq_trace body (z :: env) tri) zs trs ->
      interleave_family trs tr ->
      par_trace (Loop ParMode (Some d) lb ub body) env tr.
```

第一版更推荐根本不输出 `ParMode None`。  
这样 theorem 里不需要再额外加“这个 `ParMode` 必须有 cert 可对齐”的 side condition。

## 6. 从 trace 到状态语义

有了 `par_trace` 之后，真正的并行语义定义可以非常薄：

```text
parallel_semantics stmt env st1 st2 :=
  exists il,
    par_trace stmt env il /\
    instr_point_list_semantics il st1 st2.
```

如果还保留外层 `program = (stmt, ctxt, vars)` 包装，则再加上：

- `Compat`
- `NonAlias`
- `InitEnv`

做法与现有 `Loop.semantics` 类似即可。

这条设计的优点是：

- 真正执行状态变化的部分完全复用现有 `instr_point_list_semantics`
- `par for` 的新工作只剩“允许哪些 traces”

## 7. `erase_parallel` 的正确关系

`erase_parallel` 应当与 `seq_trace` 对齐。

最自然的 theorem 是：

```text
seq_trace stmt env il
<-> loop_instance_list_shape_of (erase_parallel stmt) env il
```

如果不想单独定义 shape-only 版本，也可以走较弱但更工程化的路线：

- 证明 `seq_trace` 与 `erase_parallel` 生成的 canonical trace 一致
- 再从那里连接到现有顺序 semantics

这里的关键不是 theorem 具体长什么样，而是：

- `erase_parallel` 对应 canonical sequential behavior
- `par_trace` 对应 parallel-allowed behaviors

## 8. 为什么 cert 不应该 baked into semantics

一个自然但不推荐的选择是：

- 直接在 `par_trace` 里要求“这个 loop 已经 safe”

我不建议这么做。

更干净的结构是：

1. `ParallelLoop` 语义独立定义
   - 它描述 runtime 允许的行为
2. `parallel_cert_sound`
   - 说明某个 `ParMode d` 的行为是安全的
3. correctness theorem
   - 若 cert sound，则该语义 refine 到顺序语义

这样有两个好处：

- semantics 本身是纯语言定义
- cert 只是决定“这个语言构造是否允许由 optimizer 输出”

## 9. 推荐的安全性定理形状

语义层最核心的 theorem 应是：

```text
parallel_cert_sound pp cert
-> codegen_matches_cert pp cert stmt
-> parallel_semantics stmt st1 st2
-> Loop.semantics (erase_parallel stmt) st1 st2'
-> State.eq st2 st2'
```

如果把 `Loop.semantics (erase_parallel stmt)` 放在结论中由 existential 给出，也可以写成：

```text
parallel_cert_sound pp cert
-> codegen_matches_cert pp cert stmt
-> parallel_semantics stmt st1 st2
-> exists st2',
     Loop.semantics (erase_parallel stmt) st1 st2' /\
     State.eq st2 st2'
```

这一步才是真正的：

- `par for` 语义被证明 refine 到顺序语义

## 10. 为什么这条 theorem 应该通过 `StablePermut` 证明

`par_trace` 允许的 interleaving，本质上就是：

- canonical sequential trace 的某种重排

而当前系统已经有：

- `Permutable`
- `Permutable_ext`
- `StablePermut`

因此最自然的路线是：

1. 证明任意 `par_trace` 都与 canonical `seq_trace` 满足某个 `par_stable_permut`
2. 证明 `parallel_cert_sound` 蕴含：
   - 所有 `par_stable_permut` 中用到的 swap 都是 `Permutable`
3. 复用 `instr_point_list_semantics` 对 stable permutation 的保序性质

这比直接从头证明“任意 interleaving 都等价”更贴近现有 proof asset。

推荐把这里真正落成下面这几条 theorem 头：

```text
Lemma interleave_family_preserves_membership :
  forall trs tr e,
    interleave_family trs tr ->
    In e tr ->
    exists tri, In tri trs /\ In e tri.

Lemma interleave_family_preserves_subtrace_order :
  forall trs tr tri e1 e2,
    interleave_family trs tr ->
    In tri trs ->
    subtrace_of tri tr ->
    before_in_list e1 e2 tri ->
    before_in_list e1 e2 tr.

Lemma interleave_family_concat_stable_permut :
  forall trs tr,
    interleave_family trs tr ->
    StablePermut ... (concat trs) tr.

Lemma par_trace_implies_stable_permut_of_seq_trace :
  forall stmt env trp,
    par_trace stmt env trp ->
    exists trs,
      seq_trace stmt env trs /\
      StablePermut ... trs trp.
```

这里真正重要的不是 `before_in_list` / `subtrace_of` 的最终具体定义，  
而是 theorem 结构必须保证：

- `interleave_family`
  -> `concat` 的 stable permutation
- `par_trace`
  -> 某个 canonical `seq_trace` 的 stable permutation

## 11. `par_stable_permut` 的稳定条件

为了真正对上 checker，这里的 stable function 不应写成“任意两个点都能交换”，而应写成：

```text
parallel_swap_ok d tau1 tau2
```

其含义至少包括：

1. `tau1` 与 `tau2` 属于同一 parallel slice
   - outer prefix `< d` 相同
2. 二者确实来自不同 `d`-iterations
   - 第 `d` 维不同
3. 它们交换是安全的

第 3 点在第一版可以保守地定义成：

- 没有 `WW/WR/RW` cross-iteration conflict

后续再放宽成：

- 由 checker 推出 `Permutable`

推荐把这一步在 theorem 层直接写成：

```text
Lemma parallel_cert_sound_implies_parallel_swap_ok :
  forall pp cert,
    parallel_cert_sound pp cert ->
    parallel_swap_ok pp cert.(certified_dim).

Lemma parallel_swap_ok_implies_swap_permutable :
  forall pp d tau1 tau2,
    parallel_swap_ok pp d ->
    same_parallel_slice d tau1 tau2 ->
    Permutable_ext tau1 tau2.
```

也就是说，语义 refinement 真正直接消费的，不该是原始 checker theorem，  
而应该是中间桥接谓词 `parallel_swap_ok`。

## 12. 关于 nested parallel 的第一版收缩

第一版建议只支持：

- 单层 `ParMode`

也就是说，一个最终 emitted program 最多只包含一层 certified `par for`。

这样有几个好处：

- `interleave_family` 只需处理一层 parallel region
- theorem 里的 slice 定义简单很多
- 与 Pluto 的 `multipar` 脱钩

等这一版稳了，再扩 nested parallel。

## 13. 推荐的第一版 theorem inventory

如果后续要落成 Coq 文件，我建议至少准备下面这些定义/定理名。

### 13.1 结构定义

- `ParallelLoop.loop_mode`
- `ParallelLoop.stmt`
- `ParallelLoop.erase_parallel`
- `ParallelLoop.seq_trace`
- `ParallelLoop.par_trace`
- `ParallelLoop.parallel_semantics`
- `ParallelLoop.interleave_family`

### 13.2 关键关系

- `ParallelLoop.parallel_swap_ok`
- `ParallelLoop.par_stable_permut`
- `ParallelLoop.codegen_matches_cert`

### 13.3 关键定理

- `erase_parallel_seq_trace_correct`
- `interleave_family_concat_stable_permut`
- `par_trace_implies_stable_permut_of_seq_trace`
- `parallel_cert_sound_implies_parallel_swap_ok`
- `parallel_cert_sound_implies_swap_permutable`
- `parallel_semantics_refines_erased_sequential`

## 14. 最后的收束

这份 minispec 的关键结论可以压成一句话：

> `par for` 的第一版 verified 语义应当定义成“允许对各次迭代 body traces 做保持单次迭代内部顺序的 interleaving”，再借助 `parallel_cert_sound` 和 `StablePermut` 风格的 theorem 证明这些 interleaving 全部 refine 到顺序擦除语义。

这条路线的优势是：

- 真正验证了 `par for` 语义本身
- 不需要立即形式化整个 OpenMP runtime
- 和现有 instruction-point / stable-permutation 证明资产高度兼容
