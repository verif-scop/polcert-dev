# Parallel Coq Skeleton

本文把 parallel 支持进一步压缩成“接近可以开写 Coq 文件”的骨架。

目标不是现在就实现，而是回答下面这些非常具体的问题：

1. 新模块应该建在哪些文件里
2. 它们应该以 `INSTR` 还是 `POLIRS` 为 functor 参数
3. 核心定义的建议类型是什么
4. 证明顺序应如何安排
5. 哪些现有 theorem 可以直接复用

它和前面几份文档的关系是：

- `parallel-proof-strategy.md`
  - 讲证明边界
- `parallel-semantics-minispec.md`
  - 讲 `par for` 语义内容
- `parallel-validator-minispec.md`
  - 讲 checker 内容
- 本文
  - 讲这些内容怎样落成 Coq 模块和 theorem inventory

## 1. 推荐的新文件布局

当前最推荐的第一版布局是：

### 1.1 `polygen/ParallelLoop.v`

functor 参数：

```text
Module ParallelLoop (IInstr : INSTR).
```

职责：

- 定义 parallel-aware loop IR
- 定义 `erase_parallel`
- 定义 `seq_trace`
- 定义 `par_trace`
- 定义 `parallel_semantics`

理由：

- 这层只依赖 instruction semantics 与 loop/program syntax
- 不需要直接依赖 `POLIRS`

### 1.2 `src/ParallelValidator.v`

functor 参数：

```text
Module ParallelValidator (PolIRs : POLIRS).
```

职责：

- 定义 `parallel_plan`
- 定义 `parallel_cert`
- 定义 `parallel_safe_dim`
- 实现 `check_pprog_parallel_currentb`
- 证明 checker soundness

理由：

- checker 工作在 `PolyLang` current-view program 上
- 因此天然依赖 `POLIRS`

### 1.3 `src/ParallelCodegen.v`

functor 参数：

```text
Module ParallelCodegen (PolIRs : POLIRS).
```

职责：

- 定义 `annotated_codegen`
- 定义 `codegen_matches_cert`
- 建立 `annotated_codegen` 与现有顺序 codegen 的关系
- 证明 `parallel_semantics_refines_erased_sequential`

理由：

- 它需要同时看见：
  - `PolyLang`
  - `PrepareCodegen`
  - `ParallelLoop`

### 1.4 `src/Validator.v`

这里只做 re-export alias 即可。

未来可以补：

- `checked_parallelize_current`
- `checked_parallelize_current_sound`

保持 API 风格与现有：

- `checked_tiling_validate_poly`
- `checked_tiling_validate_poly_correct`

一致。

### 1.5 `driver/PolOpt.v`

只在 parallel 真要接入主 pipeline 时才动它。  
它的职责是：

- 在 `current_view_pprog` 后调用 `checked_parallelize_current`
- 成功时调用 `annotated_codegen`
- 失败时回退顺序 codegen

## 2. 为什么 functor 分层应该这样切

### 2.1 `ParallelLoop` 不应依赖 `POLIRS`

因为它要表达的是：

- 一门 loop 语言及其语义

这与：

- Pluto/OpenScop
- `scheduler`
- `phase_scop_scheduler`

没有直接关系。

它只需要像现有 `Loop.v` 一样参数化在：

- `INSTR`

上即可。

### 2.2 `ParallelValidator` 必须依赖 `POLIRS`

因为它需要：

- `PolyLang`
- `current_view_pprog`
- access / schedule / domain

这些都在 `POLIRS` 的 `PolyLang` 里。

### 2.3 `ParallelCodegen` 是桥接层

它既需要：

- `ParallelLoop`
- 也需要现有 `PrepareCodegen`

因此最自然的是：

- 在 `POLIRS` functor 里实例化 `ParallelLoop PolIRs.Instr`
- 然后建立桥接 theorem

## 3. `ParallelLoop.v` 的建议骨架

### 3.1 数据结构

建议最小骨架：

```text
Inductive loop_mode := SeqMode | ParMode.

Inductive stmt :=
| Loop  : loop_mode -> option nat -> expr -> expr -> stmt -> stmt
| Instr : instr -> list expr -> stmt
| Seq   : stmt_list -> stmt
| Guard : test -> stmt -> stmt
with stmt_list :=
| SNil
| SCons : stmt -> stmt_list -> stmt_list.

Definition t := (stmt * list ident * list (ident * Ty.t))%type.
```

这里故意尽量贴近现有 `Loop.v`，以减少迁移成本。

这里建议把 `Loop` 节点里的 `option nat` 作为 ghost `origin_dim`：

- `None`
  - 这层 loop 不是由 current dimension 直接产生，或当前阶段无法可靠标识
- `Some d`
  - 这层 loop 对应 `current_view_pprog` 的第 `d` 维

推荐第一版直接把这个 ghost tag 放进 `ParallelLoop`，不要依赖后置 relation 去猜。

原因很简单：

- `parallel_cert` 说的是 current dimension `d`
- codegen 最终必须知道“哪个 emitted loop 节点就是这个 `d`”
- 如果不保留 `origin_dim`，`parallel_cert` 和 emitted `ParMode` loop 之间就没有可证明的连接点

### 3.2 基本函数

建议先定义：

- `erase_stmt : stmt -> Loop.stmt`
- `erase_stmt_list : stmt_list -> Loop.stmt_list`
- `erase_parallel : t -> Loop.t`
- `parallelize_dim_stmt : nat -> stmt -> stmt`
- `parallelize_dim : nat -> t -> t`

其中：

- `erase_parallel`
  - 擦掉 `ParMode`
  - 同时擦掉 `origin_dim`
- `parallelize_dim_stmt d`
  - 只把 `origin_dim = Some d` 的 `SeqMode` loop 改成 `ParMode`

建议最先准备的 trivial lemma 是：

- `erase_parallelize_dim_stmt_eq`
- `erase_parallelize_dim_eq`

推荐直接按下面这种 definitions-only 风格写出来：

```text
Fixpoint parallelize_dim_stmt (d : nat) (s : stmt) : stmt :=
  match s with
  | Loop SeqMode (Some d') lb ub body =>
      Loop (if Nat.eqb d d' then ParMode else SeqMode)
           (Some d')
           lb
           ub
           (parallelize_dim_stmt d body)
  | Loop mode od lb ub body =>
      Loop mode od lb ub (parallelize_dim_stmt d body)
  | Instr i es =>
      Instr i es
  | Guard t body =>
      Guard t (parallelize_dim_stmt d body)
  | Seq ss =>
      Seq (parallelize_dim_stmts d ss)
  end
with parallelize_dim_stmts (d : nat) (ss : stmt_list) : stmt_list := ...
```

其中关键约束是：

- `parallelize_dim_stmt`
  - 只改 `loop_mode`
  - 不改边界、不改 body 结构、不改 `origin_dim`
- 所以后续 `erase_parallelize_dim_eq` 才会是一个非常薄的结构定理

### 3.3 trace 层定义

建议先定义三个纯关系：

- `seq_trace`
- `interleave_family`
- `par_trace`

然后把状态语义定义成：

- `parallel_semantics`

其中：

- `parallel_semantics`
  - 通过 `par_trace`
  - 再交给现有 `instr_point_list_semantics`

### 3.4 第一批结构引理

最先需要的不会是大 theorem，而是基础结构引理：

- `interleave_family_nil`
- `interleave_family_app_left/right`
- `interleave_family_preserves_membership`
- `interleave_family_preserves_subtrace_order`
- `seq_trace_deterministic_shape`
- `erase_parallel_seq_trace_shape`

这些引理会决定后面 theorem 是否好证明。

## 4. `ParallelValidator.v` 的建议骨架

### 4.1 数据结构

建议最小化：

```text
Record parallel_plan := {
  target_dim : nat
}.

Record parallel_cert := {
  certified_dim : nat
}.
```

### 4.2 语义谓词

建议先定义：

- `same_prefix_before`
- `different_dim_at`
- `same_parallel_slice`
- `parallel_safe_dim`
- `parallel_cert_sound`

其中第一版：

- `parallel_cert_sound pp cert := parallel_safe_dim pp cert.(certified_dim)`

完全可以接受。

### 4.3 布尔 checker

建议命名：

- `check_pprog_parallel_currentb`
- `checked_parallelize_current`

风格对齐现有：

- `check_pprog_tiling_sourceb`
- `checked_tiling_validate_poly`

### 4.4 第一批 soundness 定理

建议最先瞄准：

- `check_pprog_parallel_currentb_sound`
- `checked_parallelize_current_sound`
- `checked_parallelize_current_implies_wf_after`

最后一个 theorem 的风格可以参照：

- `checked_tiling_validate_poly_implies_wf_after`

## 5. `ParallelCodegen.v` 的建议骨架

这是最容易在设计上发散的一层，所以建议一开始就把职责收窄。

### 5.1 只做桥接，不重写整个 prepare/codegen

不建议一上来复制 `PrepareCodegen.v` 一整套。

更好的结构是：

1. 继续使用现有：
   - `PrepareCodegen.prepare_codegen`
   - `PrepareCodegen.prepared_codegen`
2. 新增一层：
   - `annotated_codegen`

它的作用是：

- 从 current-view poly program 先拿到顺序 codegen 结果
- 再把 cert 对应的 loop 节点升级成 `ParMode`

如果后面发现“先拿顺序 loop 再注解”证明太绕，再回退成更早插入 annotation 的方案。

### 5.2 建议的核心定义

概念上：

```text
annotated_codegen :
  PolyLang.t -> parallel_cert -> imp ParallelLoop.t
```

这里隐含一个重要定义：

```text
codegen_matches_cert :
  PolyLang.t -> parallel_cert -> ParallelLoop.t -> Prop
```

它表达：

- emitted `ParMode` loop 节点
- 与 cert 上的 current dimension 精确对应

更精确地说，推荐不要把 `annotated_codegen` 直接理解成“在 plain loop 上打标”，而是拆成：

```text
tagged_prepared_codegen :
  PolyLang.t -> imp ParallelLoop.t

annotated_codegen :
  PolyLang.t -> parallel_cert -> imp ParallelLoop.t
```

其中：

- `tagged_prepared_codegen`
  - 生成 `SeqMode` 的 `ParallelLoop`
  - 同时在可识别的 loop 节点上写入 `origin_dim`
- `annotated_codegen pp cert`
  - 先跑 `tagged_prepared_codegen pp`
  - 再执行 `parallelize_dim cert.(certified_dim)`

这样 codegen 与 cert 的连接点就变得非常直接：

- cert 说 “`d` 可并行”
- `origin_dim` 说 “这个 loop 节点就是 `d`”
- `parallelize_dim` 只在这两个条件对齐时打 `ParMode`

推荐再把两个 definitions-only skeleton 写明。

#### 5.2.1 `tagged_prepared_codegen`

```text
tagged_prepared_codegen :
  PolyLang.t -> imp ParallelLoop.t
```

它的实现策略应是：

- 尽量复用现有 `PrepareCodegen.prepared_codegen`
- 但在“生成 loop 节点”的那一层，额外写入 `origin_dim`

proof engineering 上，不建议先从最终 plain `Loop` 反推 tag。

#### 5.2.2 `codegen_matches_current_dims`

推荐先把这个 relation 当成抽象接口，不急着在第一版就做成复杂归纳定义。

概念上它至少应表达：

```text
codegen_matches_current_dims pp pl :=
  every loop node tagged with Some d in pl
  indeed denotes current dimension d of pp
```

若要写成更接近 Coq 的骨架，可以先留成：

```text
Record codegen_matches_current_dims (pp : PolyLang.t) (pl : ParallelLoop.t) : Prop := {
  cmd_wf_origin_dims :
    forall d, tagged_dim_occurs pl d -> d < PolyLang.pprog_current_dim pp;
  cmd_par_nodes_are_tagged :
    forall path,
      par_node_at pl path ->
      exists d, origin_dim_at pl path = Some d
}.
```

第一版完全可以先把它当 theorem target，而不是立刻把所有 path machinery 实现完。

#### 5.2.3 `annotated_codegen`

Definitions-only 版本建议直接写成：

```text
Definition annotated_codegen (pp : PolyLang.t) (cert : parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen pp -;
  pure (parallelize_dim cert.(certified_dim) pl).
```

这样 theorem stacking 会最干净：

- `tagged_prepared_codegen` 负责结构与 tag
- `parallelize_dim` 负责 annotation placement
- `parallel_cert_sound` 负责语义前提

### 5.3 建议的第一批 theorem

建议至少准备：

- `annotated_codegen_matches_cert`
- `annotated_codegen_erase_eq`
- `annotated_codegen_parallel_correct`

其中：

- `annotated_codegen_erase_eq`
  - 负责把新层叠回旧顺序 codegen
- `annotated_codegen_parallel_correct`
  - 负责把 parallel semantics 接到 `PolyLang`

推荐把这三条 theorem 直接写成下面这种形状。

#### 5.3.1 `tagged_prepared_codegen_matches`

```text
Theorem tagged_prepared_codegen_matches :
  forall pp pl,
    WHEN x <- tagged_prepared_codegen pp THEN x = pl ->
    codegen_matches_current_dims pp pl.
```

它负责证明：

- `tagged_prepared_codegen` 写进去的 `origin_dim`
- 确实和 `current_view_pprog` 的维度结构一致

也就是说，之后 theorem 里只要看到某个 `Loop _ (Some d) ...`，就可以把它当成：

- “这是 current dim `d` 的 emitted loop”

#### 5.3.2 `annotated_codegen_erase_eq`

```text
Theorem annotated_codegen_erase_eq :
  forall pp cert pl,
    WHEN x <- annotated_codegen pp cert THEN x = pl ->
    erase_parallel pl =
    erase_parallel (parallelize_dim cert.(certified_dim)
                      (proj_value_of_tagged_prepared_codegen pp)).
```

在正式 Coq 里不一定要用上面这个字面写法，但其语义目标应非常明确：

- 不管 `parallelize_dim` 怎么打 `ParMode`
- 擦掉 annotation 后
- 必须退化回原来的顺序 codegen 结果

如果实现时把 `annotated_codegen` 直接定义成：

- `tagged_prepared_codegen` 后接 `parallelize_dim`

那么这条 theorem 通常会退化成非常简单的结构引理：

- `erase_parallelize_dim_eq`

#### 5.3.3 `parallelize_dim_refines_sequential`

```text
Theorem parallelize_dim_refines_sequential :
  forall pp cert pl st1 st2,
    parallel_cert_sound pp cert ->
    codegen_matches_current_dims pp pl ->
    ParallelLoop.semantics
      (parallelize_dim cert.(certified_dim) pl) st1 st2 ->
    Loop.semantics (erase_parallel pl) st1 st2.
```

这是最关键的一条桥接 theorem。

它的意思不是：

- “parallel codegen 本身 magically correct”

而是：

- 如果 cert 说 current dim `d` 可并行
- 且 codegen 证明某个 emitted loop 节点的 `origin_dim = Some d`
- 那么把那个节点改成 `ParMode` 后的并行语义
- refine 到擦除后的顺序 loop 语义

#### 5.3.4 `annotated_codegen_parallel_correct`

最后再叠到现有 `prepared_codegen_correct_general` 上，得到：

```text
Theorem annotated_codegen_parallel_correct :
  forall pol plan cert pl st1 st2,
    checked_parallelize_current
      (PolyLang.current_view_pprog pol) plan = Okk cert ->
    WHEN x <- annotated_codegen (PolyLang.current_view_pprog pol) cert THEN x = pl ->
    ParallelLoop.semantics pl st1 st2 ->
    PolyLang.instance_list_semantics pol st1 st2.
```

这条 theorem 才是最终要给 `PolOpt` 主 pipeline 消费的接口。

证明顺序应是：

1. `checked_parallelize_current_sound`
2. `tagged_prepared_codegen_matches`
3. `parallelize_dim_refines_sequential`
4. 复用现有 sequential codegen correctness

## 6. 推荐的 theorem dependency order

最容易失败的地方，不是 theorem 难度，而是顺序不对。  
我现在推荐下面这个顺序。

### Step A：先闭 `ParallelLoop` 结构层

先不碰 cert，不碰 poly，不碰 Pluto，只做：

- `erase_parallel`
- `seq_trace`
- `par_trace`
- `parallel_semantics`

以及基础结构引理。

### Step B：再闭 `ParallelValidator` soundness

先得到：

- `parallel_cert_sound`

但此时还不必把它接到 codegen。

### Step C：证明 `par_trace` 与 `seq_trace` 的 stable-permutation 关系

这一步是 parallel semantics 的数学核心。

需要形如：

- `par_trace_implies_stable_permut_of_seq_trace`

### Step D：把 cert soundness 接到 swap soundness

需要形如：

- `parallel_cert_sound_implies_swap_permutable`

### Step E：合成 parallel semantics refinement

最后证明：

- `parallel_semantics_refines_erased_sequential`

### Step F：再接 `prepared_codegen_correct_general`

这一步只是 theorem stacking。

## 7. 最适合先做哪些“伪实现”

在真正开写 Coq 前，建议先做两类纸上骨架。

### 7.1 Definitions-only skeleton

先只写：

- inductives
- records
- function signatures

不急着证明 theorem。

### 7.2 Trivial theorem stubs inventory

先列出 theorem 名称和依赖关系，例如：

- `annotated_codegen_erase_eq` 依赖哪些定义
- `parallel_semantics_refines_erased_sequential` 依赖哪些引理

这会极大减少后续重命名和拆文件成本。

## 8. 与现有 API 风格对齐的建议命名

为了减少未来 API 的认知成本，建议命名尽量贴近当前风格。

### 8.1 validator side

- `check_pprog_parallel_currentb`
- `checked_parallelize_current`
- `checked_parallelize_current_sound`

### 8.2 codegen side

- `annotated_codegen`
- `annotated_codegen_erase_eq`
- `annotated_codegen_parallel_correct`

### 8.3 semantics side

- `parallel_semantics`
- `parallel_semantics_refines_erased_sequential`
- `par_trace`
- `seq_trace`

## 9. 当前最推荐的第一版实现顺序

如果未来要真正改代码，我当前最推荐的顺序是：

1. 新增 `polygen/ParallelLoop.v`
2. 新增 `src/ParallelValidator.v`
3. 先把两边 definitions-only skeleton 写出来
4. 再写 `parallel-semantics` 的基础结构引理
5. 再写 checker soundness
6. 最后新增 `src/ParallelCodegen.v`
7. 最后才接 `driver/PolOpt.v`

这条顺序的核心优势是：

- 它把高冲突主文件留到最后
- 它先把数学对象固定，再接工程 pipeline

## 10. 最后的收束

本文最关键的设计判断是：

> 如果要在当前 PolCert 框架中真正支持 verified `par for`，第一版最稳的 Coq skeleton 应当由三个新模块组成：`ParallelLoop` 负责并行语义，`ParallelValidator` 负责 current-view 上的 checked cert，`ParallelCodegen` 负责把 cert 接到 emitted parallel loop，并把新的并行语义 correctness theorem 叠加到现有顺序 codegen theorem 之上。

## 11. `ParallelLoop.v` definitions-only skeleton

下面这段不是要求现在就能编译，而是建议未来开文件时，优先把接口先写成这个形状。

```text
Module ParallelLoop (IInstr : INSTR).

Module Instr := IInstr.
Module State := Instr.State.
Module Ty := Instr.Ty.
Module Loop := Loop Instr.

Inductive loop_mode := SeqMode | ParMode.

Inductive stmt :=
| Instr : Instr.instr -> list expr -> stmt
| Seq   : stmt_list -> stmt
| Loop  : loop_mode -> option nat -> expr -> expr -> stmt -> stmt
| Guard : test -> stmt -> stmt
with stmt_list :=
| SNil
| SCons : stmt -> stmt_list -> stmt_list.

Definition t := (stmt * list Instr.ident * list (Instr.ident * Ty.t))%type.

Fixpoint erase_stmt (s : stmt) : Loop.stmt := ...
with erase_stmt_list (ss : stmt_list) : Loop.stmt_list := ...

Definition erase_parallel (p : t) : Loop.t := ...

Fixpoint parallelize_dim_stmt (d : nat) (s : stmt) : stmt := ...
with parallelize_dim_stmts (d : nat) (ss : stmt_list) : stmt_list := ...

Definition parallelize_dim (d : nat) (p : t) : t := ...

Inductive event := ...

Definition event_semantics : event -> State.t -> State.t -> Prop := ...

Inductive seq_trace : stmt -> list Z -> list event -> Prop := ...
with seq_traces : stmt_list -> list Z -> list event -> Prop := ...

Inductive interleave_family : list (list event) -> list event -> Prop := ...

Inductive par_trace : stmt -> list Z -> list event -> Prop := ...
with par_traces : stmt_list -> list Z -> list event -> Prop := ...

Definition semantics_aux
  (s : stmt) (env : list Z) (st1 st2 : State.t) : Prop := ...

Inductive semantics : t -> State.t -> State.t -> Prop := ...

Theorem erase_parallelize_dim_stmt_eq : ...
Theorem erase_parallelize_dim_eq : ...
Theorem seq_trace_erases_to_loop_shape : ...
Theorem par_trace_implies_stable_permut_of_seq_trace : ...
Theorem parallel_semantics_refines_erased_sequential : ...

End ParallelLoop.
```

这里有两个刻意保守的点：

- `ParMode` 第一版只在 loop 节点上出现
- `par_trace` 在 `ParMode` 上只允许“跨 iteration 交错，但 iteration 内顺序保持”

这样最容易和现有 `StablePermut` machinery 对上。

## 12. `ParallelValidator.v` definitions-only skeleton

validator 侧建议优先把“辅助谓词”和“checker 输出”分开写。

```text
Module ParallelValidator (PolIRs : POLIRS).

Module Instr := PolIRs.Instr.
Module PolyLang := PolIRs.PolyLang.

Record parallel_plan := {
  target_dim : nat
}.

Record parallel_cert := {
  certified_dim : nat
}.

Definition current_coords_of (ip : PolyLang.InstrPoint_ext) : list Z := ...
Definition same_env_of
  (ip1 ip2 : PolyLang.InstrPoint_ext) : Prop := ...

Definition same_prefix_before
  (d : nat) (ip1 ip2 : PolyLang.InstrPoint_ext) : Prop := ...

Definition different_dim_at
  (d : nat) (ip1 ip2 : PolyLang.InstrPoint_ext) : Prop := ...

Definition same_parallel_slice
  (d : nat) (ip1 ip2 : PolyLang.InstrPoint_ext) : Prop := ...

Definition exec_points_ext_of
  (pp : PolyLang.t) : list PolyLang.InstrPoint_ext := ...

Definition destructive_conflict_ext
  (ip1 ip2 : PolyLang.InstrPoint_ext) : Prop := ...

Definition parallel_safe_dim
  (pp : PolyLang.t) (d : nat) : Prop := ...

Definition parallel_swap_ok
  (pp : PolyLang.t) (d : nat) : Prop := ...

Definition parallel_cert_sound
  (pp : PolyLang.t) (cert : parallel_cert) : Prop :=
  parallel_safe_dim pp cert.(certified_dim).

Definition check_pprog_parallel_currentb
  (pp : PolyLang.t) (plan : parallel_plan) : bool := ...

Definition checked_parallelize_current
  (pp : PolyLang.t) (plan : parallel_plan)
  : result parallel_cert := ...

Theorem check_pprog_parallel_currentb_sound : ...
Theorem checked_parallelize_current_sound : ...
Theorem parallel_cert_sound_implies_parallel_swap_ok : ...

End ParallelValidator.
```

这里最重要的不是 checker 的 OCaml/extraction 细节，而是：

- `parallel_cert_sound`
  - 必须是一个 theorem-friendly 的逻辑谓词
- `parallel_swap_ok`
  - 必须是 semantics 侧可以直接消费的 bridge predicate

## 13. `ParallelCodegen.v` definitions-only skeleton

这一层只做“cert 与 emitted loop 的桥接”，不建议承担新的 polyhedral 分析。

```text
Module ParallelCodegen (PolIRs : POLIRS).

Module Instr := PolIRs.Instr.
Module PolyLang := PolIRs.PolyLang.
Module Loop := PolIRs.Loop.
Module PrepareCodegen := PrepareCodegen PolIRs.
Module ParallelLoop := ParallelLoop Instr.
Module ParallelValidator := ParallelValidator PolIRs.

Definition tagged_prepared_codegen
  (pp : PolyLang.t) : imp ParallelLoop.t := ...

Record codegen_matches_current_dims
  (pp : PolyLang.t) (pl : ParallelLoop.t) : Prop := {
  cmd_wf_origin_dims :
    forall d, tagged_dim_occurs pl d -> d < PolyLang.pprog_current_dim pp;
  cmd_par_nodes_are_tagged :
    forall path,
      par_node_at pl path ->
      exists d, origin_dim_at pl path = Some d
}.

Definition annotated_codegen
  (pp : PolyLang.t)
  (cert : ParallelValidator.parallel_cert)
  : imp ParallelLoop.t :=
  BIND pl <- tagged_prepared_codegen pp -;
  pure (ParallelLoop.parallelize_dim cert.(ParallelValidator.certified_dim) pl).

Theorem tagged_prepared_codegen_matches : ...
Theorem annotated_codegen_erase_eq : ...
Theorem parallelize_dim_refines_sequential : ...
Theorem annotated_codegen_parallel_correct : ...

End ParallelCodegen.
```

这里 `tagged_dim_occurs` / `par_node_at` / `origin_dim_at` 完全可以先作为抽象 helper 留空。  
第一版只需要它们足够支持 theorem statement，不需要一开始就把 path API 做得很漂亮。

## 14. 最小可开工版本

如果下一阶段真的开始写 Coq，我现在建议的最小可开工版本就是：

1. 先把第 11 节直接翻成 `ParallelLoop.v`
2. 再把第 12 节直接翻成 `ParallelValidator.v`
3. 两边先只留 `Admitted` / theorem stubs
4. 最后再把第 13 节翻成 `ParallelCodegen.v`

也就是说，真正的开工顺序仍然应该是：

- 先定义语义对象
- 再定义 cert 对象
- 最后才定义 cert 如何被 codegen 消费

这样就不会在主 pipeline 上边改边猜接口。
