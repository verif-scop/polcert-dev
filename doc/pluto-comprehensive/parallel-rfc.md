# Parallel RFC

本文是当前 parallel 设计的冻结版决策 memo。

它的目标不是替代前面的细节笔记，而是把第一版需要拍板的事项一次性定清楚，作为后续真正实现时的单一入口。

如果只看一份文件，请优先看本文。

## 1. 第一版范围

第一版 verified parallel 只做下面这些：

- single-dim `par for`
- 只在当前主线 `iss -> affine -> tiling` 的 tiling 之后尝试
- Pluto 只负责 parallel-aware transform search
- PolCert 自己 checked 地 cert current-view 上的 candidate dimension
- 最终 `par for` 的抽象并行语义本身被证明 refine 到顺序语义

第一版明确不做：

- `multipar`
- nested parallel
- `vector`
- `private` / reduction clause 的完整形式化
- 直接 trust Pluto `<loop>` extension

## 2. 冻结版总体判断

### 2.1 Pluto 的角色

Pluto 的 `--parallel` 不是“最后打 pragma”，而是会影响 schedule / tile-schedule 搜索。

因此 Pluto 在这里的职责是：

- 生成更并行友好的 `after.scop`
- 可选提供 `<loop>` hint

但 Pluto 不是 proof object。

### 2.2 PolOpt 与 PolCert 的角色

第一版职责切分固定如下：

- `PolOpt`
  - 接受用户 `--parallel`
  - 在第二次 Pluto 调用上传递 `--tile --parallel`
  - 选择 candidate dimension
  - 调用 checked cert
  - 让最终 codegen 输出 `par for`

- `PolCert`
  - 只负责 cert
  - 不负责启发式选择
  - 不直接相信 Pluto hint
  - 必须支撑 `par for` 语义本身的 correctness theorem

### 2.3 parallel phase 的位置

parallel 不是和 tiling 并列的新主 route。  
它在第一版的固定位置是：

```text
... -> checked_tiling_validate_poly
-> current_view_pprog
-> checked_parallelize_current
-> annotated_codegen
```

也就是说：

- transform correctness 先闭合
- parallel cert 后置在 current-view 之后
- codegen 最后消费 cert

## 3. 冻结版 IR 选择

第一版固定选择：

- 新增 `ParallelLoop`
- 不直接大改现有 `Loop`

理由：

- 能最小化对现有顺序 theorem 栈的扰动
- `ParallelLoop` 可以携带 parallel-specific ghost info
- 便于把 parallel theorem 叠加到现有 `Loop` theorem 之上

### 3.1 关键结构

`ParallelLoop` 的核心建议固定为：

```text
Inductive loop_mode := SeqMode | ParMode.

Inductive stmt :=
| Instr : ...
| Seq   : ...
| Loop  : loop_mode -> option nat -> expr -> expr -> stmt -> stmt
| Guard : ...
```

这里 `option nat` 是 ghost `origin_dim`。

冻结版约束：

- `Some d`
  - 该 loop 节点对应 current-view 的第 `d` 维
- `ParMode` 第一版只出现在 `Some d` 上
- 第一版不允许 emitted `ParMode None`

### 3.2 为什么必须有 `origin_dim`

这是第一版最关键的工程决定之一。

原因是：

- `parallel_cert` 说的是 poly/current-view 上的第 `d` 维 safe
- codegen 最终必须精确知道“哪个 emitted loop 节点就是这个 `d`”

没有 `origin_dim`，证书和最终 loop 节点之间没有可证明连接点。

## 4. 冻结版语义定义

### 4.1 核心原则

`par for` 语义不是：

- any permutation of flattened instruction sequence

而是：

- 各次 iteration body 先各自产生顺序 trace
- 允许这些 iteration traces 做保每个 iteration 内部顺序的 interleaving

### 4.2 第一版 `ParMode`

第一版 `ParMode` 固定为：

- 对每个 iteration `x`
  - 用 `seq_trace body (x :: env)` 产生子 trace
- 再用 `interleave_family` 合并这些子 traces

第一版刻意不递归 `par_trace body`，原因是：

- 不做 nested parallel
- 让语义主定理聚焦在“单层 parallel region 的合法 interleaving”

### 4.3 `interleave_family`

第一版建议直接用归纳定义：

```text
IF_nil
IF_skip_nil
IF_take
```

并优先证明：

- `interleave_family_preserves_membership`
- `interleave_family_preserves_subtrace_order`
- `interleave_family_concat_stable_permut`

## 5. 冻结版 checker 定义

checker 工作对象固定为：

```text
pp_cur := current_view_pprog pol_after
```

不是 source loop，不是 raw OpenScop，也不是 final Loop AST。

### 5.1 first-version predicate

第一版采用保守定义：

- 固定 candidate dim `d`
- 固定 outer prefix `< d`
- 在同一个 parallel slice 内
- 不允许不同 `d`-iteration 之间出现 destructive conflict

也就是：

- 排除 `WW/WR/RW`
- `RAR` 不算冲突

### 5.2 checker 输出

冻结版接口固定为：

```text
Record parallel_plan := { target_dim : nat }.
Record parallel_cert := { certified_dim : nat }.

check_pprog_parallel_currentb :
  PolyLang.t -> parallel_plan -> bool

checked_parallelize_current :
  PolyLang.t -> parallel_plan -> result parallel_cert
```

并要求有：

```text
checked_parallelize_current_sound
```

其结论至少给出：

```text
parallel_cert_sound pp cert
```

## 6. 冻结版 codegen 连接方式

这是这轮设计里真正被钉死的桥接方案。

### 6.1 两阶段 codegen

第一版固定拆成两层：

```text
tagged_prepared_codegen :
  PolyLang.t -> imp ParallelLoop.t

annotated_codegen :
  PolyLang.t -> parallel_cert -> imp ParallelLoop.t
```

其中：

- `tagged_prepared_codegen`
  - 生成全 `SeqMode` 的 `ParallelLoop`
  - 同时把 `origin_dim` 写好

- `annotated_codegen pp cert`
  - 先跑 `tagged_prepared_codegen pp`
  - 再执行 `parallelize_dim cert.(certified_dim)`

### 6.2 设计理由

不能靠 printer hack，也不应靠 post-pass 猜 loop 身份。  
必须让 cert 成为 codegen 的显式输入。

否则就没法证明：

- poly/current-view 上 cert 的那个 `d`
- 正是最终变成 `ParMode` 的那层 loop

## 7. 冻结版 theorem stack

第一版 theorem layering 固定为：

1. 现有 transform correctness
   - `validate_correct`
   - `checked_tiling_validate_correct`
2. 现有 current-view bridge
   - `instance_list_semantics_current_view_iff`
3. 新 checker soundness
   - `checked_parallelize_current_sound`
4. 新 semantics bridge
   - `par_trace_implies_stable_permut_of_seq_trace`
   - `parallel_cert_sound_implies_parallel_swap_ok`
   - `parallel_swap_ok_implies_swap_permutable`
   - `parallel_semantics_refines_erased_sequential`
5. 现有 sequential codegen correctness
   - `prepared_codegen_correct_general`
6. 新 final composition
   - `annotated_codegen_parallel_correct`

### 7.1 最关键的 theorem

最关键的不是 printer 或 CLI，而是这三条：

- `interleave_family_concat_stable_permut`
- `parallelize_dim_refines_sequential`
- `annotated_codegen_parallel_correct`

这三条决定：

- 并行语义是否真的被证
- cert 与 codegen 是否真的接上
- 最终 theorem 是否能回到 `PolyLang.instance_list_semantics`

## 8. 冻结版实现顺序

实现顺序现在也固定了，不再建议反复调整：

1. 新增 `polygen/ParallelLoop.v`
2. 新增 `src/ParallelValidator.v`
3. 先写 definitions-only skeleton
4. 先闭 `interleave_family` 结构引理
5. 再闭 `checked_parallelize_current_sound`
6. 再闭 `par_trace_implies_stable_permut_of_seq_trace`
7. 再闭 `parallel_semantics_refines_erased_sequential`
8. 最后新增 `src/ParallelCodegen.v`
9. 最后才接 `driver/PolOpt.v` / `driver/Scheduler.ml`

一句话：

- 先定义语义对象
- 再定义 cert
- 最后才让 codegen 消费 cert

## 9. 共享文件改动边界

在真正开始实现之前，低冲突文件固定为：

- `doc/pluto-comprehensive/parallel-*.md`
- `work/container-overlay/polcert/polygen/ParallelLoop.v`
- `work/container-overlay/polcert/src/ParallelValidator.v`
- `work/container-overlay/polcert/src/ParallelCodegen.v`

高冲突文件固定为：

- `work/container-overlay/polcert/driver/PolOpt.v`
- `work/container-overlay/polcert/driver/Scheduler.ml`
- `work/container-overlay/polcert/src/PrepareCodegen.v`
- `work/container-overlay/polcert/polygen/CodeGen.v`
- `work/container-overlay/polcert/syntax/SLoopMain.ml`
- `work/container-overlay/polcert/syntax/SLoopPretty.ml`

冻结版建议是：

- 在 parallel semantics 与 checker theorem 没稳定之前，不碰高冲突文件

## 10. 仍保留的最小开放问题

第一版只保留两个真正还算开放的问题：

1. `codegen_matches_current_dims` 最终用 path-based relation 还是更轻的 structural relation 表达
2. `parallel_swap_ok` 是否直接定义到足以推出 `Permutable_ext`，还是保留一层更弱谓词

除此之外，第一版的大方向已经不再开放。

## 11. 后续规则

从这份 memo 开始，parallel 设计侧不再继续发散成更多 sibling notes。  
如果后续实现改变了设计，应优先更新：

1. 本文
2. `parallel-coq-skeleton.md`
3. `parallel-proof-obligation-checklist.md`
4. `parallel-implementation-staging.md`

只有在出现新的 proof boundary 时，才应再开新文档。
