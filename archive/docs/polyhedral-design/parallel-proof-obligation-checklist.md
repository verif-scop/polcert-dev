# Parallel Proof Obligation Checklist

本文把 parallel 支持需要新增的证明义务压成一份 checklist。

它的目的不是解释设计背景，而是回答非常直接的问题：

1. 到底有哪些 theorem 必须新增
2. 哪些 theorem 可以直接复用现有资产
3. 哪些 theorem 是高风险项
4. 哪些 theorem 必须先做，哪些可以后做

## 1. 已有可直接复用的 theorem / machinery

parallel 这条线不是从零开始。下面这些现有资产是明确可以复用的。

### 1.1 current-view / transform correctness

可直接复用：

- `validate_correct`
- `checked_tiling_validate_correct`
- `instance_list_semantics_current_view_iff`
- `prepared_codegen_correct_general`

它们已经负责：

- affine / tiling transform correctness
- current-view bridge correctness
- sequential codegen correctness

parallel 新证明不应重做这些内容。

### 1.2 instruction-point 执行语义

在 `polygen/InstanceListSema.v` 中已有：

- `instr_point_list_semantics`
- `instr_point_list_sema_stable_under_state_eq`
- `instr_point_list_sema_concat`

这意味着：

- 新 parallel semantics 完全不需要重写 instruction execution semantics
- 只需要定义允许哪些 traces

### 1.3 stable permutation equivalence pattern

在 `src/PolyLang.v` 中已有：

- `stable_permut_step_ext_lists_are_equivalent`
- `stable_permut'_ext_lists_are_equivalent`
- `stable_permut_ext_lists_are_equivalent`

这些定理的核心作用是：

- 如果一组 swap 都满足可交换性
- 那么 stable permutation 前后语义等价

parallel 这条线最值得复用的就是这种证明模式。

### 1.4 sequential loop 到 trace 的桥

在 `polygen/Loop.v` 中已有：

- `loop_instance_list_semantics_implies_instr_point`

它说明：

- 顺序 loop 语义可以落到 instruction-point list 语义上

这让新 parallel 语义与旧顺序 loop 语义之间存在天然桥接点。

## 2. 第一版必须新增的 theorem 组

按模块分，大致分成五组。

### Group A：`ParallelLoop` 结构层

这些 theorem 主要是为了让语义对象本身可用。

#### A1. `erase_parallel` 基本性质

至少需要：

- `erase_parallel` 保持变量上下文和 program wrapper
- `erase_parallel` 在 loop 结构上只擦除 annotation，不改控制骨架

#### A2. `seq_trace` 基本性质

至少需要：

- `seq_trace` 的 determinism / shape lemmas
- `seq_trace` 对 `erase_parallel` 的一致性

#### A3. `interleave_family` 基本性质

至少需要：

- preserving membership
- preserving per-subtrace order
- app/cons decomposition lemmas
- concat / flatten relationship

更具体地说，我建议第一版至少准备下面这些小引理：

- `interleave_family_preserves_membership`
- `interleave_family_preserves_subtrace_order`
- `interleave_family_skip_nil`
- `interleave_family_take_inv`
- `interleave_family_concat_stable_permut`

这些是之后证明 stable permutation 的前提。

### Group B：`ParallelValidator` soundness

这些 theorem 保证 cert 不是空壳。

#### B1. 维度合法性

至少需要：

- `checked_parallelize_current` 成功时，`certified_dim` 在 current-dim 范围内

#### B2. soundness 主定理

至少需要：

- `check_pprog_parallel_currentb_sound`
- `checked_parallelize_current_sound`

结论至少给出：

- `parallel_cert_sound`

#### B3. `parallel_cert_sound` 展开后应是 usable predicate

第一版推荐直接定义成：

- `parallel_safe_dim pp d`

否则后续 theorem 会难以使用。

### Group C：`par_trace` 与顺序 trace 的关系

这是 parallel semantics 的数学核心。

#### C1. `par_trace` preserves elements

至少需要：

- `par_trace` 生成的 trace 与对应 `seq_trace` 拥有相同元素多重集

#### C2. `par_trace` induces stable permutation

这是关键 theorem：

- `par_trace_implies_stable_permut_of_seq_trace`

它的作用是把“任意保序 interleaving”转成现有 `StablePermut` machinery 能吃的形式。

这一组 theorem 最自然的内部顺序是：

1. `interleave_family_concat_stable_permut`
2. `par_trace_implies_stable_permut_of_seq_trace`

不要一上来直接攻第 2 条。

### Group D：从 cert soundness 到 swap soundness

这是 parallel checker 与 parallel semantics 的接口层。

#### D1. `parallel_cert_sound` 推出 allowed swap 安全

至少需要：

- `parallel_cert_sound_implies_parallel_swap_ok`

#### D2. `parallel_swap_ok` 推出可交换性

若第一版 checker 用保守 no-conflict 定义，则这一步可以先证明成：

- `parallel_swap_ok -> Permutable`

或者直接给出足以驱动 stable-permutation preservation 的更专门 lemma。

这里建议显式再拆一层：

- `parallel_safe_dim -> parallel_swap_ok`
- `parallel_swap_ok -> Permutable_ext`

这样 validator 定义变动时，语义 theorem 不必整体重写。

### Group E：parallel semantics refinement

这是最终必须成立的强 theorem。

#### E1. 单 statement / trace 层

至少需要：

- `parallel_trace_refines_seq_trace`

或等价形式：

- `parallel_semantics_refines_erased_sequential`

#### E2. program 层

最后应得到：

- 带 cert 的 `ParallelLoop.parallel_semantics`
- refine 到 `Loop.semantics (erase_parallel ...)`

这一步完成后，才能与现有 `prepared_codegen_correct_general` 合成。

## 3. 可以暂时延后的 theorem

以下内容不是第一版 blocker。

### 3.1 Pluto hint correctness

不需要证明：

- Pluto `<loop>` hint 为什么对

hint 只影响 candidate 选择，不影响 cert correctness。

### 3.2 nested parallel correctness

第一版可以完全不做：

- multipar
- nested `ParMode`

### 3.3 vector / private clause 相关 theorem

这些都应晚于 single-dim `par for`。

## 4. 建议的 milestone 划分

为了避免 theorem 过早耦合，建议按里程碑切。

### Milestone 1：语义对象可定义

完成标准：

- `ParallelLoop` 数据结构
- `erase_parallel`
- `seq_trace`
- `par_trace`
- `interleave_family`

但不要求和 `PolyLang` 接起来。

### Milestone 2：checker 可 sound

完成标准：

- `parallel_plan`
- `parallel_cert`
- `check_pprog_parallel_currentb`
- `checked_parallelize_current_sound`

但不要求 codegen integration。

### Milestone 3：trace-level refinement 闭合

完成标准：

- `par_trace_implies_stable_permut_of_seq_trace`
- `parallel_cert_sound_implies_parallel_swap_ok`
- `parallel_semantics_refines_erased_sequential`

这时已经可以说：

- `par for` 语义本身被证明 refine 到顺序 loop 语义

### Milestone 4：pipeline integration

完成标准：

- `annotated_codegen`
- `annotated_codegen_erase_eq`
- 与 `prepared_codegen_correct_general` 合成

这时才真正进入主 pipeline。

## 5. 高风险项

并不是所有 theorem 风险都一样。  
我当前判断下面三项是最高风险。

### Risk 1：`par_trace_implies_stable_permut_of_seq_trace`

这是数学上最关键也最容易低估的一步。

风险来源：

- `interleave_family` 如果定义得不好
- 很容易让 stable permutation 的归纳变得难用

建议：

- 先把 `interleave_family` 的结构引理做厚
- 先单独证明 `interleave_family_concat_stable_permut`
- 再碰这个 theorem

### Risk 2：`parallel_cert_sound` 到 `Permutable` 的桥接

如果 checker 定义过强或过弱，这一步都会很别扭。

建议：

- 第一版先用保守 no-destructive-conflict 定义
- 不要一开始就追求 fully general `Permutable_ext`

### Risk 3：`codegen_matches_cert`

即使 parallel semantics 与 checker 都成立，如果 emitted loop 节点和 cert 维度对不上，整个 theorem 也接不起来。

建议：

- 在 `ParallelLoop` 节点里显式存 current origin dimension
- 不要依赖 post-pass 猜测 loop 身份

## 6. 低风险项

下面这些通常只是机械劳动。

### 6.1 wrapper / erase theorem

例如：

- `annotated_codegen_erase_eq`

只要表示层设计清楚，通常不难。

### 6.2 API re-export

例如：

- 在 `src/Validator.v` 增加 alias

这只是接口一致性工作。

### 6.3 CLI plumbing 文档化

例如：

- `--parallel` 开关如何进入 `Scheduler.ml`

不属于数学风险。

## 7. 建议的证明顺序

从 proof engineering 角度，我建议严格按下面顺序推进。

### Step 1

先完成：

- `ParallelLoop` definitions-only skeleton

### Step 2

先证明：

- `interleave_family` 的基础引理
- `interleave_family_concat_stable_permut`

### Step 3

再完成：

- `ParallelValidator` soundness

### Step 4

再证明：

- `par_trace_implies_stable_permut_of_seq_trace`

### Step 5

再证明：

- `parallel_cert_sound_implies_parallel_swap_ok`
- `parallel_swap_ok -> semantics-preserving swap`

### Step 6

合成：

- `parallel_semantics_refines_erased_sequential`

### Step 7

最后才做：

- `annotated_codegen`
- pipeline integration

## 8. 建议的验收标准

如果要说“第一版 parallel proof 线基本闭合”，我建议至少满足下面三条。

### 8.1 语义验收

存在明确定义的：

- `ParallelLoop.parallel_semantics`

而且它允许真实 interleaving。

### 8.2 checker 验收

存在明确 soundness theorem：

- `checked_parallelize_current_sound`

### 8.3 合成验收

存在最终 theorem：

- `ParallelLoop.parallel_semantics`
  refine 到
- `PolyLang.instance_list_semantics`

在 single-dim `par for` 前提下成立。

## 9. Proof Script Roadmap

这一节不再讨论“应该证明什么”，而是直接回答：

- 先写哪条 theorem
- 每条 theorem 最值得复用哪些现有引理
- 哪些 theorem 应当先拆小再合成

### 9.1 `interleave_family` 基础引理

建议最先完成：

- `interleave_family_preserves_membership`
- `interleave_family_preserves_subtrace_order`
- `interleave_family_skip_nil`
- `interleave_family_take_inv`

推荐 proof shape：

- 对 `interleave_family` 本身做归纳
- 不要过早引入 `StablePermut`
- 先把 list-level inversion / decomposition 引理做够

这一组 theorem 的目标是：

- 让后面的 `concat` / stable-permutation 证明有足够的结构信息可用

### 9.2 `interleave_family_concat_stable_permut`

这是第一条真正接到 `StablePermut` 的 theorem。

建议优先复用的现有 low-level 构造子有：

- `stable_permut_swap`
- `stable_permut_skip`
- `stable_permut_intro`
- `stable_permut_trans`
- `stable_permut_step_implies_stable_permut`

推荐 proof shape：

1. 对 `interleave_family` 归纳
2. `IF_skip_nil`
   - 主要是列表结构整理
3. `IF_take`
   - 通过一串局部 swap，把新取出的元素移到前面
   - 再用 transitivity 合成

这一条 theorem 一旦成立，后面就不再需要直接对 `interleave_family` 的 operational shape 做复杂归纳。

### 9.3 `par_trace_implies_stable_permut_of_seq_trace`

推荐依赖：

- `interleave_family_concat_stable_permut`
- `seq_trace` 的 canonical-shape lemma
- `erase_parallel` / `seq_trace` 对齐 lemma

推荐 proof shape：

- 对 `par_trace` 归纳
- 非 `ParMode` case 基本是结构同态
- `ParMode` case
  - 先对每个 iteration body 得到 canonical `seq_trace`
  - 再用 `interleave_family_concat_stable_permut`
  - 最后得到整个 loop trace 的 stable permutation

这里不要试图直接从最终 trace 跳到 `PolyLang` semantics；  
先停在 `StablePermut` 上，证明会干净很多。

### 9.4 `checked_parallelize_current_sound`

这一条 theorem 主要是 checker soundness，本身不依赖 codegen。

推荐依赖：

- `wf_pprog_general`
- emptiness-check soundness
- `same_prefix_before` / `same_parallel_slice` 的 helper 定义

推荐 proof shape：

- 先证明单个 bad-example polyhedron 的 soundness
- 再证明“所有坏例子都空”推出 `parallel_safe_dim`
- 最后包装成 `parallel_cert_sound`

### 9.5 `parallel_cert_sound_implies_parallel_swap_ok`

这是 validator 与 semantics 的第一条真正接口 theorem。

推荐依赖：

- `checked_parallelize_current_sound`
- `parallel_safe_dim` 的定义展开

推荐 proof shape：

- 直接 unfold `parallel_cert_sound`
- 对任意满足 `same_parallel_slice` 的 pair
- 用 `parallel_safe_dim` 排除 destructive conflict
- 得到 `parallel_swap_ok`

这一层 theorem 最好保持非常薄。  
它的价值在于把 checker 的定义改动和后面的 semantics theorem 解耦。

### 9.6 `parallel_swap_ok_implies_swap_permutable`

推荐依赖：

- `Permutable_ext`
- `Permutable_ext_symm`
- `parallel_swap_ok`

推荐 proof shape：

- 把 `parallel_swap_ok` 定义成足够接近 `Permutable_ext` 的桥接谓词
- 这样这条 theorem 可以尽量变薄

如果这里证明开始发散，通常说明：

- `parallel_swap_ok` 定义得不够贴近最终 theorem 需求

### 9.7 `parallel_semantics_refines_erased_sequential`

这是语义主定理。

推荐依赖：

- `par_trace_implies_stable_permut_of_seq_trace`
- `parallel_cert_sound_implies_parallel_swap_ok`
- `parallel_swap_ok_implies_swap_permutable`
- `stable_permut_step_ext_lists_are_equivalent`
- `stable_permut'_ext_lists_are_equivalent`
- `stable_permut_ext_lists_are_equivalent`

推荐 proof shape：

1. 从 `ParallelLoop.parallel_semantics` 取出一个 `par_trace`
2. 用 `par_trace_implies_stable_permut_of_seq_trace` 得到对应 canonical `seq_trace`
3. 用 `parallel_cert_sound_implies_parallel_swap_ok` 和
   `parallel_swap_ok_implies_swap_permutable`
   说明这些 swaps 都满足 `Permutable_ext`
4. 直接调用现有 stable-permutation equivalence theorem
5. 得到擦除后的顺序语义

### 9.8 `annotated_codegen_parallel_correct`

这是最终叠 theorem 的阶段。

推荐依赖：

- `tagged_prepared_codegen_matches`
- `parallelize_dim_refines_sequential`
- `annotated_codegen_erase_eq`
- `prepared_codegen_correct_general`
- `instance_list_semantics_current_view_iff`

推荐 proof shape：

1. checker soundness 给出 `parallel_cert_sound`
2. codegen matching 给出 emitted loop 与 current dim 对齐
3. 用 `parallelize_dim_refines_sequential` 压回顺序 `Loop`
4. 用现有 `prepared_codegen_correct_general` 接回 `PolyLang.instance_list_semantics`

## 10. 最容易复用的现有小引理

除了上面那些大 theorem，下面这些现有小引理我认为最值得优先记住：

- `instr_point_list_semantics_singleton_inv`
- `instr_point_list_semantics_nil_inv`
- `instr_point_list_semantics_app_inv`
- `iter_semantics_app`
- `loop_instance_list_semantics_implies_loop_semantics`

这些都已经在当前开发里被大量使用。  
parallel 这条线做 trace 拼接和 loop 结构归纳时，复用它们通常比重写列表/语义分解引理更省力。

## 11. 最后的收束

这份 checklist 最重要的作用，是把 parallel 支持从“很多好想法”压成：

- 哪些 theorem 是必须新增的
- 哪些 theorem 只是后续增强
- 哪些 theorem 风险最高
- 哪些 theorem 必须先做

如果后面真的开始实现，我建议直接以这份 checklist 为 proof task 顺序，而不是边写边决定顺序。
