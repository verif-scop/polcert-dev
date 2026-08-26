# Parallel Proof Strategy

本文专门整理“PolCert 真正支持 `parallel for` 时，正确性到底要证明什么，以及证明边界应如何组织”。

它回答的不是 Pluto 怎么产生 parallel 候选，而是：

1. 如果最终输出里真的出现 `parallel for`，并发本身要如何被证明。
2. 这个证明应该落在 polyhedral 表示、codegen loop 表示、还是两者之间。
3. 现有 `validate_correct` / `checked_tiling_validate_correct` / `prepared_codegen_correct_general` 能复用多少。

本文默认当前主线仍是：

```text
Loop
-> extractor
-> strengthen
-> affine
-> tiling
-> checked_tiling_validate
-> current_view_pprog
-> codegen
```

parallel 的问题是：要不要在这条主线上再插入一个“并发正确性”层，以及这个层的 theorem 该长什么样。

## 1. 先说结论

最核心的结论有五条。

### 1.1 `par for` 语义本身必须是 verified

如果最终目标写成“verified parallel for”，那么 theorem 边界里必须真的包含：

- `par for` 自身的并行语义

而不能只包含：

- 一个带并行标记的 AST
- 或一个擦除后退化成顺序 `for` 的表示层

因此，下面整份设计默认都在追求更强的目标：

- `par for` 语义本身被形式化
- `par for` 语义本身被证明 refine 到顺序语义

### 1.2 只做 annotation-erasure semantics 不够

如果只是把最终 loop 标成 `parallel for`，然后在语义里把这个标注擦掉，当成普通顺序 `for`，那么我们只证明了：

- “这个带标注的程序擦除后和原顺序程序一致”

但没有证明：

- 不同迭代真的可以并发
- 任意 worksharing / interleaving 不改变结果

所以如果目标是“PolCert cert 了 parallelization 本身”，仅有 erasure theorem 不够。

### 1.3 并发正确性不应该在最终 Loop AST 上重新做 dependence analysis

parallel-safe 的判断需要：

- domain
- current-space dimensions
- access relations
- statement-level dependence structure

这些都在 `current_view_pprog` 之后的 `PolyLang` 表示里最完整。

最终 `Loop` AST 已经不再适合做新的 dependence reasoning。  
因此：

- `parallel-safe` 的 cert 应在 `current_view_pprog` 上做
- `parallel for` 的语法落地发生在 codegen loop 上

### 1.4 正确的结构是“双层证明”

推荐把 parallel proof 拆成两层：

1. `PolyLang` 层的 parallel-safety certification
   - 证明某个 current-space loop 维度是 safe 的
2. `Loop` / codegen 层的 parallel semantics refinement
   - 证明带 parallel 标注的 loop 抽象并行语义 refine 到原顺序 loop 语义

再把这两层和现有 sequential codegen theorem 串起来。

### 1.5 最值得复用的现有资产是 `StablePermut`

当前 affine/general validator 已经不是在做“朴素 dependency emptiness”，而是在做：

- 对可能反转的 instruction-point pairs
- 证明 `Permutable_ext`
- 用 `StablePermut` 推 whole-program semantics preservation

parallel 的本质也是“某些 instruction-point pairs 允许失序/交换”。  
因此它最自然的证明路线不是另起炉灶，而是把当前的 pairwise-permutability machinery 从：

- “after schedule 相对 before 反转了哪些 pairs”

推广到：

- “某个 parallel dimension 内，哪些 pairs 可能在 runtime 下失序”

### 1.6 codegen theorem 可以大量复用，但要增加一个 parallel 语义层

理想的 theorem 组合不是“重写整个 codegen correctness”，而是：

1. 现有 theorem 继续证明顺序 loop code 正确
2. 新 theorem 证明：
   - 如果 parallel cert sound
   - 那么 annotated loop 的抽象并行语义 refine 到其顺序擦除版本
3. 两者合成得到：
   - annotated parallel loop 的抽象并行语义 refine 到 `PolyLang` semantics

这会比直接重证一遍完整 codegen 轻很多。

## 2. 需要区分的三个问题

parallel 一旦进入 verified pipeline，必须区分三件事。

### 2.1 transform correctness

这是现有系统已经在做的：

- affine schedule 合法
- tiling 合法
- `current_view_pprog` 不改变语义

这部分由现有 theorem 支撑：

- `src/AffineValidator.v` 中的 `validate_correct`
- `src/TilingValidator.v` 中的 `checked_tiling_validate_correct`
- `src/PolyLang.v` 中的 `instance_list_semantics_current_view_iff`

### 2.2 parallel-safety correctness

这是新增部分：

- 给定一个已经 validated 的 current-space program
- 某个 loop dimension 是否真的能并行

这一步和 Pluto 的启发式选择无关。  
Pluto 只负责找 schedule；是否 parallel-safe，要由 PolCert 自己 checked。

### 2.3 parallel codegen correctness

这是另一新增部分：

- 最终 codegen 输出的带 parallel 标注 loop
- 其抽象并行语义是否仍然 refine 到 current-space poly semantics

这一步不能偷换成“打印器加 pragma”。

## 3. 现有主线里可复用的 proof asset

当前系统已经有四块非常适合 parallel 复用的资产。

### 3.1 `validate_correct`

`src/AffineValidator.v` 的 `validate_correct` 已经证明：

- 如果 checker 通过
- target program 的 instance-list semantics refine 到 source program

关键是它并不依赖“schedule 完全一致”，而是依赖：

- 可能失序的 pairs 要么无冲突
- 要么 `Permutable_ext`

这正是 parallel checker 以后要复用的核心模式。

### 3.2 `checked_tiling_validate_correct`

`src/TilingValidator.v` 已经提供：

- witness/structure check
- canonical after import
- generic validate

因此并不需要把 parallel 混进 tiling witness。  
更合理的是：

- 先让 tiling 自己闭合
- 再在 `current_view_pprog after` 上做 parallel cert

### 3.3 `instance_list_semantics_current_view_iff`

`src/PolyLang.v` 中的 `instance_list_semantics_current_view_iff` 已经说明：

- current-view 只是表示转换
- 不改变 `instance_list_semantics`

这让 parallel cert 可以坚定地落在 current-view 上，而不用碰 witness-centered internal form。

### 3.4 `prepared_codegen_correct_general`

`src/PrepareCodegen.v` 的 `prepared_codegen_correct_general` 已经给出：

- 对 `current_view_pprog pol`
- 当前顺序 codegen 得到的 `Loop` 程序语义
- refine 到原 `PolyLang` semantics

这意味着：

- 我们不想破坏这条 theorem
- 最好的 parallel proof 是建立在它之上，而不是替换它

## 4. 为什么“只给 Loop 加一个 `par` 标志”在证明上不够

如果只改 AST，语义不变，那么：

- AST 确实能打印 `parallel for`
- 但 theorem 依然只在证明顺序执行

所以这里至少需要新增一种“并发可观察”的语义层。

### 4.1 annotation-erasure theorem 的真实地位

它仍然有用，但只能证明：

- 新 IR 不会破坏老的顺序 theorem

它的作用是：

- 降低 proof engineering 风险
- 帮助逐步迁移 codegen / cleanup / pretty-printer

它不能作为“parallel correctness 已经完成”的终点。

### 4.2 真正需要补的是 abstract parallel semantics

完整 OpenMP runtime semantics 很重，但没有必要一开始就 formalize 到那个粒度。

第一版更合理的是定义：

- 抽象的 `parallel for` 语义
- 覆盖 worksharing / iteration interleaving
- 但不去建模线程 API、runtime 库、private clause 实现细节

也就是说，先证明“这一层迭代可以并发且结果不变”，而不是先证明整个 OpenMP 运行时。

这里要强调：

- 抽象 parallel semantics 仍然是“真的并行语义”
- 它不是一个仅供打印使用的 annotation semantics
- 它必须允许某种非顺序 interleaving / reordering
- 然后再被证明 refine 到顺序语义

## 5. 推荐的语义分层

我现在更推荐下面这个分层。无论选哪种 IR 方案，都必须满足：

- `par for` 自身的语义是形式化定义并被证明 sound 的
- 不能把“verified”停留在顺序擦除语义

### 5.1 保留现有顺序 `Loop` 语义

当前 `polygen/Loop.v` 里的：

- `Loop.loop_semantics`
- `loop_instance_list_semantics`

继续保留，不动它的核心 meaning。

这条线仍然服务于：

- 现有 `prepared_codegen_correct_general`

### 5.2 新增一个 parallel-aware loop 层

这里有两种工程选择。

#### 方案 A：直接扩展 `Loop`

例如概念上：

```text
Loop ann origin_dim lb ub body
```

其中：

- `ann = Seq | Par`
- `origin_dim` 记录这层 loop 对应的 current-space 维度

优点：

- IR 统一
- pretty-printer 最自然

缺点：

- 旧的 `Loop` 引理会被大面积机械改动

#### 方案 B：引入一个新的 `ParallelLoop`

也就是：

- 保留现有 `Loop`
- 新增 `ParallelLoop`
- 定义 `erase_parallel : ParallelLoop.t -> Loop.t`

优点：

- 旧 theorem 基本不动
- 新 parallel theorem 可以单独发展

缺点：

- 工程上多一层 wrapper

从 proof engineering 角度，我现在更倾向于方案 B。  
从最终统一 IR 的角度，方案 A 更整洁。

### 5.3 无论 A/B，annotation 必须带“origin dimension”

一个 bare `par : bool` 只够打印，不够证明。

为了让 theorem 对得上 cert，annotation 最好显式携带：

- 这是哪一个 current-space dimension 被并行化

否则后续将很难：

- 把 cert 上的维度和最终 loop 节点对应起来
- 在 cleanup / pretty-print 之后保持这个对应关系

## 6. 推荐的抽象 parallel semantics

这一节是整个证明设计的核心。

### 6.1 不要把 `parallel for` 只建模成“whole-iteration permutation”

如果一层并行 loop 的 body 里有多个 instruction，真实并发执行可能产生：

- 不同 iteration body 的 instruction 交错

如果语义只允许“整个 iteration body 当成原子块交换”，模型会过弱。

因此更自然的是在 **instruction-point list** 层定义抽象并行语义。

### 6.2 为什么 instruction-point list 是好切入点

`polygen/Loop.v` 已经有：

- `loop_instance_list_semantics`

它把 loop 程序的执行和一串 `InstrPoint` 联系起来。  
而现有 `PolyLang` validator 也正是在 instruction-point level 使用：

- `Permutable_ext`
- `StablePermut`

这两边恰好可以接起来。

### 6.3 抽象 parallel semantics 的推荐定义

概念上，给定一个 annotated loop 程序 `Lpar`，其 parallel semantics 可以定义为：

1. 它先生成一个或多个可能的 instruction-point list
2. 每个 list 表示一种合法的并发 interleaving
3. 最终状态由这份 list 的 instruction execution 给出

其中对 `ParFor d` 的关键约束是：

- 固定 outer prefix `< d`
- 不同 `d` 迭代对应的 instruction points 可以交错
- 但只能按 cert 允许的方式交错

### 6.4 这类语义最自然地写成 stable permutation closure

最实用的形式不是直接定义线程语义，而是：

- 先有一个 canonical sequential instruction list
- 再允许它在某个 parallel dimension 上作 `StablePermut`

也就是：

- `SeqFor` 给出顺序拼接的 instruction list
- `ParFor d` 给出所有与该顺序 list 满足某种 `par_stable_permut` 关系的 list

这里的 `par_stable_permut` 可以直接建立在现有 `StablePermut` 思想上。

### 6.5 `par_stable_permut` 的稳定条件应该是什么

稳定条件的核心不是“同一层 loop 的点都能换”，而是：

- 固定 outer prefix `< d`
- 两个 instruction points 的第 `d` 维取值不同
- 它们的交换被 cert 证明安全

因此稳定性谓词大致形如：

```text
parallel_swap_ok pp d tau1 tau2
```

含义是：

1. `tau1` 和 `tau2` 属于同一个 current-view program `pp`
2. 它们 outer prefix `< d` 相同
3. 它们在 `d` 上不同
4. 它们的交换不会破坏语义

第一版最保守地可以把第 4 点定义成：

- no `WW` / `WR` / `RW` cross-iteration conflict

后续再放宽到更一般的：

- `Permutable_ext tau1 tau2`

## 7. parallel checker 在 poly 上到底证什么

推荐 checker 工作在：

- `pp_cur := current_view_pprog pol_after`

上，而不是 raw OpenScop 或最终 Loop AST 上。

### 7.1 checker 的输入

第一版可以非常简单：

- `pp_cur`
- 一个候选 current-space 维度 `d`

如果以后支持多层并行，再扩成 list。

### 7.2 checker 的目标谓词

可定义：

```text
parallel_safe_dim pp_cur d
```

含义是：

- 对任意两个 instruction instances
- 若 outer prefix `< d` 相同，且第 `d` 维不同
- 那么它们要么无破坏性冲突，要么满足可交换条件

### 7.3 checker 的布尔实现

第一版可以完全复用当前 validator 的 collision-style 约束构造方式。

对任意 pair of instructions / accesses，构造 polyhedron，约束包括：

1. 两边都在 domain 中
2. 环境参数相同
3. prefix `< d` 相同
4. 第 `d` 维不同
5. 两者访问同一 memory location
6. 冲突类型属于 `WW/WR/RW`

若这些冲突 polyhedra 全为空，则 `d` safe。

以后再用更精细的 `Permutable_ext` 版本放宽。

### 7.4 checker soundness theorem

推荐 theorem 形状：

```text
check_pprog_parallel_currentb pp_cur d = true
-> wf_pprog_general pp_cur
-> parallel_safe_dim pp_cur d
```

如果以后是 witness/list 版本，则把 `d` 换成 `pw`。

## 8. 从 parallel-safe 到抽象并行语义正确性的证明

这是最关键的一层 theorem。

### 8.1 先证明 pairwise safe swap

从 checker soundness 先得到：

- 对任意满足同 prefix、不同 `d` 的 pair
- 它们满足 `parallel_swap_ok`

### 8.2 再证明 allowed swap implies `Permutable_ext`

如果采用保守 no-collision 版本，则要证明：

- `parallel_swap_ok -> Permutable_ext`

或者直接证明：

- `parallel_swap_ok` 足以让 instruction-point list semantics 保持不变

这一步的 goal 和现有 affine validator 的 pairwise lemma 非常像。

### 8.3 再从 pairwise swap 推 stable permutation

一旦 allowed swap 是 sound 的，就可以利用 `StablePermut` 风格的归纳：

- 一个 interleaving 是一串合法交换的合成
- 每一步交换都 preserves semantics
- 所以整个 interleaving preserves semantics

这一步本质上是把现有：

- “排序后 instance list 与原 list 的 stable permutation”

推广成：

- “parallel semantics 允许的 interleaving list 与 canonical sequential list 的 stable permutation”

### 8.4 再把 slice-level 结果 lift 到整个 loop/program

一层 `ParFor d` 只是整个程序的一部分。  
还需要把：

- slice 内的 stable-permutation preservation

lift 到：

- 整个 nested loop / sequence / guard 结构

这里 `Loop.v` 里已有的：

- `loop_instance_list_semantics`
- 以及 `iter_semantics`

是很好的桥。

## 9. 最值得复用的 theorem 组合方式

我现在最推荐的组合方式不是重写整个 codegen proof，而是做 theorem stacking。

### 9.1 第一步：保留现有顺序 codegen theorem

继续使用：

- `prepared_codegen_correct_general`

它已经说明：

- 顺序 codegen 生成的 `Loop` 程序
- refine 到 `PolyLang` current-view semantics

### 9.2 第二步：新增一个 parallel annotation erasure theorem

这一步不是最终目标，但很有用：

```text
erase_parallel (annotated_codegen pp cert) = existing_codegen pp
```

或者至少：

```text
Loop.semantics (erase_parallel Lpar) st st'
<-> Loop.semantics Lseq st st'
```

它确保：

- 新 parallel-aware codegen 不会破坏旧主线

但它不是最终目标。  
真正要满足“verified parallel for”，还必须继续证明：

- `ParallelLoop.parallel_semantics` 本身是 sound 的

### 9.3 第三步：新增一个 abstract-parallel-to-sequential theorem

这是关键 theorem：

```text
parallel_cert_sound pp cert
-> ParallelLoop.parallel_semantics (annotated_codegen pp cert) st st'
-> Loop.semantics (erase_parallel (annotated_codegen pp cert)) st st'
```

它的含义是：

- 所有被 parallel semantics 允许的 interleaving
- 都 refine 到顺序擦除语义

### 9.4 第四步：组合得到最终并发正确性 theorem

把第二步和第三步与 `prepared_codegen_correct_general` 组合，得到：

```text
parallel_cert_sound pp cert
-> ParallelLoop.parallel_semantics (annotated_codegen pp cert) st st'
-> PolyLang.instance_list_semantics pp st st'
```

这才是“并发被证了”的核心结论。

## 10. pipeline 中 validation / proof 的准确插点

推荐插点是：

```text
... -> checked_tiling_validate_poly
-> current_view_pprog
-> checked_parallelize_current
-> annotated_codegen
```

这里每一层各管一件事。

### 10.1 Pluto / PolOpt 负责 transform 和启发式

如果用户给 `--parallel`，那么：

- Pluto 可以在 tiling 阶段用 `--tile --parallel`
- 这样第二次 Pluto 调用会做 parallel-aware tile scheduling

但这只是“找一个更并行友好的 after program”。

### 10.2 PolCert 只负责 cert

PolCert 不负责：

- 启发式搜索
- 相信 Pluto 的 `<loop>` extension

PolCert 只负责：

- 对 current-view program 的候选维度做 checked certification

### 10.3 codegen 才负责真正输出 `parallel for`

因此：

- cert 在 poly 表示上完成
- loop annotation 在 codegen 表示上完成
- 并发正确性 theorem 跨越这两层

## 11. “改 `Loop` 还是单独做 `ParallelLoop`”的判断

这是目前最容易摇摆的设计点。

### 11.1 如果目标是最小 proof churn

更推荐：

- 保留原 `Loop`
- 新增 `ParallelLoop`
- 定义 `erase_parallel`

好处是：

- 旧 theorem 几乎不用大改
- parallel 证明可以层层叠加

### 11.2 如果目标是最终 IR 整洁

更推荐：

- 直接给 `Loop` 加 annotation

但这样会带来很多机械性 proof 修改。

### 11.3 两种方案在数学上并没有本质区别

区别主要在 proof engineering：

- 是否想保留原 theorem 完整不动
- 是否想暂时多引入一层 wrapper

因此我的实际建议是：

1. 第一版先用 `ParallelLoop` 这样的 wrapper 层闭合 proof
2. 等 parallel semantics/证书稳定后，再考虑把 annotation 下沉回 `Loop`

## 12. 为什么我不推荐“plain Loop codegen 后再盲目 post-pass parallelize”

这条路线的问题不是做不到，而是证明边界会脏。

### 12.1 post-pass 仍然需要 origin information

如果 post-pass 想把某个最终 loop 节点改成 `parallel for`，它必须知道：

- 这个节点对应哪个 current-space dimension

否则 cert 上的维度和 loop 节点无法对齐。

### 12.2 cleanup 之后再猜 loop 身份很脆弱

当前 cleanup/simplify 会：

- 消去一些空序列
- 合并结构

如果 post-pass 在完全不带 tag 的最终 Loop AST 上工作，就很难稳定对应回 cert。

### 12.3 真正可行的 post-pass 其实已经等价于“带 tag 的 annotation 层”

如果 post-pass 之前就给 loop 节点带上：

- origin dimension
- 可并行标记

那么它本质上已经不是“盲 post-pass”，而是：

- codegen 期间或 codegen 紧后的一层 annotated representation

所以这条路线并不会比 `ParallelLoop` 更简单。

## 13. 推荐的 theorem 清单

下面给出一份比较清晰的 theorem inventory。

### 13.1 checker side

- `check_pprog_parallel_currentb`
- `check_pprog_parallel_currentb_sound`
- `checked_parallelize_current`
- `checked_parallelize_current_correct`

### 13.2 cert meaning

- `parallel_safe_dim`
- `parallel_safe_dims`
- `parallel_swap_ok`
- `parallel_cert_sound`

### 13.3 semantics side

- `erase_parallel`
- `parallel_instance_list_semantics`
- `parallel_semantics`
- `parallel_semantics_refines_erased_sequential`

### 13.4 codegen side

- `annotated_codegen`
- `annotated_codegen_erase_eq`
- `annotated_codegen_parallel_correct`

## 14. 最推荐的第一版落地顺序

### Step 1: 先把证明对象说清楚

先固定：

- cert 在 `current_view_pprog` 上
- 并发语义是 abstract parallel semantics，不是 annotation erasure

这一步比改代码更重要。

### Step 2: 先做单维 parallel cert

先只支持：

- 最外层一个 current-space dimension
- 不支持 `multipar`
- 不支持 vector

这样 checker 和 theorem 都会清楚很多。

### Step 3: 先保留旧顺序 codegen theorem

先把 parallel 层设计成“叠在旧 theorem 上”，不要直接破坏：

- `prepared_codegen_correct_general`

### Step 4: 再决定是直接改 `Loop` 还是先做 `ParallelLoop`

如果目标是尽快闭合 proof，我更建议先做 `ParallelLoop`。

## 15. 最后的收束

如果把整个 parallel proof strategy 收束成一句话，那么我当前最认同的版本是：

> Pluto/PolOpt 负责找一个更并行友好的 transformed program；PolCert 在 `current_view_pprog` 上 cert 某个维度 parallel-safe；codegen 输出带 parallel 标注的 loop；新增的 abstract parallel semantics 再证明这些并行标注的真实并发执行 refine 到现有顺序语义，从而最终 refine 到 `PolyLang` semantics。

这个版本避免了两个常见错误：

1. 把 `parallel for` 当成纯打印问题
2. 把并发正确性偷换成 annotation-erasure correctness

它也是我目前认为最贴合 PolCert 现有 proof 栈、并且最容易逐步落地的一条路线。
