# Parallel IR Choice

本文专门比较两种实现路线：

1. 直接扩展现有 `Loop`
2. 保留现有 `Loop`，新增 `ParallelLoop` wrapper

在 parallel 支持这件事上，这不是纯工程风格问题，而是会直接影响：

- proof churn
- theorem layering
- 与当前 sequential proof 栈的耦合程度
- 与其他并行开发 session 的冲突概率

## 1. 先固定评判标准

在当前项目语境下，IR 选型至少要满足五条。

### 1.1 `par for` 语义本身必须可证明

这意味着：

- 不能只支持打印 pragma
- 不能只支持 annotation erasure
- 必须能承载抽象 parallel semantics

### 1.2 不能破坏现有 sequential codegen theorem 主线

当前已经稳定的资产包括：

- `validate_correct`
- `checked_tiling_validate_correct`
- `instance_list_semantics_current_view_iff`
- `prepared_codegen_correct_general`

新的 IR 路线越能复用这条主线越好。

### 1.3 必须能把 cert 和 emitted loop 精确对应

也就是说，无论哪种 IR，都必须显式承载：

- 该 loop 对应的 current-space dimension

否则 `parallel_cert` 和 emitted `par for` 无法精确对齐。

### 1.4 第一版要尽量减少 proof churn

这轮 parallel 支持并不是在真空里做，另一个 session 还在推进 ISS / proof 相关工作。  
因此第一版最重要的是：

- 把 parallel 叠加上去
- 而不是把现有顺序基础设施全面改写

### 1.5 后续仍应允许收敛回统一 IR

第一版可以工程上保守，但不能把将来的统一性彻底堵死。

## 2. 方案 A：直接扩展现有 `Loop`

概念上可写成：

```text
Inductive stmt :=
| Loop  : loop_mode -> nat -> expr -> expr -> stmt -> stmt
| Instr : ...
| Seq   : ...
| Guard : ...
```

其中：

- `loop_mode = SeqMode | ParMode`
- `nat` 记录 current-space origin dimension

### 2.1 优点

#### 优点 1：最终 IR 最整洁

所有 loop 构造都还在一棵 AST 里：

- 顺序 loop
- 并行 loop

以后如果还要加：

- vector
- unroll hint
- 其他 loop metadata

都可以继续统一挂在同一 IR 上。

#### 优点 2：printer 与 cleanup 只维护一套数据结构

理论上：

- `SLoopPretty.ml`
- cleanup passes
- 任何后续 loop-level tooling

都只需要理解一套 AST。

#### 优点 3：长期架构更自然

如果最终 parallel 成为主功能，而不是边缘扩展，那么统一 IR 更符合长期方向。

### 2.2 缺点

#### 缺点 1：proof churn 最大

一旦直接改 `Loop`，所有依赖 `Loop.stmt` 的定义和引理都要跟着动：

- `polygen/Loop.v`
- `polygen/LoopCleanup.v`
- `polygen/LoopSingletonCleanup.v`
- `syntax/SLoopPretty.ml`
- 以及所有 pattern match / structural induction 的证明

其中很多改动只是机械性的，但数量会很多。

#### 缺点 2：更容易干扰现有 sequential 主线

即使 parallel theorem 本身单独发展，直接改 `Loop` 也会让：

- 现有顺序 theorem
- cleanup correctness
- printer / elaboration 边界

全部进入改动面。

#### 缺点 3：在当前并行开发环境下冲突概率更高

因为它会更早地碰共享核心文件。

## 3. 方案 B：新增 `ParallelLoop` wrapper

概念上：

- 保留现有 `Loop`
- 新增 `ParallelLoop`
- 定义 `erase_parallel : ParallelLoop.t -> Loop.t`

并把新 parallel semantics 放在 `ParallelLoop` 上。

### 3.1 优点

#### 优点 1：现有 sequential theorem 基本不动

最关键的顺序 theorem 仍然直接活在旧的 `Loop` 上：

- `prepared_codegen_correct_general`

parallel 只需证明：

- `ParallelLoop.parallel_semantics` refine 到 `erase_parallel` 之后的 `Loop.semantics`

这是最理想的 theorem stacking 方式。

#### 优点 2：proof boundary 更清楚

它天然把两件事分开：

- 旧 `Loop`
  - 顺序语义、旧 codegen 正确性
- 新 `ParallelLoop`
  - 并行语义、parallel correctness

这会让“什么是旧资产，什么是新增证明义务”一眼就清楚。

#### 优点 3：更适合当前项目节奏

在还有别的 session 并行改动时，wrapper 层最大的好处是：

- 可以优先新增文件
- 把碰共享核心文件的时刻推迟

这对减少协作冲突很重要。

#### 优点 4：更容易先做小范围验证

第一版只要能做到：

- single-dim `par for`
- checked certification
- abstract parallel semantics correctness

就已经很有价值。  
wrapper 路线更适合先闭合这版。

### 3.2 缺点

#### 缺点 1：会多一层表示

你需要维护：

- `Loop`
- `ParallelLoop`
- `erase_parallel`

直观上会比统一 IR 更啰嗦。

#### 缺点 2：printer / codegen bridge 需要额外一层

最终输出 C/OpenMP 时，需要决定：

- 直接从 `ParallelLoop` 打印
- 还是先 erase 再混合打印 annotation

这会比单一 AST 略绕。

#### 缺点 3：长期可能还要再收敛一次

如果未来确定 parallel 是常驻核心功能，就可能想把 wrapper 收回统一 IR。

## 4. 从“verified `par for`”角度看，哪条更合适

关键点是：

- 一旦要求 `par for` 语义本身被证明
- 新增的核心其实已经不是“一个 flag”
- 而是一整套新的语义与 theorem

在这种情况下，wrapper 层的价值反而更高，因为它能把：

- 新 parallel semantics
- 新 parallel theorems

都局部化到一个新的表示层里。

也就是说，越认真地对待 `par for` 语义本身，越说明这不是给旧 `Loop` 随手加一个布尔位就完事的事情。

## 5. 从 checker / cert / codegen 对齐角度看

无论 A/B，两条路线都必须显式带：

- current-space origin dimension

但两者的承载方式不同。

### 5.1 方案 A

origin dimension 存在：

- `Loop` 节点里

### 5.2 方案 B

origin dimension 存在：

- `ParallelLoop` 节点里

对 theorem 来说，二者并无本质区别。  
区别只在于：

- 方案 A 会让原有 `Loop` 引理全都看见这个新字段
- 方案 B 只让 parallel theorem 看见它

## 6. 从当前代码库冲突面看

考虑到当前仓库已经有很多并行改动在进行中，冲突面是一个实际约束，不是抽象约束。

### 6.1 方案 A 更早碰共享文件

会较早影响：

- `polygen/Loop.v`
- `polygen/LoopCleanup.v`
- `syntax/SLoopPretty.ml`

这些都很容易和别的证明/代码工作互相踩。

### 6.2 方案 B 可以先新增文件

可以优先落地为：

- `polygen/ParallelLoop.v`
- `src/ParallelValidator.v`
- `src/ParallelCodegen.v`

等这些新层稳定了，再把很少量桥接接到：

- `driver/PolOpt.v`
- `driver/Scheduler.ml`
- `syntax/SLoopMain.ml`

这更符合“先把不确定性局部化”的策略。

## 7. 推荐结论

### 7.1 第一版结论

如果目标是：

- 真的验证 `par for` 语义
- 同时尽量减少对现有顺序 proof 栈的扰动

那么第一版我明确更推荐：

- `ParallelLoop` wrapper

而不是直接扩展现有 `Loop`。

### 7.2 第二版结论

等下面三件事都稳定之后，再考虑收敛回统一 IR：

1. `parallel_safe_dim` checker 定义稳定
2. abstract parallel semantics theorem 闭合
3. single-dim `par for` 路线跑通

在那之后，再评估是否值得把：

- `ParallelLoop`

合回：

- `Loop + annotation`

## 8. 一个很实际的判断

很多时候人会倾向于“一开始就统一 IR”，因为看起来更整洁。  
但在这个项目当前阶段，这种整洁可能是假的：

- 因为真正难的是并行语义与 theorem
- 不是 AST 长得够不够统一

所以更务实的选择是：

- 先让 parallel semantics 和 correctness theorem 局部闭合
- 再看是否值得把表示层统一

## 9. 最后的收束

这份文档的核心判断只有一句话：

> 在当前 PolCert 阶段，如果要求 `par for` 语义本身是 verified，那么第一版最合理的工程路线是新增 `ParallelLoop` wrapper，把新的并行语义和 theorem 局部化；等 parallel checker 与 semantics theorem 稳定后，再决定是否收敛回统一的 `Loop + annotation` IR。
