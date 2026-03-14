# ISS Validation Design

这份文档只讨论 Pluto 的 ISS (`index set splitting`) 应该怎样验证，不讨论 tiling 和 parallel。

## 1. 问题重述

ISS 的本质不是：

- 同一个 statement family 上换一套 schedule

而是：

- 把原来的 statement/domain 拆成多个 statement/domain 分支

这点在 Pluto 的执行顺序里也很明确：

- ISS 入口在 `/pluto/tool/main.cpp:688-690`
- 实现在 `/pluto/lib/iss.c`
- 它发生在 `pluto_auto_transform()` 之前

所以 ISS 的验证义务不能并入现有的 affine scheduling validator。它更像：

- 一个 program refinement / partition correctness 问题

## 2. validate 的输入应该是什么

## 2.1 只给 before/after 两份 program，理论上不够好

理论上仍然可以尝试只用：

- `before.scop`
- `after.scop`

去反推 ISS 做了什么。

但和 tiling 不同，ISS 的 after program 里通常不会有那种非常机械、容易恢复的 witness。它只会表现成：

- statement 数量变多
- 每个 statement 的 domain 变了
- body/access 可能看起来相同

而“这些新 statements 为什么正好构成原 statement 的一个合法分割”并没有像 tiling floor-link 那样直接写在矩阵里。

所以只靠 before/after 反推 witness，工程上会很脆弱。

## 2.2 更合理的输入：before + after + split witness

我认为 ISS validator 更合适的接口是：

```text
before.scop + after.scop + iss_witness
```

其中 `iss_witness` 至少应包含：

1. statement map
   - after 的每个 statement 来自哪个 before statement
2. split predicates / split domains
   - 每个 after statement 覆盖原 statement 的哪一块 iteration space
3. partition facts
   - 这些 split domains 的并集应等于原 domain
   - 它们应当互不重叠，或至少不会导致重复执行
4. unchanged semantics payload
   - body 是否保持
   - access relation 是否保持
5. post-split scheduling payload
   - split 之后交给 scheduler 的次序信息

这个 witness 不必被信任；它的作用只是：

- 让 checker 有一个明确的、结构化的待检查对象

## 3. 正确性应该证明什么

ISS 的 correctness obligations 至少有五条。

## 3.1 Statement correspondence

需要先证明：

- after 中每个新 statement 都能回溯到某个 before statement

否则连“谁是谁拆出来的”都说不清。

## 3.2 Split coverage

对每个 before statement `S`，所有映射到 `S` 的 after-domains 的并集，必须等于原来的 `domain(S)`。

这是：

- 不漏点

## 3.3 Split uniqueness / disjointness

对每个 before statement `S`，映射到 `S` 的 after-domains 不应重复覆盖同一 instance。

最干净的条件是：

- 两两不交

更弱一点也至少要证明：

- 没有会造成重复执行的重叠

这是：

- 不重执行

## 3.4 Body / access preservation

每个 split statement 都应与其来源 before statement 保持同样的语义负载：

- statement body 不变
- access relation 不变
- 参数与数组语义不变

这说明 ISS 只是：

- 重新组织 instance space

而不是：

- 修改单个 instance 做什么

## 3.5 Post-split schedule legality

只证明 split 正确还不够；split 后的 after program 仍然要满足调度合法性。

这一块才是现有 validator 最接近能复用的部分：

- 可以在 split correctness 之后，再对 after program 做 schedule legality 检查

## 4. 这意味着 checker 的整体分解

一个完整的 ISS validator 更像：

```text
iss_validator(before, after, witness) =
  check_statement_map
  + check_split_coverage
  + check_split_uniqueness
  + check_body_access_preservation
  + check_schedule_legality
```

而不是：

```text
reuse_existing_schedule_validator(before, after)
```

## 5. 为什么它比 tiling 更难

tiling 虽然也会改 domain，但它通常还保持：

- 同一个 statement family
- 同一个 point instance space
- 一个较机械的 lifting witness

ISS 则直接打破了这些结构假设：

1. one-to-one statement correspondence 不再成立
2. after program 的 family 结构变化更大
3. 没有像 floor-link 那样显式的、易恢复的 witness

所以 ISS 需要的是：

- splitting equivalence framework

而不是 schedule validator 的局部加补丁。

## 6. 我对 witness 形式的建议

若后续要让 Pluto fork 支持可验证 ISS，我建议直接增加一个显式 dump，而不是只靠 `after.scop`。

一个最小的 ISS witness 可以长成：

```text
for each after statement S':
  source_statement = S
  split_domain = D'
  proof_goal:
    D' subseteq D(S)

for each source statement S:
  union_{S' from S} D'(S') = D(S)
  pairwise_disjoint(D'(S'))
  body(S') = body(S)
  access(S') = access(S)
```

如果 Pluto 不愿意直接输出逻辑公式，也至少应该输出：

- split 前后的 statement id 对应
- split 时使用的分裂条件

## 7. 一个具体样例

样例程序：

- `/pluto/test/reverse-iss.c`

命令：

```sh
pluto --debug --silent --iss --notile --noparallel --nounrolljam \
  --noprevector --nodiamond-tile test/reverse-iss.c
```

从 Pluto 的 debug 输出可以直接看到：

- `After ISS`
- 原本同一条语句体被拆成 `S1` 和 `S2`
- 两者都仍然对应同一条源语句：

```text
a[i] = 2 * a[N - 1 - i];
```

这里 validator 要证明的重点不是：

- `T(S1)` 和 `T(S2)` 比原来更优

而是：

- `domain(S1) ∪ domain(S2) = domain(S)`
- `domain(S1) ∩ domain(S2) = ∅`
- `body/access` 与原语句一致

## 8. 一个现实建议

如果要推进顺序，我仍然建议：

1. 先完成 tiling validator
2. 再做 ISS validator

因为 ISS 需要先把下面这些基础设施补齐：

- one-to-many statement correspondence
- program-family equivalence
- split-domain union/disjointness checking

这些都比 tiling 的“同 family 上做 lifting”更重。

## 9. 当前结论

当前我的结论是：

- ISS validation 不应该把输入只看成两份 program
- 更合理的接口是 `before + after + explicit split witness`
- 它的核心证明对象不是 schedule，而是 statement/domain splitting equivalence
