# Extractor Proof Strategy Memo

Date: 2026-03-05

## Strategy principle
Do not attack `extractor_correct` directly.
First freeze shape invariants, then prove semantics on top of stable definitions.

## Layered proof plan

### Layer 0: Shape-first guardrails
- Prove extraction-success implies wf checks pass for each emitted `pi`.
- Keep this lemma executable-friendly (boolean checker bridge) for fast regressions.

### Layer 1: Expression and test soundness
- Reuse/extend `expr_to_aff_correct`.
- Add normalized `exprlist_to_aff` soundness:
  - evaluated list equals affine product under the chosen column convention.
- Add `test_to_aff` soundness:
  - constraints generated for `LE`/`EQ`/`And` correspond to `eval_test`.

### Layer 2: Structural extraction invariants
- Induction over `extract_stmt` / `extract_stmts`.
- Track:
  - domain growth discipline
  - schedule-prefix discipline (`Loop` vs `Seq`)
  - depth/column update discipline.

### Layer 3: Semantic bridge
- Build an intermediate bridge theorem:
  - extracted poly instance execution corresponds to loop-instance-list execution.
- Reuse recent `polygen/Loop.v` and `InstanceListSema.v` bridge lemmas.
- Only at the end package into the public theorem statement:
  - `PolyLang.instance_list_semantics pol st1 st2`
  - implies `exists st2', Loop.semantics loop st1 st2' /\ State.eq st2 st2'`.

## Tactics for proof engineering
- Keep one "dimension context" record/hypothesis per induction branch:
  - `env_dim`, `iter_depth`, `cols`.
- Avoid ad-hoc rewriting of `pred`/`S` arithmetic in many places.
- Promote recurring arithmetic equalities to local helper lemmas early.
- Keep boolean-check lemmas close to constructors for faster diagnosis.

## Regression discipline
- Every structural extractor change should keep these checks green:
  - extractor success on representative examples
  - per-`pi` wf checker result is `true`
  - existing validator smoke tests remain unchanged.
