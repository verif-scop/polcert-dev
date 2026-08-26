# Extractor Proof Stack

Date: 2026-03-06
Purpose: Persistent push/pop stack for active Coq goals, so context survives compression.
Code checkpoint: `/polcert` `extractor@92e1407`

## Rules
- `PUSH`: add a new frame when entering a new theorem/subgoal family.
- `POP`: mark frame resolved, record exact lemma/tactic used.
- Keep at most 5 active frames; archive older resolved frames to `LOG.md`.
- Every active frame must include:
  - goal shape,
  - available hypotheses,
  - candidate lemmas,
  - next concrete proof action.

## Active Stack
- None.
- Extractor closure target is complete at this checkpoint.

## POP Log (latest)
- `POP`: closed generalized prefix recursive theorem
  - theorem: `core_sched_stmt_stmts_constrs_prefix_mutual`
  - final hard branch: `Loop`
  - key ingredients:
    - `loop_slice_filter_prefix_slice_gen`
    - `iter_semantics_refine_with_state_eq`
    - recursive `IHbody` at `prefix ++ [x]`
- `POP`: closed old slice wrapper as a true wrapper
  - theorem: `loop_slice_to_body_semantics_todo`
  - result shape:
    - `exists stB', Loop.loop_semantics body ... stA stB' /\ State.eq stB stB'`
- `POP`: closed stale theorem tail issue
  - replaced trailing `Admitted.` on `core_sched_stmt_stmts_constrs_prefix_mutual`
    with `Qed.` after the proof was fully complete
- `POP`: fixed env-reversal normalization in generalized loop case
  - stable rewrite:
```coq
symmetry.
rewrite app_assoc.
apply rev_unit.
```
  - use case:
    - align `rev (envv ++ (prefix ++ [x]))` with `x :: rev (envv ++ prefix)`
- `POP`: fixed nested bullet level after `split.` inside the loop case
  - under outer `-`, use `+`/`*`, not another `-`

## Stable Lessons From This Proof
1. The final bridge must stay prefix-aware.
2. Plain lowered completeness is the wrong theorem for a fixed slice.
3. `replace` can generate a reverse equality goal; inspect direction before blaming the lemma.
4. Even when all branches compile, run `check-admitted`; stale theorem tails happen.

## Resume Checklist
1. Read `MUST_READ.md`.
2. Read `proof/extractor/STATUS.md`.
3. Confirm current container commit.
4. Only push a new frame if starting a new extractor theorem or refactor.
