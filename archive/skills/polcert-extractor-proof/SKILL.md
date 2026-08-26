---
name: polcert-extractor-proof
description: Drive Coq proof engineering for PolCert extractor work in `src/Extractor.v`, including interactive proof-state inspection, tactic-driven decomposition of `extractor_correct`, depth/wf invariant checks, and regression-safe edit/build loops inside container `gifted_curie`. Use when tasks involve understanding extractor semantics, proving soundness lemmas, or debugging failed Coq goals in the extractor pipeline.
---

# PolCert Extractor Proof

Use this skill to keep extractor proof work deterministic, inspect real Coq proof states quickly, and avoid regressing depth/wf invariants while iterating.

## Run Loop

0. Resume context first (mandatory after long pause / context compression):
- read `MUST_READ.md`, then `LOG.md`, `PLAN.md`, `proof/extractor/STATUS.md`, `proof/extractor/CORE_LEMMA_PLAN.md`, `proof/extractor/PROOF_STACK.md`.
- confirm current admitted count with `opam exec -- make -s check-admitted` in container.
- as of 2026-03-06 closure checkpoint: expected result is `Nothing admitted.`

0.5. Proof stack discipline (mandatory):
- before entering a non-trivial subgoal, `PUSH` a frame in `proof/extractor/PROOF_STACK.md`.
- after closing subgoal/theorem, `POP` that frame with exact closing lemma/tactic.
- never leave active proof branches only in chat memory.

1. Work from host, execute Coq commands in container:
```bash
docker exec gifted_curie bash -lc 'cd /polcert && opam exec -- <cmd>'
```
2. Build only touched theorem file first:
```bash
coqc $(cat _CoqProject) src/Extractor.v
```
3. Rebuild dependent files only after extractor passes.

## Inspect Proof State

1. Start a focused `coqtop` session with project loadpath:
```bash
coqtop $(cat _CoqProject)
```
2. For extractor goals, instantiate module explicitly:
```coq
Require Import Result TPolIRs Extractor.
Module E := Extractor TPolIRs.
```
3. Use this loop:
- `Goal ...` / `Proof.`
- `intros`, `destruct`, `remember`, `inv`
- `Show.` or `Set Printing All.` only when blocked by opaque terms
- `Abort.` for probes, keep source clean

4. Prefer keyword search before writing fresh lemmas:
```bash
grep -R -n "loop_instance_list_semantics\|instr_point_list_semantics\|flatten_instrs\|rebase_ip_nth" src polygen
```

## Extractor Invariants

Enforce these invariants before proving anything heavy:

1. `cols = env_dim + iter_depth` uses nat arithmetic (`%nat`).
2. Every affine row in domain/schedule/transformation/access is resized to `cols`.
3. `pi_depth = iter_depth` at emission sites.
4. `Seq` schedule row is `(repeat 0 cols, pos)`; never `([], pos)`.
5. `extractor` first checks `wf_scop_stmt`; non-affine fragment must fail early.
6. `extractor` returns `Err` when `check_extracted_wf` fails.

## Proof Strategy

Prove in this order:

1. Expression layer (`expr_to_aff_sound`-style lemmas).
2. Constraint conversion soundness (loop bounds / guards).
3. Structural lemma for `extract_stmt` by statement induction.
4. First close wrapper-level core (`extract_stmt_to_loop_semantics_core_sched`) via constrained internal bridge.
5. Then isolate and close only constrained internal admits.
6. Keep `extractor_correct` as thin wrapper theorem (`Qed`) and avoid reworking it during core-lemma iteration.

## Final-Hole Lessons

1. If the remaining goal is about a fixed loop slice, do not lower it to a plain unrestricted `flatten_instrs` theorem.
- The correct theorem shape is prefix-aware and slice-aware.

2. For outer-loop reconstruction, prefer `iter_semantics_refine_with_state_eq` over exact-state bridge lemmas.
- This avoids getting stuck when empty slice semantics only gives `State.eq`.

3. For env alignment in loop bodies, preserve the `Loop.LLoop` shape.
- Outer env: `rev (envv ++ prefix)`
- Body env: `x :: rev (envv ++ prefix)`
- If the recursive IH yields `rev (envv ++ (prefix ++ [x]))`, normalize with:
```coq
symmetry.
rewrite app_assoc.
apply rev_unit.
```

4. Treat `replace` carefully.
- It may generate the equality goal in the reverse direction.
- If a lemma obviously has the right statement but fails, inspect goal direction first.

5. After all branches compile, still run `check-admitted`.
- It catches stale theorem-tail `Admitted.` markers.

6. Watch bullet nesting.
- Under an outer `-`, a later `split.` should usually use `+` and `*`.

Open [references/extractor-proof-checklist.md](references/extractor-proof-checklist.md) for tactic templates and branch-closing patterns.
