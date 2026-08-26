# Extractor Proof Plan

Date: 2026-03-05

## Goal
Close `Extractor.extractor_correct` on a stable extractor definition, then reconnect it to the existing `PolOpt` proof chain.

See also:
- `FOUNDATIONS.md`
- `DEPTH_WF_SPEC.md`
- `PROOF_STRATEGY.md`
- `CORE_LEMMA_PLAN.md`

## Phase 0: Stabilize Extractor Definition (must-do first)

1. Fix dimension invariant for affine rows.
- [x] Update `exprlist_to_aff` to normalize every affine row to expected width.
- [x] Replace ambiguous single `depth` with explicit `env_dim` + `iter_depth` state.
- [x] Add `exprlist_to_aff_correct` (normalized affine rows preserve expression evaluation).

2. Fix/clarify `pi_depth` convention.
- Choose one explicit invariant and enforce it:
  - recommended: `pi_depth = iterator_count` (not including `varctxt`).
- [x] Refactor extraction state to avoid ambiguous `pred depth` arithmetic.
- [x] Enforce `pi_depth := iter_depth` at emission sites.

3. Add extractor output sanity theorem/check.
- [x] Add explicit syntactic fragment check `wf_scop_stmt` (affine-only SCoP subset).
- [x] Add executable check `check_extracted_wf` in `extractor`.
- [x] Make extraction fail early when wf check fails.
- [x] Add a proved theorem relating successful `extractor` return and per-`pi` wf predicates.
- [x] Add `extractor_success_implies_wf_scop`.

## Phase 1: Local Soundness Lemmas

1. Expression/test layer
- Reuse `expr_to_aff_correct`.
- [x] Add core structural lemmas for `exprlist_to_aff` after normalization fix:
  - output list length matches source expr list;
  - each output affine row has normalized width `cols`.
- [x] Add `test_to_aff` soundness lemmas:
  - `LE`, `EQ`, `And` constraints correspond to `eval_test`.
- [x] Add `test_to_aff` completeness lemmas (needed for `poly -> loop` direction):
  - constraints satisfied imply guard test evaluates to `true`.
- [x] Add normalization-preservation and bound-constraint soundness lemmas:
  - `normalize_affine(_list)_satisfies_constraint`
  - `lb_to_constr_sound`, `ub_to_constr_sound`
- [x] Add extraction-success lemmas for syntactic affine fragment:
  - `wf_affine_expr_true_expr_to_aff_success`
  - `wf_affine_expr_list_true_exprlist_to_aff_success`
  - `wf_affine_test_true_test_to_aff_success`
- [x] Add guard-append glue lemma:
  - `guard_constraints_sound`
- [x] Add reverse-direction guard/loop split lemmas:
  - `guard_constraints_complete`
  - `loop_constraints_complete`

2. Structural extraction layer
- Prove `extract_stmt`-level invariants:
  - domains/schedules/transformation dimensions are preserved as expected.
  - sequence position encoding matches statement order.
- [x] Added structural success inversion lemmas:
  - `extract_stmt_*_success_inv`
  - `extract_stmts_*_success_inv`
- Next focus:
  - local semantic lemmas for `extract_stmt` `Guard`/`Loop` branches using the new soundness primitives.

## Phase 2: Semantic Bridge for `extractor_correct`

Recommended route (aligned with your recent commits):
1. Introduce an intermediate theorem to connect extracted poly execution with loop-instance-list view.
2. Reuse `polygen/Loop.v` lemmas around `loop_instance_list_semantics` and `instr_point_list_semantics`.
3. Finish with wrapper to `Loop.semantics` required by current statement.

Progress in this phase:
- [x] Added final wrapper lemma `loop_semantics_intro_from_envv`.
- [x] Added bridge lemmas:
  - `loop_semantics_aux_implies_loop_semantics`
  - `loop_instance_list_semantics_implies_loop_semantics`
- [x] Refactored `extractor_correct` into a thin wrapper theorem (`Qed`).
- [x] Isolated the remaining hard part as `extract_stmt_to_loop_semantics_core` (currently `Admitted`).

Remaining glue to add:
- prove `extract_stmt_to_loop_semantics_core` by structural/semantic decomposition of extracted instance lists.
- optionally add a helper equivalence between loop-structured instance semantics and sorted instruction-point semantics for extracted schedules.
- add an explicit `envv`/`rev envv` evaluation-bridge lemma for the `Instr` branch closure.

## Phase 3: Reconnect to Driver

1. Re-check `driver/PolOpt.v` chain:
- `Extract_Schedule_correct` should become fully closed once `extractor_correct` is closed.

2. Record non-goal for this phase:
- end-to-end `Opt_correct` and depth-gap/codegen composition are subsequent milestones.

## Immediate Next Actions

1. Prove `extract_stmt_to_loop_semantics_core` first; keep `extractor_correct` untouched now that it is closed.
2. Continue with dedicated `extract_stmt` sub-lemmas for:
- `Guard`: test constraints preserve feasibility when guard is true.
- `Loop`: extracted bound constraints correspond to `lb <= i < ub`.
3. Resolve environment-orientation bridge strategy for `Instr` branch:
- either prove a generic bridge lemma for accepted fragment (`envv` vs `rev envv`),
- or strengthen wf/fragment predicate to enforce bridge-compatible instruction expr lists.
4. Build the structural induction spine:
- define/close `extract_stmt` and `extract_stmts` semantic bridge lemmas (mutual induction).
5. Add a list-order alignment lemma between `flatten_instrs` order constraints and the loop execution order implied by extractor schedules.
6. Add instance-level regression examples (outside functor body) for `|varctxt|=1` and `|varctxt|>1` under new access-resolution path.
