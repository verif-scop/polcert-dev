# Extractor Proof Checklist

## 0. Resume context sync (before edits)

```bash
sed -n '1,220p' MUST_READ.md
sed -n '1,220p' LOG.md
sed -n '1,220p' PLAN.md
sed -n '1,260p' proof/extractor/STATUS.md
sed -n '1,260p' proof/extractor/CORE_LEMMA_PLAN.md
```

Then confirm current hole count:

```bash
docker exec gifted_curie bash -lc 'cd /polcert && make -s check-admitted'
```

## 1. Fast compile/debug cycle

```bash
docker cp work/Extractor.v gifted_curie:/polcert/src/Extractor.v
docker exec gifted_curie bash -lc 'cd /polcert && opam exec -- coqc $(cat _CoqProject) src/Extractor.v'
```

## 2. Open a realistic proof state

```coq
Require Import Result TPolIRs Extractor.
Module E := Extractor TPolIRs.

Goal forall loop pol st1 st2,
  E.extractor loop = Okk pol ->
  TPolIRs.PolyLang.instance_list_semantics pol st1 st2 ->
  exists st2', TPolIRs.Loop.semantics loop st1 st2' /\ TPolIRs.State.eq st2 st2'.
Proof.
  intros loop pol st1 st2 Hext Hpoly.
  destruct loop as [[stmt varctxt] vars].
  unfold E.extractor in Hext.
  remember (E.wf_scop_stmt stmt) as WfScop.
  destruct WfScop; try discriminate.
  remember (E.extract_stmt stmt nil (Datatypes.length varctxt) 0 nil) as Extract.
  destruct Extract as [l|msg].
  Show.
Abort.
```

Run it with project flags:

```bash
docker exec gifted_curie bash -lc 'cd /polcert && opam exec -- coqtop $(cat _CoqProject) -q < /tmp/extractor_probe.v'
```

## 3. Branch normalization pattern

```coq
destruct WfScop; try discriminate.
destruct Extract as [l|msg] eqn:HEX; try discriminate.
destruct (E.check_extracted_wf l varctxt vars) eqn:HWF; try discriminate.
inv Hext.
```

Use this immediately after unfolding `extractor` to remove impossible error branches.

## 4. Typical tactic micro-patterns

- Use `remember` before `destruct` when recursive calls are large.
- Use `inv` (`LibTactics`) on equations of constructors like `Okk _ = Okk _`.
- Use `rewrite app_nil_r` and `lia` aggressively for shape arithmetic and affine constants.
- Use `eapply` with explicit `with (...)` bindings for induction hypotheses.

## 5. Regression checks after proof edits

1. Re-run `coqc` on `src/Extractor.v`.
2. Re-run at least one dependent file (`driver/PolOpt.v`) to catch interface drift.
3. Keep exact-shape examples only when invariants are stable; otherwise keep boolean success examples.

## 6. Reusable inversion lemmas (current branch)

- `extract_stmt_instr_success_inv`
- `extract_stmt_seq_success_inv`
- `extract_stmt_loop_success_inv`
- `extract_stmt_guard_success_inv`
- `extract_stmts_cons_success_inv`
- `extract_stmts_nil_success_inv`
- `instance_list_semantics_inv`
- `poly_instance_list_semantics_inv`
- `test_to_aff_complete`
- `guard_constraints_complete`
- `loop_constraints_complete`
- `firstn_length_decompose`
- `flatten_instrs_singleton_inv`
- `flatten_instr_nth_in_inv`
- `flatten_instr_nth_index_split`
- `permutation_singleton`
- `instr_point_list_semantics_singleton_inv`
- `nodup_all_eq_singleton`
- `flatten_instr_nth_depth0_emptydom_singleton`
- `loop_semantics_aux_implies_loop_semantics`
- `loop_instance_list_semantics_implies_loop_semantics`
- `flattened_guard_nonempty_implies_true`
- `guard_false_core_case`
- `guard_branch_reduce`
- `guard_constraints_sound_in_poly`
- `loop_constraints_sound_lifted`
- `flatten_instr_nth_depth0_singleton_if_in_poly`
- `instr_branch_core_with_constrs`
- `flattened_guard_false_implies_nil_constrs`
- `guard_false_core_case_constrs`
- `seq_pos_points_order`
- `rebase_ip_nth`
- `rebase_ip_nth_injective_ge`
- `np_lt_rebase_ip_nth_iff`
- `instr_point_sema_rebase_ip_nth`
- `instr_point_list_semantics_map_rebase_ip_nth`
- `flatten_instr_nth_map_rebase_ip_nth`
- `flatten_instrs_app_inv_rebase`

## 7. Current theorem split (recommended)

- Keep `extractor_correct` as a thin wrapper (`Qed`).
- Focus proof work on exactly one semantic core lemma:
  - `extract_stmt_to_loop_semantics_core`

Use these first in `extractor_correct` before opening recursive semantics goals.

## 8. Critical design warning for final hole

- The remaining hole cannot be closed cleanly with a theorem specialized to:
  - `constrs = []`
  - `iter_depth = 0`
  - `sched_prefix = []`
- `Instr` fits that shape, but `Guard true` and `Loop` recurse through:
  - non-empty/lifted constraints,
  - increased `iter_depth`,
  - iterator-dependent sublists.
- Plan the final closure around a stronger internal lemma carrying iterator-prefix context (or equivalent partition invariant) before pushing tactic-level details.
