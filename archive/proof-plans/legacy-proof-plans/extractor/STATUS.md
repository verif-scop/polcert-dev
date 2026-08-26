# Extractor Proof Status

Date: 2026-03-06

## Repo Snapshot
- Container repo: `/polcert`
- Branch/commit: `extractor` / `92e1407`
- Build status:
  - `opam exec -- coqc $(cat _CoqProject) src/Extractor.v` passes
  - `opam exec -- coqc $(cat _CoqProject) driver/PolOpt.v` passes
  - `opam exec -- make -s check-admitted` prints `Nothing admitted.`

## Main Theorem Status
- `extractor_correct`: `Qed`
- `extract_stmt_to_loop_semantics_core`: `Qed`
- `extract_stmt_to_loop_semantics_core_sched`: `Qed`
- `extract_stmt_to_loop_semantics_core_sched_constrs_fuel`: `Qed`
- `extract_stmt_to_loop_semantics_core_sched_constrs`: `Qed`
- `core_sched_stmt_stmts_constrs_mutual`: `Qed`
- `core_sched_stmt_stmts_constrs_prefix_mutual`: `Qed`
- `loop_slice_to_body_semantics_todo`: `Qed`
- `core_sched_loop_constrs_len_todo`: `Qed`

## Final Closure Summary (2026-03-06 latest+24)
- The last remaining admit was `core_sched_stmt_stmts_constrs_prefix_mutual`.
- Its `Loop` case is now proved.
- The successful proof strategy was:
  - generalize the old loop reconstruction to arbitrary `prefix`
  - keep the semantics slice-aware via `flatten_instrs_prefix_slice`
  - reconstruct per-`x` body slices with `loop_slice_filter_prefix_slice_gen`
  - recurse on `IHbody` at `prefix ++ [x]`
  - convert the outer loop iteration with `iter_semantics_refine_with_state_eq`
- Important alignment detail:
  - keep the target body env as `x :: rev (envv ++ prefix)` to match `Loop.LLoop`
  - rewrite recursive IH env `rev (envv ++ (prefix ++ [x]))` to that shape with
    `symmetry; rewrite app_assoc; apply rev_unit`
- Final proof-script fixes that mattered:
  - remove the stale theorem-tail `Admitted.` and close with `Qed.`
  - fix nested bullet level after `split.` (`+`/`*`, not `-`)

## Key Infrastructure Added Along The Way
- Prefix-aware slice/loop lemmas:
  - `flattened_point_loop_index_prefix_bounds_and_timestamp_head_slice`
  - `loop_slice_point_fixed_prefix_slice`
  - `flattened_point_loop_fixed_prefix_implies_timestamp_head_slice`
  - `loop_slice_filter_prefix_slice_gen`
- Prefix-aware schedule helpers:
  - `flattened_point_schedule_has_top_prefix_slice`
  - `flattened_point_seq_pos_timestamp_with_prefix_slice`
- Prefix-aware recursive theorem support:
  - `flatten_instrs_prefix_slice_nil_implies_nil`
  - `flatten_instr_prefix_slice_singleton_if_in_poly`
  - `instr_branch_core_with_constrs_prefix_len`
  - `iter_semantics_shift_start_with_state_eq`
  - `iter_semantics_refine_with_state_eq`
- Earlier loop reconstruction machinery still used in the final close:
  - `Hsplit_head_eq` / `Hsem_split_head_eq`
  - `Hiter_prefix`, `Hiter_eq_range`, `Hiter_eq_range_from_st1`
  - `loop_constraints_sound_lifted`
  - `seq_cons_semantics_with_eq`, `guard_true_semantics_with_eq`

## Current Position
- Extractor correctness proof is closed at the Coq level.
- There is no remaining admit in `src/Extractor.v`.
- This does not mean the whole project is finished.
- The next project-level proof gaps are now outside extractor-core closure:
  - no explicit end-to-end `Opt_correct` theorem yet
  - codegen integration still has the known `depth` semantic gap
  - overflow/guard story is still a later milestone

## What To Preserve If Revisiting This Proof
- Do not change `Loop` or `PolyLang` semantic definitions to fix env alignment.
- Do not lower a fixed `head_ts = x` slice into a plain unrestricted program.
- Keep the recursive theorem prefix-aware all the way down.
- When a `replace` proof on `rev (...)` behaves strangely, check goal direction;
  `replace` may ask for the reverse equality.

## Validation Commands
1. `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- coqc $(cat _CoqProject) src/Extractor.v'`
2. `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make -s check-admitted'`
3. `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- coqc $(cat _CoqProject) driver/PolOpt.v'`
