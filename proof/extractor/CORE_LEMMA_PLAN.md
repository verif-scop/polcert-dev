# Extractor Core Lemma Plan

Date: 2026-03-05

## Target
Prove `extract_stmt_to_loop_semantics_core` in `src/Extractor.v`.

## Current Proven Pieces
- Constrained recursive bridge is implemented:
  - `extract_stmt_to_loop_semantics_core_sched_constrs_fuel` (`Qed`)
  - `extract_stmt_to_loop_semantics_core_sched_constrs` (`Qed`)
- Wrapper-level TODOs are proved:
  - `core_sched_seq_head_todo`
  - `core_sched_seq_tail_todo`
  - `core_sched_guard_true_todo`
  - `core_sched_loop_todo`

## Remaining Branch Work
1. Constrained loop branch:
- `core_sched_loop_constrs_len_todo` remains admitted.
- This is the semantic heart: lifted constraints/schedule + iterator reconstruction.

## Refined Technical Constraint (important)
- The constrained theorem currently handles arbitrary `constrs` at `iter_depth=0`, but defers:
  - loop lifting semantics reconstruction.
- Final closure still needs either:
  - proving `core_sched_loop_constrs_len_todo`, or
  - replacing it by a stronger loop-specific decomposition theorem.

## Latest+9 Observation (important)
- Newly fixed combined point lemma now compiles:
  - `flattened_point_loop_bounds_and_timestamp_head`.
- The remaining proof gap is now explicitly a recursion-interface gap:
  - available recursive theorem shape: depth-0 entry;
  - needed in loop hole: per-iteration body semantics for extraction produced at `iter_depth=1`.

## Latest+10 Observation
- Added stronger in-hole facts already proved and available:
  - every point head is bounded (`Hpoint_head_in_bounds`);
  - out-of-range head filters are empty (`Hlt_lb_nil`, `Hge_ub_nil`);
  - in-range threshold filters collapse to identity (`Hge_lb_eq_sorted`, `Hlt_ub_eq_sorted`).
- Added reusable list helper:
  - `filter_all_true_id`.

## Latest+11 Observation
- Added in-hole normalized range identity:
  - `Hrange_eq_sorted : filter in_loop_range sorted_ipl = sorted_ipl`.
- Remaining work is now concentrated on:
  - decomposing `Hrange_eq_sorted` into per-iterator slices,
  - proving each slice maps to body semantics under `(i :: rev envv)`,
  - rebuilding `IterSem.iter_semantics` over `Zrange lbv ubv`.

## Latest+12 Observation
- New split infrastructure is now available:
  - `sorted_sched_filter_split_by_prefix_head_eq`
  - in-hole `Hsem_split_head_eq` (state-threaded `<i / =i / >i` split).
- Next direct target:
  - upgrade from single-threshold splits to progressive `i`-indexed slices over
    `Zrange lbv ubv`, then connect each `=i` slice to body semantics.

## Latest+14 Observation
- New sorted-step helper is now proved:
  - `sorted_sched_filter_ltb_succ_by_prefix_head`
- In-hole step decomposition now exists:
  - `Hlt_succ_split` (list-level `i -> i+1` split),
  - `Hsem_prefix_step` (semantics-level split on `< i+1`),
  - `Hpref_lb_eq_st1` (base prefix state at `lb` collapses to start state).
- Remaining unresolved objective is now clearer:
  - convert each `filter (head_ts = i)` slice semantic step into
    `Loop.loop_semantics body (i :: rev envv)` (depth-1 body bridge),
  - then fold these steps into `IterSem.iter_semantics` for `Loop.LLoop`.

## Latest+15 Observation
- Equality-slice iteration skeleton is now formalized in-hole:
  - `Hsem_pref_ub`
  - `Hiter_prefix`
  - `Hiter_eq_range`
- New reusable helper:
  - `iter_semantics_app`
- This means the loop-hole no longer lacks `Zrange`/slice threading machinery.
- Remaining core target is now a single semantic bridge family:
  - for each `i` in range, show the `head_ts = i` slice semantics corresponds to
    `Loop.loop_semantics body (i :: rev envv)`.

## Latest+16 Observation
- Final loop hole now has an explicit range split and one side is fully discharged:
  - `lbv >= ubv` solved (empty `Zrange`, empty sorted points, direct `Loop.LLoop`).
- Therefore unresolved work is now strictly the non-empty range branch:
  - `lbv < ubv` + per-`i` body bridge.

## Suggested Next Decomposition
1. Close `core_sched_loop_constrs_len_todo`:
- partition points by loop iterator head row;
- prove per-iteration constrained body semantics;
- rebuild `IterSem.iter_semantics` and apply `Loop.LLoop`.

2. Add (or derive) a depth-bridge lemma for body recursion:
- target shape:
  - from `extract_stmt body ... iter_depth=1 ... = Okk pis`
  - and an iterator value `i`
  - derive a theorem-invocable body semantic obligation under env `(i :: rev envv)`.
- without changing `Loop`/`PolyLang` semantics.

### Newly available helpers (2026-03-05 latest+18)
- Guard/constraints:
  - `guard_constraints_sound_in_poly`
  - `flattened_guard_false_implies_nil_constrs`
  - `guard_false_core_case_constrs`
- Loop constraints:
  - `loop_constraints_sound_lifted`
- Instr base (generalized):
  - `flatten_instr_nth_depth0_singleton_if_in_poly`
  - `instr_branch_core_with_constrs`
- Seq schedule order:
  - `seq_pos_points_order`
- nth-offset handling:
  - `rebase_ip_nth`
  - `rebase_ip_nth_injective_ge`
  - `np_lt_rebase_ip_nth_iff`
  - `instr_point_sema_rebase_ip_nth`
  - `instr_point_list_semantics_map_rebase_ip_nth`
  - `flatten_instr_nth_map_rebase_ip_nth`
  - `flatten_instrs_app_inv_rebase`
  - `check_extracted_wf_app_inv`
  - `instr_point_sched_le_rebase_ip_nth`
  - `sorted_sched_le_map_rebase_ip_nth`
  - `flattened_point_seq_pos_timestamp_with_prefix`
  - `flattened_stmts_pos_ge_with_prefix`
  - `seq_cons_cross_lt_by_nth_with_prefix`
  - `extract_stmts_cons_sorted_split_by_nth` (generic `sched_prefix`)
  - `extract_stmts_cons_semantics_split_by_nth`
  - `sorted_sched_filter` (for filtered-sublists sortedness under `instr_point_sched_le`)

### Newly available loop-focused invariants (2026-03-05 latest+5)
- `skipn_length_S_singleton`
- `flattened_point_loop_bounds`
- `flattened_point_loop_timestamp_head`
- `nth_after_prefix_singleton`
- `sorted_sched_filter_split_by_prefix_head_bound`
- Loop-hole skeleton now already contains:
  - `Hpoint_bounds : forall ip in sorted_ipl, exists i, lb <= i < ub`
  - `Hpoint_ts_head : forall ip in sorted_ipl, exists i tsuf, ts(ip)=outer_prefix++[i]++tsuf`
  - `Hsplit_head_bound : forall b, sorted_ipl = filter(head<b) ++ filter(head>=b)`

3. Use `instr_point_list_semantics_app_inv` + concatenation to rebuild loop constructors.

## Risk
- The remaining admit is structural, not local arithmetic:
  - iterator-index/timestamp partitioning for loop reconstruction.
- Main subtlety is `iter_depth=1` extraction at loop body versus `Loop.LLoop`'s per-iteration environment threading.

## Latest+17 Observation
- The previous monolithic loop admit was mechanically decomposed:
  - `core_sched_loop_constrs_len_todo` now finishes (`Qed`),
  - one explicit bridge lemma remains admitted:
    `loop_slice_to_body_semantics_todo`.
- This gives a clean closure target:
  - prove only the slice bridge,
  - keep the already-closed `Zrange` iteration assembly untouched.

## Latest+18 Observation
- The current single-hole work should now follow `proof/extractor/PROOF_STACK.md`.
- Active top frame is fixed to:
  - `loop_slice_to_body_semantics_todo`,
  - with concrete candidate lemmas and immediate actions already listed.
- Rule for next iterations:
  - push subgoals there first, then prove in Coq, then pop with exact closing lemma.

## Latest+20 Observation
- `loop_slice_to_body_semantics_todo` is no longer an empty admit:
  - it now contains stabilized context setup (`Hbodyext`, `Hwf_body`, `Hconstr_body`).
- Remaining proof work is now a single explicit bridge:
  - from `Hslice` (`head_ts = i` filtered semantics),
  - reconstruct body-local flatten/sorted/permutation witnesses,
  - then finish with constrained core theorem application.

## Next Proof Target (exact)
1. Replace `loop_slice_to_body_semantics_todo` by a provable statement with sufficient hypotheses.
2. Prove it by deriving body semantics for a fixed `i` slice (`head_ts = i`) under env `(i :: rev envv)`.
3. Keep `core_sched_loop_constrs_len_todo` script stable (it should need no structural rewrite after bridge proof).
