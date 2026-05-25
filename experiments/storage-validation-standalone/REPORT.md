# Standalone Validation Report

This report is generated from `run.py`.  It records finite executable
checks over hand-modeled source/target fragments.  It is evidence that
the witness shapes are non-vacuous; it is not a proof-producing
validator or a universal translation-validation theorem.

| Case | Semantic Difference | Checked Obligations |
| --- | --- | --- |
| `source_no_alias_abstraction` | precondition / logical blocks distinct | distinct source names are interpreted as distinct logical blocks<br>logical read/write footprints are computed under the no-alias abstraction<br>validator assumptions would be unsound if A and B had the same physical base |
| `affine_interchange` | instance-preserving / storage-preserving | bijection on statement instances<br>read/write access functions are identical<br>no loop-carried dependences are introduced or reordered |
| `index_set_splitting` | instance-preserving / domain partition | target subdomains are disjoint<br>target subdomains exactly cover the source domain<br>each target substatement projects to exactly one source instance |
| `ordinary_tiling` | instance-preserving / grouped schedule | tile projection covers every source instance<br>tile projection is injective for ordinary non-overlapped tiling<br>access functions are unchanged |
| `scalar_privatization_expansion` | same instances / scalar storage expansion | private storage map rho(i) = tmp_exp[i] is injective over live private classes<br>each private read is dominated by its same-class write<br>expanded storage is not live-out or observable except through B |
| `private_copy_boundary` | same instances / private live-in and live-out boundary copies | every required public live-in has a copy-in boundary pair<br>every required public live-out has a unique copy-out boundary pair<br>boundary pairs use declared private storage cells<br>boundary copy private cells are unique on the private side<br>copy-in/copy-out boundary values match across public and private cells |
| `layout_remap_padding` | same instances / injective physical address remap | logical-to-physical address map is injective over the logical domain<br>all rewritten addresses are within allocated physical storage<br>padding cells are outside the observable logical image<br>target accesses use the declared layout rename at the access-function level<br>transpose-style accesses use a declared index-permutation layout witness<br>linearized accesses use a declared affine layout witness<br>one declared-layout checker covers same-index, permutation, and affine cases<br>layout boundary values match the represented logical cells |
| `scratchpad_packing` | same instances / copy-mediated local storage | copy-in covers every later local read<br>local buffer address k consistently maps to source B[kk+k]<br>public-to-local copy mapping is injective during each tile<br>local buffer lifetime is tile-scoped and fresh between tiles |
| `scratchpad_copy_out` | same instances / copy-mediated local update plus commit | copy-in initializes each local cell before local compute<br>copy-out commits every updated logical cell exactly once<br>copy helper instance roles align with copy protocol events<br>local writes are unobservable until committed |
| `scalar_promotion` | same instances / array cell simulated by scalar | entry load initializes the scalar from the promoted cell<br>all reads and writes in the promoted region are simulated by the scalar<br>promoted scalar storage is compatible with the source cell<br>exit store commits the scalar back before the cell is observed |
| `array_contraction` | same logical values / non-injective conflict-safe storage reuse | non-injective map rho(t,i) = (t mod 2,i) is allowed only for non-conflicting values<br>explicit live intervals cover every overlap conflict under the schedule<br>reuse boundary mapping covers every observable source live-out<br>reused physical boundary cells are storage-compatible with represented logical cells<br>reuse boundary values match the projected physical cells<br>final observable row projects from the correct parity buffer |
| `inter_array_reuse` | same instances / cross-array lifetime-based storage reuse | logical arrays mapped to one buffer have non-overlapping live ranges<br>shared physical buffer cells are used only by non-overlapping lifetimes<br>reused cells are size/alignment compatible with the shared buffer<br>all accesses in each lifetime interval are rewritten consistently |
| `array_expansion_versioning` | same instances / more physical versions plus copy-out | each read selects the version produced by the same logical iteration<br>extra versions project back to one source logical array<br>selected committed versions cover source live-outs exactly once<br>selected target versions are storage-compatible with source live-outs<br>selected version values match represented source live-outs<br>copy-out commits exactly the final source-observable version |
| `overlapped_tiling` | instance-count-changing / private recomputation plus unique commit | projection maps every target computation to a valid source instance<br>commit instances form an exact cover of source live-out instances<br>tile-local dependence closure covers every committed B computation<br>tile-local producers precede their consumers in the target trace<br>duplicated halo/internal writes are tile-local and invisible |
| `reduction_privatization` | parallel/storage privatization plus merge | iteration chunks are disjoint and exactly cover the source reduction domain<br>private accumulators are fresh per chunk<br>merge order consumes every private accumulator exactly once<br>merge-order accumulator values fold to the final reduction value<br>merge operator is closed, associative, commutative, and has an identity on the finite carrier |
| `double_buffering` | same logical values / phase-separated ping-pong storage | next buffer is written before it is read in the following phase<br>cur buffer remains live until the phase's computation completes<br>next-live values come from the phase write snapshot<br>swap implements the projection from physical buffer to logical time<br>final phase value snapshot matches the final-live physical cells<br>final phase projection covers every logical live-out<br>phase projection values match final physical buffer cells |
| `storage_view_composition` | composition / layout projection followed by private erasure | target-to-mid private-erasure view ignores only fresh private cells<br>mid-to-source layout view projects padded physical cells to logical cells<br>the two views agree on the observable intermediate cells<br>the composed cell view covers exactly the public source and target cells<br>there exists an intermediate state satisfying both view relations<br>the composed observation relates target physical cells to source logical cells<br>access remap witnesses compose through the same intermediate cells |

## Negative Tests

| Test | Related Case | Expected Failure |
| --- | --- | --- |
| `missing_private_fill` | `scalar_privatization_expansion` | tmp_exp[0] read before write |
| `private_missing_liveout_copy` | `private_copy_boundary` | private live-out has no copy-out |
| `private_duplicate_liveout_copy` | `private_copy_boundary` | private live-out copy-out is not unique |
| `private_aliasing_copyin_private` | `private_copy_boundary` | private copy-in target is not unique |
| `private_bad_copyout_value` | `private_copy_boundary` | copy-out boundary value mismatch |
| `scalar_promotion_incompatible_storage` | `scalar_promotion` | promoted scalar storage spec mismatch |
| `source_alias_violation` | `source_no_alias_abstraction` | A and B may alias |
| `aliased_layout_map` | `layout_remap_padding` | layout map aliases logical cells |
| `layout_bad_boundary_value` | `layout_remap_padding` | layout boundary value mismatch |
| `layout_bad_access_remap` | `layout_remap_padding` | layout access remap changes affine index |
| `layout_bad_permutation_access_remap` | `layout_remap_padding` | target access does not use declared index permutation |
| `layout_bad_affine_access_remap` | `layout_remap_padding` | target access does not use declared affine layout |
| `missing_copy_in` | `scratchpad_packing` | Bp[3] used before copy-in |
| `scratchpad_bad_local_remap` | `scratchpad_packing` | public cells mapped to local buffer are not injective |
| `missing_copy_out` | `scratchpad_copy_out` | copy-out does not commit every logical output |
| `scratchpad_bad_copy_instance_role` | `scratchpad_copy_out` | copy helper instance role does not match copy event |
| `missing_contraction_conflict_pair` | `array_contraction` | live-overlap conflict missing for (0, 0) and (1, 0) |
| `mod_one_contraction_conflict` | `array_contraction` | conflicting values (0, 0) and (1, 0) share (0, 0) |
| `contraction_missing_boundary_liveout` | `array_contraction` | reuse boundary mapping does not cover every source live-out |
| `contraction_incompatible_storage` | `array_contraction` | reuse boundary storage spec mismatch |
| `inter_array_live_overlap` | `inter_array_reuse` | T1 and T2 live ranges overlap |
| `inter_array_same_buffer_live_overlap` | `inter_array_reuse` | shared buffer cells have overlapping live ranges |
| `inter_array_incompatible_storage` | `inter_array_reuse` | T2 is not storage-compatible with Buf |
| `missing_expansion_copy_out` | `array_expansion_versioning` | final X differs without copy-out: {0: 0, 1: 0} != {0: 2, 1: 3} |
| `duplicate_selected_version` | `array_expansion_versioning` | selected target versions are not unique |
| `expansion_incompatible_version_storage` | `array_expansion_versioning` | selected version storage spec mismatch |
| `duplicate_overlap_commit` | `overlapped_tiling` | more than one tile commits a source output |
| `overlap_missing_halo_closure` | `overlapped_tiling` | tile does not locally close B dependences |
| `overlap_bad_producer_order` | `overlapped_tiling` | tile producer does not precede consumer |
| `overlapping_reduction_chunks` | `reduction_privatization` | reduction chunks overlap |
| `reduction_missing_merge_accumulator` | `reduction_privatization` | reduction merge order does not cover private accumulators exactly |
| `reduction_non_associative_law` | `reduction_privatization` | reduction merge operator is not associative on carrier |
| `reduction_wrong_final_value` | `reduction_privatization` | reduction merge gives different result |
| `double_buffer_without_swap` | `double_buffering` | swap does not expose the current time row |
| `double_buffer_bad_next_value` | `double_buffering` | next-live value 0 does not come from phase write or entry-live value |
| `double_buffer_bad_projection` | `double_buffering` | phase projection does not cover logical live-outs |
| `double_buffer_bad_final_snapshot` | `double_buffering` | final phase snapshot does not match final-live cells |
| `double_buffer_bad_projection_value` | `double_buffering` | phase projection value mismatch |
| `composition_bad_intermediate_public` | `storage_view_composition` | private-erasure view cannot relate target to intermediate state |
| `composition_bad_access_midpoint` | `storage_view_composition` | composed access remap is invalid |
| `composition_bad_mid_observables` | `storage_view_composition` | cell-view composition should reject incompatible intermediate observables |
