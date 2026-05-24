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
| `layout_remap_padding` | same instances / injective physical address remap | logical-to-physical address map is injective over the logical domain<br>all rewritten addresses are within allocated physical storage<br>padding cells are outside the observable logical image |
| `scratchpad_packing` | same instances / copy-mediated local storage | copy-in covers every later local read<br>local buffer address k consistently maps to source B[kk+k]<br>local buffer lifetime is tile-scoped and fresh between tiles |
| `scratchpad_copy_out` | same instances / copy-mediated local update plus commit | copy-in initializes each local cell before local compute<br>copy-out commits every updated logical cell exactly once<br>local writes are unobservable until committed |
| `scalar_promotion` | same instances / array cell simulated by scalar | entry load initializes the scalar from the promoted cell<br>all reads and writes in the promoted region are simulated by the scalar<br>exit store commits the scalar back before the cell is observed |
| `array_contraction` | same logical values / non-injective conflict-safe storage reuse | non-injective map rho(t,i) = (t mod 2,i) is allowed only for non-conflicting values<br>conflict relation is derived from live ranges under the schedule<br>final observable row projects from the correct parity buffer |
| `inter_array_reuse` | same instances / cross-array lifetime-based storage reuse | logical arrays mapped to one buffer have non-overlapping live ranges<br>reused cells are type/size compatible<br>all accesses in each lifetime interval are rewritten consistently |
| `array_expansion_versioning` | same instances / more physical versions plus copy-out | each read selects the version produced by the same logical iteration<br>extra versions project back to one source logical array<br>copy-out commits exactly the final source-observable version |
| `overlapped_tiling` | instance-count-changing / private recomputation plus unique commit | projection maps every target computation to a valid source instance<br>commit instances form an exact cover of source live-out instances<br>duplicated halo/internal writes are tile-local and invisible |
| `reduction_privatization` | parallel/storage privatization plus merge | iteration chunks are disjoint and exactly cover the source reduction domain<br>private accumulators are fresh per chunk<br>merge operator is associative for this integer example |
| `double_buffering` | same logical values / phase-separated ping-pong storage | next buffer is written before it is read in the following phase<br>cur buffer remains live until the phase's computation completes<br>swap implements the projection from physical buffer to logical time |

## Negative Tests

| Test | Related Case | Expected Failure |
| --- | --- | --- |
| `missing_private_fill` | `scalar_privatization_expansion` | tmp_exp[0] read before write |
| `source_alias_violation` | `source_no_alias_abstraction` | A and B may alias |
| `aliased_layout_map` | `layout_remap_padding` | layout map aliases logical cells |
| `missing_copy_in` | `scratchpad_packing` | Bp[3] used before copy-in |
| `missing_copy_out` | `scratchpad_copy_out` | copy-out does not commit every logical output |
| `mod_one_contraction_conflict` | `array_contraction` | conflicting values (0, 0) and (1, 0) share (0, 0) |
| `inter_array_live_overlap` | `inter_array_reuse` | T1 and T2 live ranges overlap |
| `missing_expansion_copy_out` | `array_expansion_versioning` | final X differs without copy-out: {0: 0, 1: 0} != {0: 2, 1: 3} |
| `duplicate_overlap_commit` | `overlapped_tiling` | more than one tile commits a source output |
| `overlapping_reduction_chunks` | `reduction_privatization` | reduction chunks overlap |
| `double_buffer_without_swap` | `double_buffering` | swap does not expose the current time row |
