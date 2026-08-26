# Standalone Storage Coverage

Generated from `standalone_positive.log` and `standalone_negative.log`.

- positive cases: 19
- negative cases: 76

## Positive Cases

| Case | Classification | Obligations | Negative checks |
|---|---|---:|---:|
| `source_no_alias_abstraction` | precondition / logical blocks distinct | 4 | 3 |
| `contextual_frame_preservation` | contextual frame / allowed writes plus preserved frame snapshot | 5 | 3 |
| `affine_interchange` | instance-preserving / storage-preserving | 3 | 0 |
| `index_set_splitting` | instance-preserving / domain partition | 3 | 0 |
| `ordinary_tiling` | instance-preserving / grouped schedule | 3 | 0 |
| `scalar_privatization_expansion` | same instances / scalar storage expansion | 5 | 4 |
| `private_copy_boundary` | same instances / private live-in and live-out boundary copies | 8 | 7 |
| `private_access_local_instantiation` | same instances / access-level private storage instantiation | 4 | 3 |
| `layout_remap_padding` | same instances / injective physical address remap | 10 | 7 |
| `scratchpad_packing` | same instances / copy-mediated local storage | 9 | 6 |
| `scratchpad_copy_out` | same instances / copy-mediated local update plus commit | 4 | 2 |
| `scalar_promotion` | same instances / array cell simulated by scalar | 4 | 1 |
| `array_contraction` | same logical values / non-injective conflict-safe storage reuse | 7 | 5 |
| `inter_array_reuse` | same instances / cross-array lifetime-based storage reuse | 5 | 4 |
| `array_expansion_versioning` | same instances / more physical versions plus copy-out | 9 | 6 |
| `overlapped_tiling` | instance-count-changing / private recomputation plus unique commit | 9 | 7 |
| `reduction_privatization` | parallel/storage privatization plus merge | 8 | 7 |
| `double_buffering` | same logical values / phase-separated ping-pong storage | 10 | 8 |
| `storage_view_composition` | composition / layout projection followed by private erasure | 7 | 3 |

## Details

### `source_no_alias_abstraction`

Classification: precondition / logical blocks distinct

Obligations:
- distinct source names are interpreted as distinct logical blocks
- logical read/write footprints are computed under the no-alias abstraction
- finite source accesses are covered by their declared object footprints
- validator assumptions would be unsound if A and B had the same physical base

Rejected malformed witnesses:
- `source_alias_violation`: A and B may alias
- `source_access_unknown_object`: source access object has no declared footprint
- `source_access_outside_footprint`: source access falls outside declared object footprint

### `contextual_frame_preservation`

Classification: contextual frame / allowed writes plus preserved frame snapshot

Obligations:
- fragment writes are included in a declared allowed-write set
- allowed writes are disjoint from context-owned frame cells
- every context-frame cell has aligned before/after snapshot evidence
- frame snapshot values are preserved across the fragment
- observable transformed output matches the source output on non-frame cells

Rejected malformed witnesses:
- `frame_write_not_allowed`: fragment write is not allowed
- `frame_allowed_overlaps_context`: allowed writes overlap frame
- `frame_value_changed`: frame value changed across fragment

### `affine_interchange`

Classification: instance-preserving / storage-preserving

Obligations:
- bijection on statement instances
- read/write access functions are identical
- no loop-carried dependences are introduced or reordered

### `index_set_splitting`

Classification: instance-preserving / domain partition

Obligations:
- target subdomains are disjoint
- target subdomains exactly cover the source domain
- each target substatement projects to exactly one source instance

### `ordinary_tiling`

Classification: instance-preserving / grouped schedule

Obligations:
- tile projection covers every source instance
- tile projection is injective for ordinary non-overlapped tiling
- access functions are unchanged

### `scalar_privatization_expansion`

Classification: same instances / scalar storage expansion

Obligations:
- each (source instance, source scalar cell) selects one expanded private cell
- private storage map rho(i) = tmp_exp[i] is injective over live private classes
- all scalar expansion events use the declared private cell for their key
- each private read is dominated by its same-class write
- expanded storage is not live-out or observable except through B

Rejected malformed witnesses:
- `missing_private_fill`: tmp_exp[0] read before write
- `scalar_expansion_duplicate_private`: expanded private cells are not fresh
- `scalar_expansion_event_mismatch`: scalar expansion event uses the wrong private cell
- `scalar_expansion_read_before_fill`: scalar expansion read occurs before its private fill

### `private_copy_boundary`

Classification: same instances / private live-in and live-out boundary copies

Obligations:
- every required public live-in has a copy-in boundary pair
- every required public live-out has a unique copy-out boundary pair
- boundary pairs use declared private storage cells
- private trace read/write cells are declared private cells
- declared private cells are within private array bounds
- boundary copy private cells are unique on the private side
- copy-in/copy-out boundary values match across public and private cells
- boundary public/private cells are storage-compatible for copy-in and copy-out

Rejected malformed witnesses:
- `private_missing_liveout_copy`: private live-out has no copy-out
- `private_duplicate_liveout_copy`: private live-out copy-out is not unique
- `private_aliasing_copyin_private`: private copy-in target is not unique
- `private_trace_undeclared_cell`: private trace uses undeclared private cell
- `private_out_of_declared_bounds`: private cell falls outside declared bounds
- `private_bad_copyout_value`: copy-out boundary value mismatch
- `private_incompatible_boundary_storage`: private boundary storage spec mismatch

### `private_access_local_instantiation`

Classification: same instances / access-level private storage instantiation

Obligations:
- symbolic private access trace is use-def well formed
- each finite domain point instantiates private accesses to declared cells
- instantiated private access cells are hidden from the public view
- instantiated private access cells are within declared private bounds

Rejected malformed witnesses:
- `private_access_symbolic_read_before_write`: private access read occurs before matching access write
- `private_access_instance_undeclared_cell`: instantiated private access cell is undeclared
- `private_access_instance_out_of_bounds`: instantiated private access cell falls outside declared bounds

### `layout_remap_padding`

Classification: same instances / injective physical address remap

Obligations:
- logical-to-physical address map is injective over the logical domain
- all rewritten addresses are within allocated physical storage
- padding cells are outside the observable logical image
- target accesses use the declared layout rename at the access-function level
- transpose-style accesses use a declared index-permutation layout witness
- linearized accesses use a declared affine layout witness
- one declared-layout checker covers same-index, permutation, and affine cases
- allocated physical layout cells are within declared array extents
- layout boundary values match the represented logical cells
- mapped physical layout cells are storage-compatible with represented logical cells

Rejected malformed witnesses:
- `aliased_layout_map`: layout map aliases logical cells
- `layout_bad_boundary_value`: layout boundary value mismatch
- `layout_incompatible_storage`: layout storage spec mismatch
- `layout_out_of_declared_bounds`: allocated layout cell falls outside declared array bounds
- `layout_bad_access_remap`: layout access remap changes affine index
- `layout_bad_permutation_access_remap`: target access does not use declared index permutation
- `layout_bad_affine_access_remap`: target access does not use declared affine layout

### `scratchpad_packing`

Classification: same instances / copy-mediated local storage

Obligations:
- copy-in covers every later local read
- local buffer address k consistently maps to source B[kk+k]
- public-to-local copy mapping is injective during each tile
- copy mapping public cells belong to the declared public-cell set
- copy mapping local cells belong to the declared local-buffer set
- declared public cells are within public array bounds
- declared local-buffer cells are within local array bounds
- local buffer cells are storage-compatible with represented public cells
- local buffer lifetime is tile-scoped and fresh between tiles

Rejected malformed witnesses:
- `missing_copy_in`: Bp[3] used before copy-in
- `scratchpad_bad_local_remap`: public cells mapped to local buffer are not injective
- `scratchpad_incompatible_local_storage`: scratchpad local storage spec mismatch
- `scratchpad_local_out_of_bounds`: scratchpad local cell falls outside declared bounds
- `scratchpad_public_undeclared`: copy mapping public cell is not declared
- `scratchpad_public_out_of_bounds`: scratchpad public cell falls outside declared bounds

### `scratchpad_copy_out`

Classification: same instances / copy-mediated local update plus commit

Obligations:
- copy-in initializes each local cell before local compute
- copy-out commits every updated logical cell exactly once
- copy helper instance roles align with copy protocol events
- local writes are unobservable until committed

Rejected malformed witnesses:
- `missing_copy_out`: copy-out does not commit every logical output
- `scratchpad_bad_copy_instance_role`: copy helper instance role does not match copy event

### `scalar_promotion`

Classification: same instances / array cell simulated by scalar

Obligations:
- entry load initializes the scalar from the promoted cell
- all reads and writes in the promoted region are simulated by the scalar
- promoted scalar storage is compatible with the source cell
- exit store commits the scalar back before the cell is observed

Rejected malformed witnesses:
- `scalar_promotion_incompatible_storage`: promoted scalar storage spec mismatch

### `array_contraction`

Classification: same logical values / non-injective conflict-safe storage reuse

Obligations:
- non-injective map rho(t,i) = (t mod 2,i) is allowed only for non-conflicting values
- explicit live intervals cover every overlap conflict under the schedule
- every reused physical buffer cell is within declared rolling-buffer bounds
- reuse boundary mapping covers every observable source live-out
- reused physical boundary cells are storage-compatible with represented logical cells
- reuse boundary values match the projected physical cells
- final observable row projects from the correct parity buffer

Rejected malformed witnesses:
- `missing_contraction_conflict_pair`: live-overlap conflict missing for (0, 0) and (1, 0)
- `mod_one_contraction_conflict`: conflicting values (0, 0) and (1, 0) share (0, 0)
- `contraction_missing_boundary_liveout`: reuse boundary mapping does not cover every source live-out
- `contraction_incompatible_storage`: reuse boundary storage spec mismatch
- `contraction_target_out_of_bounds`: reuse target physical cell falls outside declared bounds

### `inter_array_reuse`

Classification: same instances / cross-array lifetime-based storage reuse

Obligations:
- logical arrays mapped to one buffer have non-overlapping live ranges
- shared physical buffer cells are used only by non-overlapping lifetimes
- shared physical buffer cells are within declared Buf bounds
- reused cells are size/alignment compatible with the shared buffer
- all accesses in each lifetime interval are rewritten consistently

Rejected malformed witnesses:
- `inter_array_live_overlap`: T1 and T2 live ranges overlap
- `inter_array_same_buffer_live_overlap`: shared buffer cells have overlapping live ranges
- `inter_array_incompatible_storage`: T2 is not storage-compatible with Buf
- `inter_array_shared_buffer_out_of_bounds`: shared buffer cell falls outside declared bounds

### `array_expansion_versioning`

Classification: same instances / more physical versions plus copy-out

Obligations:
- each read selects the version produced by the same logical iteration
- read-selected produced versions are within declared version-array bounds
- read-selected produced values match target reads
- extra versions project back to one source logical array
- selected committed versions cover source live-outs exactly once
- selected target versions are storage-compatible with source live-outs
- selected target versions are within declared version-array bounds
- selected version values match represented source live-outs
- copy-out commits exactly the final source-observable version

Rejected malformed witnesses:
- `missing_expansion_copy_out`: final X differs without copy-out: {0: 0, 1: 0} != {0: 2, 1: 3}
- `duplicate_selected_version`: selected target versions are not unique
- `expansion_incompatible_version_storage`: selected version storage spec mismatch
- `expansion_version_out_of_bounds`: selected target version falls outside declared bounds
- `expansion_read_selects_unproduced_version`: read-selected version was not produced by the expected write
- `expansion_read_version_out_of_bounds`: read-selected produced version falls outside declared bounds

### `overlapped_tiling`

Classification: instance-count-changing / private recomputation plus unique commit

Obligations:
- projection maps every target computation to a valid source instance
- commit instances form an exact cover of source live-out instances
- tile-local dependence closure covers every committed B computation
- tile-local producers precede their consumers in the target trace
- internal target writes go to tile-private cells
- commit target writes go to public commit cells exactly once
- tile-private overlap write cells are within declared private-buffer bounds
- commit overlap write cells are within declared public-output bounds
- duplicated halo/internal writes are tile-local and invisible

Rejected malformed witnesses:
- `duplicate_overlap_commit`: more than one tile commits a source output
- `overlap_missing_halo_closure`: tile does not locally close B dependences
- `overlap_bad_producer_order`: tile producer does not precede consumer
- `overlap_internal_write_public_cell`: overlap write role does not match private/commit storage
- `overlap_duplicate_commit_write_cell`: overlap commit write cells are not unique
- `overlap_private_write_out_of_bounds`: overlap private write cell falls outside declared bounds
- `overlap_commit_write_out_of_bounds`: overlap commit write cell falls outside declared bounds

### `reduction_privatization`

Classification: parallel/storage privatization plus merge

Obligations:
- iteration chunks are disjoint and exactly cover the source reduction domain
- private accumulators are fresh per chunk
- private accumulators are storage-compatible with the public reduction cell
- private accumulators are within declared accumulator-array bounds
- private accumulators are disjoint from the context escape set
- merge order consumes every private accumulator exactly once
- merge-order accumulator values fold to the final reduction value
- merge operator is closed, associative, commutative, and has an identity on the finite carrier

Rejected malformed witnesses:
- `overlapping_reduction_chunks`: reduction chunks overlap
- `reduction_missing_merge_accumulator`: reduction merge order does not cover private accumulators exactly
- `reduction_incompatible_accumulator_storage`: reduction accumulator storage spec mismatch
- `reduction_accumulator_out_of_bounds`: reduction accumulator falls outside declared bounds
- `reduction_accumulator_escape`: reduction private accumulator escapes fragment
- `reduction_non_associative_law`: reduction merge operator is not associative on carrier
- `reduction_wrong_final_value`: reduction merge gives different result

### `double_buffering`

Classification: same logical values / phase-separated ping-pong storage

Obligations:
- next buffer is written before it is read in the following phase
- cur buffer remains live until the phase's computation completes
- next-live values come from the phase write snapshot
- all phase entry/read/write/next-live cells are within declared buffer bounds
- swap implements the projection from physical buffer to logical time
- final phase value snapshot matches the final-live physical cells
- final phase projection covers every logical live-out
- phase projection values match final physical buffer cells
- final phase physical cells are storage-compatible with logical live-outs
- final phase physical cells are within declared buffer bounds

Rejected malformed witnesses:
- `double_buffer_without_swap`: swap does not expose the current time row
- `double_buffer_bad_next_value`: next-live value 0 does not come from phase write or entry-live value
- `double_buffer_bad_projection`: phase projection does not cover logical live-outs
- `double_buffer_bad_final_snapshot`: final phase snapshot does not match final-live cells
- `double_buffer_bad_projection_value`: phase projection value mismatch
- `double_buffer_incompatible_projection_storage`: phase projection storage spec mismatch
- `double_buffer_projection_out_of_bounds`: phase projection target falls outside declared bounds
- `double_buffer_phase_write_out_of_bounds`: phase protocol cell falls outside declared bounds

### `storage_view_composition`

Classification: composition / layout projection followed by private erasure

Obligations:
- target-to-mid private-erasure view ignores only fresh private cells
- mid-to-source layout view projects padded physical cells to logical cells
- the two views agree on the observable intermediate cells
- the composed cell view covers exactly the public source and target cells
- there exists an intermediate state satisfying both view relations
- the composed observation relates target physical cells to source logical cells
- access remap witnesses compose through the same intermediate cells

Rejected malformed witnesses:
- `composition_bad_intermediate_public`: private-erasure view cannot relate target to intermediate state
- `composition_bad_access_midpoint`: composed access remap is invalid
- `composition_bad_mid_observables`: cell-view composition should reject incompatible intermediate observables

