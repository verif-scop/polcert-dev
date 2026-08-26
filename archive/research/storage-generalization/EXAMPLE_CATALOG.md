# Storage Transformation Example Catalog

This catalog is generated from standalone logs, source/target example files,
hand-classified evidence status, and per-transformation example variants.

## Sufficiency Rules

- has a source/target example file
- has at least two example variants in the catalog
- has positive standalone obligations
- has negative malformed-witness checks or supplemental protocol negative cases, unless it is explicitly schedule-only
- states required witness fields
- states whether evidence is real external tooling, in-repo toy OpenScop, or standalone-only

## Summary

| Case | Files | Variants | Pos obligations | Neg checks | Supplemental negs | Evidence |
|---|---|---:|---:|---:|---:|---|
| `source_no_alias_abstraction` | yes | 2 | 4 | 3 | 0 | toy OpenScop source-footprint/no-alias witness; precondition rather than storage rewrite |
| `contextual_frame_preservation` | yes | 2 | 5 | 3 | 0 | toy OpenScop contextual-frame witness; boundary condition rather than storage rewrite |
| `affine_interchange` | yes | 2 | 3 | 0 | 0 | real schedule tooling; storage-preserving rather than storage rewrite |
| `index_set_splitting` | yes | 2 | 3 | 0 | 3 | toy OpenScop domain-partition witness; storage-preserving |
| `ordinary_tiling` | yes | 2 | 3 | 0 | 0 | real schedule/tiling tooling; storage-preserving |
| `scalar_privatization_expansion` | yes | 2 | 5 | 4 | 0 | real Candl OpenScop storage access rewrite |
| `private_copy_boundary` | yes | 2 | 8 | 7 | 0 | toy OpenScop copy-boundary witness; no current Pluto/OpenScop pass observed |
| `private_access_local_instantiation` | yes | 2 | 4 | 3 | 0 | toy OpenScop symbolic-private-access witness; no current Pluto/OpenScop pass observed |
| `layout_remap_padding` | yes | 3 | 10 | 7 | 0 | toy OpenScop access rewrite; no current Pluto/OpenScop layout pass observed |
| `scratchpad_packing` | yes | 2 | 9 | 6 | 0 | toy OpenScop copy-in/local-buffer witness; no current Pluto/OpenScop scratchpad pass observed |
| `scratchpad_copy_out` | yes | 2 | 4 | 2 | 0 | toy OpenScop copy-out witness; no current Pluto/OpenScop scratchpad copy-out pass observed |
| `scalar_promotion` | yes | 2 | 4 | 1 | 9 | toy OpenScop scalar-promotion protocol witness; standalone negatives still thin |
| `array_contraction` | yes | 2 | 7 | 5 | 0 | toy OpenScop folded-storage witness; no current Pluto/OpenScop contraction pass observed |
| `inter_array_reuse` | yes | 2 | 5 | 4 | 0 | toy OpenScop shared-buffer witness; no current Pluto/OpenScop inter-array reuse pass observed |
| `array_expansion_versioning` | yes | 2 | 9 | 6 | 0 | toy OpenScop version-selection witness; no current Pluto/OpenScop versioning pass observed |
| `overlapped_tiling` | yes | 2 | 9 | 7 | 0 | toy OpenScop duplicate/commit witness; related to overlapped/diamond tiling but not Pluto-backed here |
| `reduction_privatization` | yes | 2 | 8 | 7 | 0 | toy OpenScop reduction-merge witness; no current Pluto/OpenScop reduction privatization pass observed |
| `double_buffering` | yes | 2 | 10 | 8 | 0 | toy OpenScop phase-projection witness; no current Pluto/OpenScop double-buffering pass observed |
| `storage_view_composition` | yes | 2 | 7 | 3 | 0 | toy OpenScop view-composition witness |

## Known Gaps

No catalog-level example gaps detected.

## Per-Transformation Examples

### `source_no_alias_abstraction`

Classification: precondition / logical blocks distinct

Core files:
- source: `examples/standalone/source_no_alias_abstraction.source.c`
- target: `examples/standalone/source_no_alias_abstraction.target.c`

Example variants:
- distinct arrays: establishes variable-footprint reasoning before any storage rewrite
  source: `C[i] = A[i] + B[i]`
  target: `same storage accesses under distinct logical blocks A, B, C`
- unknown object rejected: shows why public vars need declared shapes/footprints
  source: `C[i] = P[i]`
  target: `no declared footprint for P`

Required witness fields:
- source variable footprints
- non-overlap proof for distinct variables
- in-bounds source accesses

Rejected malformed witnesses:
- `source_alias_violation`: A and B may alias
- `source_access_unknown_object`: source access object has no declared footprint
- `source_access_outside_footprint`: source access falls outside declared object footprint

Evidence status: toy OpenScop source-footprint/no-alias witness; precondition rather than storage rewrite

### `contextual_frame_preservation`

Classification: contextual frame / allowed writes plus preserved frame snapshot

Core files:
- source: `examples/standalone/contextual_frame_preservation.source.c`
- target: `examples/standalone/contextual_frame_preservation.target.c`

Example variants:
- protected frame: fragment-local storage changes cannot alter context-owned vars
  source: `B[i] = A[i] + 1; F[j] unchanged`
  target: `rewrites B only; F is protected frame`
- forbidden context write: negative shape for frame preservation
  source: `F[j] is outside the fragment write set`
  target: `target writes F[j]`

Required witness fields:
- allowed write set
- protected frame variables
- pre/post frame snapshots

Rejected malformed witnesses:
- `frame_write_not_allowed`: fragment write is not allowed
- `frame_allowed_overlaps_context`: allowed writes overlap frame
- `frame_value_changed`: frame value changed across fragment

Evidence status: toy OpenScop contextual-frame witness; boundary condition rather than storage rewrite

### `affine_interchange`

Classification: instance-preserving / storage-preserving

Core files:
- source: `examples/standalone/affine_interchange.source.c`
- target: `examples/standalone/affine_interchange.target.c`

Example variants:
- loop interchange: schedule-only baseline with identical storage accesses
  source: `for i for j S(i,j)`
  target: `for j for i S(i,j)`
- dependence-blocked interchange: why schedule legality is still required
  source: `A[i][j] = A[i][j-1] + 1`
  target: `interchange would reverse dependence`

Required witness fields:
- instance bijection
- legal schedule order
- unchanged storage accesses

Rejected malformed witnesses:
- none in standalone log; schedule-only/domain cases still need schedule legality tests elsewhere

Evidence status: real schedule tooling; storage-preserving rather than storage rewrite

### `index_set_splitting`

Classification: instance-preserving / domain partition

Core files:
- source: `examples/standalone/index_set_splitting.source.c`
- target: `examples/standalone/index_set_splitting.target.c`

Example variants:
- even/odd split: domain partition without storage rewrite
  source: `for i in [0,N) S(i)`
  target: `for even i S(i); for odd i S(i)`
- prefix/suffix split: exact-cover obligation independent of schedule shape
  source: `for i in [0,N) S(i)`
  target: `for i < K S(i); for K <= i < N S(i)`

Required witness fields:
- source domain
- target subdomains
- disjoint exact-cover proof

Rejected malformed witnesses:
- none in standalone log; schedule-only/domain cases still need schedule legality tests elsewhere

Supplemental protocol negative cases:
- target subdomains overlap
- target subdomains miss a source instance
- target changes storage access while claiming pure split

Evidence status: toy OpenScop domain-partition witness; storage-preserving

### `ordinary_tiling`

Classification: instance-preserving / grouped schedule

Core files:
- source: `examples/standalone/ordinary_tiling.source.c`
- target: `examples/standalone/ordinary_tiling.target.c`

Example variants:
- strip-mined tile: storage-preserving grouped schedule
  source: `for i in [0,N) S(i)`
  target: `for ii step T for i in tile(ii) S(i)`
- rectangular 2D tile: tile projection and exact cover in multiple dimensions
  source: `for i for j S(i,j)`
  target: `for ii,jj tiles; for i,j inside tile S(i,j)`

Required witness fields:
- tile projection
- exact domain cover
- unchanged storage accesses

Rejected malformed witnesses:
- none in standalone log; schedule-only/domain cases still need schedule legality tests elsewhere

Evidence status: real schedule/tiling tooling; storage-preserving

### `scalar_privatization_expansion`

Classification: same instances / scalar storage expansion

Core files:
- source: `examples/standalone/scalar_privatization_expansion.source.c`
- target: `examples/standalone/scalar_privatization_expansion.target.c`

Example variants:
- per-iteration scalar expansion: fresh private cell per live temporary
  source: `tmp = A[i] + 1; B[i] = tmp * 2`
  target: `tmp_exp[i] = A[i] + 1; B[i] = tmp_exp[i] * 2`
- read-before-fill rejected: dominance/use-def obligation
  source: `B[i] reads tmp after source write`
  target: `B[i] reads tmp_exp[i] before target fill`

Required witness fields:
- logical temporary live range
- fresh private cell per instance
- write-before-read evidence
- optional live-out copy

Rejected malformed witnesses:
- `missing_private_fill`: tmp_exp[0] read before write
- `scalar_expansion_duplicate_private`: expanded private cells are not fresh
- `scalar_expansion_event_mismatch`: scalar expansion event uses the wrong private cell
- `scalar_expansion_read_before_fill`: scalar expansion read occurs before its private fill

Evidence status: real Candl OpenScop storage access rewrite

### `private_copy_boundary`

Classification: same instances / private live-in and live-out boundary copies

Core files:
- source: `examples/standalone/private_copy_boundary.source.c`
- target: `examples/standalone/private_copy_boundary.target.c`

Example variants:
- copy-in and copy-out: boundary protocol for private storage
  source: `A tile is read and updated`
  target: `local tile gets copy-in, local updates, then copy-out`
- live-out missing: why final public view needs copy-out coverage
  source: `updated public A tile is observable`
  target: `local tile is updated but never committed`

Required witness fields:
- copy-in map
- copy-out map
- private live-in/live-out sets
- unique public commits

Rejected malformed witnesses:
- `private_missing_liveout_copy`: private live-out has no copy-out
- `private_duplicate_liveout_copy`: private live-out copy-out is not unique
- `private_aliasing_copyin_private`: private copy-in target is not unique
- `private_trace_undeclared_cell`: private trace uses undeclared private cell
- `private_out_of_declared_bounds`: private cell falls outside declared bounds
- `private_bad_copyout_value`: copy-out boundary value mismatch
- `private_incompatible_boundary_storage`: private boundary storage spec mismatch

Evidence status: toy OpenScop copy-boundary witness; no current Pluto/OpenScop pass observed

### `private_access_local_instantiation`

Classification: same instances / access-level private storage instantiation

Core files:
- source: `examples/standalone/private_access_local_instantiation.source.c`
- target: `examples/standalone/private_access_local_instantiation.target.c`

Example variants:
- symbolic private access: finite domains instantiate symbolic private storage
  source: `logical private temp at instance i`
  target: `private_cell[f(i)] read/write after instantiation`
- out-of-bounds instantiation: bounds are part of the certificate
  source: `private access declared over tile bounds`
  target: `f(i) exceeds private array extent`

Required witness fields:
- symbolic private access
- instantiated target private cell
- hidden/private declaration
- in-bounds proof

Rejected malformed witnesses:
- `private_access_symbolic_read_before_write`: private access read occurs before matching access write
- `private_access_instance_undeclared_cell`: instantiated private access cell is undeclared
- `private_access_instance_out_of_bounds`: instantiated private access cell falls outside declared bounds

Evidence status: toy OpenScop symbolic-private-access witness; no current Pluto/OpenScop pass observed

### `layout_remap_padding`

Classification: same instances / injective physical address remap

Core files:
- source: `examples/standalone/layout_remap_padding.source.c`
- target: `examples/standalone/layout_remap_padding.target.c`

Example variants:
- padding scale: logical public A represented by different physical layout
  source: `A[i]`
  target: `A_pad[2*i]`
- transpose/permutation: same logical array through index permutation
  source: `A[i][j]`
  target: `A_t[j][i]`
- linearized affine layout: affine layout witness, not raw variable equality
  source: `A[i][j]`
  target: `A_lin[i*M + j]`

Required witness fields:
- logical public index
- physical layout map
- injectivity over live logical cells
- padding exclusion from public view

Rejected malformed witnesses:
- `aliased_layout_map`: layout map aliases logical cells
- `layout_bad_boundary_value`: layout boundary value mismatch
- `layout_incompatible_storage`: layout storage spec mismatch
- `layout_out_of_declared_bounds`: allocated layout cell falls outside declared array bounds
- `layout_bad_access_remap`: layout access remap changes affine index
- `layout_bad_permutation_access_remap`: target access does not use declared index permutation
- `layout_bad_affine_access_remap`: target access does not use declared affine layout

Evidence status: toy OpenScop access rewrite; no current Pluto/OpenScop layout pass observed

### `scratchpad_packing`

Classification: same instances / copy-mediated local storage

Core files:
- source: `examples/standalone/scratchpad_packing.source.c`
- target: `examples/standalone/scratchpad_packing.target.c`

Example variants:
- live-in cache: copy-in covers local reads; Bp is private
  source: `C[kk+k] = A[kk+k] + B[kk+k]`
  target: `Bp[k] = B[kk+k]; C[kk+k] = A[kk+k] + Bp[k]`
- partial tile guard: boundary tiles must be checked, not assumed
  source: `N may not be divisible by T`
  target: `copy/compute guarded by kk+k < N`

Required witness fields:
- tile footprint
- public-to-local copy map
- local buffer shape
- local read coverage

Rejected malformed witnesses:
- `missing_copy_in`: Bp[3] used before copy-in
- `scratchpad_bad_local_remap`: public cells mapped to local buffer are not injective
- `scratchpad_incompatible_local_storage`: scratchpad local storage spec mismatch
- `scratchpad_local_out_of_bounds`: scratchpad local cell falls outside declared bounds
- `scratchpad_public_undeclared`: copy mapping public cell is not declared
- `scratchpad_public_out_of_bounds`: scratchpad public cell falls outside declared bounds

Evidence status: toy OpenScop copy-in/local-buffer witness; no current Pluto/OpenScop scratchpad pass observed

### `scratchpad_copy_out`

Classification: same instances / copy-mediated local update plus commit

Core files:
- source: `examples/standalone/scratchpad_copy_out.source.c`
- target: `examples/standalone/scratchpad_copy_out.target.c`

Example variants:
- local update then commit: copy-out is the public commit
  source: `A[i] = A[i] + 1`
  target: `Al[k] = A[kk+k]; Al[k]++; A[kk+k] = Al[k]`
- duplicate commit rejected: commit uniqueness or deterministic resolution
  source: `one logical A[i] live-out`
  target: `two copy-out events write A[i]`

Required witness fields:
- updated local cells
- copy-out commit map
- public live-out set
- unique commit proof

Rejected malformed witnesses:
- `missing_copy_out`: copy-out does not commit every logical output
- `scratchpad_bad_copy_instance_role`: copy helper instance role does not match copy event

Evidence status: toy OpenScop copy-out witness; no current Pluto/OpenScop scratchpad copy-out pass observed

### `scalar_promotion`

Classification: same instances / array cell simulated by scalar

Core files:
- source: `examples/standalone/scalar_promotion.source.c`
- target: `examples/standalone/scalar_promotion.target.c`

Example variants:
- single-cell scalar cache: load/update/store-back protocol
  source: `A[i] = A[i] + 1`
  target: `s = A[i]; s = s + 1; A[i] = s`
- missing store-back rejected: private scalar cannot satisfy final public view
  source: `updated A[i] is public`
  target: `s is updated but A[i] is not stored`

Required witness fields:
- entry load event
- private scalar interval
- alias/clobber exclusion
- exit store-back event

Rejected malformed witnesses:
- `scalar_promotion_incompatible_storage`: promoted scalar storage spec mismatch

Supplemental protocol negative cases:
- missing load
- scalar read before load
- missing store-back
- intervening alias write clobbers promoted A[i]
- unknown call may clobber promoted A[i]
- public use reads stale A[i] instead of scalar
- store-back targets wrong public index
- two logical cells share one scalar over overlapping intervals
- promoted scalar escapes as public output

Evidence status: toy OpenScop scalar-promotion protocol witness; standalone negatives still thin

### `array_contraction`

Classification: same logical values / non-injective conflict-safe storage reuse

Core files:
- source: `examples/standalone/array_contraction.source.c`
- target: `examples/standalone/array_contraction.target.c`

Example variants:
- rolling time buffer: non-injective physical map with disjoint live intervals
  source: `A[t][i] = A[t-1][i] + 1`
  target: `A2[t mod 2][i] = A2[(t-1) mod 2][i] + 1`
- wrong modulo rejected: reuse-before-last-consumer is unsound
  source: `A[t] and A[t-1] simultaneously live`
  target: `one-slot A1[0][i] reuses too early`

Required witness fields:
- logical value ids
- physical reuse map
- valid intervals
- producer/consumer events
- kill or reuse events
- boundary projection

Rejected malformed witnesses:
- `missing_contraction_conflict_pair`: live-overlap conflict missing for (0, 0) and (1, 0)
- `mod_one_contraction_conflict`: conflicting values (0, 0) and (1, 0) share (0, 0)
- `contraction_missing_boundary_liveout`: reuse boundary mapping does not cover every source live-out
- `contraction_incompatible_storage`: reuse boundary storage spec mismatch
- `contraction_target_out_of_bounds`: reuse target physical cell falls outside declared bounds

Evidence status: toy OpenScop folded-storage witness; no current Pluto/OpenScop contraction pass observed

### `inter_array_reuse`

Classification: same instances / cross-array lifetime-based storage reuse

Core files:
- source: `examples/standalone/inter_array_reuse.source.c`
- target: `examples/standalone/inter_array_reuse.target.c`

Example variants:
- two temporaries share buffer: cross-array reuse under disjoint lifetimes
  source: `T1 produces C, then T2 produces D`
  target: `Buf represents T1 in phase 1 and T2 in phase 2`
- overlapping lifetimes rejected: valid intervals must not overlap
  source: `T1 is read after T2 is produced`
  target: `T2 overwrites Buf before T1's last read`

Required witness fields:
- logical arrays sharing one region
- disjoint lifetime intervals
- physical region compatibility
- copy-out before reuse

Rejected malformed witnesses:
- `inter_array_live_overlap`: T1 and T2 live ranges overlap
- `inter_array_same_buffer_live_overlap`: shared buffer cells have overlapping live ranges
- `inter_array_incompatible_storage`: T2 is not storage-compatible with Buf
- `inter_array_shared_buffer_out_of_bounds`: shared buffer cell falls outside declared bounds

Evidence status: toy OpenScop shared-buffer witness; no current Pluto/OpenScop inter-array reuse pass observed

### `array_expansion_versioning`

Classification: same instances / more physical versions plus copy-out

Core files:
- source: `examples/standalone/array_expansion_versioning.source.c`
- target: `examples/standalone/array_expansion_versioning.target.c`

Example variants:
- per-time version array: reads select produced versions and final selector commits
  source: `X overwritten each t; Y[t][i] reads current X[i]`
  target: `X_exp[t][i] stores each version; final X copied from X_exp[T-1]`
- old version selected rejected: final public output needs source-final version
  source: `final X is last write`
  target: `copy-out selects X_exp[T-2]`

Required witness fields:
- definition-to-version map
- read version selectors
- produced-version proof
- final version selector

Rejected malformed witnesses:
- `missing_expansion_copy_out`: final X differs without copy-out: {0: 0, 1: 0} != {0: 2, 1: 3}
- `duplicate_selected_version`: selected target versions are not unique
- `expansion_incompatible_version_storage`: selected version storage spec mismatch
- `expansion_version_out_of_bounds`: selected target version falls outside declared bounds
- `expansion_read_selects_unproduced_version`: read-selected version was not produced by the expected write
- `expansion_read_version_out_of_bounds`: read-selected produced version falls outside declared bounds

Evidence status: toy OpenScop version-selection witness; no current Pluto/OpenScop versioning pass observed

### `overlapped_tiling`

Classification: instance-count-changing / private recomputation plus unique commit

Core files:
- source: `examples/standalone/overlapped_tiling.source.c`
- target: `examples/standalone/overlapped_tiling.target.c`

Example variants:
- halo recomputation: extra computations hidden; commit set exact cover
  source: `B[i] depends on neighbors`
  target: `each tile recomputes halo privately and commits owned interior`
- duplicate public commit rejected: halo duplicates must not escape
  source: `one public B[i] output`
  target: `two overlapped tiles commit B[i]`

Required witness fields:
- source-to-target duplicate projection
- halo closure
- commit set
- exact cover of public live-outs

Rejected malformed witnesses:
- `duplicate_overlap_commit`: more than one tile commits a source output
- `overlap_missing_halo_closure`: tile does not locally close B dependences
- `overlap_bad_producer_order`: tile producer does not precede consumer
- `overlap_internal_write_public_cell`: overlap write role does not match private/commit storage
- `overlap_duplicate_commit_write_cell`: overlap commit write cells are not unique
- `overlap_private_write_out_of_bounds`: overlap private write cell falls outside declared bounds
- `overlap_commit_write_out_of_bounds`: overlap commit write cell falls outside declared bounds

Evidence status: toy OpenScop duplicate/commit witness; related to overlapped/diamond tiling but not Pluto-backed here

### `reduction_privatization`

Classification: parallel/storage privatization plus merge

Core files:
- source: `examples/standalone/reduction_privatization.source.c`
- target: `examples/standalone/reduction_privatization.target.c`

Example variants:
- chunked sum: private accumulators plus algebraic merge
  source: `sum += A[i]`
  target: `priv[c] reduces chunk c; sum = merge(priv)`
- non-associative operator rejected: operator laws are required evidence
  source: `left-fold subtraction`
  target: `chunked/reordered merge`

Required witness fields:
- chunk partition
- private accumulator initialization
- contribution coverage
- merge tree
- operator laws

Rejected malformed witnesses:
- `overlapping_reduction_chunks`: reduction chunks overlap
- `reduction_missing_merge_accumulator`: reduction merge order does not cover private accumulators exactly
- `reduction_incompatible_accumulator_storage`: reduction accumulator storage spec mismatch
- `reduction_accumulator_out_of_bounds`: reduction accumulator falls outside declared bounds
- `reduction_accumulator_escape`: reduction private accumulator escapes fragment
- `reduction_non_associative_law`: reduction merge operator is not associative on carrier
- `reduction_wrong_final_value`: reduction merge gives different result

Evidence status: toy OpenScop reduction-merge witness; no current Pluto/OpenScop reduction privatization pass observed

### `double_buffering`

Classification: same logical values / phase-separated ping-pong storage

Core files:
- source: `examples/standalone/double_buffering.source.c`
- target: `examples/standalone/double_buffering.target.c`

Example variants:
- cur/next ping-pong: phase projection and final selector
  source: `A[t][i] = step(A[t-1][i])`
  target: `next[i] = step(cur[i]); swap(cur,next)`
- read/write role swapped rejected: phase role obligations cannot be inferred from final equality
  source: `read old state, write new state`
  target: `reads next or writes cur in the same phase`

Required witness fields:
- phase projection
- current/next buffer map
- swap transition proof
- final boundary projection

Rejected malformed witnesses:
- `double_buffer_without_swap`: swap does not expose the current time row
- `double_buffer_bad_next_value`: next-live value 0 does not come from phase write or entry-live value
- `double_buffer_bad_projection`: phase projection does not cover logical live-outs
- `double_buffer_bad_final_snapshot`: final phase snapshot does not match final-live cells
- `double_buffer_bad_projection_value`: phase projection value mismatch
- `double_buffer_incompatible_projection_storage`: phase projection storage spec mismatch
- `double_buffer_projection_out_of_bounds`: phase projection target falls outside declared bounds
- `double_buffer_phase_write_out_of_bounds`: phase protocol cell falls outside declared bounds

Evidence status: toy OpenScop phase-projection witness; no current Pluto/OpenScop double-buffering pass observed

### `storage_view_composition`

Classification: composition / layout projection followed by private erasure

Core files:
- source: `examples/standalone/storage_view_composition.source.c`
- target: `examples/standalone/storage_view_composition.target.c`

Example variants:
- layout then private erasure: compose layout projection with private-storage erasure
  source: `logical A`
  target: `padded physical A_pad plus private temps`
- bad intermediate rejected: view composition needs compatible intermediate observables
  source: `logical A contents`
  target: `target and mid disagree on observable cells`

Required witness fields:
- source-to-mid public view
- mid-to-target public view
- compatible intermediate interface
- composed output view equality

Rejected malformed witnesses:
- `composition_bad_intermediate_public`: private-erasure view cannot relate target to intermediate state
- `composition_bad_access_midpoint`: composed access remap is invalid
- `composition_bad_mid_observables`: cell-view composition should reject incompatible intermediate observables

Evidence status: toy OpenScop view-composition witness

