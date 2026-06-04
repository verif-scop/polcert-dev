# Storage Transformation Manifest

| Case | Group | Tool-backed | Examples | Obligations | Negatives | Evidence status |
|---|---|---|---|---:|---:|---|
| `source_no_alias_abstraction` | precondition | yes | yes | 4 | 3 | toy OpenScop source-footprint/no-alias witness; precondition rather than storage rewrite |
| `contextual_frame_preservation` | context | yes | yes | 5 | 3 | toy OpenScop contextual-frame witness; boundary condition rather than storage rewrite |
| `affine_interchange` | schedule_only | yes | yes | 3 | 0 | real schedule tooling; storage-preserving rather than storage rewrite |
| `index_set_splitting` | schedule_domain | yes | yes | 3 | 0 | toy OpenScop domain-partition witness; storage-preserving |
| `ordinary_tiling` | schedule_domain | yes | yes | 3 | 0 | real schedule/tiling tooling; storage-preserving |
| `scalar_privatization_expansion` | storage_expansion | yes | yes | 5 | 4 | real Candl OpenScop storage access rewrite |
| `private_copy_boundary` | private_boundary | yes | yes | 8 | 7 | toy OpenScop copy-boundary witness; no current Pluto/OpenScop pass observed |
| `private_access_local_instantiation` | private_access | yes | yes | 4 | 3 | toy OpenScop symbolic-private-access witness; no current Pluto/OpenScop pass observed |
| `layout_remap_padding` | layout | yes | yes | 10 | 7 | toy OpenScop access rewrite; no current Pluto/OpenScop layout pass observed |
| `scratchpad_packing` | scratchpad | yes | yes | 9 | 6 | toy OpenScop copy-in/local-buffer witness; no current Pluto/OpenScop scratchpad pass observed |
| `scratchpad_copy_out` | scratchpad | yes | yes | 4 | 2 | toy OpenScop copy-out witness; no current Pluto/OpenScop scratchpad copy-out pass observed |
| `scalar_promotion` | promotion | yes | yes | 4 | 1 | toy OpenScop scalar-promotion protocol witness; standalone negatives still thin |
| `array_contraction` | reuse_folding | yes | yes | 7 | 5 | toy OpenScop folded-storage witness; no current Pluto/OpenScop contraction pass observed |
| `inter_array_reuse` | reuse_folding | yes | yes | 5 | 4 | toy OpenScop shared-buffer witness; no current Pluto/OpenScop inter-array reuse pass observed |
| `array_expansion_versioning` | versioning | yes | yes | 9 | 6 | toy OpenScop version-selection witness; no current Pluto/OpenScop versioning pass observed |
| `overlapped_tiling` | overlap_halo | yes | yes | 9 | 7 | toy OpenScop duplicate/commit witness; related to overlapped/diamond tiling but not Pluto-backed here |
| `reduction_privatization` | reduction | yes | yes | 8 | 7 | toy OpenScop reduction-merge witness; no current Pluto/OpenScop reduction privatization pass observed |
| `double_buffering` | versioning | yes | yes | 10 | 8 | toy OpenScop phase-projection witness; no current Pluto/OpenScop double-buffering pass observed |
| `storage_view_composition` | composition | yes | yes | 7 | 3 | toy OpenScop view-composition witness |

## Acceptance Reasons

### `source_no_alias_abstraction`

logical source variables have distinct footprints, so storage reasoning over variables is sound

### `contextual_frame_preservation`

writes stay inside the allowed fragment footprint and protected frame variables keep their values

### `affine_interchange`

instances and storage accesses are unchanged; only legal schedule order changes

### `index_set_splitting`

target subdomains disjointly and exactly cover the source domain

### `ordinary_tiling`

tile projection covers source instances and storage accesses are unchanged

### `scalar_privatization_expansion`

each source temporary live range is represented by a fresh per-instance private cell before public use

### `private_copy_boundary`

copy-in initializes private live-ins and unique copy-out commits private live-outs to public variables

### `private_access_local_instantiation`

symbolic private accesses instantiate to declared, in-bounds, hidden private cells

### `layout_remap_padding`

logical public cells are represented by an injective in-bounds physical layout map

### `scratchpad_packing`

copy-in covers local reads and local buffer cells consistently represent a public tile

### `scratchpad_copy_out`

local updates are private until every updated public cell is committed exactly once

### `scalar_promotion`

entry load, scalar updates, and exit store implement the same public cell value

### `array_contraction`

non-injective physical reuse is allowed only for non-overlapping logical lifetimes

### `inter_array_reuse`

arrays share a buffer only across disjoint lifetime intervals with compatible storage

### `array_expansion_versioning`

reads select produced versions and final copy-out selects the source-final version

### `overlapped_tiling`

extra computations are private; commit instances exactly cover public live-outs

### `reduction_privatization`

private accumulators cover source contributions and merge under checked algebraic laws

### `double_buffering`

phase projection identifies the current physical buffer and final projection covers public live-outs

### `storage_view_composition`

target-mid and mid-source public views agree on intermediate observables and compose

## Required Witness Fields

### `source_no_alias_abstraction`

- source variable footprints
- non-overlap proof for distinct variables
- in-bounds source accesses

### `contextual_frame_preservation`

- allowed write set
- protected frame variables
- pre/post frame snapshots

### `affine_interchange`

- instance bijection
- legal schedule order
- unchanged storage accesses

### `index_set_splitting`

- source domain
- target subdomains
- disjoint exact-cover proof

### `ordinary_tiling`

- tile projection
- exact domain cover
- unchanged storage accesses

### `scalar_privatization_expansion`

- logical temporary live range
- fresh private cell per instance
- write-before-read evidence
- optional live-out copy

### `private_copy_boundary`

- copy-in map
- copy-out map
- private live-in/live-out sets
- unique public commits

### `private_access_local_instantiation`

- symbolic private access
- instantiated target private cell
- hidden/private declaration
- in-bounds proof

### `layout_remap_padding`

- logical public index
- physical layout map
- injectivity over live logical cells
- padding exclusion from public view

### `scratchpad_packing`

- tile footprint
- public-to-local copy map
- local buffer shape
- local read coverage

### `scratchpad_copy_out`

- updated local cells
- copy-out commit map
- public live-out set
- unique commit proof

### `scalar_promotion`

- entry load event
- private scalar interval
- alias/clobber exclusion
- exit store-back event

### `array_contraction`

- logical value ids
- physical reuse map
- valid intervals
- producer/consumer events
- kill or reuse events
- boundary projection

### `inter_array_reuse`

- logical arrays sharing one region
- disjoint lifetime intervals
- physical region compatibility
- copy-out before reuse

### `array_expansion_versioning`

- definition-to-version map
- read version selectors
- produced-version proof
- final version selector

### `overlapped_tiling`

- source-to-target duplicate projection
- halo closure
- commit set
- exact cover of public live-outs

### `reduction_privatization`

- chunk partition
- private accumulator initialization
- contribution coverage
- merge tree
- operator laws

### `double_buffering`

- phase projection
- current/next buffer map
- swap transition proof
- final boundary projection

### `storage_view_composition`

- source-to-mid public view
- mid-to-target public view
- compatible intermediate interface
- composed output view equality

