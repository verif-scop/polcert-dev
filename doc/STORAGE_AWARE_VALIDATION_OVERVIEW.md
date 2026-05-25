# Storage-Aware Validation Overview

This is the entry point for the storage-generalization notes.  The goal is to
state the problem cleanly before choosing a mechanization strategy.  The current
verified PolOpt pipeline remains the identity storage case:

```text
same logical statement instances
same logical storage accesses
different schedule, grouping, order, or loop annotation
final relation: State.eq
```

The transformations studied here go beyond that case.  They may add dynamic
instances, duplicate work, introduce helper copies, allocate private storage,
remap layout, reuse physical cells, or commit only selected target writes.  The
correctness statement must therefore say what the target execution represents
and what the surrounding context can observe.

## Document Map

- `POLYHEDRAL_TRANSFORMATION_TAXONOMY.md` classifies transformation families by
  instance relation, storage relation, and final observation.
- `STATE_VIEW_RELATION_DESIGN.md` defines the intended role of `State.eq` as
  the identity state view and sketches view constructors for storage-aware
  relations.
- `STORAGE_GENERALIZATION_PLAN.md` records a possible proof-engineering route
  for extending PolCert without weakening the current `State.eq` route.
- `FRAGMENT_TO_CONTEXT_CORRECTNESS_GAPS.md` separates PolIR fragment theorems
  from future C/CompCert contextual correctness obligations.
- `experiments/storage-validation-standalone/` contains finite executable
  models of candidate witnesses.  They are sanity checks for obligation shapes,
  not verified validators.

## Current Status

In this host worktree, the storage-generalization material is documentation,
the standalone executable experiment package, and uncommitted Coq skeletons.
The first implementation step is `StateView.v`, which packages endpoint
relations as views and wraps the existing affine/general validators as
`same_state_view -> identity_view` refinements.  It also exposes a small
relation-inclusion algebra (`view_included_refl`, `view_included_trans`, and
`compose_view_monotone`) so storage validators can compose endpoint views
without unfolding the underlying state relations.  The current layout skeleton
also exposes `related_cells_view` and a `layout_view`-level theorem, so the
layout prototype no longer bypasses the view endpoint.  `StateObservation.v`
now proves that observer-backed cell views compose through
`compose_cell_relation`, and its `compose_cell_view` constructor makes public
footprint composition explicit through a shared-intermediate-observable
compatibility condition.  `cell_view_transform_contract_compose` then bundles
this with same-instance access-remap composition and semantic
`view_refinement` composition, giving a first end-to-end theorem shape for
composing storage-aware passes.  It also defines `cell_view`, which records the public
source/target cells represented by a cell relation; `PrivateStorageValidator.v`
uses this to state the first private-erasure theorem shape.
`PrivateStorageWitness.v` adds the
first checkable private-erasure witness: finite target-private cells must be
included in a finite hidden-cell set, which proves they are outside the public
cell relation.  It also contains small proved checkers for duplicate-free
private-cell lists, concrete private read-after-write traces, and
access-function read-after-write traces that instantiate to concrete
`MemCell` traces for every dynamic point.  It also factors out reusable finite
cell-set obligations such as private/public and private/frame disjointness.
`PrivateBoundaryWitness.v` adds the first boundary-copy layer for private
storage: required public live-ins must have copy-in pairs, required public
live-outs must have copy-out pairs, those pairs must use declared private cells,
public copy-out destinations must be unique, and an optional private-side
uniqueness checker prevents multiple boundary pairs from sharing the same
private cell.  It also adds a value-entry checker showing that copy-in/copy-out
public and private boundary values match for each aligned boundary pair.
Related skeletons include
`TransformContract.v`, `StateView.v`, `ViewPipeline.v`,
`StorageWitness.v`, `SourceNoAliasWitness.v`,
`FramePreservationWitness.v`, `FramePreservationValidator.v`,
`StateObservation.v`,
`LayoutWitness.v`, `LayoutRemapValidator.v`, `PaddingLayoutWitness.v`,
`PaddingLayoutValidator.v`, `PrivateStorageWitness.v`,
`PrivateBoundaryWitness.v`,
`PrivateStorageValidator.v`, `ScalarPromotionWitness.v`,
`ScalarPromotionValueWitness.v`, `ScalarPromotionValidator.v`,
`CopyProtocolWitness.v`, `CopyCommitWitness.v`,
`CopyInstanceWitness.v`,
`CopyProtocolValueWitness.v`,
`CopyProtocolValidator.v`, `ScratchpadCopyValidator.v`,
`ReuseConflictWitness.v`, `LifetimeConflictWitness.v`,
`ReuseValueWitness.v`, `StorageCompatibilityWitness.v`,
`InterArrayReuseWitness.v`, `InterArrayReuseValidator.v`,
`ReuseStateView.v`, `StorageBoundaryView.v`, `ReuseConflictValidator.v`,
`InstanceProjectionWitness.v`,
`InstanceProjectionValidator.v`, `OverlapClosureWitness.v`,
`OverlapTilingValidator.v`,
`VersionCommitWitness.v`, `VersionCommitValueWitness.v`,
`VersionCommitValidator.v`, `ReductionMergeWitness.v`,
`ReductionMergeValueWitness.v`, `ReductionMergeValidator.v`,
`PhaseSeparationWitness.v`, `PhaseValueWitness.v`,
`PhaseProjectionWitness.v`,
`PhaseSeparationValidator.v`, and
`CStateObservation.v`.
`StateView.v` now uses a top-level `generic_state_view` carrier so independently
instantiated validators can share one facade-level view type instead of
exporting incompatible functor-local records.  `ViewPipeline.v` factors out the
repeated composition pattern shared by most storage validators: the existing
general validator proves `before -> source_view`, while the feature-specific
pass supplies finite witness obligations plus an explicit semantic
`view_refinement` from `source_view` to the storage-changing target.
`TransformContract.checked_relational_transform_family_pair_compose` and
`StateView.checked_view_transform_family_pair_compose` are the current generic
two-pass composition hooks: two checked passes compose by composing their input
and output relations/views, so feature checkers do not need bespoke end-to-end
theorems for every pass ordering.
`StorageWitness.v` now has the analogous access-level composition hook:
`pprog_same_instance_access_remap_compose` composes two target-to-source
cell-relation remaps through the same intermediate access cells.  This keeps
the instruction/access witness layer aligned with the state-view composition
layer instead of forcing every storage pass sequence to define a fresh combined
access relation.
`PaddingLayoutValidator.v`, `ScalarPromotionValidator.v`,
`CopyProtocolValidator.v`, `ScratchpadCopyValidator.v`,
`InstanceProjectionValidator.v`, `OverlapTilingValidator.v`,
`VersionCommitValidator.v`, `ReuseConflictValidator.v`,
`ReductionMergeValidator.v`, `PhaseSeparationValidator.v`, and the
observer-backed layout/private validators now consume this shared spine.
The most concrete private route at this point is
`checked_access_local_private_expansion_view_correct`: it packages local
private obligations over access functions and composes them with the
still-explicit semantic refinement.  The most complete boundary route is
`checked_boundary_private_unique_value_expansion_view_correct`, which combines
live-in/live-out boundary copies, private-side boundary uniqueness, and aligned
boundary value evidence under the observer-backed private-erasure theorem.
`SourceNoAliasWitness.v` makes the front-end memory abstraction explicit: each
logical source object has a duplicate-free finite footprint, object ids are
duplicate-free, and different footprints are pairwise disjoint.  This remains a
precondition witness rather than a transformation theorem.
`FramePreservationWitness.v` adds the generic contextual boundary condition:
fragment writes must be contained in an allowed-write set, and that allowed set
must be disjoint from frame cells owned by the surrounding context.
`FramePreservationValidator.v` packages that side condition with the common
source-view theorem shape, so feature-specific storage views can carry a frame
contract without changing their final-state relation.
`PaddingLayoutWitness.v` adds the finite allocation side of layout/padding:
source cells map functionally to target cells, target cells are injective and
allocated, and padding cells are duplicate-free, allocated, and outside the
represented target image.  `LayoutValueWitness.v` adds the boundary value side:
each source-to-target layout map entry can be paired with evidence that the
source logical value equals the represented target physical value.
`PaddingLayoutValidator.v` composes the structural, optional access-remap, and
optional value witnesses with the same view-refinement endpoint.  The access
variants reuse `LayoutWitness.check_pprog_array_rename_access_remapb_sound` to
check that target PolIR accesses use the declared array rename relation.
`ScalarPromotionWitness.v` starts the scalar-promotion route by checking the
local load/use/store protocol for a promoted source cell: scalar reads and
writes require a prior load, ordinary writes to the promoted source cell are
rejected as interference, and live-out promoted cells require a final store.
`ScalarPromotionValueWitness.v` adds the first value-flow layer over that
protocol: a load initializes the scalar to the source value, scalar reads see
the current scalar, scalar writes update it, and store-back commits the current
scalar value.  `ScalarPromotionValidator.v` composes the storage protocol, the
optional value-flow witness, scalar-private separation, and the remaining
instruction-level semantic refinement.
`CopyProtocolWitness.v` starts the P4 route by checking finite copy-in,
local-read/local-write, and copy-out traces: local reads require earlier local
definitions, and copy-out destinations are committed at most once.
`CopyCommitWitness.v` adds exact copy-out boundary coverage for update-style
scratchpad transformations: the committed target cells must exactly cover the
expected observable target set.
`CopyInstanceWitness.v` aligns copy protocol events with projected helper
instances: copy-in/local events must be internal target instances, while
copy-out events must be commit-role target instances.
`CopyMappingWitness.v` adds the remapping-consistency layer for copy-mediated
local storage: the declared public-to-local map is injective on both sides, and
copy-in, local read/write, and copy-out events use that declared map.
`CopyProtocolValueWitness.v` adds the value-flow layer for the same protocol:
copy-in transfers source value to local value, local reads observe the current
local value, local writes update it, and copy-out commits the current local
value.  `CopyProtocolValidator.v` packages both the bookkeeping-only and
value-flow variants into composable `view_refinement` theorems under an
explicit instruction-level semantic refinement.
`ScratchpadCopyValidator.checked_scratchpad_copy_full_view_correct` lifts the
copy remapping and value-flow witnesses to the scratchpad/packing composition
layer together with instance projection, copy-out exact cover, helper-instance
roles, and local-buffer separation.
`ScratchpadCopyValidator.v` combines instance projection, copy protocol, and
local-buffer separation into one wrapper for scratchpad/packing-style
transformations.
`ReuseConflictWitness.v` starts the contraction/reuse route by checking finite
logical-to-physical reuse maps against conflict pairs: conflicting logical
values must not map to the same physical cell.  `LifetimeConflictWitness.v`
checks the preceding finite live-range obligation: every pair of overlapping
live intervals must be listed as a conflict, and conflict-safe reuse then
implies physical separation for all live overlaps.  `ReuseValueWitness.v` adds
a boundary value witness aligned with the logical-to-physical map: each
physical boundary value must equal the logical value it represents.
`ReuseConflictWitness.v` also checks boundary coverage: every source-observable
live-out selected for final projection must be present in the reuse map.
`StorageCompatibilityWitness.v` adds a finite size/alignment compatibility
checker for logical-to-physical storage maps.  This captures the explicit
storage-class side condition needed by contraction, inter-array reuse, packing,
and scratch/local-buffer reuse without pretending that the specs have already
been derived from C types.
`InterArrayReuseWitness.v` packages the inter-array reuse case without adding
a new primitive: it combines live-interval conflict cover, conflict-safe reuse,
and storage compatibility.  Its derived facts say that mapped live-overlapping
logical cells have distinct physical cells, and therefore two distinct logical
cells that share one physical cell cannot overlap in their live intervals.
`InterArrayReuseValidator.v` gives that composed finite witness the same
`view_refinement` endpoint theorem shape as the other storage features, while
leaving the concrete boundary projection as the supplied output view.
`ReuseStateView.v` turns a boundary reuse map into an observer-backed reuse
projection view, and now also exposes a `cell_view` for a declared live-out
boundary whose target-public cells are exactly the mapped image.
`StorageBoundaryView.v` is the first shared endpoint wrapper for storage-backed
boundary maps: it combines `check_reuse_boundaryb_sound`,
`check_storage_compatibilityb_sound`, and the observer-backed boundary view into
one theorem, so layout, phase projection, reuse/contraction, and copy-out style
passes can share the same final-observation discipline when their live-outs are
represented by a finite logical-to-physical map.
`ReuseConflictValidator.v` composes the finite conflict
checker, the optional live-range cover checker, the optional storage
compatibility checker, and the value witness under the remaining semantic
refinement shape.
`InstanceProjectionWitness.v` starts the overlap/helper-instance route by
checking target-to-source projection and exact live-out commit cover.  It now
also names the exact-cover consequences that later overlap proofs need:
duplicate-free commits, liveout-to-commit and commit-to-liveout directions,
and liveout-in-domain.
`InstanceProjectionValidator.v` packages that witness into the same
`view_refinement` composition pattern.
`OverlapTilingValidator.v` specializes that route for overlapped tiling: one
theorem covers duplication with no materialized private storage, and one theorem
adds tile-private separation when halo/local buffers are represented in the
target state.  `OverlapClosureWitness.v` adds the finite local-dependence
closure and ordering side conditions: each tile dependency must be supplied
either by a tile live-in or by a computation projected inside the same tile, and
tile-produced values must appear before their consumers in the tile target
trace.  Recomputed-value equivalence remains an explicit semantic obligation.
`VersionCommitWitness.v` starts the array-expansion/versioning route by
checking that each source live-out selects exactly one target version and that
selected versions are duplicate-free.  It also exposes the exact-cover
consequences as named lemmas: live-outs have selected versions, selected
sources are live-outs, selected versions belong to the version image, and both
finite images are duplicate-free.  `VersionCommitValueWitness.v` checks that
value evidence is aligned with the selected source/version cell pairs and that
every selected version value equals the represented source value;
`VersionCommitValidator.v` gives both variants the same compositional theorem
shape.
`ReductionMergeWitness.v` starts the reduction-privatization route by checking
chunk exact cover, private accumulator uniqueness, and merge-order cover;
it also exposes the exact-cover consequences as named lemmas for later
semantic proofs.
`ReductionMergeValueWitness.v` checks the narrower value-flow side: merge-order
cells are looked up in supplied accumulator values and folded with a supplied
merge operator to the claimed final value.  `ReductionMergeValidator.v`
composes both variants while keeping the reduction algebra law explicit.
`PhaseSeparationWitness.v` starts the double-buffering route by checking phase
read visibility, write/live disjointness, and next-live coverage;
`PhaseValueWitness.v` adds phase snapshot value flow: reads have entry values,
and every next-live value is either written in the phase or inherited from the
entry snapshot.  `PhaseProjectionWitness.v` checks the final-boundary projection
from source logical live-outs to the final phase-live physical cells, with an
optional value-equality layer for those projected cells.  It also exposes the
projection map as a target-to-source `cell_relation` and names the exact-cover
consequences used by later view proofs.
`PhaseSeparationValidator.v` composes these variants while keeping the
phase/swap semantic meaning explicit.
`Validator.v` re-exports the observer-independent source no-alias, frame
preservation, padding layout, scalar promotion, copy, reuse, projection,
overlap, version commit, reduction merge, and phase separation/projection
checker/theorem
interfaces;
`CStateObservation.v`
exposes the C-like observer instances for layout, private storage, and reuse
views.
Treat these files as exploration until they are committed, reviewed, and
integrated through the normal proof build.

The current committed, stage-complete result remains the state-preserving
polyhedral pipeline on `end-to-end`.  The notes in this directory describe the
next family of correctness problems; they do not claim that storage-changing
optimizations are already covered by the existing theorem.

## Canonical Axes

Use these three axes when describing any new optimization.

| Axis | Questions |
| --- | --- |
| Instance relation | Does each target dynamic instance correspond to exactly one source instance, or are there partitions, duplicated halo instances, helper copy instances, or merged reduction instances? |
| Storage relation | Does the target use the same logical cells, an injective physical layout, fresh private storage, copy-mediated local buffers, non-injective reuse, or versioned cells? |
| Final observation | Does the final target state equal the source state, project through a layout map, erase private cells, expose committed writes, or merge private partial values? |

Do not choose a theorem shape from the optimization name alone.  For example,
overlapped tiling primarily changes the instance relation, while contraction
primarily changes the storage relation.  Scratchpad tiling changes both.

## Canonical Primitive Names

The standalone experiments use the following names as a vocabulary for proof
obligations.  The numbering is only for discussion; it should not become a Coq
API.

| Primitive | Obligation |
| --- | --- |
| P-1 no-alias memory abstraction | Logical source names used by the polyhedral model denote disjoint memory footprints, or aliasing is represented explicitly. |
| P0 instance bijection / exact cover | Target instances project to valid source instances and cover the source domain with the required uniqueness condition. |
| P1 role-based projection | Duplicated or helper target instances are classified, usually as internal, commit, copy, or merge roles. |
| P2 access-map refinement | Rewritten target accesses denote the intended source logical cells or values. |
| P3 fresh private storage | Target-private cells are fresh for their live ranges and every private read has an appropriate reaching definition. |
| P4 copy protocol | Copy-in/copy-out events are ordered correctly, local reads are covered, local accesses use the same remap, and local storage is fresh for its lifetime. |
| P5 scalar simulation | A scalar temporary simulates a promoted memory cell between entry load and exit store, with no interfering writes. |
| P6 conflict-safe non-injective reuse | Logical values that are live together cannot share the same physical cell. |
| P7 version selection and commit | The target write or version that becomes source-observable is selected correctly and committed exactly once. |
| P8 reduction merge | Private partial results are merged under the algebraic assumptions claimed by the semantics. |
| P9 phase separation | Phase, swap, or visibility witnesses prevent overwriting live data and explain which physical cells represent each logical phase. |
| P10 frame preservation | Fragment writes stay inside an allowed-write set that is disjoint from surrounding-context frame cells. |

This list intentionally folds commit exactness into P7.  Earlier notes used a
separate P8 for commit exactness and shifted reduction/phase numbering; those
older numbers should not be used going forward.

## Mechanized Coverage Matrix

The current exploration branch has checkable witnesses for the following
primitive slices.  The rightmost column is the deliberately explicit semantic
gap; these are the obligations that should later be discharged by
feature-specific instruction or trace simulation proofs.

| Primitive | Current Coq hook | Checked now | Still explicit |
| --- | --- | --- | --- |
| P-1 no-alias memory abstraction | `SourceNoAliasWitness.check_source_no_aliasb_sound` | object ids and finite footprints are duplicate-free; footprints are pairwise disjoint | front-end proof that footprints over-approximate real C accesses |
| P0/P1 projection and roles | `InstanceProjectionWitness.check_instance_projectionb_sound` | projected target instances are in the source domain; commit-role instances exactly cover live-outs | deriving projected target sets from concrete codegen |
| P1 local dependence closure | `OverlapClosureWitness.check_overlap_closureb_sound`; `OverlapClosureWitness.check_overlap_ordered_closureb_sound` | every finite tile dependency is supplied by a tile live-in or a projected computation in the same tile; tile-produced dependencies precede their consumers | deriving dependencies and trace order from concrete schedule/access semantics |
| P2 access-map refinement | `LayoutWitness` and `LayoutRemapValidator` | same-instance access-list remap through a single declared-layout interface covering same-index array rename, index permutation such as transpose, and affine-composed index rewrites such as linearization | instruction-level value simulation for rewritten accesses; deriving layout declarations from generated code |
| P2 plus padding | `PaddingLayoutWitness.check_padding_layoutb_sound`; `LayoutWitness.check_pprog_declared_layout_access_remapb_sound`; compatibility hooks for the older rename/permutation/affine checkers; `LayoutValueWitness.check_layout_valueb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `PaddingLayoutValidator.checked_padding_layout_declared_access_compatible_value_view_correct` | target image is injective and allocated; padding is duplicate-free, allocated, and outside the image; target/source access functions can be checked under one declared-layout witness; mapped source/target boundary values match; mapped physical layout cells can be required size/alignment-compatible with represented logical cells | deriving value entries and storage specs from concrete semantics and deriving layout declarations from generated code |
| P3 fresh private storage | `PrivateStorageWitness.check_private_separationb_sound`; private use-def checkers; `PrivateBoundaryWitness.check_private_boundaryb_sound`; `PrivateBoundaryWitness.check_private_boundary_private_uniqueb_sound`; `PrivateBoundaryWitness.check_private_boundary_valueb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `PrivateStorageValidator.checked_boundary_private_unique_compatible_value_expansion_view_correct` | private cells are duplicate-free and disjoint from public/frame cells; private reads have prior writes; required live-ins/live-outs have boundary pairs; live-out public commits are unique; boundary private cells can be required unique; boundary public/private values match; boundary public/private cells can be required size/alignment-compatible; uniqueness, value evidence, and compatibility can be composed in one private-erasure theorem | non-escape and deriving boundary value entries/storage specs from concrete expression and type semantics |
| P4 copy protocol | `CopyProtocolWitness.check_copy_protocol_wfb_sound`; `CopyCommitWitness.check_copy_commit_coverb_sound`; `CopyInstanceWitness.check_copy_instance_traceb_sound`; `CopyMappingWitness.check_copy_mappingb_sound`; `CopyProtocolValueWitness.check_copy_value_traceb_sound`; `CopyProtocolValidator.checked_copy_protocol_commit_mapping_value_view_correct` | local reads are covered by prior local definitions; copy-out targets are duplicate-free and can exact-cover expected observable targets; copy protocol events align with internal/commit projected helper instances; public-to-local remap is injective and used consistently by copy/local events; copy/local/commit value flow is consistent; generic copy protocol can package commit exact cover, remapping, and value flow in one view theorem | deriving the trace, value trace, and helper-instance list from concrete instruction semantics |
| P4 scratchpad/packing composition | `ScratchpadCopyValidator.checked_scratchpad_copy_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_instance_commit_view_correct`; `ScratchpadCopyValidator.checked_scratchpad_copy_compatible_full_view_correct` | projection, copy protocol, optional copy-out exact cover, optional copy-instance role alignment, public-to-local remapping, copy value flow, local-buffer separation, and public/local storage compatibility compose into `view_refinement` | deriving the trace, value trace, helper-instance list, storage specs, and full copy-mediated semantic simulation |
| P5 scalar simulation | `ScalarPromotionWitness.check_scalar_promotionb_sound`; `ScalarPromotionValueWitness.check_scalar_value_traceb_sound`; `ScalarPromotionValidator.checked_scalar_promotion_compatible_value_view_correct` | load-before-use, no bypassing source write, live-out store-back; scalar value-flow consistency; promoted scalar/register storage can be required compatible with the source cell | deriving the value trace and storage specs from concrete expression/type semantics |
| P6 conflict-safe reuse | `LifetimeConflictWitness.check_live_conflictb_sound`; `ReuseConflictWitness.check_conflict_safe_reuseb_sound`; `ReuseValueWitness.check_reuse_valueb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundaryView.checked_storage_boundary_refinement_correct`; `ReuseConflictValidator.checked_compatible_live_conflict_reuse_value_view_correct`; `InterArrayReuseWitness.check_inter_array_reuseb_sound`; `InterArrayReuseValidator.checked_inter_array_reuse_view_correct` | explicit live intervals cover all overlap conflicts; conflicting logical values do not map to the same physical cell; boundary physical values equal represented logical values; mapped logical/physical cells have compatible size/alignment specs; a finite boundary map can be turned into a shared observer-backed endpoint view; live conflicts, reuse, compatibility, and boundary values can be packaged in one contraction-facing view theorem; inter-array sharing is the composed case where one physical cell cannot represent two simultaneously live logical cells | deriving live intervals, storage specs, and boundary values from schedule/access/type semantics |
| P7 version selection and commit | `VersionCommitWitness.check_version_commitb_sound`; derived facts such as `VersionCommitWitness.version_commit_liveout_selected` and `VersionCommitWitness.version_commit_selected_source_liveout`; `VersionCommitValueWitness.check_version_valueb_sound`; `VersionCommitValidator.checked_version_commit_compatible_value_view_correct` | selected source live-outs and selected target versions are duplicate-free and exactly covered; every live-out has a selected version; selected relation edges point back to live-outs; selected-version value evidence matches the mapping; selected physical versions can be required storage-compatible with represented source live-outs | deriving selected-version values and storage specs from concrete writes/types |
| P8 reduction merge | `ReductionMergeWitness.check_reduction_mergeb_sound`; `ReductionMergeValueWitness.check_reduction_value_mergeb_sound`; `ReductionAlgebraWitness.check_reduction_*_lawb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `ReductionMergeValidator.checked_reduction_merge_commutative_compatible_value_view_correct` | chunks cover the reduction domain; private accumulators and merge order are well formed; merge-order accumulator values fold to the claimed final value; a finite carrier can witness closure, associativity, commutativity, and identity laws; private accumulators can be required size/alignment-compatible with the public reduction cell; bookkeeping, value, algebra, and storage evidence can be packaged in one view theorem | deriving accumulator values/storage specs and connecting finite-carrier laws to concrete C/FP semantics |
| P9 phase separation | `PhaseSeparationWitness.check_phase_protocolb_sound`; `PhaseValueWitness.check_phase_value_protocolb_sound`; `PhaseValueWitness.check_phase_value_protocolb_final_snapshot`; `PhaseProjectionWitness.check_phase_projectionb_sound`; `PhaseProjectionWitness.check_phase_projection_valueb_sound`; `StorageCompatibilityWitness.check_storage_compatibilityb_sound`; `StorageBoundaryView.checked_storage_boundary_refinement_correct`; `PhaseSeparationValidator.checked_phase_projection_compatible_value_view_correct` | reads are visible, writes do not overwrite live cells, next-live cells are covered, next-live values come from phase writes or entry-live values, the checked value protocol yields a final snapshot matching final-live cells, final source live-outs are exactly projected to final phase-live cells, projected boundary values match, projected final phase cells can be required size/alignment-compatible with represented live-outs, and the final projection can use the shared storage-backed boundary view shape | deriving the phase/swap projection and storage specs from concrete phase arithmetic and target code |
| P10 frame preservation | `FramePreservationWitness.check_frame_preservationb_sound`; per-cell corollaries such as `FramePreservationWitness.frame_preservation_write_not_frame`; `FramePreservationValidator.checked_frame_preservation_view_correct` | writes are included in the allowed-write set; allowed writes are disjoint from frame cells; each fragment write is therefore outside the context frame; the side condition can be packaged with the common source-view theorem shape | deriving the write set from concrete instruction semantics |
| overlap-specific composition | `OverlapTilingValidator.checked_overlap_*_view_correct` | duplicated/internal instances project to source instances and commits are unique; optional tile-local closure and private separation | recomputed-value equivalence |

## Theorem Families

The taxonomy points to three theorem families.

1. Identity/schedule theorems:
   `same_state_relation` on inputs and `State.eq` on outputs.  This is the
   existing affine, tiling, ISS, diamond-without-recomputation, and checked
   annotation route.
2. State-relation theorems:
   target and source executions are related by explicit input and output state
   relations.  Layout remapping, private expansion, contraction, inter-array
   reuse, and double buffering belong here.  `ViewPipeline.v` is the common
   composition spine for the current exploratory variants of this family, and
   `generic_state_view` keeps the endpoint view carrier shared across validator
   functor instances.
3. Trace/instance theorems:
   the target trace projects to the source trace, with roles for internal,
   helper, commit, or merge instances.  Overlap tiling, copy protocols, packing,
   and reduction privatization need this family.  Some of them also need a
   state-relation theorem.

## Mechanization Order

The next mechanization should keep the current validators stable and add new
relations beside them.

1. Make the current `State.eq` route an explicit identity instance of a more
   general `state_view_rel`.  The detailed relation design is in
   `STATE_VIEW_RELATION_DESIGN.md`.
2. Finish the layout/padding story only after proving instruction-level
   simulation for rewritten accesses; access-list remapping alone is not enough.
3. Add a first-class instance-trace witness before attempting overlap, packing,
   or copy protocols.
4. Add private-storage erasure and use-def containment for a small scalar
   expansion case.  The current branch has the erasure/view theorem shape, but
   not a full scalar-expansion semantic checker.  It does check the simpler
   hidden-cell subset condition used to prove private cells are not observable,
   plus standalone private no-duplicate and read-after-write trace conditions.
5. Continue strengthening conflict-safe non-injective reuse after the
   state-view relation can express projection from logical values to reused
   physical cells.  The current branch has the finite conflict checker and an
   observer-backed boundary reuse view, but it still leaves lifetime
   over-approximation and value simulation as semantic obligations.
6. Keep C typing, C integer definedness, no-alias grounding, frame preservation,
   and OpenMP race freedom in a separate boundary contract until the PolIR
   fragment theorem is stable.

## Non-Goals

- Do not weaken `State.eq` globally.
- Do not describe the Python experiments as verified validators.
- Do not treat access lists as a substitute for instruction semantics.
- Do not use Pluto as the organizing principle for storage-changing
  transformations.  Pluto remains useful for schedule-centric cases; storage
  changes need their own witnesses.
