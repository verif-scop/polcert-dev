# Storage Generalization Mechanization Plan

This note records the intended proof-engineering direction for extending
PolCert beyond schedule-only validation.  It is a planning note for the
`storage-generalization-20260507` branch, not a claim that the storage
transformations below are already verified.

Start with `doc/STORAGE_AWARE_VALIDATION_OVERVIEW.md` for the canonical
terminology, primitive names, and status boundary.  This file is narrower: it
describes how those ideas could be turned into Coq modules without changing the
existing affine validator API.

For the relation design that explains the status of `State.eq`, private
storage, layout projection, commit, merge, and reuse views, see
`doc/STATE_VIEW_RELATION_DESIGN.md`.

For the broader boundary between these fragment-level theorems and future
contextual C/CompCert correctness, see
`doc/FRAGMENT_TO_CONTEXT_CORRECTNESS_GAPS.md`.

For the transformation taxonomy that motivates the storage and instance
relation primitives, see `doc/POLYHEDRAL_TRANSFORMATION_TAXONOMY.md`.

## Principle

The existing affine validator should remain the identity instance of a more
general transformation contract:

```text
target initial state
  related to
source initial state

target execution
  refines to
source execution

target final state
  related to
source final state
```

The current `EqDom`/same-access route is the special case where the two
programs start from the same concrete state and finish in `State.eq`.
Storage-changing transformations should not weaken or rewrite that route.  They
should add new witnesses and prove new soundness lemmas whose conclusion has
the same relational shape, but with a projection, layout, or commit relation.

## Status Boundary

In this host worktree, the storage-generalization material is documentation and
standalone executable experiments.  A Docker exploration worktree may contain
uncommitted Coq skeletons for the modules named below.  Those skeletons are
useful for understanding the proof shape, but this document should not be read
as saying that the storage-changing route is already integrated into the main
PolCert build.

The rule for integration is:

```text
design note -> local module with local theorem -> proof build -> export
```

No storage validator should be exported through `Validator.v` until its local
checker, soundness theorem, and composition theorem compile in the normal proof
pipeline.

## Mechanization Sketch

The module names in this section are exploration interfaces on the
`storage-generalization-20260507` branch/worktree.  They are not mainline
PolCert claims yet, but the files listed here are now intended to compile
together in the Docker proof environment.

The `src/TransformContract.v` module introduces:

- `state_relation`, a target-state to source-state relation.
- `observation`, the end-state instance of `state_relation`.
- `refinement_under obs before after`, the common semantic postcondition.
- `relational_refinement initial_rel final_rel before after`, the more general
  pipeline contract that relates both initial and final states.
- `observation_contains_state_eq`, allowing existing `State.eq` results to lift
  to any coarser observation.
- `checked_transform_family`, a generic checker/soundness package.
- wrappers showing that `AffineValidator.validate` and
  `AffineValidator.validate_general` are checked transform families under the
  identity observation.
- `refinement_under_to_relational`, which embeds same-initial-state validators
  into the relational contract using `same_state_relation`.
- `relational_refinement_compose`, the end-to-end composition theorem for two
  passes.
- `checked_relational_transform_family_pair_compose`, the packaged two-pass
  form for checked transform families.
- `relational_refinement_monotone`, for simplifying or weakening the composed
  input/output relations without reproving the pass semantics.

Composition shape:

```text
after  -> mid     under R_target_mid_in/out
mid    -> before  under R_mid_source_in/out
------------------------------------------------
after  -> before  under composed input/output relations
```

`src/Validator.v` re-exports the generic view vocabulary and the existing
affine/general wrappers.  The legacy validator API remains unchanged.

The first view-specific implementation step is `src/StateView.v`.  It packages
state relations as views and introduces:

- `view`, a named endpoint relation.
- `identity_view`, whose relation is the current final-state `State.eq`.
- `same_state_view`, matching the current validators' same-Coq-state input
  precondition.
- `view_refinement vin vout before after`, a view-indexed wrapper around
  `relational_refinement`.
- `compose_view`, `view_refinement_compose`, and monotonicity wrappers.
- `view_included_refl`, `view_included_trans`, and `compose_view_monotone`,
  backed by `TransformContract` relation-inclusion algebra.
- `checked_view_transform_family_pair_compose`, the view-level checked-family
  composition theorem.
- checked view-family wrappers for `AffineValidator.validate` and
  `AffineValidator.validate_general`.

This step is deliberately conservative.  Existing validators are wrapped as
`same_state_view -> identity_view`; they are not claimed to accept arbitrary
`State.eq`-related initial states.

The second step splits the storage vocabulary into two modules:

- `src/StorageWitness.v` defines target-to-source `cell_relation`, identity cell
  relation, functionality/respectfulness obligations, access-list remapping, and
  `same_instance_access_remap` for PolyInstrs.  It also proves reflexive
  identity-remap lemmas for instructions and whole PolyLang programs, plus
  compositional lemmas:

```text
same_instance_access_remap target_mid mid after ->
same_instance_access_remap mid_source before mid ->
same_instance_access_remap
  (compose_cell_relation target_mid mid_source)
  before after

pprog_same_instance_access_remap target_mid mid after ->
pprog_same_instance_access_remap mid_source before mid ->
pprog_same_instance_access_remap
  (compose_cell_relation target_mid mid_source)
  before after
```

This is the access-function analogue of `StateView.view_refinement_compose`.
It lets multi-pass storage validation compose declared layout, private erasure,
copy, or reuse remaps through a shared intermediate program instead of
constructing a bespoke combined access relation for each pass sequence.
- `src/StateObservation.v` defines an abstract `CELL_OBSERVER` interface and
  lifts a target-to-source cell relation into a state-level observation.  It
  proves that the identity cell relation yields an observation containing
  `State.eq`.  It also proves that observer-backed cell observations compose:
  a target-to-intermediate observation followed by an intermediate-to-source
  observation implies the observation induced by
  `compose_cell_relation`.  This is the state-observation counterpart of the
  access-remap composition lemmas above.
- `src/StateObservation.v` also defines `cell_view`, which records the public
  source and target cells represented by a relation; target-private cells are
  precisely cells left outside this public view.  `compose_cell_view` composes
  two public views when the first view's source-observable intermediate cells
  and the second view's target-observable intermediate cells agree.  This
  compatibility condition is the non-ad-hoc separation point: a sequence such
  as layout projection followed by private erasure can be collapsed into one
  public endpoint view only when both passes expose the same intermediate
  public footprint.
- `src/StateObservation.v` now also packages this into
  `cell_view_transform_contract`: one pass carries a public `cell_view`, a
  `pprog_same_instance_access_remap` witness under that view's cell relation,
  and a semantic `view_refinement` under that same endpoint view.
  `cell_view_transform_contract_compose` composes two such passes by composing
  both the access relation and the view refinement, then collapsing the final
  composed observation to `compose_cell_view`.  The theorem intentionally keeps
  the initial side as `View.compose_view target_mid mid_source`: a final
  endpoint observation can be weakened after the intermediate state is
  produced by execution, but an arbitrary composed initial endpoint relation
  does not by itself construct a valid intermediate initial state.

This keeps three concerns separate:

```text
TransformContract:
  semantic postcondition shape

StorageWitness:
  which target cells represent which source cells

StateObservation:
  how states are observed through those cells
```

The first concrete feature family is injective layout/access remapping.
The `src/LayoutRemapValidator.v` module introduces a source-view
decomposition:

```text
before
  original logical program

source_view
  logical/source-access view with the target schedule

after
  physical-layout target program
```

The existing validator is reused only for:

```text
validate_general before source_view
```

The storage feature must then prove either the same-initial-state obligation:

```text
layout_source_view_refines rel source_view after
```

or, for true storage layout changes, the stronger relational obligation:

```text
layout_source_view_relational_refines rel source_view after
```

The same-initial-state route composes both facts into:

```text
refinement_under
  (compose_observation (layout_observation rel) identity_observation)
  before
after
```

The relational route composes into:

```text
relational_refinement
  (layout_state_relation rel)
  (layout_pipeline_final_relation rel)
  before
  after
```

where `layout_pipeline_final_relation rel` abbreviates
`compose_state_relation (layout_state_relation rel) identity_observation`.
The input side simplifies because `source_view` and `before` share the same
concrete initial state.

This is the form that should be used for end-to-end pipelines: each pass exports
one input relation and one output relation, and the pipeline theorem composes
them through the intermediate state.

This is intentionally stronger than a taxonomy entry but weaker than a complete
layout optimizer: it fixes the proof architecture for layout remapping while
leaving the actual rewritten-instruction proof as an explicit obligation.  That
obligation is necessary because `PolyLang` execution is driven by `pi_instr`,
not only by `pi_waccess`/`pi_raccess`.

The C-like state should instantiate the observation interface:

- `src/CStateObservation.v` defines `CStateObserver`.
- `observe_cell` is backed by `CState.read_cell`.
- observed cell equivalence is strict `MemCell` equality, not
  `PolyBase.cell_eq`.

The strict choice is deliberate.  `PolyBase.cell_eq` uses vector equality
(`veq`), which is appropriate for polyhedral dependence reasoning but is broader
than the concrete indexing accepted by `CState.calc_offset`.  This split is a
useful design result: logical cell equivalence and concrete observable-cell
equivalence should not be conflated.

The first executable layout witness fragment should be deliberately small:

- `src/LayoutWitness.v` defines `array_rename`, a padding-style layout map from
  a physical target array id to a logical source array id.
- `array_rename_cell_relation` keeps subscripts unchanged and changes only the
  array id relation.
- `array_rename_access_pairb` checks that two access functions have identical
  affine subscripts and array ids related by the rename witness.
- `array_rename_access_listb` and the PolyInstr/PolyLang checkers lift this to
  access lists and programs.
- Soundness lemmas connect these boolean checks to
  `same_instance_access_remap`.

The `src/LayoutRemapValidator.v` route exposes both
`checked_array_rename_layout_remap_correct` and
`checked_array_rename_layout_remap_view_correct`, which compose:

```text
validate_general before source_view
array-rename access-remap checker for source_view/after
layout_source_view_refines for the rewritten target instruction semantics
```

The result is still not a complete layout optimizer, but it is an actual
feature-shaped checked route for the padding/array-rename subset of layout
remapping.  The view theorem is the preferred interface for future end-to-end
composition.

## Current Interface Gap

`StateTy` exposes `State.eq`, `State.non_alias`, and basic equivalence
laws, but it does not expose a generic per-cell observation or read relation.
That is enough for the existing schedule validators, because they end in
full-state equality.  It is not enough to define a concrete layout/projection
observation generically.

The storage branch currently takes the first of the two possible routes:

```text
1. add a small observable-state interface that can compare selected MemCell
   values under a projection, or
2. prove the first concrete storage primitive at the CState/CInstr layer, where
   read_cell/write_cell already exist.
```

The first choice is cleaner for a reusable validator framework and is now
represented by `CELL_OBSERVER`, `related_cells_view`, and `cell_view`.
`related_cells_view_compose_included` and `compose_cell_view` make this route
compositional: composing two storage views produces the same kind of endpoint
relation, provided their shared intermediate public footprint is compatible.
The second route remains useful for narrow prototypes but should not become the long-term
abstraction.  `src/CStateObservation.v` instantiates the observer interface
with `CState.read_cell`.

## Next Mechanization Layers

### 1. Source No-Alias Boundary

Target transformation class:

```text
not a transformation
front-end assumption that logical source objects have disjoint footprints
```

Exploratory skeleton status: `src/SourceNoAliasWitness.v` now mechanizes a
finite footprint checker:

```text
check_source_no_aliasb footprints = true ->
source_no_alias_obligations footprints
```

The checker proves:

```text
logical object ids are duplicate-free
each object footprint is duplicate-free
different object footprints are pairwise disjoint
```

This witness should eventually sit at the C/PolIR boundary.  It does not
rewrite programs; it records the memory-abstraction condition needed before
layout, private storage, reuse, or schedule legality can be interpreted over
logical cells.

### 2. Frame Preservation Boundary

Target transformation class:

```text
not a transformation
contextual condition that transformed fragments do not write frame cells
```

Exploratory skeleton status: `src/FramePreservationWitness.v` now mechanizes a
finite allowed-write checker:

```text
check_frame_preservationb frame_cells write_cells allowed_write_cells = true ->
frame_preservation_obligations frame_cells write_cells allowed_write_cells
```

The checker proves:

```text
frame cells are duplicate-free
all fragment writes are included in the allowed-write set
the allowed-write set is disjoint from frame cells
therefore fragment writes are disjoint from frame cells
```

The module now exposes both the set-level statement and per-cell corollaries:
`frame_preservation_allowed_not_frame`,
`frame_preservation_write_not_frame`, and
`frame_preservation_write_neq_frame_cell`.  These are the facts a future
contextual proof would use when showing that a transformed fragment leaves
surrounding program storage untouched.

`src/FramePreservationValidator.v` packages the same finite witness into the
common source-view theorem shape:

```text
checked_frame_preservation_view_correct
```

The contract returns the frame obligations, the derived write/frame
disjointness fact, and the supplied semantic refinement from the source view
to the target output view.  This is intended as a reusable side condition for
layout, private expansion, scratchpad, reuse, versioning, and overlap wrappers,
not as a separate storage transformation.

This should become a common side condition for storage-changing transformations
when they are moved from isolated PolIR fragments toward C/CompCert
contextual correctness.  The current skeleton still expects `write_cells` to
be supplied; deriving it from instruction semantics is future work.

### 3. Injective Access Remapping

Target transformation class:

```text
same statement instances
changed physical access map
projection observation
```

Exploratory skeleton status: the source-view composition theorem, a view-level
composition theorem, a concrete C-like observer, and a padding/array-rename
boolean checker compile in the Docker worktree.  `src/PaddingLayoutWitness.v`
now also separates the allocation/padding side from the access-rewrite side:

```text
check_padding_layoutb mapping padding_cells allocated_cells = true ->
padding_layout_obligations mapping padding_cells allocated_cells
```

The checker proves:

```text
source cells in the mapping are duplicate-free
target cells in the mapping are duplicate-free
mapped target cells are allocated
padding cells are duplicate-free
padding cells are allocated
padding cells are disjoint from the represented target image
```

`src/LayoutValueWitness.v` adds the boundary value side of the same map:

```text
check_layout_valueb value_eqb mapping entries = true ->
layout_value_obligations mapping entries
```

The entries must be positionally aligned with the source-to-target layout map,
and each source logical value must equal the represented target physical value.
As with the other value witnesses, this is boundary evidence: deriving entries
from concrete rewritten instructions remains a separate semantic proof.

`src/PaddingLayoutValidator.v` exposes
`checked_padding_layout_view_correct`, which composes these allocation and
separation facts under an explicit rewritten-access semantic refinement.
`checked_padding_layout_value_view_correct` additionally returns the boundary
value obligations.  The new access variants
`checked_padding_layout_access_view_correct` and
`checked_padding_layout_access_value_view_correct` also return the
`LayoutWitness` pprog-level access remap fact:

```text
check_pprog_array_rename_access_remapb renames source_view after = true ->
pprog_same_instance_access_remap (array_rename_cell_relation renames)
  source_view after
```

The companion permutation variants,
`checked_padding_layout_permutation_access_view_correct` and
`checked_padding_layout_permutation_access_value_view_correct`, return the same
pprog-level remap fact for finite index permutations:

```text
check_pprog_array_index_permutation_access_remapb layouts source_view after = true ->
pprog_same_instance_access_remap
  (array_index_permutation_cell_relation layouts)
  source_view after
```

This covers transpose-style rewrites such as `A[i][j] -> A_t[j][i]`.
The affine-layout variants,
`checked_padding_layout_affine_access_view_correct` and
`checked_padding_layout_affine_access_value_view_correct`, use affine
composition to cover linearized layouts:

```text
check_pprog_array_affine_layout_access_remapb layouts source_view after = true ->
pprog_same_instance_access_remap
  (array_affine_layout_cell_relation layouts)
  source_view after
```

The key proof step is `matrix_product_assoc`: if the target access function is
the matrix product of the declared layout map and the source access function,
then each target dynamic access denotes the declared affine image of the source
logical cell.  This supports patterns such as `A[i][j] -> A_lin[i * stride + j]`.
The preferred interface is now the unified declared-layout checker:

```text
check_pprog_declared_layout_access_remapb layouts source_view after = true ->
pprog_same_instance_access_remap
  (declared_layout_cell_relation layouts)
  source_view after
```

Each `declared_array_layout` carries one of three index maps: same-index,
finite permutation, or affine index composition.  The older specialized
rename/permutation/affine theorem names are retained as compatibility slices,
but new layout clients should target the declared-layout interface so future
layout fragments do not add another parallel theorem family.
`checked_padding_layout_declared_access_compatible_value_view_correct` is the
current strongest padding/layout wrapper.  It packages padding separation,
declared-layout access remapping, boundary value evidence, and
`StorageCompatibilityWitness` size/alignment compatibility for every mapped
logical-to-physical layout cell:

```text
check_storage_compatibilityb mapping logical_specs physical_specs = true ->
storage_compatibility_obligations mapping logical_specs physical_specs
```

This matters for layout and padding for the same reason it matters for reuse:
injectivity and in-bounds allocation are not enough if a physical layout cell
cannot actually represent the logical source cell's storage class.
The next missing piece is still the proof that a concrete rewritten target
instruction refines the source-view instruction under the induced cell
relation and that layout declarations are derived from generated C.

### 4. Fresh Private Storage

Target transformation class:

```text
same statement instances
private or expanded storage cells
projection observation that erases private cells
```

The initial fragment should be no-live-in/no-live-out scalar expansion.  The
main proof obligation is not scheduling legality; it is freshness plus local
use-def containment.

Exploratory skeleton status: `src/PrivateStorageValidator.v` now states the
view-level route.  A `public_view : cell_view` defines the observable public
cells, `private_target_cell` names target-only storage, and the contract
requires private cells to be outside the public target-to-source relation.
`src/PrivateStorageWitness.v` mechanizes the first finite witness for this:
`mem_cells_subsetb private_cells hidden_cells = true` proves every private cell
is hidden, and therefore unobservable under `hidden_identity_cell_view`.  The
same file also includes two local privatization checks:

```text
mem_cells_nodupb private_cells = true
  -> NoDup private_cells

check_private_separationb private_cells public_cells frame_cells = true
  -> private cells are duplicate-free and disjoint from public/frame cells

check_private_use_def_traceb trace = true
  -> every private read in trace has an earlier same-cell private write

check_private_access_use_def_traceb access_trace = true
  -> for every dynamic point, the instantiated MemCell trace has the same
     read-after-write property
```

`src/PrivateBoundaryWitness.v` adds the first live-in/live-out boundary-copy
layer:

```text
check_private_boundaryb
  private_cells public_liveins public_liveouts copyins copyouts = true
  -> private_boundary_obligations
       private_cells public_liveins public_liveouts copyins copyouts

check_private_boundary_private_uniqueb copyins copyouts = true
  -> private_boundary_private_unique_obligations copyins copyouts
```

The obligations say that every required public live-in is covered by a copy-in
pair, every required public live-out is covered by a copy-out pair, every
boundary pair uses a declared private cell, and public copy-out destinations are
unique.  The private-side uniqueness checker is deliberately separate: public
live-ins may be broadcast to many private cells, but two distinct boundary
pairs should not accidentally write or read the same private cell unless a
later, value-aware theorem explicitly justifies that aliasing.  The same module
adds a boundary value layer:

```text
check_private_boundary_valueb
  value_eqb copyins copyouts copyin_values copyout_values = true
  -> private_boundary_value_obligations
       copyins copyouts copyin_values copyout_values
```

The value entries must align with the copy-in/copy-out pairs, and each public
boundary value must equal the corresponding private boundary value.  This still
does not derive copied values from concrete expressions; it exposes the finite
value-flow evidence that an instruction-semantics proof should produce.

The semantic obligation is still abstract:

```text
private_source_view_refines_view public_view source_view after
```

`src/PrivateStorageValidator.v` exposes these composed routes as
`checked_local_private_expansion_view_correct` for concrete-cell traces and
`checked_access_local_private_expansion_view_correct` for access-function
traces.  The latter is closer to PolIR because it validates the access relation
before instantiating it at each dynamic point.  Both routes return the local
private obligations and, assuming the remaining semantic refinement, compose
the pass into the unified `view_refinement` endpoint.
`checked_boundary_private_expansion_view_correct` additionally returns the
boundary-copy obligations before composing the same endpoint theorem.
`checked_boundary_private_unique_expansion_view_correct` additionally returns
the private-side boundary uniqueness obligation.
`checked_boundary_private_value_expansion_view_correct` additionally returns
the boundary value obligations.
`checked_boundary_private_unique_value_expansion_view_correct` now combines the
last two boundary layers: it returns both private-side boundary uniqueness and
aligned public/private boundary value evidence under the same observer-backed
private-erasure view theorem.  This is the private-storage analogue of the
larger scratchpad contract: it keeps the finite boundary protocol explicit
while still leaving expression-derived copy values to the semantic refinement.
`checked_boundary_private_unique_compatible_value_expansion_view_correct` adds
the same size/alignment compatibility layer used by layout and reuse: every
copy-in and copy-out boundary pair is interpreted as a public-to-private
storage mapping, and `StorageCompatibilityWitness` must prove the mapped cells
have compatible storage specs.  This makes private copies more than fresh
names: they must also be capable of representing the public value they copy.

Later syntactic validators should discharge this obligation with freshness,
reaching-definition, boundary value-flow, and non-escape checks.  The
hidden-cell subset checker, private trace checker, boundary checker, and
boundary value checker are local witness components; they are not yet a proof
that the privatized program computes the same public values from concrete
instructions.

### 5. Scalar Promotion

Target transformation class:

```text
same statement instances
one public source cell simulated by target-private scalar storage
entry load / local scalar use / optional live-out store
```

Exploratory skeleton status: `src/ScalarPromotionWitness.v` now mechanizes the
finite local storage protocol:

```text
PromotionLoad source scalar
PromotionScalarRead scalar
PromotionScalarWrite scalar
PromotionStore scalar source
PromotionGlobalWrite cell

check_scalar_promotionb source scalar liveout trace = true ->
scalar_promotion_obligations source scalar liveout trace
```

The checker proves:

```text
scalar reads and writes occur only after the entry load
scalar events refer to the expected scalar cell
ordinary global writes do not target the promoted source cell
if the source cell is live-out, the trace ends with store-back
```

`src/ScalarPromotionValueWitness.v` now adds the first value-flow witness over
the same event stream:

```text
check_scalar_value_traceb value_eqb value_trace = true ->
scalar_value_simulation_obligations value value_trace
```

The value-flow checker proves:

```text
load initializes the scalar to the source value
scalar reads observe the current scalar value
scalar writes update the current scalar value
store-back commits the current scalar value to the source cell
```

`src/ScalarPromotionValidator.v` exposes both
`checked_scalar_promotion_view_correct` and
`checked_scalar_promotion_value_view_correct`.  The latter combines storage
protocol, value-flow consistency, and private separation before composing under
the shared `view_refinement` endpoint.  It still deliberately leaves the
instruction-level link explicit: a future proof must derive the value trace
from concrete expression and CState read/write semantics.
The new `checked_scalar_promotion_compatible_view_correct` and
`checked_scalar_promotion_compatible_value_view_correct` variants additionally
package storage compatibility for the promoted source cell and scalar/register
cell, so scalar promotion can state that the target-local scalar is fresh and
able to hold the represented source value.

### 6. Version Selection and Commit

Target transformation class:

```text
same statement instances
more physical versions than logical source values
selected version / commit observation
```

Exploratory skeleton status: `src/VersionCommitWitness.v` now mechanizes the
finite selected-version checker:

```text
check_version_commitb source_liveouts mapping = true ->
version_commit_obligations source_liveouts mapping
```

The mapping is source logical cell to selected target version cell.  The
checker proves:

```text
every source live-out appears in the selected-version domain
the selected-version domain has no duplicates
selected target versions have no duplicates
```

The module now also exposes those consequences in a form that later semantic
proofs can use directly.  `version_commit_liveout_selected` gives a selected
target version for every source live-out.  `version_commit_selected_source_liveout`
turns any selected relation edge back into a source live-out.  The companion
facts `version_commit_sources_nodup`, `version_commit_versions_nodup`, and
`version_commit_selected_version_in_versions` keep the finite image explicit.
This makes the selected-version relation behave like an exact commit view,
instead of just a well-formed list checked by a boolean procedure.

This is the array expansion/versioning counterpart to conflict-safe reuse:
expansion should select unique committed versions, while contraction may reuse
physical cells when conflicts are absent.  `src/VersionCommitValueWitness.v`
adds the selected-version value layer:

```text
check_version_valueb value value_eqb mapping entries = true ->
version_value_obligations value mapping entries
```

The checker proves:

```text
value evidence is aligned with the selected source/version cell pairs
the selected version value equals the represented source value
```

`src/VersionCommitValidator.v` exposes both
`checked_version_commit_view_correct` and
`checked_version_commit_value_view_correct`.  The value version returns finite
commit and value obligations while still leaving the derivation of selected
version values from concrete writes as an explicit semantic refinement.  The
new `checked_version_commit_compatible_view_correct` and
`checked_version_commit_compatible_value_view_correct` variants additionally
package storage compatibility for the selected source/version pairs.  This is
the array-expansion analogue of the reuse compatibility side condition:
selected physical versions must be able to store the source live-out values
they represent, while deriving size/alignment specs from concrete C types and
allocations remains explicit.

### 7. Reduction Merge

Target transformation class:

```text
private partial accumulators
merge back to source-observable accumulator
algebra-dependent observation
```

Exploratory skeleton status: `src/ReductionMergeWitness.v` now mechanizes the
finite reduction bookkeeping checker:

```text
check_reduction_mergeb source_domain chunks partial_accumulators merge_order = true ->
reduction_merge_obligations source_domain chunks partial_accumulators merge_order
```

The checker proves:

```text
chunks exactly cover the source reduction domain
private accumulators are duplicate-free
merge order covers exactly the private accumulators
```

The module also exposes these exact-cover consequences as named theorems for
downstream semantic proofs: covered chunk instances are duplicate-free,
source-domain instances are covered by chunks, covered instances belong to the
source domain, private accumulators are duplicate-free, merge order is
duplicate-free, every private accumulator is merged, and every merged
accumulator is private.

`src/ReductionMergeValueWitness.v` adds a value-flow witness for the merge
itself:

```text
check_reduction_value_mergeb value_eqb merge_op initial final merge_order values = true ->
reduction_value_merge_obligations initial final merge_order values
```

The value checker proves:

```text
each merge-order accumulator has a supplied partial value
folding those values with the supplied merge operator yields the claimed final value
```

`src/ReductionAlgebraWitness.v` adds a bounded algebra-law witness over an
explicit finite carrier:

```text
check_reduction_associative_lawb carrier = true ->
reduction_associative_obligations carrier

check_reduction_commutative_lawb carrier = true ->
reduction_commutative_obligations carrier
```

The associative witness proves closure on the carrier, associativity on the
carrier, and a two-sided identity law on the carrier.  The commutative witness
adds commutativity.  This does not replace the language-level semantic question
for arbitrary C values or floating point; it gives a checkable law witness for
bounded/example domains and keeps the global semantic interpretation explicit.

`src/ReductionMergeValidator.v` exposes both
`checked_reduction_merge_view_correct` and
`checked_reduction_merge_value_view_correct`.  It also exposes
`checked_reduction_merge_associative_view_correct` and
`checked_reduction_merge_commutative_view_correct`, which return finite
carrier-law obligations.  The combined wrappers
`checked_reduction_merge_associative_value_view_correct` and
`checked_reduction_merge_commutative_value_view_correct` package all three
pieces together: finite reduction chunk/merge cover, accumulator-value folding,
and the relevant finite-carrier algebra law.
`checked_reduction_merge_commutative_compatible_value_view_correct` adds the
private-accumulator storage side condition: each private partial accumulator is
paired with the public reduction accumulator and must be size/alignment
compatible according to `StorageCompatibilityWitness`.  These wrappers still
compose the pass under the feature-specific semantic refinement; for floating
point, bit-exact and relaxed-reassociation reductions must remain different
semantic claims.

### 8. Copy Protocol

Target transformation class:

```text
inserted copy-in / compute / copy-out instances
copy-mediated local storage
commit observation
```

This requires a target-instance role relation.  It cannot be represented by the
current `EqDom` checker, because the target has extra helper instructions.

Exploratory skeleton status: `src/CopyProtocolWitness.v` now mechanizes a
finite copy/local/commit bookkeeping witness:

```text
CopyIn source local
LocalRead local
LocalWrite local
CopyOut local target
```

The checker proves:

```text
check_copy_protocol_wfb trace = true ->
copy_protocol_wf trace

check_copy_protocol_wfb trace = true ->
NoDup (copy_protocol_committed_targets trace)

check_copy_commit_coverb expected_targets trace = true ->
copy_commit_obligations expected_targets trace

check_copy_instance_traceb targets trace = true ->
copy_instance_trace_obligations targets trace
```

This covers the local read coverage and unique copy-out commit parts of P4/P7.
`src/CopyCommitWitness.v` now adds the exact boundary coverage layer for
update-style scratchpad cases: the committed copy-out target cells are
duplicate-free and exactly equal to the expected observable target set.  This
turns the informal `missing_copy_out` standalone negative into a Coq witness
obligation.
`src/CopyInstanceWitness.v` connects the copy protocol to helper target
instances: copy-in/local events must be internal projected instances, while
copy-out events must be commit-role projected instances.  This makes the
instance-projection commit exact-cover fact talk about copy-out helpers, not
only an unrelated list of projected instances.
`src/CopyMappingWitness.v` adds the local remapping side condition:

```text
check_copy_mappingb mapping trace = true ->
copy_mapping_obligations mapping trace
```

The mapping is a finite public-to-local cell map, injective on both public and
local cells.  The checker proves that copy-in events use the declared
public/local pair, local reads and writes use declared local cells, and copy-out
events commit back through the declared pair.  This captures the packing
condition that, for example, `Bp[k]` really represents `B[kk+k]` throughout the
tile.  More aggressive local reuse can be layered later with lifetime/conflict
witnesses.

`src/CopyProtocolValueWitness.v` now adds the first source/local value-flow
layer over the same event stream:

```text
check_copy_value_traceb value_eqb value_trace = true ->
copy_value_simulation_obligations value value_trace
```

The value-flow checker proves:

```text
copy-in transfers the source value to the local cell
local reads observe the current local value
local writes update the current local value
copy-out commits the current local value to the target cell
```

It still does not prove that the inserted helper instances are ordered by a
target trace projection, nor does it derive the value trace from concrete
instruction semantics.  Those are the next layers needed before
scratchpad/packing has a full semantic theorem.

`src/CopyProtocolValidator.v` now gives this witness a composable theorem
shape:

```text
checked_copy_protocol_view_correct
checked_copy_protocol_mapping_view_correct
checked_copy_protocol_value_view_correct
checked_copy_protocol_mapping_value_view_correct
checked_copy_protocol_commit_mapping_value_view_correct
```

The value-flow and mapping variants return the corresponding protocol,
remapping, and value obligations and compose the pass into `view_refinement`,
assuming the remaining copy-specific semantic refinement.  The commit/mapping/
value variant additionally returns the copy-out exact-cover obligation, so a
generic copy-mediated update can state that its copy-outs commit exactly the
source-observable public targets without going through the scratchpad-specific
instance/private-storage wrapper.

`src/ScratchpadCopyValidator.v` combines the primitives that scratchpad and
packing transformations actually need:

```text
check_instance_projectionb source_domain source_liveouts targets = true
check_copy_protocol_wfb copy_trace = true
check_copy_commit_coverb expected_commit_targets copy_trace = true
check_copy_instance_traceb targets copy_trace = true
check_private_separationb local_cells public_cells frame_cells = true
```

The theorem `checked_scratchpad_copy_view_correct` returns a single
`scratchpad_copy_view_contract` containing projection, copy-protocol, and
local-separation obligations, and composes the pass through `view_refinement`
under the remaining semantic refinement that local computation simulates the
source computation.  The theorem
`checked_scratchpad_copy_commit_view_correct` additionally returns the
copy-out exact-cover obligation for source-observable updates.
`checked_scratchpad_copy_instance_view_correct` and
`checked_scratchpad_copy_instance_commit_view_correct` additionally return the
copy-instance role-alignment obligation.
`checked_scratchpad_copy_full_view_correct` packages the larger scratchpad
contract used by packing-style transformations: projection, copy protocol,
copy-out exact cover, copy-instance role alignment, public-to-local remapping,
copy value flow, and local-buffer separation all compose under the same
`view_refinement` endpoint.
`checked_scratchpad_copy_compatible_full_view_correct` additionally requires
`StorageCompatibilityWitness` on the public-to-local copy mapping, so the local
buffer cells used for packing/scratchpad storage must have size/alignment
compatible with the public cells they represent.  It still leaves the
derivation of traces, values, and storage specs from concrete target
instructions as the explicit semantic refinement.

### 9. Conflict-Safe Reuse

Target transformation class:

```text
same or projected logical instances
non-injective physical storage map
projection observation
```

The first version should accept an explicit conflict relation as a witness and
check:

```text
Conf(v1, v2) -> rho(v1) != rho(v2)
```

This is the rolling-buffer / array-contraction entry point.  It should come
after projection observations are already in place.

Exploratory skeleton status: `src/ReuseConflictWitness.v` now mechanizes the
finite checker for this primitive:

```text
reuse_mapping:
  logical MemCell -> physical MemCell

conflict_pairs:
  logical values whose live ranges overlap

check_live_conflictb intervals conflicts = true ->
live_conflict_obligations intervals conflicts

check_conflict_safe_reuseb mapping conflicts = true ->
conflict_safe_reuse_obligations mapping conflicts

check_reuse_valueb value_eqb mapping entries = true ->
reuse_value_obligations mapping entries

check_reuse_boundaryb mapping source_liveouts = true ->
reuse_boundary_obligations mapping source_liveouts
```

The proved obligations are:

```text
NoDup (reuse_mapping_sources mapping)
conflicts_separated mapping conflicts
```

For every listed conflict pair, both logical values must have a physical
mapping and those physical cells must be distinct.  This is still only the
finite witness check.  The boundary checker separately records which
source-observable logical cells must be projected through the reuse map at the
final observation point; every listed source live-out must have a physical
representative.  A complete contraction theorem still needs a separate
derivation that the supplied conflict relation really over-approximates
live-range overlap under the chosen schedule.

`src/LifetimeConflictWitness.v` mechanizes the intermediate live-range cover
obligation.  Given explicit half-open live intervals, it checks that the
intervals are well formed, that each logical cell has at most one interval in
the witness, and that every overlapping pair appears in the conflict list
modulo pair order.  Combined with `conflict_safe_reuse_obligations`, it proves
`live_overlaps_reuse_separated`: every pair of live-overlapping logical values
is mapped to distinct physical cells.  The remaining unmechanized step is
deriving the live intervals themselves from schedule/access semantics.

`src/ReuseValueWitness.v` adds the boundary value side of the same reuse map:
each entry is positionally aligned with a logical-to-physical mapping pair, and
the logical value must equal the physical value observed at the boundary.  This
does not prove that the physical cell was safe to reuse during execution; it
only checks the finite evidence needed by the final projection view.

`src/StorageCompatibilityWitness.v` adds the storage-class side condition for
reuse-like maps:

```text
check_storage_compatibilityb mapping logical_specs physical_specs = true ->
storage_compatibility_obligations mapping logical_specs physical_specs
```

The finite witness checks duplicate-free logical/physical specs and proves that
every logical-to-physical mapping entry has matching size/alignment specs.  It
is intentionally only a boundary compatibility check; deriving these specs from
C types, object sizes, and target allocation remains future work.

`src/ReuseConflictValidator.v` now exposes the composed contraction-facing
wrappers
`checked_compatible_live_conflict_reuse_view_correct` and
`checked_compatible_live_conflict_reuse_value_view_correct`.  These combine
the live-range overlap cover, conflict-safe non-injective reuse, derived
live-overlap physical separation, optional boundary value evidence, and
storage compatibility in one view theorem.  This is the finite side-condition
shape for rolling-buffer/array-contraction examples; the derivation of live
intervals, boundary values, and storage specs from concrete C semantics remains
explicit.

`src/InterArrayReuseWitness.v` packages the cross-array sharing case as a
composition of existing reuse primitives:

```text
check_inter_array_reuseb mapping intervals conflicts logical_specs physical_specs = true ->
inter_array_reuse_obligations mapping intervals conflicts logical_specs physical_specs
```

The record contains live-conflict cover, conflict-safe reuse, and storage
compatibility obligations.  The useful derived theorem is
`inter_array_same_physical_not_live_overlap`: two distinct logical cells that
map to the same physical cell cannot have overlapping live intervals.  This is
the intended proof fact for examples where `T1[i]` and `T2[i]` share `Buf[i]`
only after `T1[i]` is dead.

`src/InterArrayReuseValidator.v` lifts that composed witness into the common
view theorem shape:

```text
checked_inter_array_reuse_view_correct
```

The contract returns the finite inter-array reuse obligations, the derived
live-overlap separation fact, and the supplied semantic refinement from the
source view to the target output view.  This mirrors the existing reuse and
version-commit wrappers while keeping the boundary projection explicit.

`src/ReuseStateView.v` adds the first state-view side of this story:

```text
reuse_cell_relation boundary_mapping
reuse_view boundary_mapping
reuse_boundary_cell_view boundary_mapping source_liveouts
```

The mapping is a boundary selector from source logical cells to target physical
cells.  It is suitable for the final observation, not for proving that the
mapping was live-range safe throughout execution.  The new boundary cell view
restricts the public relation to the declared source live-outs and makes target
observability the image of that relation.  This connects non-injective reuse to
the same `cell_view` vocabulary used by layout and private erasure.
`src/StorageBoundaryView.v` packages the reusable endpoint version of this
pattern.  Its checked theorem combines finite source-liveout coverage,
logical/physical size-alignment compatibility, and the observer-backed boundary
view:

```text
check_storage_boundary_viewb mapping source_liveouts logical_specs physical_specs = true
semantic view_refinement to reuse_boundary_view mapping source_liveouts
----------------------------------------------------------------------
view_refinement before after under the storage-backed boundary view
```

This is deliberately not a new feature-specific optimizer theorem.  It is a
shared relation layer for any pass whose final observable state is described by
a finite logical-to-physical boundary selector, including phase projection,
reuse/contraction, layout live-outs, and copy-out protocols.
`src/ReuseConflictValidator.v` then exposes
`checked_conflict_reuse_view_correct`, which returns the finite conflict
obligations and composes the pass under the still-explicit reuse semantic
refinement.

### 10. Phase Separation

Target transformation class:

```text
same logical values
phase-dependent physical representation
visibility and no-overwrite protocol
```

Exploratory skeleton status: `src/PhaseSeparationWitness.v` now mechanizes a
finite phase protocol checker:

```text
check_phase_protocolb entry_live steps = true ->
phase_protocol_safe entry_live steps

check_phase_value_protocolb value_eqb entry_live entry_values steps value_steps = true ->
phase_value_protocol entry_live entry_values steps value_steps

check_phase_projectionb source_liveouts final_live projection = true ->
phase_projection_obligations source_liveouts final_live projection

check_phase_projection_valueb value_eqb projection projection_values = true ->
phase_projection_value_obligations projection projection_values
```

Each step records phase reads, phase writes, and next-live cells.  The checker
proves:

```text
phase reads are entry-live
phase writes are disjoint from entry-live cells
next-live cells come from entry-live cells or this phase's writes
```

`src/PhaseValueWitness.v` adds the value-flow layer for the same phase
protocol.  Each phase carries finite entry/write/next snapshots.  The checker
requires the snapshots to match the phase cell sets, every read to have an
entry value, and every next-live value to equal either the written value for
that cell or the inherited entry value.  This still does not prove that a phase
selector implements a source logical time; it only validates the local
copy/visibility value flow between phase boundaries.
The module also exposes `phase_value_protocol_final_values` plus
`phase_value_protocol_final_snapshot` and
`check_phase_value_protocolb_final_snapshot`: once the finite value protocol is
accepted, the final value snapshot is known to match
`phase_protocol_final_live`.  This is the bridge from local per-phase value
flow to the final-boundary projection witness.

`src/PhaseProjectionWitness.v` adds the final-boundary layer needed by
double-buffering-style protocols.  Given the final live physical phase cells,
the checker requires the projection map to cover every source live-out exactly
once, use duplicate-free final target cells, and point only into final-live
physical storage.  The optional value checker requires each projected source
boundary value to equal the corresponding final physical value.  This closes the
finite boundary evidence for examples such as `A[T][i]` being represented by
`cur[i]` after the last swap; it still leaves the derivation of that projection
from concrete phase arithmetic as an explicit semantic proof obligation.
The module now also exposes `phase_projection_cell_relation`, turning the
source-to-target projection list into the common target-to-source
`cell_relation` shape, plus derived facts: every source live-out has a mapped
target in final-live storage, every mapped source is a live-out, every mapped
target is final-live, and both projection sources and targets are
duplicate-free.

`src/PhaseSeparationValidator.v` exposes
`checked_phase_separation_view_correct` and
`checked_phase_separation_value_view_correct`, plus
`checked_phase_projection_view_correct` and
`checked_phase_projection_value_view_correct`.  These theorem variants return
visibility, overwrite-safety, optional value-flow, and optional final-projection
facts, then compose the pass under the remaining semantic refinement.  For
double buffering, that remaining refinement is now narrower: it must justify
that the concrete swap/phase update produces the supplied projection evidence,
rather than leaving the existence of the final projection implicit.
`checked_phase_projection_compatible_value_view_correct` is the strongest
current phase wrapper: it also requires `StorageCompatibilityWitness` for the
final projection map, so every physical final-live phase cell is compatible
with the logical source live-out it represents.

### 11. Instance Projection and Overlap

Target transformation class:

```text
duplicated or helper target instances
target-to-source projection
commit exact cover for source-visible outputs
```

Exploratory skeleton status: `src/InstanceProjectionWitness.v` now mechanizes
the finite role/projection checker:

```text
Internal:
  target instance is auxiliary or recomputed and not source-visible

Commit:
  target instance commits the projected source live-out

check_instance_projectionb source_domain source_liveouts targets = true ->
instance_projection_obligations source_domain source_liveouts targets
```

The obligations state that every target instance projects into the source
domain, and that commit-role target instances form an exact duplicate-free
cover of the requested source live-outs.  This is the global instance side of
overlapped tiling and helper-copy transformations.
The module also exposes derived facts for downstream semantic proofs:
commit sources are projected sources, commit sources are duplicate-free,
source live-outs are committed, commits are source live-outs, and every
source live-out belongs to the checked source domain.

`src/OverlapClosureWitness.v` adds the tile-local closure side condition:

```text
check_overlap_closureb tiles = true ->
overlap_closure_obligations tiles

check_overlap_ordered_closureb tiles = true ->
overlap_ordered_closure_obligations tiles
```

Each finite tile dependency records a consumer and producer source instance.
The checker proves that every dependency consumer is projected by a target
computation in the same tile, and that every producer is either listed as a
tile live-in or projected by a computation in the same tile.  The ordered
variant additionally proves that tile-produced dependencies appear before their
consumers in the tile target trace.  This is still a finite witness over
already-derived dependencies and trace order; deriving those dependencies from
the concrete schedule/access semantics remains future work.

`src/InstanceProjectionValidator.v` exposes
`checked_instance_projection_view_correct`, which follows the same composition
pattern as private/copy/reuse: return the finite projection obligations, keep
the remaining value simulation explicit, and compose through `view_refinement`.
`src/OverlapTilingValidator.v` then packages the overlap-specific theorem
shapes:

```text
checked_overlap_no_private_view_correct:
  projection witness
  semantic overlap refinement
  no extra state-view change beyond the chosen output view

checked_overlap_private_view_correct:
  projection witness
  private/tile-local separation witness
  semantic overlap refinement
  output view may erase or project tile-private state

checked_overlap_closure_view_correct:
  projection witness over flattened tile targets
  tile-local dependence-closure witness
  semantic overlap refinement

checked_overlap_private_closure_view_correct:
  projection witness over flattened tile targets
  tile-local dependence-closure witness
  private/tile-local separation witness
  semantic overlap refinement

checked_overlap_ordered_closure_view_correct:
  projection witness over flattened tile targets
  tile-local dependence-closure and producer-order witness
  semantic overlap refinement

checked_overlap_private_ordered_closure_view_correct:
  projection witness over flattened tile targets
  tile-local dependence-closure and producer-order witness
  private/tile-local separation witness
  semantic overlap refinement
```

This keeps two facts separate: duplicated target instances are justified by
the projection/commit witness; tile-local recomputation is justified by a
closure witness; materialized halo or tile buffers require storage separation
and an output view that hides or commits them.

## Integration Rule

Do not relax `EqDom`, `wf_pinstr_general`, or existing affine correctness
theorems to make storage examples pass.  Add new relation modules parallel to
the tiling pattern:

```text
StorageWitness.v
StorageRelation.v
StorageBoolChecker.v
StorageValidator.v
```

Each new validator should prove a theorem ending in either `refinement_under`
or `view_refinement`.  Generic wrappers can be exported through `Validator.v`;
observer-specific storage validators should be exported through a concrete
adapter such as `CStateObservation.v`.
