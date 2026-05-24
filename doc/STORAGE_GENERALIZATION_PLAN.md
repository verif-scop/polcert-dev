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

The module names in this section are design targets.  They may match local
exploration skeletons, but the claims below should be read as the intended
proof interface, not as a statement that these modules already compile in the
main proof build.

The intended `src/TransformContract.v` module would introduce:

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
- `relational_refinement_monotone`, for simplifying or weakening the composed
  input/output relations without reproving the pass semantics.

Composition shape:

```text
after  -> mid     under R_target_mid_in/out
mid    -> before  under R_mid_source_in/out
------------------------------------------------
after  -> before  under composed input/output relations
```

The eventual `src/Validator.v` should only re-export these definitions after the
local checker and soundness theorem compile.  The legacy validator API should
remain unchanged.

The second step would split the storage vocabulary into two modules:

- `src/StorageWitness.v` would define target-to-source `cell_relation`, identity cell
  relation, functionality/respectfulness obligations, access-list remapping, and
  `same_instance_access_remap` for PolyInstrs.  It would also prove reflexive
  identity-remap lemmas for instructions and whole PolyLang programs.
- `src/StateObservation.v` would define an abstract `CELL_OBSERVER` interface and
  lifts a target-to-source cell relation into a state-level observation.  It
  would prove that the identity cell relation yields an observation containing
  `State.eq`.

This keeps three concerns separate:

```text
TransformContract:
  semantic postcondition shape

StorageWitness:
  which target cells represent which source cells

StateObservation:
  how states are observed through those cells
```

The first concrete feature family should be injective layout/access remapping.
The intended `src/LayoutRemapValidator.v` module would introduce a source-view
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

The intended `src/LayoutRemapValidator.v` route then exposes
`checked_array_rename_layout_remap_correct`, which composes:

```text
validate_general before source_view
array-rename access-remap checker for source_view/after
layout_source_view_refines for the rewritten target instruction semantics
```

The result would still not be a complete layout optimizer, but it would be an
actual feature-shaped checked route for the padding/array-rename subset of
layout remapping.

## Current Interface Gap

`StateTy` currently exposes `State.eq`, `State.non_alias`, and basic equivalence
laws, but it does not expose a generic per-cell observation or read relation.
That is enough for the existing schedule validators, because they end in
full-state equality.  It is not enough to define a concrete layout/projection
observation generically.

The next real storage primitive therefore needs one of two choices:

```text
1. add a small observable-state interface that can compare selected MemCell
   values under a projection, or
2. prove the first concrete storage primitive at the CState/CInstr layer, where
   read_cell/write_cell already exist.
```

The first choice is cleaner for a reusable validator framework.  The second is
useful for a narrow prototype but should not become the long-term abstraction.
The exploratory Docker skeleton follows the first choice and sketches a
concrete `CState` observer instance.

## Next Mechanization Layers

### 1. Injective Access Remapping

Target transformation class:

```text
same statement instances
changed physical access map
projection observation
```

Exploratory skeleton status: the source-view composition theorem, a concrete
C-like observer, and a padding/array-rename boolean checker have been sketched
in the Docker worktree.  The next missing piece is still the proof that a
concrete rewritten target instruction refines the source-view instruction under
the induced cell relation.  Transpose and general affine index remapping remain
future work.

### 2. Fresh Private Storage

Target transformation class:

```text
same statement instances
private or expanded storage cells
projection observation that erases private cells
```

The initial fragment should be no-live-in/no-live-out scalar expansion.  The
main proof obligation is not scheduling legality; it is freshness plus local
use-def containment.

### 3. Copy Protocol

Target transformation class:

```text
inserted copy-in / compute / copy-out instances
copy-mediated local storage
commit observation
```

This requires a target-instance role relation.  It cannot be represented by the
current `EqDom` checker, because the target has extra helper instructions.

### 4. Conflict-Safe Reuse

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

Each new validator should prove a theorem ending in `refinement_under`, then be
exported through `Validator.v` only after the local module compiles.
