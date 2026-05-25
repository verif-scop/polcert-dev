# State View Relation Design

This note is the relation-design companion to
`POLYHEDRAL_TRANSFORMATION_TAXONOMY.md`.  It answers one question:

```text
After storage-aware transformations are admitted, what replaces the current
use of State.eq as the final correctness relation?
```

The short answer is: nothing should replace `State.eq` globally.  `State.eq`
should become the identity instance of a more general state-view relation.  The
current schedule-only validator remains the identity-storage case.  Storage
transformations add explicit views that explain projection, private storage,
commit, reuse, and merge.

This is a design document.  It is not a claim that the view relation is already
mechanized.

Current mechanization status: `StateView.v` contains the first-class endpoint
view relation.  Its carrier is now the top-level `generic_state_view`, not a
functor-local record, so independently instantiated storage validators can
share the same view type through the facade.  It also exposes basic inclusion
algebra for views, so later validators can compose and weaken endpoint
relations without unfolding them.  `ViewPipeline.v` records the
common composition theorem used by the storage validators.  The pattern is:
validate the schedule/control part from `before` to a storage-neutral
`source_view`, then compose that with a feature-specific semantic
`view_refinement` from `source_view` to `after` plus finite witness obligations
for layout, private storage, copy, reuse, commit, reduction, or phase behavior.

## Problem

The current affine validation route proves a strong fragment-level fact:

```text
target fragment starts from the same state as source
target fragment executes
source fragment can execute from that same state
target final state is State.eq to source final state
```

That is right for schedule-only transformations:

```text
same logical instances
same logical accesses
different execution order or grouping
```

It is not expressive enough for storage-aware transformations:

```text
layout remapping:
  target physical cells represent source logical cells

padding:
  target contains cells that have no source value

privatization:
  target has fresh local or per-thread storage

packing:
  target uses copy-in local buffers

contraction:
  many logical values share fewer physical cells over time

overlap tiling with materialized buffers:
  target computes extra instances and stores tile-local values
```

In all these cases, a final target state can be correct without being literally
equal to the final source state.

## Design Principle

`State.eq` should be preserved as the strongest identity case:

```text
identity view:
  no target-only storage
  no layout projection
  no commit selection
  no merge
  no non-injective reuse
  all source-observable cells are represented by the same target cells
```

The general theorem should use a state relation parameter:

```coq
relational_refinement
  (state_view_rel input_view)
  (state_view_rel output_view)
  before
  after
```

The existing route is the special case:

```coq
relational_refinement
  (state_view_rel same_state_view)
  (state_view_rel identity_view)
  before
  after
```

Here `same_state_view` reflects the current validators' exact same-Coq-state
input precondition, while `identity_view` reflects the final `State.eq`
observation.  If the project later proves that the fragment semantics is stable
under `State.eq` on initial states, the input side can be strengthened to
`identity_view`.

This keeps the old proof meaningful while giving storage transformations a
place to state their intended observation.

## What a View Must Explain

A view is not only a cell projection.  It must explain what the target state
means relative to the source state.

At minimum, a view should cover these components.

### Observable Source Cells

The relation must say which source cells matter at the boundary:

```text
source_public_inputs:
  values the transformed fragment may read from the surrounding context

source_public_outputs:
  values the surrounding context may observe after the fragment

source_frame:
  source cells outside the transformed region that must be preserved
```

This is what prevents a transformation from being judged by irrelevant internal
state.

### Target Representation Cells

The view must say which target cells represent source cells:

```text
cell_repr target_cell source_cell
```

For identity scheduling, `cell_repr` is identity.  For layout remapping, it maps
physical target addresses back to logical source cells.  For contraction, it
depends on which logical value is live at the boundary.

### Target-Private Cells

Private storage cannot be modeled as ordinary erased garbage.  The view needs
separation obligations:

```text
target_private cells are fresh
target_private cells do not alias source-visible representation cells
target_private cells do not alias framed cells
target_private cells do not escape to the surrounding context
target_private final values are not source-observable
```

This is the separation meaning of privatization.  Erasing target-private cells
is sound only after these ownership and lifetime obligations are known.

### Frame Cells

The view must account for memory outside the transformed fragment:

```text
target frame cells correspond to source frame cells
frame values are preserved
target-private allocations are disjoint from frame cells
```

For the current PolIR fragment theorem, this may be implicit.  For a future C or
CompCert theorem, it must be explicit.

Current exploration status: `FramePreservationWitness.v` mechanizes the finite
write-set side of this condition.  It checks that fragment writes are contained
in an allowed-write set, and that the allowed-write set is disjoint from frame
cells.  `FramePreservationValidator.v` now packages this finite side condition
under `checked_frame_preservation_view_correct`, so a storage-specific output
view can be composed with a context-frame contract without changing the old
`State.eq` route.  The missing piece is deriving `write_cells` from concrete
instruction semantics rather than supplying it as a finite witness.

### Commit Policy

Some target writes are internal, and only selected writes become
source-observable:

```text
commit_repr target_write source_cell
```

Copy-out, overlapped tiling, array expansion, and versioning need commit policy.
The relation should state that the committed target value is the one compared to
the source value.

### Merge Policy

Reductions and reduction privatization do not select one target value.  They
combine many values:

```text
merge_repr target_partials source_value
```

The view must carry the algebraic assumptions under which the merge represents
the source value.  For integer addition this may be exact.  For floating-point
reductions it may require relaxed semantics or a non-bit-exact observation.

### Phase or Version Selector

Double buffering, rolling buffers, and versioned arrays need a boundary
selector:

```text
which physical buffer currently represents logical time t?
which target version is source-observable at exit?
```

The selector belongs in the view because the same physical cell can represent
different logical values at different phases.

## Candidate Interface

A future Coq interface could start with a deliberately abstract record:

```coq
Record state_view := {
  source_observable : cell_set;
  source_frame : cell_set;
  target_repr : target_cell -> source_cell -> Prop;
  target_private : cell_set;
  value_repr : target_value -> source_value -> Prop;
  commit_policy : commit_spec;
  merge_policy : merge_spec;
  phase_policy : phase_spec;
  separation_witness : separation_spec;
  lifetime_witness : lifetime_spec;
}.

state_view_rel :
  state_view ->
  State.t ->
  State.t ->
  Prop.
```

The exact representation should match existing PolIR abstractions, but the
logical roles should stay separate.  In particular:

```text
target_repr:
  representation of source-observable values

target_private:
  ownership and non-observability of target-only storage

source_frame:
  unchanged context state

commit_policy:
  selected target effects

merge_policy:
  many-to-one target effects
```

Do not encode all of these by overloading one cell relation.

## State.eq as a View

The identity view should be the first mechanized instance.

```coq
identity_view : state_view
```

Intended facts:

```coq
State.eq st_t st_s ->
state_view_rel identity_view st_t st_s

state_view_rel identity_view st_t st_s ->
State.eq st_t st_s
```

The second direction may require the identity view to observe all relevant cells
and carry an extensionality assumption for the chosen `State.t`.  If that is too
strong initially, the first direction is still useful: it lets current affine
validator theorems lift into the view framework.

The important discipline is:

```text
existing validators do not weaken State.eq;
new validators choose a non-identity view when their target state is not
literally equal to the source state.
```

## Separation Is Part of the Relation

Private storage is the case that forces the view design to be more than
projection.

For privatization, a bad target can appear correct if we only erase private
cells:

```text
source public A
target private tmp aliases A
final observation erases tmp
```

Erasure hides the bug unless the relation also proves:

```text
tmp is fresh
tmp is disjoint from A
tmp is not reachable by source pointers
tmp does not escape after the fragment
```

The private-storage view should therefore be closer to:

```text
target state =
  represented public source state
  separated target-private state
  preserved frame state
```

This is a separation-style invariant.  It does not require adopting separation
logic immediately, but it requires the same ownership facts.

## Relation to Instance Traces

The state view is not responsible for every proof obligation.

Some transformations change the dynamic execution trace:

```text
overlap tiling duplicates computation
copy protocols insert copy-in/copy-out instances
packing inserts pack/unpack loops
reductions merge contributions
```

Those transformations need an instance or trace witness:

```coq
Record instance_view := {
  target_to_source : target_instance -> option source_instance;
  target_role : target_instance -> role;
  exact_cover : Prop;
  internal_invisible : Prop;
  dependence_closure : Prop;
}.
```

The state view says what final target state means.  The instance view says why
the target execution produces the right represented state.

For schedule-only transformations, the instance view is a bijection and the
state view is identity.  For overlap tiling, the instance view is non-bijective,
and the state view may be identity or private-erasing depending on whether the
target materializes private buffers.

## View Constructors by Optimization

This section covers every optimization family currently intended by the
taxonomy.

### Source No-Alias Abstraction

No-alias is not a target transformation.  It is an entry condition for all
memory reasoning.

View role:

```text
source logical arrays map to disjoint memory footprints
cell_repr is sound because logical cell names are meaningful
```

Required obligations:

```text
logical names used by the polyhedral model correspond to disjoint blocks or
disjoint ranges, unless aliasing is modeled explicitly
```

This belongs to the fragment interface and the C boundary, not to a storage
rewrite view.

### Affine Scheduling, Interchange, Fusion, Fission

These are identity-view transformations.

```text
instance relation:
  bijection or exact cover

storage relation:
  identity

input view:
  identity_view

output view:
  identity_view
```

The current `State.eq` route should remain the proof target.

### Index-Set Splitting

ISS changes control structure and partitions the source domain.

```text
instance relation:
  partitioned exact cover

storage relation:
  identity

view:
  identity_view
```

The proof pressure is on exact cover, not on state observation.

### Ordinary Tiling and Diamond Tiling without Recompute

Non-overlapped tiling groups instances but still executes each source instance
once.

```text
instance relation:
  tile projection exact cover

storage relation:
  identity

view:
  identity_view
```

Diamond tiling without recomputation remains in this class.  Its tile shape is
more complex, but final observation should still be `State.eq`.

### Layout Remapping

Layout changes physical representation:

```text
source:
  A[i,j]

target:
  A_phys[f(i,j)]
```

View constructor:

```coq
layout_view cell_repr
```

Required view facts:

```text
cell_repr maps each target physical cell to the represented source logical cell
cell_repr is injective over simultaneously observable source cells
target reads and writes use cell_repr consistently
target physical addresses are in bounds
value_repr preserves the element type and value
```

Final relation:

```coq
state_view_rel (layout_view cell_repr) target_final source_final
```

Access-list remapping alone is not enough.  The instruction semantics must
actually use the rewritten address.

### Padding and Alignment

Padding is a layout view with extra target cells:

```text
target allocated domain is larger than source logical domain
padding cells do not represent source values
```

View constructor:

```coq
padding_view cell_repr padding_cells
```

Required view facts:

```text
cell_repr is injective on the source logical image
padding_cells are disjoint from represented source cells
padding_cells are not source-observable
all represented target cells are in bounds
```

The view may ignore padding cells only after proving they are outside the
observable image.

### Scratchpad or Local-Buffer Tiling

Scratchpad tiling uses local storage for a tile.

```text
copy-in:
  global source region -> target local buffer

compute:
  target reads local buffer

copy-out:
  target commits updated values, if the local buffer is written
```

View constructors:

```coq
private_buffer_view local_cells cell_repr
commit_view commit_policy
```

Required view facts:

```text
local buffer is fresh for the tile lifetime
local buffer is separated from public and frame cells
copy-in initializes every later local read
copy-out commits every source-observable update exactly once
uncommitted local writes are not observable
```

This family needs both state view and instance roles, because copy-in/copy-out
are helper instances.

### Packing and Copy Tiling

Packing copies a non-contiguous or inconvenient source region into a target
buffer.

View constructor:

```coq
packed_buffer_view packed_cells pack_map
```

Required view facts:

```text
pack_map relates packed cells to source region cells
every packed read is preceded by the corresponding pack write
packed storage is fresh and non-escaping
packed storage is erased unless there is an unpack/copy-out
copy-out, if present, is unique and ordered
```

Packing is usually an inserted-helper-instance transformation, not only a state
projection.

### Scalar Promotion

Scalar promotion simulates one memory cell by a scalar inside a region.

View constructor:

```coq
scalar_simulation_view promoted_cell scalar_name region
```

Required view facts:

```text
entry load initializes the scalar from the promoted cell
every promoted read sees the scalar value
every promoted write updates the scalar value
no interfering write to the promoted cell occurs in the region
exit store commits the scalar if the cell is live-out
```

If the scalar is a real target local, the view also needs private lifetime and
non-escape.  If the scalar is modeled as an instruction-local value, final
`State.eq` may remain possible after the exit store.

### Scalar Privatization and Scalar Expansion

Privatization replaces a shared scalar cell with private cells:

```text
source:
  tmp

target:
  tmp_private[class]
```

View constructor:

```coq
private_expansion_view private_class rho_private
```

Required view facts:

```text
private cells are fresh for their live ranges
private cells are separated from public and frame cells
each private read has a reaching same-class write
live-in private values require copy-in
live-out private values require commit/copy-out
uncommitted private cells are erased from final observation
```

OpenMP `private` clauses are only one backend way to express this idea.  The
view should be polyhedral and semantic, not tied to OpenMP syntax.

### Reduction Privatization

Reduction privatization creates private partial accumulators and merges them.

View constructor:

```coq
reduction_merge_view private_accumulators merge_op
```

Required view facts:

```text
iteration chunks exactly cover the source reduction domain
private accumulators are fresh and separated
each contribution is included once
merge_op represents the source reduction semantics
```

For integer addition, the merge can be exact.  For floating point, the view must
state whether it preserves bit-exact behavior or uses relaxed reduction
semantics.

### Array Expansion and Versioning

Expansion creates extra physical versions:

```text
source:
  X[i]

target:
  X_version[v,i]
```

View constructor:

```coq
version_view version_selector commit_policy
```

Required view facts:

```text
each target read selects the version produced by the intended source write
extra versions project to one source logical value
the source-observable version is committed exactly once
unselected versions are private or dead at the boundary
```

This is the positive-storage counterpart of contraction.

### Array Contraction and Rolling Buffers

Contraction uses fewer physical cells than logical values:

```text
source logical value:
  A[t,i]

target physical cell:
  A_phys[t mod k, i]
```

View constructor:

```coq
reuse_view rho live_selector conflict
```

Required view facts:

```text
rho maps logical values to physical cells
if conflict(v1, v2), then rho(v1) != rho(v2)
live_selector identifies which logical value a physical cell represents at the
boundary
source-observable final values are selected from the correct physical cells
```

This view is intentionally not injective.  Its safety comes from conflict and
lifetime reasoning.

### Inter-Array Reuse

Inter-array reuse lets different logical arrays share one physical buffer over
time.

View constructor:

```coq
cross_array_reuse_view rho lifetime_intervals
```

Required view facts:

```text
logical arrays sharing a physical cell have non-overlapping live intervals
type, size, and alignment are compatible
all accesses in each lifetime interval use the intended interpretation
the boundary selector maps the buffer back to the live source array
```

This is contraction across array names.

### Double Buffering and Ping-Pong Buffers

Double buffering is phase-structured reuse.

View constructor:

```coq
phase_view phase_selector rho
```

Required view facts:

```text
the current phase identifies which physical buffer represents each logical value
the next buffer is not read before it is filled
the current buffer is not overwritten while still live
swap or phase update changes the physical-to-logical projection as claimed
```

This is more than `t mod 2`: the phase relation must justify visibility and
overwrite safety.

Current exploration status: `PhaseSeparationWitness.v` mechanizes a finite
phase protocol:

```text
check_phase_protocolb entry_live steps = true
```

implies each phase reads only entry-live cells, writes are disjoint from
entry-live cells, and next-live cells come from either entry-live cells or phase
writes.  `PhaseValueWitness.check_phase_value_protocolb_sound` adds the
snapshot value-flow side: read cells have entry values, and each next-live
value is either produced by the phase write for that cell or inherited from
the entry snapshot.  `PhaseProjectionWitness.check_phase_projectionb_sound`
adds the final-boundary projection side: source live-outs are covered exactly
once by a finite map into final phase-live cells, and the target cells are
duplicate-free.  `PhaseProjectionWitness.check_phase_projection_valueb_sound`
checks the optional boundary values for that map.  The
same module now exposes the projection map as
`phase_projection_cell_relation` and names the exact-cover consequences needed
by a later state-observation proof: live-outs are mapped, mapped sources are
live-outs, and mapped targets are final-live.
`PhaseValueWitness.phase_value_protocol_final_snapshot` and
`check_phase_value_protocolb_final_snapshot` make the intermediate final
boundary explicit: once the value protocol is checked, the final value snapshot
matches `phase_protocol_final_live`.  The projection witness can then be read
as a projection out of that checked final physical snapshot.
The
`PhaseSeparationValidator.checked_phase_*` theorem family packages these into
the common composition theorem.
`checked_phase_projection_compatible_value_view_correct` adds the final
projection storage side condition: each logical source live-out and final
physical phase cell pair must have compatible size/alignment specs.  The
derivation of the supplied swap/phase projection and storage specs from
concrete code remains explicit.

### Overlapped Tiling

Overlap tiling duplicates computation.

There are two cases.

Case 1: no materialized private state at the boundary.

```text
instance relation:
  duplicated/internal target instances project to source instances

state view:
  identity_view may still be enough
```

Case 2: materialized tile-private buffers.

```text
instance relation:
  duplicated/internal target instances

state view:
  private_buffer_view plus commit_view
```

Required facts:

```text
every target computation projects to a valid source instance
internal halo computations are invisible or tile-private
committed target instances exactly cover source live-out instances
tile-private buffers are fresh and separated
parallel commits are disjoint or ordered
```

Overlap shows why instance relation and state view must be separate.  Extra
execution alone does not force a non-identity state view, but materialized
private storage does.

### Memory-Space Movement

Memory-space movement covers global/local/shared/register/distributed movement.
The current branch is C-like and CPU-oriented, so this is a boundary case rather
than an immediate implementation target.

View constructor:

```coq
memory_space_view transfer_map visibility_policy
```

Required facts:

```text
transfer regions contain the required source values
reads occur only after the transferred value is visible
private or local spaces are separated from public memory
barriers or synchronization justify visibility
copy-out commits source-observable updates
```

For GPU or distributed settings, visibility and ownership become first-class
parts of the view.

## Summary Matrix

| Transformation | Input view | Output view | Extra instance witness? | Key non-equality reason |
| --- | --- | --- | --- | --- |
| Source no-alias abstraction | interface assumption | interface assumption | no | not a transform |
| Affine scheduling / interchange | identity | identity | bijection/exact cover | none |
| Index-set splitting | identity | identity | partition exact cover | none |
| Ordinary tiling | identity | identity | tile exact cover | none |
| Diamond tiling without recompute | identity | identity | tile exact cover | none |
| Layout remapping | layout or identity at entry | layout projection | no, if same instances | physical cells differ |
| Padding/alignment | padding/layout | padding/layout | no | extra target cells |
| Scratchpad/local buffer tiling | identity or layout | commit plus erase-private | yes | local buffers and helper copies |
| Packing/copy tiling | identity or layout | erase-private or commit | yes | packed buffer |
| Scalar promotion | identity | identity after exit store, or erase scalar | no | local scalar may be target-only |
| Scalar privatization/expansion | identity | erase-private or projection | no | private cells |
| Reduction privatization | identity | merge view | yes | private partials and merge |
| Array expansion/versioning | identity | version/commit view | no | extra versions |
| Array contraction/rolling buffer | phase/reuse view | reuse projection | no | non-injective physical cells |
| Inter-array reuse | reuse view | reuse projection | no | shared buffer across lifetimes |
| Double buffering | phase view | phase view | no | changing physical-to-logical phase |
| Overlapped tiling without private buffers | identity | identity | yes | extra internal instances only |
| Overlapped tiling with private buffers | identity | erase-private plus commit | yes | tile-private storage |
| Memory-space movement | transfer view | visibility/commit view | yes | different memory spaces |

## Per-Transformation Support Plan

This section spells out what "support" should mean for each transformation.  A
transformation is supported only when the proof has all three relevant parts:

```text
view support:
  the endpoint relation says what target storage represents

witness support:
  the checker input describes the needed instance, access, lifetime, copy,
  conflict, phase, or merge facts

semantic support:
  the local soundness theorem proves a relational_refinement endpoint that can
  compose with other passes
```

Some rows need only identity view support.  Others need new view constructors
and a trace witness.  The list below is deliberately complete for the current
taxonomy.

### Source No-Alias Abstraction

Support goal:

```text
make the source memory abstraction explicit before any transformation proof
uses logical cells
```

Required design pieces:

```text
fragment interface:
  maps source array names to logical memory objects

no-alias witness:
  proves distinct logical objects have disjoint concrete footprints, or records
  explicit aliasing when disjointness is not true

view role:
  identity_view assumes this abstraction is already sound
```

Theorem shape:

```coq
no_alias_sound interface concrete_state ->
state_view_rel identity_view polir_state polir_state
```

Current exploration status: `SourceNoAliasWitness.v` mechanizes the finite
footprint side of this precondition.  `check_source_no_aliasb footprints = true`
proves duplicate-free logical object ids, duplicate-free per-object footprints,
and pairwise disjoint footprints.  This is deliberately not a transformation
validator; it is the finite assumption that makes later logical-cell reasoning
sound.

This is a precondition, not an optimizer.  It should be discharged by the
front-end or boundary layer.

### Affine Scheduling, Interchange, Fusion, and Fission

Support goal:

```text
preserve current theorem shape while expressing it as identity-view refinement
```

Required design pieces:

```text
instance witness:
  bijection or exact cover of source instances

storage witness:
  identity access relation

view:
  same_state_view at entry for the current theorem
  identity_view at exit
```

Theorem shape:

```coq
validate_affine before after = true ->
view_refinement same_state_view identity_view before after
```

This should be a wrapper around the existing validator, not a rewrite of the
existing affine proof.  A stronger `identity_view -> identity_view` theorem
requires a separate proof that the fragment semantics is stable under
`State.eq`-related initial states.

### Index-Set Splitting

Support goal:

```text
validate source-domain partitioning without changing storage observation
```

Required design pieces:

```text
partition witness:
  target subdomains are disjoint
  target subdomains exactly cover source domain
  every target statement projects to the intended source statement

view:
  same_state_view at entry for the current theorem
  identity_view at exit
```

Theorem shape:

```coq
validate_iss_split witness before after = true ->
view_refinement same_state_view identity_view before after
```

No new state relation is needed.  The proof pressure is on exact cover and
guard/domain reasoning.

### Ordinary Tiling and Diamond Tiling without Recompute

Support goal:

```text
validate tiling as grouped scheduling when each source instance executes once
```

Required design pieces:

```text
tile witness:
  tile loops project to source iteration points
  every source point is covered exactly once
  dependences are preserved by the tile schedule

view:
  same_state_view at entry for the current theorem
  identity_view at exit
```

Theorem shape:

```coq
validate_tiling witness before after = true ->
view_refinement same_state_view identity_view before after
```

Diamond tiling enters here only when it does not introduce recomputation or
target-private storage.  Overlapped or redundant diamond-style execution belongs
to the overlap plan below.

### Layout Remapping

Support goal:

```text
prove that target physical accesses represent source logical accesses
```

Required design pieces:

```text
layout view:
  layout_view cell_repr

access witness:
  target access functions are related to source access functions by cell_repr

instruction witness:
  target instruction semantics actually read and write the rewritten target
  cells, not merely matching access-list annotations

boundary facts:
  physical addresses are in bounds
  element types are compatible
```

Theorem shape:

```coq
validate_layout_access witness source_view after = true ->
instr_layout_refines witness source_view after ->
view_refinement
  layout_input_view
  (layout_view cell_repr)
  source_view
  after
```

The current branch sketches the access-witness side.  Full support requires the
instruction-level simulation theorem.

### Padding and Alignment

Support goal:

```text
support layout maps into a larger physical domain
```

Required design pieces:

```text
padding view:
  padding_view cell_repr padding_cells

address witness:
  cell_repr is injective over source-observable cells
  padding cells are outside the source image
  all represented cells are within allocation bounds

observation:
  padding cells are ignored because they represent no source value
```

Theorem shape:

```coq
validate_padding witness before after = true ->
view_refinement input_view (padding_view cell_repr padding_cells) before after
```

Current exploration status: `PaddingLayoutWitness.v` mechanizes the finite
boundary obligations for padded layouts: the source side of the map is
functional, the target image is injective and allocated, and padding cells are
duplicate-free, allocated, and disjoint from that target image.
`LayoutValueWitness.check_layout_valueb_sound` adds boundary value evidence:
entries must align with the source-to-target layout map, and each represented
source value must equal the corresponding target physical value.
`PaddingLayoutValidator.checked_padding_layout_view_correct` packages those
facts as another `view_refinement` wrapper.
`checked_padding_layout_access_view_correct` additionally returns the
`LayoutWitness` access-function remap fact for array-renaming layouts, and
`checked_padding_layout_access_value_view_correct` combines that with the
boundary value obligations.  The corresponding permutation variants
`checked_padding_layout_permutation_access_view_correct` and
`checked_padding_layout_permutation_access_value_view_correct` prove the same
access-remap shape for finite index permutations, covering transpose-style
rewrites such as `A[i][j] -> A_t[j][i]`.  The affine variants
`checked_padding_layout_affine_access_view_correct` and
`checked_padding_layout_affine_access_value_view_correct` prove the same shape
when the target access function is the affine composition of a declared layout
map with the source access function, covering linearized layouts such as
`A[i][j] -> A_lin[i * stride + j]`.  The unified
`checked_padding_layout_declared_access_view_correct` and
`checked_padding_layout_declared_access_value_view_correct` wrappers expose
the same proof shape through one declared-layout relation whose cases are
same-index, finite permutation, and affine composition.
`checked_padding_layout_declared_access_compatible_value_view_correct` adds the
storage-compatibility layer to the same wrapper: every mapped logical cell must
have a finite storage spec, every mapped physical layout cell must have a
finite storage spec, and the paired specs must agree on size and alignment.
The proof that concrete target instruction semantics realizes those rewritten
accesses, values, and storage specs remains explicit.

Padding support is a special case of layout support plus a proof that extra
cells are unobservable.

### Scratchpad or Local-Buffer Tiling

Support goal:

```text
validate explicit local buffers used inside a tile
```

Required design pieces:

```text
private-buffer view:
  private_buffer_view local_cells cell_repr

commit view:
  commit_view copy_out_policy, when local writes update source-observable values

trace witness:
  copy-in, compute, and copy-out roles

copy witness:
  every local read is covered by a prior copy-in or local write
  every source-observable local update is copied out exactly once

separation witness:
  local buffer is fresh for the tile lifetime
```

Theorem shape:

```coq
validate_scratchpad witness before after = true ->
view_refinement input_view output_commit_or_erase_view before after
```

Current exploration status: `CopyProtocolWitness.v` mechanizes the finite
copy bookkeeping part:

```text
check_copy_protocol_wfb trace = true
```

implies local reads are covered and committed target cells are duplicate-free.
`CopyCommitWitness.check_copy_commit_coverb_sound` adds exact commit coverage:
the copy-out targets in the trace must cover the expected observable target
cells and no others.
`CopyInstanceWitness.check_copy_instance_traceb_sound` connects this copy trace
to projected helper instances: copy-in/local events must be internal
instances, and copy-out events must be commit-role instances.  This is the
finite witness that lets instance projection and copy protocol speak about the
same helper trace.
`CopyMappingWitness.check_copy_mappingb_sound` adds the local remapping layer:
a finite public-to-local map is injective on both sides, and copy-in, local
read/write, and copy-out events must use that declared map consistently.
`CopyProtocolValueWitness.v` adds a value-flow layer for copy protocols:
copy-in transfers source value to local value, local reads observe the current
local value, local writes update it, and copy-out commits it to the target.
`CopyProtocolValidator.checked_copy_protocol_value_view_correct`,
`checked_copy_protocol_mapping_view_correct`, and
`checked_copy_protocol_mapping_value_view_correct` package these facts into the
common composition theorem under an explicit copy-specific semantic refinement.
`checked_copy_protocol_commit_mapping_value_view_correct` additionally packages
copy-out exact cover with remapping and value-flow evidence, giving a generic
copy-mediated update theorem that does not require the scratchpad-specific
instance/private-storage wrapper.
`ScratchpadCopyValidator.checked_scratchpad_copy_view_correct`
combines this copy witness with instance projection and local-buffer
separation, which is closer to a scratchpad/packing transformation.  It still
does not derive the event trace, value trace, or helper-instance ordering from
concrete target instruction semantics; that remains the semantic refinement
obligation.
`checked_scratchpad_copy_commit_view_correct` additionally packages the
copy-out exact-cover obligation needed for update-style scratchpad passes.
`checked_scratchpad_copy_instance_view_correct` and
`checked_scratchpad_copy_instance_commit_view_correct` additionally package the
copy-instance role-alignment obligation.
`checked_scratchpad_copy_full_view_correct` packages the larger scratchpad
contract: exact copy-out cover, helper-instance roles, remapping consistency,
value-flow simulation, and local-buffer separation are returned together under
the common view theorem.
`checked_scratchpad_copy_compatible_full_view_correct` adds the storage-spec
side condition to the same public-to-local remapping: each local buffer cell
must be size/alignment-compatible with the public cell it temporarily
represents.

This support cannot be reduced to schedule legality.  The copy protocol is part
of correctness.

### Packing and Copy Tiling

Support goal:

```text
validate packed buffers that represent a source region for faster access
```

Required design pieces:

```text
packed-buffer view:
  packed_buffer_view packed_cells pack_map

trace witness:
  pack helper instances and unpack/copy-out helper instances, if present

copy witness:
  pack_map is filled before each packed use
  packed cells are read consistently with pack_map
  unpack/copy-out, if present, commits the intended source cells

separation witness:
  packed buffer is fresh and non-escaping
```

Theorem shape:

```coq
validate_packing witness before after = true ->
view_refinement input_view output_view before after
```

Read-only packing usually ends with erase-private.  Packing that updates values
needs commit view.

### Scalar Promotion

Support goal:

```text
validate replacing repeated memory access to one cell by a scalar temporary
inside a region
```

Required design pieces:

```text
scalar simulation witness:
  entry load
  scalar operations that simulate reads and writes
  exit store when promoted cell is live-out

interference witness:
  no write to the promoted cell bypasses the scalar

view:
  identity_view if exit store restores the observable cell
  erase-private view if the scalar is modeled as target-local state
```

Theorem shape:

```coq
validate_scalar_promotion witness before after = true ->
view_refinement identity_view output_view before after
```

Current exploration status: `ScalarPromotionWitness.v` mechanizes the finite
local protocol for one promoted source cell and one scalar cell.  It checks
load-before-use, rejects ordinary writes that bypass the scalar and target the
promoted source cell, and requires a final store when the promoted cell is
live-out.  `ScalarPromotionValueWitness.v` adds a value-flow witness over the
same event stream: load/source values must match, reads observe the current
scalar, writes update it, and store-back commits the current scalar value.
`ScalarPromotionValidator.checked_scalar_promotion_value_view_correct` combines
the storage protocol, value-flow witness, and private separation for the scalar
cell, while the derivation of that value trace from concrete expression
semantics remains explicit.
`checked_scalar_promotion_compatible_value_view_correct` adds the finite
storage-compatibility side condition for the source/scalar pair, matching the
same size/alignment witness used by reuse and version-selection wrappers.

This is local storage refinement, not a global layout transformation.

### Scalar Privatization and Scalar Expansion

Support goal:

```text
validate replacing one shared scalar cell by private or per-instance cells
```

Required design pieces:

```text
private expansion view:
  private_expansion_view private_class rho_private

use-def witness:
  every private read has a reaching same-class definition

freshness witness:
  simultaneously live private classes map to disjoint physical cells

boundary witness:
  live-in requires copy-in
  live-out requires commit/copy-out
  uncommitted private cells are erased
```

Theorem shape:

```coq
validate_scalar_private witness before after = true ->
view_refinement input_view private_output_view before after
```

This support should be semantic.  OpenMP `private` is only one possible
backend notation for the same idea.

### Reduction Privatization

Support goal:

```text
validate private partial accumulators and final merge
```

Required design pieces:

```text
merge view:
  reduction_merge_view private_accumulators merge_op

partition witness:
  iteration chunks are disjoint and exactly cover the source reduction domain

private witness:
  private accumulators are fresh and initialized correctly

algebra witness:
  merge_op implements the source reduction semantics
```

Theorem shape:

```coq
validate_reduction_private witness before after = true ->
view_refinement identity_view (reduction_merge_view accs merge_op) before after
```

Current exploration status: `ReductionMergeWitness.v` mechanizes the finite
bookkeeping part:

```text
check_reduction_mergeb source_domain chunks partial_accumulators merge_order = true
```

implies chunks exactly cover the source reduction domain, private accumulators
are duplicate-free, and the merge order covers exactly those private
accumulators.  The same module now names the derived exact-cover facts used by
later semantic proofs: source instances are covered iff they are in the chunk
domain, merge-order cells are private iff they are private accumulators, and
both covered instances and merge order are duplicate-free.
`ReductionMergeValueWitness.v` adds the fold-value side: it
looks up supplied values for merge-order accumulators and checks that folding
them with a supplied merge operator yields the claimed final value.
`ReductionAlgebraWitness.v` adds a finite-carrier law checker: the associative
variant checks closure, associativity, and two-sided identity on the carrier;
the commutative variant additionally checks commutativity.
`ReductionMergeValidator.checked_reduction_merge_value_view_correct` packages
these facts into the common composition theorem.
`checked_reduction_merge_associative_view_correct` and
`checked_reduction_merge_commutative_view_correct` package the finite-carrier
law witnesses.  The newer
`checked_reduction_merge_associative_value_view_correct` and
`checked_reduction_merge_commutative_value_view_correct` wrappers package the
bookkeeping witness, accumulator-value fold witness, and finite-carrier law in
one view theorem.
`checked_reduction_merge_commutative_compatible_value_view_correct` adds the
storage view side condition for privatized reductions: the public reduction
cell and each private partial accumulator must have compatible finite storage
specs.  The remaining semantic question is how those finite-carrier facts and
storage specs connect to the concrete source language semantics.

For floating point, the view must say whether it preserves bit-exact results or
uses relaxed reduction semantics.

### Array Expansion and Versioning

Support goal:

```text
validate more physical versions than source logical cells
```

Required design pieces:

```text
version view:
  version_view version_selector commit_policy

version witness:
  each target read selects the version produced by the intended source write

commit witness:
  the source-observable version is committed exactly once

erasure witness:
  unselected versions are private or dead at the boundary
```

Theorem shape:

```coq
validate_array_expansion witness before after = true ->
view_refinement input_view (version_view selector commit) before after
```

Current exploration status: `VersionCommitWitness.v` mechanizes the finite
commit-selection part:

```text
check_version_commitb source_liveouts mapping = true
```

implies every source live-out is selected exactly once and selected target
versions are duplicate-free.  The current witness exposes the derived facts
needed by a later semantic proof: every live-out has a selected version,
every selected source is a live-out, every selected version belongs to the
version image, and both source and version images are duplicate-free.
`VersionCommitValueWitness.v` adds selected source/version value evidence
aligned with the mapping and proves that selected version values equal
represented source values.
`VersionCommitValidator.checked_version_commit_value_view_correct` packages
both witnesses into the common composition theorem under the remaining
semantic obligation that concrete target writes produce the supplied value
evidence.
`checked_version_commit_compatible_value_view_correct` additionally packages
storage compatibility for selected source/version pairs, so array expansion can
state in one theorem that selected versions cover live-outs, are unique,
contain the represented boundary values, and have compatible size/alignment
specs.

This is useful as a counterpart to contraction and as a generalization of scalar
expansion.

### Array Contraction and Rolling Buffers

Support goal:

```text
validate non-injective reuse of physical cells
```

Required design pieces:

```text
reuse view:
  reuse_view rho live_selector conflict

conflict witness:
  if conflict(v1, v2), then rho(v1) != rho(v2)

lifetime witness:
  conflict over-approximates values that may be live together

boundary selector:
  maps each source-observable logical value to the physical cell containing it
  at exit
```

Theorem shape:

```coq
validate_contraction witness before after = true ->
view_refinement input_view (reuse_view rho selector conflict) before after
```

Current exploration status: `ReuseConflictWitness.v` mechanizes the finite
conflict check:

```text
check_conflict_safe_reuseb mapping conflicts = true
```

implies the reuse map has duplicate-free logical keys and every supplied
conflict pair maps to distinct physical cells.  This is the core
non-injective-storage safety condition.  `LifetimeConflictWitness.v` now checks
one finite live-range layer above that: explicit live intervals must be
well-formed, logical cells must be unique in the witness, and every overlapping
pair must appear in the conflict relation modulo pair order.  Combining the
live-range cover checker with conflict-safe reuse proves that all live-overlap
pairs are physically separated.  This still does not derive the intervals from
the schedule and access semantics.  `ReuseValueWitness.check_reuse_valueb_sound`
adds the boundary equality witness: finite value entries must be aligned with
the logical-to-physical selector and each physical boundary value must equal
the logical value it represents.  `ReuseStateView.reuse_view` now defines the
boundary projection view from a logical-to-physical selector.  The more precise
`ReuseStateView.reuse_boundary_cell_view` restricts that relation to declared
source live-outs and uses their image as the target-public footprint.  Its
finite premise is `ReuseConflictWitness.check_reuse_boundaryb_sound`: every
source-observable live-out is covered by the reuse map.
`ReuseConflictValidator.checked_*reuse*_view_correct` composes the finite
checkers under the remaining semantic refinement.
The contraction-facing wrappers
`checked_compatible_live_conflict_reuse_view_correct` and
`checked_compatible_live_conflict_reuse_value_view_correct` now package the
full finite side condition expected by a rolling-buffer proof: live-overlap
cover, conflict-safe physical separation, storage compatibility, and optional
boundary value equality.  They still do not derive the live intervals or
boundary observations from concrete code.

This view must not require injectivity.  Safety comes from conflict/lifetime
separation.

### Inter-Array Reuse

Support goal:

```text
validate sharing one physical buffer across different logical arrays over time
```

Required design pieces:

```text
cross-array reuse view:
  cross_array_reuse_view rho lifetime_intervals

lifetime witness:
  arrays mapped to the same physical cells are not live at the same time

compatibility witness:
  type, size, and alignment are compatible

access witness:
  each lifetime interval interprets the shared buffer as the intended source
  logical array
```

Theorem shape:

```coq
validate_inter_array_reuse witness before after = true ->
view_refinement input_view (cross_array_reuse_view rho live) before after
```

Current exploration status: `InterArrayReuseWitness.v` treats this as a
composed reuse obligation rather than a new primitive.  It packages explicit
live intervals, conflict-safe logical-to-physical reuse, and storage
compatibility.  The derived facts expose the property the view needs at the
boundary of a shared buffer: mapped live-overlapping logical cells have
distinct physical cells, and two distinct logical cells sharing one physical
cell therefore cannot live-overlap.  `InterArrayReuseValidator.v` now packages
that witness under `checked_inter_array_reuse_view_correct`, so the composed
reuse facts can participate in the same source-view pipeline theorem as layout,
version commit, and conflict-safe reuse.  This is still a reuse view with array
names included in the lifetime relation; deriving the live intervals and
rewritten accesses from concrete code remains outside this finite witness.

### Double Buffering and Ping-Pong Buffers

Support goal:

```text
validate phase-structured reuse of two or more buffers
```

Required design pieces:

```text
phase view:
  phase_view phase_selector rho

phase witness:
  reads occur only after the relevant buffer is filled
  live buffers are not overwritten
  swap or phase update changes the projection as claimed

reuse witness:
  physical cells reused across phases are not simultaneously live
```

Theorem shape:

```coq
validate_double_buffer witness before after = true ->
view_refinement input_phase_view output_phase_view before after
```

The input and output views may differ because the phase selector changes.

### Overlapped Tiling

Support goal:

```text
validate duplicate halo/internal computation with unique source-visible commit
```

Required design pieces:

```text
instance witness:
  target computations project to source instances
  roles classify internal and commit instances
  commit instances exactly cover source live-out instances

closure witness:
  each committed computation has required inputs through local recomputation or
  legal external reads

view:
  identity_view if no target-private storage remains observable
  private_buffer_view plus commit_view if tile-local buffers are materialized
```

Theorem shapes:

```coq
validate_overlap_no_private witness before after = true ->
view_refinement same_state_view identity_view before after

validate_overlap_private witness before after = true ->
view_refinement same_state_view erase_private_commit_view before after
```

Current exploration status: `InstanceProjectionWitness.v` mechanizes the finite
role/projection part:

```text
check_instance_projectionb source_domain source_liveouts targets = true
```

implies every target projection is in the source domain and commit-role target
instances form an exact, duplicate-free cover of source live-outs.
The same module now names the derived facts needed by later semantic proofs:
live-outs are committed, commits are live-outs, commits are duplicate-free,
commits project to source-domain instances, and therefore live-outs are in the
source domain.
`OverlapClosureWitness.v` mechanizes the next finite obligation:

```text
check_overlap_closureb tiles = true
check_overlap_ordered_closureb tiles = true
```

implies that each listed tile dependency has a consumer computed in the same
tile and a producer supplied either by a tile live-in or by a computation in
the same tile.  The ordered variant additionally implies that a tile-produced
dependency appears before its consumer in the tile trace.  This is a closure
witness over finite, already-derived dependencies and trace order; it does not
yet derive the dependency set from schedule/access semantics.
`InstanceProjectionValidator.checked_instance_projection_view_correct` packages
the witness into the shared `view_refinement` composition shape.
`OverlapTilingValidator.checked_overlap_no_private_view_correct` specializes
the route to duplicated/internal computation with unique source-visible commit.
`OverlapTilingValidator.checked_overlap_private_view_correct` adds the
tile-private separation witness for materialized halo/local buffers.
`OverlapTilingValidator.checked_overlap_closure_view_correct` and
`checked_overlap_private_closure_view_correct` additionally package the finite
tile-local closure witness.  `checked_overlap_ordered_closure_view_correct` and
`checked_overlap_private_ordered_closure_view_correct` package the stronger
producer-order variant.  Value equivalence of recomputed halo/internal
instances is still a separate semantic refinement obligation.

Overlap support requires keeping instance duplication separate from state
projection.

### Memory-Space Movement

Support goal:

```text
validate moving values across global, local, shared, register, or distributed
memory spaces
```

Required design pieces:

```text
memory-space view:
  memory_space_view transfer_map visibility_policy

transfer witness:
  copied region contains the required source values
  reads occur after visibility is established
  writes are committed back when source-observable

ownership witness:
  local/shared/register storage is separated from public memory

synchronization witness:
  barriers or communication protocol justify visibility and race freedom
```

Theorem shape:

```coq
validate_memory_space_move witness before after = true ->
view_refinement input_transfer_view output_visibility_view before after
```

This is not an immediate CPU PolIR target, but the view framework should not
rule it out.

## Support Coverage Checklist

Before calling a transformation supported, answer these questions.

```text
1. What is the input view?
2. What is the output view?
3. Does State.eq suffice, or is projection/erasure/commit/merge/reuse needed?
4. Does the target add, duplicate, or merge instances?
5. Which witness proves that target accesses represent source values?
6. Which witness proves freshness, separation, lifetime, or no-alias facts?
7. Which theorem proves view_refinement?
8. Does the theorem compose with earlier and later passes?
9. Which C/CompCert boundary obligations remain outside this fragment proof?
```

The answer should be written before implementing the checker.  This prevents
feature-specific relations from accumulating without a common semantic endpoint.

## Composition

Views must compose because end-to-end validation composes transformations:

```text
target after pass 2
  relates to
intermediate after pass 1
  relates to
source before pass 1
```

The already proposed semantic shape is:

```coq
relational_refinement R_tm0 R_tm1 mid after ->
relational_refinement R_ms0 R_ms1 before mid ->
relational_refinement
  (compose_state_relation R_tm0 R_ms0)
  (compose_state_relation R_tm1 R_ms1)
  before after
```

For views, the corresponding design obligation is:

```text
compose_view view_target_mid view_mid_source
```

`StateView.view_refinement_compose` expands this to
`compose_state_relation` over `state_view_rel`.  The packaged theorem
`StateView.checked_view_transform_family_pair_compose` is the current
end-to-end hook for two checked pass families: once each pass returns a
`view_refinement`, the composed theorem uses only `compose_view`, not any
feature-specific relation.

The access-witness layer now has the matching storage-side theorem.  A
target-to-mid access remap and a mid-to-source access remap compose via:

```coq
StorageWitness.pprog_same_instance_access_remap_compose
```

The resulting relation is `compose_cell_relation target_mid mid_source`, whose
witness is the intermediate `MemCell`.  This is important for multi-pass
storage pipelines: the final state-view relation and the instruction-level
access relation can be composed along the same intermediate program boundary.

View composition should also support simplification:

```text
layout ; identity = layout
identity ; private-erasure = private-erasure
phase ; phase-update = updated phase view
commit ; identity = commit
```

These simplifications are useful for readable end-to-end theorems, but the
semantic composition theorem should not depend on them.

## Mechanization Plan

The first Coq step should avoid committing to all concrete fields at once.

### Step 1: Abstract View Interface

Introduce a module that treats views abstractly:

```coq
Parameter view : Type.
Parameter state_view_rel : view -> State.t -> State.t -> Prop.
Parameter identity_view : view.
Parameter same_state_view : view.
Parameter identity_view_contains_state_eq :
  forall st_t st_s,
    State.eq st_t st_s ->
    state_view_rel identity_view st_t st_s.
Parameter same_state_view_included_identity_view :
  forall st_t st_s,
    state_view_rel same_state_view st_t st_s ->
    state_view_rel identity_view st_t st_s.
```

This is enough to restate the current affine validators as
`same_state_view -> identity_view` validators.

### Step 2: View Relation Packaging

Connect views to `relational_refinement`:

```coq
Definition view_refinement vin vout before after :=
  relational_refinement
    (state_view_rel vin)
    (state_view_rel vout)
    before
    after.
```

This keeps the theorem endpoint uniform.

### Step 3: Concrete Identity View

Prove that the current final-state equality route is the identity view instance,
and that the current same-Coq-state input precondition is represented by
`same_state_view`.  Do not change existing validator proofs.  Add wrappers.

### Step 4: Layout View

Mechanize the first non-identity view:

```text
layout_view cell_repr
```

This should reuse the existing observer idea, but it must be framed as one
instance of state views rather than a separate `layout_state_rel`.

Current exploration status: `StateObservation.related_cells_view` provides the
observer-backed cell relation view, and `LayoutRemapValidator.layout_view`
exposes the layout case through `view_refinement`.  The view is now
compositional at the observation level:

```coq
related_cells_view target_mid ;
related_cells_view mid_source
  <= related_cells_view (compose_cell_relation target_mid mid_source)
```

The inclusion direction is deliberate.  If there exists an intermediate state
that satisfies both cell observations, then every target cell can be observed
as the source cell reached through the intermediate cell.  The reverse
direction would require constructing an intermediate state from only the
composed endpoint observation, which is not justified by the current state
interface.

### Step 5: Private-Erasure View

Mechanize:

```text
private_view public_repr private_cells separation
```

This is the first view that forces separation obligations.

Current exploration status: `StateObservation.cell_view` records the public
source/target footprint of a cell relation, and
`PrivateStorageValidator.private_erasure_view` uses it to state the theorem
shape for target-private storage.  `PrivateStorageWitness.hidden_identity_cell_view`
and `mem_cells_subsetb` provide the first checked sub-obligation: finite
private cells are contained in the hidden set, hence outside the public
identity relation.  `mem_cells_nodupb` and
`check_private_use_def_traceb` additionally cover two local witness facts:
distinct private cells and concrete-cell read-after-write coverage.
`check_private_access_use_def_traceb` lifts the same idea to access functions
and proves that every dynamic point instantiates to a valid private cell trace.
`check_private_separationb` captures the reusable separation side condition:
private cells are duplicate-free and disjoint from public/frame cells.
`PrivateBoundaryWitness.check_private_boundaryb_sound` adds the boundary-copy
side condition: required public live-ins are covered by copy-in pairs, required
public live-outs are covered by copy-out pairs, boundary pairs use declared
private cells, and public copy-out destinations are unique.
`check_private_boundary_private_uniqueb_sound` adds the optional private-side
uniqueness condition: copy-in and copy-out boundary pairs cannot reuse the same
private cell on their private side.  This intentionally does not require public
live-ins to be unique, because broadcasting one public live-in to many private
cells is a normal privatization pattern.
`check_private_boundary_valueb_sound` adds aligned boundary value evidence:
copy-in and copy-out entries must match their boundary pairs, and public/private
values must be equal at those boundary points.
The current contract still needs an abstract semantic refinement obligation,
but `PrivateStorageValidator.checked_access_local_private_expansion_view_correct`
now returns these local facts and composes the view theorem under that
remaining semantic assumption.  `checked_boundary_private_expansion_view_correct`
also returns the boundary-copy facts, and
`checked_boundary_private_unique_expansion_view_correct` returns the private
boundary uniqueness facts.
`checked_boundary_private_value_expansion_view_correct` returns the boundary
value facts.
`checked_boundary_private_unique_value_expansion_view_correct` combines the
unique-private-boundary and boundary-value layers in one observer-backed
private-erasure theorem.
`checked_boundary_private_unique_compatible_value_expansion_view_correct` adds
boundary storage compatibility for the same copy-in/copy-out pairs: public and
private cells must both have finite storage specs, and paired specs must agree
on size and alignment.  Non-escape, deriving those specs from C types, and full
instruction-derived value-simulation checkers are future work.

`StateObservation.compose_cell_view` now composes these public views when the
two passes agree on the shared intermediate public cells:

```text
target_mid.cv_source_observable mid
  <-> mid_source.cv_target_observable mid
```

This is important for keeping the design principled.  Private-erasure,
layout-remapping, reuse-boundary, and copy-protocol views all become instances
of one endpoint relation discipline, while pass-specific validators only
justify their own witness obligations.  The composed public view is meaningful
only when the intermediate cells hidden by the first pass are not required as
public target cells by the second pass, and vice versa.

`StorageBoundaryView.v` now factors out one common endpoint instance of that
discipline.  It treats a finite logical-to-physical boundary selector as the
source of both the observer-backed `cell_view` and the storage-compatibility
obligation.  This is the intended non-adhoc path for passes whose final public
state is a projected live-out boundary: layout live-outs, phase/double-buffer
projection, contraction/inter-array reuse, and copy-out/packing can all use the
same final relation shape while keeping their feature-specific trace,
lifetime, or value-simulation obligations separate.

The next mechanized layer is `cell_view_transform_contract`.  It packages the
common pass shape:

```text
public cell_view
same-instance access remap under cv_cell_relation
semantic view_refinement under cell_view_state_view
```

`cell_view_transform_contract_compose` composes two such passes.  The access
witness is composed with `StorageWitness.pprog_same_instance_access_remap_compose`;
the semantic theorem is composed with `StateView.view_refinement_compose`; and
the final relation is weakened with
`cell_view_state_view_compose_included`.  The input relation is left as the
explicit `compose_view` rather than collapsed to `compose_cell_view`, because
the collapsed endpoint relation only says corresponding endpoint cells agree;
it does not synthesize an intermediate initial state.

### Step 6: Commit and Version Views

Mechanize commit/version selection before contraction:

```text
commit_view
version_view
```

These views are needed by copy protocols, array expansion, and overlap with
commit.

### Step 7: Reuse and Phase Views

Mechanize:

```text
reuse_view
phase_view
```

These cover contraction, inter-array reuse, and double buffering.  They require
lifetime/conflict witnesses and should come after the simpler projection and
private-erasure views.

## Boundary with C and CompCert

`state_view_rel` should be designed so it can later be interpreted over CompCert
memory.

The PolIR version can speak about `MemCell` and `State.t`.  The C boundary will
need additional facts:

```text
logical cells map to CompCert blocks and offsets
target-private blocks are fresh
source and target public blocks are related
frame blocks are preserved
loop/index expressions are defined in C
typed values are compatible
private locals do not escape
parallel writes are race-free
```

These facts should not be duplicated in each transformation validator.  They
belong to the fragment interface and lowering/contextual correctness layer.

## Non-Goals

This design deliberately does not:

```text
weaken State.eq globally
make OpenMP private clauses the semantic primitive
pretend access-list remapping proves instruction semantics
merge instance duplication into state observation
claim whole-program C correctness from a PolIR fragment relation
```

The state view is the semantic endpoint.  Each transformation still needs the
right instance, access, copy, lifetime, conflict, or merge witness to prove that
the endpoint holds.
