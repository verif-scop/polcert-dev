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
  (state_view_rel identity_view)
  (state_view_rel identity_view)
  before
  after
```

with `state_view_rel identity_view` equivalent to, or at least implied by,
`State.eq`.

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

or, initially, a theorem that expands to `compose_state_relation` over
`state_view_rel`.

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
Parameter identity_view_contains_state_eq :
  forall st_t st_s,
    State.eq st_t st_s ->
    state_view_rel identity_view st_t st_s.
```

This is enough to restate the current affine validators as identity-view
validators.

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

Prove that the current state equality route is the identity view instance.  Do
not change existing validator proofs.  Add wrappers.

### Step 4: Layout View

Mechanize the first non-identity view:

```text
layout_view cell_repr
```

This should reuse the existing observer idea, but it must be framed as one
instance of state views rather than a separate `layout_state_rel`.

### Step 5: Private-Erasure View

Mechanize:

```text
private_view public_repr private_cells separation
```

This is the first view that forces separation obligations.

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
