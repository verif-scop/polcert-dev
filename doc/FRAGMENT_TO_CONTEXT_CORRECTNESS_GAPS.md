# From Fragment Refinement to Contextual C Correctness

This note records the semantic gaps that appear when PolCert's current
polyhedral-fragment validators are viewed as part of a future end-to-end
CompCert-backed pipeline.  The intended reader is a PolCert developer studying
the storage-generalization problem.  The goal is to keep later theorem
statements honest: existing validators prove useful fragment-level facts, but
those facts do not by themselves justify contextual correctness for a complete C
program.

This is a design note, not a statement of implemented support.

Read `STORAGE_AWARE_VALIDATION_OVERVIEW.md` first for the canonical
transformation axes and primitive names.  This file focuses on a different
question: even after a PolIR storage-aware validator is proved, what remains
before one can claim contextual correctness for generated C or a full CompCert
program?

## Current Theorem Boundary

The current validator family works at the PolIR fragment level.  Its core
postcondition has this shape:

```coq
refinement_under obs before after
```

where `after` is the transformed target fragment, `before` is the source
fragment, and `obs` compares the final target state with the final source state.
The existing affine route instantiates `obs` with `State.eq`.  The
storage-generalization design factors this shape further:

```coq
relational_refinement R_in R_out before after
```

Here `R_in` relates target and source initial states, and `R_out` relates target
and source final states.  The old same-initial-state theorem is the special case
where `R_in` is `same_state_relation` and `R_out` is the previous observation.

This is the right abstraction for composing validated transformations inside
PolIR.  It is still a fragment theorem.  It says nothing by itself about C loop
variables, C integer overflow, pointer blocks, stack lifetimes, or the memory
outside the transformed region.

## Layered View

The design should keep five layers separate.

1. Polyhedral layer

   This layer reasons about statement instances, iteration vectors, affine
   schedules, logical access functions, dependence order, and instance
   projection.  Its arithmetic is naturally over mathematical integers.

2. PolIR fragment layer

   This layer gives operational meaning to a list of polyhedral instruction
   instances.  Current validators prove semantic facts about this layer, usually
   by comparing final `State.t` values.

3. Storage-transformation layer

   This layer explains how target storage represents source storage.  Layout
   remapping, private expansion, packing, copy protocols, contraction, and
   overlap tiling all live here.  Each feature needs witnesses for instance
   mapping, storage mapping, freshness, commit, projection, or conflict
   freedom.

4. C/CompCert boundary layer

   This layer connects PolIR states and instructions to Clight or generated C.
   It must prove that C variables, typed values, pointer offsets, and memory
   blocks realize the PolIR fragment semantics.

5. Whole-program context layer

   This layer embeds the transformed fragment back into the surrounding C
   program.  It must account for public inputs and outputs, target-only
   temporaries, frame preservation, non-escaping locals, undefined behavior, and
   observable events.

The current project mainly proves facts in layers 1 and 2.  These notes start
to expose layer 3.  Layers 4 and 5 are the main remaining boundary if the paper
or artifact later claims contextual C correctness.

## Mismatch 1: Fragment State vs Whole C Memory

`State.eq` compares two PolIR states.  It is not a whole-program memory
equivalence.  A complete C program has memory outside the transformed fragment,
stack-allocated locals, possibly unreachable blocks, and variables whose
lifetimes end before the surrounding context can observe them.

For the current affine fragment, `State.eq` is a useful and strong conclusion.
For a transformed C program, the observable relation must know an interface:

```text
source-visible inputs
source-visible outputs
target-only private cells
framed cells outside the transformed region
dead cells that cannot be observed after the fragment
```

This suggests a future relation of the form:

```coq
state_view_rel interface target_state source_state
```

`State.eq` should be treated as the identity-interface instance of this
relation, not as the only meaningful final-state relation.

## Mismatch 2: Access Lists vs Instruction Semantics

PolyInstrs carry read and write access lists, but `PolyLang` execution is driven
by `pi_instr`.  A checker that proves two access lists are related does not prove
that the target instruction actually reads and writes those cells.

This matters for layout transformation.  A witness can relate:

```text
target physical cell A_phys[f(i,j)]
source logical cell A[i,j]
```

but the proof still needs an instruction-level simulation:

```text
target rewritten instruction under the physical layout
  simulates
source-view instruction under the logical layout
```

The current `LayoutWitness` module is therefore only a storage-witness
component.  A complete layout validator also needs a theorem about the concrete
instruction semantics that use the rewritten addresses.

## Mismatch 3: Logical Cell Equality vs Concrete Cell Equality

Polyhedral dependence reasoning can use logical cell equivalence, such as vector
equality up to the representation used by the dependence layer.  Concrete
memory observation is stricter.  A C-like state reads a cell by computing a
concrete block, offset, and basetype.

The exploratory skeleton reflects this split by using strict observable-cell
equality for the CState observer instead of reusing the logical `cell_eq`
relation.  This is not an implementation detail.  Later interfaces should keep
three relations distinct:

```text
logical cell relation:
  used by dependence and access witnesses

physical cell relation:
  used by layout and storage allocation

observable cell relation:
  used by state comparison and C memory reads
```

Conflating these relations would make layout and padding proofs look simpler
than they are.

## Mismatch 4: Loop Variables Are Not Memory Cells

PolIR treats an instance point as a semantic parameter:

```text
S(i,j)
```

The loop variables `i` and `j` are not modeled as C memory cells.  This is the
right abstraction for affine scheduling, but a generated C loop realizes those
coordinates through typed variables, assignments, comparisons, and increments.

A contextual theorem needs a loop-realization obligation:

```text
the C loop-control variables at each dynamic step
  encode
the PolIR instance coordinates for the simulated instance
```

The obligation should also say that loop variables do not escape, are not
address-taken in a way the context can observe, and do not introduce memory
effects outside the fragment interface.

## Mismatch 5: Mathematical Integers vs C Integer Semantics

Affine reasoning uses mathematical integers.  C expression evaluation is typed
and partial.  Signed overflow is undefined behavior; unsigned overflow wraps;
casts can truncate or sign-extend; pointer offsets must remain inside their
allocated block.

A source schedule can be safe while a transformed schedule is not.  Tiling,
skewing, strip-mining, layout linearization, and padding can introduce new
expressions:

```text
tile index arithmetic
min/max guards
skewed loop bounds
linearized array offsets
private-buffer indices
copy-loop bounds
```

A future C boundary theorem needs an `IndexSafety` or `ExprDefinedness`
interface:

```text
every generated bound, guard, schedule expression, and access offset
evaluates in C exactly as its intended integer expression
```

This should remain outside individual storage validators.  The validators should
record which expressions they introduce; a common boundary theorem should prove
that those expressions are C-defined.

## Mismatch 6: Thin Variable and Value Types

The current C-like instruction layer is much thinner than full CompCert C.  In
particular, many polyhedral quantities are effectively treated as integers.  A
complete C embedding must distinguish:

```text
loop and index variable types
scalar temporary types
array element basetypes
pointer types
private-buffer element types
cast policies
alignment requirements
```

Storage transformations need type obligations.  For example, a layout map is not
only a cell map; it must preserve the value type read from and written to that
cell.  A private buffer must have a compatible element type and sufficient
alignment.  A packing transformation must not change the type of the packed
values unless the conversion is part of the validated semantics.

The likely interface is:

```coq
type_env_rel source_types target_types storage_witness
```

or a set of per-feature obligations that all feed into one lowering theorem.
This should not be duplicated in every layout, overlap, or contraction proof.

## Mismatch 7: Abstract Non-Alias vs CompCert Blocks

Polyhedral dependence analysis assumes a sound memory abstraction.  Logical
arrays such as `A` and `B` are treated as distinct storage objects unless the
front end says otherwise.  C pointer parameters do not automatically satisfy
that assumption.

The C boundary must ground no-alias assumptions in memory blocks:

```text
logical array A maps to block bA
logical array B maps to block bB
required non-alias means bA != bB, or a more precise disjoint-range fact
```

For storage-changing transformations the target side also adds obligations:

```text
private buffers are fresh
packed buffers are disjoint from public arrays
layout-remapped arrays do not overlap invalidly
copy-out writes only the committed public region
```

Without this grounding, a dependence-valid schedule can still be unsound as a C
transformation.

## Mismatch 8: Private Storage and Lifetime

Many storage transformations introduce target-only storage:

```text
tile-private halo buffers
expanded scalar or array temporaries
packed blocks
copy-in/copy-out scratch arrays
rolling buffers
```

If these objects are represented inside the final PolIR state, `State.eq` is too
strong.  If they are represented as block-local C variables whose lifetimes end
before the context resumes, they may be erased from the final observation.

The theorem should make this explicit:

```coq
erase_private_observation private_cells target_final source_final
```

or, more generally:

```coq
state_view_rel interface target_final source_final
```

where the interface classifies target-only storage as private and non-escaping.

This is why overlap tiling has two different proof shapes:

```text
overlap without materialized private storage:
  duplicated instances
  final relation may remain State.eq

overlap with tile-private buffers:
  duplicated instances plus target-only storage
  final relation must erase or hide private buffers
```

The difference is semantic, not cosmetic.

## Mismatch 9: Instance Relation vs State Relation

Two independent dimensions are easy to mix together.

The state/storage dimension asks how target states represent source states:

```text
full equality
layout projection
private erasure
copy/commit observation
conflict-safe reuse observation
```

The instance/trace dimension asks how target dynamic executions correspond to
source dynamic executions:

```text
same instances in a different order
duplicated halo instances
inserted copy instances
merged reduction instances
version-selection instances
```

Current affine validation mainly changes the schedule:

```text
same logical instances
same logical storage
different order
```

Overlap tiling mainly changes the instance relation.  It may still end in
`State.eq` if duplicated computations leave no target-only storage and commit
exactly the source-visible writes.  Packing and copy tiling insert helper
instances and usually need a commit observation.  Contraction changes storage
reuse and needs a conflict-based state relation even if the statement instances
remain one-to-one.

The design should therefore avoid feature-name-based theorem shapes.  It should
factor the proof into:

```text
instance witness
storage witness
state-view relation
```

Each transformation then instantiates only the dimensions it changes.

## Mismatch 10: Sequential Semantics vs Parallel Race Freedom

PolIR instance-list semantics is closer to a sequential execution model.  A
target program may be semantically equivalent in a sequential order while still
being invalid as a parallel C or OpenMP program.

Duplicated writes are the clearest example.  If two overlap tiles recompute the
same halo value and write the same global cell, a sequential model might see no
observable difference.  In a parallel C execution, those writes can still be a
data race.

Parallel correctness needs a separate race-freedom obligation:

```text
concurrent target writes are disjoint
or all shared writes are synchronized, atomic, or reduction-validated
```

This should not be hidden inside `State.eq`.  It belongs either to the parallel
validator or to the C/OpenMP code-generation boundary.

## Transformation-Specific Consequences

### Schedule-Only Transformations

Affine scheduling, ordinary tiling, ISS-style splitting, and schedule-driven
parallel exposure fit the current identity case:

```text
same logical instances
same logical storage
initial relation: same_state_relation
final relation: State.eq
```

Their main missing pieces for contextual C correctness are loop realization,
integer definedness, memory safety, and frame preservation.

### Layout Remapping

Layout transformation keeps the statement instances but changes the physical
access map:

```text
same logical instances
changed physical storage
final relation: layout projection, possibly followed by State.eq
```

The exploratory skeleton identifies the relation and access-witness shape.  A
theorem-bearing layout validator still needs instruction-level simulation and C
memory-layout obligations.

### Overlap Tiling

Overlap tiling changes the instance relation:

```text
target has duplicated/internal halo instances
committed target instances cover source-visible results
internal instances are invisible or private
```

If no private storage remains observable, the final relation can be `State.eq`.
If tile-private buffers are materialized in the target state, the final relation
must erase target-only private storage.

### Private Expansion

Privatization and scalar or array expansion change the storage relation:

```text
source shared cell
target private or per-instance cells
```

The validator needs freshness, use-def containment, no-live-in or copy-in, and
no-live-out or copy-out.  The final relation usually erases private storage or
projects it back to source-visible cells.

### Packing and Copy Protocols

Packing inserts helper instances:

```text
copy-in
compute using packed storage
optional copy-out
```

The proof needs role classification, copy coverage, private freshness,
consistent remapping, and commit exactness.  This is both an instance-relation
extension and a state-relation extension.

### Array Contraction and Reuse

Contraction uses a non-injective physical storage map:

```text
many logical values share fewer physical cells
```

The proof should not require injectivity.  It should require conflict-safe
reuse:

```text
if two logical values have overlapping live ranges,
then they must not map to the same physical cell
```

This relation depends on schedule and lifetime information.  It belongs outside
the existing same-access validator.

## Proposed Interfaces

The following interfaces would make the current assumptions explicit without
rewriting the existing affine proof.

### Fragment Interface

```coq
Record fragment_interface := {
  public_inputs : cell_set;
  public_outputs : cell_set;
  frame_cells : cell_set;
  target_private_cells : cell_set;
  source_live_cells : cell_set;
}.
```

This interface tells the state relation what a surrounding context can observe.
For the current validator, the identity interface can classify all relevant
cells as public and no cells as target-private.

### State View Relation

```coq
state_view_rel :
  fragment_interface ->
  storage_view_witness ->
  target_state ->
  source_state ->
  Prop
```

This relation should cover the cases currently described separately:

```text
State.eq
layout projection
private erasure
copy/commit observation
version projection
conflict-safe reuse observation
```

The current `State.eq` route should be proved as a special case of
`state_view_rel` for the identity interface and identity storage witness.

### Instance Trace Relation

```coq
Record instance_trace_witness := {
  target_to_source : target_instance -> option source_instance;
  target_role : target_instance -> role;
  commit_exact : Prop;
  internal_invisible : Prop;
  dependence_closure : Prop;
}.
```

For affine scheduling, `target_to_source` is a bijection and every target
instance is a commit.  For overlap tiling, some target instances are internal
halo recomputations.  For copy protocols, some target instances are copy-in or
copy-out helpers.

### Expression Definedness

```coq
expr_defined :
  c_type_env ->
  generated_expr ->
  intended_Z_expr ->
  Prop
```

This interface should cover loop bounds, guards, schedules, access offsets, and
linearized layout expressions.  It should prove that generated C expression
evaluation is defined and equals the intended mathematical integer expression.

### Memory Layout Relation

```coq
memory_layout_rel :
  logical_cell ->
  compcert_block ->
  byte_offset ->
  basetype ->
  Prop
```

This relation grounds logical cells in CompCert memory.  Layout and padding
transformations instantiate it differently on the target side, while preserving
source-visible values through `state_view_rel`.

### Type Compatibility

```coq
storage_type_compatible :
  source_cell ->
  target_cell ->
  source_type_env ->
  target_type_env ->
  Prop
```

This obligation prevents a storage witness from silently changing the type or
alignment requirements of a value.  It also gives private buffers and packed
buffers explicit basetypes.

## End-to-End Theorem Shape

The intended final theorem should compose several refinement steps, not replace
them with one monolithic validator.

Fragment transformation theorem:

```coq
validated_transform :
  check_transform witness before after = true ->
  relational_refinement
    (state_view_rel input_interface input_view)
    (state_view_rel output_interface output_view)
    before
    after.
```

C extraction or front-end theorem:

```coq
source_c_fragment_matches_polir :
  c_fragment_semantics source_c ctx0 ctx1 ->
  exists polir_state0 polir_state1,
    c_to_polir_state_rel source_interface ctx0 polir_state0 /\
    polir_semantics before polir_state0 polir_state1 /\
    c_to_polir_state_rel source_interface ctx1 polir_state1.
```

Target code-generation theorem:

```coq
target_polir_matches_generated_c :
  polir_semantics after polir_state0 polir_state1 ->
  c_to_polir_state_rel target_interface ctx0 polir_state0 ->
  exists ctx1,
    c_fragment_semantics target_c ctx0 ctx1 /\
    c_to_polir_state_rel target_interface ctx1 polir_state1.
```

Contextual theorem:

```coq
whole_program_refinement :
  extraction_ok source_c before ->
  check_transform witness before after = true ->
  codegen_ok after target_c ->
  boundary_obligations source_c target_c witness interface ->
  whole_program_behaviors target_program
    refines
  whole_program_behaviors source_program.
```

The important point is that each arrow has its own relation.  The
`relational_refinement_compose` theorem in `TransformContract.v` is the PolIR
instance of this style.  A CompCert integration would need analogous composition
lemmas across C-state and PolIR-state relations.

## Design Rules for Future Work

1. Do not weaken `State.eq` globally.

   Keep the current affine theorem as the identity case.  Add new relations for
   new observations.

2. Do not use access-list equality as a substitute for instruction semantics.

   Access witnesses should feed into semantic simulation proofs.  They are not
   semantic simulations by themselves.

3. Separate instance projection from state projection.

   Overlap tiling, copy protocols, and contraction stress different dimensions.
   A single feature name should not determine the theorem shape.

4. Treat C integer safety as a boundary obligation.

   Storage validators may introduce expressions.  The C boundary must prove
   that those expressions are defined under the chosen C types.

5. Make private storage explicit.

   Every target-only object must be fresh, typed, non-escaping, and either
   erased by the final observation or proved unobservable by scope.

6. Ground no-alias assumptions in memory.

   Logical non-alias facts must correspond to CompCert block or range
   separation before they can justify C transformations.

7. Frame the surrounding context.

   The final relation must state which memory is preserved outside the fragment
   and which target-only allocations the context cannot observe.

## Immediate Mechanization Implications

The next storage features should extend this design in this order:

1. Turn `State.eq` into an explicit identity instance of a future
   `state_view_rel`.
2. Add an `InstanceTraceWitness` layer for overlap and copy-protocol examples.
3. Keep layout remapping on the `state_relation` path, but add an
   instruction-level semantic obligation.
4. Add a private-storage erasure relation before modeling materialized
   tile-private overlap buffers.
5. Add a document-only boundary contract for C typing, overflow, no-alias, and
   frame conditions before claiming any whole-program theorem.

This order lets the current affine route remain stable while making the
additional assumptions visible one at a time.
