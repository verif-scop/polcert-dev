# Polyhedral Transformation Taxonomy for Storage-Aware Validation

This note records the taxonomy used in the storage-generalization discussion.
It connects three views of the same design space:

1. polyhedral optimization concepts from Pluto-adjacent and storage-optimizer
   literature;
2. standalone executable experiments in
   `experiments/storage-validation-standalone`;
3. PolCert theorem obligations that would be needed to mechanize each class.

The intended reader is a PolCert developer deciding what belongs in the current
verified pipeline, what should remain a standalone experiment, and what needs a
new validator primitive.  This document is not a claim that all transformations
below are implemented in PolCert.

Read `STORAGE_AWARE_VALIDATION_OVERVIEW.md` first.  That file fixes the
canonical primitive names and the status boundary for this document set.
Then read `STATE_VIEW_RELATION_DESIGN.md` for the relation design behind the
"Final observation" column.

## Classification Axes

The current affine validator lives in a narrow but important corner:

```text
same logical instances
same logical storage accesses
different schedule / grouping / order / parallel exposure
```

The broader taxonomy separates four dimensions.

### Instance Relation

```text
same instances:
  every source dynamic statement instance has exactly one target instance

partitioned instances:
  source domain is split into subdomains, but still covered exactly once

duplicated/projected instances:
  target may compute extra instances that project to source instances

inserted helper instances:
  target adds copy, pack, unpack, merge, or commit statements

merged instances:
  target combines multiple source contributions, as in reductions
```

### Storage Relation

```text
identity:
  target accesses the same logical cells as source

injective remap:
  logical cells map to distinct physical cells, possibly with padding

fresh private storage:
  target creates per-thread, per-tile, or per-instance private cells

copy-mediated remap:
  target uses explicit copy-in, local compute, and optional copy-out

non-injective reuse:
  multiple logical values share physical cells when lifetimes do not conflict

version selection:
  target creates multiple versions and selects the source-observable one
```

### State Observation

```text
State.eq:
  target and source final states are equal in the current PolIR state model

projection:
  target physical cells are projected back to source logical cells

erase private:
  target-only private cells are ignored or out of scope

commit observation:
  only committed target writes are source-observable

merge observation:
  private partial results are merged into one source-visible value
```

### Boundary Obligations

These are not transformation-specific, but become necessary for a complete C or
CompCert setting:

```text
no-alias grounding
C integer definedness
loop-variable realization
typed load/store compatibility
memory block/offset layout
frame preservation
private storage lifetime
parallel race freedom
```

## Summary Table

| Transformation | Standalone case | Instance relation | Storage relation | Final observation | PolCert status | Main validation primitive |
| --- | --- | --- | --- | --- | --- | --- |
| Source no-alias abstraction | `source_no_alias_abstraction` | unchanged | logical blocks assumed distinct | `State.eq` under assumption | prerequisite, not a transform | source logical names must map to non-aliasing memory footprints |
| Affine scheduling / interchange | `affine_interchange` | bijection | identity | `State.eq` | current core | instance bijection plus dependence/order preservation |
| Index-set splitting | `index_set_splitting` | partitioned exact cover | identity | `State.eq` | current/near-current ISS support | disjoint subdomains exactly cover source domain |
| Ordinary tiling | `ordinary_tiling` | grouped exact cover | identity | `State.eq` | current tiling route | tile projection covers each source instance exactly once |
| Diamond tiling without recomputation | none yet | grouped exact cover | identity | `State.eq` | Pluto-relevant schedule/control class | non-rectangular tile cover plus dependence legality |
| Layout remapping | `layout_remap_padding` | same instances | injective physical remap | projection, possibly followed by `State.eq` | design sketch; not integrated | access-map injectivity, in-bounds physical image, instruction semantic remap |
| Padding/alignment | `layout_remap_padding` | same instances | injective remap into larger storage | projection ignoring padding cells | design sketch through layout subset | padding cells outside logical image and never observed as source values |
| Scratchpad / local buffer tiling | `scratchpad_packing`, `scratchpad_copy_out` | same compute instances plus helper copies | copy-mediated local storage | erase-private or commit observation | standalone only | copy-in coverage, local freshness, copy-out exactness |
| Packing / copy tiling | `scratchpad_packing` | helper copy instances | copy-mediated remap | erase packed buffer | standalone only | packed cell corresponds to source region and is filled before use |
| Scalar promotion | `scalar_promotion` | same instances | array cell simulated by scalar | `State.eq` or local commit | standalone only | entry load, scalar simulation, exit store, no interference |
| Scalar privatization / expansion | `scalar_privatization_expansion` | same instances | fresh private/expanded scalar cells | erase private or projection | Pluto/Candl-related concept, not current PolCert | freshness, same-class reaching definition, no uncommitted live-out |
| Reduction privatization | `reduction_privatization` | merged contributions | private partial accumulators | merge observation | standalone only | partition cover, fresh accumulators, associative/commutative merge |
| Array expansion / versioning | `array_expansion_versioning` | same instances | more physical versions | commit/project selected version | standalone only | version selection, read-after-write version correctness, copy-out exactness |
| Array contraction / rolling buffer | `array_contraction` | same logical values | non-injective reuse | projection by live version | standalone only; SMO-relevant | conflict relation implies distinct physical cells for overlapping live ranges |
| Inter-array reuse | `inter_array_reuse` | same instances | cross-array non-injective reuse over time | projection by lifetime interval | standalone only; SMO-relevant | live ranges of arrays sharing a buffer do not overlap |
| Double buffering / ping-pong | `double_buffering` | same logical values | phase-separated two-buffer reuse | projection through current phase | standalone only | phase separation, no overwrite of live buffer, swap/projection correctness |
| Overlapped tiling | `overlapped_tiling` | duplicated/projected instances | private recomputation or unique commit | `State.eq` if no private state; otherwise erase-private/commit | standalone only; Flextile/PolyMage-relevant | target-to-source projection, internal/commit roles, unique commit, local closure |
| Memory-space movement | none yet | helper transfers | copy-mediated movement across spaces | projection/commit plus visibility | out of current CPU/C-like scope | transfer region correctness, barriers, ownership, visibility |

## Pluto and Related Optimizer Relation

Pluto is best treated as a schedule-centric baseline, not as the organizing
principle for this taxonomy.

Directly Pluto-relevant classes:

```text
affine scheduling
fusion/fission as schedule/control changes
ordinary tiling
diamond tiling without recomputation
parallel exposure
some privatization/renaming support through Candl or generated OpenMP code
```

Pluto-adjacent classes:

```text
scratchpad tiling
packing/copy tiling
scalar promotion
array/scalar expansion
overlap-style stencil transformations
```

These passes can use a Pluto-like schedule or tile structure, but they need
storage witnesses that Pluto's schedule validator does not supply.

Mostly Pluto-external classes:

```text
layout transformation
padding as a storage remap
array contraction
inter-array reuse
double buffering
general memory-space movement
```

SMO is a closer reference point for contraction and inter-array reuse.  PolyMage
and overlapped/Flextile-style work are closer reference points for recomputation
and overlap.  The PolCert contribution should therefore be framed as validation
primitives for semantic transformation classes, not as a checklist of Pluto
features.

## Relation to Exploratory PolCert Modules

The proof-engineering direction discussed here uses the following module names.
In this host worktree they are not committed implementation files; a Docker
exploration worktree may contain uncommitted skeletons with these names.  Treat
them as a design vocabulary until they are reviewed and integrated.

```text
TransformContract.v:
  observation, state_relation, relational_refinement, composition lemmas

StorageWitness.v:
  target-to-source cell relations and access-list remapping witnesses

StateObservation.v:
  lifts cell relations into state observations through an abstract observer

CStateObservation.v:
  CState-specific observer using CState.read_cell

LayoutWitness.v:
  executable/checkable array-rename layout witness for a padding-style subset

LayoutRemapValidator.v:
  source-view composition theorem for layout remapping
```

This direction targets the layout/padding row first and prepares a theorem
shape for other storage-changing transformations.  It does not yet prove private
expansion, overlap tiling, contraction, packing, or whole-program C correctness.

## Relation to Standalone Experiments

The standalone experiment package is:

```text
experiments/storage-validation-standalone
```

Its main files are:

```text
README.md:
  user-facing case list and commands

REPORT.md:
  generated case table with checked obligations and negative tests

PRIMITIVES.md:
  validation primitive catalogue and coverage matrix

VALIDATOR_CORRECTNESS.md:
  soundness boundaries for the executable validators

run.py:
  finite executable validators for each case

cases/:
  generated C-like source/target examples
```

Those validators are finite executable specifications, not proof-producing
checkers.  They are useful because they make each witness shape concrete before
we decide what to mechanize in Coq.

## Primitive Catalogue

The standalone primitive names are useful as design labels:

```text
P-1 no-alias abstraction
P0  exact-cover instance projection
P1  role-based projection
P2  access-map refinement
P3  fresh private storage
P4  copy protocol coverage
P5  scalar simulation
P6  conflict-safe non-injective reuse
P7  version selection and commit
P8  reduction merge
P9  phase separation
```

Mapping to transformations:

```text
schedule/interchange/ordinary tiling:
  P0

layout and padding:
  P0 + P2

scalar privatization:
  P0 + P2/P3

scratchpad and packing:
  P0 + P3 + P4 + P7 when copy-out/commit is present

scalar promotion:
  P5

contraction and inter-array reuse:
  P6

array expansion/versioning:
  P0 + P2 + P7

overlapped tiling:
  P1 + P3 if private storage is materialized + P7

reduction privatization:
  P3 + P8

double buffering:
  P6 + P9
```

The exact numbering is not meant to become a Coq API.  The important point is
that each primitive names a proof obligation that can be reused across several
optimizations.

## Theorem Consequences

The taxonomy implies three theorem families.

### Identity/Schedule Theorems

These are the existing PolCert shape:

```coq
relational_refinement
  same_state_relation
  identity_observation
  before
  after
```

They cover affine scheduling, ordinary tiling, and ISS-like exact-cover control
changes.

### State-Relation Theorems

These keep the source and target instance relation simple but change storage:

```coq
relational_refinement
  R_in
  R_out
  before
  after
```

Layout, padding, private expansion, contraction, inter-array reuse, and
double-buffering live here.  `R_out` might project target cells, erase private
cells, select the current version, or relate non-injective reused storage to
source logical values.

### Trace/Instance Theorems

These change target dynamic instances:

```text
target trace projects to source trace
some target instances are internal/helper/commit/merge roles
source-visible effects are covered exactly
```

Overlap tiling, copy protocols, packing, and reductions need this family.  Some
of them also need state-relation theorems if they materialize private storage or
helper buffers in the final state.

## Recommended Mechanization Order

1. Keep the existing affine validators as the identity theorem family.
2. Finish the layout/padding path by adding instruction-level semantic
   refinement for rewritten accesses.
3. Introduce a first-class `state_view_rel` so private erasure and layout
   projection share one endpoint relation.
4. Add an `InstanceTraceWitness` module before attempting overlap or copy
   protocols.
5. Mechanize a small private-scalar expansion case, because it exercises
   freshness and use-def containment without requiring target trace duplication.
6. Mechanize array contraction only after the state-view relation can express
   non-injective logical-to-physical projection.
7. Keep C typing, overflow, no-alias grounding, and frame conditions in a
   separate boundary contract until the PolIR fragment story is stable.

This order keeps existing proofs stable while turning the taxonomy into
incremental theorem obligations.
