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

In this host worktree, the storage-generalization material is documentation plus
the standalone executable experiment package.  A Docker worktree used during
exploration may also contain uncommitted Coq skeletons named
`TransformContract.v`, `StorageWitness.v`, `StateObservation.v`,
`LayoutWitness.v`, `LayoutRemapValidator.v`, and related files.  Treat those
files as design sketches until they are committed, reviewed, and integrated
through the normal proof build.

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

This list intentionally folds commit exactness into P7.  Earlier notes used a
separate P8 for commit exactness and shifted reduction/phase numbering; those
older numbers should not be used going forward.

## Theorem Families

The taxonomy points to three theorem families.

1. Identity/schedule theorems:
   `same_state_relation` on inputs and `State.eq` on outputs.  This is the
   existing affine, tiling, ISS, diamond-without-recomputation, and checked
   annotation route.
2. State-relation theorems:
   target and source executions are related by explicit input and output state
   relations.  Layout remapping, private expansion, contraction, inter-array
   reuse, and double buffering belong here.
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
   expansion case.
5. Add conflict-safe non-injective reuse only after the state-view relation can
   express projection from logical values to reused physical cells.
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
