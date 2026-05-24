# Candidate Validation Primitives

These primitives are factored from the standalone cases in `run.py`.  They are
not an implementation plan for RCoq yet; they are a vocabulary for deciding what
would need to be formalized if PolCert moves beyond schedule-only validation.

This file is the canonical primitive-numbering reference for the standalone
package.  P7 includes both version selection and commit exactness, P8 is
reduction merge, and P9 is phase separation.  There is no P10 in the current
package.

P4 and P7 are related but not identical.  P4 checks the copy/local-buffer
protocol itself: copy ordering, local read coverage, freshness, and consistent
remapping.  P7 checks which target value becomes source-observable and whether
that value is committed exactly once.  A copy-out transformation can need both.

## P-1. No-Alias Memory Abstraction

Used by:

- `source_no_alias_abstraction`

Witness:

```text
block_of : SourceName -> LogicalBlock
```

Obligations:

- source names assumed distinct map to distinct logical blocks;
- access footprints are computed over those logical blocks;
- any source-level aliasing that can collapse distinct blocks must be ruled out
  by preconditions or represented in the model.

This is not a transformation primitive, but the rest of the storage reasoning is
only sound relative to this abstraction.

## P0. Instance Bijection / Exact Cover

Used by:

- `affine_interchange`
- `index_set_splitting`
- `ordinary_tiling`
- `scalar_privatization_expansion`
- `layout_remap_padding`
- `scratchpad_packing`
- `scratchpad_copy_out`
- `scalar_promotion`
- `array_expansion_versioning`

Witness:

```text
pi : TargetInstance -> SourceInstance
```

Obligations:

- every target instance maps to a valid source instance;
- every source instance is covered;
- ordinary schedule/control transforms require no duplicates;
- accesses remain the same unless combined with another primitive.

This is the closest to the current affine scheduling validator.

## P1. Role-Based Projection

Used by:

- `overlapped_tiling`

Witness:

```text
pi   : TargetInstance -> SourceInstance
role : TargetInstance -> internal | commit
```

Obligations:

- every target computation projects to a valid source computation;
- commit instances exactly cover observable source outputs;
- internal instances may be duplicated but are invisible;
- committed writes are disjoint or ordered.

This is the first primitive that breaks the same-instance-count assumption.

## P2. Access-Map Refinement

Used by:

- `scalar_privatization_expansion`
- `layout_remap_padding`
- `array_expansion_versioning`

Witness:

```text
rho : LogicalCell or LogicalValue -> PhysicalCell
```

Obligations:

- every rewritten target read/write corresponds to the intended source value;
- ordinary layout maps are injective over the logical image;
- expansion maps may introduce extra physical cells but need a projection back
  to source-observable state;
- padding cells are outside the logical image.

This primitive directly violates a validator assumption that access functions are
unchanged.

## P3. Fresh Private Storage

Used by:

- `scalar_privatization_expansion`
- `reduction_privatization`
- tile-local parts of `overlapped_tiling`

Witness:

```text
private_class : TargetInstance -> Class
rho_private   : Class -> PhysicalCell
```

Obligations:

- private classes that can be live together map to disjoint cells;
- each private read has a same-class reaching definition;
- no live-in exists unless there is copy-in;
- no live-out exists unless there is commit/copy-out/merge.

This captures the semantic core of scalar privatization independent of OpenMP.

## P4. Copy Protocol

Used by:

- `scratchpad_packing`
- `scratchpad_copy_out`

Witness:

```text
copy_in  : GlobalCell -> LocalCell
copy_out : LocalCell -> GlobalCell  (optional)
```

Obligations:

- copy-in covers every local read;
- local accesses consistently use the same remapping;
- local storage is fresh for its lifetime;
- copy-out events, if present, are ordered before the committed values are
  observed.

This is the scratchpad/packing/local-buffer primitive.

## P5. Scalar Simulation

Used by:

- `scalar_promotion`

Witness:

```text
entry_load : ArrayCell -> Scalar
simulation : SourceAccess* -> ScalarOperation*
exit_store : Scalar -> ArrayCell
```

Obligations:

- the entry load initializes the promoted scalar correctly;
- all promoted reads/writes are simulated by scalar operations;
- no interfering write changes the promoted cell while it is simulated;
- the exit store occurs before the cell is observed.

This is local storage refinement rather than a global array layout change.

## P6. Conflict-Safe Non-Injective Reuse

Used by:

- `array_contraction`
- `inter_array_reuse`
- storage part of `double_buffering`

Witness:

```text
rho  : LogicalValue -> PhysicalCell
conf : LogicalValue * LogicalValue -> bool
```

Obligation:

```text
conf(v1, v2) -> rho(v1) != rho(v2)
```

The `conf` relation is usually derived from live ranges under the chosen
schedule.  This is the right abstraction for contraction, where injectivity is
intentionally false.

## P7. Version Selection and Commit

Used by:

- `array_expansion_versioning`
- `overlapped_tiling`
- `scratchpad_copy_out`

Witness:

```text
version_of_read : TargetRead -> TargetWrite
commit          : TargetWrite -> SourceObservableCell
```

Obligations:

- each target read selects the version corresponding to the intended source
  dynamic value;
- each source-observable output is committed exactly once;
- extra versions/internal writes are erased from final observation.

This is useful for both expansion and recomputation.

## P8. Reduction Merge

Used by:

- `reduction_privatization`

Witness:

```text
partition : SourceIteration -> PrivateAccumulator
merge     : PrivateAccumulator* -> OutputCell
```

Obligations:

- partitions are disjoint and cover the source reduction domain;
- private accumulators are fresh;
- the merge operator satisfies the algebraic assumptions claimed by the
  semantics;
- floating-point reductions need explicit relaxed or non-bit-exact semantics.

## P9. Phase Separation

Used by:

- `double_buffering`
- async/copy variants of scratchpad protocols, if added later

Witness:

```text
phase : TargetStep -> Phase
visible_after : Phase -> StorageRelation
```

Obligations:

- data written in one phase is visible before later phase reads;
- still-live data is not overwritten in the same phase;
- swaps/barriers update the physical-to-logical projection as claimed.

This primitive captures why ping-pong buffering is more than just `t mod 2`.

## Coverage Matrix

| Case | P-1 | P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `source_no_alias_abstraction` | x | | | | | | | | | | |
| `affine_interchange` | | x | | | | | | | | | |
| `index_set_splitting` | | x | | | | | | | | | |
| `ordinary_tiling` | | x | | | | | | | | | |
| `scalar_privatization_expansion` | | x | | x | x | | | | | | |
| `layout_remap_padding` | | x | | x | | | | | | | |
| `scratchpad_packing` | | x | | | x | x | | | | | |
| `scratchpad_copy_out` | | x | | | x | x | | | x | | |
| `scalar_promotion` | | x | | | | | x | | | | |
| `array_contraction` | | | | | | | | x | | | |
| `inter_array_reuse` | | | | | | | | x | | | |
| `array_expansion_versioning` | | x | | x | | | | | x | | |
| `overlapped_tiling` | | | x | | x | | | | x | | |
| `reduction_privatization` | | | | | x | | | | | x | |
| `double_buffering` | | | | | | | | x | | | x |
