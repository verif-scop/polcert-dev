# End-to-End Correctness Story

The storage survey should answer one question:

```text
Why is the optimized target accepted as correct?
```

The universal answer is:

```text
For every target execution, there exists a source execution such that final
public logical views have the same observable contents.
```

This deliberately weakens the old endpoint:

```text
final target state = final source state
```

to:

```text
final target/source agree on the public logical interface
```

The optimized target may allocate, overwrite, fold, or drop private/helper
storage.  That storage is irrelevant unless it affects a public variable.

## Intuitive Top Theorem

The theorem should read like this:

```text
if the storage validator accepts a certificate for source -> target,
then target refines source under equality of final public logical views.
```

Equivalently:

```coq
validator cert source target = true
  -> semantic_refinement
       source target
       (fun source_final target_final =>
          public_output_view_eq cert source_final target_final).
```

The exact Coq names can differ, but the theorem should not expose the
cell/event machinery.  That machinery belongs to the validator soundness proof:
accepted certificates elaborate public variables into footprints and prove the
right representation obligations.

`public_output_view_eq` is not raw same-name state equality.  For layout remap,
the source logical `A` may be represented by target physical `A_pad`; for
folding, there may be no target variable with the same name as the source
logical temporary.  The certificate defines how target storage exports the
logical public interface.

## Acceptance Boundary

A storage optimization is accepted when the validator proves three things.

1. Public variables are identified.

The certificate names the logical variables that are observable at the boundary
and explains how the target exports them.  These are the only observations in
the final relation.

2. Target private storage is justified.

Every target read that contributes to a public value is justified by one of:

- source public input;
- private write-before-read evidence;
- copy-in/copy-out evidence;
- layout representation evidence;
- lifetime/reuse evidence;
- version selection evidence;
- reduction merge evidence;
- halo/overlap commit evidence.

3. Final public values are represented.

For every final public variable element, the target value is shown to represent
the value produced by the source semantics.

The same boundary covers memory folding and contraction.  Folding is not a
special theorem endpoint; it is a harder representation witness.  The validator
must prove that physical collisions happen only between dead logical values, and
that final public values are copied, selected, or projected before reused
storage is overwritten.

## Per-Transformation End-to-End Reason

### Scalar Expansion / Privatization

Accepted because each logical temporary live range is represented by a fresh
per-instance private cell.  Private cells are not public, and every public write
that used the old temporary now reads the matching private cell.

Correctness endpoint: public outputs such as `B` match; `tmp` and `tmp_exp` are
not observed.

### Scalar Promotion

Accepted because the scalar protocol loads the public cell, performs local
updates through private scalar storage, and stores back before the public cell is
observed.

Correctness endpoint: the public variable after store-back matches the source.

### Scratchpad / Copy

Accepted because copy-in initializes every local read, local computation uses the
declared local representation, and copy-out commits every public live-out exactly
once.

Correctness endpoint: public arrays match after copy-out; scratchpad buffers are
private.

### Layout Remap

Accepted because every public logical element is represented by an injective
physical location under the declared layout map, and all target accesses use the
same map.

Correctness endpoint: logical public array contents match even if physical
layout differs.

### Contraction / Reuse / Folding

Accepted because physical storage is shared only by logical values whose
lifetimes do not overlap.  Every read observes the correct reaching logical
value, and final public live-outs are projected or copied out.

Correctness endpoint: folded buffers need not equal source arrays; public
logical outputs match.

### Inter-Array Reuse

Accepted because arrays mapped to one buffer have disjoint live ranges and
compatible storage.  The shared buffer is internal and does not expose stale
values.

Correctness endpoint: public variables that survive the fragment match.

### Versioning / Array Expansion

Accepted because every read selects the version produced by the corresponding
source reaching definition, and final public variables select the final version.

Correctness endpoint: only committed/selected versions determine public output.

### Double Buffering

Accepted because the phase projection tells which physical buffer row represents
the current logical state.  Swaps update the projection, and final projection
covers all public live-outs.

Correctness endpoint: public final snapshot matches; non-current buffer rows are
private implementation detail.

### Reduction Privatization

Accepted because chunks exactly cover source contributions, private accumulators
are fresh and initialized, and merge consumes each accumulator exactly once under
the required algebraic laws.

Correctness endpoint: public reduction result matches the source reduction.

### Overlap / Halo / Redundant Computation

Accepted because target extra computations project to source computations but
only designated commit events write public outputs.  Commit events form an exact
cover of source live-outs.

Correctness endpoint: duplicate halo values are private; public committed
outputs match.

## What Must Not Be in the Top Theorem

The top theorem should not mention:

- concrete array names like `B`;
- concrete finite indices such as `[0;1;2;3]`;
- concrete target private cells such as `tmp_exp[0]`;
- concrete CInstr execution traces;
- proof-only `MemCell` enumerations.

Those belong in examples and witness elaboration.

The theorem should mention:

- accepted certificate;
- source and target programs;
- public variable visibility;
- semantic refinement with final public-variable equality.

## Where Complexity Belongs

The design is universal only if complexity is pushed below the theorem boundary:

- variable shapes and footprints explain what a public array means;
- representation evidence explains where the target stores each logical value;
- lifetime and phase evidence explains non-injective reuse;
- copy and commit evidence explains private/public boundaries;
- algebraic merge evidence explains reductions.

Those are certificate/checker facts.  The top theorem should stay stable when a
new storage transformation is added.
