# Correctness of the Validators

This note is about the validators themselves, not just about the transformations
they model.  The current Python validators are executable research models.  They
make obligations concrete, but they are not soundness proofs for all programs or
all parameter values.

For the broader taxonomy and theorem families, read
`../../doc/STORAGE_AWARE_VALIDATION_OVERVIEW.md` first.  This file is narrower:
it explains what the executable validators do and what a theorem-bearing
validator would still have to prove.

## Current Status

The current `run.py` checks each case by finite execution over small parameter
values and explicit witness checks.  A passing case establishes:

- the source and target behave the same for the chosen finite parameters;
- the intended witness shape is present in that finite run;
- the negative tests reject several common invalid witnesses.

This is useful for understanding and debugging the contracts.  It is not a
translation-validation theorem:

- the checks are bounded, not universally quantified over symbolic parameters;
- the checker is ordinary Python and is fully trusted;
- the source and target fragments are hand-modeled, not parsed from C;
- negative tests show sensitivity to known bugs, not completeness.

The accurate claim is:

```text
These standalone validators are executable specifications of candidate
validation obligations. They are not mechanized proof-producing validators.
```

## Current Case Audit

These experiments intentionally simplify several things.  The simplifications are
acceptable for contract exploration, but they must not be promoted to theorem
claims.

### Source/Target Snippets Are Explanatory

The `.source.c` and `.target.c` files are C-like fragments for human inspection.
The Python validators do not parse or execute those C snippets.  They directly
model the intended source and target semantics.

Consequence:

```text
snippet equivalence is not checked by a C front end.
```

For a real validator, L0 modeling correctness must connect parsed C/IR to the
polyhedral semantic objects being checked.

### Layout Example Assumes Whole-Program Remapping

`layout_remap_padding` validates an address map into padded/transposed physical
storage.  The target snippet declares `A_pad`, but the Python model assumes the
logical values are already stored in the new physical layout.

Consequence:

```text
This is a layout-map validator, not a redistribution/copy validator.
```

If a pass inserts a new allocation mid-program, correctness also needs a copy or
redistribution protocol proving that old-layout values are transferred to the new
layout.

### Boundary Conditions Are Often Fixed

Some examples use parameter values chosen to avoid boundary complications:

- `scratchpad_packing` and `scratchpad_copy_out` use `N` divisible by tile size;
- `reduction_privatization` uses `N` divisible by number of partitions;
- `array_contraction` uses a one-step recurrence with a two-row rolling buffer;
- `overlapped_tiling` uses a one-dimensional read-only stencil-like expression,
  not a full time-space recursive stencil.

Consequence:

```text
The current validators clarify the core obligation, not every boundary case.
```

The theorem-bearing version must handle remainder tiles, triangular domains,
non-unit dependence distances, and other affine boundary structure.

### Dependence Preservation Is Mostly Not Modeled

The schedule-only examples are deliberately dependence-light.  They demonstrate
instance cover and access preservation, not a complete affine scheduling
legality checker.

Consequence:

```text
P0 exact cover must be combined with dependence preservation for real schedules.
```

This is consistent with the current PolCert boundary: dependence/schedule
legality is already a separate major concern, while these experiments isolate the
additional storage obligations.

### Arithmetic Semantics Are Simplified

The validators use Python integers.  They do not model C overflow, floating
point rounding, NaNs, aliasing through casts, volatile accesses, or undefined
behavior.

Consequence:

```text
The arithmetic model is exact mathematical integer arithmetic unless stated
otherwise.
```

For C-like validation, the model must either rule out these behaviors or include
them in the semantic relation.

## Correctness Layers

### L0. Modeling Correctness

The extracted model must faithfully represent the source and target programs.

Examples:

- no-alias assumptions must match the C calling convention or preconditions;
- affine access relations must over-approximate the real memory footprint;
- scalar and array cells must use the same observability convention as the
  language semantics;
- undefined behavior, integer overflow, and floating-point reordering must be
  excluded, modeled, or explicitly relaxed.

If L0 fails, even a perfect polyhedral checker proves the wrong statement.

### L1. Checker Soundness

The Boolean validator must imply the mathematical obligation it claims to check.

Example:

```text
check_exact_cover(pi, Dsrc, Dtgt) = true
  -> forall s in Dsrc, exists unique t in Dtgt, pi(t) = s
```

This is the local correctness theorem for each primitive checker.

### L2. Obligation Sufficiency

The mathematical obligations must imply semantic preservation.

Example:

```text
exact cover + unchanged accesses + preserved dependences
  -> target trace is a legal reordering of source trace
```

For storage-changing transforms, this is where freshness, copy coverage, commit
exactness, conflict-safe reuse, and phase separation become semantic lemmas.

### L3. Decision-Procedure Soundness

Symbolic validators rely on Presburger/polyhedral decision procedures.  Their
results need a trust story:

- the decision procedure is verified;
- or it emits checkable certificates;
- or it remains part of the trusted computing base.

For a verified validator, the best route is to make external solvers emit small
certificates for emptiness, inclusion, exact cover, and non-overlap.

## Primitive Soundness Shapes

### P-1. No-Alias Memory Abstraction

Checker theorem:

```text
check_no_alias(block_of, accesses) = true
  -> distinct logical source blocks are disjoint in the memory model
```

This is a precondition.  It does not prove a transformation, but all later
read/write reasoning is only sound relative to this abstraction.

### P0. Instance Bijection / Exact Cover

Checker theorem:

```text
check_exact_cover(pi, Dsrc, Dtgt) = true
  -> pi is total on Dtgt and exactly covers Dsrc
```

When accesses and statement semantics are unchanged, exact cover reduces target
execution to a reordering or grouping of the same dynamic instances.  It is not
enough if the schedule violates dependences or if accesses changed.

### P1. Role-Based Projection

Checker theorem:

```text
check_roles(pi, role, liveout) = true
  -> every committed source live-out has exactly one target committer
     and every internal target instance is unobservable
```

This handles target instance duplication, such as overlapped tiling.  It also
needs local dependence closure: a commit cannot depend on a halo value that was
neither recomputed locally nor legally imported.

### P2. Access-Map Refinement

Checker theorem:

```text
check_access_refinement(rho, source_accesses, target_accesses) = true
  -> every target physical access denotes the intended source logical value
```

This is the core lemma for layout, padding, scalar expansion, and versioned
arrays.  Injectivity is correct for layout-like transforms, but expansion and
contraction need different side conditions.

### P3. Fresh Private Storage

Checker theorem:

```text
check_private(class, rho_private, live) = true
  -> simultaneously live private classes occupy disjoint cells
     and every private read has a reaching same-class definition
```

Freshness alone is insufficient.  The validator also needs use-def containment:
a private cell read before it is filled is invalid.

### P4. Copy Protocol

Checker theorem:

```text
check_copy(copy_in, local_use, copy_out) = true
  -> local reads are covered by prior copy-in or local writes
     and copy-out writes are well formed and ordered by the protocol
```

Copy-in coverage and copy-out protocol checking are separate from final commit
selection.  Read-only packing can omit copy-out; local updates cannot.

When a copy-out value is the final source-observable value, this primitive
combines with P7: P4 establishes that the local protocol is well formed, and P7
establishes that the committed target write is the unique source-visible one.

### P5. Scalar Simulation

Checker theorem:

```text
check_scalar_sim(entry, sim, exit, region) = true
  -> scalar state simulates the promoted array cell throughout the region
```

This requires no interfering write to the promoted cell while the scalar is
standing in for memory.

### P6. Conflict-Safe Non-Injective Reuse

Checker theorem:

```text
check_reuse(rho, conf) = true
  -> forall v1 v2, conf(v1, v2) -> rho(v1) != rho(v2)
```

The hard part is deriving a sound conflict relation from the schedule and all
future uses.  Once `conf` is sound, the implication is the core contraction
check.

### P7. Version Selection and Commit

Checker theorem:

```text
check_versions(select, commit) = true
  -> each read observes the intended version
     and each observable source output is committed exactly once
```

Unique commit is not enough if a read selects the wrong version before commit.

### P8. Reduction Merge

Checker theorem:

```text
check_reduction(partition, merge, op_semantics) = true
  -> private partial results merge to the source reduction result
```

The algebraic assumptions are part of the semantics.  Floating-point reductions
are not bit-exact under reassociation unless the validator assumes relaxed
floating-point semantics.

### P9. Phase Separation

Checker theorem:

```text
check_phases(phase, visible_after) = true
  -> no still-live value is overwritten before its last use
     and every phase read observes a completed prior write
```

The phase relation must include swaps, barriers, waits, or other visibility
events.  This is why ping-pong buffering is more than just `t mod 2`.

## Composition Theorem

The useful theorem is not one giant validator theorem per optimization.  It is a
composition theorem over primitives:

```text
If
  model_ok(source, target)
  and all primitive checkers used by the witness accept
  and the primitive obligations compose without inconsistent projections
then
  target observationally refines source.
```

Composition has to align shared objects:

- the instance projection used by P0/P1 must agree with the value projection used
  by P2/P7;
- copy protocol outputs and P7 commits must agree with the logical cells that
  live-out exact-cover expects;
- conflict relations for P6 must be derived under the target schedule actually
  being validated;
- private-storage freshness P3 must be scoped to the same lifetime or phase used
  by P4/P9.

## Completeness Is Not the Goal

The validator should be sound, not complete.  It is acceptable to reject legal
transformations if the witness is too hard to prove:

- reject a valid contraction if the conflict relation is outside the supported
  fragment;
- reject a valid layout transform if the address map cannot be proved injective;
- reject a valid floating-point reduction unless relaxed semantics are enabled.

This matters for paper framing: the contribution is a family of checkable
contracts, not a complete optimizer.

## Mechanization Checklist

For a theorem-bearing version, each primitive needs:

1. an abstract semantic relation;
2. a witness data type;
3. a Boolean checker;
4. a checker soundness lemma;
5. a semantic preservation lemma;
6. composition lemmas for combinations used in concrete transformations.

The standalone scripts identify these pieces, but they should not be described
as verified validators.
