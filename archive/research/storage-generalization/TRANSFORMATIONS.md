# Storage Transformation Taxonomy

This file records each storage transformation as a validation target.  Each
entry uses the same end-to-end meaning: only public variables must agree at the
program boundary; private/helper storage is internal.

## Universal Reading

Every entry below should be readable as an instance of the same certificate
shape:

```text
public variables + shapes/footprints
  + representation evidence
  + checked obligations
  => final public variables agree
```

The representation evidence is allowed to mention target physical cells, events,
phases, versions, or merge trees.  That evidence is internal to validation.  The
top-level semantic statement remains variable-based.

## Source No-Alias Abstraction

What it does:

This is not an optimization by itself.  It is the source-level memory model
assumption used by many storage transformations: different logical variables are
treated as distinct blocks unless aliasing is explicitly modeled.

Public/private view:

- public vars are still ordinary source variables;
- no private storage is introduced;
- the abstraction lets the validator reason about variable footprints rather
  than arbitrary pointer aliases.

Correctness obligations:

- declared source variables have distinct logical blocks;
- every source access is inside the declared footprint of its variable;
- transformations that rely on non-aliasing must reject unknown or overlapping
  footprints.

Universal representation instance:

- logical variable footprints are the units of reasoning;
- no target-private representation is introduced.

Counterexamples:

- `A` and `B` may alias, but a transformation assumes writes to `A` cannot
  change reads from `B`;
- a source access is outside the declared footprint.

## Contextual Frame Preservation

What it does:

This is the context boundary condition for fragment validation.  A storage
optimization may rewrite internal storage, but it must not modify context-owned
variables outside its allowed write set.

Public/private view:

- public vars may include both transformed outputs and context-owned frame vars;
- frame vars should be preserved if the fragment is not allowed to write them.

Correctness obligations:

- all fragment writes are included in an allowed-write set;
- allowed writes are disjoint from protected frame variables;
- frame snapshots before/after the fragment agree.

Universal representation instance:

- protected frame variables are public observations that must map to themselves;
- allowed writes define the fragment boundary for public equality.

Counterexamples:

- transformed code writes a context-owned variable;
- allowed writes overlap the frame;
- a frame value changes even though the fragment should preserve it.

## Scalar Expansion / Scalar Privatization

What it does:

```c
for (i = 0; i < N; i++) {
  tmp = A[i] + 1;
  B[i] = tmp * 2;
}
```

becomes:

```c
for (i = 0; i < N; i++) {
  tmp_exp[i] = A[i] + 1;
  B[i] = tmp_exp[i] * 2;
}
```

The reused scalar or one-cell temporary becomes per-instance private storage.

Public/private view:

- public vars: `A`, `B`;
- private vars: `tmp`, `tmp_exp`;
- final observation: `B` equals the source result, and unchanged public inputs
  such as `A` remain equal if they are part of the public post-state.

Correctness obligations:

- each source temporary live range maps to exactly one private cell;
- every private read is dominated by the matching private write;
- private cells are fresh or non-observable;
- if a private value is live-out, it must be copied to a public variable.

Universal representation instance:

- `(tmp, logical instance i, live range)` maps to `(tmp_exp, i, target event)`;
- the map is fresh per live range;
- final public variables exclude `tmp_exp`.

Counterexamples:

- `tmp_exp[i]` read before write;
- two live iterations share the same private cell;
- a private cell escapes as a public output without copy-out.

External evidence:

- Candl `-scalexp` changes OpenScop access arity for scalar `t` from scalar to
  per-iteration indexed access.
- Pluto `--scalpriv` is related but is mainly a Candl dependence-analysis mode
  in the current source.

## Scalar Promotion

What it does:

```c
for (i = 0; i < N; i++) {
  A[i] = A[i] + 1;
}
```

may be represented internally as:

```c
for (i = 0; i < N; i++) {
  s = A[i];
  s = s + 1;
  A[i] = s;
}
```

or a longer local scalar protocol around repeated accesses.

Public/private view:

- public vars: the promoted source variable, for example `A`;
- private vars: scalar registers or temporary locals;
- final observation: public `A` after store-back equals source `A`.

Correctness obligations:

- load initializes the promoted scalar before use;
- every public live-out update is stored back;
- no hidden scalar write clobbers a public value without a final store;
- alias conditions ensure the cached value is not invalidated by another public
  write.

Universal representation instance:

- a public cell is represented temporarily by a private scalar between load and
  store-back events;
- the final public observation is the store-back target cell, not the scalar.

Counterexamples:

- missing load;
- missing live-out store;
- another write to `A[i]` occurs while scalar `s` is assumed current.

## Scratchpad / Copy-In Copy-Out

What it does:

```c
for (i = 0; i < T; i++) local[i] = A[base + i];
... use local ...
for (i = 0; i < T; i++) B[base + i] = local[i];
```

Public array tiles are copied into local storage and later committed.

Public/private view:

- public vars: source arrays and output arrays such as `A`, `B`;
- private vars: scratchpad/local buffers;
- final observation: committed public outputs match source semantics.

Correctness obligations:

- every required live-in has a copy-in;
- every required live-out has a copy-out;
- copy pairs map the intended public indices to local indices;
- local cells are in bounds and do not alias incompatible live values;
- copy-out writes are unique or otherwise deterministically resolved.

Universal representation instance:

- copy-in maps public logical cells to private local cells for a tile phase;
- copy-out maps selected local cells back to public logical cells at the
  boundary;
- local-only cells are private observations.

Counterexamples:

- missing copy-in for a local read;
- missing copy-out for a public live-out;
- two local cells claim the same public output with different values.

## Layout Remap / Padding / Permutation

What it does:

```c
A[i][j]
```

is stored as:

```c
A_pad[f(i,j)]
```

where `f` may add padding, transpose dimensions, or use an affine layout.

Public/private view:

- public var is still logical `A`;
- target physical var may be `A_pad`;
- final observation compares logical `A` contents, not raw physical layout.

Correctness obligations:

- layout map is injective over simultaneously live logical cells;
- all mapped physical cells are in bounds;
- every public logical cell has a represented physical cell;
- reads and writes use the same declared layout map.

Universal representation instance:

- `(A, logical index p, boundary)` maps to `(A_pad, f(p), boundary)`;
- padding-only physical cells have no public logical observation;
- if `f` is not globally injective, the validator must prove lifetime
  separation, which moves the case into folding/reuse.

Counterexamples:

- two logical public cells map to the same physical cell while both live;
- target access uses a different affine map than the witness;
- padding cell is treated as public output.

## Array Contraction / Storage Folding / Reuse

What it does:

```c
T[t][i]
```

is contracted to:

```c
T[t % k][i]
```

or several logical temporaries share one physical buffer.

Public/private view:

- public vars are final logical outputs, not the folded temporary store;
- folded storage is private unless explicitly committed.

Correctness obligations:

- logical cells sharing a physical cell have non-overlapping live ranges;
- every read observes the most recent represented write for its logical value;
- boundary live-outs are copied to public variables before reuse destroys them.

Universal representation instance:

- `(T, logical index p, logical time t)` maps to `(T_fold, g(t,p), phase t)`;
- the physical map may be non-injective across all time;
- the validator proves live-range disjointness for every physical collision.

Counterexamples:

- two live logical values share one physical slot;
- a physical slot is reused before the old logical value is consumed;
- final public output reads a destroyed version.

## Inter-Array Reuse

What it does:

```c
T1[...]  // used in phase 1
T2[...]  // used in phase 2
```

share one buffer when their lifetimes do not overlap.

Public/private view:

- original public outputs remain public;
- shared buffer is private/internal;
- final public variables cannot depend on overwritten private values.

Correctness obligations:

- lifetime intervals for reused buffers are disjoint;
- storage specs are compatible;
- no public live-out points to the shared private buffer without copy-out.

Universal representation instance:

- different logical variables map to the same target buffer only under disjoint
  lifetime intervals;
- public final values are copied/projected out before another variable reuses
  the buffer.

Counterexamples:

- `T1` is read after `T2` overwrites the shared slot;
- incompatible element sizes or alignment;
- a shared private buffer escapes as public state.

## Versioning / Array Expansion

What it does:

```c
X[i] = ...
X[i] = ...
```

becomes:

```c
X_v0[i] = ...
X_v1[i] = ...
X[i] = select_final(X_v1[i])
```

Public/private view:

- public var: logical `X`;
- private vars: versions `X_v0`, `X_v1`, ...;
- final observation: selected committed version equals logical `X`.

Correctness obligations:

- each read selects a produced version;
- final public value selects exactly the source-final version;
- selected versions are in bounds and storage-compatible;
- copies or commits cover all public live-outs.

Universal representation instance:

- `(X, p, definition d)` maps to `(X_vd, p, producer event d)`;
- each target read carries a checked version selector;
- final public `X[p]` selects the source-final version.

Counterexamples:

- final copy selects an old version;
- read selects an unproduced version;
- two versions are both committed to one public cell inconsistently.

## Double Buffering

What it does:

```c
for (t = 0; t < T; t++)
  A[t+1] = step(A[t]);
```

uses two physical buffers:

```c
cur = t % 2;
next = 1 - cur;
Buf[next] = step(Buf[cur]);
```

Public/private view:

- public var is the logical final state;
- physical buffers are private implementation storage unless one is committed.

Correctness obligations:

- phase projection says which physical row represents the current logical row;
- swaps preserve the current/next interpretation;
- final snapshot is copied or projected to the public output.

Universal representation instance:

- `(A, p, phase t)` maps to `(Buf, (t mod 2, p), phase t)`;
- phase-transition obligations prove swaps update the projection correctly;
- non-current rows are private.

Counterexamples:

- missing swap;
- final public output reads the stale buffer;
- a phase write reads from `next` instead of `cur`.

## Reduction Privatization and Merge

What it does:

```c
for (i = 0; i < N; i++)
  sum += A[i];
```

becomes:

```c
for each chunk c:
  priv[c] = reduce A over chunk c
sum = merge(priv[0], ..., priv[k-1])
```

Public/private view:

- public var: `sum`;
- private vars: partial accumulators;
- final observation: public `sum` equals source reduction result.

Correctness obligations:

- chunks partition the source iteration domain;
- each private accumulator is initialized correctly;
- merge consumes every partial exactly once;
- operator laws justify reorder/grouping, usually associativity plus identity,
  and commutativity if chunks are reordered.

Universal representation instance:

- individual source contributions map to private accumulator events;
- the final public scalar is represented by a merge tree, not by one cell map;
- algebraic laws are part of the certificate because storage evidence alone is
  insufficient.

Counterexamples:

- chunks overlap or miss iterations;
- merge omits a private accumulator;
- operator is not associative but schedule changes grouping.

## Overlap / Halo / Redundant Computation

What it does:

Tiles compute extra halo points locally so each tile can run with fewer external
dependencies.  Only selected commit points update public outputs.

Public/private view:

- public vars are committed outputs;
- halo and duplicate computations are private/internal;
- final observation ignores duplicate private results.

Correctness obligations:

- halo closure covers every local read dependency;
- only designated commit events write public cells;
- each public output has exactly one committed value;
- private halo writes do not escape.

Universal representation instance:

- duplicate/halo computations may represent the same logical value internally;
- only commit events represent final public observations;
- commit events must exactly cover public live-outs.

Counterexamples:

- missing halo producer for a local read;
- two tiles commit different values for the same public output;
- internal halo write is accidentally observed as public output.
