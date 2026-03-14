# Witness-Centered Tiling Redesign

## Motivation

The current split into:

- `pi_transformation`
- `pi_access_transformation`

fixes a real modeling problem, but it is still a transitional shape.

The deeper issue is not "we need two arbitrary transformations". The deeper
issue is that a polyhedral instruction has:

- a current instance space
- a semantic/source instance space

and tiling changes the first without changing the second.

In the affine-only case, these two spaces coincide, so a single transformation
 field was enough. In the tiling case, they do not coincide.

The more principled redesign is:

- keep a single semantic transformation
- add an explicit witness describing how current points project to semantic
  points

This lets a `PolyInstr` stay self-contained while making the source/access
 semantics explicit.

## Current and Proposed Views

For a tiled statement, distinguish:

- current point-space:
  `env ++ tiles ++ point`
- semantic/source point-space:
  `env ++ point`

The current split models these as two transformations. The proposed redesign
models them as:

- one semantic transformation, from semantic/source point-space to instruction
  arguments
- one witness, from current point-space to semantic/source point-space

## Proposed Core Change

Introduce a point-space witness field in `PolyLang.PolyInstr`.

Suggested shape:

```coq
Inductive point_space_witness :=
| PSWIdentity
| PSWTiling (w : statement_tiling_witness).
```

Then replace the transitional pair:

- `pi_transformation`
- `pi_access_transformation`

with a single:

- `pi_transformation`

plus:

- `pi_point_witness`

The semantic intent is:

- `pi_schedule` and `pi_poly` live on the current point-space
- `pi_transformation` and accesses live on the semantic/source point-space
- `pi_point_witness` explains how to project a current point into a
  semantic/source point

## Canonical Projection Functions

Define a projection from current points to semantic/source points.

For identity witness:

```coq
project_point PSWIdentity idx = Some idx
```

For tiling witness:

```coq
project_point (PSWTiling w) (env ++ tiles ++ point) = Some (env ++ point)
```

iff the `tiles` fragment satisfies the floor-link constraints from `w`.

This is the key relation currently spread across:

- `eval_statement_tiling_witness_with_env`
- compiled link-domain checks
- domain completeness lemmas

## Semantic Argument Function

Define semantic/source arguments from a current point:

```coq
src_args_of pi idx :=
  match project_point pi.(pi_point_witness) idx with
  | Some base_idx => affine_product pi.(pi_transformation) base_idx
  | None => []
  end.
```

`PolyLang.poly_semantics` should use `src_args_of` instead of directly using
`affine_product pi_transformation idx`.

This is the central semantic change.

## Access Interpretation

The key simplification is that instruction semantics and access validity should
continue to share the same source-argument vector.

That vector is no longer read directly from the raw current point. Instead it
is computed in two steps:

1. project the current point to a semantic/base point using the witness
2. apply the semantic/source transformation on that projected point

So the canonical derived object is:

```coq
current_src_transformation pi
```

which means:

```coq
current point-space -> base/source point-space -> instruction/source args
```

Then:

- `Instr.instr_semantics` sees `src_args_of`
- access validity also sees the same `src_args_of`
- dependence reasoning composes accesses with `current_src_transformation`

This preserves the original affine reading of `INSTR.valid_access_function`.

## Effect on `INSTR`

Under this refined witness-centered design, `INSTR` likely does **not** need to
change.

Why:

- the old interface already states that instruction semantics and access
  validity share one parameter vector
- the witness now explains how to derive that one vector from the current
  point-space
- both the source semantics and access/dependence reasoning can therefore
  continue to talk about the same source-argument vector

So the real refactoring target moves from `InstrTy` to `PolyLang`:

- `PolyLang` must stop treating `pi_transformation` as a map directly over the
  raw current point-space
- instead it must derive a current-space source transformation through witness
  projection

This is strictly smaller and cleaner than introducing a permanently split
`INSTR` interface.

## Recommended Direction

Recommend the witness-centered `PolyLang` design with unchanged `INSTR`:

- `pi_poly` and `pi_schedule` stay on current space
- `pi_point_witness` projects current points to base/source points
- `pi_transformation` maps base/source points to instruction/source args
- a derived `current_src_transformation` is used wherever current-space affine
  reasoning is needed

This yields a self-contained `PolyInstr` while preserving the original affine
meaning of instruction/access correctness.

## Well-Formedness Redesign

With the witness-centered design:

- `wf_pinstr` should be the weak, common notion
- `wf_pinstr_affine` should become:
  - `wf_pinstr`
  - witness is identity
  - optional affine-specific shape conditions, only if actually needed
- `wf_pinstr_tiling` should become:
  - `wf_pinstr`
  - witness is well-formed tiling witness

## Target `PolyInstr` Shape

The intended end-state is not "two unrelated transformations". The intended
shape is:

```coq
Record PolyInstr := {
  pi_depth : nat;
  pi_instr : Instr.t;
  pi_poly : Domain;
  pi_schedule : Schedule;
  pi_transformation : Transformation;
  pi_point_witness : point_space_witness;
  pi_waccess : list AccessFunction;
  pi_raccess : list AccessFunction;
}.
```

Interpretation:

- `pi_poly` and `pi_schedule` are over the current point-space
- `pi_point_witness` projects current points to semantic/base points
- `pi_transformation` maps semantic/base points to instruction arguments
- accesses are interpreted on semantic/base points, not on raw current points

This keeps a `PolyInstr` self-contained without forcing the semantic argument
space to coincide with the current/tiled point-space.

## Concrete Example

Consider:

```c
for (i = 0; i < N; i++)
  for (j = 0; j < M; j++)
    C[i][j] = A[i][j] + B[i][j];
```

### Affine case

- current point-space: `[N, M, i, j]`
- semantic/base point-space: `[N, M, i, j]`
- witness: identity
- transformation: identity

### Tiled case

If Pluto introduces:

```text
ti = floor(i / 32)
tj = floor(j / 32)
```

then:

- current point-space: `[N, M, ti, tj, i, j]`
- semantic/base point-space: `[N, M, i, j]`
- witness: tiling witness encoding `ti`, `tj`
- transformation: still the source-side map producing `[N, M, i, j]`

The key point is that the instruction still semantically sees the same source
arguments, while the current point-space has been enriched with tile
coordinates.

## Canonical Derived Functions

With the witness-centered design, the core derived functions are:

```coq
project_base_point : point_space_witness -> list Z -> option (list Z)
src_args_of        : PolyInstr -> list Z -> option (list Z)
acc_args_of        : PolyInstr -> list Z -> option (list Z)
```

Intended meanings:

- `project_base_point w current = Some base`
  means `current` is a valid current-space instance whose semantic/base point
  is `base`
- `src_args_of pi current`
  means the argument vector seen by `Instr.instr_semantics`
- `acc_args_of pi current`
  means the argument vector on which access functions are interpreted

For the recommended redesign, `acc_args_of` should simply be the projected/base
point, or a fixed affine view of it. It should not be a second ad hoc
transformation over the raw current point-space.

## Impact on Existing Proof Shape

The high-level proof strategy does not change:

1. affine phase correctness
2. tiling witness / lifting correctness
3. tiled schedule legality
4. composition

What changes is the generic interface through which steps 2 and 3 are stated.

### What stays conceptually the same

- the `before -> mid -> after` decomposition
- the use of a tiling witness as explicit evidence
- the reuse of affine schedule validation on the schedule-only subproblem
- the final semantic statement `after -> before`

### What changes in theorem details

- `PolyLang.poly_semantics` no longer feeds raw current points directly through
  `pi_transformation`
- `InstrTy.valid_access_function` can no longer assume one shared parameter
  vector for both source semantics and access interpretation
- tiling lemmas that previously talked about padded transformations should be
  restated in terms of witness projection

So the redesign does not change the proof idea, but it does change a genuine
generic interface boundary. This is more than cosmetic proof churn.

## Required `INSTR` Interface Change

The current blocker is:

```coq
valid_access_function wl rl i :=
  forall p ...,
    instr_semantics i p ... ->
    valid_access_cells p ...
```

This assumes a single parameter vector `p`.

Under witness-centered tiling, the natural statement is:

```coq
forall current src_args acc_args ...,
  src_args = src_args_of pi current ->
  acc_args = acc_args_of pi current ->
  instr_semantics i src_args ... ->
  valid_access_cells acc_args ...
```

This can be packaged either as:

- an explicit relation between `src_args` and `acc_args`, or
- a direct quantified statement over `current`

The second form is more witness-centered and avoids pretending that
instruction arguments and access arguments are literally the same object.

## Migration Plan

Recommended order:

1. add `point_space_witness`
2. add projection functions over current points
3. refactor `PolyLang.poly_semantics` to use projected/base points
4. refactor `InstrTy.valid_access_function`
5. collapse the temporary dual-transformation split back to:
   - one semantic transformation
   - one explicit witness
6. restate the remaining tiling theorems over witness projection

Immediate theorem targets after the record/interface refactor:

- `wf_pinstr_affine -> wf_pinstr`
- `wf_pinstr_affine -> wf_pinstr_tiling`
- affine identity witness implies projected/current source arguments coincide
- tiling source/access arguments coincide because both are derived from the same
  witness-projected source vector

## Consequence for Affine-Only Code

Affine-only code should remain almost unchanged:

- affine witness is identity
- projected/base points equal current points
- `wf_pinstr_affine` becomes the identity-witness specialization
- many affine proofs should reduce by simplification once the identity witness
  is unfolded

## Updated Blocker Assessment

The earlier diagnosis "generic closure requires changing `INSTR`" was too
strong. A more accurate statement is:

- generic closure requires making the current-to-source projection explicit
- once that projection is explicit, `INSTR` can likely stay unchanged
- the real model bug is that current-space and source-space were previously
  collapsed into one implicit transformation field

This is a better outcome: the redesign is still real, but it is more localized
than a full instruction-interface rewrite.

Important consequence:

- the old `length pi_transformation = env_dim + pi_depth` requirement should
  not remain in the common `wf_pinstr`

That condition is affine-specific at best.

## Validator Impact

The proof strategy does not fundamentally change:

1. validate structural relation / witness correctness
2. prove current-space to source-space projection is correct
3. use schedule legality on the same current-space domain
4. compose the two

But the internal lemmas do change materially:

- `belongs_to`
- `wf_pinstr_ext`
- ext-compose lemmas
- `valid_access_function`
- `validate_two_accesses`
- transformation/effect bridge theorems

So this is not merely cosmetic proof churn. The high-level proof plan survives,
but several statement forms must change.

## Pluto/Tiling Interpretation

For tiling, the witness says:

```text
base = env ++ point
current = env ++ tiles ++ point
tiles = eval_tile_links [] point env links
```

So the current point-space is a witness-controlled lifting of the semantic
point-space.

For affine scheduling, the witness is identity.

This unifies both cases cleanly.

## Migration Plan

1. Replace transitional dual-transformation design with:
   - one `pi_transformation`
   - one `pi_point_witness`
2. Redefine `PolyLang.poly_semantics` via `project_point`
3. Redefine validator access interpretation to use projected/base points
4. Refactor `INSTR.valid_access_function` or its use site accordingly
5. Re-express affine validator over identity witnesses
6. Re-express tiling validator over tiling witnesses
7. Re-prove:
   - common `wf`
   - affine validator soundness
   - tiling structural checker soundness
   - phase-aligned `before -> mid -> after` composition

## Transitional Admit Mapping

The current proof debt already suggests which theorem shapes are transitional.

### Likely to disappear or move

- validator-side transformation equality theorems that try to show a direct
  equality between tiled-space transformation evaluation and source-space
  transformation evaluation
- ext-compose lemmas that assume old/new views can be recovered from a single
  transformation field

Concrete current examples:

- `tiling_rel_pinstr_structure_transformation_sound`
- `tiling_rel_pinstr_structure_transformation_lifted`
- `tiling_rel_pinstr_structure_compiled_transformation_lifted`
- `tiling_rel_pprog_structure_compiled_transformation_lifted_nth`

These are artifacts of the transitional dual-transformation model.

### Should survive but change statement form

- source-side instruction semantics bridge
- domain/access lifting theorems
- schedule legality composition

These should be restated through:

- `project_point`
- `src_args_of`
- projected/base-space access interpretation

## Assessment

This redesign should preserve the overall proof idea:

- affine step correctness
- tiling step correctness
- composition

The main change is representational, not strategic.

However, it is more than just proof-detail churn:

- some theorem statements must change
- `INSTR` must expose the right argument discipline
- validator plumbing must be rewritten around projected/base points

That said, this direction is more semantically natural than permanently keeping
two unrelated transformation fields.
