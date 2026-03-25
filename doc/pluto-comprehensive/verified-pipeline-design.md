# Verified Pipeline Design

This document explains the design of the current verified PolCert/PolOpt
pipeline. It focuses on *why* the pipeline is structured the way it is, which
modules own which responsibilities, and why several boundaries that may look
redundant are in fact deliberate.

For the public naming glossary, see:

- [verified-phase-pipeline.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/verified-phase-pipeline.md)

For the external Pluto phase order, see:

- [pipeline.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/pipeline.md)

For the current proof/runtime status, see:

- [formalization-status.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/formalization-status.md)

## 1. Design Goal

The current design is trying to achieve all of the following at once:

1. keep the original affine proof chain intact where it is already correct
2. support real Pluto tiling output, not just an abstract tiling model
3. keep the final optimizer path verified end-to-end
4. avoid pushing tiling-specific complexity into every existing affine theorem
5. keep concrete language instantiations thin and proof-free

This is why the final design is not "replace the affine path with a tiling path"
but rather:

- preserve the affine path as a stable verified sub-pipeline
- add a checked tiling path on top of it
- rejoin the old codegen route through a carefully chosen normalization step

## 2. Final High-Level Route

For programs with loop dimensions, the current verified route is:

```text
Loop
-> extractor
-> strengthen
-> try affine-only checked scheduler route
-> try two-stage Pluto phase route
   -> affine import/validation on before -> mid
   -> checked tiling validation on mid -> after
   -> current_view_pprog after
   -> existing verified codegen
-> if the tiling route does not complete successfully, fall back to the
   affine-only checked route
```

For programs with no loop dimensions:

```text
Loop
-> extractor
-> strengthen
-> prepare/codegen directly
```

This split is intentional. It avoids sending scalar-only cases through external
Pluto machinery that cannot contribute useful loop restructuring.

## 3. Stage-By-Stage Responsibilities

The easiest way to understand the current design is to separate the pipeline
stages by *role*, not only by execution order.

There are three especially important kinds of stage:

1. semantic extraction
2. representation-strengthening / normalization
3. checked transformation and code generation

The normalization stages are easy to misread because they all "adjust" the
program, but they do so for different reasons. The sections below focus on the
non-obvious stages and explain why each one exists.

### 3.1 `Extractor.extractor`

This is the semantic front-end:

- convert the source loop program into `PolyLang`
- move the proof context from surface loop syntax to the polyhedral
  instance-list model

The reason it is its own stage is straightforward: every downstream theorem is
phrased over `PolyLang`, not directly over source loop syntax.

### 3.2 `Strengthen.strengthen_pprog`

This is the first normalization pass. It does **not** change schedules,
transformations, witnesses, or accesses. It only strengthens domains.

Concretely, it:

- looks for pairs of constraints that cancel the current iterator
- infers prefix-only guards from those pairs
- appends those guards to the domain

The purpose is not optimization. The purpose is to make domain facts explicit
that are already semantically implied. This helps later validation/import stages
by reducing dependence on hidden derived facts.

So `strengthen_pprog` is best understood as a **domain-explicating
normalization**, not as a schedule transformation.

### 3.3 `has_nonscalar_stmt`

This is a routing predicate, not a proof idea. It detects whether any statement
still has positive loop depth.

Its purpose is:

- avoid sending scalar-only programs through external Pluto/OpenScop machinery
- keep the no-loop case on the simplest verified route

This explains why the scalar-only branch bypasses the external scheduler/tiling
path entirely.

### 3.4 `checked_affine_schedule`

This stage:

1. calls the external affine scheduler
2. immediately validates the returned program with the affine validator

The design reason is to force the external scheduler behind a checked contract:

- the optimizer should never continue on an unvalidated affine-scheduled
  program

This stage is both:

- the older stable verified sub-pipeline
- the fallback target when the two-stage tiling route does not complete

### 3.5 `export_for_pluto_phase_pipeline`

This is a format-bridging stage.

It exports the internal `PolyLang` program into the OpenScop view expected by
the dedicated two-stage Pluto phase pipeline.

The key point is that this is **not** a tiling transform. It is a boundary
conversion:

- internal verified representation
- external Pluto-facing OpenScop representation

This is why it deserves a dedicated name. It marks a specific external contract,
not a generic "to OpenScop" conversion in the abstract.

### 3.6 `run_pluto_phase_pipeline`

This is the external two-stage Pluto contract:

- run affine scheduling
- then run tiling
- return both the affine midpoint and the tiled result

The design reason is that the verified route needs both artifacts:

- `mid_scop` to validate the affine phase
- `after_scop` plus a witness to validate the tiling phase

That is why this route cannot be modeled as just "run one scheduler and get one
program back".

### 3.7 Midpoint import and affine validation

After the external phase pipeline returns, the midpoint is imported into the
internal `PolyLang` representation and validated with the ordinary affine
validator.

This stage exists so that the tiling proof boundary is:

```text
mid -> after
```

rather than:

```text
before -> after
```

The midpoint is therefore a real proof boundary, not a debugging artifact.

### 3.8 Witness inference

Witness inference is intentionally outside the verified core.

Its role is:

- read `(mid_scop, after_scop)`
- produce a candidate tiling witness

The design boundary is deliberate:

- witness production may be heuristic
- witness checking must be verified

This keeps the trusted core small without forcing the project to prove the
entire OpenScop-to-witness inference heuristic.

### 3.9 `import_canonical_tiled_after_poly`

This is one of the most important representation stages in the tiling route.

It does **not** import the raw `after.scop` as an arbitrary final internal
program. Instead it:

1. builds the canonical tiled skeleton from `(before, witness)`
2. imports only Pluto's final schedule over that skeleton

The reason is structural control:

- the witness determines the intended tiled structure
- the internal checked validator should reason over a canonical tiled program,
  not over every accidental detail of a raw imported OpenScop object

So this stage is a **canonicalization-by-import** step. It minimizes how much of
the external `after.scop` must be trusted structurally.

### 3.10 `checked_tiling_validate_poly`

This is the full checked tiling validator on the outer `PolyLang` type.

It is intentionally composed from:

1. structural/witness checking
2. canonical tiled import
3. generic validation on the imported program

The design reason is separation of concerns:

- witness/structure mismatches should be rejected before generic schedule
  legality is even considered
- generic dependence/permutability reasoning should be reused once the program
  is in the right internal form

### 3.11 `current_view_pprog`

This is the second major normalization pass. It does **not** optimize and does
**not** change the validated current-space semantics.

Its role is:

- materialize the witness-induced current-space transformation explicitly
- replace the witness-centered representation with an affine-style
  current-space view

The reason this stage exists is codegen reuse. Without it, the project would
have had to rewrite the older affine codegen proof chain to reason directly
about arbitrary witness-centered tiled programs.

So `current_view_pprog` is best understood as a **representation-lowering pass
for the proof boundary**, not as another schedule/domain optimization.

### 3.12 `PrepareCore.prepare_codegen`

This is the third normalization pass. It regularizes the current-space program
for code generation.

Concretely, it:

- computes a target column dimension
- resizes domain, schedule, transformation, and access matrices to that
  dimension
- encodes trailing extra dimensions into the domain
- records padding using `PSWInsertAtEnd`

The reason for this stage is that the code generator wants a regularized,
fixed-dimension view:

- schedules must have the expected width
- transformations must have the expected width
- tail dimensions must be semantically harmless and explicit

So `prepare_codegen` is a **shape-regularization pass for codegen**, not a
tiling-specific pass and not a semantic optimization in the ordinary sense.

### 3.13 `CodeGen.codegen` and cleanup

The final stage consumes the prepared program and produces loops, followed by a
cleanup pass over the generated loop syntax.

The reason cleanup remains separate is that codegen first aims for correctness
and structural generation, while cleanup improves the emitted loop syntax
without changing semantics.

## 4. Why There Are Two Pluto-Facing Routes

There are two Pluto-facing contracts in the current implementation.

### 4.1 Affine-only scheduler route

This is the historical route:

- one external scheduling step
- one imported scheduled program
- one affine validator call

Its contract is simple:

```text
before PolyLang
-> external affine scheduler
-> mid PolyLang
-> validate(before, mid)
```

This route is already well-understood and already had a usable verified codegen
path.

### 4.2 Two-stage Pluto phase route

This is the tiling-aware route:

```text
before PolyLang
-> export_for_pluto_phase_pipeline
-> run_pluto_phase_pipeline
-> (mid_scop, after_scop)
-> import mid from OpenScop
-> validate(before, mid)
-> infer witness from (mid_scop, after_scop)
-> import canonical tiled after
-> checked_tiling_validate_poly(mid, after, witness)
```

This route is fundamentally different from the affine-only route:

- it consumes and produces two OpenScop outputs, not one
- it needs a witness to explain the tiling relation
- it has two correctness boundaries:
  - affine `before -> mid`
  - tiling `mid -> after`

This is why the two routes must remain distinguishable in both naming and proof
structure.

## 5. Why The Fallback Exists

The fallback is often misunderstood. It is **not**:

```text
Pluto failed -> give up on Pluto entirely
```

It is:

```text
the dedicated two-stage phase-aligned tiling route did not complete as a fully
checked verified route -> reuse the already-verified affine-only route
```

This design serves two purposes.

### 4.1 It preserves soundness

The optimizer should only continue on a tiling path if all of the following
succeed:

1. export to the phase pipeline
2. Pluto phase execution
3. midpoint import
4. affine validation of `before -> mid`
5. witness inference
6. canonical tiled import
7. checked tiling validation

If any one of these fails, the optimizer should not continue with a half-checked
tiled program.

### 4.2 It preserves optimization value

The fallback does not return the original program unless the affine route itself
also fails. It falls back to the checked affine path, which still provides
useful scheduling optimizations and keeps the mainline optimizer usable.

## 6. Why The Validator Layer Is Split

The validator layer is now organized into three files:

- `src/AffineValidator.v`
- `src/TilingValidator.v`
- `src/Validator.v`

This split is not cosmetic.

### 5.1 `AffineValidator.v`

This file owns:

- affine-only well-formedness checks
- affine-only validation
- the witness-aware generic validator core

The generic validator core is there because schedule/dependence reasoning is
still largely the same once the program has been imported into the right
representation. The important point is that this generic core is *not* by itself
the full tiling validator.

### 5.2 `TilingValidator.v`

This file owns:

- conversion between the outer `PolyLang` view and the internal tiling model
- canonical tiled import
- the full checked tiling validator
- the bridge from checked tiling to codegen

This is where the tiling-specific structure lives. Keeping it out of the affine
validator prevents tiling-specific proof obligations from polluting the older
affine core.

### 5.3 `Validator.v`

This file is a public aggregator. It re-exports:

- affine validator names
- general witness-aware validator names
- checked tiling validator names

Its purpose is API stability. `PolOpt.v` should talk to `Validator.v`, not to a
mix of internal submodules.

## 7. Why `validate_general` Is Not The Tiling Validator

One point that caused repeated confusion is the role of `validate_general`.

`validate_general` is the witness-aware generic validator core. It is close to
the old affine validator because it is intentionally reusing the dependence and
permutability infrastructure.

But the *full* checked tiling validator is:

```text
check structural tiling relation
+ import canonical tiled after
+ run the generic validator core on the imported program
```

So:

- `validate_general` is a reusable component
- `checked_tiling_validate_poly` is the full checked tiling validator

### 7.1 Band-aware ordinary-tiling route

The repository now also contains a band-aware alternative ordinary-tiling
schedule validator in:

- [TilingBandScheduleValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingBandScheduleValidator.v)
- [PolOptBandTiling.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOptBandTiling.v)

This route is motivated by a presentation mismatch in the generic path:

- the default checked tiling route is correct and reusable
- but its schedule-legality story is intentionally generic
- for paper purposes, Pluto ordinary tiling is better explained in terms of
  inferred bands, strip-mined schedules, and permutable-band legality

The experimental route therefore factors the ordinary-tiling schedule proof
into:

1. recover the candidate tiled band from the witness
2. check the `after` schedule has the expected strip-mined form for that band
3. discharge the resulting band-specific legality obligation

This does not replace the existing generic validator architecture in the Coq
mainline theorem family. It is a more Pluto-shaped proof route kept alongside
the historical generic route, and it now drives the default frontend
ordinary-tiling path.

This separation exists so that:

1. the structural/witness relation is checked exactly once
2. the generic schedule/dependence machinery is reused rather than duplicated

## 8. Why A Witness-Centered `PolyLang` Is Necessary

Tiling changes the current point-space.

Before tiling, a statement instance can often be read as:

```text
env ++ point
```

After tiling, the current point-space becomes more like:

```text
env ++ tiles ++ point
```

The source semantics of the instruction, however, still want to talk about the
original source/base point-space.

This is why the current model needs:

- `pi_point_witness`
- `current_base_point_of`
- `current_src_args_of`

The witness is not an optimization-correctness proof. It is an internal
descriptor that says:

- what the current point-space is
- how to project it back to the source/base point-space

Without this layer, the code would again conflate:

- current-space structure
- source/base-space arguments
- access/dependence-space interpretation

That conflation was exactly what tiling forced the project to make explicit.

## 9. Why `current_view_pprog` Exists

`current_view_pprog` is one of the key architectural choices.

It is *not* another optimization pass. It is a representation bridge.

Its purpose is:

```text
witness-centered program
-> affine-style current-space program with identity witness
```

This is needed because the existing affine codegen theorems were already correct
and were written against an affine-style representation.

There were two possible strategies:

1. rewrite the entire codegen proof chain to reason directly about arbitrary
   witness-centered tiled programs
2. convert a checked tiled program into an affine-style current-space view and
   reuse the old codegen chain

The implementation chose the second option because it is both cleaner and more
robust:

- fewer affine theorems need to change
- the new tiling-specific reasoning stays local to the tiling pipeline
- the verified codegen route stays stable

## 10. Why `prepare_codegen` Was Kept

The current design deliberately keeps the older `prepare_codegen` structure in
place.

The reason is that `prepare_codegen` and codegen are not conceptually about
"affine only" versus "tiling". They are about converting a well-formed program
into the regularized representation expected by the code generator.

What changed is not the need for prepare/codegen. What changed is the proof
boundary in front of them:

- affine-only programs already fit the old codegen proof boundary directly
- checked tiled programs now pass through `current_view_pprog` first

This preserves the role of `prepare_codegen` without requiring a tiling-specific
prepare pass as a permanent architectural concept.

## 11. Why `PolOpt.v` Owns The Final Composition

The final optimizer composition lives in:

- `driver/PolOpt.v`

This is deliberate.

The shared theorem-carrying modules in `src/` should provide:

- validator definitions
- checker definitions
- correctness theorems
- conversion functions

But the actual optimizer policy, including fallback behavior, belongs in the
driver-level pipeline assembly.

That means:

- `PolOpt.v` decides when to try the phase pipeline
- `PolOpt.v` decides when to fall back
- `PolOpt.v` decides when to call `current_view_pprog`

Concrete instantiations such as `TPolOpt.v`, `CPolOpt.v`, and `SPolOpt.v` should
remain thin wrappers over this generic composition, with no duplicated proofs.

## 12. Why `export_for_pluto_phase_pipeline` Has A Dedicated Name

The old name `to_phase_openscop` was misleading because it suggested something
like:

- a tiling-specific operation
- or a special OpenScop unrelated to the normal scheduler path

What it actually means is:

- export the internal `PolyLang` program into the OpenScop form consumed by the
  dedicated two-stage Pluto phase pipeline

That is why the clearer name is:

- `export_for_pluto_phase_pipeline`

Similarly:

- `run_pluto_phase_pipeline`

is clearer than the older `phase_scop_scheduler`, because the two-stage Pluto
route does more than "schedule a scop". It returns the midpoint and tiled phase
results needed for the checked route.

## 13. Why Concrete Language Modules Should Stay Proof-Free

A core design goal is that concrete instantiations should not own proof logic.

They should only instantiate the generic interfaces with:

- an instruction language
- a loop language
- OpenScop import/export details
- printing/runtime adapters

This matters because otherwise the project risks re-creating proof architecture
three times:

- once for syntax-level examples
- once for trace-level tests
- once for C/OpenScop-level drivers

The current design keeps the proofs in the shared layer and leaves the concrete
modules as thin wrappers.

## 14. What The Current Design Intentionally Does Not Do

The current pipeline intentionally does **not** try to solve everything at once.

It does not attempt to:

- verify witness inference itself
- absorb ISS into the same validator route
- add full parallel semantics/codegen into the same proof step
- make every external Pluto mode part of the same checked path

Instead, it aims for one clean, working, verifiable route:

- affine scheduling
- checked tiling
- verified codegen

This narrowness is a feature, not a deficiency. It is what keeps the proof
boundary coherent.

## 15. Summary Of The Main Reasons

The current pipeline looks the way it does for four main reasons:

1. **Preserve the old affine proof investment.**
   The affine validator and affine codegen chain were already valuable and
   should not be destabilized unnecessarily.

2. **Make tiling explicit where it changes the model.**
   Tiling changes the point-space and therefore needs explicit witness-aware
   reasoning.

3. **Rejoin the old codegen route through normalization, not duplication.**
   `current_view_pprog` is the representation bridge that makes this possible.

4. **Keep the public optimizer route understandable.**
   `PolOpt.v` owns the final policy; the shared `src/` layer owns the reusable
   definitions and proofs.

That is the current verified pipeline design in its intended form.
