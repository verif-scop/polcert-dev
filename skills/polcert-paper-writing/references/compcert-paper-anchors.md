# CompCert Paper Anchors

Use this note when writing or reviewing PolCert paper prose.

The point is not to copy the style of these papers mechanically. The point is
to preserve their discipline about what is proved, what is validated, and what
is merely implemented.

## 1. CompCert / Leroy 2009

Paper role in our workspace:

- baseline reference for end-to-end verified compilation
- anchor for "compiler as weak link" motivation
- anchor for semantic-preservation framing rather than piecemeal proof folklore

Rhetorical moves worth preserving:

- start with the trust problem, not just with optimization opportunity
- state exactly which source and target languages the compiler covers
- say what formal verification buys and for whom
- present usefulness claims in proportion to the actual theorem boundary

What this means for PolCert:

- motivate why verified polyhedral compilation matters as part of a longer
  trust chain from source loops to optimized loops
- do not claim "full-fledged" support in places where the theorem boundary is
  still narrower

## 2. Necula 2000

Paper role in our workspace:

- canonical translation-validation reference
- anchor for per-run checking instead of proving the whole optimizer

Rhetorical moves worth preserving:

- explicitly contrast global compiler proof with per-compilation validation
- explain what information the validator uses and what assumptions remain
- argue for practicality without pretending full proof where there is none

What this means for PolCert:

- when discussing affine rescheduling, tiling, ISS, or checked parallel routes,
  say what is checked on each optimizer run
- do not blur "validated optimizer proposal" into "proved optimizer algorithm"

## 3. Courant--Leroy 2021

Paper role in our workspace:

- direct predecessor for verified polyhedral code generation
- anchor for narrow but strong polyhedral theorem statements

Rhetorical moves worth preserving:

- define the polyhedral subpipeline under study precisely
- say sequential if the proved result is sequential
- make Coq mechanization a support claim, not a substitute for scope clarity

What this means for PolCert:

- if the default theorem is the ordinary sequential affine-plus-tiling route,
  keep saying that
- treat checked parallelization and checked diamond routes as additional,
  narrower stories unless and until the theorem boundary catches up

## 4. Local PolCert risk list

These are the paper-specific places where overclaiming is most likely:

- diamond tiling: implemented checked route exists, but it is not the default
  theorem baseline
- checked parallelization: strong story exists, but the main optimizer theorem
  remains narrower
- `li2024affine`: direct predecessor for affine-schedule validation, not for
  the whole pipeline
- theorem statements in `correctness.tex`: watch for free variables, missing
  preconditions, and underexplained success domains
- `StateEq` and cross-model refinement: if the paper says one judgment unifies
  multiple semantic layers, the observational contract must not stay implicit

## 5. Section-specific reminders

### Abstract / Introduction

- strongest temptation to overcompress maturity boundaries
- must match `correctness.tex`

### Related Work

- avoid generic "similar area" comparisons
- every sentence should answer: predecessor, nearby contrast, or boundary-setter?

### Correctness

- theorem statements should read as self-contained mathematical objects, not as
  chat shorthand

### Conclusion

- summarize exactly what the artifact proves today
- future work belongs after the proved boundary is clearly restated
