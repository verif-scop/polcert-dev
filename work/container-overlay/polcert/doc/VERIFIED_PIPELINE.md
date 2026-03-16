# Verified Pipeline

This note records the current verified `polopt` / `polcert` pipeline shape at a
high level. It is intentionally short and only explains the stages that tend to
be confusing after the tiling extension.

## Main idea

The repository now has one verified optimizer pipeline with two validated
optimization routes:

- an affine scheduling route
- a phase-aligned tiling route layered on top of affine scheduling

The affine route remains the stable baseline. The tiling route is used when the
external two-phase Pluto pipeline succeeds and its outputs can be imported and
checked.

## `polopt`

The optimizer pipeline is:

```text
.loop
-> extract
-> strengthen
-> checked affine schedule
-> optional checked tiling phase
-> current_view_pprog
-> prepare_codegen
-> codegen
-> cleanup
```

The main stages are:

- `Extractor.extractor`
  Builds the internal polyhedral model from the structured loop fragment.
- `StrengthenDomain.strengthen_pprog`
  Makes implicit parameter/domain facts explicit so later validation and code
  generation operate on a more precise representation.
- checked affine schedule
  Runs Pluto's affine scheduling result and validates it with the verified
  affine validator.
- optional checked tiling phase
  Runs the phase-aligned tiling route. This route checks the imported tiling
  witness and then reuses the generic validator core on the canonical imported
  tiled program.
- `current_view_pprog`
  Materializes the witness-centered program as an explicit current-space affine
  view so the existing affine codegen story can be reused without teaching the
  full code generator about every witness form.
- `prepare_codegen`
  Normalizes matrix shapes and tail dimensions into the regular form expected by
  code generation. This is a formatting and regularization pass, not another
  optimization pass.
- `CodeGen.codegen`
  Produces loop code from the validated polyhedral program.
- cleanup
  Removes singleton loops and performs small structural cleanups on the
  generated loop tree.

If the tiling-specific route fails at any stage, the optimizer falls back to
the already-validated affine result instead of failing the whole pipeline.

Current strict-suite snapshot:

- total generated inputs: `62`
- successful runs: `62`
- changed outputs: `60`
- nontrivially changed outputs: `60`
- automatically detected tiled outputs: `38`

Representative visible outcomes:

- `covcol` remains the standard affine-scheduling example
- `matmul-init` is now a compact explicit tiling example with extra tile loops,
  `max/min` strip-mined bounds, and visible `/ 32` tile-size arithmetic

## `polcert`

`polcert` now exposes three practically important validation modes:

- direct affine validation of `before.scop -> after.scop`
- tiling-only validation of `mid.scop -> after.scop` with `--kind tiling`
- phase-aligned validation of `before -> mid -> after`

The phase-aligned route checks:

1. `before -> mid` with the affine validator
2. `mid -> after` with the checked tiling validator

## Why there are several normalization stages

The tiling extension introduced a point-space witness layer. That means a
program can carry both:

- its current iteration-space coordinates
- the source/base coordinates used by instruction semantics

Because of that, the pipeline needs several distinct "format-fixing" stages:

- strengthening
  Improves domain precision before any external scheduling step.
- canonical tiling import
  Rebuilds the imported tiled program into the canonical internal form expected
  by the checked tiling validator.
- `current_view_pprog`
  Eliminates witness indirection by materializing explicit current-space
  transformations.
- `prepare_codegen`
  Regularizes the program for code generation.

These stages are not duplicates; they solve different representation problems.

## Proof boundary

The proved core includes:

- extraction into the internal polyhedral model
- affine validation
- checked tiling validation
- current-view conversion
- prepare-codegen
- code generation
- cleanup

The unproved parts remain:

- Pluto itself
- OpenScop parsing and printing details
- witness inference from external phase outputs
- frontend parsing of `.loop` text
