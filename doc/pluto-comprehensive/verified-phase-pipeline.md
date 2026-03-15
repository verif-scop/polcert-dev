# Verified Phase Pipeline

This note records the final naming and layering of the verified affine+tiling
pipeline. The goal is to avoid the ambiguity that accumulated while the tiling
proofs were being integrated into the older affine-only code path.

For the detailed design rationale behind this pipeline shape, see:

- [verified-pipeline-design.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/verified-pipeline-design.md)

## Main idea

There are two different Pluto-facing routes in the codebase:

1. The older affine-only scheduler route
2. The newer two-stage Pluto phase route

Both may ultimately invoke Pluto, but they are not the same interface and they
do not carry the same proof obligations.

The verified optimizer in `driver/PolOpt.v` now makes this distinction explicit:

- affine-only route:
  - external affine scheduler
  - affine validator
  - verified codegen
- two-stage Pluto phase route:
  - export to the OpenScop view expected by the two-stage Pluto driver
  - run Pluto affine phase, then Pluto tiling phase
  - re-import the affine midpoint
  - affine validation on `before -> mid`
  - checked tiling validation on `mid -> after`
  - `current_view_pprog`
  - verified codegen

If any tiling-phase-specific step fails, the optimizer falls back to the
affine-only verified route. This is a fallback from the *two-stage phase
pipeline* to the *affine-only pipeline*, not from "Pluto" to "non-Pluto".

## Naming table

The historical names are still kept as compatibility aliases in a few places,
but the code should now be read using the names below.

### Pluto / scheduler boundary

- `affine_scheduler`
  - historical alias: `scheduler`
  - meaning: the older affine-only external scheduler contract

- `export_for_pluto_phase_pipeline`
  - historical alias: `to_phase_openscop`
  - meaning: export a `PolyLang` program to the OpenScop view consumed by the
    external two-stage Pluto phase pipeline

- `run_pluto_phase_pipeline`
  - historical alias: `phase_scop_scheduler`
  - meaning: run Pluto affine scheduling first, then Pluto tiling, and return
    `(mid_scop, after_scop)`

### Affine validation

- `check_wf_polyprog`
  - affine-only wf checker

- `validate`
  - affine-only schedule validator

- `checked_affine_schedule`
  - historical alias: `scheduler'`
  - meaning: call the affine scheduler and immediately validate its result

### General witness-aware validation

- `check_wf_polyprog_general`
  - historical alias: `check_wf_polyprog_tiling`
  - meaning: the shared witness-aware wf checker used by the tiling/current-space
    validator core

- `validate_general`
  - historical alias: `validate_tiling`
  - meaning: the shared witness-aware schedule/dependence validator core
  - important: this is **not** the full checked tiling validator by itself

### Checked tiling validation

- `to_tiling_pprog`
  - historical alias: `outer_to_tiling_pprog`
  - meaning: change representation from the generic outer `PolyLang` program to
    the internal tiling-model `PolyLang`

- `from_tiling_pprog`
  - historical alias: `tiling_to_outer_pprog`
  - meaning: the inverse representation change

- `import_canonical_tiled_after_poly`
  - historical alias: `import_canonical_tiled_after_outer`
  - meaning: build the canonical tiled skeleton from `(before, witness)` and
    import Pluto's final `after.scop` schedule over that skeleton

- `checked_tiling_validate_poly`
  - historical alias: `checked_tiling_validate_outer`
  - meaning: the full checked tiling validator on the generic outer `PolyLang`
    type
  - structure:
    1. structural/witness checker
    2. shared witness-aware validator core on the imported tiled program

## `current_view_pprog`

`current_view_pprog` is not another optimization pass. It is the bridge from a
witness-centered program to an affine-style program whose transformation is
already expressed directly on the current point-space.

This is the step that lets the old affine codegen theorems be reused after
checked tiling validation succeeds.

## File structure

Validator-related files are now organized by role:

- `src/AffineValidator.v`
  - affine-only validator core
  - shared witness-aware validator core (`validate_general`)

- `src/TilingValidator.v`
  - checked tiling validator
  - tiling-model conversion helpers
  - checked tiling + codegen bridge

- `src/Validator.v`
  - thin public aggregator
  - re-exports the stable public interface used by `PolOpt`

`driver/PolOpt.v` is the only place that assembles the final verified optimizer
pipeline. Concrete language instantiations (`TPolOpt.v`, `CPolOpt.v`,
`SPolOpt.v`, `STilingOpt.v`, `TPolValidator.v`) are intentionally thin wrappers.

## Final `PolOpt` route

The final verified route for programs with loop dimensions is:

1. extract and strengthen
2. try the two-stage Pluto phase pipeline
3. if the affine phase import/validation succeeds:
   - try witness inference
   - try canonical tiled import
   - try checked tiling validation
4. if the checked tiling route succeeds:
   - codegen `current_view_pprog after`
5. otherwise:
   - fall back to the affine-only verified route

Programs with no loop dimensions bypass Pluto and go directly to
`prepared_codegen`.
