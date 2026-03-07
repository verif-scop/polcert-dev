# Extractor Depth and WF Spec

Date: 2026-03-05

## Why this note exists
Extractor proofs are currently slowed down by unstable dimension conventions.
This note defines the target convention for upcoming refactor/proofs.

## Symbols
- `env_dim := length varctxt`
- `iter_depth := number of surrounding loop iterators at an instruction`
- `cols := env_dim + iter_depth`

## Target Depth Convention
- `pi_depth` means **iterator depth only**.
- `pi_depth` must not include `varctxt` dimension.
- At an emitted instruction:
  - `pi_depth = iter_depth`
  - affine rows are interpreted in `cols = env_dim + iter_depth`.

## Target Row-Shape Invariants (per `pi`)
- Domain:
  - every row in `pi_poly` has exactly `cols` coefficients.
- Transformation:
  - every row in `pi_transformation` has exactly `cols` coefficients.
  - `length pi_transformation = cols`.
- Schedule:
  - every row in `pi_schedule` has exactly `cols` coefficients.
- Accesses:
  - every row in each access function has exactly `cols` coefficients.

These are exactly the shape assumptions checked by validator-side wf checks.

## Constructor-Level Rules
- `Instr` emission:
  - normalize each transformation row to `cols`.
  - emit `pi_depth = iter_depth`.
- `Loop` step:
  - convert lb/ub to domain constraints with width `env_dim + iter_depth + 1`
    for recursive body extraction.
  - append loop schedule row with the same width.
- `Seq` step:
  - sequence-position row must also have full width `cols`
    (constant row represented by zero coefficient vector of length `cols`).

## Current Mismatch to fix
- `exprlist_to_aff` currently ignores its `depth` argument and does not normalize row width.
- extractor currently uses `pi_depth := pred depth` with a mixed-depth state initialized by `length varctxt`.
- sequence schedule uses empty coefficient rows (`[]`) for position, which conflicts with strict fixed-column checks.

## Minimum acceptance criterion for refactor
- Add a lightweight post-condition theorem/check:
  - if extraction returns `Okk (pis, varctxt, vars)`,
  - then `forall pi in pis, check_wf_polyinstr pi varctxt vars = true`.
