# `polopt` Strict-Path Failure Analysis

Date: 2026-03-08

## Current state
- Current strict proved-path result: `62 / 62`
- There is no remaining semantic blocker in the regression suite.

## Historical blockers that were resolved

### 1. Source scattering exporter bug
- `schedule_to_source_like_rows` used to drop a middle dynamic schedule
  dimension.
- Effect:
  - source `before.scop` no longer matched the C-path scheduling problem
  - Pluto solved the wrong source scheduling problem
- Resolution:
  - fix the exporter so all dynamic source schedule dimensions are preserved

### 2. Missing parameter-only domain strengthening
- Some cases needed parameter-only rows that are logically implied by the
  iterator bounds of the statement domain.
- Effect:
  - Pluto chose a different optimized schedule family on the weaker source
    domain
- Resolution:
  - strengthen statement domains before export
  - do not treat those rows as global program assumptions

### 3. Broken compact/pad schedule design
- The old compact design removed zero rows locally per statement.
- Effect:
  - it destroyed the program-wide shared schedule skeleton
  - multi-statement cases such as `mxv` and `mxv-seq3` failed even though
    `Validator` itself was not the bug
- Resolution:
  - preserve source-like schedule structure for export
  - import optimized schedules with `from_openscop_schedule_only`
  - canonicalize schedules with a program-wide row mask

### 4. `advect3d` performance
- `advect3d` was the last case that looked like a suite failure after the
  semantic blockers were fixed.
- Diagnosis:
  - not parser
  - not Pluto
  - not validator
  - almost all cost was in `CodeGen.codegen`
- Resolution:
  - treat it as a codegen performance issue, not a semantic blocker
  - with a realistic timeout budget it succeeds on the strict path

### 5. Clean-build discipline correction
- The earlier clean-build failure was not related to VPL.
- The real issue was:
  - `make depend` had been run outside `opam exec`
  - `coqdep` was missing from PATH
- Clean rebuild now succeeds under:
  - `make clean`
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`

## What did not become the repair path
- `Validator` was not modified as a fix.
- No validation-only runtime branch was introduced.
- The runtime path stayed aligned with the proved path.

## Oracle discipline
- Do not use cross-source `polcert(our_before, c_before)` or
  `polcert(our_after, c_after)` as an equality oracle.
- OpenScop metadata differs by origin.
- Use the C-path Pluto route as the behavioral oracle:
  - compare raw Pluto `before.scop` / `after.scop`
  - compare `SCATTERING` metadata and optimization family
  - require the strict proved path to succeed on our route
