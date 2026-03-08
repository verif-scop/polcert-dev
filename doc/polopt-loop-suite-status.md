# Polopt Loop Suite Status

Date: 2026-03-08

## Objective
- Run the generated Pluto benchmark `.loop` suite through the strict proved `polopt` path.
- Match the C-path Pluto scheduling problem and optimization behavior as closely as possible.

## Current strict status
- Total generated cases: `62`
- Current strict result: `62 / 62`
- Current strict proved path succeeds on the full generated suite.

## Non-blocker performance case
- `advect3d` is no longer treated as a semantic blocker.
- The full `polopt` run is slow because `CodeGen.codegen` is slow on that case.
- Pluto and validator are both fast enough.

## Current mxv-class repair conclusion
- The last real blocker was the `mxv` / `mxv-seq3` class.
- Root cause: local per-statement compaction lost the program-wide shared schedule skeleton.
- Effective repair:
  - preserve source-like export shape
  - import optimized schedules with `from_openscop_schedule_only`
  - canonicalize imported schedules with a program-wide row mask
- This repair restored the full strict suite to `62 / 62` without changing `Validator` and without adding a validation-only branch.

## Current generated artifacts
- Inputs: `tests/polopt-generated/inputs/*.loop`
- Per-case outputs: `tests/polopt-generated/cases/<case>/`

## Current acceptance criterion
A benchmark is only considered really done when:
1. strict `polopt` succeeds on the true proved path
2. the source `before.scop` matches the C-path scheduling problem closely enough
3. Pluto produces the same essential optimization family on both paths

## Important constraints
- Do not modify `Validator` as a repair path.
- Do not add validation-only runtime branches.
- Keep runtime path aligned with the proved path.
