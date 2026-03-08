# Source Model Fidelity Goal

Date: 2026-03-08

## Goal
The target is not merely:
- `polopt` succeeds
- validator accepts the scheduled poly

The stronger target is:
- `extractor + to_openscop` should encode the same source scheduling problem that the C/Clan/Pluto path sees
- Pluto should therefore produce the same optimization family on both paths

## What counts as "aligned"
For a benchmark to count as aligned with Pluto:
1. source `before.scop` should match the C-path scheduling problem as closely as possible
2. Pluto should produce the same essential optimized schedule family
3. strict `polopt` should still succeed on the true proved path

## Current state
- Most earlier source-model/exporter bugs have been removed.
- `advect3d` is no longer a semantic blocker; its remaining issue is `CodeGen.codegen` runtime.
- The previous live semantic blockers `mxv` and `mxv-seq3` are now fixed on the proved path.
- Current strict proved-path suite result is `62 / 62`.
- Current raw Pluto family comparison is also aligned on the generated suite:
  - raw strengthened `before.scop` matches the C-path Pluto raw `before.scop`
    on `SCATTERING` metadata across all `62`
  - raw Pluto `after.scop` matches the C-path Pluto raw `after.scop`
    on `SCATTERING` metadata across all `62`

## Current `mxv` repair conclusion
- `mxv` / `mxv-seq3` exposed the real compact/pad design bug.
- The key point is not that validator needed a special case.
- The key point is:
  - local per-statement compaction lost the program-wide shared schedule skeleton
  - zero rows are not mere formatting in multi-statement programs
  - they carry cross-statement timestamp alignment
- Effective repair:
  - export source-like schedule shape
  - import optimized schedules with `from_openscop_schedule_only`
  - canonicalize schedules with a program-wide row mask
- Result:
  - `mxv` and `mxv-seq3` now pass
  - full strict proved-path suite is `62 / 62`

## Current conclusion
- The source-model fidelity target is currently met at the structural level we
  have been using as the oracle:
  - same source scheduling problem shape
  - same optimized schedule family shape
  - strict proved path succeeds
- Remaining work, if any, is no longer about generated-suite blocker recovery;
  it would be about strengthening the argument or broadening the benchmark set.

## What not to do
- do not repair this by changing `Validator`
- do not add a validation-only runtime branch
- do not drift away from the proved pipeline

## Current debugging unit
For schedule-representation issues, the right comparison unit remains:
1. strengthened source poly
2. source `before.scop`
3. Pluto raw `after.scop`
4. source-aware imported scheduled poly
5. complete-view imported scheduled poly
