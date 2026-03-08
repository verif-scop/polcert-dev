# Polopt Loop Suite Status

Date: 2026-03-08

Current objective:
- generate `.loop` versions for the Pluto benchmark suite without changing source semantics
- run the supported subset through the strict, proved `polopt` pipeline

Current generator and artifacts:
- generator script: `tests/polopt-generated/tools/generate_pluto_loops.py`
- generated input loops: `tests/polopt-generated/inputs/*.loop`
- per-case strict outputs: `tests/polopt-generated/cases/<case>/`

Current benchmark split:
- total Pluto benchmark cases seen by the generator: `62`
- semantics-preserving `.loop` inputs generated: `62`
- explicitly unsupported and therefore skipped: `0`

Current strict-path pass rate:
- current rerun with a 30s per-case timeout gives `59 / 62`
- current blocker set:
  - `advect3d` (`timeout`)
  - `mxv` (`Scheduler validation failed`)
  - `mxv-seq3` (`Scheduler validation failed`)

Per-case directory layout:
- `input.loop`: generated source input
- `input.pretty.loop`: normalized pretty-printed input, when optimization succeeded
- `optimized.loop`: optimized output loop, when optimization succeeded
- `diff.patch`: unified diff between normalized input and optimized output, when optimization succeeded
- `status.txt`: exit code and result metadata
- `stderr.txt`: failure diagnostics, when optimization failed

Current successful-but-unchanged set:
- `1dloop-invar`
- `dsyr2k`
- `dsyrk`
- `floyd`
- `nodep`
- `noloop`
- `strmm`
- `tmm`
- `tricky4`
- `wavefront`

What changed in this round:
- `.loop` generation is no longer allowed to silently change benchmark semantics
- syntax frontend now supports `/` in instruction RHS expressions
- syntax frontend now supports:
  - pure calls
  - ternary expressions
  - arbitrary-precision float literals
- `/=` is lowered as `x = x / y`
- calls/ternaries/floats are preserved instead of approximated or rejected
- source-aware OpenScop import now reliably round-trips the current source model:
- padded scattering detection accepts a nonzero tail constant row
- importer refills schedules from the source template while preserving structural zero constant slots
- source scattering export now preserves middle constant schedule rows in the OpenScop shape expected by Pluto/Clan for imperfect nests
- source scattering export now also preserves leading constant schedule dimensions without inserting a spurious zero row first
- true proved path now includes `StrengthenDomain`
- optimized OpenScop import now uses a hybrid strategy:
  - preserve source-template refill when Pluto's optimized scattering still matches the source-like family
  - fall back to compact/schedule-only import when refill would distort the optimized scattering

Newly recovered because `/` is now preserved rather than rewritten to `*`:
- `adi`
- `doitgen`
- `lu`
- `trisolv`

Newly supported and successful after frontend extension:
- `fdtd-2d`
- `floyd`

Important current interpretation:

1. Successful set
- these are genuine runs of the strict proved path:
  - `SPolOpt.opt = PreparedOpt.Opt`
- they are the trustworthy baseline for what the current optimizer actually handles

2. Current blocker split
- the old `8`-case split is stale after the latest source-scattering exporter fix
- `fusion1` and `multi-stmt-stencil-seq` now recover under the strict path
- `mxv` and `mxv-seq3` are now the clearest representation-sensitive failures:
  - complete/padded validation view accepts the optimized schedule
  - strengthened raw/source validation view still rejects it with `res=false`
- `advect3d` has moved out of the pure source-fidelity bucket:
  - source scattering metadata now matches the C-path extractor
  - remaining trouble is downstream of source export

3. Strengthening is necessary but not sufficient
- `StrengthenDomain` fixes the missing parameter-only guard issue on the previously failing six cases
- direct Pluto runs on strengthened source scop show that the raw optimized `after.scop` can already satisfy `polcert = EQ`
- the remaining failures are therefore downstream of source-domain strengthening, in optimized OpenScop import

Important runtime facts:
- `polopt` is on the strict proved path only; the CLI fallback exporter is gone
- `polcert` still uses `from_openscop_complete`
- `polopt` still uses the source-aware scheduler decode in `syntax/SPolIRs.v`

Reference analysis:
- [polopt-success-summary.md](./polopt-success-summary.md)
- [polopt-failure-analysis.md](./polopt-failure-analysis.md)
- [openscop-representation-gap.md](./openscop-representation-gap.md)

High-value next steps:
1. Keep the proved runtime path strict; do not reintroduce CLI-only fallbacks.
2. For the importer-only bucket (`corcol3`, `dct`, `gemver`, `mxv`, `pca`), continue refining optimized schedule import without regressing the successful source-like family cases.
3. For the raw-NE bucket (`advect3d`, `fusion1`, `multi-stmt-stencil-seq`), compare source `before.scop` against the C/Clan path and isolate the remaining source-model mismatch.
