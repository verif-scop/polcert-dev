# Polopt Loop Suite Status

Date: 2026-03-07

Current objective:
- generate `.loop` versions for the Pluto benchmark suite
- run them through the strict, proved `polopt` pipeline

Current generator and artifacts:
- host generator script: `tests/polopt-generated/tools/generate_pluto_loops.py`
- generated input loops: `tests/polopt-generated/inputs/*.loop`
- per-case strict outputs: `tests/polopt-generated/cases/<case>/`

Current suite size:
- `62` generated `.loop` files

Current strict-path pass rate:
- `45 / 62` pass the default `./polopt file.loop`
- `17 / 62` fail

Current strict-path failing set:
- `adi.loop`
- `advect3d.loop`
- `corcol.loop`
- `corcol3.loop`
- `covcol.loop`
- `dct.loop`
- `doitgen.loop`
- `fusion1.loop`
- `fusion8.loop`
- `jacobi-1d-imper.loop`
- `jacobi-2d-imper.loop`
- `lu.loop`
- `multi-stmt-stencil-seq.loop`
- `pca.loop`
- `ssymm.loop`
- `tricky1.loop`
- `trisolv.loop`

Per-case directory layout:
- `input.loop`: generated source input
- `input.pretty.loop`: normalized pretty-printed input, when optimization succeeded
- `optimized.loop`: optimized output loop, when optimization succeeded
- `diff.patch`: unified diff between normalized input and optimized output, when optimization succeeded
- `status.txt`: exit code and result metadata
- `stderr.txt`: failure diagnostics, when optimization failed

Current comparison result:
- `43 / 45` successful cases currently have `changed=true`
- unchanged successful cases:
  - `nodep`
  - `noloop`

What was already fixed:
- extractor access bug:
  - extracted `pi_waccess/pi_raccess` must use `normalize_access_list`
  - not `normalize_access_list_rev`
- syntax frontend slot order:
  - `slot_env env = env.params @ env.loops`
  - `syntax_slot_names names = names`
- OpenScop zero-parameter printing:
  - `Some []` now prints the no-parameter form Pluto/OSL accepts
- scheduler Pluto flags:
  - restored README flags such as `--nointratileopt` and `--nodiamond-tile`
- scheduler-side source-aware decode:
  - syntax path uses `from_openscop_like_source`
- pretty-printer cleanup:
  - singleton `range(e, e+1)` loops print as let-like substitutions
  - expressions and tests are simplified before printing

Important current classification:

1. Roundtrip-before already fails
- `adi`
- `corcol`
- `corcol3`
- `dct`
- `doitgen`
- `pca`

Interpretation:
- the source-aware OpenScop export/import path is not idempotent even before Pluto changes the schedule
- these cases are not yet stable source models for the strict scheduler path

2. Roundtrip-before succeeds, but scheduled result fails
- `advect3d`
- `covcol`
- `fusion1`
- `fusion8`
- `jacobi-1d-imper`
- `jacobi-2d-imper`
- `lu`
- `multi-stmt-stencil-seq`
- `ssymm`
- `tricky1`
- `trisolv`

Interpretation:
- these cases are self-consistent under our own source-aware roundtrip
- but Pluto’s scheduled result is rejected by validator on the strict proved path

3. Comparison to original C path
- for all `17 / 17` failures:
  - our extracted source scop vs the benchmark’s original `*.beforescheduling.scop`
  - `polcert` returns `NE`

Interpretation:
- even the “roundtrip-before true” cases are only self-consistent with our own source model
- they are still not the same source model that Clan/Pluto extracts from the original C benchmark

Important debugging result:
- for the remaining failures, the root issue was not `eqdom` or `valid_access`
- the failing component is `res` inside validator
- this means:
  - domains, transformations, and access self-checks are accepted
  - the remaining failure is schedule/dependence validation

Important source-model results:
- `covcol` is representative of the “same schedule skeleton, weaker domain” bucket:
  - the extracted source scop misses parameter-only guards such as `M - 1 >= 0` and `N - 1 >= 0`
- `jacobi-1d-imper` and `jacobi-2d-imper` are representative of the “different source schedule skeleton” bucket:
  - Clan/Pluto extracts a time-expanded affine source schedule
  - the generated `.loop` model does not reproduce that structure
- `adi`, `dct`, and `pca` are representative of the “source scop not even stable enough for readscop/roundtrip” bucket

Important generator result:
- the current `.loop` generator is intentionally lossy on several constructs:
  - division is rewritten as multiplication
  - `sqrt` is collapsed
  - ternaries are collapsed
- this directly affects at least:
  - `adi`
  - `corcol3`
  - `lu`
  - `pca`
  - `trisolv`

Reference analysis:
- [polopt-success-summary.md](./polopt-success-summary.md)
- [polopt-failure-analysis.md](./polopt-failure-analysis.md)
- [openscop-representation-gap.md](./openscop-representation-gap.md)

High-value next steps:
1. Improve generator/source-model fidelity for imperfect nests and reductions.
2. Restore missing parameter-only domain guards in the exported source scop.
3. Recover the `11` scheduled-only failures by fixing the generic `SPolIRs.scheduler` path rather than reintroducing a CLI-only wrapper.
4. Re-run the full `62` benchmark suite after each change and keep this file updated.
