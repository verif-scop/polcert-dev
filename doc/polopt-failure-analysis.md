# `polopt` Strict-Path Failure Analysis

Date: 2026-03-07

Scope:
- strict runtime path only
- `polopt` runs the proved path directly
- suite root: `/polcert/tests/polopt-generated`
- failures: `17 / 62`

All current failures stop in the same outer phase:
- scheduler validation
- user-visible error: `Scheduler validation failed.`

But there are two materially different subcases.

## Phase split

For every failing case:
- `validate(extracted, extracted) = true`

So the source polyhedral model is internally well-formed.

The split is:

1. `roundtrip-before` already fails
- `validate(extracted, roundtrip-before) = false`
- the source-aware OpenScop export/import path is already not idempotent before Pluto changes the schedule

Cases:
- `adi`
- `corcol`
- `corcol3`
- `dct`
- `doitgen`
- `pca`

2. `roundtrip-before` succeeds, but `scheduled` fails
- `validate(extracted, roundtrip-before) = true`
- `validate(extracted, scheduled) = false`
- the source model survives a no-op roundtrip, but the scheduled result is rejected

Cases:
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

Additionally, every failing case also differs from the original C/Clan source model:
- comparing our extracted source scop against `tests/pluto-all/<case>/<case>.beforescheduling.scop`
- `polcert` returns `NE` for all `17 / 17`

So even the “roundtrip-before true” cases are only self-consistent with our own source model, not with the original C path.

## Root-cause buckets

There are three recurring failure causes.

### A. Source-model semantic approximation in the `.loop` generator

The generator in `tests/polopt-generated/tools/generate_pluto_loops.py` is intentionally lossy:
- division is rewritten as multiplication
- `sqrt` and other calls collapse to read-based approximations
- ternaries collapse to read-based approximations

This directly changes the source polyhedral model before extractor ever runs.

Cases strongly affected:
- `adi`
- `corcol3`
- `lu`
- `pca`
- `trisolv`

Likely affected in a smaller way:
- `corcol`
- `covcol`

### B. Missing or weaker source-domain constraints than the C/Clan path

A representative example is `covcol`.
Its source schedule skeleton matches the C path modulo renaming, but our exported source scop is weaker:
- it omits parameter-only guards such as `M - 1 >= 0` and `N - 1 >= 0`

This means Pluto is optimizing a weaker source domain than the original benchmark.

This same pattern is likely present in other cases where:
- `T(S...)` looks structurally similar
- but `polcert` still reports `NE`

Cases that likely belong here:
- `covcol`
- `ssymm`
- `tricky1`
- `trisolv`

### C. Different statement-order / source-schedule skeleton than the C extractor

Here the failure is not a minor guard mismatch.
The source model fed to Pluto is structurally different from the one Clan/Pluto gets from the original C benchmark.

This shows up clearly in Pluto’s own `T(S...)` summary.

Typical symptoms:
- statement-order constants are reversed
- imperfect nests are not expanded into the same affine source schedule
- multi-statement kernels use a different statement-order skeleton

Cases:
- `advect3d`
- `corcol`
- `corcol3`
- `doitgen`
- `fusion1`
- `fusion8`
- `jacobi-1d-imper`
- `jacobi-2d-imper`
- `lu`
- `multi-stmt-stencil-seq`
- `pca`

## Case-by-case notes

- `adi`
  - stage: roundtrip-before already fails
  - source-model issue: generator rewrites division; our extracted source scop also makes `pluto --readscop` abort, so the boundary model is not even stable enough for Pluto’s own reader
  - comparison to C path: strongly different source schedule structure

- `advect3d`
  - stage: scheduled-only failure
  - source-model issue: roundtrip is self-consistent, but our source schedule makes all four statements share the same `(j,i,k)` skeleton
  - C path difference: Clan/Pluto extracts `S4` with shifted structure `(j+1, i+1, k+1)`

- `corcol`
  - stage: roundtrip-before already fails
  - source-model issue: imperfect multi-statement source schedule is very different from the C path; parameter/domain information is also weaker
  - C path difference: clean four-statement ordering `(3,0,1,2)` versus our zero-heavy constant layout

- `corcol3`
  - stage: roundtrip-before already fails
  - source-model issue: generator approximates `sqrt` / ternary / division; statement skeleton also differs
  - C path difference: eight statements are extracted in a different order and with different constants

- `covcol`
  - stage: scheduled-only failure
  - source-model issue: roundtrip is stable and the `T(S...)` skeleton matches the C path modulo renaming
  - C path difference: our domain is weaker because parameter-only guards are missing; `polcert` still reports `NE`

- `dct`
  - stage: roundtrip-before already fails
  - source-model issue: our source scop makes `pluto --readscop` abort; this is an OpenScop/source-model fidelity problem before scheduling
  - C path difference: original benchmark has a stable five-statement source model

- `doitgen`
  - stage: roundtrip-before already fails
  - source-model issue: statement-order constants are collapsed into a zero-heavy source skeleton rather than the clean `0/1/2` structure seen by Clan
  - C path difference: source `T(S...)` differs materially

- `fusion1`
  - stage: scheduled-only failure
  - source-model issue: self-roundtrip is stable
  - C path difference: statement-order constants are reversed
    - ours: `S1 = (i+1,1)`, `S2 = (i,0)`
    - C: `S1 = (i,0)`, `S2 = (i+1,1)`

- `fusion8`
  - stage: scheduled-only failure
  - source-model issue: self-roundtrip is stable
  - C path difference: same reversal pattern as `fusion1`

- `jacobi-1d-imper`
  - stage: scheduled-only failure
  - source-model issue: our model is self-consistent but stays close to the direct `(t,i)` loop structure
  - C path difference: Clan/Pluto extracts the imperfect nest into a time-expanded affine source schedule of the form `(2t-i, 2t+i)` / `(2t-j+1, 2t+j+1)`

- `jacobi-2d-imper`
  - stage: scheduled-only failure
  - source-model issue: same pattern as `jacobi-1d-imper`
  - C path difference: the original C extractor uses a time-expanded affine embedding that our `.loop` source model does not reproduce

- `lu`
  - stage: scheduled-only failure
  - source-model issue: generator rewrites division; source model is self-consistent but not equivalent to the C path
  - C path difference:
    - ours `S1`: `(k, j, 0)`
    - C `S1`: `(k, j, k)`
  - this loses a dependence-carrying source coordinate

- `multi-stmt-stencil-seq`
  - stage: scheduled-only failure
  - source-model issue: self-roundtrip is stable
  - C path difference:
    - C uses monotone statement constants `(i,0), (i+1,1), ..., (i+4,4)`
    - ours reorders them as `(i+1,4), (i,0), (i+1,1), (i+2,2), (i+3,3)`

- `pca`
  - stage: roundtrip-before already fails
  - source-model issue: generator approximates `sqrt` / ternary / division; our source scop also makes `pluto --readscop` abort
  - C path difference: very large multi-statement source model with different ordering and statement decomposition

- `ssymm`
  - stage: scheduled-only failure
  - source-model issue: self-roundtrip is stable
  - C path difference: `T(S...)` matches modulo renaming, so the remaining mismatch is likely in domain/access/context details rather than statement-order skeleton

- `tricky1`
  - stage: scheduled-only failure
  - source-model issue: self-roundtrip is stable
  - C path difference: `T(S...)` matches modulo renaming, so this again looks like a lower-level source-model mismatch rather than a schedule-skeleton mismatch

- `trisolv`
  - stage: scheduled-only failure
  - source-model issue: generator rewrites division; self-roundtrip is stable
  - C path difference: `T(S...)` is close modulo renaming, so the remaining mismatch is likely in access/domain semantics rather than statement-order structure

## What this says about the current extractor/frontend boundary

The remaining failures are not one single bug.
They are a mixture of:

1. lossy `.loop` generation from C benchmarks
2. missing source-domain guards in the exported source scop
3. incorrect source-schedule skeleton for imperfect or multi-statement kernels
4. a smaller residual class where the source schedule skeleton matches, but the full source polyhedral model still differs in access/domain/context details

## Practical next steps

1. Fix generator fidelity first
- stop rewriting `/` as `*`
- stop collapsing `sqrt` and ternary expressions into read-only approximations

2. Fix source-domain export fidelity
- preserve parameter-only guards in the exported scop

3. Fix source schedule skeletons for imperfect nests
- especially:
  - `jacobi-1d-imper`
  - `jacobi-2d-imper`
  - `multi-stmt-stencil-seq`
  - `fusion1`
  - `fusion8`

4. Re-run strict suite after each source-model fidelity improvement
- the current `45 / 62` should be treated as the strict proved-path baseline
