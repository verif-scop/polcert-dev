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
- Current raw Pluto family comparison is also aligned on the regression suite:
  - raw strengthened `before.scop` matches the C-path Pluto raw `before.scop`
    on `SCATTERING` metadata across all `62`
  - raw Pluto `after.scop` matches the C-path Pluto raw `after.scop`
    on `SCATTERING` metadata across all `62`

## Current domain mismatch pattern
The residual raw `before.scop` mismatch is no longer in `SCATTERING`. It is in
source `DOMAIN` metadata.

Important scope note:
- the checked-in raw comparison report currently uses `polopt --extract-only`
- so it is measuring the pure extractor source model, not the strict proved-path
  source model after `StrengthenDomain`
- this means the report is still useful for structural trend analysis, but it
  underestimates the fidelity of the actual strict path

Representative cases show that the extra C-path rows are parameter-only guards
that express non-emptiness of iterator bound intervals:

- `covcol`
  - extra rows: `M-1 >= 0`, `N-1 >= 0`
- `costfunc`
  - extra rows: `N-1 >= 0`, `N-2 >= 0`
- `mxv`
  - extra rows: `N-1 >= 0`
- `matmul`
  - extra rows: `M-1 >= 0`, `N-1 >= 0`, `K-1 >= 0`
- `advect3d`
  - extra rows such as `ny+3 >= 0`, `nx+2 >= 0`, `nz+2 >= 0`
  - more generally: upper-bound minus lower-bound for each iterator

This supports the current interpretation:

- the remaining domain gap is statement-domain strengthening
- not a source `SCATTERING` problem
- and not a reason to introduce global context assumptions

Direct confirmation:
- `covcol` under `./polopt --debug-scheduler` already emits a strengthened
  source OpenScop whose `DOMAIN` row counts match the C-path

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

## Strengthened before / raw after full comparison
A full-suite comparison was run using the strict proved-path source model:
- our path: `polopt --debug-scheduler` and slice `== Debug Extracted OpenScop ==`
- then run raw `pluto --readscop` on that strengthened `before.scop`
- compare against the C-path raw Pluto `after.scop`

Current result on the regression suite:
- strengthened `before.scop` `SCATTERING` metadata match: `62 / 62`
- strengthened `before.scop` `DOMAIN` metadata match: `52 / 62`
- raw Pluto `after.scop` `SCATTERING` metadata match: `62 / 62`
- the remaining `10` mismatches are still only in `DOMAIN` metadata

The `10` residual `DOMAIN` mismatches are:
- `fusion10`
- `fusion2`
- `fusion3`
- `fusion4`
- `fusion8`
- `lu`
- `nodep`
- `ssymm`
- `strsm`
- `trisolv`

Important interpretation:
- these residual `DOMAIN` mismatches do **not** currently change the optimization family on the suite
- for all `10`, the raw Pluto `after.scop` `SCATTERING` metadata still matches the C-path raw `after.scop`
- so the remaining fidelity gap is narrower than before: it is a residual domain-shape / strengthening mismatch, not an optimization-family mismatch on the current suite

## Residual domain mismatch classification
The remaining `10` `DOMAIN` metadata mismatches do not all have the same cause.
They currently split into two practical classes:

### A. Tautological / obviously redundant extras on our side
These do not change the optimization family and look like over-eager strengthening:
- `fusion10`
- `fusion2`
- `fusion3`
- `fusion4`
- `fusion8`
- `nodep`

Representative pattern:
- our strengthened domain emits an extra constant-only row such as `1 >= 0`, `99 >= 0`, or `3 >= 0`
- the C-path extractor omits these tautologies

### B. Nontrivial strengthening / normalization mismatch
These still differ from the C-path in a more meaningful domain-shape sense, even though the raw Pluto `after.scop` scattering family already matches on the current suite:
- `lu`
- `ssymm`
- `strsm`
- `trisolv`

This class currently splits again:
- inner-range non-emptiness strengthening:
  - `lu`
  - `ssymm`
  - `trisolv`
- guard/singleton normalization difference:
  - `strsm`

Representative patterns:
- `lu`
  - C-path adds rows like `N-1 >= 0` and `-k+N-2 >= 0`, making explicit that the `j=k+1..N-1` and `i=k+1..N-1` domains are nonempty only when those inequalities hold
- `ssymm`
  - C-path adds rows like `j-2 >= 0`, corresponding to non-emptiness of the inner `k=0..j-2` range
- `trisolv`
  - same pattern as `ssymm`, with `j-1 >= 0` / inner-range non-emptiness made explicit
- `strsm`
  - C-path normalizes the guard `k == i+1` as an equality row `-i+k-1 == 0`
  - our current strengthened domain still represents the same effect via inequality-style domain rows

Important interpretation:
- this is now a domain normalization / strengthening-rule gap
- not a remaining source `SCATTERING` issue
- and not an optimization-family blocker on the regression suite

## Likely next strengthening generalization
Current `StrengthenDomain` only keeps pairwise-added guards that are parameter-only.
That is enough to recover the suite, but it does not yet match all C-path domain normalizations.

The remaining four nontrivial domain mismatches suggest a more general, still-structured rule:
- eliminate the current innermost iterator from a bound pair
- keep the resulting guard if it depends only on outer iterators and parameters

This matches the observed residual cases:
- `lu`
  - from `j >= k+1` and `j <= N-1`, derive `N-k-2 >= 0`
- `ssymm`
  - from `k >= 0` and `k <= j-2`, derive `j-2 >= 0`
- `trisolv`
  - from `k >= 0` and `k <= j-1`, derive `j-1 >= 0`
- `strsm`
  - the guard `k == i+1` is better normalized as an equality row, rather than only as paired inequalities

So the current residual fidelity debt looks like:
- not a schedule problem
- not a validator problem
- a still-too-weak domain-strengthening / normalization rule

If we continue improving fidelity, the next coherent target is:
- a level-aware strengthening pass that can derive outer-iterator/parameter guards
- plus singleton/equality normalization when lower and upper bounds collapse

Current status of that direction:
- the suite-closing strengthening repair now implements the first half of this:
  - eliminate the current innermost iterator from a bound pair
  - retain only guards over outer iterators + parameters
- this was enough to restore the strict proved-path regression suite to `62 / 62`
- singleton/equality normalization remains a source-fidelity refinement task, not
  a current suite blocker
