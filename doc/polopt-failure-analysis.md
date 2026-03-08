# `polopt` Strict-Path Failure Analysis

Date: 2026-03-08

Scope:
- strict runtime path only
- `polopt` runs the proved path directly
- suite root: `/polcert/tests/polopt-generated`

All `62 / 62` benchmarks now have semantics-preserving `.loop` inputs.

The old `8 / 62` failing set is no longer current after the latest
source-scattering exporter fix.

Two previously failing cases already recovered:
- `fusion1`
- `multi-stmt-stencil-seq`

The blockers that are now firmly classified are:
- `mxv`
- `mxv-seq3`
- `advect3d`

All current failures stop in the same outer phase:
- scheduler validation
- user-visible error: `Scheduler validation failed.`

For every failing supported case:
- `validate(extracted, extracted) = true`

## Current split

### A. `mxv` and `mxv-seq3`: raw/source vs complete/padded schedule representation mismatch

Current facts:
- `validate(strengthened, roundtrip-before) = true`
- `validate(complete-before, complete-after)` has `eqdom=true` and `res=true`
- `validate(strengthened, scheduled)` still has `res=false`
- the imported optimized compact schedule for statement 2 is `[1; i; j]`
- the complete/padded optimized view uses the same compact schedule

Interpretation:
- this is no longer a simple importer bug
- the remaining mismatch is between:
  - the strengthened raw/source schedule representation
  - and the complete/padded validation representation
- the validator accepts the optimized schedule in the complete view, but rejects
  it in the raw/source view
- `mxv-seq3` shows the same pattern:
  - `validate(strengthened, roundtrip-before) = true`
  - `validate(complete-before, complete-after)` has `eqdom=true` and `res=true`
  - `validate(strengthened, scheduled)` still has `res=false`

### B. `advect3d`: no longer a source-fidelity mismatch

After the source-scattering exporter fix:
- source `before.scop` scattering metadata matches the C-path extractor shape
- `advect3d` should no longer be classified with the old source-model
  mismatches

Current observation:
- `--debug-scheduler` reaches and prints the extracted source OpenScop
- the remaining issue happens downstream of source export
- this currently looks more like scheduler/import runtime cost or a later
  representation problem than a source extractor mismatch

## What changed after extending the frontend language

The old mixed bucket is gone. The current failure set is now cleaner because:

- `/` is preserved end-to-end instead of being rewritten to `*`
- pure calls are preserved
- ternary expressions are preserved
- float literals are preserved as exact text

Interpretation:
- remaining failures are no longer frontend expression-language gaps
- they are true optimizer-path failures on semantics-preserving inputs

## What changed in the diagnosis

The old "nine remaining failures" picture is no longer current.

Two earlier issues were already removed:
- source-scattering exporter bug that dropped a middle dynamic schedule dimension
- missing source-domain strengthening on parameter-only guards

After those fixes, the remaining failures no longer support a single explanation.
The real split is now:
- schedule representation mismatch (`mxv`)
- downstream runtime/representation cost after source export (`advect3d`)

## Practical next steps

1. Do not regress the strengthened true proved path while fixing `mxv`.
2. For `mxv`, compare the raw/source validation view and complete/padded validation view until the exact representation mismatch is isolated.
3. For `advect3d`, measure where the cost appears after source export instead of continuing to treat it as a source-fidelity bug.
