# Must Read

## Workspace layout
- Real code repo: `gifted_curie:/polcert` on branch `extractor`
- This outer workspace stores notes, logs, plans, and scratch context

## Proof state
- `src/Extractor.v`: `extractor_correct` is `Qed`
- `src/PrepareCodegen.v`: `prepare_codegen_semantics_correct` is `Qed`
- `driver/PolOptPrepared.v` exposes:
  - `Definition Opt := Opt_prepared`
  - `Theorem Opt_correct`
- `check-admitted` reports `Nothing admitted.`

## Runtime state
- `opam exec -- make test` is green
- `polcert` still uses `from_openscop_complete`
- `polopt` is back on the single proved path:
  - `syntax/SPolOpt.v: opt = PreparedOpt.Opt`
  - `syntax/SPolOpt.v: opt_poly = CoreOpt.scheduler' ; Prepare.prepared_codegen`
- `syntax/SInstr.v` now has a real lightweight store semantics:
  - `State.t := MemCell -> Z`
  - `SSkip` preserves state
  - `SAssign` functionally updates one `MemCell`

## Key runtime fixes already identified

### 1. Generic extractor fix
- In `src/Extractor.v`, extracted access functions must use:
  - `normalize_access_list`
- They must not use:
  - `normalize_access_list_rev`

This restored the official `CInstr` validation line and fixed `CSample2/covcol`.

### 2. Syntax-only follow-up
- `syntax/SInstr.v` had an outdated `access_function_checker`
- It only accepted:
  - raw access
  - reverse-normalized access
- After the extractor fix, syntax extractor output became:
  - plain normalized access
- The syntax checker now accepts:
  - raw
  - normalized
  - reverse-normalized

This restored:
- `validate(extracted, extracted) = true`
- `validate(extracted, roundtrip-before) = true`
- `validate(extracted, scheduled) = true`

on `covcol`

## Important non-conclusions
- The last `covcol` blocker was not a proof issue
- It was not a Pluto parameter issue
- It was not a validator-algorithm regression
- It was not necessary to keep the old normalized/raw split workaround in `syntax/SPolOpt.v`

## Current focus after recovery
- consolidate and commit the container fixes
- then move back up to output-shape cleanup / post-pass work if desired

## Reference note
- [doc/openscop-representation-gap.md](doc/openscop-representation-gap.md)
- [doc/polopt-loop-suite-status.md](doc/polopt-loop-suite-status.md)
- [doc/polopt-success-summary.md](doc/polopt-success-summary.md)
- [doc/polopt-failure-analysis.md](doc/polopt-failure-analysis.md)

- Read `doc/polopt-loop-suite-status.md` before continuing Pluto `.loop` suite work.
- Read `doc/polopt-success-summary.md` before making claims about what strict-path `polopt` is actually optimizing.
- Read `doc/polopt-failure-analysis.md` before debugging the remaining `17` failing cases.
- Read `doc/sinstr-semantics.md` before changing `syntax/SInstr.v` again.
- Current strict suite artifacts live under:
  - `tests/polopt-generated/inputs/*.loop`
  - `tests/polopt-generated/cases/<case>/`
- 2026-03-07 strict status:
  - `45 / 62` pass on the default proved path
  - strict failing set:
    - `adi`
    - `advect3d`
    - `corcol`
    - `corcol3`
    - `covcol`
    - `dct`
    - `doitgen`
    - `fusion1`
    - `fusion8`
    - `jacobi-1d-imper`
    - `jacobi-2d-imper`
    - `lu`
    - `multi-stmt-stencil-seq`
    - `pca`
    - `ssymm`
    - `tricky1`
    - `trisolv`
- The CLI fallback exporter is no longer in the default path.
- `SPolOpt.opt` now points back to `PreparedOpt.Opt`; any remaining failures are now on the true proved path, not on a wrapper path.
- `syntax/SLoopPretty.ml` now does display-only cleanup:
  - singleton `range(e, e+1)` loops print as let-like substitutions
  - loop/instruction expressions and tests are simplified before printing
