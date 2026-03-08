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
- Read `doc/polopt-failure-analysis.md` before debugging the remaining strict-path failures.
- Read `doc/polopt-remaining-9-cases.md` before touching the remaining scheduler-validation failures.
- Read `doc/sinstr-semantics.md` before changing `syntax/SInstr.v` again.
- Read `doc/source-model-fidelity-goal.md` before evaluating `polopt` success claims against Pluto.
- Current strict suite artifacts live under:
  - `tests/polopt-generated/inputs/*.loop`
  - `tests/polopt-generated/cases/<case>/`
- 2026-03-08 current `.loop` suite status:
  - total Pluto benchmark cases: `62`
  - semantics-preserving generated `.loop` inputs: `62`
  - explicitly unsupported inputs: `0`
  - strict proved-path successes: `59 / 62` (30s per-case timeout rerun)
  - strict failing set:
    - `advect3d`
    - `mxv`
    - `mxv-seq3`
- Runtime success is no longer the main acceptance criterion; source-model fidelity with the C/Clan `before.scop` remains the north star.
- The current source-model fidelity bug that was identified and fixed:
  - `src/PolyLang.v: schedule_to_source_like_rows`
  - old implementation dropped a middle dynamic schedule dimension during source OpenScop export
  - minimal Coq reproducer showed extractor internal schedules were correct; the loss happened in source OpenScop export
  - after the fix, representative extracted `before.scop` scattering metadata now matches C-path source scop on `covcol` and `matmul`
- The current north star is source-model fidelity with the C/Clan `before.scop`, then parity of Pluto's actual optimization behavior.
- Important correction:
  - the remaining `mxv` / `mxv-seq3` issue should not be treated as a reason to
    insert an ad hoc validation-only normalization pass
  - the design bug is in compact schedule handling itself
  - source-like zero rows are semantically relevant for cross-statement global
    timestamp alignment
  - current local zero-row removal is not trustworthy as a semantics-preserving
    compact representation
  - the repair target is a correct global compact/canonical schedule design,
    while keeping strict runtime path = proved path
- New key diagnosis after adding `StrengthenDomain`:
  - strengthening is necessary, but it is not the current top blocker
  - on representative cases such as `covcol`, strengthened `before.scop`
    plus Pluto raw `after.scop` already satisfy `polcert = EQ`
  - the remaining failures are now:
    - `mxv`, `mxv-seq3`
      - complete/padded validation view accepts the optimized schedule
      - strengthened raw/source validation view still rejects it with `res=false`
      - this is now a schedule-representation mismatch, not a simple source exporter bug
    - `advect3d`
      - source scattering metadata now matches the C-path extractor
      - remaining issue is downstream of source export and currently manifests as runtime cost / timeout
      - temporary extracted-OCaml timing showed:
        - `strengthen+scheduler+validate`: about `1.6s`
        - `codegen`: about `38.5s`
        - parser / elaboration / pretty-print are negligible
      - so `advect3d` is a `CodeGen.codegen` performance issue, not a validator issue
- Division is now preserved end-to-end in the syntax frontend.
- Pure calls, ternaries, and exact float literals are also preserved.
- The CLI fallback exporter is no longer in the default path.
- `SPolOpt.opt` now points back to `PreparedOpt.Opt`; any remaining failures are now on the true proved path, not on a wrapper path.
- `syntax/SLoopPretty.ml` now does display-only cleanup:
  - singleton `range(e, e+1)` loops print as let-like substitutions
  - loop/instruction expressions and tests are simplified before printing
