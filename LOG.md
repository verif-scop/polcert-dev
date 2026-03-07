# PolCert Project Log

Date: 2026-03-06

## Environment
- Container: `gifted_curie`
- Code repo: `gifted_curie:/polcert`
- Active branch: `extractor`

## Closed proof work
- `Extractor.extractor_correct`: `Qed`
- `PrepareCodegen.prepare_codegen_semantics_correct`: `Qed`
- `driver/PolOptPrepared.v`:
  - `Definition Opt := Opt_prepared`
  - `Theorem Opt_correct`
- `check-admitted`: `Nothing admitted.`

## Runtime regression baseline
- `main` in a clean worktree passes `make test`
- `extractor` had a real regression on `covcol` and many Pluto tests before the runtime fixes

## Runtime fixes that survived testing

### Extractor access fix
- File: `src/Extractor.v`
- Change:
  - `normalize_access_list_rev` -> `normalize_access_list`
  - for extracted `pi_waccess/pi_raccess`
- Result:
  - official `CInstr` tests recovered
  - `CSample2/covcol` recovered
  - `make test` returned to green

### Syntax frontend follow-up
- File: `syntax/SInstr.v`
- Problem:
  - syntax checker only accepted raw or reverse-normalized access
  - after the extractor fix, syntax extractor output became plain normalized access
- Change:
  - syntax checker now accepts:
    - raw access
    - normalized access
    - reverse-normalized access
- Result on `covcol`:
  - `validate(extracted, extracted) = true`
  - `validate(extracted, roundtrip-before) = true`
  - `validate(extracted, scheduled) = true`

### Runtime entrypoint cleanup
- File: `syntax/SPolOpt.v`
- The temporary normalized/raw split workaround was removed
- `polopt` is back on the single-object route:
  - `opt = PreparedOpt.Opt`
  - `opt_poly = CoreOpt.scheduler' ; Prepare.prepared_codegen`

## Current validated runtime status
- `opam exec -- make test`: green
- `./polopt --debug-scheduler /tmp/covcol.loop`:
  - all three validation checks return `true`
- `./polopt /tmp/covcol.loop`:
  - produces optimized output

## Remaining modified code in container
- `src/Extractor.v`
- `src/PolyLang.v`
- `syntax/SInstr.v`
- `syntax/SPolOpt.v`

## Notes
- The last runtime blocker was not a proof regression
- It was not a validator-algorithm regression
- It was not necessary to keep the previous normalized/raw split in `syntax/SPolOpt.v`
- The useful reference note is:
  - [doc/openscop-representation-gap.md](doc/openscop-representation-gap.md)

## Pluto `.loop` suite work

### Generator
- Generator script now lives in the test area:
  - `tests/polopt-generated/tools/generate_pluto_loops.py`
- Generated suite input files:
  - `tests/polopt-generated/inputs/*.loop`
- Per-case strict outputs:
  - `tests/polopt-generated/cases/<case>/`
- Current generated count:
  - `62`

### Current pass rate
- Current strict batch result for the default `./polopt file.loop` path:
  - `45 / 62` pass
  - `17 / 62` fail

### Important runtime/frontend fixes during suite work
- `lib/OpenScopPrinter.ml`
  - zero-parameter OpenScop printing fixed so Pluto/OSL accepts the file
- `syntax/SLoopElab.ml`
  - `slot_env` now follows `params @ loops`
- `syntax/SInstr.v`
  - `syntax_slot_names names = names`
- `syntax/SPolIRs.v`
  - source-aware scheduler decode currently uses `from_openscop_like_source`
- `syntax/SLoopMain.ml`
  - CLI fallback was removed
  - default `polopt` now stays on the strict proved path only

### Current failure taxonomy
- Remaining source-model hard failures:
  - `advect3d`
  - `corcol3`
  - `jacobi-1d-imper`
  - `jacobi-2d-imper`
  - `lu`
- Remaining strict proved-path scheduler failures:
  - `adi`
  - `corcol`
  - `covcol`
  - `dct`
  - `doitgen`
  - `fusion1`
  - `fusion8`
  - `multi-stmt-stencil-seq`
  - `pca`
  - `ssymm`
  - `tricky1`
  - `trisolv`

### Key technical finding
- For the remaining validation failures, the failing component is usually:
  - `res = false`
- while:
  - `wf1 = true`
  - `wf2 = true`
  - `eqdom = true`
  - `valid_access = true`
- This means most remaining failures are schedule/dependence-validation issues, not basic IR inconsistency.

### Important specific finding
- `from_openscop_like_source` needed a fix for padded scattering tail constants.
- Without that fix, kernels like `covcol` lost the final statement-order constant on roundtrip.
- The current implementation still does not cover every Pluto output shape cleanly.

### Reference note
- [doc/polopt-loop-suite-status.md](doc/polopt-loop-suite-status.md)

## 2026-03-07 strict polopt path and per-case directories
- `syntax/SLoopMain.ml` default path reverted to strict `SPolOpt.opt` only; CLI fallback removed.
- `syntax/SPolOpt.v` now runs the proved path directly:
  - `opt = proved_opt = PreparedOpt.Opt`
- Added `tests/polopt-generated/tools/materialize_polopt_cases.py` to materialize one directory per generated `.loop` case.
- Materialized strict-path outputs at `tests/polopt-generated/cases/<case>/` with:
  - `input.loop`
  - `input.pretty.loop` (for successful runs)
  - `optimized.loop` (for successful runs)
  - `diff.patch` (for successful runs)
  - `stderr.txt`
  - `status.txt`
- Current strict-path batch result on generated suite: `45/62` succeed, `17/62` fail.
- Current strict-path failing set:
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
- All successful strict-path cases currently show `changed=true` under the normalized `input.pretty.loop` vs `optimized.loop` comparison.

## 2026-03-07 `SInstr` lightweight real semantics
- `syntax/SInstr.v` no longer uses an empty instruction semantics.
- New state model:
  - `State.t := MemCell -> Z`
  - extensional `State.eq`
  - `dummy_state` returns `0`
- New instruction behavior:
  - `SSkip` preserves state
  - `SAssign lhs rhs` writes one target `MemCell` with the evaluated RHS
- `access_function_checker_correct` is now non-vacuous.
- `bc_condition_implie_permutbility` is now proved against this concrete store model rather than by inversion on an empty semantics.
- Validation after the change:
  - `opam exec -- make syntax/SInstr.vo` passes
  - `opam exec -- make test` passes
  - strict `polopt` suite remains `45 / 62`
- This improves the quality of the `SPolIRs` example instance without changing the currently observed strict proved-path coverage.
- Reference note:
  - [doc/sinstr-semantics.md](doc/sinstr-semantics.md)
- Container repo commit for this step:
  - `68e37e4` `syntax: give SInstr a lightweight real semantics`

## 2026-03-07 pretty-printer cleanup and strict suite analysis
- `syntax/SLoopPretty.ml`
  - added display-only simplification for:
    - loop expressions
    - instruction expressions
    - tests
  - singleton loops of the form `for x in range(e, e+1)` are now printed as a let-like substitution into the body
  - `if (true)` is dropped in the pretty output
- Re-materialized strict `polopt` case directories under:
  - `tests/polopt-generated/cases`
- Current strict-path status is unchanged at:
  - `45 / 62` succeed
  - `17 / 62` fail
- Unchanged successful cases:
  - `nodep`
  - `noloop`
- New analysis documents:
  - [doc/polopt-success-summary.md](doc/polopt-success-summary.md)
  - [doc/polopt-failure-analysis.md](doc/polopt-failure-analysis.md)
- Important failure split:
  - roundtrip-before already fails:
    - `adi`, `corcol`, `corcol3`, `dct`, `doitgen`, `pca`
  - roundtrip-before passes but scheduled result fails validation:
    - `advect3d`, `covcol`, `fusion1`, `fusion8`, `jacobi-1d-imper`, `jacobi-2d-imper`, `lu`, `multi-stmt-stencil-seq`, `ssymm`, `tricky1`, `trisolv`
- All `17` failing cases are also `NE` when comparing our extracted source scop against the original C path `*.beforescheduling.scop` with `polcert`.
