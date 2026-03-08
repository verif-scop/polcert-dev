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

## 2026-03-08 strengthened-domain vs importer diagnosis

- The true proved path currently includes an uncommitted strengthening pass:
  - `src/StrengthenDomain.v`
  - wired in `driver/PolOptPrepared.v`
- On `covcol`, strengthening is active on the source poly and the exported `before.scop`
  now includes the expected extra parameter-only guards:
  - `M - 1 >= 0`
  - `N - 1 >= 0`
- Running Pluto directly on that strengthened raw source scop yields a raw optimized
  `after.scop` such that:
  - `./polcert strengthened_before_raw.scop strengthened_after_raw.scop = EQ`
- Therefore, missing guards are not the final blocker on the strict path.
- The remaining blocker is the scheduled importer:
  - `from_openscop_like_source`
- It mis-imports Pluto's optimized scattering and reconstructs the old source-like
  skeleton, after which validator fails in `res`.
- A direct experiment switching `syntax/SPolIRs.v` to
  - `from_openscop_schedule_only`
  restored all six remaining failures:
  - `corcol`, `costfunc`, `covcol`, `intratileopt3`, `shift`, `tricky1`
  but regressed `22` previously successful cases.

## 2026-03-08 source-scattering exporter and remaining strict blockers

- Fixed another source OpenScop exporter bug in `src/PolyLang.v`:
  - leading constant schedule dimensions produced by `Seq` must not be preceded
    by an extra zero row in source-like scattering export.
- This bug was in the source OpenScop boundary, not in `Extractor`.
- After the fix:
  - `fusion1` strict path recovers
  - `multi-stmt-stencil-seq` strict path recovers
  - source `before.scop` metadata for `advect3d` matches the C-path extractor
    much more closely

- `mxv` is now the clearest remaining representation problem:
  - `validate(strengthened, roundtrip-before) = true`
  - `validate(complete-before, complete-after)` has `eqdom=true` and `res=true`
  - `validate(strengthened, scheduled)` still has `res=false`
  - `scheduled payload` compact schedule for statement 2 is `[1; i; j]`
  - `complete-after payload` uses the same compact schedule
  - but the raw/source strict path still rejects it
- This means `mxv` is no longer a simple importer bug. It is now a schedule
  representation mismatch between:
  - the strengthened raw/source poly view
  - and the complete/padded validation view

- `advect3d` should no longer be described as a source-fidelity mismatch.
  Current observation:
  - within 8s of `--debug-scheduler`, it reaches and prints the extracted source
    OpenScop
  - the source exporter now matches the C-path source scattering metadata
  - the remaining issue is downstream of source export, likely scheduler/import
    runtime cost or a later representation problem

## 2026-03-08 current strict suite count and remaining blocker split

- Fresh rerun of the strict suite with a 30s per-case timeout gives:
  - `59 / 62` success
  - blockers:
    - `advect3d` (`timeout`)
    - `mxv` (`Scheduler validation failed`)
    - `mxv-seq3` (`Scheduler validation failed`)

- `mxv` and `mxv-seq3` now show the same pattern:
  - `validate(strengthened, roundtrip-before) = true`
  - `validate(complete-before, complete-after)` has `eqdom=true` and `res=true`
  - `validate(strengthened, scheduled)` has `eqdom=true`, `valid_access=true`,
    but `res=false`
- This makes them schedule-representation mismatches between the raw/source view
  and the complete/padded view, not simple source exporter failures.
- Conclusion:
  - `schedule_only` is not a global fix
  - importer logic must distinguish "still source-like" schedules from genuinely
    optimized schedules that should not be refilled into the old template

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

## 2026-03-07 semantics-preserving `.loop` generation
- The generated `.loop` suite no longer uses lossy expression rewrites.
- `syntax` frontend now supports division in RHS expressions:
  - `SLoopAst.expr` adds division
  - `SLoopParse` parses `/`
  - `SLoopElab` lowers it to `SInstr.ExDiv`
  - `syntax/SInstr.v` gives it concrete semantics and OpenScop printing via `ArrDiv`
  - `SLoopPretty` prints and simplifies it
- The benchmark generator no longer rewrites:
  - `/` to `*`
  - `/=` to multiplication update
- Instead:
  - `/=` is lowered to `x = x / y`
  - pure calls are preserved
  - ternary expressions are preserved
  - non-integral float literals are preserved as exact text
- Generator script remains:
  - `tests/polopt-generated/tools/generate_pluto_loops.py`
- New supported split:
  - total benchmark cases: `62`
  - generated semantics-preserving `.loop` inputs: `62`
  - unsupported and skipped: `0`
- Strict proved-path result:
  - `45 / 62` succeed
  - `17 / 62` fail
- Failing set:
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
- Cases newly supported and successful after the frontend extension:
  - `fdtd-2d`
  - `floyd`
- Updated failure split from `--debug-scheduler`:
  - roundtrip-before already fails:
    - `adi`
    - `corcol`
    - `corcol3`
    - `dct`
    - `doitgen`
    - `pca`
  - roundtrip-before passes but scheduled result fails validation:
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
- `check-admitted` still reports `Nothing admitted.`
- `make test` still completes successfully on the official suite.

## 2026-03-07 source roundtrip importer fixes
- The strict proved-path `.loop` suite improved from `45 / 62` to `53 / 62`.
- Remaining failures are now only:
  - `corcol`
  - `corcol3`
  - `covcol`
  - `dct`
  - `jacobi-1d-imper`
  - `jacobi-2d-imper`
  - `pca`
  - `ssymm`
  - `tricky1`
- Most importantly, `validate(extracted, roundtrip-before) = true` now holds across the generated suite.
- The importer-side fixes were:
  - padded scattering tail-constant detection now accepts a nonzero tail constant row
  - source-template schedule refill preserves structural zero constant slots
- This means the remaining failures are no longer source roundtrip failures.
- They are all in the “Pluto-scheduled result rejected by validator” bucket.
- Detailed per-case source-scope comparison for the remaining failures is now in:
  - [doc/polopt-remaining-9-cases.md](doc/polopt-remaining-9-cases.md)

## 2026-03-07 second-class OpenScop schedule export fix
- Investigated the remaining `9` strict-path failures as two missing-information classes:
  - parameter-only domain guards
  - source schedule skeleton mismatches on imperfect nests / multi-stmt kernels
- Added a Coq-side comment in `src/PolyLang.v` documenting the OpenScop format requirement:
  - middle constant schedule rows encode statement-order skeleton directly
  - they must not be emitted as `zero row + constant row` pairs
- Adjusted source scattering export in `src/PolyLang.v` to preserve middle constant schedule rows in the Clan/Pluto shape.
- Important correction:
  - an earlier negative result was measured against a stale extracted `polopt` binary
  - after rebuilding `polopt`, the second-class cases recovered
- Current strict-path runtime result:
  - `62 / 62` generated `.loop` inputs now run successfully through the strict proved path
- Recovered scheduled-validation cases include:
  - `corcol`
  - `corcol3`
  - `jacobi-1d-imper`
  - `jacobi-2d-imper`
  - `pca`
  - `dct`
- Remaining fidelity debt:
  - `validate(extracted, roundtrip-before) = false` still occurs for:
    - `covcol`
    - `dct`
    - `pca`
    - `ssymm`
  - but `validate(extracted, scheduled) = true` now holds across the full suite

## 2026-03-07 objective shift: source-model fidelity over mere runtime success
- The success criterion for `polopt` has been tightened.
- It is no longer sufficient that:
  - the strict proved path runs, and
  - scheduled validation succeeds.
- The new criterion is:
  - our `extractor + to_openscop` source scop must match the C/Clan/Pluto `before.scop` closely enough that Pluto is solving the same optimization problem.
- The anchor case is now `covcol`:
  - current strict `polopt` succeeds,
  - but the optimized loop does not match Pluto's C-path transformation,
  - because the source `before.scop` still differs materially.
- New reference note:
  - [doc/source-model-fidelity-goal.md](doc/source-model-fidelity-goal.md)

## 2026-03-07 source scattering root cause analysis
- The current source-model fidelity gap is now localized more precisely.
- `Extractor` internal schedules are not missing loop dimensions.
- A direct Coq check on a minimal `j1/j2/Seq[Loop i S1; S2]` example shows:
  - internal `pi_schedule` for `S1` is `[j1; j2; 0; i]`
  - after `remove_zero_schedule_dims`, it is `[j1; j2; i]`
- The loss happens inside `src/PolyLang.v` in `schedule_to_source_like_rows`.
- The current pattern
  - `aff1 :: (aff2 :: sched' as tl)`
  binds `tl` to `sched'`, not to `(aff2 :: sched')`.
- As a result, for three consecutive non-constant schedule dims `[a; b; c]`, the function computes:
  - `[a; zero; c]`
  instead of
  - `[a; zero; b; zero; c]`
- So the exporter drops every middle dynamic dimension when two non-constant dimensions are adjacent.
- This explains the observed source `before.scop` row-count mismatch such as:
  - `covcol` statement `S1`: internal compact schedule has three dynamic dims, but exported source scattering has only five rows.
- This is an exporter bug in the current uncommitted `src/PolyLang.v`, not an extractor bug and not a Pluto behavior issue.
- No code fix has been applied yet after this diagnosis.
2026-03-07

- Fixed a concrete source-scattering exporter bug in `/polcert/src/PolyLang.v`:
  `schedule_to_source_like_rows` used the pattern
  `aff1 :: (aff2 :: sched' as tl)`, which in practice caused the recursive
  call to skip the middle dynamic schedule dimension.
- Minimal Coq reproduction showed:
  internal extractor schedule for a `j1 / j2 / Seq[Loop i S1; S2]` example was
  correct (`j1 ; j2 ; 0 ; i`), but source OpenScop export became
  `j1 ; 0 ; i` instead of `j1 ; 0 ; j2 ; 0 ; i`.
- After fixing the helper, extracted `before.scop` scattering now matches C-path
  Pluto/Clan metadata on representative cases:
  - `covcol`: `S1 7x14x7`, `S2 5x11x5`
  - `matmul`: `7x15x7`
- This bug did not necessarily break validation on every case because it only
  affected the source OpenScop fed to Pluto, not the extracted poly semantics
  directly. Many cases still validated because either:
  - the statement schedule shape did not trigger the bug, or
  - Pluto optimized a weaker source model but still returned a schedule that
    was legal for the original extracted poly.
- Current strict `polopt` suite after the exporter/source-schedule fix:
  - `56 / 62` succeed
  - failures: `corcol`, `costfunc`, `covcol`, `intratileopt3`, `shift`, `tricky1`
- Follow-up analysis of those six failures:
  - `SCATTERING` now matches the C/Clan `before.scop` on all six
  - the remaining mismatch is entirely in `DOMAIN`
  - the extra C-path rows are all parameter-only guards such as:
    - `M-1 >= 0`
    - `N-1 >= 0`
    - `M-2 >= 0`
    - `N-2 >= 0`
- Controlled guard-patching experiment on:
  - `corcol`
  - `costfunc`
  - `covcol`
  - `intratileopt3`
  - `shift`
  - `tricky1`
- Result:
  - Pluto produces optimized `after.scop` on all six
  - `after.scop` scattering metadata matches the C-path `after.scop`
  - `polcert(patched_before, patched_after)` returns `EQ` on all six
- This showed:
  - strengthening is necessary
  - but the remaining failure after strengthening is no longer raw domain weakness

2026-03-08

- Added `StrengthenDomain` on the true proved path:
  - `driver/PolOptPrepared.v` now calls `Strengthen.strengthen_pprog`
    before `scheduler'`
- Rebuilt `polopt` explicitly and confirmed the remaining six failures do not
  come from a stale binary.
- Temporary debug instrumentation of `syntax/SLoopMain.ml` showed:
  - strengthened `covcol` `before.scop` really contains the expected implied
    parameter-only guards:
    - statement 1 gains `M-1 >= 0` and `N-1 >= 0`
    - statement 2 gains `M-1 >= 0`
  - but strict `polopt` still fails with:
    - `wf1 = true`
    - `wf2 = true`
    - `eqdom = true`
    - `valid_access = true`
    - `res = false`
- Direct Pluto run on the strengthened source scop for `covcol`:
  - `pluto --readscop ... cov_strengthened_before.scop`
  - produced a raw optimized `after.scop`
  - and `polcert(cov_strengthened_before.scop.beforescheduling.scop, cov_strengthened_before.scop.afterscheduling.scop) = EQ`
- This means:
  - the strengthened source model is already sufficient for Pluto to compute a
    validator-accepted optimized schedule
  - the remaining strict-path blocker is no longer missing domain guards
- The blocker is now localized to `from_openscop_like_source` in
  `/polcert/src/PolyLang.v`.
- `covcol` witness:
  - Pluto raw `after.scop` statement 1 scattering meta:
    - `4 11 4 3 0 2`
  - strict-path re-export after import:
    - `7 14 7 3 0 2`
  - so the importer expands the optimized schedule back into the old
    source-like skeleton instead of preserving Pluto's actual optimized schedule
- Therefore the current remaining failures are importer failures:
  - `from_openscop_like_source` mis-decodes Pluto optimized scattering
  - validator then sees the wrong scheduled poly and fails in `res`

- Added a hybrid importer checkpoint in `src/PolyLang.v`:
  - it keeps source-template refill only when the optimized scattering can be
    round-tripped back to the same source-like family
  - otherwise it falls back to compact/schedule-only import
- Re-ran the strict suite after this importer checkpoint:
  - `54 / 62` succeed
  - remaining failures:
    - `advect3d`
    - `corcol3`
    - `dct`
    - `fusion1`
    - `gemver`
    - `multi-stmt-stencil-seq`
    - `mxv`
    - `pca`
- These now split cleanly into:
  - importer/view failures, where raw Pluto already validates:
    - `corcol3`
    - `dct`
    - `gemver`
    - `mxv`
    - `pca`
  - genuine source-model / scheduling-problem mismatches:
    - `advect3d`
    - `fusion1`
    - `multi-stmt-stencil-seq`
- Further refinement of the importer/view bucket:
  - `corcol3`, `dct`, `gemver`, `pca`
    - `polcert(raw_after, imported_after) = EQ`
    - so the remaining failure is not visible in OpenScop
    - it must live in source poly payload hidden from OpenScop
 - `mxv`
    - `polcert(raw_after, imported_after) = NE`
    - so `mxv` is still a direct importer bug at the OpenScop level

- Timed `advect3d` on the true strict path using a temporary extracted-OCaml
  timing patch:
  - `parse_file`: `0.000s`
  - `elaborate`: `0.000s`
  - `extractor`: `0.000s`
  - `strengthen + scheduler + validate`: `1.645s`
  - `prepare`: `0.000s`
  - `codegen`: `38.493s`
  - `opt-total`: `40.751s`
  - `pretty`: `0.000s`
- Therefore `advect3d` is not slow because of parser, printer, Pluto, or
  validator.
- Its current `~41s` runtime is almost entirely in `CodeGen.codegen`.
- The generated loop is not large at the text level, so the cost is internal to
  polyhedral code generation (region splitting / loop construction), not output
  printing.
