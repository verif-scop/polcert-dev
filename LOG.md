# PolCert Project Log

Date: 2026-03-08

## Environment
- Container: `gifted_curie`
- Code repo: `gifted_curie:/polcert`
- Active branch: `extractor`

## Current proved state
- `src/Extractor.v`: `extractor_correct` is `Qed`
- `src/PrepareCodegen.v`: `prepare_codegen_semantics_correct` is `Qed`
- `driver/PolOpt.v`: final `Opt_correct` is `Qed`
- `driver/PolOptPrepared.v`: now just re-exports `PolOpt`
- `opam exec -- make -s check-admitted`: `Nothing admitted.`

## Clean-build fact
- The earlier clean-build failure was not a VPL issue.
- Root cause:
  - `make depend` had been run outside `opam exec`
  - `coqdep` was missing from PATH
- Current clean rebuild procedure that succeeds:
  - `make clean`
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`

## Current runtime status
- `opam exec -- make test`: green
- strict proved-path `polopt` suite: `62 / 62`
- `syntax/SPolOpt.v`: `opt = CoreOpt.Opt`, so the CLI now runs the same final `Opt` defined in `driver/PolOpt.v`
- Clean acceptance rerun completed successfully with:
  - `make clean`
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make -s check-admitted`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`
  - strict generated-suite rerun: `62 / 62`

## `PolOpt.v` consolidation
- `driver/PolOpt.v` now contains the final verified optimizer definition.
- The old raw pipeline was renamed to `Opt_raw`.
- The final strengthened+prepared optimizer is now:
  - `Opt_prepared`
  - `Opt = Opt_prepared`
- `driver/PolOptPrepared.v` was reduced to a compatibility wrapper that re-exports `PolOpt`.

## Runtime fixes that survived

### 1. Extractor access normalization
- File: `src/Extractor.v`
- `normalize_access_list_rev` was wrong for extracted accesses.
- Fixed to `normalize_access_list`.
- Result:
  - `CInstr` tests recovered
  - `CSample2/covcol` recovered
  - `make test` returned to green

### 2. Source scattering exporter bug
- File: `src/PolyLang.v`
- `schedule_to_source_like_rows` used to drop a middle dynamic schedule row.
- This made source `before.scop` differ from the C-path scheduling problem.
- Fix is in place and survives the full suite.

### 3. Domain strengthening
- Statement domains are strengthened with parameter-only rows logically implied
  by iterator bounds.
- These are not treated as global program assumptions.
- This is needed so Pluto sees the intended guarded scheduling problem.

### 4. `mxv` / `mxv-seq3` schedule representation repair
- Root cause:
  - compaction was local per statement
  - zero rows were dropped without preserving the program-wide shared schedule
    skeleton
- Effective repair:
  - preserve source-like schedule structure for export
  - import optimized schedules with `from_openscop_schedule_only`
  - canonicalize schedules with a program-wide row mask
- Important:
  - this is a schedule representation fix
  - not a `Validator` fix
  - not a validation-only branch

### 5. `advect3d` status
- `advect3d` is not a semantic blocker.
- Temporary timing experiment showed:
  - `strengthen + scheduler + validate`: about `1.6s`
  - `CodeGen.codegen`: about `38.5s`
  - total `polopt`: about `40.7s`
- Conclusion:
  - parser/printer/validator/Pluto are not the issue
  - `CodeGen.codegen` dominates runtime on this corner case

## Oracle discipline
- C-path Pluto remains the optimization oracle.
- Do not use cross-source `polcert(our_before, c_before)` or
  `polcert(our_after, c_after)` as equality oracles.
- OpenScop names, IDs, and metadata differ by origin.
- Valid structural oracle:
  - compare raw Pluto `before.scop` / `after.scop`
  - compare `SCATTERING` family / schedule shape
  - require strict proved-path `polopt` to succeed on our route

## Current raw structural comparison
- Checked-in report:
  - `doc/pluto-raw-family-compare.md`
  - `doc/pluto-raw-family-compare.json`
- Scope warning:
  - the current report uses `polopt --extract-only`
  - it compares pure extractor output, not the strict proved-path source model
    after `StrengthenDomain`
- Current summary:
  - `62 / 62` source `before.scop` `SCATTERING` metadata match the C-path
  - `62 / 62` raw Pluto `after.scop` `SCATTERING` metadata match the C-path
  - residual mismatch is concentrated in source `DOMAIN` metadata
- Sampled row-level `DOMAIN` comparisons (`covcol`, `tricky1`, `mxv`, `matmul`,
  `advect3d`, `costfunc`) show a stable pattern:
  - our exporter emits iterator bound rows only
  - the C-path adds one parameter-only row per iterator, expressing the
    non-emptiness consequence of the bound interval
  - examples:
    - `N-1 >= 0`
    - `N-2 >= 0`
    - `M-1 >= 0`
    - `K-1 >= 0`
    - `nz+2 >= 0`
- Current interpretation:
  - the remaining source-model fidelity gap is statement-domain strengthening
  - it is no longer a source `SCATTERING` problem
- `covcol` spot-check with `./polopt --debug-scheduler` confirms that the
  strict-path strengthened source OpenScop already reaches the C-path `DOMAIN`
  row counts, so `--extract-only` underreports current fidelity.

## Current conclusion
- The generated-suite semantic blockers are closed.
- The strict proved path is currently:
  - proof-complete
  - clean-buildable
  - `62 / 62` on the generated suite
- Remaining work, if any, is now about:
  - strengthening the source-model fidelity argument
  - or broadening the benchmark set

## Precise strengthening repair
- The final strengthening change that survived is not the earlier broad
  parameter-only guard collection.
- Current `StrengthenDomain` now derives extra rows only by:
  - canceling the current innermost iterator between two constraints
  - keeping the resulting guard only if it depends on outer iterators +
    parameters
- This precise strengthening was recompiled, re-extracted, and revalidated
  through a clean rebuild.

## Follow-up TODOs
- Add GitHub CI to the source repo:
  - run the README/opam build flow
  - run `check-admitted`
  - run `make test`
  - run the strict `polopt` generated-suite regression
- Evaluate moving the current OCaml-only post-codegen simplification into a verified Coq cleanup pass:
  - expr/test simplification
  - guard/seq cleanup
  - singleton-loop elimination via verified substitution

## Cleanup pass integration
- `polygen/LoopCleanup.v` is now implemented and compiled.
- `src/PrepareCodegen.v` now wraps codegen with:
  - `Cleanup.cleanup`
- Current clean build + strict rerun confirms the cleanup pass is in the proved
  path:
  - `Nothing admitted`
  - README clean build succeeds
  - strict suite remains `62 / 62`
- Implemented cleanup layers:
  - expression/test simplification
  - structural cleanup for `Seq` / trivial `Guard`
- Deferred layer:
  - singleton-loop elimination by substitution

## Strengthened-before / raw-after comparison
- Full-suite strict-path comparison was run using strengthened source `before.scop` extracted from `polopt --debug-scheduler`, then raw `pluto --readscop`.
- Results:
  - strengthened `before.scop` scattering metadata match: `62 / 62`
  - strengthened `before.scop` domain metadata match: `52 / 62`
  - raw Pluto `after.scop` scattering metadata match: `62 / 62`
- Residual domain-only mismatches are limited to:
  - `fusion10`, `fusion2`, `fusion3`, `fusion4`, `fusion8`, `lu`, `nodep`, `ssymm`, `strsm`, `trisolv`
- For those `10`, raw Pluto `after.scop` still lands in the same scattering family as the C-path raw `after.scop`.
- Therefore the current residual source-model fidelity gap is domain-shape only; on the generated suite it is no longer changing the observed optimization family.

## Residual domain mismatch classes
- Residual `DOMAIN` metadata mismatches now split into:
  - tautological / clearly redundant extras on our side:
    - `fusion10`, `fusion2`, `fusion3`, `fusion4`, `fusion8`, `nodep`
  - still-nontrivial strengthening mismatches:
    - `lu`, `ssymm`, `strsm`, `trisolv`
- Even for the second class, the raw Pluto `after.scop` scattering family currently still matches the C-path on the generated suite.

- The residual nontrivial domain mismatches are now better understood:
  - `lu`, `ssymm`, `trisolv` are mainly inner-range non-emptiness strengthening differences
  - `strsm` is mainly a guard/singleton normalization difference (`k == i+1` represented as equality in the C-path)
- This refines the remaining debt: it is a domain-normalization mismatch, not a schedule mismatch.

## Next strengthening direction
- Current `StrengthenDomain` only emits parameter-only guards.
- The remaining nontrivial source-domain mismatches suggest the next principled extension:
  - eliminate the innermost iterator from a lower/upper bound pair
  - keep guards that depend on outer iterators + parameters
  - normalize singleton domains / guard equalities as equality rows when appropriate
- Representative targets:
  - `lu`: derive `N-k-2 >= 0`
  - `ssymm`: derive `j-2 >= 0`
  - `trisolv`: derive `j-1 >= 0`
  - `strsm`: normalize `k == i+1` as equality
