# PolCert Project Log

Date: 2026-03-08

## Environment
- Container: `gifted_curie`
- Code repo: `gifted_curie:/polcert`
- Active branch: `extractor`

## Current proved state
- `src/Extractor.v`: `extractor_correct` is `Qed`
- `src/PrepareCodegen.v`: `prepare_codegen_semantics_correct` is `Qed`
- `driver/PolOptPrepared.v`: `Opt_correct` is `Qed`
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

## Current conclusion
- The generated-suite semantic blockers are closed.
- The strict proved path is currently:
  - proof-complete
  - clean-buildable
  - `62 / 62` on the generated suite
- Remaining work, if any, is now about:
  - strengthening the source-model fidelity argument
  - or broadening the benchmark set

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
