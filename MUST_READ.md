# Must Read

## Workspace
- This outer repo is a separate git repo: `polcert-dev`
- `polcert-dev` remote: `git@github.com:verif-scop/polcert-dev.git`
- Real code/proof repo lives in the container: `gifted_curie:/polcert`
- Container repo remote: `git@github.com:Hughshine/PolCert.git`
- Default working branch in the container: `end-to-end`
- `work/container-overlay/polcert` is an overlay/edit mirror for syncing into the container repo
- Do not confuse `work/container-overlay/polcert` with the container repo itself
- Commit/push policy:
  - documentation, context, notes, plans, reports, host-side analysis tools -> `polcert-dev`
  - Coq/OCaml/runtime/build changes for PolCert itself -> `gifted_curie:/polcert`
  - do not stage `work/container-overlay/polcert/**` in `polcert-dev` unless the change is intentionally about the overlay mirror itself

## Raw Pluto Structural Comparison
- The checked-in raw comparison report is:
  - `doc/pluto-raw-family-compare.md`
  - `doc/pluto-raw-family-compare.json`
- Important scope note:
  - that report currently uses `polopt --extract-only`
  - so it compares the pure extractor source model
  - it does **not** yet compare the strict proved-path source model after `StrengthenDomain`
  - do not confuse extractor-before with strengthened-before
- Current report summary over the `polopt` regression suite:
  - cases compared: `62`
  - source `before.scop` `SCATTERING` metadata match: `62 / 62`
  - raw Pluto `after.scop` `SCATTERING` metadata match: `62 / 62`
  - remaining raw structural mismatch is concentrated in source `DOMAIN` metadata
- The current domain mismatch pattern is concrete rather than accidental:
  - C-path usually adds one parameter-only row per iterator, expressing non-emptiness of that iterator's bound interval
  - examples:
    - `0 <= i <= N-1` gives extra row `N-1 >= 0`
    - `1 <= j <= N-1` gives extra row `N-2 >= 0`
    - `4 <= k <= nz+6` gives extra row `nz+2 >= 0`
- Treat these as statement-domain strengthening candidates, not global context assumptions.
- Sample confirmation:
  - on `covcol`, `./polopt --debug-scheduler` shows that the strict-path
    strengthened source OpenScop already has the C-path domain row counts
    (`8` rows for statement 1, `5` rows for statement 2)

- A full strict-path strengthened-before comparison has now been run:
  - strengthened `before.scop` vs C-path `before.scop`: `SCATTERING` matches `62 / 62`, `DOMAIN` matches `52 / 62`
  - raw Pluto `after.scop` from strengthened-before vs C-path raw `after.scop`: `SCATTERING` matches `62 / 62`
- Residual domain-only mismatches are currently:
  - `fusion10`, `fusion2`, `fusion3`, `fusion4`, `fusion8`, `lu`, `nodep`, `ssymm`, `strsm`, `trisolv`
- Important interpretation:
  - these residual domain mismatches do not currently change the optimization family on the regression suite
  - they remain a source-model fidelity debt, but not a current suite blocker
- Residual domain-only mismatches currently split into:
  - tautological / obviously redundant extras: `fusion10`, `fusion2`, `fusion3`, `fusion4`, `fusion8`, `nodep`
  - nontrivial domain normalization mismatches: `lu`, `ssymm`, `strsm`, `trisolv`
- The nontrivial four are now understood as:
  - `lu`, `ssymm`, `trisolv`: inner-range non-emptiness strengthening differences
  - `strsm`: guard/singleton equality normalization (`k == i+1`)
- The current `StrengthenDomain` repair is no longer the old broad parameter-only heuristic.
  It now works by:
  - canceling the current innermost iterator between a lower/upper bound pair
  - keeping only guards that depend on outer iterators + parameters
  - leaving `depth = 0` statements unchanged
  This was the change that closed the strict suite back to `62 / 62`.

## Operating rules
- Before and after substantial diagnosis work, update `LOG.md` and keep this file current.
- Use already-approved container commands only:
  - `docker exec gifted_curie sh -lc '...'`
  - `docker cp ...`
- Repo-handling rules:
  - inspect `git status` separately in `polcert-dev` and in `gifted_curie:/polcert`
  - commit/push each repo separately
  - never assume host staging state says anything about the container repo staging state
- Avoid `rm`; prefer overwrite or unique temp paths.
- Follow the README build flow in the container, but invoke it under `opam exec`.
- `make depend` exists and is valid here; the earlier failure was not a VPL issue, it was running `make depend` outside `opam exec`, so `coqdep` was missing from PATH.
- `all` / `make -j4` will auto-create `.depend`; a step-by-step clean rebuild should do:
  - `make clean`
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`
- Before any final status report, do a clean acceptance rerun:
  - `make clean`
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`
  - rerun the strict `polopt` suite

## Repair constraints
- Do not modify `Validator` as a repair path.
- Do not add a validation-only runtime branch.
- Keep runtime path aligned with the proved path.
- Do not change the proved pipeline structure just to make runtime pass.
- Do not "fix" `mxv` by special-casing the validation path.
- The remaining `mxv` issue is a schedule representation/design issue, not a validator bug.
- The key `mxv` lesson must remain explicit:
  - the old compact design was local per statement
  - that dropped zero rows without preserving the program-wide shared schedule skeleton
  - fixes must stay at the schedule representation level, not drift back to validator-side or domain-only explanations

## Oracle / acceptance criterion
- C-path Pluto is the reference behavior.
- For any benchmark:
  - `polcert(c_before, c_after)` should be `EQ`
  - cross-source `polcert(our_before, c_before)` is not an oracle because OpenScop metadata differs
  - re-exported scheduled OpenScop from `polopt --debug-scheduler` is also not a raw Pluto-after oracle; it is importer -> internal poly -> exporter again
  - when comparing optimization family with C-path, compare Pluto raw `after.scop` against C-path Pluto raw `after.scop`, not importer-reexported OpenScop
- Runtime success alone is not enough.
- Goal:
  - strict `polopt` succeeds
  - source `before.scop` matches the C-path scheduling problem as closely as possible
  - resulting optimization matches the same Pluto optimization family
  - use raw Pluto `after.scop` as the optimization oracle, not importer-reexported scheduled OpenScop
- `pluto --readscop` behavior must be treated as empirical, not assumed:
  - output file naming may differ from naive expectations
  - in degenerate/no-change cases it may not emit a separate `afterscheduling.scop`
  - any comparison script must handle that explicitly instead of hard-coding one filename pattern

## Build discipline
- Follow the repository README build order directly.
- For a full clean acceptance rerun, explicitly run `opam exec -- make depend` after `make clean`.
- Do not reintroduce the temporary top-level VPL symlink workaround; it was a mistaken local workaround and polluted the namespace / build artifacts.

## Current proved state
- `src/Extractor.v`: `extractor_correct` is `Qed`
- `src/PrepareCodegen.v`: `prepare_codegen_semantics_correct` is `Qed`
- `driver/PolOpt.v`: final `Opt_correct` is `Qed`
- `driver/PolOptPrepared.v`: compatibility wrapper re-exporting `PolOpt`
- `polygen/LoopCleanup.v`: cleanup pass after codegen is implemented
- `check-admitted`: `Nothing admitted.`

## Current runtime state
- `make test` is green
- Current proved-path `polopt` strict suite: `62 / 62` succeed
- `syntax/SPolOpt.v`: `opt = CoreOpt.Opt`
- `driver/PolOpt.v` now contains the final verified optimizer definition:
  - `Opt_raw` is the old raw pipeline
  - `Opt_prepared` is the strengthened+prepared final pipeline
  - `Opt = Opt_prepared`
- `driver/PolOptPrepared.v` is now only a compatibility wrapper.
- `advect3d` is not a semantic blocker; most runtime is still in `CodeGen.codegen`
- `mxv` / `mxv-seq3` were fixed by repairing compact/pad design at the schedule representation level, not by modifying `Validator` and not by a validation-only branch
- `prepared_codegen` now applies a verified cleanup pass after codegen.
- Current clean acceptance rerun status:
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make -s check-admitted`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`
  - strict suite rerun: `62 / 62`

## Cleanup pass status
- `polygen/LoopCleanup.v` is now part of the proved pipeline.
- `src/PrepareCodegen.v` now does:
  - `prepare_codegen`
  - `CodeGen.codegen`
  - `Cleanup.cleanup`
- The cleanup stack now has three verified layers:
  - expression/test simplification
  - structural cleanup for `Seq` / trivial `Guard`
  - singleton-loop elimination by substitution
- The singleton pass lives in:
  - `polygen/LoopSingletonCleanup.v`
- `src/PrepareCodegen.v` now routes cleanup through that module.
- The OCaml pretty-printer remains display-only; the semantic cleanup is now in Coq.
- `syntax/SLoopPretty.ml` should not reintroduce cleanup logic:
  - no expression/test simplification
  - no guard simplification
  - no singleton-loop let-like rewriting
  - keep it to formatting, naming, and raw rendering only

## Pending engineering follow-ups
- Add GitHub CI to the source repo:
  - run the README build flow under `opam exec`
  - run `check-admitted`
  - run `make test`
  - run the strict `polopt` generated-suite regression
- Continue the verified cleanup pass after codegen:
  - singleton-loop elimination via verified substitution
  - then keep shrinking the OCaml pretty-printer toward display-only logic

## Current `mxv` / `mxv-seq3` diagnosis
- The earlier diagnosis was correct in substance: the bug was in compact/pad design, not in `Validator`.
- The broken behaviour came from local per-statement compaction losing the program-wide shared schedule skeleton.
- The effective repair is now in the schedule representation itself:
  - keep source-like schedule structure for export
  - import optimized schedules with `from_openscop_schedule_only`
  - canonicalize schedules with a program-wide row mask, not per-statement local zero-row deletion
- With that repair in place, both `mxv` and `mxv-seq3` now pass on the proved path, and the full strict suite is `62 / 62`.
- Do not forget the design lesson:
  - ideal `pad`/`compact` should be symmetric and semantics-preserving
  - the broken compact was not global enough to be a true inverse of padding
  - fixes belong in schedule representation design, not in validator-side special cases
- Record this explicitly when resuming work:
  - the key design bug was that compaction was local to each instruction schedule
  - zero rows were treated as removable formatting, but in multi-statement programs they carry the shared global schedule skeleton
  - any future compact/pad change must preserve that program-wide skeleton
- Do not revert to local per-statement zero-row removal.
- Do not introduce validation-only normalization branches.
- Do not modify `Validator` for this issue.

## Historical but still relevant lessons
- `normalize_access_list_rev` for extracted accesses was wrong; extractor now uses `normalize_access_list`.
- `schedule_to_source_like_rows` used to drop a middle dynamic schedule dimension; that exporter bug is fixed.
- `StrengthenDomain` is needed, but it is domain-only. Do not reintroduce schedule rewriting there.
- The earlier top-level VPL symlink workaround was wrong. Do not reintroduce it.
- The direct cause of the earlier clean-build failure was running `make depend` outside `opam exec`; `coqdep` was simply missing from PATH.
- `PolOptPrepared.v` is no longer the place to read the final verified optimizer definition; that logic now lives in `driver/PolOpt.v`.
- C-path Pluto remains the oracle for optimization behavior, but do not use cross-source `polcert(our_before, c_before)` as an equality oracle because OpenScop metadata differs.
- For whole-suite source/after comparisons:
  - exact row-string equality is too strong because comments, names, and IDs differ
  - `SCATTERING` metadata and row-count shape are the first useful structural signal
  - only after structural agreement should finer mismatches be investigated

## Files to consult before continuing
- `doc/polopt-loop-suite-status.md`
- `doc/source-model-fidelity-goal.md`
- `LOG.md`
