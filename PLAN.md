# PolCert Working Plan

Date: 2026-03-05

## Direction
- Follow your default route:
  - Decision #1: depth gap via translation/normalization layer (reuse PolyGen proof)
  - Decision #2: optimistic overflow by runtime guard + fallback
  - Decision #3: tiling starts from verified Loop-level strip-mining

## Milestone 0 (in progress)
1. Baseline audit
- [x] Read `README.md` and confirm intended workflow
- [x] Confirm container/repo state
- [x] Run `check-admitted`
- [x] Quick proof/assumption scan (`Admitted/Abort/Axiom/Parameter`) in `src/polygen/driver`
- [x] Generate `doc/TODO-proof.md` for full scoped dependency map
- [x] Map TCB/untrusted boundaries (external scheduler, extraction constants, backend assumptions), with explicit trust story

2. Reproducible baseline commands
- [x] Verify executable path (`./polcert`)
- [x] Verify one OpenScop validation case
- [x] Add a small script/notes for repeatable baseline checks in container
- [x] Run representative tests (`scopreader-test`, `csample1-test`, `csample2-test`)

## Current Position (snapshot)
- Container/toolchain status: usable and stable (`gifted_curie`, branch `extractor`, commit `c48a0ff`).
- Build/test status: core checks pass in-container after opam env setup.
- Formal status: only one direct unfinished proof hole in project core path remains in `src/Extractor.v` (`extract_stmt_to_loop_semantics_core`).
- Integration status: optimization pipeline exists (`Extractor -> scheduler'+validate -> CodeGen`), but there is no end-to-end `Opt_correct` theorem wiring `CodeGen.codegen_correct` into `driver/PolOpt.v`.
- Codegen linkage status: `polygen/CodeGen.v` has `codegen_correct`, but it is not referenced outside that file, and the README still states a `depth` semantics gap for reuse of PolyGen proofs.
- Research bottleneck: end-to-end verified pass is blocked by (1) extractor correctness closure and (2) explicit depth-gap bridging/alignment theorem(s) for codegen reuse.

## Next (Milestone 1 start)
1.1 Scope boundary
- [x] Introduced explicit `wf_scop_stmt` predicate for extractor-supported Loop subset.
- [x] Extractor now rejects non-affine fragment upfront with explicit `Err`.

1.2 Proof closure
- Eliminate `Admitted` in `Extractor.extractor_correct` via staged lemmas:
  - expression-to-affine soundness
  - bound/condition-to-constraint soundness
  - structural induction over `extract_stmt`

## Progress Update (2026-03-05, later)
- Phase 0 definition stabilization for extractor is implemented in working tree and `src/Extractor.v` compiles in container.
- Next concrete proof step is now:
  - derive theorem-level consequence from `check_extracted_wf`;
  - then expand `extractor_correct` branch-by-branch using `remember/destruct` skeleton.

## Progress Update (2026-03-05, latest)
- Added explicit syntactic fragment gate in extractor:
  - `wf_scop_stmt`, `wf_affine_expr(_list)`, `wf_affine_test`.
  - new lemma: `extractor_success_implies_wf_scop`.
- Added reusable bridge lemmas for proof engineering:
  - `exprlist_to_aff_correct`
  - `wf_affine_expr_true_expr_to_aff_success`
  - `wf_affine_expr_list_true_exprlist_to_aff_success`
  - `wf_affine_test_true_test_to_aff_success`
  - `guard_constraints_sound`
- Container compile status remains green:
  - `opam exec -- coqc ... src/Extractor.v`
  - `opam exec -- coqc ... driver/PolOpt.v`
  - `make -s check-admitted` still reports only `src/Extractor.v:Admitted.`

## Progress Update (2026-03-05, latest+1)
- Refactored `extractor_correct` into a closed wrapper theorem (`Qed`).
- Introduced one explicit core semantic lemma:
  - `extract_stmt_to_loop_semantics_core` (currently `Admitted`).
- Added proved wrapper bridge:
  - `loop_semantics_intro_from_envv`.
- Re-validated compile chain:
  - `opam exec -- coqc ... src/Extractor.v`
  - `opam exec -- coqc ... driver/PolOpt.v`
  - `make -s check-admitted` unchanged (single entry).

## Current TODOs
1. GitHub CI for source repo
- Add a GitHub Actions workflow to the code repo so every push/PR runs:
  - `make clean`
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make -s check-admitted`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`
  - strict `polopt` regression suite (`tests/polopt-regression/tools/materialize_polopt_cases.py`)
  - `make test`
- Prefer one canonical workflow that uses the same README build order as local acceptance.
- Cache opam where possible, but do not change the build semantics to chase cache hits.

2. Verified cleanup pass
- Current `syntax/SLoopPretty.ml` still performs display-layer simplification only.
- Desired direction:
  - move the simplification logic to a Coq `Loop -> Loop` pass after codegen
  - prove semantic preservation
  - then optionally keep a thin pretty-printer normalization on top
- Candidate subpasses:
  - algebraic simplification of `expr` / `test`
  - `Seq` / trivial `Guard` cleanup
  - singleton-loop elimination (`for x in [e, e+1)`) via verified substitution

## Progress Update (2026-03-09, tiling)
- Built an experimental OCaml tiling validator into container `polopt`:
  - `./polopt --extract-tiling-witness-openscop before.scop after.scop`
  - `./polopt --validate-tiling-openscop before.scop after.scop`
- Current OCaml structure is now explicit:
  - extract witness
  - check witness
  - validate = extract + check
- Current validated Pluto tiling families:
  - basic tiling
  - second-level tiling
  - skewed tiling
  - diamond tiling
- Supporting parser work was also necessary:
  - `OpenScopParser.mly` now skips Pluto `<loop>` extensions instead of failing to parse them
- First Coq tiling formalization entry is now concrete, not just a note:
  - `src/TilingWitness.v`
  - currently formalizes:
    - affine expression evaluation
    - `tile_parent = floor(phi / T)`
    - interval soundness for one link
    - lifted-point length/suffix properties

## Near-Term Next
1. Replace the temporary padded-transformation `Admitted` theorems in `src/TilingRelation.v`.
2. Keep the current runtime split explicit:
  - validator-side padded transformation
  - syntax/codegen-side source-argument lifted transformation
3. Investigate and, if practical, eliminate the residual runtime warning:
  - `isl_map.c:12117: number of columns too small`
4. Preserve the current phase-aligned consumption structure:
  - `polcert`: 2-input auto, 3-input phase-aligned
  - `polopt`: affine-only Pluto, then tile-only Pluto, then two validation gates
5. After the padded-transformation proof debt is closed, re-check whether any of the now-debug-only syntax hooks can be simplified or removed.

## Progress Update (2026-03-19, artifact-strengthening)

The current bottleneck is no longer proof closure in isolation. The artifact
now has theorem-aligned affine, tiling, ISS, and explicit-dimension parallel
routes, and the strict loop suite already succeeds.

The next milestone is therefore artifact strengthening rather than another
single-feature proof push.

The active roadmap is now recorded in:

- `work/container-overlay/polcert/doc/ARTIFACT_STRENGTHENING_PLAN.md`

That roadmap supersedes this file for the next iteration of work. Its four main
tracks are:

1. whole-C end-to-end wrapper and performance harness
2. `advect3d` codegen performance repair
3. Pluto bug reproducibility / validator-value case studies
4. diamond tiling as an affine-midpoint-plus-ordinary-tiling track
   - first target: sequential correctness through a diamond-aware midpoint
   - later target: concurrent-start / load-balance style properties

## Progress Update (2026-03-23, generated perf harness)

The whole-C artifact-strengthening track now has a concrete generated perf
campaign:

- a wrapper-based generated C harness over the 62-case regression corpus
- tiered parameter sizing (`smoke / perf / heavy`)
- per-case best-pipeline search across:
  - default no-ISS affine+tiling
  - affine-only
  - ISS
  - parallel (`4` threads)
  - ISS+parallel (`4` threads)
  - identity fallback
- a fixed report table:
  - `work/container-overlay/polcert/tests/end-to-end-generated/BEST_PIPELINES.md`
- one-command local refresh:
  - `opam exec -- make test-end-to-end-generated-perf-refresh`

This generated perf campaign is intentionally not part of default CI. It is a
local artifact-evaluation workflow, not a minimal regression gate.
