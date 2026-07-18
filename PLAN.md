# PolCert Working Plan

Date: 2026-03-05

Current priority updated: 2026-07-18

## Current Priority (State.eq Milestone)

The completed `State.eq` result must first be frozen as a reproducible research
milestone. Proof cleanup should happen only after that baseline is archived, on
a separate branch, so it cannot blur which source version supports the current
claims.

### 1. Freeze and document the completed milestone

- [x] Treat annotated tag
  `state-eq-polyhedral-verification-complete-2026-05-25-v2` (commit
  `13295e741ad62173411882c6d900dd9dc57337a8`) as the current implementation
  baseline; do not move or overwrite it.
- [x] Check out that exact commit in a clean worktree and run the complete
  proof, extraction, regression, and `artifact-check` workflow.
- [x] Archive the proof report, admitted/axiom checks, capability matrix,
  regression results, command log, and toolchain manifest produced by that
  exact run.
- [x] Add a durable milestone document that maps every paper-facing claim to a
  theorem, executable route, test family, and known boundary.
- [x] Record the exact PolCert and Pluto commits together. The verified Pluto
  baseline is `6f43860b6c4cddeeca09189bf3073f05b78b14a5`.
- [ ] If archival metadata or scripts require a new commit, create a new
  annotated archival tag rather than changing the completed-result tag.

### 2. Build a new reproducible Docker artifact

- [x] Build a Docker image from the frozen source baseline, with the exact
  source tree, Pluto/base-image digest, Coq, and OCaml versions pinned.
- [x] Include source, proofs, extracted executables, benchmarks, test inputs,
  artifact scripts, claim matrix, and reviewer documentation in the image.
- [x] Provide one reviewer-facing command that rebuilds or checks the proofs,
  checks for admitted obligations, regenerates proof/capability reports, and
  runs all claimed transformation families.
- [x] Cover the full supported route surface in the artifact: affine
  scheduling, ordinary/identity/second-level/diamond tiling, ISS, parallel and
  multipar, checked vector routes, the supported unroll/jam subset, stride
  lowering, cleanup, and their documented supported compositions.
- [x] Re-run the Pluto flag-compatibility suites, including the comprehensive
  compatibility suite and strict regression corpus, and preserve both positive
  and expected-rejection results.
- [x] Label the local image with source revisions and dependency versions and
  record content ID
  `sha256:573831494258848d553801ee244b9d49ee8f84c2d39716255637b2c8970bfd6f`.
- [ ] Publish the image and record its registry digest; finish locking Ubuntu
  apt and non-Coq opam package versions.
- [x] Test the documented commands from a fresh Docker environment and archive
  the resulting logs. After the image has been pulled, the core reproduction
  path should not require network access.
- [x] Keep the artifact guide claim-oriented: each claim should name the exact
  command and expected output that demonstrates it.

### 3. Simplify the affine-scheduling proofs

This is proof-maintenance work, not a missing-correctness obligation. Begin it
only after the completed baseline and its artifact evidence are recoverable.

- [x] Create dedicated branch `proof-cleanup-affine-batch1` from the frozen
  milestone. Its first proof-only commit is `50aefe5`.
- [x] Inventory copy-pasted and structurally repeated proof blocks in the
  original affine-scheduling validator and its helper lemmas.
- [x] Record a pre-refactor baseline: public theorem statements, assumptions,
  extraction output, build result, and relevant regression results.
- [ ] Factor repeated reasoning into narrowly scoped lemmas or local tactics;
  improve theorem/variable names and comments where the invariants are hard to
  recover from the proof script.
  - [x] First slice: replace the duplicate
    `nth_error_compose_ipl_ext_inv` induction with the existing local lemma and
    add proof-structure comments, without changing net source lines.
  - [x] Second slice: factor WW/WR/RW access-to-cell noncollision lifting into
    one local helper, reducing `AffineValidator.v` by 17 lines.
  - [x] Third slice: share access-transformation shape facts across the three
    collision branches, reducing `AffineValidator.v` by another 16 lines.
- [ ] Preserve theorem statements, accepted schedules, extracted behavior, and
  trust assumptions unless a deliberate semantic change is separately
  justified.
- [ ] Refactor in small reviewable commits, rebuilding the dependent proof
  chain and rerunning assumption and regression checks after each slice.
- [ ] Avoid a wholesale rewrite. Stabilize the paper-facing theorem interface
  first, then clean the portions readers are most likely to inspect.
- [ ] Refresh the Docker artifact after cleanup only if the cleaned revision is
  chosen as the paper artifact; retain the original milestone image and digest.

### 4. Write the paper

- [x] Freeze a contribution ledger against the archived artifact before making
  headline claims.
- [x] Rewrite the abstract, introduction, and contribution list relative to the
  inherited affine-scheduling validator: the new contribution is the completed
  end-to-end, multi-family verified compiler path, not affine scheduling itself.
  The draft is `0219e1a`; the LaTeX integration is `31e205c`.
- [x] State the exact correctness boundary around `State.eq`, including why
  storage-changing transformations remain outside this theorem family.
- [x] Make tiling and its supported variants the central technical extension;
  present ISS and parallel/multipar as substantial semantic extensions, with
  vector, unroll/jam, stride lowering, and cleanup as supporting checked routes.
- [ ] Derive all capability tables and evaluation numbers from the frozen
  artifact outputs. The first exact-tag artifact table is committed at paper
  revision `5424324`; remaining evaluation presentation is still pending.
- [ ] Audit theorem names, implementation paths, capability counts, references,
  and limitations consistently across the abstract, introduction, technical
  sections, evaluation, and conclusion.

Paper drafting can begin once the claim ledger is frozen; it need not wait for
every cosmetic proof cleanup. Storage generalization and overlapped tiling are
separate future research tracks and are not prerequisites for this paper.

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
