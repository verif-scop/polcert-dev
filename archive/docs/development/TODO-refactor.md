# Refactor TODO

Date: 2026-04-10
Scope: current HEAD in container `/polcert` (`f367b11`, branch `end-to-end`)

## Why This Exists

The project's proof core is no longer the main organizational problem.
The larger engineering cost now comes from duplicated orchestration across:

- `driver/PolOpt.v`
- `driver/ParallelPolOpt.v`
- `syntax/SLoopMain.ml`
- `driver/Entry.ml`
- `tools/end_to_end_c/*`

The goal of this plan is to reduce duplication and sharpen boundaries without
destabilizing the proved core.

## Refactor Principles

1. Preserve current user-visible behavior first.
2. Refactor orchestration and boundaries before touching proof-heavy semantic kernels.
3. Keep the trust story explicit:
   - proved Coq core
   - extracted OCaml glue
   - external Pluto / OpenScop / witness inference interfaces
4. Prefer shared pipeline combinators over mode-specific copies.
5. Add regression coverage before or together with each structural move.

## Non-Goals

- Rewriting the core semantics in `src/PolyLang.v`
- Replacing Pluto as the scheduling engine
- Redesigning the Loop / PolyLang formalization from scratch
- Large proof rewrites unless a boundary cleanup forces them

## Workstream 1: Unified Pipeline Planning Layer

Problem:
- Default, ISS, affine-only, tiling, and parallel-current paths currently repeat
  the same high-level skeleton with small variations.

Current duplication hotspots:
- `driver/PolOpt.v`
- `driver/ParallelPolOpt.v`
- `syntax/SLoopMain.ml`

Plan:
- Introduce a shared planning layer that separates:
  - extraction + strengthening
  - external phase scheduling / ISS preparation
  - checked affine / tiling validation
  - materialization of the validated polyhedral result
  - final consumer: sequential codegen vs parallel codegen
- Target shape:
  - one internal "prepared validated poly program" path
  - one sequential consumer
  - one parallel consumer

Suggested landing pieces:
- `driver/PhasePipeline.v`
- `driver/OptimizationPlan.v`
- optional extracted-side mirrors if the Coq/OCaml split needs one

Acceptance criteria:
- `Opt`, `Opt_with_iss`, and `Opt_parallel_current*` stop re-encoding the same
  control flow by hand.
- Default and ISS routes share the same phase/tiling fallback structure.
- Parallel-current consumes the same validated intermediate that sequential
  codegen uses, instead of rebuilding a parallel-only variant of the path.

## Workstream 2: Split IR Semantics From External Tool Backends

Problem:
- `POLIRS` instances currently mix:
  - IR-specific semantics and types
  - external scheduler hooks
  - ISS inference hooks
  - tiling witness inference hooks

Current examples:
- `src/CPolIRs.v`
- `src/TPolIRs.v`
- `syntax/SPolIRs.v`

Plan:
- Split the current interface into at least two layers:
  - `POLY_IR`
    - instructions, state, types, Loop/PolyLang instances
  - `EXTERNAL_PIPELINE_BACKEND`
    - scheduler
    - phase scheduler
    - ISS import/inference
    - tiling witness inference
- Keep the trusted semantic instance separate from the untrusted external
  adapter.

Acceptance criteria:
- The trusted proof core no longer receives Pluto/OpenScop/bridge hooks through
  the same module type as instruction semantics.
- It becomes possible to describe the TCB without saying "POLIRS contains both
  semantics and external scheduling hooks".

## Workstream 3: Thin CLI / Entry Layers

Problem:
- `syntax/SLoopMain.ml` is acting as parser, dispatcher, profiler, validator
  wrapper, pretty-printer, and feature gate.
- `driver/Entry.ml` also mixes CLI parsing with validation orchestration.

Plan:
- Split `syntax/SLoopMain.ml` into focused modules:
  - `syntax/cli/ParseArgs.ml`
  - `syntax/cli/Dispatch.ml`
  - `syntax/cli/Pretty.ml`
  - `syntax/cli/Profile.ml`
  - `syntax/cli/StandaloneValidation.ml`
- Apply the same idea to `driver/Entry.ml` if it remains large after ISS and
  tiling helpers are moved.

Acceptance criteria:
- `SLoopMain.ml` becomes a small `main` wrapper.
- Mode selection logic lives in a dispatch module instead of being interleaved
  with pretty-printing and helper scripts.
- `polcert` and `polopt` CLI code can be understood without reading through the
  full extracted runtime interface.

## Workstream 4: Remove `polcert -> polopt` Subprocess Coupling

Problem:
- `polcert` currently delegates ISS validation modes by shelling out to
  `polopt`.

Current location:
- `driver/Entry.ml`

Plan:
- Move ISS bridge / dump validation entrypoints into a shared OCaml library
  linked by both binaries.
- Keep CLI binaries as thin shells over the same library functions.

Acceptance criteria:
- `polcert` no longer needs to locate and invoke `polopt` as a helper process
  for ISS modes.
- ISS validation is represented as shared library functionality, not binary
  coupling.

## Workstream 5: Unify Harness / Benchmark Runner Infrastructure

Problem:
- End-to-end harness logic is duplicated across handwritten cases, generated
  cases, best-pipeline search, and tuning scripts.
- Timeout, tolerance, OpenMP, and status/reporting behavior are not fully
  normalized across tools.

Current scope:
- `tools/end_to_end_c/*`

Plan:
- Extract a shared Python runner library for:
  - command execution with consistent timeout semantics
  - compile/run lifecycle
  - numeric comparison with explicit tolerance policy
  - OpenMP/thread configuration
  - summary/status serialization
- Keep thin entry scripts for each workflow:
  - single case
  - suite
  - generated suite
  - best-pipeline search
  - parameter tuning

Acceptance criteria:
- `run_case.py` and `run_generated_case.py` share one execution core.
- Binary runtime timeout behavior is uniform.
- Numeric comparison policy is documented once and implemented once.

## Workstream 6: Declarative Test Suites

Problem:
- Test coverage is growing as Make targets and one-off Python scripts.
- Suite definitions are encoded partly in Make, partly in scripts, and partly in
  docs.

Plan:
- Introduce suite manifests for:
  - strict generated loop suite
  - ISS suites
  - parallel-current suite
  - second-level tiling suite
  - whole-C harness suites
- Makefiles should call a smaller set of generic runners.

Acceptance criteria:
- Adding a new regression family does not require another bespoke Make target
  plus another standalone script unless the behavior is genuinely new.
- Expected case counts / thresholds / required tiled cases live in manifest data
  instead of being scattered through Make and Python.

## Workstream 7: Documentation Cleanup Around Supported Boundaries

Problem:
- Several user-facing docs describe capabilities at too high a level relative to
  the actual frontend or harness behavior.

Immediate doc debt to clean during refactor:
- supported `.loop` syntax in affine positions
- distinction between theorem-aligned routes and experimental CLI routes
- strict loop-suite guarantees vs heavier local-only perf harnesses
- trust boundary between proved core and external interfaces

Acceptance criteria:
- `README.md`, `POLOPT.md`, `POLCERT.md`, `syntax/README.md`, and
  `doc/FEATURE_STATUS.md` tell the same story.
- Unsupported frontend constructs are documented where users first look, not
  only in smoke tests or implementation details.

## Recommended Execution Order

1. Workstream 5: unify harness runtime behavior and reporting
2. Workstream 6: declarative test suites and cleaner regression wiring
3. Workstream 3: thin CLI / entry layers
4. Workstream 1: unified pipeline planning layer
5. Workstream 2: split semantic IR from external backend hooks
6. Workstream 4: remove `polcert -> polopt` subprocess coupling
7. Workstream 7: final doc pass after interfaces settle

Reasoning:
- Start with test/harness normalization so later structural changes are easier
  to verify.
- Thin CLI layers before deeper pipeline surgery so the dispatch surface is
  clearer.
- Split interfaces only after the duplicated flow is better understood through a
  unified planning layer.

## Artifact Submission Goal

The submission-facing artifact plan now lives in
[`doc/artifact-submission-goal.md`](artifact-submission-goal.md).

The immediate artifact priorities are:

- native Pluto-compatible `polopt` flag filtering;
- one-command artifact reproduction through `make artifact-check`;
- four-phase diamond route closure;
- second-level tiling suite and composition boundaries;
- generated capability matrix and proof report.

Diamond should be pushed to the limit of the current architecture. The current
sequential non-ISS single-level route is supported, but the artifact still needs
explicit work on frontend-rejection reporting, timeout stability, theorem/driver
closure, and combinations with ISS, parallel, and second-level tiling.

## Near-Term Concrete Tasks

- [x] Create a shared Python helper module under `tools/end_to_end_c/` for
      timeout-aware run/compile/report behavior.
- [x] Make generated and handwritten harnesses use the same numeric comparison
      policy.
- [ ] Split `syntax/SLoopMain.ml` into parse/dispatch/pretty/profile modules.
      Progress: parse/dispatch/common/ISS/profile slices are now extracted;
      standalone validation/import helpers remain the next low-risk cut.
- [ ] Extract a shared "validated poly result" pipeline helper from
      `driver/PolOpt.v` and `driver/ParallelPolOpt.v`.
- [ ] Draft a replacement for the current overloaded `POLIRS` boundary.
- [ ] Move ISS validator entrypoints behind a shared OCaml library instead of a
      subprocess hop.
- [x] Move strict loop-suite thresholds and required case lists into manifest
      data.
- [ ] Move remaining suite thresholds and required case lists into manifest
      data.
- [ ] Update user docs once the new module boundaries settle.

## Progress Notes

### 2026-04-10

Completed low-risk refactor slices aligned with Workstream 5 and 6:

- Added a shared `tools/end_to_end_c/runner_common.py` helper so handwritten
  and generated harnesses no longer depend on `run_case.py` as an implicit
  library surface.
- Centralized runtime timeout handling, output comparison, and run-directory
  lifecycle helpers in that shared module.
- Moved the strict generated loop regression thresholds into
  `tests/polopt-generated/strict_suite_manifest.json`.
- Changed `tests/polopt-generated/tools/check_polopt_cases.py` and
  `make test-polopt-loop-suite` to consume that manifest.
- Added manifest-driven flag-family regression suites for
  `parallel-current` and `second-level-tile`, backed by a shared
  `tools/polopt_flag_suites/manifest_runner.py`.
- Added manifest support to `tests/polopt-generated/tools/materialize_polopt_cases.py`
  so suite roots, case subsets, and `polopt` passthrough flags can move out of
  Makefile literals.
- Extracted `SLoopMain.ml` flag-model preflight checks into dedicated helpers,
  aligning the implementation more closely with the route-family layering
  documented in `POLOPT_FLAG_GUIDE.md`.

Immediate next refactor candidates after this slice:

1. Continue Workstream 6 by introducing manifests for diamond generated and
   whole-C regression families.
2. Start Workstream 3 by shrinking `syntax/SLoopMain.ml` into
   parse/dispatch/pretty/profile submodules before touching deeper Coq
   orchestration.
3. Use the thinner CLI surface to guide a later Workstream 1 extraction of the
   shared validated polyhedral pipeline between sequential and parallel modes.

### 2026-04-10 (later)

Follow-up landing after the initial harness normalization:

- Pushed `f367b11` on `end-to-end`:
  - manifestized `parallel-current` and `second-level-tile` regression suites
  - moved strict loop-suite materialization parameters into
    `tests/polopt-generated/materialize_manifest.json`
  - tightened `SLoopMain.ml` flag-model preflight validation into named helpers
- Rebased `/worktrees/polcert-diamond-phase-20260409` onto `f367b11` and
  revalidated:
  - `make test-polopt-diamond-generated` passes after the rebase
  - `tools/diamond_tiling/run_pluto_diamond_suite.py` passes at the default
    suite timeout
  - the earlier `heat-3d-imperfect.c` timeout only reproduces under an
    aggressive `--timeout-seconds 30` smoke budget; the default suite no longer
    has a residual failing case

Concrete remaining refactor items after this update:

1. Continue splitting `syntax/SLoopMain.ml` into parse/dispatch/profile/
   pretty/standalone-validation modules now that flag preflight checks are
   isolated.
2. Decide whether the diamond live suite should grow per-case timeout metadata
   if shorter smoke budgets are meant to stay actionable for heavier cases like
   `heat-3d-imperfect.c`.

### 2026-04-10 (diamond manifest follow-up)

- Moved the diamond generated regression suite onto manifest data:
  - `tests/polopt-diamond/materialize_manifest.json`
  - `tests/polopt-diamond/strict_suite_manifest.json`
- Simplified the corresponding `Makefile` targets so the case list, timeout,
  `--diamond-tile` passthrough, and strict thresholds are no longer duplicated
  in Make variables.
- Revalidated with `make test-polopt-diamond-generated`; the suite still passes
  `4/4 ok`.

### 2026-04-10 (CLI front-half split)

- Started Workstream 3 on `end-to-end` by extracting the lowest-risk CLI
  front-half from `syntax/SLoopMain.ml` into a new `syntax/SLoopCli.ml` module.
- Moved:
  - `usage`
  - `config`
  - `parse_args`
  - `validate_flag_model`
  - `configure_scheduler_modes`
- Updated `Makefile.extr` so incremental OCaml builds know `SLoopMain`
  depends on `SLoopCli`.
- Revalidated with:
  - `opam exec -- make polopt`
  - `opam exec -- make test-parallel-current-suite`
  - `opam exec -- make test-second-level-tile-suite`
  - `opam exec -- make test-polopt-loop-suite`

Next safe extraction targets after this slice:

1. standalone validation/import helpers such as `read_openscop_or_fail`
2. stage timing and profiling helpers

### 2026-04-10 (route-spec and profile follow-up)

- Pushed two more mainline commits on `end-to-end` after the initial CLI split:
  - `5622935` `Factor polopt flag routing through explicit route specs`
  - `c86dc6f` `Stabilize strict loop materializer scratch directories`
- The route-spec landing introduced:
  - `syntax/SLoopConfig.ml`
  - `syntax/SLoopRoute.ml`
  - `syntax/SLoopDispatch.ml`
- The strict loop materializer now writes each case through a scratch directory
  and only swaps it into place once the case is complete, fixing the earlier
  `advect3d`/`tce`-style half-materialized directory hazard.
- Pushed `00809b2` `Extract profiling helpers from SLoopMain`, which moved
  stage-timing and structural-stat helpers into `syntax/SLoopProfile.ml`.
- Revalidated this post-split state with:
  - `opam exec -- make polopt`
  - `opam exec -- make test-polopt-loop-suite`
  - `opam exec -- make test-iss-pluto-live-suite`
  - `opam exec -- make test-parallel-current-suite`
  - `opam exec -- make test-second-level-tile-suite`

Updated next safe extraction targets after this follow-up:

1. standalone validation/import helpers such as `read_openscop_or_fail`,
   `run_affine_validator`, and tiling witness/validator wrappers
2. deeper `polopt` route execution helpers once the CLI shell is thinner

## Success Condition

This refactor is successful if:

- the number of mode-specific pipeline copies is materially reduced,
- the trust boundary is easier to explain,
- `polopt` and `polcert` orchestration becomes thinner and more local,
- harness behavior is consistent across workflows,
- adding a new route no longer requires edits across proof driver, OCaml CLI,
  Make targets, and multiple benchmark scripts at the same time.
