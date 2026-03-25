# Formalization Status

This document records the current proof boundary of the PolCert/PolOpt stack.
It is intentionally about the verified status of the implementation as it
exists now, not about speculative future extensions.

For the public naming and layering of the final affine+tiling route, see:

- [verified-phase-pipeline.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/verified-phase-pipeline.md)

For the architectural design rationale of the current verified pipeline, see:

- [verified-pipeline-design.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/verified-pipeline-design.md)

## 1. What Is Fully Covered Today

The current mainline proof stack covers the following end-to-end route:

1. extract a loop program into `PolyLang`
2. strengthen/normalize the polyhedral program
3. run the affine scheduler route and validate `before -> mid`
4. run the tiling phase route and checked-validate `mid -> after`
5. convert the tiled result through `current_view_pprog`
6. reuse the existing affine codegen correctness chain
7. generate sequential loop code

The resulting verified optimizer therefore supports:

- sequential affine rescheduling
- checked phase-aligned tiling
- verified codegen after successful checked tiling
- verified fallback to the affine-only route when the tiling route does not
  complete successfully
- verified single-dimension `parallel for` generation after checked
  certification on `current_view_pprog`
- Pluto-hinted checked parallelization via `--parallel`
- manual checked parallelization via `--parallel-current d`
- both default and `--iss` frontend routes for:
  - identity/no-schedule codegen
  - affine-only codegen
  - full tiled codegen

This is no longer an affine-only story. The verified pipeline now includes the
tiling route as a first-class checked phase, and it also includes a first
version of verified parallel loop generation.

Diamond tiling is not on the current mainline checked path yet, but the design
boundary is already settled in the notes:

- sequentially, it should be treated as a diamond-aware affine midpoint on
  `before -> mid_diamond`
- followed by ordinary checked tiling on `mid_diamond -> after`

This is a narrower claim than the full diamond-tiling paper story. The current
theorem direction would aim at sequential refinement, not at certifying:

- concurrent-start optimality
- maximal tile-level parallelism
- load balance
- tile-size-ratio conditions needed for those stronger properties

## 2. The Main Semantic Boundary

The proof stack is still ultimately grounded in:

- `PolyLang.instance_list_semantics`
- `PolyLang.semantics`
- `Loop.semantics`

The key semantic shift introduced by tiling is that the current point-space and
the source/base point-space are no longer implicitly the same object. That is
why the witness-centered layer is now explicit:

- `pi_point_witness`
- `current_base_point_of`
- `current_src_args_of`
- `current_view_pprog`

`current_view_pprog` is the crucial bridge used to reuse the older affine
codegen theorems after a witness-centered tiling program has been checked.

The same intended layering applies to future diamond support:

- the diamond-specific intelligence belongs in the affine midpoint
- the `mid -> after` checked tiling relation should stay ordinary

## 3. What The Verified Tiling Route Actually Checks

The tiling route is split into two logically different parts.

### 3.1 Structural / witness-side checking

This lives in:

- [TilingBoolChecker.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingBoolChecker.v)

Its role is to check the source-side tiling relation:

- the witness is well-formed
- the imported tiled program matches the witness
- lifted domains, transformations, and accesses line up with the source-side
  interpretation

### 3.2 Generic dependence / schedule validation on the tiled program

This lives in:

- [AffineValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/AffineValidator.v)
- [TilingValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingValidator.v)

The important distinction is:

- `validate` is the affine-only validator
- `validate_general` is the witness-aware generic validator core
- `checked_tiling_validate_poly` is the full checked tiling validator on the
  outer `PolyLang` program type

The full checked tiling validator is therefore:

1. structural tiling/witness checking
2. import to the canonical tiled representation
3. generic validation on the imported tiled program

This is also why the current design notes do not recommend a separate
"diamond tiling theorem family". For sequential correctness, diamond should
reuse this same checked tiling structure after importing a diamond-aware
midpoint.

### 3.3 Band-aware ordinary-tiling route

The repository now also contains an alternative band-aware ordinary-tiling
schedule validator:

- [TilingBandScheduleValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingBandScheduleValidator.v)
- [PolOptBandTiling.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOptBandTiling.v)

At the moment, the repository has two different notions of "default":

- the Coq mainline theorem route in `driver/PolOpt.v` still uses the historical
  generic `checked_tiling_validate_poly` path
- the default `polopt` frontend route for the non-ISS full tiled path now uses
  the band-aware route, with the historical generic route retained behind
  `--legacy-generic-tiling`

Its purpose is narrower and more Pluto-specific:

1. recover the tiled band from the tiling witness
2. check that `after` has the expected strip-mined schedule shape for that band
3. check the band-specific legality obligation on the induced reordered pairs

The proof stack for this route now also contains a Pluto-facing declarative
specification layer for permutable bands, not only the operational reordered-
pair obligation used by the executable checker.

Important caveat:

- this route is now the default ordinary-tiling path in the `polopt` frontend
  for the non-ISS full tiled route
- it is not yet the default theorem family inside `driver/PolOpt.v`
- the current executable checker is already band-aware, but it still reuses the
  list-level validator kernel (`validate_instr_list`) rather than introducing a
  brand-new dependence emptiness engine
- the historical generic checked tiling route is still present as a legacy
  path and remains useful as a comparison baseline

## 4. Current File-Level Structure

Validator-related modules are now organized by role rather than by historical
accumulation:

- [AffineValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/AffineValidator.v)
  - affine-only validator core
  - witness-aware generic validator core
- [TilingValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingValidator.v)
  - conversion between outer and tiling-specific views
  - canonical tiled import
  - checked tiling validator
  - checked tiling + codegen bridge
- [TilingBandScheduleValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingBandScheduleValidator.v)
  - experimental band-aware ordinary-tiling schedule validator
  - inferred-band certificates
  - declarative Pluto-style permutable-band specs
  - bridge from band-aware schedule checking to the existing tiling semantics
- [Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v)
  - thin public aggregator with stable names

The optimizer entry point is assembled only once:

- [PolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOpt.v)

The experimental band-aware route is assembled separately in:

- [PolOptBandTiling.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOptBandTiling.v)

Concrete language instantiations are intentionally thin wrappers:

- [TPolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/TPolOpt.v)
- [CPolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/CPolOpt.v)
- [SPolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/syntax/SPolOpt.v)
- [STilingOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/syntax/STilingOpt.v)
- [TPolValidator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/TPolValidator.v)

These wrapper modules should remain definition-only. The generic theorems belong
in the shared `src/` layer.

## 5. Current Naming Boundary

The codebase now uses clearer public names while keeping older names as
compatibility aliases.

Preferred public names:

- Pluto / scheduler boundary
  - `affine_scheduler`
  - `export_for_pluto_phase_pipeline`
  - `run_pluto_phase_pipeline`
- validator boundary
  - `check_wf_polyprog_general`
  - `validate_general`
  - `checked_tiling_validate_poly`
- optimizer boundary
  - `checked_affine_schedule`
  - `affine_only_opt_prepared_from_poly`
  - `try_verified_tiling_after_phase_mid`
  - `phase_pipeline_opt_prepared_from_poly`

The historical names still exist as aliases:

- `scheduler`
- `to_phase_openscop`
- `phase_scop_scheduler`
- `check_wf_polyprog_tiling`
- `validate_tiling`
- `outer_to_tiling_pprog`
- `checked_tiling_validate_outer`

The main purpose of this cleanup is to remove one recurring ambiguity:

- the fallback path is not "Pluto failed, so use non-Pluto"
- it is "the dedicated two-stage Pluto phase pipeline did not produce a fully
  checked tiling route, so use the already-verified affine-only route"

## 6. Runtime Status

The verified tiling gate is now consumed by both `polcert` and `polopt`.

### 6.1 `polcert`

The phase-aligned validation path is:

1. import `mid.scop` and `after.scop`
2. infer a tiling witness
3. build the canonical tiled skeleton
4. import Pluto's final schedule over that skeleton
5. run the extracted checked tiling validator

If future diamond support is added on the public path, the intended extension is:

1. import and validate `mid_diamond` as an affine midpoint
2. infer the ordinary floor-link tiling witness from `(mid_diamond, after)`
3. reuse the same checked tiling validator

That future path would still certify sequential correctness only unless extra
diamond-specific witness material is introduced.

Confirmed working cases include:

- basic rectangular tiling
- second-level tiling
- skewed tiling

The three-input phase-aligned checker now succeeds on:

- affine `before -> mid`
- tiling `mid -> after`

### 6.2 `polopt`

The verified optimizer now uses:

1. the affine-only checked route when no loop dimensions exist, or when the
   phase-aligned tiling route does not complete successfully
2. the checked tiling route when the two-stage Pluto phase pipeline succeeds

Confirmed real examples include:

- `syntax/examples/matadd.loop`
- `syntax/examples/covariance.loop`
- `syntax/examples/covariance_outer.loop`

These now generate genuinely tiled loop nests, not only proof-only intermediate
objects.

## 7. Codegen Status

The current codegen story is closed through `current_view_pprog`.

This matters because the older affine codegen theorems were not rewritten to
reason directly about arbitrary witness-centered programs. Instead, the proof
goes through:

1. checked tiling validation on the witness-centered tiled program
2. `current_view_pprog`
3. the older affine codegen correctness chain

Important theorems:

- [PrepareCodegen.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PrepareCodegen.v)
  - `prepared_codegen_correct_general`
- [TPolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/TPolOpt.v)
  - `checked_tiling_prepared_codegen_correct`
- [CPolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/CPolOpt.v)
  - `checked_tiling_prepared_codegen_correct`

## 8. Confirmed Build / Test Status

The last fully confirmed container-side build reached all of:

- `src/PolyLang.vo`
- `src/PrepareCodegen.vo`
- `src/Validator.vo`
- `src/ParallelValidator.vo`
- `src/ParallelCodegen.vo`
- `src/TilingRelation.vo`
- `src/TilingBoolChecker.vo`
- `polygen/ParallelLoop.vo`
- `driver/ParallelPolOpt.vo`
- `driver/PolOptBandTiling.vo`
- `syntax/STilingOpt.vo`
- `syntax/STilingBandSched.vo`
- `driver/TPolOpt.vo`
- `driver/CPolOpt.vo`
- `polopt`
- `polcert`

Additionally:

- no `Admitted.` remained under:
  - `src/`
  - `driver/`
  - `syntax/`
  - `polygen/`
- the generated optimizer suite succeeded:
  - total: `62`
  - ok: `62`
  - fail: `0`
  - changed: `60`
- the experimental band-aware ordinary-tiling route matched the baseline on the
  generated optimizer suite:
  - `status.txt` mismatches: `0`
  - `optimized.loop` mismatches: `0`
- the following parallel smoke routes were manually confirmed:
  - `--parallel`
  - `--parallel --parallel-strict`
  - `--parallel-current d`
  - `--iss --parallel`
  - `--iss --parallel --parallel-strict`
  - `--iss --parallel-current d`

## 9. What Is Still Out Of Scope

The current verified mainline still does not cover:

### 9.1 ISS

ISS is not just a schedule reordering. It changes statement/domain structure and
requires one-to-many statement reasoning rather than a one-to-one validator.

That is no longer completely out of scope in the codebase:

- there is now a dedicated ISS validator line in `polcert`
- the extracted runtime checker validates Pluto-style
  `complete-cut-shape` witnesses
- proof-only modules establish the backward semantic correctness theorem for
  that checker
- Pluto can emit a native ISS bridge consumed by
  `./polopt --validate-iss-bridge`

What remains out of the default verified mainline is narrower:

- ISS is still not enabled in the default `PolOpt` phase pipeline
- the ISS suites are still manual rather than part of default CI
- the Docker-pinned Pluto image still needs to move from `latest` to the
  versioned ISS bridge image

### 9.2 Parallel semantics and parallel codegen

This area is no longer completely out of scope.

The current codebase now includes:

- a dedicated checked parallel validator line
- a `ParallelLoop` IR with explicit `ParMode`
- an abstract verified `par for` semantics
- a refinement bridge back to sequential loop semantics
- checked parallel codegen driven by either:
  - Pluto `--parallel` hints
  - or manual `--parallel-current d`
- frontend support on both the default and `--iss` routes

What remains out of scope is narrower:

1. reduction-aware parallelization
2. nested / multi-parallel loop generation
3. a larger systematic regression matrix rather than the current focused smoke
   coverage
4. any claim about verified OpenMP/C runtime semantics beyond the verified
   loop-to-loop semantics currently used by PolCert

### 9.3 Fully verified witness extraction

The checked tiling pipeline assumes that a witness is supplied or inferred and
then *checked*. The checker is verified; the witness inference glue is still an
untrusted producer whose output is validated.

This is an intentional proof boundary.

## 10. Residual Runtime Caveats

One remaining practical caveat is the Pluto/runtime warning:

- `isl_map.c:12117: number of columns too small`

At present this warning does not block:

- affine validation
- checked tiling validation
- current example-level tiled code generation

It is therefore a runtime cleanliness issue, not a current proof blocker, but it
is still worth isolating later.

## 11. Recommended Next Extensions

If the project extends beyond the current verified affine+tiling pipeline, the
cleanest order remains:

1. richer schedules without domain growth
2. domain-augmenting transformations such as more aggressive tiling variants
3. statement/domain splitting transformations such as ISS
4. true parallel code generation over an explicit concurrent loop semantics

That order preserves the current semantic layering instead of collapsing several
orthogonal generalizations into one step.
