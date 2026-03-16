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

This is no longer an affine-only story. The verified pipeline now includes the
tiling route as a first-class checked phase.

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
- [Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v)
  - thin public aggregator with stable names

The optimizer entry point is assembled only once:

- [PolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/PolOpt.v)

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
- `src/TilingRelation.vo`
- `src/TilingBoolChecker.vo`
- `syntax/STilingOpt.vo`
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

What remains missing here is both:

1. the polyhedral legality side for wavefront / tile-space parallel schedules
2. the loop/codegen side that would target actual parallel loop semantics such
   as `#pragma omp parallel for`

The current verified semantics remain sequential loop semantics.

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
