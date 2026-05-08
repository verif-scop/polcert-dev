# Formalization Status

This document records the current proof boundary of the PolCert/PolOpt stack.
It is intentionally about the verified status of the implementation as it
exists now, not about speculative future extensions.

For the public naming and layering of the final affine+tiling route, see:

- [verified-phase-pipeline.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/verified-phase-pipeline.md)

For the architectural design rationale of the current verified pipeline, see:

- [verified-pipeline-design.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/verified-pipeline-design.md)

## 1. What Is Fully Covered Today

The current theorem-facing optimizer surface is the unified compiler wrapper:

```coq
compile : raw_config -> Loop.t -> imp ParallelLoop.t
```

The top-level theorem is
`driver/VerifiedParallelCompilerConfig.v:compile_correct`. It says that every
successful accepted config produces a `ParallelLoop.t` whose observable result
is matched by an execution of the original `Loop.t` under `State.eq`.

The main route shape is:

1. parse and elaborate a supported `.loop` program;
2. lower verified loop sugar such as literal stride ranges;
3. extract `Loop.t` into `PolyLang`;
4. strengthen and normalize the polyhedral program;
5. choose an accepted route through `check_config`;
6. ask Pluto only for route-specific middle artifacts or loop hints;
7. validate the accepted middle artifacts;
8. generate `ParallelLoop.t`.

The resulting verified optimizer supports:

- identity and affine-only routes;
- ordinary band-aware affine-plus-tiling;
- the historical generic tiling route behind `--legacy-generic-tiling`;
- second-level tiling on the checked tiled routes;
- ISS variants for identity, affine, full tiled, second-level, and diamond
  routes;
- checked diamond and full-diamond phase routes;
- checked explicit-current `parallel for` generation through the unified
  `Loop -> ParallelLoop` compiler;
- Pluto-hinted non-`multipar` `--parallel`, where Pluto supplies candidate
  current dimensions and the unified compiler rechecks the chosen dimension;
- checked vector routes using Pluto vector hints or explicit vector-current
  dimensions;
- checked loop-level unroll/jam and verified symbolic display simplification;
- verified positive- and negative-literal stride lowering before extraction.

This is no longer an affine-only or sequential-only story. Sequential routes
now return all-`SeqMode` `ParallelLoop` targets, while parallel-current routes
return `ParallelLoop` targets with `ParMode` annotations.

Diamond tiling is now part of the checked route surface. Its current proof
interpretation is still deliberately narrow:

- treat the diamond-specific work as a diamond-aware affine midpoint;
- validate the later tiling boundary with the ordinary checked tiling
  architecture;
- prove state-preserving semantic refinement, not the stronger performance
  properties from the diamond-tiling literature.

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

`current_view_pprog` is the crucial bridge used to reuse the codegen theorem
structure after a witness-centered tiling program has been checked. The unified
compiler wrapper then emits a `ParallelLoop.t`, either with all loops in
`SeqMode` or with checked `ParMode` annotations.

The diamond route follows the same layering:

- the diamond-specific intelligence belongs in the affine midpoint;
- the later tiling relation stays in the checked tiling architecture.

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

Current status:

- this route is now the default ordinary-tiling path in the `polopt` frontend
  for the non-ISS full tiled route
- it is included in the theorem-facing wrapper through
  `VerifiedParallelCompilerConfig`
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

The diamond public path follows the same phase discipline:

1. import and validate the diamond-aware midpoint;
2. validate the posttile target with the checked tiling architecture;
3. validate the final affine reschedule when Pluto produces one.

Confirmed working cases include:

- basic rectangular tiling
- second-level tiling
- skewed tiling
- diamond and full-diamond tiling
- diamond plus ISS, second-level tiling, and checked parallel-current routes

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

The current container-side smoke command is:

```bash
make -j4 artifact-check
```

The most recent confirmed run passed:

- extraction and `polopt`/`polcert` builds;
- `make -s check-admitted` with `Nothing admitted.`;
- proof report generation with no missing listed route theorem;
- capability matrix generation;
- Pluto compatibility suite with 105 checks;
- generated-C end-to-end checks for stride and unroll/jam cases;
- second-level tiling suite;
- diamond tiling suite.

The proof report lists the unified route:

- route: unified `Loop -> ParallelLoop` compiler config wrapper;
- theorem file: `driver/VerifiedParallelCompilerConfig.v`;
- theorem names:
  - `compile_correct`;
  - `compile_verified_correct`;
  - `compile_seq_verified_correct`;
  - `checked_sequential_current_annotated_codegen_correct`;
  - `compile_unsupported_no_result`.

## 9. What Is Still Out Of Scope

The remaining hard boundaries are narrower than before.

### 9.1 Memory-changing transformations

Scalar privatization, array contraction, storage remapping, and related
layout-changing transformations are outside the current `State.eq` theorem
boundary. They can be attacked as future validator families, but they need a
state relation that accounts for fresh or remapped storage.

### 9.2 Parallel and vector extensions beyond the current certificate

The current proof stack covers checked doall-style dimensions and the
`ParallelLoop` semantic bridge. It does not cover:

1. reduction-aware parallelization;
2. arbitrary nested or unbounded multi-parallel route selection as a single
   unified config theorem;
3. OpenMP runtime semantics beyond the verified loop-to-loop target semantics.

The existing `--multipar` path has checked multi-certificate code generation,
but it is still separate from the single-config `compile` wrapper.

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

The cleanest next extensions are:

1. fold the existing `--multipar` path into the single config wrapper or state
   its separate theorem boundary more prominently;
2. broaden vector-route evidence without changing the current doall
   certificate story;
3. finish a memory-changing validation layer for scalar privatization,
   contraction, and layout transformations;
4. add a generalized state relation for transformations that allocate,
   privatize, or remap storage.

That order keeps state-preserving polyhedral compilation separate from the
storage-changing families that need a different semantic relation.
