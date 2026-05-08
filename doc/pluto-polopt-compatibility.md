# Pluto-Polopt Compatibility Surface

Date: 2026-05-08

Audience: PolCert developers who need to align `polopt` with Pluto as the reference optimizer.

## Purpose

`polopt` should be understood as a Pluto-compatible checked subset, not as a separate optimizer with unrelated flags. The intended architecture is:

```text
Pluto-like optimizer flags
  -> polopt flag normalizer
  -> capability filter with explicit rejection reasons
  -> Pluto used only as optimization oracle
  -> validator/import/codegen in polopt
```

This document records what is supported, what is not supported, why it is not supported, and how each unsupported part could be supported.

The main design point is that Pluto's CLI mixes several layers:

- frontend extraction
- dependence analysis and solver selection
- affine scheduling and fusion
- tiling and tile scheduling
- code generation and post-codegen rewrites

`polopt` should align with Pluto's optimizer-facing surface. It should reject Pluto flags that belong to Pluto's frontend or codegen surface, unless `polopt` implements an equivalent checked feature.

## Evidence Used

The current assessment is based on these concrete checks.

- Pluto source inspection in `/pluto`:
  - `tool/main.cpp`: option parser, normalization rules, main pass order
  - `lib/program.cpp`: actual default values
  - `lib/pluto.c`: affine scheduling, fusion, custom `.fst/.precut`, diamond insertion
  - `lib/tile.c`: tiling, second-level tiling, tile scheduling, intra-tile optimization
  - `lib/iss.c`: ISS restrictions
  - `tool/pluto_codegen_if.c` and `tool/ast_transform.c`: OpenMP, vector, unroll-jam marking
- Current Pluto build:
  - version: `polcert-pluto-baseline-7cb0892-1-gac5ea83`
  - `config.h` has no `GLPK` or `GUROBI`
  - Pluto's own `./test.sh` passed after building `test_libpluto` and `unit_tests`: `65 / 65`
- Current `polopt` route inspection:
  - `syntax/SLoopRoute.ml`: route normalization and explicit rejections
  - `driver/Scheduler.ml`: actual Pluto flag recipes sent by `polopt`
- Executed compatibility wrapper:
  - `tools/polopt_flag_suites/pluto_compat_driver.py`
  - `tools/polopt_flag_suites/run_pluto_compat_suite.py`
  - result: `105` checks passed in the current smoke suite
- Executed diamond validation suite:
  - `make test-diamond-tiling-suite`
  - result: the checked diamond and full-diamond fixtures validate through the
    current four-phase route; Pluto/Clan frontend failures remain rejected as
    frontend failures rather than validator failures
- Executed reviewer-facing smoke:
  - `make -j4 artifact-check`
  - result: proof report, capability matrix, Pluto-compatible flag suite,
    generated-C checks, second-level suite, and diamond suite completed

One important correction: Pluto's `--help` is not reliable for defaults in this build. The help text says some features are disabled by default, but `lib/program.cpp` initializes `tile=1`, `parallel=1`, `diamondtile=1`, `intratileopt=1`, `prevector=1`, `unrolljam=1`, and `smartfuse`.

## Status Classes

This document uses five status classes.

| Status | Meaning |
|---|---|
| Supported | Current `polopt` exposes a checked route and tests exercise it. |
| Surface gap | Pluto can express it and current validators likely suffice, but `polopt` does not yet expose the flag or route. |
| Composition gap | Existing validators cover pieces, but the requested flag combination needs a new composed route, witness plumbing, or theorem invocation sequence. |
| Validator/semantic gap | Supporting it needs a new validator, codegen proof, or operational semantics argument. |
| Out of optimizer surface | The flag belongs to Pluto's frontend, backend, or stale scripts. `polopt` should not expose it as an optimizer flag. |

## Supported Optimizer Surface

The supported surface is already nontrivial.

| Pluto-style request | Current `polopt` behavior | Evidence |
|---|---|---|
| Default full tiled route | Runs checked affine + ordinary band-aware tiling route. | generated suite and wrapper `ordinary-tiled` |
| `--notile` | Runs affine-only checked route. | wrapper `affine-only` |
| `--identity --notile` | Runs no-Pluto identity extraction/codegen route. | existing CLI route |
| `--iss` | Runs ISS + affine + tiling route when the input satisfies ISS shape constraints. | existing ISS suite |
| `--second-level-tile` | Runs checked second-level tiling route on full tiled paths. | wrapper `second-level`; second-level suite |
| `--iss --second-level-tile` | Runs sequential ISS + second-level route when the witness bridge succeeds. | second-level and route-wrapper checks |
| `--parallel` | Runs Pluto-hinted checked parallel route for one parallel loop. | wrapper `parallel`; parallel tests |
| `--parallel-current d` | Runs explicit-dimension checked parallel route. | parallel-current suite |
| `--multipar` | Runs checked multi-certificate code generation for multiple parallel dimensions. | multipar route; separate from the single config theorem |
| `--diamond-tile` | Runs sequential diamond phase-aligned route on default full tiled path. | wrapper `diamond`; diamond suite |
| `--full-diamond-tile` | Runs stronger diamond producer mode on the same checked route. | wrapper `full-diamond` |
| `--diamond-tile --parallel-current d` and related checked compositions | Compose the checked diamond route with checked parallel-current, ISS, and second-level route choices where the route map accepts them. | unified config wrapper and diamond/second-level suites |
| `--prevector` | Runs checked vector annotation route using Pluto's vector hint only as a candidate. | vector route and generated-C smoke |
| `--unrolljam [--ufactor N]` | Runs checked Loop-level unroll/jam subset after the verified sequential route. | unroll/jam effect corpus and generated-C smoke |
| `--smartfuse` | Compatible with current default affine scheduler recipe. | scheduler flags and wrapper no-op note |
| `--rar` | Compatible with current scheduler recipes. | scheduler flags |
| `--nointratileopt`, `--noprevector`, `--nounrolljam`, `--noparallel`, `--nodiamond-tile` | Accepted when they match the checked route's disabled Pluto-side effects. | wrapper suite |

The current default `polopt` route is not "Pluto default". It intentionally uses phase-aligned recipes. For ordinary sequential optimization, it runs an affine-only Pluto phase with tiling and codegen effects disabled, then a tile-only Pluto phase with `--identity --tile`. This makes the output easier to validate because affine scheduling and tiling are separated.

The bare Pluto flag `--identity` needs special care. In the current Pluto source, tiling is enabled by default, so `--identity` can still reach the tiling phase. The compatible `polopt` no-tiling identity route is therefore better modeled as `--identity --notile`. Bare `--identity` and `--identity --tile` are identity-plus-tiling gaps for a Pluto-compatible wrapper.

The compatibility wrapper still requires callers to be explicit when a Pluto
default would otherwise select a route outside the checked surface. That is now
mainly about `--intratileopt`, implicit frontend/backend behavior, and
unsupported memory-changing transformations. `--prevector`, `--unrolljam`,
`--parallel`, and diamond modes are no longer categorical defaults that force
rejection; they are accepted only when they map to the checked PolOpt routes
listed here.

## Frontend and Input Flags

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--pet` | Unsupported | `polopt` uses its own loop extractor. PET would change the frontend and the source model being validated. | Not as an optimizer flag. | Keep rejecting. If PET input is desired, add a separate importer mode with its own source-model contract. |
| `--readscop` | Unsupported | `polopt` user input is `.loop`, not arbitrary OpenScop. | Possible as a separate validator/debug mode. | Add `polopt --input-openscop` or a standalone validation action. Do not mix it with normal `.loop` compilation. |
| `--dumpscop` | Unsupported as user flag | Pluto dumps are internal oracle artifacts. `polopt` already has explicit validation actions for OpenScop pairs. | Possible as debug output. | Add `--dump-oracle-scops` that names before/mid/posttile/after files. Keep it distinct from Pluto's exact `--dumpscop` semantics. |

These are not proof limitations. They are interface-boundary choices.

## Codegen and Post-Codegen Flags

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--prevector` | Supported through checked vector route | Pluto's vector bit is used only as a candidate hint; PolOpt rechecks the selected current dimension with the doall/parallel certificate before emitting a vector annotation. | Already supported for the current annotation-only subset. | Future work is richer SIMD-specific certificates, not trusting Pluto's backend annotation. |
| `--noprevector` | Compatible no-op | Disables Pluto vector hints. | Already acceptable. | Keep as route control. |
| `--unrolljam` | Supported through checked Loop-level subset | PolOpt does not trust Pluto's rewritten AST. It applies its own checked unroll/jam pass on the sequential Loop IR. | Already supported for constant/block same-bound cases. | Future work is broader peeling/stride-aware/full Pluto unroll-jam coverage. |
| `--nounrolljam` | Compatible no-op | Disables the checked unroll/jam post route. | Already acceptable. | Keep as route control. |
| `--ufactor` | Supported when paired with `--unrolljam` in the checked subset | The factor is treated as part of the candidate plan and must be accepted by the checked pass. | Already supported for accepted factors. | Reject nonpositive or shape-incompatible factors with specific reasons. |
| `--cloogsh`, `--cloogf`, `--cloogl` | Unsupported | These tune Cloog code generation, which `polopt` does not use as trusted output. | Not as optimizer flags. | Only expose equivalent `polopt` codegen knobs if needed. |
| `--nocloogbacktrack` | Compatible no-op in the wrapper | It only constrains Pluto/Cloog code generation, which `polopt` discards. Accepting it avoids rejecting a harmless disabling flag. | Already acceptable as no-op. | Keep the wrapper note explicit so users do not infer Cloog output is validated. |
| `--codegen-context` | Unsupported | This shapes Pluto/Cloog generated bounds. `polopt` regenerates code itself. | Possible as a `polopt` codegen knob. | Add a checked codegen context option if the loop language needs it. |
| `--bee`, `--indent`, `-o` | Unsupported in wrapper | These are backend/output concerns. | Possible under `polopt` names. | Add `polopt` output formatting/path options separately from optimizer compatibility. |

These are mostly not "missing Pluto optimization". They are backend features.
The current support deliberately does not validate Pluto's emitted C or CLAST
rewrite. It validates PolOpt's own vector annotation and Loop-level unroll/jam
transformation.

## DFP and Typed Fusion

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--typedfuse` | Unsupported | Current Pluto build lacks GLPK/Gurobi, and `polopt` has no typed-fusion route. | Yes in principle. | Build Pluto with an LP solver, pass the flag during the affine oracle phase, then validate the resulting affine schedule. Add typed-fusion cases. |
| `--hybridfuse` | Unsupported | Depends on typed fusion and DFP. | Yes in principle. | Same as `--typedfuse`, plus tests for hybrid behavior. |
| `--delayedcut` | Unsupported | DFP-only option. | Yes in principle. | Same as DFP route. |
| `--dfp`, `--lp`, `--ilp`, `--lpcolor`, `--clusterscc` | Unsupported | Current binary does not expose these because GLPK/Gurobi are not enabled. | Yes if the Pluto build changes. | Enable LP solver support, mirror Pluto normalization rules, add schedule-validation tests. |
| `--glpk`, `--gurobi` | Unsupported | Current build has neither solver. | Build-dependent. | Treat as oracle solver selection only. Validation should not trust the solver. |

This category is likely a surface/build gap before it is a proof gap. If DFP only changes which affine schedule Pluto finds, the existing affine validator should be the central correctness check. Work is still needed because DFP may produce schedule shapes that current import/canonicalization has not seen.

## Fusion and Scheduling Objective Knobs

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--nofuse` | Unsupported | Current `polopt` route fixes `--smartfuse`. | Likely surface gap. | Add a fusion-mode enum and pass `--nofuse` in the affine phase. Validate resulting schedule. |
| `--maxfuse` | Unsupported | Same as `--nofuse`. | Likely surface gap. | Add the route and regression cases. |
| `--smartfuse` | Supported as default | Current recipes use it. | Already supported. | Keep explicit acceptance. |
| `--per-cc-obj` | Unsupported | Current route does not expose per-connected-component objective. | Likely surface gap. | Pass through to affine phase and test import/validation of produced schedules. |
| `.fst` / `.precut` | Unsupported as public interface | Pluto can read working-directory files that force fusion or partial schedules. This is implicit global state. | Possible, but should not be implicit. | Add explicit `--fusion-structure FILE` or `--precut FILE`, copy into an isolated Pluto working directory, validate the output. |
| `--nodepbound` | Unsupported | Search-constraint tuning is not exposed. | Possibly surface gap. | Pass as oracle tuning after tests show schedules import and validate. |
| `--coeff-bound` | Unsupported | Search-bound tuning with a value. | Possibly surface gap. | Add value parsing and pass to affine phase; validate output. |
| `--fast-lin-ind-check`, `--flic` | Unsupported | Search heuristic, not a semantic feature. | Surface gap if useful. | Allow as oracle tuning with validation and regression tests. |

The strongest candidates for near-term support are `--nofuse`, `--maxfuse`, and `--per-cc-obj`. They should not require new proof principles if the output remains an affine schedule accepted by the current affine validator.

## Dependence and Solver Knobs

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--isldep` | Compatible no-op | Pluto uses ISL dependence analysis by default. | Already acceptable. | Keep as no-op or pass-through. |
| `--islsolve` | Compatible no-op | Pluto uses ISL ILP solving by default. | Already acceptable. | Keep as no-op or pass-through. |
| `--candldep` | Unsupported | Current route has not tested Candl-derived schedules. | Yes, as oracle tuning. | Pass to Pluto, keep validation as the correctness gate, add Candl cases. |
| `--pipsolve` | Unsupported | Solver selection not exposed. | Yes, as oracle tuning. | Pass to Pluto and validate. |
| `--lastwriter`, `--nolastwriter` | Unsupported | Changes Pluto dependence analysis mode. | Likely yes. | Mirror Pluto's consistency rule: `--lastwriter` only with ISL dependence. Validate schedules against `polopt`'s own semantics. |
| `--isldepaccesswise`, `--isldepstmtwise`, `--isldepcoalesce` | Unsupported | Dependence-analysis tuning not tested. | Likely yes. | Pass through as oracle tuning, add regression cases. |
| `--scalpriv` | Unsupported | Candl scalar privatization mode. | Unclear. | First test whether Pluto output stays inside current loop/source model. If scalar privatization changes memory behavior, a validator/codegen extension may be needed. |

These flags do not need to be trusted for correctness if `polopt` validates the output schedule. The main risks are representation gaps and untested schedule shapes.

## Tiling Controls

| Pluto flag or feature | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--tile` | Supported on default full route | Current default is tiled. | Already supported. | Keep explicit compatibility. |
| `--notile` | Supported | Affine-only route exists. | Already supported. | Keep. |
| `--second-level-tile` | Supported on sequential full tiled route, including the ISS route at the route/scheduler level | Existing validator route supports it. | Already supported for ordinary route; ISS combination needs a dedicated regression case. | Keep and extend tests. |
| `--intratileopt` | Unsupported | Current checked recipes disable Pluto's intra-tile post-tiling schedule rewrite to keep phase witnesses canonical. | Possible, but not just parser work. | Treat Pluto's intra-tile rewrite as a separate affine/post-tiling phase and validate that phase explicitly. Add cases where it changes loop order. |
| `--nointratileopt` | Compatible no-op | Current checked recipes already disable this Pluto rewrite. | Already acceptable. | Keep as no-op with explanation. |
| `--determine-tile-size` | Unsupported | Current checked tiling route does not expose Pluto's tile-size model. | Likely surface gap for semantics. | Pass to tile phase, extract actual tile sizes from OpenScop/witness, require positive sizes, validate tiling. |
| `--cache-size`, `--data-element-size` | Unsupported | Only meaningful with `--determine-tile-size`. | Depends on tile-size model support. | Add value parsing after `--determine-tile-size` works. |
| `tile.sizes` | Unsupported as implicit file | Pluto reads this from the working directory. Implicit files are poor compiler interface. | Yes with explicit file input. | Add `--tile-sizes FILE`, copy into isolated Pluto cwd, and validate actual generated tile sizes. |
| `--ft`, `--lt` | Unsupported | Pluto's partial tiling-level controls are under-specified in current route. | Possible, but more than surface. | Extend tiling witness extraction to partial bands/sub-bands and add tests. |
| bare `--identity` or `--identity --tile` | Unsupported in Pluto-compatible wrapper | Current Pluto keeps tiling enabled by default, while `polopt --identity` means no tiling. | Surface/composition gap. | Add an `IdentityTiled` route: extract identity schedule, run tile-only Pluto phase, validate tiling. |
| `--second-level-tile --parallel` | Supported for the checked non-`multipar` parallel route | Pluto supplies candidate current dimensions, then PolOpt rechecks one accepted dimension after second-level tiling validation. | Already supported in the current route surface. | Keep focused regression cases. |
| `--second-level-tile --parallel-current d` | Supported | Explicit-current route composes second-level tiling validation with checked parallel code generation. | Already supported. | Keep focused positive/negative cases. |

Tile size control is likely easy from a proof perspective if the validator already proves tiling for arbitrary positive sizes. Partial tiling and identity+tiling need more route and witness work.

## Parallel Controls

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--parallel`, `--parallelize` | Supported for one Pluto-hinted parallel loop | Current route validates one loop and emits checked parallel code. | Already supported. | Keep. |
| `--noparallel` | Supported as route control/no-op | Sequential routes use it. | Already supported. | Keep. |
| `--innerpar` | Compatible no-op | Current checked `--parallel` tiled recipe already keeps a canonical inner-parallel style. | Already acceptable. | Keep explanatory note. |
| `--multipar` | Supported as separate checked route | PolOpt checks multiple candidate dimensions and emits checked multi-certificate code. It is not yet folded into the single `raw_config -> ParallelLoop` theorem wrapper. | Already supported operationally; theorem-wrapper integration remains. | Either fold it into the unified config theorem or present it as a separate theorem-backed executable route. |
| `--forceparallel` | Unsupported | Current Pluto source accepts the flag but does not use it. | Not useful until Pluto implements it. | Keep rejecting or treat as error explaining it has no effective use site. |
| `--parallel-current d` | Supported as `polopt` extension, not a Pluto flag | Explicit checked parallel dimension. | Already supported. | Keep separate from Pluto compatibility mode. |
| `--parallel --parallel-strict` | Supported as `polopt` extension | Requires certified parallel loop to match Pluto hint. | Already supported. | Keep. |

The remaining `--multipar` gap is theorem presentation and wrapper integration,
not executable validation. It changes the route shape from one certified
parallel dimension to a multi-certificate route, so it should either become a
first-class config in the unified wrapper or stay clearly documented as a
separate checked route.

## Diamond Tiling and Diamond Combinations

`--diamond-tile` and `--full-diamond-tile` are supported as checked diamond
phase routes. The core proof idea is unchanged from ordinary tiling:
diamond-aware affine midpoint validation followed by checked tiling over that
midpoint, plus the final affine phase when Pluto emits the four-phase route.

| Combination | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--diamond-tile` | Supported | Phase-aligned route validates before -> mid affine, mid -> posttile tiling, and posttile -> after affine. | Already supported. | Keep suite coverage. |
| `--full-diamond-tile` | Supported | Same checked route with stronger Pluto producer mode. | Already supported. | Add more full-diamond cases beyond smoke. |
| `--diamond-tile --parallel` | Supported for the checked non-`multipar` parallel route | Diamond phase validation runs first; the accepted target is then checked for one parallel dimension. | Already supported in the route map. | Keep positive and strict-rejection cases. |
| `--diamond-tile --parallel-current d` | Supported | Explicit-current parallel validation composes with the diamond route. | Already supported. | Keep positive and negative dimension cases. |
| `--diamond-tile --iss` | Supported where the ISS witness and diamond phase artifacts are recoverable | ISS split validation precedes the diamond-aware affine/tiling phases. | Supported route surface. | Keep cases that exercise the split-to-diamond bridge. |
| `--diamond-tile --second-level-tile` | Supported in the checked route surface | The route validates the ordered tiling links and diamond phase artifacts. | Supported route surface. | Continue expanding examples beyond smoke coverage. |
| `--diamond-tile --notile` | Unsupported | Pluto itself disables diamond when tiling is off. | Correct rejection. | Keep rejecting. |
| `--diamond-tile --identity` | Unsupported | Diamond requires Pluto scheduling and tiling phase. | Correct rejection for current route. | Only reconsider if an identity-diamond route has a clear Pluto meaning and tests. |

The diamond gap is no longer composition with ISS, parallel-current, or
second-level tiling. The remaining boundaries are Pluto/Clan frontend failures,
memory-changing extensions, and stronger diamond-performance properties that
are outside the state-preservation theorem.

## Stale or Current-Pluto-Unsupported Flags

These flags appear in old scripts, examples, or code fields, but the current Pluto binary rejects them.

| Flag | Current state | Action |
|---|---|---|
| `--multipipe` | Pluto rejects. | Treat as stale. Do not support. |
| `--lbtile` | Pluto rejects. | Treat as stale. Do not support. |
| `--sched` | Pluto rejects. | Treat as stale. Do not support. |
| `--variables_not_global` | Pluto rejects. | Treat as stale. Do not support. |
| `--dump-iss-bridge` | Baseline `/pluto` binary rejects it; the ISS-export Pluto fork parses it as debug/export surface. | Keep it outside optimizer compatibility. If needed, expose it only as explicit ISS debug tooling. |
| `--output` | Pluto rejects; current binary uses `-o`. | Use `polopt` output options, not Pluto compatibility. |
| `--unroll` | Accepted only as a getopt abbreviation for `--unrolljam`. | Do not expose as a separate capability. |

These are not `polopt` deficiencies.

## Implementation Plan

The next step should be to turn `pluto_compat_driver.py` into the design contract for `polopt`'s own CLI.

1. Define a `PlutoCompat` flag module.
   - Parse Pluto-like flags.
   - Normalize according to Pluto's actual rules, not only `--help`.
   - Emit structured capability decisions.

2. Keep a capability table in code.
   - Each entry should have status, reason, and route mapping.
   - Rejection messages should match tests.

3. Map supported flags to existing routes.
   - ordinary tiled
   - affine-only
   - identity with `--notile`
   - ISS
   - second-level tiling
   - parallel
   - diamond and full diamond

4. Add remaining surface-gap support.
   - `--nofuse`
   - `--maxfuse`
   - `--per-cc-obj`
   - `--candldep`
   - `--pipsolve`
   - `--lastwriter`
   - bare `--identity` / `--identity --tile`
   - explicit tile-size file or positive tile-size controls

5. Keep the composition-route suite stable.
   - diamond + parallel-current
   - diamond + second-level tiling
   - second-level tiling + parallel
   - diamond + ISS

6. Treat semantic extensions as separate projects.
   - scalar privatization if it changes memory behavior
   - richer SIMD semantics beyond doall-safe vector annotations
   - full Pluto-style unroll/jam peeling coverage beyond the checked subset
   - memory reuse, storage contraction, layout remapping, and privatization

7. Keep stale flags rejected.
   - The rejection should say "current Pluto does not support this flag", not "polopt does not support this optimization".

## Testing Plan

The executable compatibility suite should grow into the regression test for this interface.

Current smoke command:

```bash
python3 tools/polopt_flag_suites/run_pluto_compat_suite.py --timeout 30
```

Current result:

```text
[pluto-compat-suite] OK (105 checks)
```

The suite should add one test per supported flag group and one test per rejection class. For every new supported flag, the acceptance criterion should be:

1. Pluto accepts the same flag combination on a comparable case.
2. `polopt` accepts the flag combination.
3. `polopt` output validates through the checked route.
4. The test confirms that the flag is not silently ignored when it should change the schedule.

For rejected flags, the acceptance criterion is a stable, specific reason. A generic "unsupported" message is not enough.

## Short Summary

The current `polopt` surface covers the core state-preserving Pluto-compatible
subset: affine scheduling, ordinary tiling, second-level tiling, ISS, checked
parallel-current routes, checked non-`multipar` Pluto-hinted parallelization,
checked `multipar` as a separate route, diamond and full-diamond mode, checked
vector annotation, and checked Loop-level unroll/jam.

Most remaining Pluto optimizer knobs are surface/build gaps or oracle-tuning
flags whose outputs can be validated by the existing affine/tiling checkers.
The clearest semantic gaps are memory-changing transformations such as scalar
privatization, storage contraction, layout remapping, and overlapped/reuse-based
tiling families that require a relation weaker than the current `State.eq`.
Frontend and pure backend flags should remain outside the optimizer
compatibility surface unless PolOpt adds its own checked counterpart.
