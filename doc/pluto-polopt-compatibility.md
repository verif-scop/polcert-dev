# Pluto-Polopt Compatibility Surface

Date: 2026-05-03

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
  - result: `21 / 21` checks passed
- Executed diamond validation suite:
  - `make test-diamond-tiling-suite`
  - result: 6 diamond-effect cases validated, 2 no-effect cases validated, 11 unsupported Pluto inputs rejected as expected

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
| `--iss --second-level-tile` | Route normalization and scheduler support the sequential ISS + second-level route. | `SLoopRoute.ml` and `Scheduler.ml`; needs a focused wrapper case |
| `--parallel` | Runs Pluto-hinted checked parallel route for one parallel loop. | wrapper `parallel`; parallel tests |
| `--parallel-current d` | Runs explicit-dimension checked parallel route. | parallel-current suite |
| `--diamond-tile` | Runs sequential diamond phase-aligned route on default full tiled path. | wrapper `diamond`; diamond suite |
| `--full-diamond-tile` | Runs stronger diamond producer mode on the same checked route. | wrapper `full-diamond` |
| `--smartfuse` | Compatible with current default affine scheduler recipe. | scheduler flags and wrapper no-op note |
| `--rar` | Compatible with current scheduler recipes. | scheduler flags |
| `--nointratileopt`, `--noprevector`, `--nounrolljam`, `--noparallel`, `--nodiamond-tile` | Accepted when they match the checked route's disabled Pluto-side effects. | wrapper suite |

The current default `polopt` route is not "Pluto default". It intentionally uses phase-aligned recipes. For ordinary sequential optimization, it runs an affine-only Pluto phase with tiling and codegen effects disabled, then a tile-only Pluto phase with `--identity --tile`. This makes the output easier to validate because affine scheduling and tiling are separated.

The bare Pluto flag `--identity` needs special care. In the current Pluto source, tiling is enabled by default, so `--identity` can still reach the tiling phase. The compatible `polopt` no-tiling identity route is therefore better modeled as `--identity --notile`. Bare `--identity` and `--identity --tile` are identity-plus-tiling gaps for a Pluto-compatible wrapper.

The compatibility wrapper also requires callers to say how they want to handle Pluto defaults that are outside the checked route. A bare invocation is rejected. The caller must explicitly disable unsupported default-on Pluto side effects with `--nointratileopt --noprevector --nounrolljam`, and must choose either `--noparallel` or `--parallel`, and either `--nodiamond-tile` or a diamond route.

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
| `--prevector` | Unsupported | Pluto marks vectorizable loops during codegen. `polopt` discards Pluto AST/codegen output. | Yes, but not by pass-through. | Add a checked vector-annotation or vector-loop route in `polopt` codegen. If pragmas are semantically ignored, prove or document that they do not affect semantics. |
| `--noprevector` | Compatible no-op | Current checked recipes already disable Pluto prevector output. | Already acceptable. | Keep as no-op with explanation. |
| `--unrolljam` | Unsupported | Pluto performs loop-body rewriting after codegen. This is not a schedule-only oracle effect. | Yes, but requires new validation/proof. | Implement checked unroll-and-jam as a `polopt` transformation or add a validator for Pluto's unrolled AST/code. |
| `--nounrolljam` | Compatible no-op | Current checked recipes already disable Pluto unroll-jam. | Already acceptable. | Keep as no-op with explanation. |
| `--ufactor` | Unsupported | Only meaningful with `--unrolljam`. | Depends on unroll-jam support. | Add after checked unroll-jam exists. |
| `--cloogsh`, `--cloogf`, `--cloogl` | Unsupported | These tune Cloog code generation, which `polopt` does not use as trusted output. | Not as optimizer flags. | Only expose equivalent `polopt` codegen knobs if needed. |
| `--nocloogbacktrack` | Compatible no-op in the wrapper | It only constrains Pluto/Cloog code generation, which `polopt` discards. Accepting it avoids rejecting a harmless disabling flag. | Already acceptable as no-op. | Keep the wrapper note explicit so users do not infer Cloog output is validated. |
| `--codegen-context` | Unsupported | This shapes Pluto/Cloog generated bounds. `polopt` regenerates code itself. | Possible as a `polopt` codegen knob. | Add a checked codegen context option if the loop language needs it. |
| `--bee`, `--indent`, `-o` | Unsupported in wrapper | These are backend/output concerns. | Possible under `polopt` names. | Add `polopt` output formatting/path options separately from optimizer compatibility. |

These are mostly not "missing Pluto optimization". They are backend features. Supporting `--prevector` and `--unrolljam` as transformations would require real work, especially for `--unrolljam`.

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
| `--second-level-tile --parallel` | Unsupported | Route rejected although scheduler code has a flag recipe for parallel second-level tiling. | Composition gap. | Compose second-level tiling witness validation with parallel-loop validation. Add route and tests. |
| `--second-level-tile --parallel-current d` | Unsupported | Route normalization rejects the explicit-current parallel composition too. | Composition gap. | Compose second-level tiling validation with explicit-current parallel validation. |

Tile size control is likely easy from a proof perspective if the validator already proves tiling for arbitrary positive sizes. Partial tiling and identity+tiling need more route and witness work.

## Parallel Controls

| Pluto flag | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--parallel`, `--parallelize` | Supported for one Pluto-hinted parallel loop | Current route validates one loop and emits checked parallel code. | Already supported. | Keep. |
| `--noparallel` | Supported as route control/no-op | Sequential routes use it. | Already supported. | Keep. |
| `--innerpar` | Compatible no-op | Current checked `--parallel` tiled recipe already keeps a canonical inner-parallel style. | Already acceptable. | Keep explanatory note. |
| `--multipar` | Unsupported | Pluto may expose multiple degrees of parallelism; current validator/codegen handles one selected parallel dimension. | Validator/codegen gap. | Extend parallel witness to a list of dimensions, prove/codegen nested or multiple OpenMP loops, add race-freedom checks for each dimension. |
| `--forceparallel` | Unsupported | Current Pluto source accepts the flag but does not use it. | Not useful until Pluto implements it. | Keep rejecting or treat as error explaining it has no effective use site. |
| `--parallel-current d` | Supported as `polopt` extension, not a Pluto flag | Explicit checked parallel dimension. | Already supported. | Keep separate from Pluto compatibility mode. |
| `--parallel --parallel-strict` | Supported as `polopt` extension | Requires certified parallel loop to match Pluto hint. | Already supported. | Keep. |

The largest real gap here is `--multipar`. That is not a simple parser issue because the semantic artifact changes from one certified parallel loop to a set of parallel loops.

## Diamond Tiling and Diamond Combinations

`--diamond-tile` is supported, but only on one route:

```text
default full tiled + sequential + non-ISS + single-level tiling
```

`--full-diamond-tile` is supported on the same route.

| Combination | Current state | Reason | Can support? | How to support |
|---|---|---|---|---|
| `--diamond-tile` | Supported | Phase-aligned route validates before -> mid affine, mid -> posttile tiling, and posttile -> after affine. | Already supported. | Keep suite coverage. |
| `--full-diamond-tile` | Supported | Same checked route with stronger Pluto producer mode. | Already supported. | Add more full-diamond cases beyond smoke. |
| `--diamond-tile --parallel` | Unsupported | Current diamond route forces `--noparallel`. | Composition gap. | Run diamond phase validation, then validate a final parallel loop on the resulting schedule. Add OpenMP codegen checks. |
| `--diamond-tile --parallel-current d` | Unsupported | Same issue, with explicit dimension. | Composition gap. | Compose diamond phase validation with explicit-current parallel validator. |
| `--diamond-tile --iss` | Unsupported | ISS changes statement structure before affine scheduling. Current diamond witness path assumes the non-ISS phase shape. | Composition gap. | Sequence ISS split validation, diamond affine validation, tiling validation, and final affine validation. Add bridge mapping from split statements to diamond witnesses. |
| `--diamond-tile --second-level-tile` | Unsupported | Current diamond phase validator handles one tiling boundary. | Composition gap. | Validate mid -> first-tile and first-tile -> second-tile separately, or generalize tiling validation to multi-level tiling witnesses. |
| `--diamond-tile --notile` | Unsupported | Pluto itself disables diamond when tiling is off. | Correct rejection. | Keep rejecting. |
| `--diamond-tile --identity` | Unsupported | Diamond requires Pluto scheduling and tiling phase. | Correct rejection for current route. | Only reconsider if an identity-diamond route has a clear Pluto meaning and tests. |

The diamond gap is not "diamond is unsupported". The gap is composition with ISS, parallel, and second-level tiling.

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

4. Add near-term surface-gap support.
   - `--nofuse`
   - `--maxfuse`
   - `--per-cc-obj`
   - `--candldep`
   - `--pipsolve`
   - `--lastwriter`
   - bare `--identity` / `--identity --tile`
   - explicit tile-size file or positive tile-size controls

5. Add composition routes after surface gaps are stable.
   - diamond + parallel
   - diamond + second-level tiling
   - second-level tiling + parallel
   - diamond + ISS

6. Treat semantic extensions as separate projects.
   - unroll-jam
   - vector pragmas or vector loop annotations
   - multipar/nested OpenMP
   - scalar privatization if it changes memory behavior

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
[pluto-compat-suite] OK (21 checks)
```

The suite should add one test per supported flag group and one test per rejection class. For every new supported flag, the acceptance criterion should be:

1. Pluto accepts the same flag combination on a comparable case.
2. `polopt` accepts the flag combination.
3. `polopt` output validates through the checked route.
4. The test confirms that the flag is not silently ignored when it should change the schedule.

For rejected flags, the acceptance criterion is a stable, specific reason. A generic "unsupported" message is not enough.

## Short Summary

The current `polopt` surface already covers the core checked subset: affine scheduling, ordinary tiling, second-level tiling, ISS, one-loop parallelization, sequential diamond tiling, and full-diamond mode.

Most missing Pluto optimizer knobs are either surface gaps or composition gaps. The clearest proof/semantic gaps are `--unrolljam`, vector/codegen effects, `--multipar`, and any scalar-privatization feature that changes memory behavior. Frontend and backend flags should remain outside the optimizer compatibility surface.
