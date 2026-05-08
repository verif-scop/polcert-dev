# PolOpt Pipeline

This document records the current execution path of `polopt` and aligns it
with the Pluto pipeline described in [pipeline.md](./pipeline.md). Pluto remains
an optimization oracle: it proposes middle-stage polyhedral artifacts and loop
hints, while `polopt` keeps the verified front end, validation, route selection,
and code generation.

## 1. Top-Level Shape

The current `polopt` optimizer path is:

```text
parse .loop source
lower supported loop sugar
extract Loop.t -> PolyLang.t
strengthen / normalize PolyLang
choose a checked route from CLI config
ask Pluto for route-specific middle artifacts or hints
validate each accepted middle artifact
generate ParallelLoop.t through the extracted unified compiler
print Loop/parallel-loop syntax
```

The theorem-facing compiler surface is now:

```coq
compile : raw_config -> Loop.t -> imp ParallelLoop.t
```

The proof-side statement is `VerifiedParallelCompilerConfig.compile_correct`:
if `compile cfg loop` returns `pl` and `pl` executes from `st` to `st'`, then
the source `loop` has a matching execution from `st` to some `st''` with
`State.eq st' st''`.

That theorem is the reason the executable route is described as
`Loop -> ParallelLoop`, not as a separate sequential compiler plus a separate
parallel printer. Sequential routes produce all-`SeqMode` `ParallelLoop`
targets; parallel routes preserve `ParMode` annotations.

## 2. Pluto-to-PolOpt Phase Correspondence

| Pluto phase | Pluto role | PolOpt use |
| --- | --- | --- |
| CLI option parsing and normalization | Decide which optimizer phases Pluto will run. | `SLoopCli.ml` and `SLoopRoute.ml` filter Pluto-style flags before any checked route runs. Unsupported combinations fail with a specific reason. |
| Front end (`PET`, Clan, or `readscop`) | Build Pluto's internal `PlutoProg`. | Not trusted for the main source input. `polopt` uses its own `.loop` parser, verified sugar lowering, and verified extractor. |
| Dependence analysis | Build Pluto's dependence representation for scheduling. | Treated as part of Pluto's oracle behavior. PolOpt validates the produced before/after artifacts instead of trusting Pluto's dependence representation. |
| ISS before scheduling | Rewrite statement/domain structure before affine scheduling. | Accepted only through the checked ISS route. The witness/bridge is untrusted; the ISS checker proves the accepted split refines the source program. |
| `pluto_auto_transform()` | Produce affine schedules, fusion/distribution structure, and diamond-aware bands. | Used as an oracle for affine midpoints. `polopt` validates `before -> mid` with the affine validator or the diamond phase route. |
| `pluto_tile()` | Add tile dimensions, tile schedules, second-level tiling, and diamond rescheduling. | Used as an oracle for tiling targets. `polopt` validates midpoint-to-target tiling with ordinary, second-level, or diamond-aware route checks. |
| Parallel loop marking | Mark parallel loops in the generated OpenScop/codegen path. | Used only as a hint source. `polopt` rechecks the chosen current dimension and emits checked `ParallelLoop` code. |
| Vector marking | Mark vectorizable loops. | Used as a hint source for the checked vector route. The route reuses the doall certificate before emitting vector annotations. |
| Unroll-jam marking | Select unroll/jam candidates and factors. | Mapped to the checked loop-level unroll/jam subset. Candidate selection is untrusted; each applied unroll/jam step is checked by the extracted pass. |
| CLooG/AST code generation | Emit C-like loops and annotations. | Not trusted by `polopt`. The final target comes from extracted PolCert code generation and the `ParallelLoop` printer. |

## 3. Route Selection in PolOpt

The route selector first classifies the request into a base route:

| Base route | Meaning |
| --- | --- |
| `Identity` | Extract, strengthen, and code-generate without asking Pluto for a schedule. |
| `AffineOnly` | Ask Pluto for affine scheduling only, then validate the schedule. |
| `FullTiled` | Run the phase-aligned affine-plus-tiling route. |

It then composes optional dimensions:

| Dimension | Supported values |
| --- | --- |
| Structural extension | plain or ISS |
| Tiling family | none, ordinary band-aware, legacy generic, second-level, diamond, full diamond |
| Parallel family | sequential, Pluto-hinted parallel, explicit `--parallel-current d` |
| Vector family | Pluto-hinted vector or explicit `--vector-current d` outside the unified parallel wrapper |
| Post loop route | checked constant/block unroll and checked same-bound jam on sequential Loop IR |

The ordinary no-flag route uses the band-aware affine-plus-tiling path. The
historical generic tiling route remains available behind
`--legacy-generic-tiling`.

## 4. Unified Compiler Wrapper

The extracted wrapper is `syntax/SVerifiedParallelCompilerConfig.v`; the proof
mirror is `driver/VerifiedParallelCompilerConfig.v`.

The accepted configs are:

```text
RawSeq seq_cfg
RawParallelCurrentIdentity d
RawParallelCurrentIdentityTiled d
RawParallelCurrentAffine d
RawParallelCurrentDefault d
RawParallelCurrentDiamond d
RawParallelCurrentDiamondISS d
RawParallelCurrentIdentityISS d
RawParallelCurrentAffineISS d
RawParallelCurrentDefaultISS d
```

`RawSeq` covers the sequential variants. Most sequential variants now code
generate directly through checked all-`SeqMode` `ParallelLoop` code generation.
Some existing second-level identity variants still use the old sequential
compiler internally and then pass through a checked lift into `ParallelLoop`.

The explicit-current parallel variants preserve `ParMode` by calling the
existing checked parallel-current routes. Non-`multipar` Pluto-hinted
`--parallel` first obtains candidate current dimensions from Pluto, then calls
the same unified compiler on those candidates. In strict mode, only Pluto's
hinted dimension may be accepted.

## 5. How Pluto-Compatible Flags Map to Routes

`--pluto-compat` does not forward arbitrary Pluto defaults into a trusted
compiler. It parses Pluto-like flags, rejects combinations outside the checked
surface, and then selects a PolOpt route.

| Pluto-style request | PolOpt route |
| --- | --- |
| `--identity --notile` | `RawSeq RawIdentity` |
| `--notile` | `RawSeq RawAffine` |
| ordinary `--tile` | `RawSeq RawDefaultBand` |
| `--identity --tile` | checked identity tiling route |
| `--second-level-tile` | checked second-level tiling route |
| `--iss` | checked ISS route |
| `--diamond-tile` / `--full-diamond-tile` | checked diamond phase route |
| `--parallel` | Pluto hint -> checked current dimension -> unified compiler |
| `--parallel-current d` | explicit checked current dimension -> unified compiler |
| `--multipar` | checked multi-certificate code generation path, currently outside the single-config wrapper |
| `--prevector` | checked vector route using Pluto vector hints and the doall certificate |
| `--unrolljam [--ufactor N]` | checked Loop-level unroll/jam subset |

The remaining hard boundary is not the Pluto optimizer itself. It is the class
of transformations that change memory or require a weaker state relation, such
as scalar privatization and storage/layout transformations.

## 6. Artifact Checks

The reviewer-facing smoke command is:

```bash
make artifact-check
```

The current smoke check rebuilds the extracted tools and runs:

- Python syntax checks for artifact tools;
- proof report generation;
- capability matrix generation;
- codegen-gap and identity-composition explorations;
- unroll-jam effect corpus;
- Pluto compatibility suite;
- generated-C end-to-end cases for unroll/jam and stride lowering;
- second-level tiling suite;
- diamond tiling suite.

The proof report lists the route-level theorem names, including the unified
`Loop -> ParallelLoop` wrapper theorem.
