# State.eq Claim Ledger

Updated: 2026-07-18

This ledger connects each intended paper claim to the exact implementation
baseline, proof surface, executable route, and artifact evidence. It separates
proofs present in the tagged source from checks reproduced on that exact tag.

## Frozen baseline

- PolCert tag:
  `state-eq-polyhedral-verification-complete-2026-05-25-v2`
- PolCert commit: `13295e741ad62173411882c6d900dd9dc57337a8`
- Pluto commit: `6f43860b6c4cddeeca09189bf3073f05b78b14a5`, verified in
  both `tools/ci/pluto-baseline.env` and the frozen Dockerfile
- Exact-tag source reproduction: passed on 2026-07-18; see
  `doc/STATE_EQ_BASELINE_REPRODUCTION.md` and
  `doc/evidence/state-eq-baseline-2026-07-18/`
- New Docker image review: image built; offline full review pending
- Earlier full artifact evidence: commit `72deba1`; useful historical evidence,
  but not sufficient evidence for the final tag because multipar code changed
  after that run

The tag is immutable. Archival scripts or metadata added later require a new
commit and annotated archival tag.

## Headline correctness contract

The paper-facing entry point is:

```coq
compile : raw_config -> Loop.t -> imp ParallelLoop.t
```

The main theorem is
`driver/VerifiedParallelCompilerConfig.v:compile_correct`. For every accepted
configuration and generated `ParallelLoop.t` execution, it produces a matching
source `Loop.t` execution whose final state is related by `State.eq`.

Supporting wrapper theorems at the frozen tag include:

- `compile_seq_verified_correct`
- `compile_verified_correct`
- `compile_unsupported_no_result`
- `checked_sequential_current_annotated_codegen_correct`

This is a verified loop-to-loop / loop-to-parallel-loop transformation claim.
It does not verify Pluto's search heuristics, the C frontend, arbitrary C
backend behavior, or OpenMP runtime semantics.

## Contribution ledger

| Contribution | Proof surface at frozen tag | Executable evidence required | Exact-tag status |
| --- | --- | --- | --- |
| End-to-end verified compiler closure | `Extractor.extractor_correct`; `PrepareCodegen.prepared_codegen_correct_general`; `VerifiedParallelCompilerConfig.compile_correct` | Clean proof build, extraction, `polopt` build, representative source-to-output runs | Exact-tag proof/build, `artifact-check-full`, and `make test`: pass |
| Inherited affine scheduling validation | `AffineValidator.v`; `PolOptCorrect.Affine_opt_prepared_correct` and `Opt_correct` | Affine-only positive and negative cases in strict and Pluto-compatible suites | Strict `62/62`; compatibility `114/114` |
| Witness-centered generic tiling | `TilingValidator.checked_tiling_validate_poly_correct`; `checked_tiling_prepared_codegen_correct` | Ordinary and identity tiling cases, witness rejection cases, generated-code checks | Strict, compatibility, and identity-composition checks: pass |
| Pluto-oriented band-aware tiling | `TilingBandScheduleValidator.checked_tiling_schedule_stripmined_validate_correct_same_ctxt_pluto_structured` | Default band-aware route plus legacy generic comparison and rejection cases | Strict and compatibility checks: pass |
| Second-level / hierarchical tiling | Accepted `RawSeq` and checked route composition through `compile_seq_verified_correct` | Dedicated second-level suite and ISS/parallel composition cases | Second-level suite: pass; compatibility compositions: pass |
| Diamond and full-diamond routes | `ParallelPolOptCorrect.try_diamond_phase_pipeline_from_source_pol_poly_correct` and diamond route lemmas; final composition through `compile_correct` | Diamond suite, full-diamond cases, ISS/parallel compositions, frontend versus validator rejection classification | Diamond suite and compatibility compositions: pass |
| ISS structural generalization | `ISSValidatorCorrect.checked_iss_complete_cut_shape_validate_semantics_correct`; ISS route lemmas in `PolOptCorrect.v` and `ParallelPolOptCorrect.v` | ISS-only, affine, tiled, second-level, diamond, and parallel compositions | Dump suite and live Pluto suite: pass |
| Checked parallel-current | `ParallelValidator.checked_parallelize_current_sound`; `ParallelCodegen.checked_annotated_codegen_correct_general`; single-current route theorems in `ParallelPolOptCorrect.v` | Explicit-current and Pluto-hinted positive/negative cases; emitted `ParMode` output | Parallel-current and compatibility suites: pass |
| Checked multipar | `ParallelCodegen.checked_annotated_codegen_many_correct_general`; `Opt_parallel_current_many_*_correct`; final `compile_correct` composition | Pluto-hinted multi-current cases, strict hint handling, unsupported plan rejection | Compatibility multipar and strict-hint cases: pass |
| Checked vector annotations | `ParallelCodegen.checked_vector_annotated_codegen_correct_general`; `ParallelPolOpt.checked_vector_current_annotated_codegen_correct` | Explicit and Pluto-hinted vector cases using the documented doall certificate | Vector-current and compatibility vector cases: pass |
| Checked unroll/jam subset | `LoopUnroll.const_unroll_correct`, `peel_unroll_correct`, `suffix_peel_unroll_correct`, and `block_unroll_correct` | Effect corpus and generated-C semantic checks for supported factors/shapes | Effect corpus and three generated-C checks: pass |
| Literal stride lowering | `LoopStride.stride_loop_stmt_semantics` and `down_stride_loop_stmt_semantics` | Positive- and negative-literal stride generated-C cases | Both generated-C stride checks: pass |
| Verified cleanup | `LoopCleanup.cleanup_correct`; `LoopSingletonCleanup.cleanup_correct` | Cleanup/singleton cases and downstream extraction/codegen checks | Exact-tag proof, extraction, strict, and core test gates: pass |

The exact-tag proof report confirmed all 24 theorem-facing routes named by its
route map. The ledger should remain checked against the generated report before
paper freeze.

## Artifact acceptance matrix

The Docker artifact is claim-complete only if one documented top-level command
records all of the following:

- exact PolCert tag and commit;
- exact Pluto commit and dirty-state check;
- Coq, OCaml, opam, compiler, Python, and system dependency versions;
- clean proof build and extraction;
- admitted, abort, and unrealized extraction-axiom scans;
- theorem-route proof report;
- generated Pluto flag capability matrix;
- comprehensive Pluto-compatible flag suite;
- strict generated regression corpus;
- ordinary, identity, second-level, diamond, full-diamond, and ISS tiling cases;
- explicit-current parallel, Pluto-hinted parallel, and multipar cases;
- vector, unroll/jam, stride, and cleanup cases;
- expected rejection cases with stable reasons;
- machine-readable result summary and human-readable report;
- command exit status, runtime, and hardware assumptions.

An image build is not sufficient evidence by itself. The image must be tested
from a fresh Docker environment and identified by an immutable digest.

## Claim boundaries

The following are explicit non-claims for the current paper:

- scalar privatization, scalar expansion, array contraction, storage remapping,
  and layout transformations that require a state relation beyond `State.eq`;
- overlapped / flextended tiling;
- reduction-aware parallelization;
- full SIMD lowering and machine-level vector-code correctness;
- diamond-tiling load-balance, concurrent-start, or maximal-parallelism
  properties;
- correctness of Pluto's optimization heuristics or witness extraction glue;
- a verified C frontend, C printer, or OpenMP runtime.

The checked witness/certificate is trusted only after validation; its producer
remains outside the proof boundary.

## Paper contribution wording

The contribution order should be:

1. End-to-end closure of PolCert into a unified verified compiler whose
   accepted routes all satisfy the `State.eq` refinement contract.
2. Witness-centered validation and code-generation reuse for ordinary,
   identity, hierarchical, diamond, and composed tiling routes.
3. Semantic extensions for ISS and checked sequential/parallel/multipar target
   generation.
4. Adjacent checked routes for vector annotations, the supported unroll/jam
   subset, literal stride lowering, and cleanup.
5. A claim-oriented artifact that exercises the supported Pluto-facing surface
   and reports unsupported storage-changing requests explicitly.

Affine scheduling validation is the inherited baseline. The paper should not
present it as a new contribution, although the end-to-end compiler continues to
depend on it.

## Freeze procedure

1. Complete the new Docker image's offline full review and archive its digest
   and report.
2. Generate paper capability tables from the archived machine-readable output.
3. Cross-check abstract, introduction, correctness theorem, evaluation, and
   conclusion against this ledger.
4. If proof cleanup changes the paper artifact revision, repeat this process and
   retain the original tag's image and report.
