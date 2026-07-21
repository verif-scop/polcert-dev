# State.eq Claim Ledger

Updated: 2026-07-21

This ledger binds each intended paper claim to an immutable implementation
revision, a proved theorem surface, executable routes, and artifact evidence.
Source verification and Docker review are separate gates: passing one is not
reported as evidence for the other.

## Frozen baseline

- PolCert tag:
  `state-eq-polyhedral-verification-complete-2026-07-21-v3`
- Annotated tag object: `1fe3bf79f14065dc24df7190cd6d6dc1d3ff9b5d`
- Commit: `4bc20817c32f2073221cf68475bf9b78c0bab74b`
- Tree: `5c21c31e54536dff78c376b4e861efdba3c0d4fb`
- Pluto baseline: `6f43860b6c4cddeeca09189bf3073f05b78b14a5`
- Exact-tag source verification: clean proof build, extraction, `polcert`, and
  `polopt` builds passed. The generated proof report covers 185 Coq files, 27
  top-level route entries, and 60 named theorem obligations, with zero admitted
  markers, aborted proofs, extraction axioms, or missing route theorems.
- Exact-tag route verification: the Pluto compatibility matrix passed 138
  checks; dedicated ordinary, second-level, diamond, ISS, parallel, multipar,
  vector, unroll/jam, stride, cleanup, and negative-route suites passed.
- v3 Docker review: pending. No v3 image is publication-eligible until a fresh
  network-disabled full run produces schema-v2 evidence for that exact image.
- Historical dependency provenance: the v2 review records in
  `artifact/state-eq/evidence/` authenticate the installed dependency lock and
  provide a serial timing baseline. They are not review evidence for v3.

The tag is immutable. Any implementation change requires a new commit and tag;
artifact-control changes require a new packaging revision and fresh evidence.

## Headline correctness contract

The paper-facing entry point is:

```coq
compile : raw_config -> Loop.t -> imp ParallelLoop.t
```

The main theorem is
`driver/VerifiedParallelCompilerConfig.v:compile_correct`. For every accepted
configuration and generated `ParallelLoop.t` execution, it constructs a
matching source `Loop.t` execution whose final state is related by `State.eq`.
Supporting wrappers include `compile_seq_verified_correct`,
`compile_verified_correct`, `compile_unsupported_no_result`, and
`checked_sequential_current_annotated_codegen_correct`.

For tiling boundaries, the public route theorem is
`TilingBandDirectRuntime.checked_tiling_schedule_sourceb_first_direct_runtime_validate_route_correct`.
A `permutable-band` result combines the direct semantic checker with the
layout-specific reversal bridge. A successful legacy, canonical, or general
validator is reported separately as `general-fallback`.

This is a verified loop-to-loop or loop-to-parallel-loop transformation claim.
It does not verify Pluto's optimization search, a C frontend, arbitrary C
backend behavior, or OpenMP runtime semantics.

## Permutable-band contract

The v3 direct tiling route checks a pointwise semantic formulation of Pluto's
fully permutable-band condition. For two source-ordered dynamic instances, if
their schedule prefix before the band is equal and a component in the band
decreases, the checker proves that the instances commute. Operationally, it
constructs the old-order, equal-prefix, and decreasing-component regions and
requires their WW, WR, and RW conflict regions to be empty. RR pairs are
irrelevant, as in dependence-based band legality.

This is the contrapositive of Pluto's core condition: a dependence not already
carried by the outer prefix cannot be negative in any band component. The
direct route reuses the shared access-conflict and polyhedral-emptiness kernel;
it does not call the complete affine-schedule validator.

The proof then connects the local property to transformation correctness:

1. Empty conflict regions imply semantic commutativity (`Permutable_ext`).
2. Checking every component establishes the common permutable-band property.
3. Structural bridge lemmas show that any order reversal introduced by a
   supported ordinary or grouped/interleaved second-level tiling exposes such
   a decreasing component.
4. Safe reordering yields the final `State.eq` refinement theorem.

Only a `DirectBandAccepted` / `permutable-band` result supports this claim.
Other successful transformations are labeled `GeneralFallbackAccepted`; they
remain verified by a more general proved route but are not counted as direct
band-checker acceptances. The exact-tag matrices currently report:

- non-second-level: 90 cases, comprising 50 direct band acceptances, 34
  explicit general fallbacks, and 6 explicit vector-hint rejections;
- second-level manifest: 58 checks, comprising 53 successful cases (36 direct
  and 17 fallback) plus 5 expected-failure cases; these five are malformed or
  mismatched inputs, not five `route=rejected` observations;
- additional diamond plus second-level runtime matrix: 16 direct acceptances
  and 4 explicit vector-hint rejections;
- additional rejection probe: 2 explicit tiling-route rejections, 4 optional
  vector skips that preserve verified fallback results, and 8 invalid explicit
  current selections split between 4 tiling-route rejections and 4 vector-route
  rejections;
- direct-versus-general differential check: 5 cases, all passing with no solver
  alarms: 3 expected direct acceptances, 1 expected direct rejection accepted
  by the whole-program checker, and 1 expected rejection by all three scopes.

The claim is about checking a supplied band. PolCert does not verify Pluto's
ILP search, band discovery, maximality, or linear-independence detector, and it
does not claim a formal equivalence between Pluto's dependence-graph
construction and PolCert's pointwise access-conflict semantics. The direct
checker is sound, not proved complete; unsupported shapes may fall back. The
current checker also does not reconstruct Pluto's later implementation
relaxation for earlier scalar dimensions inside a candidate band.

## Contribution ledger

| Contribution | Principal proved surface | Required executable evidence | v3 source status |
| --- | --- | --- | --- |
| End-to-end verified compiler closure | `Extractor.extractor_correct`; `PrepareCodegen.prepared_codegen_correct_general`; `VerifiedParallelCompilerConfig.compile_correct` | Clean proof/extraction/executable builds and representative source-to-output runs | Passed |
| Inherited affine scheduling validation | `AffineValidator.v`; `PolOptCorrect.Affine_opt_prepared_correct`; `PolOptCorrect.Opt_correct` | Affine positive/negative cases in strict and Pluto-compatible suites | Passed; affine proof cleanup frozen |
| Direct permutable-band validation | `validate_two_instrs_pluto_band_component_direct_sound`; `check_pprog_pluto_permutable_tiling_bands_direct_sound_with_env_len`; `check_pinstr_list_pluto_componentwise_permutable_bands_direct_sound`; unified route theorem in `TilingBandDirectRuntime.v` | Direct/fallback/rejection ledgers, differential cases, ordinary and second-level suites | Passed with counts above |
| Generic tiling fallback | `TilingValidator.checked_tiling_validate_poly_correct`; `checked_tiling_prepared_codegen_correct` | Explicit fallback labels plus witness positive/negative cases | Passed |
| Ordinary and identity tiling | Structural tiling and code-generation bridge theorems | Strict, compatibility, identity, and route-classification cases | Passed |
| Second-level / hierarchical tiling | `checked_second_level_direct_band_check_correct`; `second_level_local_reversal_bridge_by_layout_wf_with_env_len`; componentwise direct-check soundness; composed wrapper routes | Dedicated manifest, runtime matrix, and explicit rejection/fallback probes | Passed |
| Diamond and full-diamond routes | Diamond pipeline and route lemmas; final `compile_correct` composition | Direct accounting for the tiling leg, separately checked final affine leg, and second-level/ISS/parallel compositions | Passed; the final affine leg is not counted as a direct band check |
| ISS structural generalization | `ISSValidatorCorrect.checked_iss_complete_cut_shape_validate_semantics_correct`; ISS route lemmas | ISS-only and composed affine, tiling, diamond, and parallel cases | Passed in frozen dump suite; live suite is supplemental |
| Checked parallel-current and multipar | Parallel validator/codegen soundness and single/many-current route theorems | Explicit-current and Pluto-hinted positive/negative cases | Passed |
| Checked vector annotations | `ParallelCodegen.checked_vector_annotated_codegen_correct_general`; vector-current route theorem | Innermost-only explicit and Pluto-hinted cases, with non-innermost hints rejected | Passed |
| Checked unroll/jam subset | `LoopUnroll` and loop-jam validation/lowering soundness theorems | Effect corpus and generated-C semantic comparisons | Passed |
| Literal stride lowering | `LoopStride.stride_loop_stmt_semantics`; `down_stride_loop_stmt_semantics` | Positive- and negative-literal stride comparisons | Passed |
| Verified cleanup | `LoopCleanup.cleanup_correct`; `LoopSingletonCleanup.cleanup_correct` | Cleanup cases plus downstream extraction/codegen | Passed |

## Artifact acceptance matrix

The v3 Docker artifact is claim-complete only when one documented top-level
command records all of the following for the same image ID:

- exact PolCert tag object, commit, tree, and source-archive hash;
- exact Pluto commit, base-image digest, and clean source state;
- Coq, OCaml, opam, compiler, Python, OS, dpkg, and opam dependency state;
- clean proof build, extraction, `polcert`, and `polopt` builds;
- zero admitted markers, aborted proofs, extraction axioms, and missing routes;
- the 185-file, 27-route, 60-obligation proof report;
- the 81-row generated Pluto capability surface and 138-check compatibility
  matrix, with 112 expected successes and 26 expected rejections;
- the 62-case strict generated regression corpus;
- five differential comparisons: three expected direct accepts, two expected
  direct rejects, and no solver alarms;
- direct-band, ordinary, identity, second-level, diamond, full-diamond, and ISS
  route checks with explicit direct/fallback/rejection results;
- parallel-current, multipar, vector, unroll/jam, stride, and cleanup checks;
- stable expected-rejection reasons;
- a mechanically resolved C1-C6 claim-to-route/log/artifact report;
- complete raw-result tree digest, command statuses, runtimes, and host context.

An image build is not evidence by itself. Publication additionally requires
schema-v2 evidence recomputed from the untouched raw directory and an immutable
registry digest.

## Claim boundaries

The current paper does not claim:

- scalar privatization, scalar expansion, array contraction, storage remapping,
  or any transformation requiring a state relation beyond `State.eq`;
- overlapped or flextended tiling;
- reduction-aware parallelization;
- full SIMD lowering or machine-level vector-code correctness;
- diamond-tiling load-balance, concurrent-start, or maximal-parallelism
  properties;
- completeness of the direct band checker;
- necessity of the band condition for every possible fixed tiled target;
- Pluto's later scalar-dimension relaxation inside a candidate band;
- correctness of Pluto's optimization heuristics, band discovery, or witness
  producer;
- a verified C frontend, C printer, or OpenMP runtime.

The witness producer is outside the proof boundary; every accepted witness is
checked before use.

## Paper contribution order

1. End-to-end closure of PolCert into a unified verified compiler whose
   accepted routes satisfy one `State.eq` refinement contract.
2. A direct validator for the semantic fully permutable-band property, plus
   structural proofs connecting it to ordinary and hierarchical tiling and an
   explicit verified fallback for shapes outside the direct route.
3. Validation and composition of ISS, diamond tiling, and checked
   sequential/parallel/multipar target generation in the same framework.
4. Checked supporting routes for vector annotations, the documented
   unroll/jam subset, literal stride lowering, and cleanup.
5. A claim-oriented artifact that resolves every claim to theorem surfaces,
   executable routes, logs, and structured results.

Affine scheduling validation is the inherited baseline. Its bounded proof
cleanup improves maintainability but is not a new correctness contribution.

## Freeze procedure

1. Build and review the v3 Docker candidate with networking disabled.
2. Archive raw results and schema-v2 evidence; record measured reproduction
   time and the candidate image ID.
3. Validate publication eligibility, then publish only under an immutable
   versioned registry reference and record its digest.
4. Generate paper capability tables from the archived machine-readable output.
5. Cross-check abstract, introduction, correctness, evaluation, and conclusion
   against this ledger and run the planned adversarial paper reviews.
