# State.eq Claim Ledger

Updated: 2026-08-26

This ledger binds the paper claims to the frozen v9 implementation, named proof
surfaces, executable routes, and artifact evidence. Source verification and a
Docker review are separate gates. A source result is not reported as an artifact
result until the exact candidate completes the offline review.

## Frozen v9 implementation

- PolCert tag:
  `state-eq-polyhedral-verification-complete-2026-08-26-v9`
- Annotated tag object: `66a632f44b231d4e210d115529619d8f761a7840`
- Commit: `604587ecfec9ff3bf6be655dd66e25af6178d604`
- Tree: `3e1daad0f8d05ac0b41c5cb0d50094d45662c121`
- Source archive SHA-256:
  `d53b7232a707d33a0af9404b201b9ab1cf35a49ca0a45d7b02460d53c5d253ca`
- Pluto baseline: `488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02`

The v9-r1 artifact packaging revision is `verified-compilation-v9-r1`. Its
reviewed image ID is
`sha256:554ee8822bf7eca53e76b537e1e8f999787b1824a6b060d2e953dccf9b3476fc`.
The 5,173.2-second full offline review passed all 13 outer gates and all 29
nested checks. Compact schema-v2 evidence has SHA-256
`80b7ed282e622ca8ff844eba899f9c70c4a8853195ea9753247fb66ed90389ec`;
its raw-result tree has SHA-256
`3ea78f4bc97822cd33d51cb05885aa76ad7a5c2d86016cb5793e24be335b2a42`.
Earlier v2 and v3 evidence authenticates only the dependency lock or historical
implementations; it is not evidence for v9.

## Headline correctness contract

The paper-facing partial compiler is:

```coq
compile : raw_config -> Loop.t -> imp ParallelLoop.t
```

`VerifiedParallelCompilerConfig.compile_correct` states that every terminating
execution of a returned structured target has a matching source execution whose
final state is related by `State.eq`. `compile_verified_correct` and
`compile_unsupported_no_result` expose the accepted and rejected cases.
Extraction and preparation for verified code generation are covered by
`ExtractorCorrect.extractor_correct` and
`PrepareCodegen.prepared_codegen_correct_general`.

Tiling validation has exactly two product outcomes:

```coq
DirectBandAccepted | Rejected
```

Every returned tiled target has passed exact work realization, the applicable
layout bridge, and the direct semantic permutable-band checker. Failure of any
obligation returns no tiled target. There is no alternative tiling-validation
acceptance route. In a diamond pipeline, an optional same-space affine
reschedule is a later independently checked transformation; it cannot justify a
failed tiling leg.

## Direct permutable-band contract

For midpoint-ordered instances `x` and `y`, the checker considers pairs whose
schedule prefixes before a supplied band agree and for which some band
component decreases. It proves that every such pair commutes by requiring the
write-write, write-read, and read-write conflict regions to be empty.
Read-read pairs need no check.

This is a semantic sufficient condition patterned on the contrapositive of
Pluto's componentwise dependence nonnegativity. The proof does not claim
equivalence with Pluto's dependence graph, completeness of the checker, or
correctness of band discovery.

The checked tiling theorem has three parts:

1. Ordered quotient links and domain/work checks give an exact one-to-one
   realization of midpoint occurrences in the target point space.
2. The direct conflict checker establishes the semantic band condition.
3. A layout lemma shows that every target-order tie or reversal of a
   midpoint-ordered pair decreases a checked band component.

The common adjacent-exchange argument then proves target-to-midpoint
refinement. The supported layout bridges are:

- one-level ordinary tiling over a common band;
- tiling from an identity midpoint;
- recovered source-like and mixed-depth bands;
- phase-separated mixed-depth one-level tiling;
- grouped or interleaved two-level ordinary, identity-midpoint, recovered
  mixed-depth, and diamond tiling;
- grouped two-level phase-separated mixed-depth tiling;
- one- or two-level diamond tiling after a checked affine midpoint.

All of these use the same direct checker. Unsupported, malformed, or
uncertified proposals reject.

## Claim map

The authoritative machine-readable map is
`artifact/state-eq/claims.json`. Its current theorem surface contains 40 unique
named entries.

| ID | Paper claim | Principal proof surface | Required evidence | Current state |
| --- | --- | --- | --- | --- |
| C1 | End-to-end structured-loop refinement | `ExtractorCorrect.extractor_correct`; `PrepareCodegen.prepared_codegen_correct_general`; `VerifiedParallelCompilerConfig.compile_correct` | Proof build, proof report, no-admit check | Proved; v9 review passed |
| C2 | Direct cross-space tiling for every supported variant, with rejection as the only unsuccessful outcome | Direct checker soundness; exact-realization and layout bridges; `checked_second_level_direct_band_check_correct`; diamond tiling-leg theorems | Direct-route, ordinary, mixed-depth, identity, two-level, diamond, negative, and fail-closed suites | Proved; v9 review passed |
| C3 | ISS is an exact semantic partition and composes with checked routes | `ISSValidatorCorrect.checked_iss_complete_cut_shape_validate_semantics_correct`; ISS composition theorems | ISS and Pluto-compatibility suites | Proved; v9 review passed |
| C4 | Annotation filtering is sound for accepted coordinates; checked annotation routes use the stated restricted target semantics | `ParallelValidator.check_pprog_parallel_currentb_sound`; parallel, multiparallel, innermost-vector, and code-generation theorems | Parallel/vector and Pluto-compatibility suites | Proved; v9 review passed |
| C5 | Literal-stride lowering and the documented checked unroll-and-jam subset | `LoopStride` semantics; `LoopUnroll`; checked loop-jam validation and lowering | Stride comparisons, unroll/jam smoke cases, effect corpus | Proved; v9 review passed |
| C6 | Declared Pluto-facing capability surface | Executable configuration dispatch and fail-closed guards | Capability matrix and compatibility suite | Contract fixed; v9 review passed |

Affine scheduling validation and verified polyhedral reconstruction are inherited
foundations. They are required by C1 but are not presented as new contributions.

## Required v9-r1 artifact observations

The following predeclared assertions were observed in the validated v9 review.

- 13 outer review gates and 29 nested artifact checks;
- zero admitted proofs, aborted proofs, extraction axioms, or missing named
  theorem surfaces;
- non-second-level matrix: 90 cases, 84 direct PB compositions, zero
  alternative tiling acceptances, and 6 explicit vector rejections;
- second-level manifest: 58 checks, 53 direct PB acceptances and 5 negative
  cases, with zero alternative tiling acceptances;
- diamond second-level stress matrix: 16 accepted tilings and 4 later vector
  rejections;
- direct-route smoke matrix: 20 cases;
- extracted fail-closed gate: 6 direct API rejection paths;
- final-affine negative matrix: 48 cases in which a successful diamond tiling
  leg is preserved but the later affine reschedule returns no result;
- Pluto-facing surface: 81 capability rows and 138 checks, comprising 112
  expected successes and 26 expected rejections;
- end-to-end corpus: 62 supported loops, with change and visible-tiling counts
  read only from generated evidence.

The final evidence file is
`artifact/state-eq/evidence/2026-08-26-v9-full-review.json`. Paper tables and
timings must be generated from that file and the untouched v9 raw directory,
never copied from development logs.

## Claim boundaries

The current paper does not claim:

- scalar privatization, scalar expansion, array contraction, storage remapping,
  or another storage-changing transformation;
- overlapped, redundant-work, or flextended tiling;
- reduction-aware parallelization;
- OpenMP, unrestricted fork/join, or machine-SIMD adequacy;
- progress or divergence preservation;
- completeness or necessity of the direct band condition for arbitrary tiled
  targets;
- verification of Pluto's search, profitability, band discovery, maximality, or
  dependence-graph construction;
- correctness of C/OpenScop parsing, printing, downstream C compilation, or an
  external runtime.

The checker is sound and conservative. Rejecting a proposal does not prove that
the transformation is semantically invalid.

## Paper contribution order

1. One compositional target-to-source refinement theorem connects extraction,
   affine scheduling, ISS, tiling, normalization, reconstruction, and the stated
   annotation semantics.
2. Direct cross-space tiling validation combines exact work realization, a
   semantic permutable-band checker, and layout lemmas for ordinary,
   identity-midpoint, mixed-depth, two-level, and diamond variants.
3. The extracted implementation and claim-oriented artifact exercise the same
   checked routes end to end.

ISS and checked annotations provide important breadth but remain supporting
parts of the end-to-end result. Annotation refinement is scoped to the formal
target semantics and is not a runtime-correctness claim.

## Freeze and release state

1. Complete: freeze and tag the v9 proof/validator implementation.
2. Complete: run the exact v9 clean-build workflow; all seven remote CI shards
   passed.
3. Complete: define the v9-r1 manifest, claim catalog, and fail-closed archive
   checks; all 75 local artifact control tests pass.
4. Complete: build and run the exact v9-r1 candidate with networking disabled;
   all 13 outer gates and all 29 nested checks passed.
5. Complete: archive and independently validate compact v9 evidence.
6. In progress: regenerate paper tables and timing from v9 evidence, compile
   all variants, and perform final source/PDF review.
7. Pending external action: publish an immutable registry reference. A local
   candidate image is not a published artifact.
