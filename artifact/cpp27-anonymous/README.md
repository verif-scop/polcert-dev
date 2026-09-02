# PolCert Supplementary Artifact

This artifact contains the source code, Rocq proofs, and tests for PolCert, an
end-to-end verified polyhedral compiler. PolCert accepts a bounded affine loop
and transformation proposals from an external optimizer. It returns an
optimized sequential or parallel loop only after the selected transformations
pass their checks.

Open [`docs/index.html`](docs/index.html) for the offline artifact handbook.

## Compiler Infrastructure and Polyhedral Compilation

PolCert extracts statement domains, access functions, and schedules from a
structured source loop. Its verified pipeline supports index-set splitting,
affine scheduling, ordinary and two-level tiling, diamond tiling,
parallelization, loop generation and cleanup, unrolling, and checked
unroll-and-jam. Pluto searches for transformations; PolCert treats each result
as a proposal and checks it before code generation.

The [compiler guide](docs/compiler.html) introduces the polyhedral model, gives
the complete pipeline, and links every stage to its implementation.

## Proofs

The main theorem states a refinement result: every execution of an accepted
target loop has a source execution from the same initial state with the same
final state. The proof composes local correctness results for extraction,
domain strengthening, transformation validation, sequential or parallel loop
generation, cleanup, and loop postpasses.

The [proof guide](docs/proof.html) states the top-level theorem and links its
supporting results to the Rocq sources and generated proof documentation.

## Tests and Evaluation

The test suite exercises complete compiler routes as well as individual
validators. Case pages show source and optimized programs when both are
executable, the selected options, the run parameters, and whether their results
agree. The evaluation also records performance comparisons and invalid
optimizer proposals that PolCert rejects. Focused reliability cases show the
validators rejecting confirmed optimizer defects. A separate regression checks
Pluto parallel-hint coordinate mapping.

Use the [evaluation guide](docs/evaluation.html) for representative results and
the [test catalog](evidence/results/test-catalog.html) to inspect individual
cases.

## Reproduction

To serve the documentation locally:

```sh
python3 -m http.server 8000 --bind 127.0.0.1
```

Then open [http://127.0.0.1:8000/docs/index.html](http://127.0.0.1:8000/docs/index.html).

To rebuild the artifact and run the default checks:

```sh
docker build -f environment/Dockerfile -t polcert-artifact .
docker run --rm polcert-artifact
```

The [reproduction guide](docs/reproduce.html) lists the available test modes,
expected running times, proof-only commands, and recorded results. The archive
stores the validated PolCert source under `source/`, generated Rocq pages under
`docs/proof/`, pinned Pluto sources under `third_party/pluto/`, and test and
evaluation results under `evidence/`.
