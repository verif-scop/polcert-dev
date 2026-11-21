# PolCert Supplementary Artifact

This artifact contains the source, Rocq proofs, and evaluation of PolCert, an
end-to-end verified polyhedral compiler. Open [the offline guide](docs/index.html)
to inspect the compiler, follow the proofs, or review the results without
rebuilding.

## Compiler and Proofs

PolCert combines verified loop extraction and generation with validators for
affine scheduling, index-set splitting, tiling, and parallelization. Pluto
proposes optimizations; the verified components establish semantic refinement
for successful loop-to-loop compilation.

The [compiler guide](docs/compiler.html) maps the pipeline to its source files.
The [proof guide](docs/proof.html) links the end-to-end theorem and its supporting
lemmas to the Rocq sources and generated documentation.

## Evaluation

The evaluation addresses optimization retention, compilation overhead, and
miscompilation detection. Paired comparisons check effects in the final
generated loops, rather than counting successful compilations. Compilation
measurements report both end-to-end time and the main stages. Five
execution-confirmed Pluto bugs exercise rejection of unsafe schedules and
parallel hints, and checked compilation that omits unsafe loop fusion.

Start with the [evaluation guide](docs/evaluation.html) and
[recorded results](evaluation/results/index.html). Per-case evidence and
machine-readable tables are available from the result pages. The
[test catalog](evidence/results/test-catalog.html) separately records the
compiler and validator regression checks.

## Build and Run

From the extracted archive root:

```sh
docker build -f environment/Dockerfile -t polcert-artifact .
docker run --rm polcert-artifact
```

The default command runs the main compiler checks. Use `full` for the complete
artifact checks or `bugs` for the five paper reliability cases. See the
[reproduction guide](docs/reproduce.html) for proof rebuilding and evaluation
commands.

Every test mode is expected to exit with status 0. Negative regressions pass
when their specified rejection and output conditions hold. Producer failures
are recorded separately from validator rejection.

The archive contains `source/`, `docs/proof/`, `third_party/pluto/`,
`evaluation/`, and `evidence/`. It includes the fixed Pluto used for ordinary
compilation and current tests, plus a historical version used to reproduce bugs.
Recorded measurements retain their original compiler and producer identities.
