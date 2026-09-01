# PolCert Source Snapshot

This directory contains the compiler, its Rocq proofs, and its tests. It is the
source snapshot used for the recorded proof build and compiler checks.

The main source directories are:

| Directory | Responsibility |
| --- | --- |
| `src/` | The polyhedral model and checks for schedules, tiling, and parallel loops. |
| `polygen/` | Source and target loop languages, loop generation, and unrolling. |
| `driver/` | Complete compiler configurations and top-level correctness theorems. |
| `syntax/` | Concrete instructions, text input, and the extracted command-line tool. |
| `common/`, `cfrontend/`, `cparser/`, `lib/` | Reused CompCert infrastructure. |
| `VPL/`, `flocq/`, `MenhirLib/` | Vendored third-party proof and parsing libraries. |
| `tests/`, `tools/` | Test inputs and validation tools. |

## Instruction Models and Examples

The validators are parameterized by the interfaces in `polygen/StateTy.v`,
`polygen/InstrTy.v`, and `polygen/PolIRs.v`. A client supplies its instruction
syntax, execution relation, state equality, read and write footprints, and
proof that non-conflicting instructions may exchange order. The validation
algorithms therefore depend on nested-loop structure and memory effects, not
on one fixed source-language instruction set.

The executable `.loop` frontend uses the lightweight instruction model in
`syntax/SInstr.v`. Its proofs establish the required interface laws for that
modeled store. A hand-written `.loop` input does not, by itself, prove that its
declared accesses describe an external C program; the recorded tests exercise
the validator under those supplied memory effects.

The more concrete `src/CInstr.v` instance includes typed scalar and array
instructions. `samples/CSample1.v`, `CSample2.v`, and `CSample3.v` encode
matrix multiplication, covariance, and a four-statement GEMVER kernel, with
the corresponding C snippets in `samples/*.c`. `samples/CTypedLoopSamples.v`
adds compact typed examples for extraction, ISS, ordinary and two-level
tiling, diamond tiling, and parallel-loop checking. These files are
hand-constructed Rocq programs, not output from a verified C parser.

The main reusable theorem is
`VerifiedParallelCompilerConfig.compile_correct` in
`driver/VerifiedParallelCompilerConfig.v`. The corresponding theorem for the
executable compiler is `extracted_parallel_compile_correct` in
`driver/ExtractedPipelineCorrect.v`.

The validated toolchain used OCaml 4.13.1 and Rocq/Coq 8.13.2. Run:

```sh
./configure x86_64-linux
make depend
make proof
make extraction
```

For the packaged proof environment, run the Docker build described in
`../environment/README.md` from the archive root.

Tests that run the external Pluto optimizer require a compatible Pluto
installation. Their recorded results are under `../evidence/`.
