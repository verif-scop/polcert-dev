# PolCert Source Snapshot

This directory contains the compiler, its Rocq proofs, and its tests. All
formal `.v` files exactly match the validated snapshot; their hashes are in
`../FORMAL_SOURCE_SHA256SUMS`.

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

For a fixed proof environment, run the Docker build described in
`../environment/README.md` from the archive root.

Tests that run the external Pluto optimizer require a compatible Pluto
installation. Their recorded results are under `../evidence/`.
