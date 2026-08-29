# PolCert Source Snapshot

This directory contains the proof, compiler, extraction, test, and support
source used by the CPP supplement. All formal `.v` files are byte-for-byte
identical to the validated source snapshot; their hashes are listed in
`../FORMAL_SOURCE_SHA256SUMS`.

The main source directories are:

| Directory | Responsibility |
| --- | --- |
| `src/` | Polyhedral semantics, extraction correctness, validators, and semantic bridges. |
| `polygen/` | Structured target languages, loop generation, and verified loop rewrites. |
| `driver/` | Composition of checked components into complete compiler routes. |
| `syntax/` | Concrete instantiation and the extracted command-line pipeline. |
| `common/`, `cfrontend/`, `cparser/`, `lib/` | Reused CompCert infrastructure. |
| `VPL/`, `flocq/`, `MenhirLib/` | Vendored third-party proof and parsing libraries. |
| `tests/`, `tools/` | Test inputs and artifact runners. |

The paper-facing generic endpoint is
`VerifiedParallelCompilerConfig.compile_correct` in
`driver/VerifiedParallelCompilerConfig.v`. The closest theorem to the extracted
pipeline is `extracted_parallel_compile_correct` in
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

The optimizer's Pluto-dependent executable tests require a compatible Pluto
installation in addition to this source. Their validated outputs are provided
under `../evidence/`.
