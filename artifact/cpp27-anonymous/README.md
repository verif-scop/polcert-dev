# PolCert Supplementary Material

PolCert verifies loop optimizations proposed by an external optimizer. It
represents each execution of a loop statement as an integer point, checks the
proposed execution order, tiling, and parallel loops, and generates code only
after the required checks succeed.

The main theorem is end to end: whenever PolCert accepts a compilation, every
execution of the generated program has a matching execution of the source
program with the same modeled memory. The optimizer that searches for a good
transformation need not be trusted.

This archive contains the source snapshot, proof scripts for the Rocq proof
assistant, readable proof documentation, and recorded validation results for
*End-to-End Verified Polyhedral Compilation*. Start with
[`docs/index.html`](docs/index.html):

- **Overview:** read Compiler Design, Correctness Guarantee, and Project Map.
- **Proof:** read Top-Level Proof, Proof Structure, and Proof by Component.
- **Details:** follow theorem links to the generated Rocq pages and source.

## Contents

| Path | Contents |
| --- | --- |
| `docs/index.html` | Offline guide to the compiler, proof, and evidence. |
| `docs/proof/` | Generated Rocq pages for the main proof modules. |
| `source/` | The validated source and proof snapshot. |
| `environment/Dockerfile.proof` | Reproducible proof-build environment. |
| `evidence/artifact-check/` | Results and logs from all 30 artifact checks. |
| `evidence/transformation-examples/` | Inputs and outputs for 62 loop examples. |
| `evidence/executable-checks/` | Baseline and optimized execution comparisons. |
| `evidence/pluto-bug-witnesses/` | Optimizer outputs that PolCert correctly rejects. |
| `evidence/validation-summary.json` | Short machine-readable result summary. |
| `THIRD_PARTY.md` | Third-party attribution and license map. |
| `MANIFEST.json` | Snapshot metadata and content counts. |
| `FORMAL_SOURCE_SHA256SUMS` | Per-file hashes for every packaged `.v` file. |
| `SHA256SUMS` | Hashes for every other file in the extracted archive. |

## Build Information

The validated environment used OCaml 4.13.1 and Rocq/Coq 8.13.2. The fixed
proof environment can be built from the extracted archive root:

```sh
docker build -f environment/Dockerfile.proof -t polcert-proof .
```

With the listed dependencies already installed, the equivalent source build is:

```sh
cd source
./configure x86_64-linux
make depend
make proof
make extraction
```

## Integrity

From the extracted archive root:

```sh
sha256sum -c SHA256SUMS
```

This command checks every packaged file. Formal-source hashes are also listed
separately in `FORMAL_SOURCE_SHA256SUMS` and recorded in `MANIFEST.json`.
