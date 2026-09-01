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
*End-to-End Verified Polyhedral Compilation*. [`docs/index.html`](docs/index.html)
links the compiler pipeline, correctness theorem, proof structure, and source.

Open `docs/index.html` in a browser. If the browser restricts links below a
local `file://` page, serve the extracted directory instead:

```sh
python3 -m http.server 8000 --bind 127.0.0.1
```

Then open <http://127.0.0.1:8000/docs/index.html>.

For the complete test inventory, open
[`evidence/results/test-catalog.html`](evidence/results/test-catalog.html).

## Contents

| Path | Contents |
| --- | --- |
| `docs/index.html` | Offline guide to the compiler, proof, and evidence. |
| `docs/proof/` | Generated Rocq pages for the main proof modules. |
| `source/` | The validated source and proof snapshot. |
| `third_party/pluto/` | Pluto source archives used for ordinary tests and invalid-proposal cases. |
| `environment/Dockerfile` | Rebuilds Pluto, the proofs, and the extracted compiler. |
| `evidence/README.md` | Guide to the recorded proof and test results. |
| `evidence/results/` | Test catalog, theorem and proof-build report, commands, and raw output. |
| `evidence/optimized-loop-examples/` | Before-and-after loop outputs, labeled by transformation. |
| `evidence/execution-comparisons/` | Checks that original and optimized programs return the same result. |
| `evidence/rejected-optimizer-outputs/` | Unsafe or non-certifiable optimizer proposals, their causes, and PolCert's response. |
| `THIRD_PARTY.md` | Third-party attribution and license map. |
| `MANIFEST.json` | Snapshot metadata and content counts. |

## Build Information

The Docker environment builds both Pluto snapshots, OCaml 4.13.1, Rocq/Coq
8.13.2, every proof, and the extracted `polcert` and `polopt` executables. From
the extracted archive root, run:

```sh
docker build -f environment/Dockerfile -t polcert-artifact .
docker run --rm polcert-artifact
```

The build requires network access for Ubuntu and opam packages and requires an
x86-64 Docker environment. The default container command runs 25 compiler and
executable checks. The following modes are useful for a complete review:

```sh
docker run --rm polcert-artifact full   # all 30 artifact checks
docker run --rm polcert-artifact bugs   # seven Pluto reliability checks
docker run --rm polcert-artifact proof  # clean proof and extraction rebuild
```

The default run is the shortest end-to-end check; `full` adds the five slower
checks. See [`environment/README.md`](environment/README.md) for targeted test
modes and expected running times.

With the listed dependencies already installed, this proof-only source check is
also available:

```sh
cd source
./configure x86_64-linux
make depend
make proof
make check-admitted
make extraction
```
