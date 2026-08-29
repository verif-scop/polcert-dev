# PolCert Supplementary Material

This archive contains the proof scripts, source snapshot, proof documentation,
and validation evidence for the CPP submission *End-to-End Verified
Polyhedral Compilation*.

Start by opening [`docs/index.html`](docs/index.html) in a browser. The handbook
offers three reading paths:

- **10-minute design pass:** tool design, trust boundary, and project map.
- **30-60 minute proof pass:** final refinement theorem and one complete route.
- **Deep review:** generated Rocq pages, formal source, and per-check evidence.

## Contents

| Path | Contents |
| --- | --- |
| `docs/index.html` | Main offline handbook and paper-to-artifact crosswalk. |
| `docs/proof/` | Generated Rocq documentation for the proof-critical modules. |
| `source/` | Source snapshot. Formal source files match the validated snapshot. |
| `environment/Dockerfile.proof` | Fixed proof and extraction build environment. |
| `evidence/artifact-check/` | Record and logs from the complete 30-check local run. |
| `evidence/transformation-examples/` | Indexed inputs, optimized outputs, and diffs for the 62-example strict suite. |
| `evidence/executable-checks/` | 62 baseline-vs-optimized comparisons plus five effect-focused runs. |
| `evidence/pluto-bug-witnesses/` | Inputs and explanations for invalid candidates rejected by PolCert. |
| `evidence/validation-summary.json` | Compact machine-readable acceptance summary. |
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

The packaging gate verifies that all formal `.v` files match the validated
source snapshot. It also checks HTML links, JSON files, archive paths, and the
internal file hashes. The per-file formal-source inputs are recorded in
`FORMAL_SOURCE_SHA256SUMS`; its own digest is recorded in `MANIFEST.json` and
the packaged artifact result record.
