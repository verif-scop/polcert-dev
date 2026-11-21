# PolCert: Supplementary Material

This archive accompanies the submission "End-to-End Verified Polyhedral
Compilation". It contains the Rocq source of PolCert, the two Pluto snapshots
used in the evaluation, a reproducible build environment, the recorded
evaluation data, and the miscompilation study. Nothing needs to be built to
read the proofs or the results.

| Directory | Contents |
| --- | --- |
| `source/` | The PolCert source: Rocq proofs, extraction, the OCaml driver, tests, and the evaluation scripts and inputs. |
| `docs/proof/` | Browsable Rocq sources of the semantic spine and the proof reading guides (`docs/proof/index.html`). |
| `third_party/pluto/` | Source archives of the fixed Pluto used for compilation and of the historical Pluto in which the bugs were found. |
| `environment/` | `Dockerfile` and test entry points. |
| `evaluation/` | Data behind Tables 1 and 2: the recorded collection, the rerun of every Table 1 pair on the submitted source, and timing records. |
| `bugs/` | The miscompilation study (Table 3 and the code-generation bugs): one directory per bug with a reproducer and the recorded outcome. |

## Reading the proofs

Start at `docs/proof/index.html`. The end-to-end theorems are in
`source/driver/ExtractedPipelineCorrect.v`; `source/doc/PROOF_READING_GUIDE.md`
explains the proof structure. The development builds with Coq 8.13.2 and
contains no admitted proofs. The top-level theorems assume excluded middle,
dependent functional extensionality, and 17 computational parameters
(untrusted optimizer, witness-recovery, ordering, VPL backend, naming, and
printing interfaces).

## Building and running

From the extracted archive root:

```sh
docker build -f environment/Dockerfile -t polcert-artifact .
docker run --rm polcert-artifact          # main compiler and validator checks
docker run --rm polcert-artifact bugs     # replay the rejected miscompilations
```

Without root access, rootless Podman runs the same image; pass
`--format docker` so that the Dockerfile's `SHELL` instruction is kept:

```sh
podman build --format docker -f environment/Dockerfile -t polcert-artifact .
podman run --rm polcert-artifact
```

The image build compiles all proofs. `environment/README.md` lists every mode,
the expected running times, and the build arguments.

## Evaluation and bugs

`evaluation/README.md` describes the Table 1 and Table 2 data and how each
number is computed. `bugs/README.md` lists the miscompilations, the Pluto
versions in which they occur, and PolCert's outcome for each.
