# PolCert v10 Artifact

This artifact accompanies *End-to-End Verified Polyhedral Compilation*. It
gives reviewers a fixed source snapshot, a prebuilt Linux
container, and the complete evidence from the release run.

The shortest useful evaluation is `./verify.sh quick`. It checks every
downloaded file, loads the fixed image, checks the proof inventory, runs eight
handwritten C-level examples, exercises extracted rejection paths, and runs the
seven Pluto bug witnesses. On the release machine this took 16 seconds after
the image was loaded. Allow two minutes on a typical workstation, in addition
to the time needed for `docker load`.

## Files

| File | Purpose |
| --- | --- |
| `README.md` | This reviewer guide. |
| `LICENSE` | PolCert's LGPL 2.1 license text. Source dependencies retain their own licenses. |
| `RELEASE.json` | Machine-readable commit, image, CI, and evidence identity. |
| `verify.sh` | Uniform entry point for quick, full, and evidence-only checks. |
| `polcert-v10-source-9d612d0.tar.gz` | Source from the annotated v10 tag, without generated test outputs. |
| `polcert-v10-docker-image.tar` | Prebuilt `linux/amd64` image. This is the supported evaluation environment. |
| `polcert-v10-evidence.zip` | Full local results, transformation examples, provenance, and CI records. |
| `SHA256SUMS` | SHA-256 hashes for the other seven files. |

The Docker image is a separate file because it is large and optional for
readers who only want to inspect the source and frozen evidence. The evidence
is a ZIP so Zenodo can expose its directory tree without creating thousands of
files in the record.

## Requirements

The executable checks require Docker Engine on an `x86_64` Linux host. Reserve
10 GB of disk space for the download, loaded image, and temporary results. Four
CPU cores and 16 GB of RAM are sufficient for the measured CI configuration.
The prebuilt image needs no network access.

The source and evidence can be inspected on any platform with `gzip`, `tar`,
and ZIP support.

## Quick Evaluation

Run from the directory containing all eight files:

```sh
./verify.sh quick
```

The script first runs `sha256sum -c SHA256SUMS`. It then loads this exact image:

```text
polcert-artifact:state-eq-polyhedral-verification-complete-2026-08-29-v10
sha256:6404668840fdac7333abf47f8784b5514e7ca94baa7d47d48fc6e6c6b7d9510a
```

A successful run ends after three groups of executable checks:

- the proof report has zero admitted proofs, aborted proofs, extraction axioms,
  and missing extracted-route theorems;
- the extracted rejection gate and eight handwritten C-level cases pass;
- all seven Pluto bug witnesses pass, which means PolCert rejects the invalid
  candidates produced by the fixed buggy Pluto revision.

This quick check is a representative evaluator path. It does not replace the
complete release run.

## Full Evaluation

Run the complete 30-check artifact suite with:

```sh
./verify.sh full
```

The script uses the prebuilt image without a source bind mount. It copies the
result tree to `review-results/polcert-artifact-check/`, even when a check
fails. A successful run ends with:

```text
[artifact-check] passed 30/30 checks
```

The measured v10 run took 36 minutes on a 16-core host with 27 GB of RAM. The
exact-commit GitHub Actions run used four cores and completed the build plus
seven isolated test shards in 61 minutes 45 seconds. Allow 75 minutes for the
full local command on a four-core host.

The GitHub Actions record is:
<https://github.com/Hughshine/PolCert/actions/runs/33243898549>.

## Inspect Frozen Evidence

Reviewers can inspect the accepted result without Docker:

```sh
./verify.sh evidence
```

This checks all upload hashes and prints the summary from
`artifact-check/artifact-results.json`. To inspect individual files directly:

```sh
unzip polcert-v10-evidence.zip -d polcert-v10-evidence
```

The most useful entries are:

| Path inside the ZIP | Meaning |
| --- | --- |
| `artifact-check/artifact-results.json` | Commands, status, duration, and raw-log paths for all 30 checks. |
| `artifact-check/proof-report.md` | Proof inventory and top-level theorem index. |
| `artifact-check/capability-matrix.md` | Tested route and option coverage. |
| `artifact-check/tiling-route-summary.json` | Tiling-family acceptance and rejection summary. |
| `artifact-check/*.stdout.txt` | Human-readable output for each check. |
| `transformation-examples/` | Input, output, and diff for the 62-case strict Loop suite. |
| `ci/github-actions-33243898549.log` | Combined log for the exact frozen commit. |
| `local-release-validation.log` | Final image, Pluto baseline, and bug-oracle acceptance log. |
| `EXPANDED_RELEASE_SHA256SUMS` | Hashes of the unbundled release evidence before Zenodo packaging. |

## Correctness Boundary

The top-level compiler theorem states refinement from a structured source Loop
program to the generated `ParallelLoop` program for every accepted pipeline
configuration. The checked routes cover affine scheduling, index-set splitting
(ISS), ordinary and multi-level tiling, diamond tiling, constant unrolling,
supported unroll-and-jam cases, and checked parallel or vector annotations.
Vectorization is treated as restricted innermost-loop parallelism; the artifact
does not claim SIMD instruction generation.

Pluto proposes schedules and transformation hints, but it is outside the
trusted base. PolCert either validates a proposal and returns code covered by
the refinement theorem or rejects it. The seven bug witnesses demonstrate this
rejection behavior; they are not a claim that the fixed Pluto revision has been
fully audited.

The theorem does not verify the text parser, pretty-printer, external C
compiler, machine runtime, or transformations that change storage layout or
the dynamic occurrence/work multiset. See `README.md`, `POLOPT.md`, and
`doc/VERIFIED_PIPELINE.md` inside the source archive for the detailed interface
and theorem map.

## Source Inspection

Extract the tagged source into an empty directory:

```sh
mkdir polcert-v10-source
tar -xzf polcert-v10-source-9d612d0.tar.gz -C polcert-v10-source
```

The uncompressed tar must have this SHA-256 hash:

```text
ed4a1cce93b3332bf2b2b80fdb01d7203dddc887f249fff95503d0205c31928c
```

Verify it without keeping a second copy:

```sh
gzip -dc polcert-v10-source-9d612d0.tar.gz | sha256sum
```

The two theorem-level reading entry points are:

- `driver/VerifiedParallelCompilerConfig.v`, theorem `compile_correct`;
- `driver/ExtractedPipelineCorrect.v`, theorem
  `extracted_parallel_compile_correct`.

The Docker image is the reference environment. Building from the source
archive is a maintainer workflow because the artifact Docker target requires
release provenance arguments. The exact procedure is documented in
`ENVIRONMENT.md` inside the archive.

## Release Identity

- PolCert tag: `state-eq-polyhedral-verification-complete-2026-08-29-v10`
- PolCert commit: `9d612d02ac8f27d46c5ec632f912f8a67939e748`
- Validated Pluto commit: `8c43c210c9c08c5958198f22db4b54000380925e`
- Bug-witness Pluto commit: `6f43860b6c4cddeeca09189bf3073f05b78b14a5`
- License: `LGPL-2.1-or-later`

`RELEASE.json`, the image labels, `BUILD_PROVENANCE.json`, the source hash, and
the exact CI commit all encode the same release identity. The packaging script
refuses to create an upload directory when these records disagree.
