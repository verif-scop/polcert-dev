# State.eq Baseline Reproduction

Date: 2026-07-18

This report records a clean reproduction of the tagged State.eq milestone. It
is intended for the artifact maintainer and for reviewers who need to connect a
paper claim to an exact source revision, Pluto revision, command, and result.

## Result

The tagged implementation builds from source and passes the full artifact
runner under the pinned Pluto revision. The runner completed all 18 checks. The
proof report found no local admitted or aborted proofs, no unrealized extracted
axioms, and no missing theorem named in its route map.

This run validates the tagged source in one existing container image. It does
not yet establish that the repository can build a fresh, self-contained Docker
image without hidden setup. The bootstrap findings below define concrete work
for that artifact.

## Pinned Baseline

| Item | Recorded value |
|---|---|
| PolCert tag | `state-eq-polyhedral-verification-complete-2026-05-25-v2` |
| Tag kind | annotated tag |
| Tag object | `f9cc209ae597f58e98841a96e13f8b355ee75eb3` |
| Tag message | `State.eq polyhedral verification complete, with unbounded multipar` |
| Peeled PolCert commit | `13295e741ad62173411882c6d900dd9dc57337a8` |
| PolCert commit date | `2026-05-25T22:00:06+03:00` |
| Pluto commit | `6f43860b6c4cddeeca09189bf3073f05b78b14a5` |
| Pluto remote | `https://github.com/verif-scop/pluto.git` |
| Container image name | `hughshine/polcert:latest` |
| Container image digest | `hughshine/polcert@sha256:e0ae1229898a76407fa2ebbe65aa74b0a37d2dac1d89ed0b6b1d993f4aa03b96` |
| Image creation time | `2023-10-26T14:57:45.129477555Z` |

The mutable `latest` name is not sufficient archival metadata. The digest
above identifies the image used for this run. A replacement artifact should
publish an immutable name and digest derived from the exact source commit.

## Isolation

The run used a detached worktree at
`/tmp/polcert-state-eq-v2-repro` inside container `gifted_curie`:

```sh
cd /polcert
git worktree add --detach /tmp/polcert-state-eq-v2-repro \
  state-eq-polyhedral-verification-complete-2026-05-25-v2
```

Before configuration, the worktree had no tracked changes, ignored build
products, `.vo` files, `polopt`, or `polcert`. The container's active
`unify-multipar-wrapper` branch was not checked out, reset, or modified.

The artifact runner always writes to `/tmp/polcert-artifact-check` and does not
clear that directory. An older directory existed before this run. It was moved
to
`/tmp/polcert-artifact-check.before-state-eq-v2-repro.20260718T064044Z`
before the runner started. The recorded output directory was therefore empty
and was created by this run.

The strict suite materializes its corpus into tracked paths. It left 56 modified
files under `tests/polopt-generated/cases/` in the disposable worktree. No proof
or implementation file changed.

## Toolchain

All build commands used `opam exec --` with switch `polcert`.

| Tool | Version |
|---|---|
| Operating system | Ubuntu 20.04.6 LTS, x86-64 |
| OCaml | 4.13.1 |
| Coq | 8.13.2 |
| Menhir | 20230608 |
| Python | 3.8.10 |
| GCC | 9.4.0 |
| GNU Make | 4.2.1 |
| Pluto | `6f43860` |

The container's default shell resolves system OCaml 4.08.1 and Coq 8.11.0.
Running `./configure x86_64-linux` without `opam exec --` therefore fails the
Coq version check. Reviewer commands must enter the opam switch explicitly or
the Docker entrypoint must initialize it.

## Reproduction Commands

The reliable sequence in this image is:

```sh
cd /tmp/polcert-state-eq-v2-repro
opam exec -- ./configure x86_64-linux
opam exec -- make depend
opam exec -- make artifact-check-full
opam exec -- make test
opam exec -- make test-vector-current-suite
opam exec -- make test-iss-pluto-live-suite
```

Exit status was zero for every command in this sequence.

`artifact-check-full` builds all Coq proofs, extracts the OCaml implementation,
builds `polopt` and `polcert`, and then invokes
`tools/artifact/run_artifact_check.py --mode full`.

## Full Artifact Results

The full runner reported `ok: true` for 18 of 18 checks:

| Check | Result | Time |
|---|---:|---:|
| Python artifact-tool compilation | pass | 0.0 s |
| Proof report | pass | 0.3 s |
| Capability matrix | pass | 0.1 s |
| Codegen-gap exploration | pass | 0.9 s |
| Unroll/jam effect corpus | pass | 13.4 s |
| Unbounded identity-composition exploration | pass | 175.7 s |
| Pluto compatibility suite | pass | 355.4 s |
| Five whole-C cases | pass | 0.8 s total |
| Second-level tiling suite | pass | 63.3 s |
| Diamond tiling suite | pass | 93.1 s |
| `check-admitted` | pass | 0.0 s |
| Strict generated loop suite | pass | 358.4 s |
| ISS dump suite | pass | 0.3 s |
| Parallel-current suite | pass | 39.2 s |

The five whole-C cases cover constant unrolling, variable-block unroll/jam,
dependent-guard unroll/jam, positive stride, and negative stride.

## Proof and Capability Counts

The generated proof report contains 24 theorem-facing routes and reports:

| Measure | Count |
|---|---:|
| Coq files scanned | 178 |
| Local admitted markers | 0 |
| Local abort markers | 0 |
| Extracted OCaml unrealized axioms | 0 |
| Missing listed route theorems | 0 |

The capability report contains 81 capability rows and 114 compatibility
checks. The executable Pluto compatibility suite passed all 114 checks.

The strict generated loop suite reported:

| Measure | Count |
|---|---:|
| Inputs | 62 |
| Passed | 62 |
| Failed | 0 |
| Changed | 59 |
| Nontrivially changed | 59 |
| Detected tiled outputs | 39 |

The ISS dump suite accepted four positive witnesses and rejected three negative
witnesses as expected. The live ISS suite accepted three Pluto-generated
witnesses and rejected its malformed-cut fixture. The parallel-current,
vector-current, and second-level tiling suites each reported `OK`.

The diamond suite reported six fixtures with a diamond effect, two accepted
fixtures with no effect, and eleven inputs rejected by Pluto's C frontend. Its
overall `OK` result means every fixture matched its expected classification; it
does not mean Pluto transformed all nineteen inputs.

The legacy `make test` target also exited zero. It completed the OpenScop
reader, CPol/OpenScop conversion, Pluto invocation, three sample programs, and
all 62 Pluto examples in both validation directions.

## Bootstrap Findings

Two failed attempts identify gaps that the Docker artifact should fix.

First, a fresh worktree has no ignored `Makefile.config`. Calling
`make artifact-check-full` immediately fails with:

```text
Makefile:17: Makefile.config: No such file or directory
make: *** No rule to make target 'Makefile.config'.  Stop.
```

Second, after successful configuration but before dependency generation,
`opam exec -- make artifact-check-full` starts Coq compilation in an invalid
order and fails with:

```text
COQC VPL/coq/ASAtomicCond.v
Error: Unable to locate library Itv.
make: *** [Makefile:454: ASAtomicCond.vo] Error 1
```

Running `opam exec -- make depend` fixes the order. Retrying the same full
target then passes. The current target is therefore not a one-command entry
point from a fresh checkout.

The reviewer-facing Docker command should run configuration and dependency
generation itself. It should also allocate or clear a unique artifact output
directory, because the Python runner preserves files already present under its
output root.

## Evidence

Git-tracked evidence is stored in
`doc/evidence/state-eq-baseline-2026-07-18/`. The primary files are:

| File | SHA-256 |
|---|---|
| `artifact-results.json` | `6fb1e7b50793bd3e4342e7b610aa50e702a14ee357865b3b78c366e5199a9245` |
| `proof-report.json` | `19d3908e3f36da35c32446fa4c5963ac45e86f3140fa4c8fba8d601694a8c838` |
| `capability-matrix.json` | `c7fa0bea0c1eec90dcf6cda040b18fe2628ceb66b62ade4a56eea0928ffd5e82` |

That directory also retains the generated Markdown reports and the key suite
stdout files. The complete 12 MiB runner output and console logs remain in the
git-ignored directory
`work/state-eq-baseline-reproduction-2026-07-18/`.

## Interpretation

This run closes the missing exact-tag execution record: commit `13295e7` passes
the complete full artifact runner under Pluto `6f43860`. The result supports
claims represented by the proof report and capability matrix at that commit.

The record does not cover storage-changing transformations, scalar
privatization semantics, reduction semantics, or a fresh build of a newly
published Docker image. Those remain outside this baseline. Do not move the
existing annotated tag; publish any artifact fixes as new commits and identify
the final image by digest.
