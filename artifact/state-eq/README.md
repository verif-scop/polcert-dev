# PolCert State.eq Artifact Scaffold

This directory builds and runs a claim-oriented Docker artifact for the frozen
PolCert milestone:

- tag: `state-eq-polyhedral-verification-complete-2026-05-25-v2`
- commit: `13295e741ad62173411882c6d900dd9dc57337a8`
- tree: `8b83093929e54657c033fa09c5aae73b492c0b67`
- Pluto compiler baseline: `6f43860b6c4cddeeca09189bf3073f05b78b14a5`

The scaffold lives in the host-side control repository so it does not modify
the frozen implementation tag. It exports the tagged commit with `git archive`,
uses that archive as the only PolCert build context, and adds the reviewer
entry point in a final image layer.

## Reviewer Command

From this directory, with any clone that contains the annotated tag:

```sh
make reproduce POLCERT_SOURCE=/path/to/PolCert
```

This builds `polcert-artifact:state-eq-2026-05-25-v2` and runs the full claim
suite with Docker networking disabled. Results are written to `results/`:

- `manifest.json`: immutable source and toolchain pins;
- `claims.json`: claim-to-check map and explicit non-claims;
- `environment.json`: observed tool versions;
- `claim-results.json`: top-level command results;
- `artifact-check/artifact-results.json`: implementation-level artifact report;
- `logs/`: stdout and stderr for every top-level command.

Use separate commands when building and reviewing at different times:

```sh
make build POLCERT_SOURCE=/path/to/PolCert
make review
```

The shorter health check is:

```sh
make smoke
```

`smoke` still performs a clean proof and executable bootstrap because the
artifact is meant to validate source, not merely replay precompiled binaries.

## Clean-Tree Bootstrap

The frozen source archive does not contain generated `.depend` files. Running
`make artifact-check-full` immediately on a fresh tree can therefore fail while
building `VPL/coq/ASAtomicCond.v` with `Cannot find a physical path bound to
logical path Itv`.

The reviewer sequence treats dependency generation as a required bootstrap
step:

```sh
opam exec -- make depend
```

It then builds proofs, checks admitted markers, runs extraction, builds
`polopt`/`polcert`, and invokes the existing full artifact check. The default
outer gate additionally executes the core regression suite and the explicit
vector-current suite, which are not both included in the frozen
`artifact-check-full` target.

The live Pluto-backed ISS suite has a larger integration surface and is kept as
an extended profile instead of a default reviewer gate:

```sh
make extended
```

## Provenance Checks

Before building, `bin/validate_source.py` checks:

- annotated tag object, commit, and tree IDs;
- Pluto remote, commit, and image values in `tools/ci/pluto-baseline.env`;
- matching Pluto defaults in the frozen `Dockerfile`;
- the registry digest of the locally resolved Pluto base image.

The build writes `build/build-metadata.json` with the source archive SHA-256,
Docker image IDs/digests, and OCI labels. The published artifact should retain
this file alongside the image digest.

After validating the local Pluto base digest, the build uses Docker with
`--pull=false`. This prevents a moved registry tag from replacing the already
verified base between validation and image construction.

## Network Boundary

Image construction is not offline: the frozen Dockerfile installs apt/opam
packages and fetches the pinned Pluto commit. The scaffold pins the Pluto base
image digest and verifies the source commits, but apt packages and the
non-Coq opam packages are not version-locked. This is the remaining build-time
reproducibility gap.

After the image has been built or pulled, review is offline. `bin/run-image.sh`
always uses `docker run --network none`; the proof build and all claim checks
must use only files and tools already present in the image.

## Claim Boundary

The claim ledger is intentionally about the completed `State.eq` milestone.
It does not claim storage-changing transformations, scalar/array
privatization, reduction-aware parallelization, or full SIMD semantics. See
`claims.json` for the complete claim-to-evidence map.
