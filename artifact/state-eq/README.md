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
- `dependency-lock-audit.json`: build dependency classifications and observed
  versions;
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

The result directory must be empty at the start of a review. This prevents a
second run from leaving stale logs or nested suite outputs in the archived
evidence. Use a new `POLCERT_ARTIFACT_OUTPUT` path, or explicitly remove the
previous generated results with `make clean-results`, before rerunning.

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
packages and fetches the pinned Pluto commit. The lock status is not uniform:

- PolCert source, Pluto source, and the Pluto base registry digest are
  immutable content pins checked before the build.
- OCaml `4.13.1`, Coq `8.13.2`, and the opam executable `2.0.8` are explicit
  version selections, but their repository state or downloaded bytes are not
  all enforced by immutable checks in the frozen Dockerfile.
- apt package requests have no `=version` constraints and use moving Ubuntu
  Focal repositories.
- `zarith`, `glpk`, `menhir`, and `stdlib-shims` have no version constraints;
  their transitive opam dependencies are also resolved from an unpinned opam
  repository snapshot.

[`dependency-lock-audit.json`](./dependency-lock-audit.json) records the exact
versions observed in the verified image and classifies each dependency. An
observed version is evidence about that image, not a guarantee that a future
networked rebuild will resolve the same bytes.

After the image has been built or pulled, review is offline. `bin/run-image.sh`
always uses `docker run --network none`; the proof build and all claim checks
must use only files and tools already present in the image.

The complete human-readable analysis and the bounded locking plan are in
[`DEPENDENCY_LOCK_AUDIT.md`](./DEPENDENCY_LOCK_AUDIT.md).

## Reviewed Image Publication

Publication is separate from building. By default it uses the archived full
review evidence in `evidence/2026-07-18-full-review.json` and refuses any local
image whose Docker image ID differs from the reviewed ID.

First validate an explicit, versioned registry reference without tagging,
pushing, or contacting the registry:

```sh
make publication-validate \
  POLCERT_PUBLICATION_REF=ghcr.io/example/polcert:state-eq-2026-05-25-v2
```

The reference must include a registry host, lowercase repository, and a
versioned tag. Moving tags such as `latest`, `main`, and `stable` are rejected.
There is no default registry.

After authenticating Docker separately, publish with:

```sh
make publish-reviewed-image \
  POLCERT_PUBLICATION_REF=ghcr.io/example/polcert:state-eq-2026-05-25-v2
```

The workflow performs these checks and actions:

1. Require successful `full`, `network=none` review evidence.
2. Require source tag/commit/tree to match `manifest.json`, zero proof holes,
   18/18 artifact subchecks, 114 Pluto compatibility checks, 62/62 strict
   cases, and passing ISS/parallel/vector/second-level/diamond suites.
3. Require the local Docker image ID to equal the ID archived in that evidence.
4. Run `docker tag` and `docker push` for the explicit registry tag.
5. Read the matching registry digest from Docker `RepoDigests` after push.
6. Atomically write `publication/publication-record.json`, binding the review
   evidence checksum, local image ID, tag, and immutable `repository@digest`.

The script never calls `docker login`. Registry credentials and authorization
must already be configured. A rebuilt wrapper has a different image ID and is
rejected by the default evidence; publishing it requires an explicit new full
review evidence file via `POLCERT_REVIEW_EVIDENCE`.

The publication parser and refusal paths have a no-network fixture suite:

```sh
make publication-test
```

## Claim Boundary

The claim ledger is intentionally about the completed `State.eq` milestone.
It does not claim storage-changing transformations, scalar/array
privatization, reduction-aware parallelization, full SIMD semantics, or
overlapped/flextended tiling. See `claims.json` for the complete
claim-to-evidence map.
