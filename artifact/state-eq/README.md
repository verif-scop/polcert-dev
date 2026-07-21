# PolCert State.eq Artifact Scaffold

This directory builds and runs a claim-oriented Docker artifact for the frozen
PolCert milestone:

- tag: `state-eq-polyhedral-verification-complete-2026-07-21-v3`
- commit: `4bc20817c32f2073221cf68475bf9b78c0bab74b`
- tree: `5c21c31e54536dff78c376b4e861efdba3c0d4fb`
- Pluto compiler baseline: `6f43860b6c4cddeeca09189bf3073f05b78b14a5`

The scaffold lives in the host-side control repository so it does not modify
the frozen implementation tag. It exports the tagged commit with `git archive`,
uses that archive as the only PolCert build context, and adds the reviewer
entry point in a final image layer.

The frozen source `.dockerignore` excludes generated `*.scop` files. Four
tracked differential fixtures also use that suffix, so the builder creates a
temporary Dockerfile-specific ignore file that admits exactly the four paths
listed in `manifest.json`. It then checks that all four are present in the
source image and that the temporary ignore file was not copied. The source
archive itself remains byte-for-byte the tagged Git archive.

## Reviewer Command

From this directory, with any clone that contains the annotated tag:

```sh
make reproduce POLCERT_SOURCE=/path/to/PolCert
```

This builds `polcert-artifact:state-eq-2026-07-21-v3-candidate` and runs the
full claim suite with Docker networking disabled. The v3 candidate is distinct
from the historical v2 dependency-lock origin image. Results are written to
`results/`:

- `manifest.json`: immutable source and toolchain pins;
- `dependency-lock-audit.json`: build dependency classifications and observed
  versions;
- `dependency-lock.json`: the exact dpkg/opam state accepted by the reviewer;
- `apt-packages.lock`, `opam-packages.lock`, and
  `opam-switch-full.export`: the companion dependency state records;
- `claims.json`: claim-to-evidence catalog and explicit non-claims;
- `environment.json`: observed tool versions;
- `claim-results.json`: top-level command results;
- `claim-evidence.json`: mechanically resolved claim IDs, passing routes,
  concrete logs, and structured-result assertions;
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

## Full Review Evidence

The v3 candidate uses schema-v2 review evidence. Do not summarize a run by
hand. After one successful full offline review, create the compact evidence
directly from its untouched raw result directory and matching build metadata:

```sh
make archive-full-review \
  POLCERT_REVIEW_RESULTS="$PWD/results-v3-2026-07-21" \
  POLCERT_REVIEW_EVIDENCE_OUTPUT="$PWD/evidence/2026-07-21-v3-full-review.json"

make review-evidence-validate \
  POLCERT_REVIEW_RESULTS="$PWD/results-v3-2026-07-21" \
  POLCERT_REVIEW_EVIDENCE_OUTPUT="$PWD/evidence/2026-07-21-v3-full-review.json"
```

The archiver refuses an existing evidence path. It requires the exact 13 full
review gates in order, with `dependency-lock` first and every gate reporting
`ok=true` and `returncode=0`. It also rechecks the proof and capability counts,
binds the manifest candidate reference to its Docker image ID and build
metadata, compares all copied lock/manifest inputs byte for byte, and records a
deterministic SHA-256 tree digest over the complete raw result directory. It
independently resolves every full-profile claim reference through the outer or
nested result ledger, verifies the referenced stdout/stderr files and JSON
assertions, and rejects unknown, missing, failed, or stale routes. The
extended-only ISS-live reference is explicitly supplemental and recorded as
unavailable in a full run; both required C3 references still resolve
successfully.

The raw directory remains excluded from Git and must be archived externally
with the image. Its recorded tree digest, file count, byte count, and required
file hashes allow the extracted archive to be verified later. Run the focused
tests without starting a review using `make review-evidence-test`. Use
`make claim-evidence-test` for only the claim-reference contract tests.

The shorter health check is:

```sh
make smoke
```

`smoke` still performs a clean proof and executable bootstrap because the
artifact is meant to validate source, not merely replay precompiled binaries.

## Expected Review Time

The v3 full-review time will be recorded from its own raw evidence. Until that
run completes, the only archived planning baseline is the historical v2
network-disabled serial review: 1,996.4 seconds, or 33.3 minutes. Reviewers
should provision at least 45 minutes on a comparable host.

In that historical run, the clean Coq proof build took 748.8 seconds, the
nested artifact check took 1,097.0 seconds, and the strict 62-case suite took
355.4 seconds. The `advect3d` case took 148.8 seconds, dominated by verified
`CodeGen.codegen`. These values are not yet v3 measurements. See
`REPRODUCTION_TIMING.md` for the preserved baseline and the v3 measurement
status.

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
versions observed in the full-reviewed dependency-lock origin image and
classifies each dependency. An observed version is evidence about that image,
not a guarantee that a future networked rebuild will resolve the same bytes.

The generated [`locks/dependency-lock.json`](./locks/dependency-lock.json)
strengthens this boundary. It covers the full 684-package dpkg closure, the
dpkg database and installed package file contents, the 22-package opam closure,
the complete opam switch export and switch filesystem contents, the opam
executable SHA-256, and the OS release. `build-image.sh` verifies it after
building the frozen source image and before adding the reviewer layer. The same
verification is the first offline review gate. Resolution or installed-content
drift therefore fails closed.

Capture and verification commands are:

```sh
make dependency-lock-capture  # only when creating a new reviewed-image lock
make dependency-lock-verify
make dependency-lock-test
```

Capture defaults to the separately named
`polcert-artifact:state-eq-2026-05-25-v2` origin image. It refuses an existing
lock directory and requires that image ID to match strict full-review evidence.
`dependency-lock-verify` instead checks the current candidate image by default.

The origin evidence is copied into the candidate wrapper only so the first
review gate can authenticate the dependency lock's provenance and checksum. It
is not review evidence for the v3 wrapper. The v3 candidate requires a separate
successful full offline run in
`evidence/2026-07-21-v3-full-review.json`, tied to its exact image ID.

After the image has been built or pulled, review is offline. `bin/run-image.sh`
first resolves the candidate tag to a Docker image ID, then runs that immutable
`sha256:` ID with `docker run --network none`. The ID is recorded in both the
raw environment and claim ledger, and archiving requires it to match the live
image and build metadata. The proof build and all claim checks must use only
files and tools already present in the image.

The complete human-readable analysis and the bounded locking plan are in
[`DEPENDENCY_LOCK_AUDIT.md`](./DEPENDENCY_LOCK_AUDIT.md).

## Reviewed Image Publication

Publication is separate from building. By default it expects the v3 schema-v2
evidence in `evidence/2026-07-21-v3-full-review.json`. The historical
`2026-07-18-full-review.json` and `lock-v1-full-review.json` records remain v2
dependency provenance and review history; neither authorizes v3 publication.
Publication refuses any local image whose Docker image ID differs from the ID
in the selected evidence. It also requires the untouched raw result directory
and recomputes the compact record from the raw ledgers, claim report, complete
tree digest, and build metadata before tagging or pushing.

Schema-v1 remains accepted only for the historical reviewed pre-lock image.
The v3 candidate must use schema-v2; the publication guard independently
rechecks its exact 13-gate ledger, dependency-lock SHA-256,
proof/capability/claim assertions, and required raw file hashes.

First validate an explicit, versioned registry reference without tagging,
pushing, or contacting the registry:

```sh
REVIEWED_IMAGE_HEX=38d1df0a35de3fa9e2f5af9b925c8978564e1731cd095caca94c3f3eeba5e304
make publication-validate \
  POLCERT_PUBLICATION_REF=ghcr.io/example/polcert:state-eq-2026-07-21-v3-${REVIEWED_IMAGE_HEX} \
  POLCERT_REVIEW_RESULTS="$PWD/results-v3-2026-07-21"
```

The reference must include a registry host, lowercase repository, and a
versioned tag. Moving tags such as `latest`, `main`, and `stable` are rejected.
There is no default registry.

After authenticating Docker separately, publish with:

```sh
REVIEWED_IMAGE_HEX=38d1df0a35de3fa9e2f5af9b925c8978564e1731cd095caca94c3f3eeba5e304
make publish-reviewed-image \
  POLCERT_PUBLICATION_REF=ghcr.io/example/polcert:state-eq-2026-07-21-v3-${REVIEWED_IMAGE_HEX} \
  POLCERT_REVIEW_RESULTS="$PWD/results-v3-2026-07-21"
```

For schema-v2 evidence, set `REVIEWED_IMAGE_HEX` to all 64 hexadecimal
characters after `sha256:`. This content-derived suffix prevents two compliant
publishers from assigning different reviewed images to the same tag.

The workflow performs these checks and actions:

1. Require successful `full`, `network=none` review evidence.
2. Require source tag/commit/tree to match `manifest.json`, zero proof holes,
   22/22 artifact subchecks, an 81-row capability surface, 138 Pluto
   compatibility checks (112 success and 26 rejection expectations), 62/62
   strict cases, and passing ISS/parallel/vector/second-level/diamond suites.
3. Recompute schema-v2 evidence from the untouched raw result directory.
4. Require the local Docker image ID to equal the ID archived in that evidence.
5. Tag the reviewed image ID with a process-unique staging reference and push
   it, taking the manifest digest directly from that push.
6. Pull the immutable digest and require it to resolve to the reviewed image
   ID, then promote the same manifest to the requested tag without a wrapper
   index and verify the registry reports the same digest.
7. Atomically write `publication/publication-record.json`, binding the review
   evidence checksum, local image ID, tag, and immutable `repository@digest`.

The script never calls `docker login`. Registry credentials and authorization
must already be configured. The v3 candidate is not publication-eligible until
its own full offline evidence exists, and remains unpublished until a registry
reference is provided and a push records its immutable registry digest.

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
