# PolCert State.eq Artifact Scaffold

This directory builds and runs a claim-oriented Docker artifact for the v9
PolCert milestone:

- tag: `state-eq-polyhedral-verification-complete-2026-08-26-v9`
- tag object: `66a632f44b231d4e210d115529619d8f761a7840`
- commit: `604587ecfec9ff3bf6be655dd66e25af6178d604`
- tree: `3e1daad0f8d05ac0b41c5cb0d50094d45662c121`
- source archive SHA-256:
  `d53b7232a707d33a0af9404b201b9ab1cf35a49ca0a45d7b02460d53c5d253ca`
- Pluto compiler baseline: `488ea2f0c3b7d5e7f6b849809f312aa4a6bcad02`

The scaffold lives in the host-side control repository so it does not modify
the implementation tag. It exports the tagged commit with `git archive`, uses
that archive as the only PolCert build context, and adds the reviewer entry
point in a final image layer.

The source `.dockerignore` excludes generated `*.scop` files. Four tracked
tiling-route fixtures also use that suffix, so the builder creates a
temporary Dockerfile-specific ignore file that admits exactly the four paths
listed in `manifest.json`. It then checks that all four are present in the
source image and that the temporary ignore file was not copied. The source
archive itself remains byte-for-byte the tagged Git archive.

## Reviewer Command

From this directory, with any clone that contains the annotated tag:

```sh
make reproduce POLCERT_SOURCE=/path/to/PolCert
```

This builds `polcert-artifact:state-eq-2026-08-26-v9-candidate` and runs the
full claim suite with Docker networking disabled. The v9 candidate is distinct
from the historical v2 dependency-lock origin and reviewed v3 images. Results
are written to `results/`:

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

The v9 candidate uses schema-v2 review evidence. Do not summarize a run by
hand. After one successful full offline review, create the compact evidence
directly from its untouched raw result directory and matching build metadata:

```sh
make archive-full-review \
  POLCERT_REVIEW_RESULTS="$PWD/results-v9-2026-08-26-r3" \
  POLCERT_REVIEW_EVIDENCE_OUTPUT="$PWD/evidence/2026-08-26-v9-full-review.json"

make review-evidence-validate \
  POLCERT_REVIEW_RESULTS="$PWD/results-v9-2026-08-26-r3" \
  POLCERT_REVIEW_EVIDENCE_OUTPUT="$PWD/evidence/2026-08-26-v9-full-review.json"
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

## Measured Review Time

The completed serial, network-disabled v9 review took 5,173.2 seconds
(86.2 minutes). Its largest top-level gates were the 2,153.0-second nested
29-check artifact run, the 1,473.2-second extraction gate, and the
1,396.8-second clean proof build. The strict 62-case loop suite, which runs
inside the artifact gate, took 252.7 seconds; its slowest case was `advect3d`
at 80.0 seconds. Nested rows overlap with the total and must not be summed.

The extraction target rebuilt nearly the complete proof dependency graph even
though the preceding clean proof gate had succeeded. This explains most of the
serial review's long wall time and is a build-graph optimization opportunity,
not a proof or artifact failure. The recorded run used one make job.

The exact v9 source commit passed the optimized seven-shard GitHub Actions run
in 46 minutes 17 seconds. That run is useful capacity evidence but is not the
network-disabled artifact review: it builds a CI image and distributes test
shards across separate jobs. Reviewers should provision about 90 minutes for a
serial run on a comparable host. Image construction is separate.

The v9 compact evidence is
`evidence/2026-08-26-v9-full-review.json` (SHA-256
`80b7ed282e622ca8ff844eba899f9c70c4a8853195ea9753247fb66ed90389ec`).
It binds image ID
`sha256:554ee8822bf7eca53e76b537e1e8f999787b1824a6b060d2e953dccf9b3476fc`
and raw-result tree SHA-256
`3ea78f4bc97822cd33d51cb05885aa76ad7a5c2d86016cb5793e24be335b2a42`.
See `REPRODUCTION_TIMING.md` for the detailed v9, v3, and v2 records.

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

Before construction, `bin/validate_source.py` checks:

- annotated tag object, commit, and tree IDs;
- Pluto remote, commit, and image values in `tools/ci/pluto-baseline.env`;
- matching Pluto defaults in the frozen `Dockerfile`;
- the registry digest of the locally resolved Pluto base image;
- the exact local image ID of the full-reviewed dependency origin.

The build writes `build/build-metadata.json` with the source archive SHA-256,
Docker image IDs/digests, and OCI labels. The published artifact should retain
this file alongside the image digest.

After validating both image identities, the build uses Docker with
`--pull=false`. The dependency origin is addressed by the exact local image ID
recorded in the manifest, while the Pluto base is addressed by registry digest.

## Network Boundary

Image construction fetches and rebuilds the pinned Pluto commit, but it does
not resolve apt or opam packages again. The artifact-specific
`source-image.Dockerfile` starts from the full-reviewed v2 dependency origin,
whose local image ID is checked before construction. It then replaces the old
PolCert tree with the exact v9 archive and reconfigures the source tree.

- The v9 PolCert source is pinned by its annotated tag object, commit, and tree
  IDs. Pluto source and the Pluto base registry digest are also pinned.
- The 684-package apt state, 22-package opam state, OCaml `4.13.1`, Coq
  `8.13.2`, and opam `2.0.8` are inherited byte-for-byte from the authenticated
  origin instead of being redownloaded for v9.
- The origin image is not yet published. A source rebuild therefore requires
  importing the exact image recorded in `manifest.json`; the final v9 image can
  be replayed independently after it is exported or published by digest.

[`dependency-lock-audit.json`](./dependency-lock-audit.json) records the exact
versions observed in the full-reviewed dependency-lock origin image and
classifies the original networked Dockerfile. The 2026-08-26 update in
`DEPENDENCY_LOCK_AUDIT.md` records why v9 construction now reuses those bytes
instead of re-resolving the moving repositories.

The generated [`locks/dependency-lock.json`](./locks/dependency-lock.json)
strengthens this boundary. It covers the full 684-package dpkg closure, the
dpkg database and installed package file contents, the 22-package opam closure,
the complete opam switch export and switch filesystem contents, the opam
executable SHA-256, and the OS release. `build-image.sh` verifies it after
building the v9 source image and before adding the reviewer layer. The same
verification is the first offline review gate. Dependency-origin substitution
or installed-content drift therefore fails closed.

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
is not review evidence for the v9 wrapper. The reviewed v3 record
`evidence/2026-07-21-v3-full-review.json` is also historical. The v9 candidate
requires its own successful full offline run in
`evidence/2026-08-26-v9-full-review.json`, tied to its exact image ID.

After the image has been built or pulled, review is offline. `bin/run-image.sh`
first resolves the candidate tag to a Docker image ID, then runs that immutable
`sha256:` ID with `docker run --network none`. The ID is recorded in both the
raw environment and claim ledger, and archiving requires it to match the live
image and build metadata. The proof build and all claim checks must use only
files and tools already present in the image.

The complete human-readable analysis and the bounded locking plan are in
[`DEPENDENCY_LOCK_AUDIT.md`](./DEPENDENCY_LOCK_AUDIT.md).

## Reviewed Image Publication

Publication is separate from building and review. The v9 schema-v2 record is
`evidence/2026-08-26-v9-full-review.json`; it authorizes publication only when
the local image ID and untouched raw result directory reproduce that record.
The historical `2026-07-18-full-review.json`, `lock-v1-full-review.json`, and
`2026-07-21-v3-full-review.json` records retain v2/v3 provenance and review
history; none authorizes v9 publication.
Publication refuses any local image whose Docker image ID differs from the ID
in the selected evidence. It also requires the untouched raw result directory
and recomputes the compact record from the raw ledgers, claim report, complete
tree digest, and build metadata before tagging or pushing.

Schema-v1 remains accepted only for the historical reviewed pre-lock image.
The v9 candidate must use schema-v2; the publication guard independently
rechecks its exact 13-gate ledger, dependency-lock SHA-256,
proof/capability/claim assertions, and required raw file hashes.

First validate an explicit, versioned registry reference without tagging,
pushing, or contacting the registry:

```sh
REVIEWED_IMAGE_ID="$(docker image inspect \
  polcert-artifact:state-eq-2026-08-26-v9-candidate --format '{{.Id}}')"
REVIEWED_IMAGE_HEX="${REVIEWED_IMAGE_ID#sha256:}"
make publication-validate \
  POLCERT_PUBLICATION_REF=ghcr.io/example/polcert:state-eq-2026-08-26-v9-${REVIEWED_IMAGE_HEX} \
  POLCERT_REVIEW_RESULTS="$PWD/results-v9-2026-08-26-r3"
```

The reference must include a registry host, lowercase repository, and a
versioned tag. Moving tags such as `latest`, `main`, and `stable` are rejected.
There is no default registry.

After authenticating Docker separately, publish with:

```sh
REVIEWED_IMAGE_ID="$(docker image inspect \
  polcert-artifact:state-eq-2026-08-26-v9-candidate --format '{{.Id}}')"
REVIEWED_IMAGE_HEX="${REVIEWED_IMAGE_ID#sha256:}"
make publish-reviewed-image \
  POLCERT_PUBLICATION_REF=ghcr.io/example/polcert:state-eq-2026-08-26-v9-${REVIEWED_IMAGE_HEX} \
  POLCERT_REVIEW_RESULTS="$PWD/results-v9-2026-08-26-r3"
```

For schema-v2 evidence, set `REVIEWED_IMAGE_HEX` to all 64 hexadecimal
characters after `sha256:`. This content-derived suffix prevents two compliant
publishers from assigning different reviewed images to the same tag.

The workflow performs these checks and actions:

1. Require successful `full`, `network=none` review evidence.
2. Require source tag/commit/tree to match `manifest.json`, zero proof holes,
   29/29 artifact subchecks, an 81-row capability surface, 138 Pluto
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
must already be configured. The local v9 candidate now has matching schema-v2
evidence, but it has not been pushed and therefore is not yet a published
artifact.

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
