# Dependency Lock Audit

Date: 2026-07-18

This audit separates three identities: the image covered by the archived full
review, the dependency state captured from that image, and the new lock-v1
candidate wrapper that enforces that state. The candidate uses a distinct local
tag and has no full-review evidence yet. A content-addressed reviewed image
fixes bytes already built; it does not make a Dockerfile reproducible when that
Dockerfile resolves packages from moving repositories.

The classification record is
[`dependency-lock-audit.json`](./dependency-lock-audit.json). The enforced
content lock is [`locks/dependency-lock.json`](./locks/dependency-lock.json).

## v9 Construction Update

On 2026-08-26, a fresh execution of the historical source Dockerfile resolved
`conf-pkg-config 5` instead of the locked version 4. The post-build lock rejected
that image before the reviewer wrapper was created. This is the repository-drift
case the original audit anticipated.

The v9 builder no longer resolves apt or opam dependencies. It requires the
full-reviewed v2 origin image at the exact local image ID recorded in
`manifest.json`, verifies that ID, and uses the origin as the dependency base in
`source-image.Dockerfile`. It replaces only the PolCert source tree, rebuilds the
pinned Pluto commit, and configures the v9 tree. The complete dependency state
is then verified again before the reviewer layer is added and at offline review
startup.

This closes package-resolution drift for the v9 image construction available on
this machine. It does not make the origin independently downloadable: until the
origin or final v9 image is exported or published by digest, another machine
must import that exact authenticated image before rebuilding.

## Lock Status

| Component | Status | Current enforcement |
|---|---|---|
| PolCert source | Immutable content pin | Annotated tag object, commit, and tree are checked before `git archive` |
| Pluto compiler source | Immutable content pin | Full Git commit plus build-time and runtime baseline checks |
| Pluto base image | Immutable content pin | Registry digest is verified before `docker build --pull=false` |
| Base Ubuntu/tool packages | Transitively immutable | Their bytes are inside the verified Pluto base digest |
| opam executable | Version pin plus fail-closed checksum | `2.0.8` URL still disables TLS verification, but the built executable must match the reviewed SHA-256 |
| OCaml | Version pin only | `opam switch create polcert 4.13.1` against an unpinned repository state |
| Coq | Version pin only | `opam pin add coq 8.13.2`; no frozen repository snapshot is imported |
| Other opam packages | Resolved-state and installed-content lock | Exact package closure, full switch export, and switch filesystem tree are compared after build and at review startup |
| New apt layers | Resolved-state and installed-content lock | All 684 installed package versions, the dpkg database, and package-owned filesystem contents are compared after build and at review startup |
| Installed switch and dpkg bytes | Fail-closed installed-state lock | Final filesystem tree digests are verified after build; they are not archived inputs to resolution |

The full-reviewed dependency-lock origin image contains `glpk 0.1.8`, `menhir 20260209`,
`stdlib-shims 0.3.0`, and `zarith 1.14`, plus the transitive package versions
listed in the JSON audit. These are observations from the successful offline
origin-image review, not constraints in the frozen Dockerfile.

The same distinction applies to apt. For example, the image contains
`git 1:2.25.1-1ubuntu3.14`, `libglpk-dev 4.65-2`, and
`libgmp-dev 2:6.2.0+dfsg-4ubuntu0.1`, but a fresh `apt-get install` is free to
select other versions.

## Recorded Checksums

- Pluto base registry digest:
  `sha256:0e15a7614af280b02ab0dc31f110c3ee3f7a1fe3ee3d1b503cc3400d87b4f4ce`
- Observed opam `2.0.8` executable SHA-256:
  `95365a873d9e3ae6fb48e6109b5fc5df3b4e526c9d65d20652a78e263f745a35`
- Observed full opam switch export SHA-256:
  `8011b64bbe6c0cfb339cae59bb2cb73ef0162e24b72194784a601f4aece6c5d9`

The opam executable, full switch export, dpkg/package-owned filesystem tree,
and opam switch tree checksums are now enforced after the frozen Dockerfile
finishes. The same verification is the first offline review gate.

- Complete dpkg closure SHA-256:
  `2ef0290183ff3392e14b9803877b1b804c376cb3230a775222d5f9f8566c594b`
- Complete opam package list SHA-256:
  `b0d1b546ec3d8e657ecf3d84f1f967bfef570709440a33930239eb3ae17003dc`

The origin image's local ID is recorded in the evidence report. It is not
called a published registry digest because the image has not been published.
That report authenticates lock capture only for the candidate; it does not
claim the candidate wrapper passed review.

The frozen Dockerfile still resolves packages from network repositories rather
than importing these locks. `build-image.sh` now fails before creating the
candidate wrapper image if that resolution differs in any installed dpkg package,
package-owned file, opam package, switch file, switch metadata, opam executable
byte, or OS release byte. This is a strong detection lock, not an offline
source archive.

## Bounded Locking Plan

Completed locally:

1. Captured the full 684-package dpkg closure, 22-package opam closure, full
   opam switch export, installed filesystem trees, opam binary checksum, and OS
   release identity.
2. Added fail-closed verification after the source image build and as the first
   offline reviewer gate.

Remaining external actions:

1. Archive the opam `2.0.8` executable, remove `--no-check-certificate`, and
   verify its SHA-256 before installation rather than only after installation.
2. Import the captured full opam switch export during package installation and
   archive or verify every downloaded package source.
3. Replace moving Ubuntu endpoints with a dated snapshot, or archive the exact
   `.deb` closure in a small local repository. Version strings without an
   available snapshot are insufficient.
4. Build the toolchain image once, publish it, and record its registry digest.
   Then build the exact PolCert source and reviewer layer from that digest.
5. Re-run the clean offline full profile for the candidate, archive evidence
   tied to its exact image ID, and publish the final image by
   registry digest together with `build-metadata.json` and the result bundle.

These steps change only artifact packaging. They do not require changing the
frozen PolCert source tag. They do require a new image build because package
installation inputs change. The 33-minute full review should then be rerun
once for the newly locked image; documentation-only changes do not invalidate
the already recorded review.
