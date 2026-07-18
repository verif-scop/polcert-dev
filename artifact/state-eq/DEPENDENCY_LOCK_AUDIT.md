# Dependency Lock Audit

Date: 2026-07-18

This audit separates the identity of the verified image from the ability to
rebuild that image later. A content-addressed image fixes the bytes already
built. It does not make a Dockerfile reproducible when that Dockerfile resolves
packages from moving repositories.

The machine-readable record is
[`dependency-lock-audit.json`](./dependency-lock-audit.json).

## Lock Status

| Component | Status | Current enforcement |
|---|---|---|
| PolCert source | Immutable content pin | Annotated tag object, commit, and tree are checked before `git archive` |
| Pluto compiler source | Immutable content pin | Full Git commit plus build-time and runtime baseline checks |
| Pluto base image | Immutable content pin | Registry digest is verified before `docker build --pull=false` |
| Base Ubuntu/tool packages | Transitively immutable | Their bytes are inside the verified Pluto base digest |
| opam executable | Version pin only | `2.0.8` URL; observed SHA-256 is not checked and TLS verification is disabled |
| OCaml | Version pin only | `opam switch create polcert 4.13.1` against an unpinned repository state |
| Coq | Version pin only | `opam pin add coq 8.13.2`; no frozen repository snapshot is imported |
| Other opam packages | Observed only | Package names are installed without version constraints |
| New apt layers | Observed only | Package names are installed without versions from moving Focal repositories |
| Installed switch and dpkg bytes | Indirectly immutable in this image | The local final image ID fixes the bytes, but they are not locked inputs to a fresh build |

The verified image contains `glpk 0.1.8`, `menhir 20260209`,
`stdlib-shims 0.3.0`, and `zarith 1.14`, plus the transitive package versions
listed in the JSON audit. These are observations from the successful offline
review image, not constraints in the frozen Dockerfile.

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

The latter two checksums are not yet enforced during a rebuild. They identify
what was observed in the verified image.

The final local image ID is recorded in the evidence report. It is not called
a published registry digest because the image has not been published.

No opam lock or full switch export is currently consumed by the Dockerfile.
The recorded export hash identifies the observed switch state only. Similarly,
the apt list covers the Dockerfile's direct requests, not the entire transitive
dpkg closure or an SBOM.

## Bounded Locking Plan

1. Archive and checksum the opam `2.0.8` executable, remove
   `--no-check-certificate`, and verify its SHA-256 before installation.
2. Check in the full opam switch export from the verified image and import it
   as the package metadata lock. Verify that every downloaded source has an
   opam checksum.
3. Replace moving Ubuntu endpoints with a dated snapshot, or archive the exact
   `.deb` closure in a small local repository. Version strings without an
   available snapshot are insufficient.
4. Build the toolchain image once, publish it, and record its registry digest.
   Then build the exact PolCert source and reviewer layer from that digest.
5. Re-run the clean offline full profile and publish the final image by
   registry digest together with `build-metadata.json` and the result bundle.

Steps 1-4 change only artifact packaging. They do not require changing the
frozen PolCert source tag. They do require a new image build because package
installation inputs change. The 33-minute full review should then be rerun
once for the newly locked image; documentation-only changes do not invalidate
the already recorded review.
