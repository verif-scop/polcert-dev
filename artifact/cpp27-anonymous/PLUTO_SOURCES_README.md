# Pluto Source Snapshots

Pluto proposes optimization schedules, and PolCert checks them before code
generation. The two source archives here make those checks reproducible:

- `fixed.tar.xz` is used for ordinary compilation and tests.
- `historical.tar.xz` reproduces earlier Pluto behavior used to test how PolCert
  handles invalid optimization proposals.

Both archives contain Pluto and all of its recursively pinned submodules.
Git repositories and history, configured remotes, CI files, fork-specific
documentation, and build products have been removed. Nested `.gitmodules`
files remain as third-party attribution; the build does not use their URLs.
`environment/Dockerfile` extracts and builds both snapshots. It assigns each
tree a local Git revision because Pluto embeds a revision in its version output.

`MANIFEST.json` records each source tree's file count and archive identity.

Pluto is distributed under the MIT license. Its dependencies retain the
license and attribution files included in their source directories.
