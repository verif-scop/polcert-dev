# Pluto Source Snapshots

PolCert treats Pluto as an untrusted producer of optimization proposals. The
two source snapshots here make the optimizer-dependent checks reproducible:

- `fixed/` is used for ordinary compilation and tests.
- `historical/` reproduces earlier Pluto behavior used to test how PolCert
  handles invalid optimization proposals.

Both directories contain Pluto and all of its recursively pinned submodules.
Git repositories and history, configured remotes, CI files, fork-specific
documentation, and build products have been removed. Nested `.gitmodules`
files remain as third-party attribution; the build does not use their URLs.
`environment/Dockerfile` builds both snapshots from source. It assigns each
tree a local Git revision because Pluto embeds a revision in its version output;
the packaged source trees are the artifact inputs.

`MANIFEST.json` records each tree's file count and a deterministic tree hash.
That hash covers the sorted relative path, a NUL byte, the file's SHA-256, and a
newline for every file. The archive hash in the manifest identifies the
packaging input; the compressed archive itself is not included in the package.

Pluto is distributed under the MIT license. Its dependencies retain the
license and attribution files included in their source directories.
