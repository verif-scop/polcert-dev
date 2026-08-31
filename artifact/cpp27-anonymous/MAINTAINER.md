# Supplement Packaging Notes

This file is maintained with the packaging code and is not copied into the
submission archive.

## Inputs

The packager consumes the frozen PolCert source tar, both Pluto source archives,
the local artifact result tree, transformation examples, bug-witness log, and
generated Rocq HTML. Generate the Rocq HTML from the frozen image before
packaging:

```sh
docker run --name polcert-proof-doc --entrypoint bash \
  polcert-artifact:state-eq-polyhedral-verification-complete-2026-08-29-v10 \
  -lc 'eval "$(opam env --switch=polcert)" && make proof-documentation'

docker cp \
  polcert-proof-doc:/polcert/doc/proof-html \
  output/releases/state-eq-polyhedral-verification-complete-2026-08-29-v10/anonymous-proof-html

docker rm polcert-proof-doc
```

Then build the single upload:

```sh
python3 artifact/cpp27-anonymous/bin/prepare_anonymous.py --force
```

## Packaging Boundary

The submission archive includes formal source, both Pluto source snapshots,
proof HTML, and local evidence. It excludes the release Docker image and GitHub
Actions records because those objects carry account, repository, and Git-history
metadata. The publication package under `artifact/zenodo-v10/` retains those
exact identities.

The source filter removes release orchestration, historical proof audits, and a
tracked local ELF containing its build path. It must not modify any `.v` file;
the packager checks the complete formal-source hash map before writing output.

## Final Gate

The packager checks:

- exact frozen source and 30/30 artifact acceptance;
- byte identity of every formal source file;
- every JSON file;
- every relative HTML target and fragment;
- ZIP CRC integrity and deterministic archive construction;
- archive paths and symlink targets;
- complete recursive Pluto components and absence of prebuilt ELF files;
- names, accounts, repository coordinates, public revisions, and CI run IDs;
- binary payloads as well as decoded text.

After generation, extract the ZIP into a fresh temporary directory and perform
one manual browser pass from `docs/index.html`.
