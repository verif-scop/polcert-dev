# Supplement Packaging Notes

This file is maintained with the packaging code and is not copied into the
submission archive.

## Inputs

The packager consumes the frozen PolCert source tar, both Pluto source archives,
the local artifact result tree, transformation examples, bug-witness log, and
generated Rocq HTML. Generate the Rocq HTML from the frozen image before
packaging:

```sh
docker run --rm --entrypoint bash \
  -v "$PWD:/workspace" \
  polcert-cpp27-anonymous-736c \
  -lc 'eval "$(opam env --switch=polcert)" && \
    cd /workspace/work/verified-compilation-v10-driver && \
    make proof-documentation && \
    rm -rf /workspace/output/releases/cpp27-parallel-hint-fix-736c3781/anonymous-proof-html-736c && \
    cp -a doc/proof-html \
      /workspace/output/releases/cpp27-parallel-hint-fix-736c3781/anonymous-proof-html-736c'
```

Regenerate the reviewer-facing program comparisons from the configured build
of the source snapshot. The collector checks the exact `polopt`, fixed Pluto,
and historical Pluto binary hashes. It stores accepted outputs and rejected
candidates under the release result tree:

```sh
docker run --rm --entrypoint bash \
  -v "$PWD:/workspace" \
  -e POLCERT_BUGGY_POLYCC=/opt/polcert/pluto-historical/polycc \
  polcert-cpp27-anonymous-736c \
  -lc 'python3 /workspace/artifact/cpp27-anonymous/bin/collect_program_comparisons.py \
    --source /polcert \
    --output /workspace/output/releases/cpp27-parallel-hint-fix-736c3781/final/polcert-artifact-check/program-comparisons \
    --force'
```

`collect_typed_program_views.py` runs against a configured build of the same
source commit and writes `typed-program-comparisons/`. Running the three
`csample` tests produces the `orig.cpol` and `opt.cpol` files copied under
`typed-refinement-comparisons/`.

Then build the single upload:

```sh
python3 artifact/cpp27-anonymous/bin/prepare_anonymous.py --force
```

## Packaging Boundary

The submission archive includes formal source, both Pluto source snapshots,
proof HTML, local evidence, and sanitized CI output. It excludes the release
Docker image and account, repository, and Git-history metadata. The publication
package under `artifact/zenodo-v10/` retains those exact identities.

The source filter removes release orchestration, historical proof audits, and a
tracked local ELF containing its build path. It must not modify any `.v` file;
the packager checks the complete formal-source hash map before writing output.

## Final Gate

The packager checks:

- the exact frozen source and successful artifact checks;
- byte identity of every formal source file;
- one supported reviewer view for every catalog record;
- every JSON file;
- every relative HTML target and fragment;
- ZIP CRC integrity and deterministic archive construction;
- archive paths and symlink targets;
- complete recursive Pluto components and absence of prebuilt ELF files;
- names, accounts, repository coordinates, public revisions, and CI run IDs;
- binary payloads as well as decoded text.

After generation, extract the ZIP into a fresh temporary directory and perform
one manual browser pass from `docs/index.html`.
