# Build and Test Environment

`Dockerfile` builds the two packaged Pluto source snapshots, the Rocq proofs,
and the extracted compiler. From the archive root, run:

```sh
docker build -f environment/Dockerfile -t polcert-artifact .
docker run --rm polcert-artifact
```

The build requires network access for Ubuntu and opam packages and requires an
x86-64 Docker environment. Pluto itself is built from `third_party/pluto`; the
build does not fetch an optimizer repository or use a prebuilt optimizer image.
The Ubuntu base image is digest-pinned; apt and opam still use online package
repositories.

On the artifact preparation host, a cold build took about 40 minutes and the
default checks took about 31 minutes. The final image was about 2.1 GB; hardware
and cache state affect these values. On an ARM host, enable emulation and add
`--platform linux/amd64` to the build command.

The default command runs 25 compiler, executable, and regression checks. Other
modes are:

| Command | Work performed |
| --- | --- |
| `docker run --rm polcert-artifact full` | Run all 30 artifact checks. |
| `docker run --rm polcert-artifact ci` | Run all seven CI test groups in sequence. |
| `docker run --rm polcert-artifact ci base` | Run one named CI test group. |
| `docker run --rm polcert-artifact bugs` | Run seven Pluto regression/witness checks, including the historical snapshot. |
| `docker run --rm polcert-artifact proof` | Clean and rebuild the proofs, unfinished-proof gate, and extraction. |
| `docker run --rm polcert-artifact all` | Run `full` and every CI test group; do not repeat `proof`. |
| `docker run --rm -it polcert-artifact shell` | Open a shell in the built environment. |

The CI group names are `tiling-second-rejection`, `tiling-second-manifest`,
`tiling-second-routes`, `tiling-compat`, `generated`, `tiling-core`, and `base`.

The `evidence/` directory contains the submitted run. To retain the output from
a new `full` run, mount its output directory:

```sh
mkdir -p artifact-check-output
docker run --rm \
  -v "$PWD/artifact-check-output:/tmp/polcert-artifact-check" \
  polcert-artifact full
```

CI groups use group-specific paths under `/tmp` and generated cases under
`/polcert/tests`. To retain them, omit `--rm`, name the container, and use
`docker cp` after the run.
The submitted evidence includes the release-image provenance check. A new image
correctly reports that gate as not required; `MANIFEST.json` describes its inputs.
For a low-memory build, reduce `PLUTO_BUILD_JOBS`, `PROOF_JOBS`, or `BUILD_JOBS`
with `docker build --build-arg NAME=VALUE ...`.
