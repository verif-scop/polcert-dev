# Build and Test Environment

`Dockerfile` builds the two packaged Pluto source archives, the Rocq proofs,
and the extracted compiler. From the archive root, run:

```sh
docker build -f environment/Dockerfile -t polcert-artifact .
docker run --rm polcert-artifact
```

The build requires network access for Ubuntu and opam packages and requires an
x86-64 Docker environment. Pluto itself is extracted and built from
`third_party/pluto`; the build does not fetch an optimizer repository or use a
prebuilt optimizer image.
The Ubuntu base image is digest-pinned; apt and opam still use online package
repositories.

Proof and dependency builds can take tens of minutes. Hardware and cache state
affect build time. On an ARM host, enable emulation and add
`--platform linux/amd64` to the build command.

The default command runs the main compiler and executable checks. Other modes
are:

| Command | Work performed |
| --- | --- |
| `docker run --rm polcert-artifact full` | Run the complete artifact check set. |
| `docker run --rm polcert-artifact ci` | Run every CI test group in sequence. |
| `docker run --rm polcert-artifact bugs` | Replay the five paper bugs using the historical and fixed Pluto snapshots. |
| `docker run --rm -v "$PWD/evaluation-results:/results" polcert-artifact evaluation-data retention --output /results/retention` | Collect paired optimization proposals and final loops. |
| `docker run --rm -v "$PWD/evaluation-results:/results" polcert-artifact evaluation-data timing --output /results/timing` | Measure compilation time, with three runs per compiler and kernel. |
| `docker run --rm polcert-artifact proof` | Clean and rebuild the proofs, unfinished-proof gate, and extraction. |
| `docker run --rm polcert-artifact all` | Run `full` and every CI test group; do not repeat `proof`. |
| `docker run --rm -it polcert-artifact shell` | Open a shell in the built environment. |

The additional `bugs-extended` mode runs all source-level Pluto regressions
(also included in `ci` and `all`). Every selected test must pass and the command
must exit with status 0. Negative regressions check specific invalid proposals
and require the documented rejection. The diamond regression checks successful
compilation and matching array states with and without `--rar`.

For a low-memory build, reduce `PLUTO_BUILD_JOBS`, `PROOF_JOBS`, or `BUILD_JOBS`
with `docker build --build-arg NAME=VALUE ...`.

Retention collection requires at least 12 GiB of available memory and waits
while less is available, including for subset runs. Build-job limits do not
change this collection threshold.

Use `evaluation-data --help` for subset options. Recorded paper results are
available offline at `evaluation/results/index.html`; new collections write
fresh outputs and do not replace them. Run timing without concurrent tests.
