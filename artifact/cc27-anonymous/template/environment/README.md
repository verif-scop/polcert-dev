# Build and Test Environment

`Dockerfile` builds the two packaged Pluto source archives, the Rocq proofs,
and the extracted compiler. From the archive root, run:

```sh
docker build -f environment/Dockerfile -t polcert-artifact .
docker run --rm polcert-artifact
```

Without root access, rootless Podman runs the same image; pass
`--format docker` so that the Dockerfile's `SHELL` instruction is kept:

```sh
podman build --format docker -f environment/Dockerfile -t polcert-artifact .
podman run --rm polcert-artifact
```

The build requires network access for Ubuntu and opam packages and an x86-64
Docker environment. Pluto is extracted and built from `third_party/pluto`; the
build does not fetch an optimizer repository or use a prebuilt image. The
Ubuntu base image is digest-pinned; apt and opam use online repositories. On
an ARM host, enable emulation and add `--platform linux/amd64`.

The proof build uses up to 8 parallel jobs, limited to one job per 6 GiB of
available memory. Lower the limits with
`--build-arg PROOF_JOBS=2 --build-arg BUILD_JOBS=2 --build-arg PLUTO_BUILD_JOBS=2`.

| Command | Work performed |
| --- | --- |
| `docker run --rm polcert-artifact` | `make check-smoke`: the main compiler, validator, and route checks. |
| `docker run --rm polcert-artifact full` | `make check-full`: the complete check set. |
| `docker run --rm polcert-artifact ci [group]` | Run every CI test group in sequence, or one group. |
| `docker run --rm polcert-artifact bugs [output]` | Replay the recorded paper bugs and the added miscompilations with the historical and fixed Pluto snapshots. |
| `docker run --rm polcert-artifact bugs-extended` | `make test-pluto-bugs`: all source-level Pluto regressions. |
| `docker run --rm -v "$PWD/results:/results" polcert-artifact evaluation-data retention --cohort primary-affine --output /results/affine` | Collect paired optimization proposals and final loops for one cohort (see `evaluation/README.md`). |
| `docker run --rm -v "$PWD/results:/results" polcert-artifact evaluation-data timing --output /results/timing` | Measure compilation time, three runs per compiler and kernel. |
| `docker run --rm polcert-artifact proof` | Clean and rebuild the proofs, the unfinished-proof gate, and extraction. |
| `docker run --rm polcert-artifact all` | `full` followed by every CI group. |
| `docker run --rm -it polcert-artifact shell` | Open a shell in the built environment. |

Every mode exits with status 0 when all selected checks pass. Negative
regressions check specific invalid proposals and require the documented
rejection. Producer failures are recorded separately from validator rejection.
Run timing without concurrent load.

