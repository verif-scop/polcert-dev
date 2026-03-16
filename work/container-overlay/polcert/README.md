# PolCert

PolCert provides two user-facing tools:

- [`polcert`](./POLCERT.md): validate a Pluto/OpenScop scheduling result.
- [`polopt`](./POLOPT.md): run a verified polyhedral optimization pipeline on a structured loop fragment.

If you care about the optimizer, start with [`POLOPT.md`](./POLOPT.md).
If you already have OpenScop files and only want validation, start with [`POLCERT.md`](./POLCERT.md).
For a concise note on the current verified affine+tiling route, see
[`doc/VERIFIED_PIPELINE.md`](./doc/VERIFIED_PIPELINE.md).

## Environment and setup

The standard environment for this repository is defined by [Dockerfile](./Dockerfile).
If you want the supported setup, use Docker or a container built from that file.
If you prefer to configure the environment manually, treat `Dockerfile` as the source of truth and mirror its dependencies.
Detailed instructions are in [ENVIRONMENT.md](./ENVIRONMENT.md).

## Quick start

Inside the project container, build with:

```sh
make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
make test
```

This produces:

- `./polcert <before.scop> <after.scop>`
- `./polopt <file.loop>`

## Two usage stories

### 1. I already have Pluto `before.scop` / `after.scop`

Use [`polcert`](./POLCERT.md).
It checks whether the schedule change preserves the polyhedral dependence semantics.

### 2. I have a loop nest and want the optimizer to do the full pipeline

Use [`polopt`](./POLOPT.md).
It parses a `.loop` file, extracts a polyhedral model, runs the verified
affine+tiling optimization pipeline, generates optimized loop code, and applies
verified post-codegen cleanup.

## Status

- The verified optimization core lives in [driver/PolOpt.v](./driver/PolOpt.v).
- The final optimizer definition is `Opt = Opt_prepared`.
- The final end-to-end theorem is `Opt_correct`.
- `polopt` now includes the checked tiling route in its main verified pipeline.
- `polcert` now supports both direct affine validation and the phase-aligned
  tiling validation route.
- The strict proved-path `polopt` regression suite currently succeeds on all generated benchmark inputs:
  - total inputs: `62`
  - succeeded: `62`
  - changed: `60`
  - unchanged: `2`
  - nontrivially changed: `60`
  - automatically detected tiled outputs: `38`

## CI

GitHub Actions runs the Docker-based clean build and regression flow on every push and pull request.
The CI job builds the image from [Dockerfile](./Dockerfile) and then runs [tools/ci/run_ci.sh](./tools/ci/run_ci.sh), which executes:

- the full Coq proof build
- `check-admitted`
- extraction
- `polcert` / `polopt` builds
- `make test`
- the strict `polopt` benchmark suite

## Documentation map

- [`ENVIRONMENT.md`](./ENVIRONMENT.md): Docker setup, environment notes, and how to mirror the Dockerfile manually.
- [`POLCERT.md`](./POLCERT.md): validator-only executable, user workflow, and examples.
- [`POLOPT.md`](./POLOPT.md): optimizer pipeline, examples, proof boundary, benchmark behavior, and testing workflow.
- [`doc/VERIFIED_PIPELINE.md`](./doc/VERIFIED_PIPELINE.md): concise explanation of the current verified affine+tiling pipeline, fallback behavior, and the main normalization stages.
- [`syntax/README.md`](./syntax/README.md): textual `.loop` syntax reference and authoring notes.
- [`tests/polopt-generated/README.md`](./tests/polopt-generated/README.md): generated strict-suite inputs, outputs, and how to inspect changes.
- [`doc/`](./doc): additional design notes and analysis.

## Project structure

Main mechanized development is in:

- [`src`](./src): extractor, validator stack, polyhedral semantics, strengthening, point-witness layer, prepare-codegen bridge
- [`polygen`](./polygen): verified code generation and verified cleanup passes
- [`driver`](./driver): top-level optimizer definitions and wrappers
- [`syntax`](./syntax): loop frontend used by `polopt`
- [`tests`](./tests): Pluto suite, generated `polopt` suite, scripts

## Paper

The paper of this mechanization is published at Springer:
<https://link.springer.com/chapter/10.1007/978-3-031-64626-3_17>

<details>
<summary>BibTeX</summary>

```bibtex
@inproceedings{li2024verified,
  title={Verified Validation for Affine Scheduling in Polyhedral Compilation},
  author={Li, Xuyang and Liang, Hongjin and Feng, Xinyu},
  booktitle={Theoretical Aspects of Software Engineering},
  pages={287--305},
  year={2024},
  publisher={Springer}
}
```

</details>

## License

See [LICENSE](./LICENSE).
