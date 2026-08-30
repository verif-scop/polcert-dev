# Proof Build Environment

`Dockerfile.proof` records the operating system, OCaml, Rocq/Coq, and package
versions used to build the proofs and extracted compiler. From the archive
root, run:

```sh
docker build -f environment/Dockerfile.proof -t polcert-proof .
```

The build requires network access and an x86-64 Docker environment.

The image configures the source, builds all proofs, checks for unfinished
proofs, and extracts the compiler. It does not require Pluto because the
external optimizer is not needed to check the proofs.

Recorded optimizer and executable tests are under `evidence/`. Running those
tests again requires Pluto.
