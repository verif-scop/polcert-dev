# Proof Build Environment

`Dockerfile.proof` fixes the operating-system base, OCaml switch, Rocq/Coq
version, and OCaml package versions used for the proof and extraction build.
From the extracted archive root, run:

```sh
docker build -f environment/Dockerfile.proof -t polcert-proof .
```

The image build runs `configure`, dependency generation, the clean proof build,
the admitted-proof scan, and extraction. It does not require Pluto because
optimizer search is outside the formal proof build.

The frozen optimizer-facing and executable tests are indexed under
`evidence/`; those tests additionally require the external Pluto toolchain.
