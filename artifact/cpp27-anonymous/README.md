# PolCert Supplementary Material

PolCert checks polyhedral loop transformations and generates code only after
the required checks succeed. Its main theorem covers the complete path from a
source loop to the generated sequential or parallel loop.

Start with [`docs/index.html`](docs/index.html). It provides four reading paths:

- [`docs/compiler.html`](docs/compiler.html): compiler pipeline and supported transformations;
- [`docs/proof.html`](docs/proof.html): main theorem, proof structure, and source pointers;
- [`docs/evaluation.html`](docs/evaluation.html): all tests, program executions, rejections, and performance;
- [`docs/reproduce.html`](docs/reproduce.html): build commands, test modes, and expected running times.

The complete test inventory is
[`evidence/results/test-catalog.html`](evidence/results/test-catalog.html).

To serve the documentation locally:

```sh
python3 -m http.server 8000 --bind 127.0.0.1
```

Then open <http://127.0.0.1:8000/docs/index.html>.

To rebuild the artifact and run the default checks:

```sh
docker build -f environment/Dockerfile -t polcert-artifact .
docker run --rm polcert-artifact
```

The archive contains the validated source snapshot under `source/`, generated
Rocq documentation under `docs/proof/`, pinned Pluto sources under
`third_party/pluto/`, and recorded results under `evidence/`.
