# Proof Build and Compiler Tests

- `test-catalog.html`: tests grouped by transformation and purpose.
- `test-catalog.json`: the same catalog in machine-readable form.
- `proof-report.md`: compiler-route and extracted-axiom closure inventory.
- `tested-configurations.md`: command-line options and their tests.
- `run-results.json`: local commands, status, duration, and output path.

Raw output and generated intermediates are under `raw-output/`.
`raw-output/remote-ci-test-results.stdout.txt` records the complete proof and
extraction build phases. `FORMAL_SOURCE_SHA256SUMS` at the archive root covers
every packaged Rocq source file.
