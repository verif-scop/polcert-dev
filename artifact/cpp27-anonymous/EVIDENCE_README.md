# Evidence

- `proof-and-test-results/proof-report.md`: compiler-route and extracted-axiom
  closure inventory.
- `proof-and-test-results/test-catalog.html`: tests grouped by transformation
  and purpose, with expected results, observed transformations, and evidence.
- `rejected-optimizer-outputs/index.html`: unsafe or non-certifiable effects
  and PolCert's response.
- `optimized-loop-examples/index.html`: source and optimized loop programs.
- `execution-comparisons/results.json`: executable source/target comparisons.

Machine-readable records are in `summary.json` and
`proof-and-test-results/{test-catalog.json,run-results.json}`. Raw command
output is under `proof-and-test-results/raw-output/`; the complete proof and
extraction build is recorded in `remote-ci-test-results.stdout.txt` there.
