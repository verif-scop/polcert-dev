# Proof Build and Compiler Tests

Start with these files:

- `test-catalog.html`: every recorded test case, its expected result, the
  observed loop transformation, the actual result, and the supporting log;
- `test-catalog.json`: the same complete catalog in machine-readable form;
- `proof-report.md`: whether any Rocq proof is unfinished or missing;
- `tested-configurations.md`: supported command-line configurations and the
  tests that exercise them;
- `tiling-tests.json`: a short result summary for the tiling configurations;
- `run-results.json`: every recorded command, its result, duration, and raw
  output path.

Detailed command output and generated intermediate files are under
`raw-output/`. `remote-ci-test-results.stdout.txt` contains the concise remote
CI phase and result lines used by the catalog.
