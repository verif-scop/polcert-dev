# Proof Build and Compiler Tests

Start with these files:

- `test-overview.md`: the main test groups, case counts, and purpose;
- `proof-report.md`: whether any Rocq proof is unfinished or missing;
- `tested-configurations.md`: supported command-line configurations and the
  tests that exercise them;
- `tiling-tests.json`: a short result summary for the tiling configurations;
- `run-results.json`: every recorded command, its result, duration, and raw
  output path.

Detailed command output and generated intermediate files are under
`raw-output/`. That directory also contains the short
`typed-c-pipeline.stdout.txt` excerpt from remote CI.
