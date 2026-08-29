# Validation Evidence

This directory contains recorded results from the validated source snapshot.

Start with `validation-summary.json`, then inspect:

- `artifact-check/artifact-results.json` for the packaged record of all 30
  commands, statuses, and timings;
- `artifact-check/proof-report.md` for the proof inventory and main theorems;
- `artifact-check/capability-matrix.md` for tested configurations and options;
- `artifact-check/tiling-route-summary.json` for tiling results;
- `artifact-check/*.stdout.txt` and `*.stderr.txt` for raw per-check output;
- `transformation-examples/index.html` for each test input, optimized
  output, status, and diff;
- `executable-checks/results.json` for 62 baseline-vs-optimized executable
  comparisons and five additional effect-focused runs;
- `pluto-bug-witnesses/` for seven unsafe or malformed optimizer proposals and
  their expected rejection;
- `pluto-bug-witnesses/witness-results.json` and `validation.log` for the
  structured and concise results of all seven witnesses.

Paths in `artifact-results.json` are relative to `artifact-check/`. Its
`formal_source_hash_manifest_sha256` binds the run record to the formal-source
hash manifest at the archive root.

These results support the paper's correctness and test-coverage claims. They
do not claim a performance improvement.
