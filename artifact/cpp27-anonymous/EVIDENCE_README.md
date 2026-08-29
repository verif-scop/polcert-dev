# Proof and Test Results

This directory contains the results used to check the proof build and compiler
behavior. Choose the question you want to answer:

- **Did all proofs build without unfinished proofs?**
  Read `proof-and-test-results/proof-report.md`.
- **Which compiler features were tested?**
  Read `proof-and-test-results/tested-configurations.md`.
- **What loops did the optimizer produce?**
  Open `optimized-loop-examples/index.html` for 62 before-and-after examples.
- **Did the original and optimized programs return the same result?**
  Read `execution-comparisons/results.json`.
- **Does PolCert reject invalid optimizer output?**
  Read `rejected-optimizer-outputs/README.md` and its `results.json`.

`summary.json` provides a short machine-readable overview. The complete command
record is `proof-and-test-results/run-results.json`; files ending in
`.stdout.txt` or `.stderr.txt` under `proof-and-test-results/raw-output/`
contain the corresponding raw output.

These results support the paper's correctness and test-coverage claims. They
do not claim a performance improvement.
