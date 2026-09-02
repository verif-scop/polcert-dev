# Generated End-to-End Checks

This suite performs the same executable check across the generated loop
corpus. It builds complete C programs from the baseline and optimized loops,
compiles both, and compares their results.

Focused tests for parallel loops, two-level tiling, and optimization inside a
tile also check that the requested transformation occurred. Results are under
`evidence/execution-comparisons/`.

Run the default suite with:

```sh
opam exec -- make test-end-to-end-generated-smoke
```

Run the recorded performance configuration with:

```sh
opam exec -- make test-end-to-end-generated-perf
```

The selected route for each kernel is in `best_pipelines.json`; exact recorded
parameters and results are under `evidence/performance-comparisons/`.

The generated C wrappers are tests, not part of the theorem. These comparisons
use positive division operands. Diamond cases with negative operands are
covered by the verified compiler tests instead.
