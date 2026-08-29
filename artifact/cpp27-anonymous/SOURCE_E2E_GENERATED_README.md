# Generated End-to-End Checks

This suite performs the same executable check for each of 62 loop inputs. It
builds complete C programs from the baseline and optimized loops, compiles
both, and compares their results.

The standard test covers all 62 cases. Five focused tests for parallel loops,
two-level tiling, and optimization inside a tile also check that the requested
transformation occurred. Results are under `evidence/execution-comparisons/`.

Run the default suite with:

```sh
opam exec -- make test-end-to-end-generated-smoke
```

The generated C wrappers are tests, not part of the theorem. These comparisons
use positive division operands. Diamond cases with negative operands are
covered by the verified compiler tests instead.
