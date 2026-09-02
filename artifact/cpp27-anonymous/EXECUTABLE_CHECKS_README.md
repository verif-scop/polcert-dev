# Program Output Comparisons

These records run the baseline and optimized C programs generated from each
`.loop` input and compare their results.

- `results.json` records every comparison.
- `validation.log` contains the corresponding concise per-case results.

This directory contains the original CI campaign: 62 generated kernels and
five focused checks for parallel loops, two-level tiling, and optimization
inside a tile. The focused checks also confirm that the requested optimization
occurred.

The complete test catalog extends this check to every saved, accepted
before/after Loop pair. Open `../results/test-catalog.html` to inspect the two
programs, the number of modeled state values hashed, and the digest comparison
result for each applicable test. The generated execution records are under
`../results/program-executions/`.

These tests check executable integration around the compiler. They complement,
but do not replace, the Rocq refinement theorem.
