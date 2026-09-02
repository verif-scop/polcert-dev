# Program Output Comparisons

These records run the baseline and optimized C programs generated from each
`.loop` input and compare their results.

- `results.json` records every comparison.
- `validation.log` contains the corresponding concise per-case results.

This directory contains the generated-kernel campaign and focused checks for
parallel loops, two-level tiling, and optimization inside a tile. The focused
checks also confirm that the requested optimization occurred.

The complete test catalog extends this check to every saved, accepted
before/after Loop pair. Open `../results/test-catalog.html` to inspect the two
programs, their parameters and run count, and whether they produced the same
result. The generated execution records are under
`../results/program-executions/`.
