# Program Output Comparisons

These records run the baseline and optimized C programs generated from each
`.loop` input and compare their results.

- `results.json` records every comparison.
- `validation.log` contains the corresponding concise per-case results.

The records contain 62 baseline-versus-optimized comparisons and five checks
for parallel loops, two-level tiling, and optimization inside a tile. The five
additional checks also confirm that the requested optimization occurred. These
tests complement, but do not replace, the Rocq theorem.
