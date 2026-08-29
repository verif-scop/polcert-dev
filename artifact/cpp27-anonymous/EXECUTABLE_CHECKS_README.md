# Program Output Comparisons

These records run the baseline and optimized C programs generated from each
`.loop` input and compare their results.

- `results.json` contains 62 standard comparisons and five additional checks
  for parallel loops, two-level tiling, and optimization inside a tile.
- `validation.log` contains the corresponding concise per-case results.

The 62 standard comparisons check that baseline and optimized programs agree.
The five additional runs also check that the requested optimization occurred.
These tests complement, but do not replace, the Rocq theorem.
