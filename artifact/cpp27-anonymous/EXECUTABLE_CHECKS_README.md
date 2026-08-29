# Generated Executable Checks

These records compare each generated optimized C program with the generated
baseline for the same `.loop` input.

- `results.json` contains 62 default-corpus comparisons and five additional
  effect-focused runs for parallel, second-level tiling, and intra-tile routes.
- `validation.log` contains the corresponding concise per-case results.

The 62 default comparisons establish executable agreement for the full strict
input corpus. The additional runs require both executable agreement and the
requested structural effect. These runtime checks complement, but do not
replace, the Rocq refinement theorem.
