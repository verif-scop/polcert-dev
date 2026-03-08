# Remaining 9 Strict-Path Failures

Date: 2026-03-07

Scope:
- strict proved-path `polopt`
- after the importer fixes that restored `validate(extracted, roundtrip-before) = true` across the generated suite

Current failing set:
- `corcol`
- `corcol3`
- `covcol`
- `dct`
- `jacobi-1d-imper`
- `jacobi-2d-imper`
- `pca`
- `ssymm`
- `tricky1`

For all nine:
- `validate(extracted, extracted) = true`
- `validate(extracted, roundtrip-before) = true`
- the failure is only on `validate(extracted, scheduled)`

So the remaining problem is no longer source roundtrip.
It is the mismatch between:
- the source polyhedral model we feed to Pluto from the `.loop` path
- and the source polyhedral model Clan/Pluto gets from the original C benchmark

## Case-by-case comparison

### `corcol`
- C-path source scop and `.loop`-path source scop are both `NE` under `polcert`.
- Domain rows per statement:
  - ours: `[2, 4, 6, 4]`
  - C path: `[3, 5, 8, 5]`
- Scattering rows per statement:
  - ours: `[3, 7, 11, 7]`
  - C path: `[3, 5, 7, 5]`
- Interpretation:
  - our source domain is weaker
  - our source schedule skeleton has extra constant slots in the multi-statement parts

### `corcol3`
- C-path source scop and `.loop`-path source scop are `NE`.
- Domain rows per statement:
  - ours: `[2, 4, 2, 2, 4, 2, 2, 2]`
  - C path: `[3, 6, 3, 3, 6, 3, 3, 3]`
- Scattering rows per statement:
  - ours: `[3, 7, 3, 5, 9, 5, 5, 5]`
  - C path: `[3, 5, 3, 3, 5, 3, 3, 3]`
- Interpretation:
  - same two problems as `corcol`, but more severe
  - source schedule skeleton is visibly inflated by inserted constant slots

### `covcol`
- C-path source scop and `.loop`-path source scop are `NE`.
- Domain rows per statement:
  - ours: `[6, 4]`
  - C path: `[8, 5]`
- Scattering rows per statement:
  - ours: `[7, 5]`
  - C path: `[7, 5]`
- Interpretation:
  - source scattering skeleton is already aligned
  - the remaining source mismatch is mainly domain weakness
  - the missing rows are parameter-only guards like `M-1 >= 0` and `N-1 >= 0`

### `dct`
- C-path source scop and `.loop`-path source scop are `NE`.
- Domain rows per statement:
  - ours: `[4, 6, 4, 6, 4]`
  - C path: `[5, 7, 5, 7, 5]`
- Scattering rows per statement:
  - ours: `[5, 9, 7, 11, 7]`
  - C path: `[5, 7, 5, 7, 5]`
- Interpretation:
  - weaker source domain
  - extra constant slots in the source schedule skeleton

### `jacobi-1d-imper`
- C-path source scop and `.loop`-path source scop are `NE`.
- Domain rows per statement:
  - ours: `[4, 4]`
  - C path: `[6, 6]`
- Scattering rows per statement:
  - ours: `[5, 7]`
  - C path: `[5, 5]`
- Interpretation:
  - the source domain is weaker
  - the source schedule skeleton for the second statement has one extra constant slot
  - C path also carries parameter guards such as `T-1 >= 0` and `N-4 >= 0`

### `jacobi-2d-imper`
- C-path source scop and `.loop`-path source scop are `NE`.
- Domain rows per statement:
  - ours: `[6, 6]`
  - C path: `[8, 8]`
- Scattering rows per statement:
  - ours: `[7, 9]`
  - C path: `[7, 7]`
- Interpretation:
  - same shape as `jacobi-1d-imper`
  - weaker source domain plus an inflated source schedule skeleton on the later statement

### `pca`
- C-path source scop and `.loop`-path source scop are `NE`.
- Domain rows per statement:
  - ours: `[2, 4, 2, 2, 4, 2, 2, 2, 4, 4, 4, 4, 2, 4, 6, 4]`
  - C path: `[3, 6, 3, 3, 6, 3, 3, 3, 6, 6, 6, 6, 3, 5, 8, 5]`
- Scattering rows per statement:
  - ours: `[3, 7, 3, 5, 9, 5, 5, 5, 7, 7, 7, 7, 5, 9, 13, 9]`
  - C path: `[3, 5, 3, 3, 5, 3, 3, 3, 5, 5, 5, 5, 3, 5, 7, 5]`
- Interpretation:
  - strongest example of both issues:
    - much weaker source domain
    - much larger source schedule skeleton

### `ssymm`
- C-path source scop and `.loop`-path source scop are `NE`.
- Domain rows per statement:
  - ours: `[6, 6, 4]`
  - C path: `[8, 8, 5]`
- Scattering rows per statement:
  - ours: `[7, 7, 5]`
  - C path: `[7, 7, 5]`
- Interpretation:
  - source schedule skeleton is already aligned
  - source domain is weaker
  - this is in the same family as `covcol`, but with more statements

### `tricky1`
- C-path source scop and `.loop`-path source scop are `NE`.
- Domain rows per statement:
  - ours: `[4, 4]`
  - C path: `[5, 5]`
- Scattering rows per statement:
  - ours: `[5, 5]`
  - C path: `[5, 5]`
- Interpretation:
  - cleanest remaining case
  - source scattering skeleton already matches
  - mismatch is only the weaker source domain
  - the missing row is the standalone parameter guard `N-1 >= 0`

## Current classification

### Mostly weaker source domain
- `covcol`
- `ssymm`
- `tricky1`

### Weaker source domain plus source schedule skeleton mismatch
- `corcol`
- `corcol3`
- `dct`
- `jacobi-1d-imper`
- `jacobi-2d-imper`
- `pca`

## Working hypothesis

There are two remaining gaps between the `.loop` path and the C/Clan path:

1. `to_openscop` still exports a source domain that is weaker than the one Clan emits.
   The strongest symptom is missing parameter-only guards that encode non-emptiness conditions.

2. For multi-statement imperfect-nest kernels, the `.loop` path still chooses a different source schedule skeleton than the one Clan emits.
   The strongest symptom is extra constant rows in the source scattering.

## Next fixes to investigate

1. Domain strengthening:
   export parameter-only guards that Clan/OpenScop emits for the same source loop bounds.

2. Source schedule skeleton alignment:
   inspect how the `.loop` frontend and extractor shape statement order for imperfect nests,
   especially on:
   - `jacobi-1d-imper`
   - `jacobi-2d-imper`
   - `corcol`
   - `corcol3`
   - `dct`
   - `pca`
