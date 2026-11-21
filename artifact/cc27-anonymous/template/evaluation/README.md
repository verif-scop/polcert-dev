# Evaluation Data

| Directory | Contents |
| --- | --- |
| `recorded/` | The recorded collection: paired retention records, per-case evidence archives, timing records and protocol, and the five recorded bugs. |
| `rerun/` | Every Table 1 pair rerun on the submitted source with the fixed Pluto snapshot, the index-set splitting collection, the build and test logs, and the scripts that compute the table. |
| `timing-rerun/` | Compilation-time measurements of the submitted source (Table 2 candidate; see `TABLE2.md`). |

## Table 1: optimization retention

Each row counts distinct sources for which Pluto produces the named effect
(`Pluto`) and those whose PolCert output retains it (`Retained`), using the
counting rule in `rerun/iss-supplement-summary.json` (`counting_rule`).

| Row | Pluto | Retained | Inputs |
| --- | --- | --- | --- |
| Affine scheduling | 48 | 48 | 66 |
| Index-set splitting | 11 | 11 | 11 sources × 5 configurations |
| Rectangular tiling | 55 | 55 | 66 |
| Two-level tiling | 45 | 45 | 66 (7 without a Pluto baseline) |
| Diamond tiling | 7 | 7 | 66 + 3 diamond examples |
| Parallelization | 57 | 51 | 66 |

The 66 inputs are the 62 kernels of `source/tests/polopt-generated/inputs/`
and four regression programs (`triple-nodep`, `diamond-example-inner-batch`,
`jacobi-batch`, `symbolic-independent-2d`). The diamond row adds
`diamond-tile-example`, `heat-3d-imperfect` and `jacobi-2d`. Pluto splits none
of the 66 inputs. The index-set splitting row uses Pluto's splitting tests: a
reversal kernel and two matrix variants of it, seven periodic stencils
rewritten with an explicit phase coordinate, and a two-dimensional
bidirectional kernel (`source/tests/iss-native/README.md`).

How the numbers are obtained:

- The recorded collection reviewed the optimization effect of every pair
  (`recorded/retention-records.json`).
- `rerun/` reran all 414 pairs of the five primary cohorts on the submitted
  source. Every pair reproduces PolCert's return code and final loop, so the
  recorded effect reviews apply unchanged (`rerun/table1.json`,
  `changed_pairs` is empty). The six parallelization losses occur in loop
  generation.
- The index-set splitting row is a fresh collection
  (`rerun/iss-supplement-summary.json`, 55 of 55 pairs retained).

Rerun a cohort inside the image with
`evaluation-data retention --cohort <name> --output <dir>`; cohort manifests
are in `source/evaluation/manifests/`.

## Table 2: compilation overhead

See `TABLE2.md`.
