# Test Coverage Overview

The 62-loop corpus is one test group, not the whole test suite. The groups
below overlap, so their counts should not be added into one total.

| Test group | Recorded cases | What is checked |
| --- | ---: | --- |
| Driver configurations | 189 | Supported option combinations, expected rejections, and requested transformation effects. |
| Default loop corpus | 62 | End-to-end optimization and validation of a broad loop collection. |
| Two-level tiling | 58 | Two tiling levels combined with ISS, diamond tiling, and parallel-loop configurations. |
| One-level tiling layouts | 90 | 84 accepted layouts and 6 expected rejections, with no validation fallback. |
| Diamond tiling | 19 | Accepted diamond transformations and unsupported inputs that must be rejected. |
| Parallel eligibility checking | 21 | 9 general parallel-loop cases and 12 cases that reuse the check but require the innermost loop. |
| Index-set splitting | 10 | Valid splits, incomplete partitions, name collisions, and mutated invalid splits. |
| Unroll-and-jam corpus | 11 | Six cases where checked fusion occurs and five where it must not occur. |
| Generated execution comparisons | 67 | 62 original-versus-optimized comparisons and 5 focused transformation checks. |
| Typed C instruction pipelines | 6 | Ordinary and two-level tiling, ISS, diamond tiling with post-tiling rescheduling, parallel loops, and the innermost-restricted eligibility case. |
| Handwritten C harnesses | 10 packaged examples | C reference wrappers plus structured-loop kernels for ISS, tiling, parallel loops, strides, and unrolling; five focused cases are rerun in this validation record. |

The source also includes `samples/CSample1.v`, `CSample2.v`, and `CSample3.v`.
They instantiate the concrete C-like instruction semantics for matrix
multiplication, covariance, and GEMVER. `samples/CTypedLoopSamples.v` contains
smaller typed examples for the individual verified compiler components.
The six-case remote CI record is `raw-output/typed-c-pipeline.stdout.txt`.

`run-results.json` lists the complete local artifact-check command set. The
typed pipeline excerpt above comes from remote CI. This table summarizes the
reviewer-facing coverage rather than every unit test and packaging gate.
