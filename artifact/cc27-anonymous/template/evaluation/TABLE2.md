# Table 2: Compilation Time

The paper's Table 2 reports the measurement in `timing-rerun/`, taken with
the submitted source and the fixed Pluto snapshot.

**Setup.**
- 62 kernels of `source/tests/polopt-generated/inputs/`.
- Both compilers run a fixed configuration of affine scheduling, one-level
  rectangular tiling and parallelization.
- Each compiler runs each kernel three times end to end; the median is
  reported.
- The stage breakdown comes from one additional profiled PolCert run per
  kernel.

**Machine.** Intel Xeon Platinum 8275CL at 3.0 GHz, eight cores.
`timing-rerun/load.log` records the one-minute load average during the run.

## Table 2a: end-to-end wall time (s)

δ is PolCert's additional time over Pluto. P95 is the 95th percentile.

| Wall time | Mean | Median | P95 | Max |
| --- | ---: | ---: | ---: | ---: |
| Pluto | 0.192 | 0.092 | 0.997 | 1.427 |
| PolCert | 10.606 | 1.480 | 57.175 | 184.829 |
| δ | 10.414 | 1.403 | 56.571 | 183.402 |

- 46 of the 62 kernels incur less than 5 s of additional time.
- Ten exceed 10 s.
- The maximum, 183.40 s, is `advect3d`.

## Table 2b: one profiled PolCert run per kernel (s)

| Stage | Mean | Max |
| --- | ---: | ---: |
| Pluto | 0.392 | 2.946 |
| V_aff (in F_aff) | 0.325 | 3.365 |
| V_aff (in F_post) | 2.511 | 45.071 |
| V_tile | 1.128 | 26.113 |
| V_par | 0.978 | 11.953 |
| F_gen | 5.212 | 168.192 |
| Others | 0.003 | 0.008 |

Loop generation and post-tiling affine validation account for 76.0% of the
profiled PolCert time excluding Pluto.

**Files.**
- `timing-rerun/timing-results.json`: summary statistics and the largest
  cases.
- `timing-rerun/timing-cases.csv`: per-kernel times.
- `timing-rerun/run-metadata.json`: commands, environment and the profiled
  breakdown.
- `timing-rerun/load.log`: host load during the run.

Rerun inside the image, without concurrent load:
`evaluation-data timing --output <dir>`.

## Historical measurement (not the reported table)

`recorded/timing-records.json`, `recorded/timing-protocol.json`,
`recorded/timing.csv` and `recorded/stages.csv` are an earlier measurement of
the same protocol. It was taken in 2026-09 with an earlier build of PolCert,
on a desktop AMD Ryzen 7 7800X3D in an Ubuntu 20.04 container under WSL2.

The paper does not report it. PolCert's outputs are identical in both
measurements for all 62 kernels; the times differ with the processor.
