# Table 2: Compilation Time

<!-- TABLE2-SELECTION: replace this section with the record set that the paper's Table 2 reports. -->
This section names the record set behind the paper's Table 2.

Two record sets are available. Both use the 62 kernels of
`source/tests/polopt-generated/inputs/`, a fixed configuration of affine
scheduling, one-level rectangular tiling and parallelization for both
compilers, three end-to-end runs per compiler and kernel (median reported),
and one profiled run per kernel for the stage breakdown.

| Record set | Machine | Files |
| --- | --- | --- |
| Recorded collection | Desktop AMD Ryzen 7 7800X3D, Ubuntu 20.04 container under WSL2 | `recorded/timing-records.json`, `recorded/timing-protocol.json`, `recorded/stages.csv`, `recorded/timing.csv` |
| Rerun on the submitted source | Intel Xeon Platinum 8275CL @ 3.00 GHz, 8 pinned cores, Docker | `timing-rerun/timing-results.json`, `timing-rerun/timing-cases.csv`, `timing-rerun/run-metadata.json`, `timing-rerun/load.log` |

PolCert's outputs are identical in both record sets for all 62 kernels; the
times differ with the processor.

Rerun inside the image, without concurrent load, with
`evaluation-data timing --output <dir>`.
