# Candidate-Validation Witnesses

These seven cases give PolCert unsafe or malformed output from Pluto. Depending
on the configuration, PolCert either rejects compilation or drops only the
unsafe parallel or loop-fusion step and keeps a verified sequential result.

| Case | Boundary exercised | Recorded outcome |
| --- | --- | --- |
| `auto-affine-lp-cc-scaling` | Execution order | Illegal automatic schedule rejected. |
| `affine-fst-reversed` | Execution order | Deliberately reversed producer/consumer order rejected. |
| `tiling-innerpar-satvec` | Tiling plus parallel loop | Legal tiling retained; unsafe parallel annotation removed or rejected. |
| `diamond-nointratile-reschedule` | Diamond tiling | Invalid tiling schedule rejected. |
| `matmul-parallel-hint` | Parallel dimension | Unsafe hinted dimension rejected. |
| `vanished-outer-parallel` | Parallel loop | Unsafe replacement dimension rejected. |
| `notile-unrolljam-nonpermutable` | Unroll-and-jam | Unrolling retained; unsafe loop fusion rejected. |

The recorded outcomes are in `witness-results.json` and `validation.log`.
Each case directory contains its input and explanation; shared test runners
are under `runners/`.
