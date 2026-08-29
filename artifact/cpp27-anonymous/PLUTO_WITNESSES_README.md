# Candidate-Validation Witnesses

These seven cases exercise checked boundaries with unsafe or malformed
optimizer output. They do not all reject the whole compilation: a checked
route may reject only the unsafe annotation or jam and retain a certified
sequential result.

| Case | Boundary exercised | Recorded outcome |
| --- | --- | --- |
| `auto-affine-lp-cc-scaling` | Affine schedule | Illegal automatic schedule rejected. |
| `affine-fst-reversed` | Affine schedule | Deliberately reversed producer/consumer schedule rejected. |
| `tiling-innerpar-satvec` | Tiling plus parallel overlay | Legal tiling retained; unsafe parallel overlay removed or rejected. |
| `diamond-nointratile-reschedule` | Diamond tiling | Malformed mixed-scalar candidate rejected. |
| `matmul-parallel-hint` | Parallel dimension | Unsafe hinted dimension rejected. |
| `vanished-outer-parallel` | Parallel annotation | Dependence-carrying replacement dimension rejected. |
| `notile-unrolljam-nonpermutable` | Unroll-and-jam | Unroll retained; unsafe jam rejected. |

The archive records structured statuses in
`evidence/pluto-bug-witnesses/witness-results.json` and concise producer,
numerical, and checked-pipeline results in the adjacent `validation.log`. Case
directories contain inputs and detailed notes; shared runners are collected
under `runners/`, with the matmul runner also beside its input.
