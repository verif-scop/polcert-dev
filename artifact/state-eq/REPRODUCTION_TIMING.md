# Reproduction Timing

This note records the measured v3 review and retains the historical v2 planning
baseline for comparison. Authoritative v3 values come from schema-v2 evidence
generated from the untouched raw review directory.

## Reviewed v3 Measurement

The 2026-07-21 review ran the immutable image
`sha256:38d1df0a35de3fa9e2f5af9b925c8978564e1731cd095caca94c3f3eeba5e304`
with Docker networking disabled. Both the outer review and nested builds were
serial (`make_jobs=1`); no parallel make was requested.

| Scope | Time |
|---|---:|
| Full 13-gate review | 4,531.8 s (75.5 min) |
| Clean Coq proof build | 1,447.0 s (24.1 min) |
| Extraction | 93.9 s |
| `polopt` build | 73.1 s |
| Core regression | 51.6 s |
| Nested 22-check artifact run | 2,838.0 s (47.3 min) |
| Strict 62-case loop suite | 585.5 s (9.8 min) |
| `advect3d` strict case | 80.2 s (1.3 min) |

Nested rows overlap with the full review and must not be summed. The compact
record is `evidence/2026-07-21-v3-full-review.json`; its SHA-256 is
`c4a0d4607cfa774f0754d18a45cad95bb19e6bc3ac9236ce8e602a5df6a37f54`.
Reviewers should reserve at least 90 minutes on a comparable host. Image
construction is separate, requires network access, and is not included.

## Historical v2 Baseline

The 2026-07-18 full review used
`polcert-artifact:state-eq-lock-v1-candidate` with Docker networking disabled.
The runner invoked `make` without `-j`, the image did not set `MAKEFLAGS`, and
the observed build was serial.

| Scope | Time |
|---|---:|
| Full 13-gate review | 1,996.4 s (33.3 min) |
| Clean Coq proof build | 748.8 s (12.5 min) |
| Extraction | 25.3 s |
| `polopt` build | 53.5 s |
| Core regression | 50.2 s |
| Nested 18-check artifact run | 1,097.0 s (18.3 min) |
| Strict 62-case loop suite | 355.4 s (5.9 min) |
| `advect3d` strict case | 148.8 s (2.5 min) |

This older run is not a v3 measurement and should not be used as the current
review budget.

## Known Long Tail

`advect3d` took 80.2 seconds in the reviewed v3 image, compared with 148.8
seconds in the lock-v1 review and 150.8 seconds in the preceding exact-tag
baseline. Existing stage profiling identifies the verified `CodeGen.codegen`
path as the dominant cost; Pluto and the affine/tiling validators are not the
bottleneck. This is a compile-time performance caveat, not a semantic failure
or an unchecked fallback.

The next slow strict cases in the recorded run were `tce` (59.6 seconds),
`fdtd-2d` (33.6 seconds), `pca` (19.3 seconds), and `adi` (17.7 seconds). These
per-case values are retained in the historical raw strict-suite stdout bound by
the `lock-v1-full-review.json` schema-v2 result-tree digest.

## Parallel Runs

Neither the 75.5-minute v3 review nor the 33.3-minute historical review is a
parallel-build result. A future `-j4` or `-j$(nproc)` review may reduce
proof-build time, but much of the nested suite consists of sequential compiler
invocations. Do not quote a parallel estimate until it has been measured with
a fresh result directory and archived alongside its job count and host CPU
allocation.
