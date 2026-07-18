# Reproduction Timing

This note records expected wall-clock time for the lock-v1 State.eq artifact.
The authoritative machine-readable values are in
`evidence/lock-v1-full-review.json`; this document explains how to use them.

## Recorded Baseline

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

Reviewers should reserve 45 minutes for a comparable serial full review. The
margin covers Docker filesystem and host-load variation. Image construction is
separate and may require network access; its duration is not included because
it depends on local layer caches and package mirrors.

## Known Long Tail

`advect3d` took 148.8 seconds in the lock-v1 review and 150.8 seconds in the
preceding exact-tag baseline. The close repeat is useful for planning. Existing
stage profiling identifies the verified `CodeGen.codegen` path as the dominant
cost; Pluto and the affine/tiling validators are not the bottleneck. This is a
compile-time performance caveat, not a semantic failure or an unchecked
fallback.

The next slow strict cases in the recorded run were `tce` (59.6 seconds),
`fdtd-2d` (33.6 seconds), `pca` (19.3 seconds), and `adi` (17.7 seconds). These
per-case values are retained in the raw strict-suite stdout bound by the
schema-v2 result-tree digest.

## Parallel Runs

The 33.3-minute figure is not a parallel-build result. A future `-j4` or
`-j$(nproc)` review may reduce proof-build time, but much of the nested suite is
made of sequential compiler invocations and includes the `advect3d` long tail.
Do not quote a parallel estimate until it has been measured with a fresh result
directory and archived alongside its job count and host CPU allocation.
