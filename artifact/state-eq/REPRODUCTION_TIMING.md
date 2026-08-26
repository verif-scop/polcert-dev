# Reproduction Timing

This note records the completed v9 measurement and retains the measured v3 and
v2 baselines. Authoritative values come only from schema-v2 evidence generated
from an untouched raw review directory.

## Reviewed v9 Measurement

The 2026-08-26 review ran immutable image
`sha256:554ee8822bf7eca53e76b537e1e8f999787b1824a6b060d2e953dccf9b3476fc`
with Docker networking disabled. The 13 outer gates and all 29 nested checks
passed. Both the outer review and nested builds were serial (`make_jobs=1`).

| Scope | Time |
|---|---:|
| Full 13-gate review | 5,173.2 s (86.2 min) |
| Clean Coq proof build | 1,396.8 s (23.3 min) |
| Extraction | 1,473.2 s (24.6 min) |
| `polopt` build | 81.1 s |
| `polcert` build | 1.5 s |
| Core regression | 52.1 s |
| Nested 29-check artifact run | 2,153.0 s (35.9 min) |
| Strict 62-case loop suite | 252.7 s (4.2 min) |
| `advect3d` strict case | 80.0 s (1.3 min) |

Nested rows overlap with the full review and must not be summed. Extraction
rebuilt nearly the complete proof dependency graph after the clean proof gate,
so it took slightly longer than proof checking itself. This is the main
remaining build-time optimization opportunity; it does not weaken the review.

The compact record is `evidence/2026-08-26-v9-full-review.json`; its SHA-256 is
`80b7ed282e622ca8ff844eba899f9c70c4a8853195ea9753247fb66ed90389ec`.
It binds a 2,069-file, 6,777,749-byte raw result tree with SHA-256
`3ea78f4bc97822cd33d51cb05885aa76ad7a5c2d86016cb5793e24be335b2a42`.
Image construction was separate and is not included.

## Exact v9 Remote CI Measurement

The exact v9 source commit completed GitHub Actions run
[`32958239151`](https://github.com/Hughshine/PolCert/actions/runs/32958239151)
in 46 minutes 17 seconds. The clean proof build took 997 seconds, extraction
152 seconds, `polcert` 27 seconds, and `polopt` 21 seconds. The seven test
shards completed within a 21-minute-32-second critical window.

This is not artifact review evidence. The CI constructs a shared image and
runs seven independent jobs, whereas the artifact review executes one exact
candidate image with Docker networking disabled and produces a bound raw
result tree. The CI timing therefore establishes that the source commit passes
the project workflow on a GitHub-hosted runner; it does not replace the
schema-v2 artifact record above.

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
This is a historical v3 measurement. Image construction was separate, required
network access, and was not included.

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

This older run is neither a v3 nor v9 measurement and should not be used as the
current review budget.

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

The 86.2-minute v9, 75.5-minute v3, and 33.3-minute v2 reviews are all serial.
A future measured v9 `-j4` or `-j$(nproc)` review may reduce proof-build time,
but much of the nested suite consists of sequential compiler invocations. Do
not quote a parallel estimate until it has been measured with a fresh result
directory and archived alongside its job count and host CPU allocation.
