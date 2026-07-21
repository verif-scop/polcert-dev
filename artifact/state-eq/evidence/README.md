# Recorded Artifact Evidence

`2026-07-18-full-review.json` and `lock-v1-full-review.json` are historical v2
records. They authenticate the dependency-lock origin and the earlier wrapper;
they are not review evidence for the v3 source tag or candidate image.

The pre-lock origin run directory is intentionally local-only. It contains
2,038 files and about 12 MiB of logs, generated programs, suite summaries, and
Pluto dumps. The later lock-v1 schema-v2 record covers a different 2,045-file,
6,913,016-byte raw bundle. The artifact-local `.gitignore` excludes `results*/`
so those files cannot enter the repository accidentally.

The compact summary records:

- exact source tag object, commit, tree, and archive SHA-256;
- base, source, and final image identities;
- toolchain versions and the offline network contract;
- every top-level reviewer gate and its elapsed time;
- proof-report counts and the main capability-suite counts;
- remaining dependency-lock and frozen-Dockerfile warning boundaries.

The local full result bundle remains at
`artifact/state-eq/results-full-20260718/`. It should be archived externally
with the corresponding exported image if distributed, rather than committed to
this control repository.

## Historical v2 Evidence

`2026-07-18-full-review.json` uses schema-v1 and remains the review record for
the pre-lock dependency origin image. `lock-v1-full-review.json` is schema-v2
full-review evidence accepted by the publication guard for the separately
identified lock-v1 candidate; this does not assert that the image was pushed.
Copying either file and changing an image ID is rejected.

## Current v3 Evidence

The expected current record is `2026-07-21-v3-full-review.json`, generated only
after a fresh full network-disabled review of
`polcert-artifact:state-eq-2026-07-21-v3-candidate`. Until that file is produced
from the untouched raw results and validates against the candidate image ID,
the v3 image is not publication-eligible.

Schema-v2 is generated from an untouched raw result directory. For v3 it must
establish the exact 13 outer gates in order, including `dependency-lock` first,
and the zero-proof-hole, 22/22 artifact-check, 81-row capability-surface,
138 compatibility-check (112 success and 26 rejection expectation), 62/62
strict-suite, and named suite assertions. It binds the candidate image
reference and ID, build metadata, dependency lock SHA-256, every static input
copied into the result bundle, selected structured result files, and a complete
raw-directory tree digest. It also binds the SHA-256 of `claims.json` and the
independently recomputed `claim-evidence.json` report. Each claim must resolve
to passing routes and concrete result files in the full profile; a catalog
entry with a missing or obsolete route is rejected. A full run may mark the
extended-only ISS-live route unavailable, but that supplemental route must
still be recognized and every required full-profile reference must resolve.

Use `make archive-full-review` once after the full run, then
`make review-evidence-validate` against the same raw directory. Both commands
fail closed; the create command refuses to overwrite an existing evidence
file. The raw directory remains local-only and should be packaged externally
without changing its contents. Schema-v2 publication also requires this raw
directory and independently recomputes the compact evidence before any image
tag or push.

The v3 schema-v2 timing summary will be mechanically derived from its new raw
result tree. It records the make configuration, total review, proof-build,
artifact-check, and strict-suite times, and the `advect3d` long-tail case from
the 62-case stdout log. These are observed wall-clock values, not performance
guarantees.
