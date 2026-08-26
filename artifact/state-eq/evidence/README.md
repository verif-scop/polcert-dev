# Recorded Artifact Evidence

`2026-07-18-full-review.json`, `lock-v1-full-review.json`, and
`2026-07-21-v3-full-review.json` are historical records. The first two
authenticate the v2 dependency-lock origin and earlier wrapper; the third is
the completed v3 review. None is review evidence for the v9 source tag or
candidate image.

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

## Historical v3 Evidence

`2026-07-21-v3-full-review.json` is the schema-v2 record for the reviewed v3
candidate. Its source and image identities remain immutable historical
evidence, but they do not satisfy the v9 manifest or claim ledger.

## Current v9 Evidence

`2026-08-26-v9-full-review.json` is the validated schema-v2 record for the full
network-disabled review of
`polcert-artifact:state-eq-2026-08-26-v9-candidate`. Its SHA-256 is
`80b7ed282e622ca8ff844eba899f9c70c4a8853195ea9753247fb66ed90389ec`, and it
binds artifact image ID
`sha256:554ee8822bf7eca53e76b537e1e8f999787b1824a6b060d2e953dccf9b3476fc`.

Schema-v2 is generated from an untouched raw result directory. For v9 it must
establish the exact 13 outer gates in order, including `dependency-lock` first,
and the zero-proof-hole, 29/29 artifact-check, 81-row capability-surface,
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

The v9 raw result tree contains 2,069 files and 6,777,749 bytes; its SHA-256
tree digest is
`3ea78f4bc97822cd33d51cb05885aa76ad7a5c2d86016cb5793e24be335b2a42`.
The recorded serial wall times are 5,173.2 seconds total, 1,396.8 seconds for
the clean proof build, 1,473.2 seconds for extraction, 2,153.0 seconds for the
nested artifact check, 252.7 seconds for the strict suite, and 80.0 seconds for
`advect3d`. These are observed values, not performance guarantees.

This record makes the matching local image eligible for the guarded publication
step. It does not assert that any registry push has occurred; publication must
still bind an immutable repository digest to this exact image and raw result
tree.
