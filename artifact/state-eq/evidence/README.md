# Recorded Artifact Evidence

`2026-07-18-full-review.json` is the compact, checked-in summary of the first
offline full review of the frozen State.eq image.

The original run directory is intentionally local-only. It contains 2,038
files and about 12 MiB of logs, generated programs, suite summaries, and Pluto
dumps. The artifact-local `.gitignore` excludes `results*/` so those files
cannot enter the repository accidentally.

The compact summary records:

- exact source tag object, commit, tree, and archive SHA-256;
- base, source, and final image identities;
- toolchain versions and the offline network contract;
- every top-level reviewer gate and its elapsed time;
- proof-report counts and the main capability-suite counts;
- remaining dependency-lock and frozen-Dockerfile warning boundaries.

The local full result bundle remains at
`artifact/state-eq/results-full-20260718/`. It should be archived externally
with the published image rather than committed to this control repository.

## Lock-v1 Evidence

The existing file uses schema-v1 and remains the publication evidence for the
pre-lock reviewed image only. The lock-v1 candidate must use schema-v2 evidence
created by `bin/archive_full_review.py`; copying this file and changing an image
ID is intentionally rejected.

Schema-v2 is generated from an untouched raw result directory. It requires the
exact 13 outer gates in order, including `dependency-lock` first, and preserves
the existing zero-proof-hole, 18/18 artifact-check, 114 compatibility-check,
62/62 strict-suite, and named suite assertions. It binds the candidate image
reference and ID, build metadata, dependency lock SHA-256, every static input
copied into the result bundle, selected structured result files, and a complete
raw-directory tree digest.

Use `make archive-full-review` once after the full run, then
`make review-evidence-validate` against the same raw directory. Both commands
fail closed; the create command refuses to overwrite an existing evidence
file. The raw directory remains local-only and should be packaged externally
without changing its contents.
