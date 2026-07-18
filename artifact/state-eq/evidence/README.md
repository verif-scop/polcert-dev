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
