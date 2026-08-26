# PolCert Syntax Frontend

Use this skill when working on the isolated `syntax/` frontend for PolCert.

## Scope
- The real git repo is inside container `gifted_curie:/polcert`.
- The `syntax/` subtree is experimental and should stay isolated from the old validator driver.
- `polopt` currently links to `syntax/SLoopMain.ml`.

## Fast path
- Build proof/extraction: `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make -s proof && opam exec -- make -s extraction'`
- Build frontend binary: `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make polopt'`
- Stable smoke run: `docker exec gifted_curie sh -lc 'cd /polcert && ./polopt --extract-only syntax/examples/matadd.loop'`

## Important conventions
- `Loop` semantic env order and `SInstr` slot order are different.
- `Loop` expressions use the true semantic env order.
- `SInstr` variables use `context ++ outer-to-inner iterators`.
- The frontend must synthesize `Loop.Instr ... es` to bridge those orders.
- The pretty-printer must substitute `es` back through `instr`; do not print `instr` as if slots were identity.

## Current status
- `polopt` now defaults to the strict proved path again:
  - `syntax/SPolOpt.v: opt = CoreOpt.Opt`
- The old CLI fallback is gone.
- The generated `.loop` suite currently passes `45 / 62` on the strict path.

## `SInstr` semantics
- `syntax/SInstr.v` no longer uses an empty semantics.
- It now has a lightweight but meaningful store model:
  - `State.t := MemCell -> Z`
  - `SSkip` preserves state
  - `SAssign` writes one `MemCell` with the evaluated RHS
- This keeps the frontend simple while making:
  - `access_function_checker_correct`
  - `bc_condition_implie_permutbility`
  non-vacuous.

## Debug recipe
- Generate frontend scop: `./polopt --extract-only syntax/examples/matadd.loop > /tmp/frontend.scop`
- Pluto reference: create a small `#pragma scop` C file and run `pluto --dumpscop ...`
- Compare with `/tmp/*.beforescheduling.scop`, especially:
  - domain rows
  - scattering padding
  - statement extensions
  - array extensions

## 2026-03-06 Lessons
- Do not assume `polcert` self-validation implies Pluto compatibility.
  - The decisive frontend/OpenScop gap was scattering shape, not domain rows.
- `src/PolyLang.v` now needs dual-format support:
  - emit padded Pluto-style scattering
  - parse both padded and compact scattering back
- `syntax/SInstr.v` access checking must accept both raw and normalized access forms.
  - extractor calls the checker on raw `waccess/raccess`
  - validator calls it later on normalized access lists stored in `pi_waccess/pi_raccess`
- `syntax/SLoopElab.ml` variable lookup must use raw env order compatible with extractor normalization:
  - `inner-to-outer loops ++ reversed params`
  - using source-order params will silently swap parameter columns in emitted domains/accesses

## 2026-03-07 Lessons
- Keep CLI behavior on the strict proved path unless you are explicitly doing runtime diagnosis.
- The decisive generic extractor fix was:
  - `normalize_access_list_rev` -> `normalize_access_list`
  - for extracted access lists in `src/Extractor.v`
- `syntax/SInstr.v` should model real reads/writes even if it stays much simpler than `CInstr`.
- The remaining strict-path failures are not proof breakage.
  - They are source-model / scheduler-boundary fidelity issues.
