# OpenScop Runtime Alignment

Date: 2026-03-06

## Scope

This note records the runtime issue that showed up after the proof work was closed:

- `polcert` must validate Pluto `before/after` scop pairs
- `polopt` must run the final proved pipeline exposed by `driver/PolOpt.v`
- Current code state:
  - `driver/PolOpt.v` is the canonical place to read the verified optimizer
  - `driver/PolOptPrepared.v` is only a compatibility wrapper
- `covcol` is the concrete regression-driving example

The proof layer was not the blocker. The problem lived in the extracted runtime representation.

## Final Diagnosis

There were two separate runtime bugs.

### 1. Generic extractor bug

`Extractor` was storing access functions with:

- `normalize_access_list_rev`

while validator expects the extracted access lists to stay in the instruction-argument space and only applies `pi_transformation` later.

Fix:

- `src/Extractor.v`
- change extracted `pi_waccess/pi_raccess` to use:
  - `normalize_access_list`

Effect:

- official `CInstr` validation/test line recovered
- `CSample2/covcol` went back to `SUCCEED`
- `make test` returned to green

### 2. Syntax-only checker lag

After fixing extractor access normalization, the `syntax` frontend still failed on:

- `validate(extracted, extracted)`

Decomposing validator showed:

- `wf = true`
- `eqdom = true`
- `res = true`
- `valid_access = false`

So the remaining failure was not schedule/dependence logic. It was `SInstr.access_function_checker`.

The reason was simple:

- `SInstr` raw access functions are sparse / minimal-length
- extractor now normalizes them with plain `resize`
- `syntax/SInstr.v` checker only accepted:
  - raw access
  - reverse-normalized access

Fix:

- extend `syntax/SInstr.v` checker to also accept:
  - plain normalized access

Effect:

- `validate(extracted, extracted) = true`
- `validate(extracted, roundtrip-before) = true`
- `validate(extracted, scheduled) = true`

on `covcol`

## What Did Not Need To Change

- no proof theorem changed
- no `PrepareCodegen` proof changed
- no validator algorithm changed
- no Pluto parameter change was needed

The remaining `OpenScop` parser/exporter work in `src/PolyLang.v` is still relevant for Pluto compatibility, but it was not the last blocker for raw `polopt` validation on `covcol`.

## Runtime Architecture After The Fix

`polcert`:

- still uses `from_openscop_complete`

`polopt`:

- is back on the single-object path
- `syntax/SPolOpt.v` now uses:
  - `opt = CoreOpt.Opt`
  - `opt_poly = CoreOpt.scheduler' ; Prepare.prepared_codegen`

So the temporary split workaround:

- validate normalized view
- codegen raw view

is no longer needed for `covcol`.

## Verified / Runtime Status

Current status in container `gifted_curie:/polcert`:

- `check-admitted`: `Nothing admitted.`
- `make test`: green
- `./polopt --debug-scheduler /tmp/covcol.loop`:
  - `validate(extracted, extracted) = true`
  - `validate(extracted, roundtrip-before) = true`
  - `validate(extracted, scheduled) = true`
- `./polopt /tmp/covcol.loop` produces optimized output

## Practical Lesson

Do not mix these two questions:

1. OpenScop schedule/scattering compatibility
2. extractor/validator access-coordinate contract

The last `covcol` blocker turned out to be the second one.
