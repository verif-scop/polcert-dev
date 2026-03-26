# PolCert `--parallel` Tile Phase Needed `--innerpar` To Stay Phase-Aligned

## Status

This is a confirmed PolCert integration bug.

It is not a new Pluto upstream bug.

The issue was reproduced in Docker on 2026-03-26 and fixed in
`driver/Scheduler.ml` by adding `--innerpar` to the tile-stage
`--parallel` Pluto invocation.

## Short Version

PolCert's phase-aligned parallel route used this tile-stage Pluto command
shape:

```text
pluto --readscop --identity --tile ... --parallel
```

On `matmul`, Pluto's default tiled `--parallel` path produced a skewed /
wavefront tile schedule rather than the canonical strip-mined tiled order that
PolCert's current tiling witness and validator expect.

So the checked path failed at:

```text
[debug-parallel] phase tiling validate=false(ok=true)
```

and the frontend fell back to the sequential optimized loop.

Adding `--innerpar` keeps the tiled schedule canonical enough for the current
phase-aligned witness:

```text
pluto --readscop --identity --tile ... --parallel --innerpar
```

After that change, the same `matmul --parallel` case passes checked tiling and
emits verified `parallel for`.

## What Was Wrong

PolCert currently reconstructs a canonical tiled-after program from the
tiling witness extracted between `mid_affine` and `after_tiled`:

- `build_canonical_tiled_after_spol`
- `checked_tiling_validate`

That witness shape matches ordinary strip-mined tiling.

But Pluto's default tile-stage `--parallel` path is allowed to do more than
ordinary strip-mining. On this case it performs a tile-scheduling step and
skews the outer tile dimensions into a wavefront-style order.

For the `matmul` phase-2 input, the direct Pluto output changed from the
canonical first tile dimension

```text
fk0
```

to the skewed first tile dimension

```text
fk0 + fk1
```

which showed up in the raw scheduled OpenScop as:

```text
## c1 == fk0+fk1
```

That output is not wrong for Pluto's own semantics, but it is outside the
current PolCert phase-aligned ordinary-tiling witness story.

## Why This Is Not The Same As The Earlier Pluto `readscop` Bug

This was investigated only after fixing the older Pluto `compute_deps_osl`
`--readscop` bug.

After that earlier fix, Pluto no longer miscomputed dependences or mislabeled
the parallel hint on this path. The remaining failure was different:

- affine phase validation succeeded
- the tile-phase witness was extractable
- but the checked tiling gate failed because the scheduled result had become a
  wavefront/skewed tiled order

So this second issue is a PolCert-side configuration mismatch, not another
Pluto parser / dependence reconstruction defect.

## Minimal Reproducer

In Docker, first get the affine-only phase result:

```sh
./polopt --dump-scheduled-openscop --notile tests/end-to-end-c/cases/matmul/matmul.loop > /tmp/matmul.mid.scop
```

Then compare Pluto's tile-stage behavior with and without `--innerpar`:

```sh
pluto --dumpscop --readscop \
  --identity --tile --nointratileopt --nodiamond-tile \
  --noprevector --nounrolljam --parallel --rar \
  /tmp/matmul.mid.scop

pluto --dumpscop --readscop \
  --identity --tile --nointratileopt --nodiamond-tile \
  --noprevector --nounrolljam --parallel --innerpar --rar \
  /tmp/matmul.mid.scop
```

Observed behavior:

- default `--parallel`:
  - Pluto reports `After tile scheduling`
  - the scheduled relation contains `fk0+fk1`
  - PolCert's phase-aligned checked tiling route rejects it
- `--parallel --innerpar`:
  - the tile schedule stays canonical
  - PolCert accepts the phase-aligned tiling witness
  - PolCert emits verified `parallel for`

## PolCert Symptom Before The Fix

```sh
POLCERT_DEBUG_PARALLEL_HINT=1 ./polopt --parallel tests/end-to-end-c/cases/matmul/matmul.loop
```

Observed debug summary before the fix:

```text
[debug-parallel] Pluto hint iterator=t2 current_dim=1
[debug-parallel] phase affine validate=true(ok=true)
[debug-parallel] phase tiling validate=false(ok=true)
[alarm] optimization triggered a checked fallback or warning
```

The frontend then returned the sequential optimized loop.

## Fix

Changed:

- `driver/Scheduler.ml`

Specifically, `tile_only_parallel_flags` now includes:

```text
--innerpar
```

This keeps the tile-stage `--parallel` Pluto run in the "pure inner parallel"
mode instead of the default pipelined / wavefront-oriented mode.

## Regression Coverage Added

To make this easy to re-check, the whole-C harness now supports:

- extra `polopt` arguments via `--polopt-arg`
- a `--require-parallelized` assertion

and the Makefile now exposes:

```sh
make test-end-to-end-c-matmul-parallel
```

This target checks that:

- `polopt --parallel` on the handwritten `matmul` wrapper really emits
  `parallel for`
- the optimized whole C program still matches the baseline output

## Post-Fix Validation

The fix was validated in Docker with:

```sh
./polopt --parallel tests/end-to-end-c/cases/matmul/matmul.loop
./polopt --parallel --parallel-strict tests/end-to-end-c/cases/matmul/matmul.loop
make test-end-to-end-c-matmul-parallel
```

Observed results after the fix:

- both frontend commands emit `parallel for i1 ...`
- debug output shows:
  - `phase affine validate=true(ok=true)`
  - `phase tiling validate=true(ok=true)`
  - `checked_tiling_validate=true(ok=true)`
- the new regression target passes with:
  - `parallelized_loop=true`
  - `exact_match=true`

## Takeaway

This is a good example of the verified validator being useful even when Pluto
itself is behaving as designed.

Pluto's default tiled `--parallel` mode is richer than PolCert's current
ordinary phase-aligned tiling witness. The checked validator exposed that
mismatch immediately instead of silently accepting a schedule transformation it
does not currently justify.
