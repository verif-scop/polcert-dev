# Example: two hypotheses, end to end

Run inside the PolCert development image from a built PolCert tree, with the
historical Pluto snapshot (`PLUTO_ROOT` default). Programs are in `examples/`.

## Hypothesis 1: the unroll-and-jam remainder reads a stale iterator

Audit: `tool/pluto_codegen_if.c` marks loops parallel and then unroll-jams
them. The remainder loop continues from the loop iterator, which OpenMP makes
private, so its value after the parallel loop is unspecified. Expected
symptom: wrong under OpenMP even with one thread, right without OpenMP.

```sh
POLOPT_FLAGS="--tile --parallel --diamond-tile --intratileopt --unrolljam --noprevector" \
  scripts/check_program.sh examples/unrolljam_remainder.loop
# unrolljam_remainder PLUTO-BUG reference pluto=wrong:openmp-one-thread; PolCert's output is correct
```

Pluto runs with its default flags, which include `--prevector`. `polopt`
refuses `--prevector` with `--parallel`, so PolCert gets the same flags
without it and serves as the reference. Refinement: with `--noprevector` for
Pluto too, the class is `OK`, so the defect needs the vectorization rewrite of
the jammed loop.

## Hypothesis 2: diamond tiling completes the schedule inconsistently

Audit: after the concurrent-start hyperplanes are found, the remaining rows
are completed per statement, and the result is not checked against the
dependences. Two fused statements can then break ties differently. Expected
symptom: wrong sequential result for a two-statement stencil with small tiles.

```sh
TILE_SIZES=examples/tile4.sizes scripts/check_program.sh examples/diamond_jacobi1d.loop \
  --tile --diamond-tile --intratileopt --noprevector --nounrolljam --noparallel
# diamond_jacobi1d PLUTO-BUG validator pluto=wrong:sequential; Post-tiling affine validation failed.
```

The rejecting validator names the stage: the affine check after tiling, i.e.
the diamond schedule. Minimizing keeps two statements and two time steps.

Both defects also reproduce with plain `polycc` on upstream Pluto (the
development head and release 0.13.1).
