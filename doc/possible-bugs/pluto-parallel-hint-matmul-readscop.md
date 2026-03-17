# Pluto `--parallel` Hint May Be Unsound On `--readscop` Tiled `matmul`

## Status

This is not yet a confirmed Pluto bug, but it is a strong candidate.

PolCert currently treats Pluto parallel metadata as an untrusted hint, and this
case is a concrete reason why.

## Short Version

For the tiled `matmul` pipeline driven by two `pluto --readscop` calls,
Pluto marks the outer tiled `K/32` loop as parallel (`t1` in `<loop>`), and
the generated C also emits `#pragma omp parallel for` on that loop.

PolCert's checked parallel validator rejects that dimension and instead accepts
the next tiled `N/32` loop. The frontend therefore falls back to a different
dimension unless `--parallel-strict` is used.

## Why This Looks Suspicious

In the tiled schedule

```text
T(S1): ($i2/32, $i1/32, $i0/32, $i2, $i1, $i0)
```

the first tile dimension corresponds to `K/32`.

Different `K`-tiles contribute to the same output element `C[i][j]`, so this
dimension should not be treated as an ordinary doall-parallel loop. In the
generated loop nest, different iterations of the outer `t1` loop update the
same `C[t6][t5]`.

That is exactly why PolCert rejects current dimension `0` on this case.

## Reproducer

Run the normal PolCert frontend:

```sh
./polopt --parallel tests/polopt-generated/inputs/matmul.loop
```

Observed result:

```text
== Optimized Loop ==
context(M, N, K);

if ((1 <= M && (1 <= N && 1 <= K))) {
  for i0 in range(0, ((K + 31) / 32)) {
    parallel for i1 in range(0, ((N + 31) / 32)) {
      ...
    }
  }
}

[alarm] optimization triggered a checked fallback or warning
```

With debug output:

```sh
POLCERT_DEBUG_PARALLEL_HINT=1 ./polopt --parallel tests/polopt-generated/inputs/matmul.loop
```

Observed debug lines:

```text
[debug-parallel] Pluto hint iterator=t1 current_dim=0
[debug-parallel] current-dim 0: rejected(ok=true,msg=Parallel validation failed)
[debug-parallel] current-dim 1: accepted(ok=true)
[debug-parallel] checked_parallelize_current dim=0 => rejected(ok=true,msg=Parallel validation failed)
[debug-parallel] checked_parallelize_current dim=1 => accepted(ok=true)
[debug-parallel] checked_annotated_codegen dim=1 => accepted(ok=true)
```

So the pipeline behavior is:

1. Pluto hints `t1`
2. PolCert rejects hinted dim `0`
3. PolCert falls back to dim `1`
4. The frontend emits an alarm because the hinted dimension was not used

## Direct Pluto Reproducer

The behavior can be reproduced by mirroring the PolCert phase-aligned Pluto
pipeline:

1. export the extracted OpenScop
2. run affine scheduling without tiling
3. feed the affine result back into Pluto with `--readscop --identity --tile --parallel`

Representative commands:

```sh
./polopt --dump-extracted-openscop tests/polopt-generated/inputs/matmul.loop > /tmp/matmul.before.scop

pluto --dumpscop --readscop \
  --nointratileopt --nodiamond-tile --noprevector --smartfuse \
  --nounrolljam --noparallel --notile --rar \
  /tmp/matmul.before.scop

cp matmul.before.scop.afterscheduling.scop matmul.mid.scop

pluto --dumpscop --readscop \
  --identity --tile --nointratileopt --nodiamond-tile \
  --noprevector --nounrolljam --parallel --rar \
  matmul.mid.scop
```

Pluto reports:

```text
[pluto] Number of deps: 0
[Pluto] After tiling:
T(S1): ($i2/32, $i1/32, $i0/32, $i2, $i1, $i0)
```

And the raw `matmul.mid.scop.afterscheduling.scop` contains:

```text
<scatnames>
t1 t2 t3 t4 t5 t6
</scatnames>

<loop>
# Number of loops
1
# ===========================================
# Loop number 1
# Iterator name
t1
# Number of stmts
1
# Statement identifiers
1
# Private variables
t2,t3,t4,t5,t6
# Directive
1
</loop>
```

The generated C also places OpenMP parallelism on `t1`:

```c
#pragma omp parallel for private(lbv,ubv,t2,t3,t4,t5,t6)
for (t1=lbp;t1<=ubp;t1++) {
  ...
}
```

## Current PolCert Mitigation

PolCert does not trust Pluto `<loop>` extensions as certified facts.

Instead:

1. Pluto `--parallel` is treated as a search hint only
2. PolCert re-checks the hinted current dimension with
   `checked_parallelize_current`
3. only a checked-successful dimension is emitted as verified `parallel for`
4. by default, if the hinted dimension fails, the frontend may fall back to a
   different certified dimension
5. with `--parallel-strict`, the frontend keeps the sequential optimized loop
   unless the hinted dimension itself is certified

## Working Hypotheses

There are at least three plausible explanations:

1. Pluto's `--readscop` tiled path is dropping or weakening dependences in this
   case
2. Pluto's `<loop>` directive has a weaker intended meaning than "ordinary
   doall-parallel loop", and PolCert is using the safer interpretation
3. the particular dependence model in Pluto under this pipeline is not handling
   accumulation into `C[i][j]` conservatively enough

The debug line

```text
[pluto] Number of deps: 0
```

on the second `--readscop` call makes (1) or (3) especially plausible.

## Follow-Up

Before filing an upstream issue or PR against Pluto, do the following:

1. shrink this to the smallest possible OpenScop reproducer
2. check whether the same wrong parallel marking appears without `--readscop`
3. inspect Pluto's dependence reconstruction on the tiled second phase
4. verify whether Pluto intentionally treats this case as legal due to a
   different semantic assumption
5. if still reproducible and unsound, file an issue with:
   - the two-stage command sequence
   - the raw `<loop>` extension
   - the generated pragma placement
   - a short explanation of why `t1` updates overlapping `C[i][j]`
