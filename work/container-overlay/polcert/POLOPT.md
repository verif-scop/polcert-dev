# polopt

`polopt` is the loop-language optimizer frontend backed by the verified optimization core.
It is the closest thing in this repository to a Pluto counterpart: Pluto is still used as the untrusted scheduler, but extraction, schedule validation, schedule/domain strengthening, code generation, and post-codegen cleanup are all tied to Coq proofs.

## What it does

`polopt` takes a structured loop fragment, runs the verified polyhedral optimization core, and prints an optimized loop.
The scheduler is Pluto itself, so the optimization decisions come from Pluto;
the difference is that extraction, affine validation, checked tiling
validation, code generation, and cleanup are integrated into a proved pipeline.

At a high level:

```text
.loop text
-> parser / elaborator
-> Loop IR
-> Extractor.extractor
-> StrengthenDomain.strengthen_pprog
-> affine Pluto route with verified affine validation
-> if the phase-aligned tiling route succeeds:
   -> checked tiling validation
   -> current_view_pprog
-> otherwise:
   -> verified affine-only fallback
-> PrepareCodegen.prepare_codegen
-> CodeGen.codegen
-> verified cleanup passes
-> Loop IR
```

For a concise summary of the current verified pipeline shape and the role of
`current_view_pprog`, see:

- [doc/VERIFIED_PIPELINE.md](./doc/VERIFIED_PIPELINE.md)

## Pluto configuration used by `polopt`

`polopt` intentionally tracks the scheduling capability of Pluto under the same flag set used throughout this repository:

```sh
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
      --smartfuse --nounrolljam --noparallel --notile --rar
```

This matters because the current verified path is aimed at **checked
schedule/domain transformation and schedule-driven code generation**, not at the
full Pluto transformation space.
In particular, the current `polopt` path should be read as supporting the optimization capability that Pluto exposes **under exactly this flag set**:

- affine scheduling / loop reordering
- skewing / wavefront-style rescheduling
- statement reordering, fission, and related schedule effects
- schedule changes that stay within the validated affine-scheduling story

The current path does **not** claim support for the full Pluto transformation
space. It now includes the checked phase-aligned tiling route, but still does
not claim support for transformations such as:

- index-set splitting
- transformations whose correctness would require a stronger structural
  validator than the current checked affine+tiling path
- parallel code generation

## Main example: covariance (`covcol`)

Input `.loop`:

```text
context(M, N);

for j1 in range(1, (M + 1)) {
  for j2 in range(j1, (M + 1)) {
    for i in range(1, (N + 1)) {
      symmat[j1][j2] = (symmat[j1][j2] + (data[i][j1] * data[i][j2]));
    }
    symmat[j2][j1] = symmat[j1][j2];
  }
}
```

Current optimized output:

```text
context(M, N);

if ((1 <= N && 1 <= M)) {
  for i0 in range(1, (N + 1)) {
    for i1 in range(1, (M + 1)) {
      for i2 in range(i1, (M + 1)) {
        symmat[i1][i2] = (symmat[i1][i2] + (data[i0][i1] * data[i0][i2]));
      }
    }
  }
}
if (1 <= M) {
  for i0 in range(1, (M + 1)) {
    for i1 in range(i0, (M + 1)) {
      symmat[i1][i0] = symmat[i0][i1];
    }
  }
}
```

What changed:

- the accumulation statement and the symmetry-copy statement are split into separate phases
- the accumulation is reordered to run with `i` outermost
- this improves temporal locality for the accumulation phase and matches the Pluto-style optimization family for this kernel

In the previous evaluation for this kernel, with `M = N = 1500`, this transformation achieved about **4x speed-up** on our machine.

## Main tiling example: matrix multiply initialization (`matmul-init`)

Input `.loop`:

```text
context(N);

for i0 in range(0, N) {
  for i1 in range(0, N) {
    C[i0][i1] = 0;
    for i2 in range(0, N) {
      C[i0][i1] = (C[i0][i1] + (A[i0][i2] * B[i2][i1]));
    }
  }
}
```

Current optimized output:

```text
context(N);

if (1 <= N) {
  for i0 in range(0, ((N + 31) / 32)) {
    for i1 in range(0, ((N + 31) / 32)) {
      for i2 in range(max((32 * i0), 0), min(((32 * i0) + 32), N)) {
        for i3 in range(max((32 * i1), 0), min(((32 * i1) + 32), N)) {
          C[i2][i3] = 0;
        }
      }
    }
  }
}
if (1 <= N) {
  for i0 in range(0, ((N + 31) / 32)) {
    for i1 in range(0, ((N + 31) / 32)) {
      for i2 in range(0, ((N + 31) / 32)) {
        for i3 in range(max(0, (32 * i0)), min(N, ((32 * i0) + 32))) {
          for i4 in range(max(0, (32 * i1)), min(N, ((32 * i1) + 32))) {
            for i5 in range(max(0, (32 * i2)), min(N, ((32 * i2) + 32))) {
              C[i3][i4] = (C[i3][i4] + (A[i3][i5] * B[i5][i4]));
            }
          }
        }
      }
    }
  }
}
```

What changed:

- the output now contains explicit tile loops with tile size `32`
- the point-within-tile loops use `max/min` strip-mined bounds
- the initialization and accumulation phases are both tiled, not just rescheduled
- this is the visible shape that the strict suite now classifies as a detected tiled output

## What is proved

The final optimizer definition and theorem are in [driver/PolOpt.v](./driver/PolOpt.v):

- final optimizer: `Opt = Opt_prepared`
- final theorem: `Opt_correct`

The proved passes used by `Opt` are:

1. [src/Extractor.v](./src/Extractor.v)
   - `Extractor.extractor`
   - verified `Loop -> PolyLang` extraction
2. [src/StrengthenDomain.v](./src/StrengthenDomain.v)
   - `strengthen_pprog`
   - conservative strengthening of statement domains by implied parameter guards
3. [driver/PolOpt.v](./driver/PolOpt.v)
   - `checked_affine_schedule`
   - `phase_pipeline_opt_prepared_from_poly`
   - the final verified optimizer route, including checked affine scheduling,
     checked tiling validation, and verified fallback
4. [src/PrepareCodegen.v](./src/PrepareCodegen.v)
   - `prepare_codegen`
   - regularizes the validated program into the codegen-ready representation
5. [polygen/CodeGen.v](./polygen/CodeGen.v)
   - verified polyhedral code generation
6. verified post-codegen cleanup passes:
   - [polygen/LoopCleanup.v](./polygen/LoopCleanup.v)
   - [polygen/LoopSingletonCleanup.v](./polygen/LoopSingletonCleanup.v)

At a high level, `Opt_correct` states:

- if the verified optimizer returns an optimized loop
- and that optimized loop runs to a final state
- then the original input loop can also run to an equivalent final state

## What is not proved

The following remain engineering layers around the proved core:

- the textual `.loop` parser / elaborator
- OpenScop textual parsing / printing implementation details
- Pluto itself
- witness inference from Pluto phase outputs
- the final OCaml pretty-printer

## What inputs it supports

`polopt` reads the structured `.loop` syntax documented in [syntax/README.md](./syntax/README.md).
The current frontend supports:

- symbolic parameters via `context(...)`
- structured `for` loops with half-open bounds
- affine `if` guards
- scalar and array assignments
- arithmetic using `+`, `-`, `*`, `/`
- pure calls in RHS expressions
- ternary expressions in RHS expressions
- float literals in RHS expressions

Still intentionally restricted in affine positions (bounds, guards, indexes):

- non-affine multiplication
- general calls in affine bounds / guards / indexes
- non-affine ternaries in affine bounds / guards / indexes

## Assumptions and model boundary

The current `polopt` frontend works over the lightweight `SInstr` model rather than full CompCert C semantics.
That means:

- calls are treated as pure computations
- the frontend does not model realistic floating-point precision/rounding effects
- the instantiated instruction model still assumes the non-aliasing / compatibility conditions required by the verified core
- practical C-level issues such as overflow, aliasing, and full floating-point semantics remain separate integration work

So the right reading is:

- the optimizer uses **Pluto's optimization choices** under the flag set above
- the surrounding extraction / validation / code generation path has a formal correctness argument in the current loop-language model
- users should read current floating-point and overflow behavior under the current simplified model assumptions

## Benchmark behavior

The generated strict regression suite is under [tests/polopt-generated](./tests/polopt-generated).
Current strict proved-path status:

- total inputs: `62`
- succeeded: `62`
- changed: `60`
- unchanged: `2`
- nontrivially changed: `60`
- automatically detected tiled outputs: `38`

Interpretation:

- scheduling decisions come from Pluto itself
- the strict `polopt` path now succeeds on the full generated benchmark suite
- the stronger `nontrivial_changed` metric ignores only trivial loop-variable
  alpha-renaming and whole-program outer guard wrappers
- the `detected_tiled` metric is intentionally narrower than `changed`; it
  only counts outputs with explicit strip-mined tile structure
- across the suite, the resulting loop transformations follow the same optimization families as the corresponding C-path Pluto runs under the exact flag set shown above
- in that sense, `polopt` currently covers the checked affine route and the
  checked phase-aligned tiling route under the supported Pluto setup, with
  verified extraction / validation / code generation around them
- this should still not be read as support for the full Pluto transformation
  space: index-set splitting and parallel code generation remain out of scope

One practical exception is performance on `advect3d`:

- it succeeds semantically
- but `CodeGen.codegen` currently takes about `40s` on that case
- the slowdown is in code generation, not in parsing, Pluto, or validation

## How to run

Build with the standard sequence from [README.md](./README.md), then run:

```sh
./polopt file.loop
```

Useful modes:

```sh
./polopt --extract-only file.loop
./polopt --debug-scheduler file.loop
```

## How to write your own example

Start from a small structured loop fragment, for example:

```text
context(N, M);
for i in range(0, N) {
  for j in range(0, M) {
    C[i][j] = A[i][j] + B[i][j];
  }
}
```

Guidelines:

- use `context(...)` for symbolic parameters
- use half-open loop bounds `range(lb, ub)`
- keep bounds, guards, and indexes affine
- use calls/ternaries only in RHS expressions, not in affine control/index positions

## How to test

Full regression is already wired into CI through [tools/ci/run_ci.sh](./tools/ci/run_ci.sh).
Locally, the main commands are:

```sh
make clean
opam exec -- make depend
opam exec -- make proof
opam exec -- make -s check-admitted
opam exec -- make extraction
opam exec -- make polopt
opam exec -- make polcert.ini
opam exec -- make polcert
make test
opam exec -- make test-polopt-loop-suite
```

The generated per-case results live under:

- [tests/polopt-generated/cases](./tests/polopt-generated/cases)

The strict suite now reports progress case by case and uses a `300s` per-case
timeout instead of a suite-wide timeout, so slow kernels such as `advect3d` are
visible during the run instead of appearing to hang silently.

## Key source files

Compiler / CLI entry:
- [syntax/SLoopMain.ml](./syntax/SLoopMain.ml)

Frontend bridge to the verified optimizer:
- [syntax/SPolOpt.v](./syntax/SPolOpt.v)

Final optimizer definition and theorem:
- [driver/PolOpt.v](./driver/PolOpt.v)

Key passes:
- [src/Extractor.v](./src/Extractor.v)
- [src/StrengthenDomain.v](./src/StrengthenDomain.v)
- [src/PrepareCodegen.v](./src/PrepareCodegen.v)
- [polygen/CodeGen.v](./polygen/CodeGen.v)
- [polygen/LoopCleanup.v](./polygen/LoopCleanup.v)
- [polygen/LoopSingletonCleanup.v](./polygen/LoopSingletonCleanup.v)
