# Standalone Storage-Transformation Validation Experiments

This directory is deliberately outside PolOpt/RCoq.  The goal is to make each
semantic transformation class concrete with:

- a small C-like source fragment;
- a hand-written optimized target fragment;
- a lightweight Python validator that checks the shape of the required witness.

Run:

```bash
python3 experiments/storage-validation-standalone/run.py
python3 experiments/storage-validation-standalone/run.py --negative
python3 experiments/storage-validation-standalone/run.py --case scalar_privatization_expansion --show-code
python3 experiments/storage-validation-standalone/run.py --dump-cases experiments/storage-validation-standalone/cases
python3 experiments/storage-validation-standalone/run.py --dump-report experiments/storage-validation-standalone/REPORT.md
```

The validators are intentionally small exhaustive checks over finite parameter
instances.  They are not proof-producing validators.  They are meant to clarify
which validation primitive each optimization needs before deciding what belongs
in a mechanized PolCert extension.

For the canonical terminology used by these examples, see:

- `../../doc/STORAGE_AWARE_VALIDATION_OVERVIEW.md`
- `../../doc/POLYHEDRAL_TRANSFORMATION_TAXONOMY.md`
- `PRIMITIVES.md`
- `VALIDATOR_CORRECTNESS.md`

The primitive names in `PRIMITIVES.md` are the canonical names for this package:
P7 means version selection and commit, P8 means reduction merge, and P9 means
phase separation.  Older notes that split commit exactness into a separate P8
should be treated as stale.

## Current Cases

| Case | Semantic Difference | Main Validation Primitive |
| --- | --- | --- |
| `source_no_alias_abstraction` | source names interpreted as distinct blocks | no-alias memory abstraction |
| `affine_interchange` | same instances, same storage, different order | instance bijection plus dependence preservation |
| `index_set_splitting` | same instances split across subdomains | disjoint exact-cover projection |
| `ordinary_tiling` | same instances grouped into tiles | tile projection exact cover |
| `scalar_privatization_expansion` | scalar cell becomes per-iteration storage | private freshness and use-def containment |
| `layout_remap_padding` | logical cells remap to physical addresses | injective/in-bounds address map |
| `scratchpad_packing` | values copied through tile-local buffer | copy-in coverage and local freshness |
| `scratchpad_copy_out` | local update committed back to global storage | copy-in/compute/copy-out protocol |
| `scalar_promotion` | array cell simulated by scalar | entry load, local simulation, exit store |
| `array_contraction` | logical values share physical cells | non-injective map guarded by live-range conflicts |
| `inter_array_reuse` | different arrays share one buffer over time | cross-array lifetime separation |
| `array_expansion_versioning` | one logical array gets more physical versions | version selection plus copy-out |
| `overlapped_tiling` | target computes duplicate halo instances | projection, internal invisibility, unique commit |
| `reduction_privatization` | private partial reductions plus merge | partition cover, fresh locals, associative merge |
| `double_buffering` | two buffers implement logical time dimension | phase separation and swap projection |

`REPORT.md` is generated from the current validators.  It includes both passing
case obligations and intentional invalid witnesses that the validators reject.
Current generated snippets are under `cases/` as 30 source/target files.

`VALIDATOR_CORRECTNESS.md` separates the executable experiments from the
soundness theorems a theorem-bearing validator would need.

## Reading the Results

A passing case means the standalone validator found the expected witness for the
chosen finite parameters.  For example:

- `ordinary_tiling` validates that tile loops project to every source instance
  exactly once.
- `scalar_privatization_expansion` validates that every `tmp_exp[i]` read is
  dominated by the matching write and that expanded cells are not observable.
- `array_contraction` validates that two logical values mapped to the same
  rolling-buffer cell do not have overlapping live ranges.
- `overlapped_tiling` validates that duplicated halo computations are internal,
  while every source output has exactly one committing target instance.

These cases separate three proof shapes that the current schedule-only
validator does not need:

1. target-to-source projection is not necessarily bijective;
2. storage access functions may change;
3. logical values may be expanded, contracted, copied, or privately committed
   before they become observable.

## How to Extend

Add a new `@add_case(...)` block in `run.py` with:

1. the source C-like fragment;
2. the optimized target fragment;
3. a validator that returns the obligations it checked.

The validator should make the witness explicit.  For instance, overlap needs a
target-to-source projection plus a `commit/internal` role; contraction needs a
non-injective storage map plus a conflict relation; copy-mediated transforms need
a copy-in/copy-out coverage relation.
