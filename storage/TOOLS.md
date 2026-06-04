# Storage Survey Tools

## External Tools Used

### Candl

Location in current environment:

```text
/pluto/candl
```

Used for:

- scalar expansion evidence with `-scalexp`;
- scalar privatization dependence metadata calibration with `-scalpriv`.

Important result:

- `-scalexp 1` changes scalar temporary `t` into indexed storage `t[i]` in
  OpenScop access metadata.
- `-scalpriv 1` marks a dependence as `RAW_SCALPRIV`, but does not by itself
  demonstrate a storage rewrite.

### Pluto

Location in current environment:

```text
/pluto
```

Used for:

- checking whether `--scalpriv` changes generated C on Candl's `scalpriv.c`
  unit input.

Important result:

- with and without `--scalpriv`, generated C is identical for the tested input;
- this is negative evidence against treating Pluto `--scalpriv` as a broad
  storage transformation pass in the current source.

## In-Repo Survey Tools

All generated survey summaries can be rebuilt from the repo root with:

```sh
make -C storage all
```

### `openscop_storage_diff.py`

```sh
python3 storage/tools/openscop_storage_diff.py BEFORE.scop AFTER.scop
```

Extracts:

- per-array access arity;
- access index relation rows;
- dependence count.

This is intentionally a small survey probe, not a full OpenScop parser.

### `toy_openscop_layout_remap.py`

```sh
python3 storage/tools/toy_openscop_layout_remap.py \
  storage/evidence/candl_scalexp0.scop \
  storage/evidence/toy_layout_remap_a_scale2.scop \
  --array a --scale 2
```

Rewrites a narrow one-dimensional OpenScop access relation from `[1] == i` to
`[1] == scale * i`.  This is toy tool-backed evidence for layout remapping as a
storage-view transformation.  It is not evidence that Pluto currently performs a
layout-remap pass.

### `toy_openscop_scratchpad.py`

```sh
python3 storage/tools/toy_openscop_scratchpad.py \
  --out-dir storage/evidence
```

Generates:

- `toy_scratchpad_packing_source.scop`;
- `toy_scratchpad_packing_target.scop`;
- `toy_scratchpad_copyout_source.scop`;
- `toy_scratchpad_copyout_target.scop`;
- `toy_scratchpad_witness.json`.

The packing skeleton has a copy-in cache: public `B[kk+k]` is copied to private
`Bp[k]`, and the public output `C[kk+k]` is computed from `A[kk+k]` and `Bp[k]`.

The copy-out skeleton has a private update boundary: public `A[kk+k]` is copied
to private `Al[k]`, updated locally, and then committed back to public
`A[kk+k]`.

This is toy OpenScop-level evidence for scratchpad boundary witnesses, not a
full OpenScop optimizer and not a Pluto-emitted pass.  OpenScop access
relations show reads and writes; the copy-in/copy-out roles are supplied by the
structured witness sidecar.

### `toy_openscop_reuse_folding.py`

```sh
python3 storage/tools/toy_openscop_reuse_folding.py \
  --out-dir storage/evidence
```

Generates OpenScop-shaped skeletons and a JSON witness for:

- `array_contraction`: logical `A[t][i]` represented by physical
  `A2[t mod 2][i]`;
- `inter_array_reuse`: logical `T1[i]` and `T2[i]` sharing private `Buf[i]` in
  disjoint phases;
- `double_buffering`: logical state represented by `Buf[cur/next][i]` under a
  phase projection.

Generated `.scop` files show folded/shared physical storage.  The correctness
facts that make non-injective reuse legal are in `toy_reuse_folding_witness.json`:
logical value ids, physical regions, valid intervals, producer/consumer events,
kill-or-reuse events, storage compatibility, and final boundary projection.
This is not evidence that Pluto currently emits these transformations.

### `toy_openscop_advanced_storage.py`

```sh
python3 storage/tools/toy_openscop_advanced_storage.py \
  --out-dir storage/evidence
```

Generates OpenScop-shaped skeletons and a JSON witness for:

- `array_expansion_versioning`: produced versions, read selectors, final
  selector, and copy-out/projection;
- `reduction_privatization`: chunk partition, private accumulators, merge tree,
  and operator laws;
- `overlapped_tiling`: duplicate computations, halo closure, commit set, and
  exact public-output cover;
- `storage_view_composition`: private-erasure stage, layout-projection stage,
  intermediate interface, and composed public output view.

The generated `.scop` files show access shape.  The roles and correctness
evidence are in `toy_advanced_storage_witness.json`: `statement_roles`,
`representation_witness`, `checked_obligations`, `negative_cases`, and endpoint
notes for each case.  This is not evidence that Pluto currently emits these
transformations.

### `toy_openscop_private_protocols.py`

```sh
python3 storage/tools/toy_openscop_private_protocols.py \
  --out-dir storage/evidence
```

Generates OpenScop-shaped skeletons and a JSON witness for:

- `private_copy_boundary`: copy-in/copy-out boundary pairs, private-cell
  declarations, compatibility, and commit coverage;
- `private_access_local_instantiation`: symbolic private access `local[f(i)]`,
  finite instantiation, declared private cells, and bounds;
- `scalar_promotion`: load/update/store-back protocol, scalar interval, public
  uses, and alias/clobber exclusion.

The generated `.scop` files show access shape only.  The correctness evidence is
in `toy_private_protocols_witness.json`: statement roles, storage declarations,
boundary protocols, representation witnesses, checked obligations, and negative
cases.  This is not evidence that Pluto currently emits these transformations.

### `toy_openscop_boundary_domain.py`

```sh
python3 storage/tools/toy_openscop_boundary_domain.py \
  --out-dir storage/evidence
```

Generates OpenScop-shaped skeletons and a JSON witness for:

- `source_no_alias_abstraction`: declared source footprints, no-alias logical
  blocks, and in-bounds accesses;
- `contextual_frame_preservation`: allowed writes, protected frame variables,
  frame snapshots, and private target storage;
- `index_set_splitting`: source domain, target subdomains, exact cover, and
  disjointness.

These are boundary/domain witnesses, not storage rewrites.  They are included so
the survey has an explicit artifact for every transformation/precondition entry.

### `summarize_standalone.py`

```sh
python3 storage/tools/summarize_standalone.py \
  storage/evidence/standalone_positive.log \
  storage/evidence/standalone_negative.log
```

Extracts:

- positive validation cases;
- obligation counts;
- rejected malformed witnesses grouped by transformation case.

### `build_example_catalog.py`

```sh
python3 storage/tools/build_example_catalog.py \
  --positive storage/evidence/standalone_positive.log \
  --negative storage/evidence/standalone_negative.log \
  --examples storage/examples/standalone
```

Generates `EXAMPLE_CATALOG.md` and `EXAMPLE_CATALOG.json` through
`make -C storage all`.  The catalog is the survey-level example sufficiency
check: for every transformation it lists the core source/target files, extra
positive or negative variants, standalone obligations, malformed-witness
negative checks, required witness fields, and evidence status.

The catalog is intentionally honest about weak spots.  For example, a case may
have several documented variants but still need stronger executable negative
coverage or real external-tool evidence.

## Standalone Validator

Location in container:

```text
/polcert-storage-generalization-20260507/experiments/storage-validation-standalone
```

Used for broad toy validation across storage transformations:

```sh
python3 experiments/storage-validation-standalone/run.py
python3 experiments/storage-validation-standalone/run.py --negative
```

Current saved evidence:

- 19 positive cases;
- 76 negative checks.

This is not an external optimizer.  It is an executable specification of what
storage witnesses should accept and reject.
