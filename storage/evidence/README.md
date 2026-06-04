# Storage Evidence

This directory stores small, reproducible evidence files for the storage survey.

## Candl Scalar Expansion

Source input:

```text
/pluto/candl/tests/unitary/scalexp.c.orig.scop
```

Reproduction commands inside the Pluto checkout:

```sh
./candl/candl -outscop -scalexp 0 -o /tmp/storage_scalexp0.scop \
  candl/tests/unitary/scalexp.c.orig.scop

./candl/candl -outscop -scalexp 1 -o /tmp/storage_scalexp1.scop \
  candl/tests/unitary/scalexp.c.orig.scop
```

Copied outputs:

- `candl_scalexp0.scop`: scalar expansion disabled;
- `candl_scalexp1.scop`: scalar expansion enabled.

Survey probe:

```sh
python3 storage/tools/openscop_storage_diff.py \
  storage/evidence/candl_scalexp0.scop \
  storage/evidence/candl_scalexp1.scop
```

Observed summary:

```text
t: 1D x4 -> 2D x4 changed
Dependence count: before 9, after 5
```

Interpretation:

- `t` is originally a scalar temporary access.
- With `-scalexp 1`, Candl rewrites `t` accesses to include the loop index,
  i.e. a per-iteration private storage dimension.
- This is concrete evidence for scalar expansion as a storage transformation.

Limit:

- This is Candl `-scalexp`, not Pluto `--scalpriv`.
- Pluto `--scalpriv` is related because Pluto forwards it to Candl
  `scalar_privatization`, but current Pluto does not expose the resulting
  storage rewrite as a checked PolOpt witness.

## Candl/Pluto Scalar Privatization Calibration

Candl scalar privatization can change dependence metadata without changing
storage access arity:

```sh
./candl/candl -outscop -scalpriv 0 -o /tmp/storage_scalpriv0.scop \
  candl/tests/unitary/scalpriv.c.orig.scop

./candl/candl -outscop -scalpriv 1 -o /tmp/storage_scalpriv1.scop \
  candl/tests/unitary/scalpriv.c.orig.scop
```

The copied files are:

- `candl_scalpriv0.scop`;
- `candl_scalpriv1.scop`;
- `candl_scalpriv_summary.txt`.

The summary shows no access-arity change and the same dependence count:

```text
a: 1D x2 -> 1D x2
b: 2D x1 -> 2D x1
Dependence count: before 3, after 3
```

The useful difference is in dependence type: `RAW` becomes
`RAW_SCALPRIV #(scalar priv)`.

Pluto was also run on Candl's `scalpriv.c` with and without `--scalpriv`:

```sh
/pluto/tool/pluto candl/tests/unitary/scalpriv.c \
  --candldep --scalpriv --parallel -o /tmp/storage_pluto_scalpriv.c

/pluto/tool/pluto candl/tests/unitary/scalpriv.c \
  --candldep --parallel -o /tmp/storage_pluto_no_scalpriv.c
```

The generated C files are identical in this case; the saved diff
`pluto_scalpriv_generated_c.diff` is empty.  This is negative evidence against
treating Pluto `--scalpriv` itself as a demonstrated storage rewrite.

## Toy OpenScop Layout Remap

The in-repo toy tool rewrites a simple OpenScop access relation:

```sh
python3 storage/tools/toy_openscop_layout_remap.py \
  storage/evidence/candl_scalexp0.scop \
  storage/evidence/toy_layout_remap_a_scale2.scop \
  --array a --scale 2
```

The summary is saved in `toy_layout_remap_summary.txt`.  It keeps the same
array arity but changes the affine index row for `a` from `[1] == i` to
`[1] == 2*i`.

Interpretation:

- this is evidence that layout remapping can be represented as an OpenScop
  access-function transformation;
- it is a toy transformation tool, not a Pluto-emitted pass;
- it calibrates the witness shape needed for logical public `A` to be
  represented by a different physical layout.

## Toy OpenScop Scratchpad Boundary

The in-repo toy tool generates two scratchpad-shaped OpenScop skeletons:

```sh
python3 storage/tools/toy_openscop_scratchpad.py \
  --out-dir storage/evidence
```

Generated files:

- `toy_scratchpad_packing_source.scop`;
- `toy_scratchpad_packing_target.scop`;
- `toy_scratchpad_copyout_source.scop`;
- `toy_scratchpad_copyout_target.scop`;
- `toy_scratchpad_witness.json`;
- `toy_scratchpad_packing_summary.txt`;
- `toy_scratchpad_copyout_summary.txt`.

Interpretation:

- `scratchpad_packing` copies a public live-in tile cell such as `B[kk+k]` to
  private `Bp[k]`, then computes the public output from the private cache.
- `scratchpad_copy_out` copies public `A[kk+k]` into private `Al[k]`, updates
  `Al[k]`, and commits it back to public `A[kk+k]`.
- scratchpad buffers are private target storage and are excluded from the final
  public logical view.
- OpenScop access relations encode reads and writes; copy-in/copy-out roles are
  supplied by the structured JSON witness sidecar.

Limits:

- This is a toy OpenScop-shaped generator, not evidence that Pluto emits
  scratchpad packing or copy-out transformations.
- The `.scop` skeleton is evidence for certificate shape only.  Soundness still
  requires checked validator obligations: local read coverage, copy-out live-out
  coverage, exact public commits, in-bounds local accesses, and guarded boundary
  tiles.

## Toy OpenScop Reuse and Folding

The in-repo toy tool generates OpenScop-shaped skeletons for storage reuse:

```sh
python3 storage/tools/toy_openscop_reuse_folding.py \
  --out-dir storage/evidence
```

Generated files:

- `toy_array_contraction_source.scop`;
- `toy_array_contraction_target.scop`;
- `toy_inter_array_reuse_source.scop`;
- `toy_inter_array_reuse_target.scop`;
- `toy_double_buffering_source.scop`;
- `toy_double_buffering_target.scop`;
- `toy_reuse_folding_witness.json`;
- `toy_array_contraction_summary.txt`;
- `toy_inter_array_reuse_summary.txt`;
- `toy_double_buffering_summary.txt`.

Interpretation:

- `array_contraction` folds logical time `A[t][i]` into physical
  `A2[t mod 2][i]`;
- `inter_array_reuse` maps logical `T1[i]` and `T2[i]` to shared private
  `Buf[i]` in disjoint phases;
- `double_buffering` maps logical state to `Buf[cur/next][i]` through an
  explicit phase projection.

Limits:

- OpenScop access relations show reads, writes, and physical storage names.
  They do not by themselves encode logical value ids, valid intervals,
  kill/reuse events, or final boundary projection.
- The JSON sidecar is the validator-facing artifact for reuse/folding
  obligations.
- Non-injective physical maps are accepted only when simultaneous-live logical
  values do not collide.
- Every target read must be tied to a still-valid producer; final value equality
  alone is not enough.
- This is toy OpenScop-shaped evidence, not evidence that Pluto emits these
  storage reuse transformations.

## Toy OpenScop Advanced Storage Witnesses

The in-repo toy tool generates OpenScop-shaped skeletons for the remaining
advanced storage families:

```sh
python3 storage/tools/toy_openscop_advanced_storage.py \
  --out-dir storage/evidence
```

Generated files:

- `toy_versioning_source.scop`;
- `toy_versioning_target.scop`;
- `toy_reduction_source.scop`;
- `toy_reduction_target.scop`;
- `toy_overlap_source.scop`;
- `toy_overlap_target.scop`;
- `toy_view_composition_source.scop`;
- `toy_view_composition_target.scop`;
- `toy_advanced_storage_witness.json`;
- `toy_versioning_summary.txt`;
- `toy_reduction_summary.txt`;
- `toy_overlap_summary.txt`;
- `toy_view_composition_summary.txt`.

Interpretation:

- `array_expansion_versioning` uses `X_exp[t][i]` as target version storage and
  a final selector from `X_exp[T-1][i]` to public `X[i]`;
- `reduction_privatization` uses private `local[p]` accumulators and a merge
  tree that commits to public `sum`;
- `overlapped_tiling` lets tiles compute duplicate halo values privately and
  only commits owner-tile outputs to public `B`;
- `storage_view_composition` composes private erasure with layout projection:
  target `tmp` is hidden and target `A_pad[2*i]` exports logical `A[i]`.

Limits:

- OpenScop access relations encode reads/writes/schedules only.  Statement
  roles, version selectors, merge trees, commit sets, and composition
  observables are supplied by the JSON sidecar.
- Private target versions, accumulators, halo buffers, and intermediate temps
  are excluded from final public observation unless explicitly exported.
- Final value equality alone is too weak; every target read contributing to a
  public output must be justified by produced-version, reduction contribution,
  halo closure, or composed-view evidence.
- This is toy OpenScop-shaped evidence, not evidence that Pluto emits these
  storage transformations.

## Toy OpenScop Private Protocols

The in-repo toy tool generates OpenScop-shaped skeletons for the remaining
private/protocol storage families:

```sh
python3 storage/tools/toy_openscop_private_protocols.py \
  --out-dir storage/evidence
```

Generated files:

- `toy_private_copy_boundary_source.scop`;
- `toy_private_copy_boundary_target.scop`;
- `toy_private_access_source.scop`;
- `toy_private_access_target.scop`;
- `toy_scalar_promotion_source.scop`;
- `toy_scalar_promotion_target.scop`;
- `toy_private_protocols_witness.json`;
- `toy_private_copy_boundary_summary.txt`;
- `toy_private_access_summary.txt`;
- `toy_scalar_promotion_summary.txt`.

Interpretation:

- `private_copy_boundary` uses explicit copy-in/copy-out pairs between public
  cells and private `local` cells;
- `private_access_local_instantiation` instantiates symbolic private access
  `local[f(i)]` into declared, in-bounds private cells;
- `scalar_promotion` represents public `A[i]` through private scalar `s`
  between load and store-back.

Limits:

- OpenScop access relations encode reads/writes/schedules only.  JSON supplies
  copy roles, private declarations, boundary pairs, scalar protocols, and
  alias/clobber exclusions.
- Private cells and scalars are excluded from final public observation unless
  explicitly copied or stored back.
- Alias/clobber exclusion is a real proof obligation, especially for scalar
  promotion.
- This is toy OpenScop-shaped evidence, not evidence that Pluto emits these
  transformations.

## Toy OpenScop Boundary and Domain Witnesses

The in-repo toy tool generates OpenScop-shaped skeletons for survey entries
that are preconditions or domain transformations rather than storage rewrites:

```sh
python3 storage/tools/toy_openscop_boundary_domain.py \
  --out-dir storage/evidence
```

Generated files:

- `toy_no_alias_source.scop`;
- `toy_no_alias_target.scop`;
- `toy_frame_source.scop`;
- `toy_frame_target.scop`;
- `toy_index_split_source.scop`;
- `toy_index_split_target.scop`;
- `toy_boundary_domain_witness.json`;
- `toy_no_alias_summary.txt`;
- `toy_frame_summary.txt`;
- `toy_index_split_summary.txt`.

Interpretation:

- `source_no_alias_abstraction` records source variable footprints and
  non-aliasing as validator preconditions;
- `contextual_frame_preservation` records protected context variables and the
  fragment allowed-write set;
- `index_set_splitting` records a disjoint exact cover of the source iteration
  domain.

Limits:

- These are not storage rewrites.  They are included because storage
  transformations depend on source-footprint, context-frame, and domain-cover
  boundaries.
- OpenScop access relations show the access/domain skeleton; JSON supplies the
  precondition or domain witness.

## Standalone Storage Validator Logs

The container checkout `/polcert-storage-generalization-20260507` contains a
standalone executable storage-validation prototype:

```sh
python3 experiments/storage-validation-standalone/run.py
python3 experiments/storage-validation-standalone/run.py --negative
```

Saved logs:

- `standalone_positive.log`;
- `standalone_negative.log`.

These logs cover positive and negative cases for many storage families:
scratchpad packing, copy-out, scalar promotion, array contraction, inter-array
reuse, array expansion/versioning, overlapped tiling, reduction privatization,
double buffering, layout remap, and storage-view composition.

Interpretation:

- This is broad validation-target evidence for the survey taxonomy.
- It is not evidence that Pluto currently emits all of these transformations.
- It is not a Coq soundness theorem.  It is a useful executable specification
  of what each witness family must accept and reject.
