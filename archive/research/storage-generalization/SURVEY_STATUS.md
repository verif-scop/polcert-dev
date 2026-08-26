# Storage Survey Status

Date: 2026-06-04

## Done

- Created a `storage/` survey workspace.
- Wrote a theorem-facing model centered on public variables rather than
  concrete `MemCell`s.
- Wrote an initial taxonomy covering:
  - scalar expansion / scalar privatization;
  - scalar promotion;
  - scratchpad and copy-in/copy-out;
  - layout remap and padding;
  - contraction, folding, and reuse;
  - inter-array reuse;
  - versioning and double buffering;
  - reduction privatization and merge;
  - overlap / halo / redundant computation.
- Added a small OpenScop probe:
  `storage/tools/openscop_storage_diff.py`.
- Ran Candl scalar-expansion evidence and saved:
  - `storage/evidence/candl_scalexp0.scop`;
  - `storage/evidence/candl_scalexp1.scop`;
  - `storage/evidence/candl_scalexp_summary.txt`.
- Ran Candl/Pluto scalar-privatization calibration and saved:
  - `storage/evidence/candl_scalpriv0.scop`;
  - `storage/evidence/candl_scalpriv1.scop`;
  - `storage/evidence/candl_scalpriv_summary.txt`;
  - `storage/evidence/pluto_no_scalpriv.c`;
  - `storage/evidence/pluto_scalpriv.c`;
  - `storage/evidence/pluto_scalpriv_generated_c.diff`.
- Ran the standalone storage-validation prototype and saved:
  - `storage/evidence/standalone_positive.log`;
  - `storage/evidence/standalone_negative.log`.
- Copied standalone C-like source/target examples into
  `storage/examples/standalone/`.
- Added `storage/tools/summarize_standalone.py` and generated:
  - `storage/evidence/standalone_coverage.md`;
  - `storage/evidence/standalone_coverage.json`.
- Added `storage/tools/build_manifest.py` and generated:
  - `storage/MANIFEST.md`;
  - `storage/MANIFEST.json`.
- Added `storage/tools/build_example_catalog.py` and generated:
  - `storage/EXAMPLE_CATALOG.md`;
  - `storage/EXAMPLE_CATALOG.json`.
- Added `storage/tools/toy_openscop_layout_remap.py` and generated:
  - `storage/evidence/toy_layout_remap_a_scale2.scop`;
  - `storage/evidence/toy_layout_remap_summary.txt`.
- Added `storage/tools/toy_openscop_scratchpad.py` and generated:
  - `storage/evidence/toy_scratchpad_packing_source.scop`;
  - `storage/evidence/toy_scratchpad_packing_target.scop`;
  - `storage/evidence/toy_scratchpad_copyout_source.scop`;
  - `storage/evidence/toy_scratchpad_copyout_target.scop`;
  - `storage/evidence/toy_scratchpad_witness.json`;
  - `storage/evidence/toy_scratchpad_packing_summary.txt`;
  - `storage/evidence/toy_scratchpad_copyout_summary.txt`.
- Added `storage/tools/toy_openscop_reuse_folding.py` and generated:
  - `storage/evidence/toy_array_contraction_source.scop`;
  - `storage/evidence/toy_array_contraction_target.scop`;
  - `storage/evidence/toy_inter_array_reuse_source.scop`;
  - `storage/evidence/toy_inter_array_reuse_target.scop`;
  - `storage/evidence/toy_double_buffering_source.scop`;
  - `storage/evidence/toy_double_buffering_target.scop`;
  - `storage/evidence/toy_reuse_folding_witness.json`;
  - `storage/evidence/toy_array_contraction_summary.txt`;
  - `storage/evidence/toy_inter_array_reuse_summary.txt`;
  - `storage/evidence/toy_double_buffering_summary.txt`.
- Added `storage/tools/toy_openscop_advanced_storage.py` and generated:
  - `storage/evidence/toy_versioning_source.scop`;
  - `storage/evidence/toy_versioning_target.scop`;
  - `storage/evidence/toy_reduction_source.scop`;
  - `storage/evidence/toy_reduction_target.scop`;
  - `storage/evidence/toy_overlap_source.scop`;
  - `storage/evidence/toy_overlap_target.scop`;
  - `storage/evidence/toy_view_composition_source.scop`;
  - `storage/evidence/toy_view_composition_target.scop`;
  - `storage/evidence/toy_advanced_storage_witness.json`;
  - `storage/evidence/toy_versioning_summary.txt`;
  - `storage/evidence/toy_reduction_summary.txt`;
  - `storage/evidence/toy_overlap_summary.txt`;
  - `storage/evidence/toy_view_composition_summary.txt`.
- Added `storage/tools/toy_openscop_private_protocols.py` and generated:
  - `storage/evidence/toy_private_copy_boundary_source.scop`;
  - `storage/evidence/toy_private_copy_boundary_target.scop`;
  - `storage/evidence/toy_private_access_source.scop`;
  - `storage/evidence/toy_private_access_target.scop`;
  - `storage/evidence/toy_scalar_promotion_source.scop`;
  - `storage/evidence/toy_scalar_promotion_target.scop`;
  - `storage/evidence/toy_private_protocols_witness.json`;
  - `storage/evidence/toy_private_copy_boundary_summary.txt`;
  - `storage/evidence/toy_private_access_summary.txt`;
  - `storage/evidence/toy_scalar_promotion_summary.txt`.
- Added `storage/tools/toy_openscop_boundary_domain.py` and generated:
  - `storage/evidence/toy_no_alias_source.scop`;
  - `storage/evidence/toy_no_alias_target.scop`;
  - `storage/evidence/toy_frame_source.scop`;
  - `storage/evidence/toy_frame_target.scop`;
  - `storage/evidence/toy_index_split_source.scop`;
  - `storage/evidence/toy_index_split_target.scop`;
  - `storage/evidence/toy_boundary_domain_witness.json`;
  - `storage/evidence/toy_no_alias_summary.txt`;
  - `storage/evidence/toy_frame_summary.txt`;
  - `storage/evidence/toy_index_split_summary.txt`.
- Added `storage/Makefile`; `make -C storage all` rebuilds the summaries and
  OpenScop probes.

## Current Evidence

The Candl `-scalexp` run demonstrates a real storage-representation change:

```text
t: 1D x4 -> 2D x4 changed
Dependence count: before 9, after 5
```

This supports scalar expansion as a concrete storage transformation target.

For scalar privatization, Candl marks a dependence as `RAW_SCALPRIV`, but the
access arities and dependence count stay unchanged in the unit test.  Pluto's
generated C for the tested `--candldep --scalpriv --parallel` case is identical
to the no-`--scalpriv` output.  This is useful negative evidence: it keeps the
survey from overstating Pluto `--scalpriv` as an observed storage rewrite.

The standalone logs provide broad toy-tool coverage over the transformation
taxonomy.  They are useful for deciding whether a transformation makes semantic
sense and what negative cases matter, but they are not evidence that those
optimizations are emitted by Pluto/OpenScop.

The generated coverage table currently reports 19 positive cases and 76
negative checks.

The generated manifest currently has 19 entries and no missing source/target
examples.

The generated example catalog currently has 19 entries; every entry has:
source/target example files, at least two documented variants, positive
obligations, required witness fields, explicit evidence status, and either
negative malformed-witness checks or a schedule-only/domain explanation.

Tool-backed status:

- tool-backed entries: `affine_interchange`, `ordinary_tiling`,
  `scalar_privatization_expansion`, `layout_remap_padding`,
  `scratchpad_packing`, `scratchpad_copy_out`, `array_contraction`,
  `inter_array_reuse`, `array_expansion_versioning`, `overlapped_tiling`,
  `reduction_privatization`, `double_buffering`, `storage_view_composition`,
  `private_copy_boundary`, `private_access_local_instantiation`,
  `scalar_promotion`, `source_no_alias_abstraction`,
  `contextual_frame_preservation`, `index_set_splitting`;
- only `scalar_privatization_expansion` is a real external storage-access
  rewrite;
- `layout_remap_padding` is backed by an in-repo toy OpenScop access rewrite,
  not by a current Pluto pass;
- `scratchpad_packing` and `scratchpad_copy_out` are backed by an in-repo toy
  OpenScop skeleton plus JSON witness sidecar, not by a current Pluto pass;
- `array_contraction`, `inter_array_reuse`, and `double_buffering` are backed by
  an in-repo toy OpenScop skeleton plus JSON reuse/folding witness sidecar, not
  by a current Pluto pass;
- `array_expansion_versioning`, `overlapped_tiling`,
  `reduction_privatization`, and `storage_view_composition` are backed by an
  in-repo toy OpenScop skeleton plus JSON advanced-storage witness sidecar, not
  by a current Pluto pass;
- `private_copy_boundary`, `private_access_local_instantiation`, and
  `scalar_promotion` are backed by an in-repo toy OpenScop skeleton plus JSON
  private-protocol witness sidecar, not by a current Pluto pass;
- `source_no_alias_abstraction`, `contextual_frame_preservation`, and
  `index_set_splitting` are backed by an in-repo toy OpenScop skeleton plus JSON
  boundary/domain witness sidecar;
- all 19 entries have OpenScop-shaped or real-tool evidence.  Scalar promotion's
  executable standalone negatives are thin, but the catalog includes
  supplemental protocol negative cases.

## Rebuild Check

Current command:

```sh
make -C storage all
```

Status: passes.

## Important Design Correction

The top theorem should not be a concrete theorem about one hand-written loop.
The top theorem should expose:

```text
validator accepted
=> semantic refinement with final public logical views equal
```

Concrete programs such as `tmp -> tmp_exp[i]` are validation/smoke examples,
not theorem-facing APIs.

## Further Strengthening

The survey objective is covered: every entry has source/target examples,
documented variants, accepted obligations, negative cases, witness fields,
evidence status, and either real-tool or in-repo OpenScop-shaped evidence.

Useful follow-up work:

- replace more toy OpenScop witnesses with real external optimizer artifacts if
  such tools are found;
- add parser-backed checking or richer executable negative generation for the
  toy OpenScop sidecars;
- refine the universal formalization into a candidate Coq interface:
  public logical interface, private target vars, variable shapes, footprint
  elaboration, representation witnesses, and public logical view equality;
- map existing Coq witness/checker modules to the taxonomy without claiming
  completed soundness where only examples exist.
