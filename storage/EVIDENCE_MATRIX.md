# Evidence Matrix

The generated manifest is the authoritative matrix:

```text
storage/MANIFEST.md
storage/MANIFEST.json
storage/EXAMPLE_CATALOG.md
storage/EXAMPLE_CATALOG.json
```

Regenerate it with:

```sh
make -C storage all
```

## Current Summary

- manifest entries: 19
- entries with source/target examples: 19
- example catalog entries: 19
- entries with at least two documented example variants: 19
- tool-backed entries: 19
- toy-only entries: 0

Every entry now has either real external-tool evidence or in-repo
OpenScop-shaped toy evidence.  Most storage-rewrite entries are still toy
OpenScop evidence rather than real Pluto/OpenScop optimizer output.

The example catalog is the current sufficiency audit.  It records, for every
transformation:

- core source/target files;
- additional positive or negative variants;
- accepted obligations;
- malformed-witness negative checks;
- required witness fields;
- evidence status and known gaps.

Tool-backed does not always mean "storage rewrite":

- `scalar_privatization_expansion` is the only entry currently backed by a real
  external storage-access rewrite, via Candl `-scalexp`.
- `layout_remap_padding` is backed by the in-repo toy OpenScop rewrite probe.
  It is useful for testing the representation shape, but it is not evidence
  that Pluto currently performs this pass.
- `scratchpad_packing` and `scratchpad_copy_out` are backed by the in-repo toy
  OpenScop scratchpad generator plus a structured JSON witness sidecar.  This
  tests copy-in/copy-out evidence shape, not Pluto support.
- `array_contraction`, `inter_array_reuse`, and `double_buffering` are backed by
  the in-repo toy OpenScop reuse/folding generator plus a structured JSON
  witness sidecar.  This tests lifetime/phase evidence shape, not Pluto support.
- `array_expansion_versioning`, `reduction_privatization`,
  `overlapped_tiling`, and `storage_view_composition` are backed by the in-repo
  toy OpenScop advanced-storage generator plus structured JSON witnesses.  This
  tests version selectors, merge trees, commit sets, and view composition shape,
  not Pluto support.
- `private_copy_boundary`, `private_access_local_instantiation`, and
  `scalar_promotion` are backed by the in-repo toy OpenScop private-protocol
  generator plus structured JSON witnesses.  This tests boundary pairs,
  symbolic private-access instantiation, scalar load/store-back protocols, and
  alias/clobber evidence shape, not Pluto support.
- `source_no_alias_abstraction`, `contextual_frame_preservation`, and
  `index_set_splitting` are backed by the in-repo toy OpenScop boundary/domain
  generator.  These are precondition/context/domain entries, not storage
  rewrites.
- `affine_interchange` and `ordinary_tiling` are backed by real schedule tooling,
  but they are storage-preserving baselines.

## Real-Tool Gap

Only `scalar_privatization_expansion` currently has real external
storage-access rewrite evidence, via Candl `-scalexp`.  `affine_interchange` and
`ordinary_tiling` have real schedule-tooling evidence but are storage-preserving
baselines.  The rest of the storage survey is in-repo toy OpenScop evidence plus
standalone validation logs.

## Next Tool Evidence Targets

Priority order:

1. Strengthen `layout_remap_padding`: the toy access rewrite exists; the next
   step is either a parser-backed OpenScop rewrite or a tool-emitted example.
2. Strengthen `scratchpad_packing` / `scratchpad_copy_out`: the toy skeleton and
   witness sidecar exist; the next step is parser-backed role checking or a
   tool-emitted scratchpad example.
3. Strengthen reuse/folding/version/reduction/overlap/composition/private
   protocol toy evidence: sidecars now exist; the next step is parser-backed
   obligation checking, richer negative generation, or real tool-emitted
   examples.
