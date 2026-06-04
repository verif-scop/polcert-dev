# Storage Transformation Survey

This folder is a validation-first survey of storage transformations.

The theorem-facing idea should stay simple:

```text
old endpoint: final target state equals final source state
new endpoint: final target/source observations agree on public variables
```

Private, temporary, scratch, version, or reused storage is internal.  It may be
created, renamed, folded, copied, or overwritten as long as the final public
variables have the same observable contents.

The files here separate three layers:

- `TRANSFORMATIONS.md`: what each storage transformation does and why it can be
  accepted end to end.
- `FORMAL_MODEL.md`: a universal theorem-facing model based on public variables,
  with cell-level machinery kept below the API.
- `END_TO_END_CORRECTNESS.md`: the common correctness story for accepted
  storage transformations.
- `EVIDENCE_MATRIX.md`: generated manifest interpretation and tool-backed vs
  toy-only status.
- `EXAMPLE_CATALOG.md`: generated example sufficiency catalog for every
  transformation, including variants, negative checks, witness fields, and
  evidence status.
- `TOOLS.md`: external and in-repo tools used by the survey.
- `SUBAGENT_REVIEWS.md`: independent review notes folded back into the survey.
- `tools/openscop_storage_diff.py`: a small OpenScop text probe for comparing
  access arities and dependence counts in before/after `.scop` files.
- `tools/toy_openscop_layout_remap.py`: a narrow toy OpenScop rewrite for
  access-level layout remapping evidence.
- `tools/toy_openscop_scratchpad.py`: a narrow toy OpenScop skeleton generator
  for scratchpad copy-in/copy-out witness evidence.
- `tools/toy_openscop_reuse_folding.py`: a narrow toy OpenScop skeleton
  generator for contraction, inter-array reuse, and double-buffering witnesses.
- `tools/toy_openscop_advanced_storage.py`: a narrow toy OpenScop skeleton
  generator for versioning, reduction privatization, overlap/halo, and view
  composition witnesses.
- `tools/toy_openscop_private_protocols.py`: a narrow toy OpenScop skeleton
  generator for private copy boundaries, symbolic private access instantiation,
  and scalar promotion protocols.
- `tools/toy_openscop_boundary_domain.py`: a narrow toy OpenScop skeleton
  generator for source no-alias, contextual frame preservation, and index-set
  splitting witnesses.
- `tools/summarize_standalone.py`: a log parser that turns standalone
  validation runs into a coverage table.
- `tools/build_example_catalog.py`: a generated catalog builder that keeps
  example variants and negative families visible for every transformation.
- `examples/`: minimal C targets used to calibrate the survey.

## Current Evidence Target

The strongest current external evidence is Candl scalar expansion:

```sh
./candl/candl -outscop -scalexp 0 -o /tmp/scalexp0.scop \
  candl/tests/unitary/scalexp.c.orig.scop

./candl/candl -outscop -scalexp 1 -o /tmp/scalexp1.scop \
  candl/tests/unitary/scalexp.c.orig.scop
```

Then compare the OpenScop files:

```sh
python3 storage/tools/openscop_storage_diff.py \
  /tmp/scalexp0.scop /tmp/scalexp1.scop
```

Expected high-level signal: the temporary scalar `t` changes from scalar access
`Arr == t` to indexed access `Arr == t, [1] == i`, and the dependence count
drops in the Candl output.  That is a real storage-representation change.

Pluto `--scalpriv` is related but weaker as evidence: in the current Pluto
source it is forwarded to Candl dependence analysis and may mark or prune
dependences, but Pluto does not expose it as a checked storage-rewrite witness.

The in-repo toy layout-remap probe gives one additional OpenScop-level storage
artifact: it rewrites a simple access relation while keeping the public logical
array interface separate from the target physical layout.  This is deliberately
not claimed as Pluto support.

The in-repo toy scratchpad generator adds OpenScop-shaped skeletons for
copy-in/local-buffer use and copy-out commit.  The `.scop` files show the
read/write access shape; the JSON sidecar records the semantic roles needed by
the validator.  This is deliberately not claimed as Pluto support or as a full
OpenScop proof of equivalence.

The in-repo toy reuse/folding generator adds OpenScop-shaped skeletons for
folded physical storage and a JSON sidecar for lifetime/phase obligations:
valid intervals, reaching producers, kill/reuse events, and final boundary
projection.  This is deliberately not claimed as Pluto support or as a full
OpenScop proof of equivalence.

The in-repo toy advanced-storage generator adds OpenScop-shaped skeletons for
version selection, reduction merge, overlap/halo commit, and view composition.
The JSON sidecar records selectors, merge trees, commit sets, intermediate
interfaces, checked obligations, and negative cases.  This is deliberately not
claimed as Pluto support or as a full OpenScop proof of equivalence.

The in-repo toy private-protocol generator adds OpenScop-shaped skeletons for
copy-in/copy-out boundaries, symbolic private access instantiation, and
load/update/store-back scalar promotion.  The JSON sidecar records private
declarations, boundary protocols, scalar intervals, alias/clobber exclusions,
checked obligations, and negative cases.  This is deliberately not claimed as
Pluto support or as a full OpenScop proof of equivalence.

The in-repo toy boundary/domain generator adds OpenScop-shaped skeletons for
source-footprint no-alias assumptions, contextual frame preservation, and
index-set splitting.  These are not storage rewrites, but they are part of the
validator boundary needed by the storage theorem.

## Broad Toy Coverage

The copied standalone examples in `examples/standalone/` and logs in
`evidence/standalone_*.log` cover the wider storage taxonomy.  Regenerate the
coverage table with:

```sh
make -C storage all
```

or directly:

```sh
python3 storage/tools/summarize_standalone.py \
  storage/evidence/standalone_positive.log \
  storage/evidence/standalone_negative.log \
  > storage/evidence/standalone_coverage.md
```

The current generated table is `storage/evidence/standalone_coverage.md`.
