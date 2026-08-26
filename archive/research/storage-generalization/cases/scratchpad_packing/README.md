# scratchpad_packing

Classification: same instances / copy-mediated local storage

Correctness reason: copy-in covers local reads and local buffer cells consistently represent a public tile

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- tile footprint
- public-to-local copy map
- local buffer shape
- local read coverage

## Required Roles

- tile_footprint
- copy_boundary
- local_buffer_shape
- public_commit_or_read_cover

## Examples

- positive certificates: 3
- negative certificates: 21
- source file: `examples/standalone/scratchpad_packing.source.c`
- target file: `examples/standalone/scratchpad_packing.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
