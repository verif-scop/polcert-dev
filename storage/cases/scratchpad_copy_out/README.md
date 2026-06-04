# scratchpad_copy_out

Classification: same instances / copy-mediated local update plus commit

Correctness reason: local updates are private until every updated public cell is committed exactly once

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- updated local cells
- copy-out commit map
- public live-out set
- unique commit proof

## Required Roles

- tile_footprint
- copy_boundary
- local_buffer_shape
- public_commit_or_read_cover

## Examples

- positive certificates: 3
- negative certificates: 17
- source file: `examples/standalone/scratchpad_copy_out.source.c`
- target file: `examples/standalone/scratchpad_copy_out.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
