# contextual_frame_preservation

Classification: contextual frame / allowed writes plus preserved frame snapshot

Correctness reason: writes stay inside the allowed fragment footprint and protected frame variables keep their values

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- allowed write set
- protected frame variables
- pre/post frame snapshots

## Required Roles

- allowed_write_set
- protected_frame
- frame_snapshot

## Examples

- positive certificates: 3
- negative certificates: 14
- source file: `examples/standalone/contextual_frame_preservation.source.c`
- target file: `examples/standalone/contextual_frame_preservation.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
