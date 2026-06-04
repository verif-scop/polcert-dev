# private_copy_boundary

Classification: same instances / private live-in and live-out boundary copies

Correctness reason: copy-in initializes private live-ins and unique copy-out commits private live-outs to public variables

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- copy-in map
- copy-out map
- private live-in/live-out sets
- unique public commits

## Required Roles

- copy_in
- private_live_set
- copy_out
- unique_public_commit

## Examples

- positive certificates: 3
- negative certificates: 20
- source file: `examples/standalone/private_copy_boundary.source.c`
- target file: `examples/standalone/private_copy_boundary.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
