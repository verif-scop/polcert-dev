# double_buffering

Classification: same logical values / phase-separated ping-pong storage

Correctness reason: phase projection identifies the current physical buffer and final projection covers public live-outs

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- phase projection
- current/next buffer map
- swap transition proof
- final boundary projection

## Required Roles

- version_selector
- phase_projection
- buffer_role
- final_projection

## Examples

- positive certificates: 3
- negative certificates: 21
- source file: `examples/standalone/double_buffering.source.c`
- target file: `examples/standalone/double_buffering.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
