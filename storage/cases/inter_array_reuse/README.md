# inter_array_reuse

Classification: same instances / cross-array lifetime-based storage reuse

Correctness reason: arrays share a buffer only across disjoint lifetime intervals with compatible storage

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- logical arrays sharing one region
- disjoint lifetime intervals
- physical region compatibility
- copy-out before reuse

## Required Roles

- logical_value_id
- physical_reuse_map
- live_interval
- producer_consumer
- boundary_projection

## Examples

- positive certificates: 3
- negative certificates: 20
- source file: `examples/standalone/inter_array_reuse.source.c`
- target file: `examples/standalone/inter_array_reuse.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
