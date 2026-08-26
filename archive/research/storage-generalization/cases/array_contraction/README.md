# array_contraction

Classification: same logical values / non-injective conflict-safe storage reuse

Correctness reason: non-injective physical reuse is allowed only for non-overlapping logical lifetimes

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- logical value ids
- physical reuse map
- valid intervals
- producer/consumer events
- kill or reuse events
- boundary projection

## Required Roles

- logical_value_id
- physical_reuse_map
- live_interval
- producer_consumer
- boundary_projection

## Examples

- positive certificates: 3
- negative certificates: 23
- source file: `examples/standalone/array_contraction.source.c`
- target file: `examples/standalone/array_contraction.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
