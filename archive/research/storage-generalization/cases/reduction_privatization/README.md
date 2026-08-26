# reduction_privatization

Classification: parallel/storage privatization plus merge

Correctness reason: private accumulators cover source contributions and merge under checked algebraic laws

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- chunk partition
- private accumulator initialization
- contribution coverage
- merge tree
- operator laws

## Required Roles

- chunk_partition
- accumulator_init
- contribution_cover
- merge_tree
- operator_laws

## Examples

- positive certificates: 3
- negative certificates: 25
- source file: `examples/standalone/reduction_privatization.source.c`
- target file: `examples/standalone/reduction_privatization.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
