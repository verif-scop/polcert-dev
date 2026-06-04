# ordinary_tiling

Classification: instance-preserving / grouped schedule

Correctness reason: tile projection covers source instances and storage accesses are unchanged

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- tile projection
- exact domain cover
- unchanged storage accesses

## Required Roles

- domain_cover
- domain_disjointness
- storage_access_identity

## Examples

- positive certificates: 3
- negative certificates: 11
- source file: `examples/standalone/ordinary_tiling.source.c`
- target file: `examples/standalone/ordinary_tiling.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
