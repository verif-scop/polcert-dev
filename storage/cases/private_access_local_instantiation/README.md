# private_access_local_instantiation

Classification: same instances / access-level private storage instantiation

Correctness reason: symbolic private accesses instantiate to declared, in-bounds, hidden private cells

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- symbolic private access
- instantiated target private cell
- hidden/private declaration
- in-bounds proof

## Required Roles

- symbolic_private_access
- private_cell_instantiation
- hidden_storage
- bounds_check

## Examples

- positive certificates: 3
- negative certificates: 16
- source file: `examples/standalone/private_access_local_instantiation.source.c`
- target file: `examples/standalone/private_access_local_instantiation.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
