# affine_interchange

Classification: instance-preserving / storage-preserving

Correctness reason: instances and storage accesses are unchanged; only legal schedule order changes

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- instance bijection
- legal schedule order
- unchanged storage accesses

## Required Roles

- instance_bijection
- schedule_legality
- storage_access_identity

## Examples

- positive certificates: 3
- negative certificates: 11
- source file: `examples/standalone/affine_interchange.source.c`
- target file: `examples/standalone/affine_interchange.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
