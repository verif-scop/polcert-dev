# index_set_splitting

Classification: instance-preserving / domain partition

Correctness reason: target subdomains disjointly and exactly cover the source domain

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- source domain
- target subdomains
- disjoint exact-cover proof

## Required Roles

- domain_cover
- domain_disjointness
- storage_access_identity

## Examples

- positive certificates: 3
- negative certificates: 17
- source file: `examples/standalone/index_set_splitting.source.c`
- target file: `examples/standalone/index_set_splitting.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
