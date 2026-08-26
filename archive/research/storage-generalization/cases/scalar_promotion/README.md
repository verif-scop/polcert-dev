# scalar_promotion

Classification: same instances / array cell simulated by scalar

Correctness reason: entry load, scalar updates, and exit store implement the same public cell value

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- entry load event
- private scalar interval
- alias/clobber exclusion
- exit store-back event

## Required Roles

- entry_load
- private_scalar_interval
- alias_clobber_exclusion
- exit_store_back

## Examples

- positive certificates: 3
- negative certificates: 25
- source file: `examples/standalone/scalar_promotion.source.c`
- target file: `examples/standalone/scalar_promotion.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
