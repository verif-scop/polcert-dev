# array_expansion_versioning

Classification: same instances / more physical versions plus copy-out

Correctness reason: reads select produced versions and final copy-out selects the source-final version

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- definition-to-version map
- read version selectors
- produced-version proof
- final version selector

## Required Roles

- version_selector
- phase_projection
- buffer_role
- final_projection

## Examples

- positive certificates: 3
- negative certificates: 21
- source file: `examples/standalone/array_expansion_versioning.source.c`
- target file: `examples/standalone/array_expansion_versioning.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
