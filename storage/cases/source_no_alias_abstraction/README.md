# source_no_alias_abstraction

Classification: precondition / logical blocks distinct

Correctness reason: logical source variables have distinct footprints, so storage reasoning over variables is sound

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- source variable footprints
- non-overlap proof for distinct variables
- in-bounds source accesses

## Required Roles

- source_footprint
- no_alias
- in_bounds

## Examples

- positive certificates: 3
- negative certificates: 14
- source file: `examples/standalone/source_no_alias_abstraction.source.c`
- target file: `examples/standalone/source_no_alias_abstraction.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
