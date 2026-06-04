# storage_view_composition

Classification: composition / layout projection followed by private erasure

Correctness reason: target-mid and mid-source public views agree on intermediate observables and compose

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- source-to-mid public view
- mid-to-target public view
- compatible intermediate interface
- composed output view equality

## Required Roles

- source_mid_view
- mid_target_view
- interface_compatibility
- composed_public_view

## Examples

- positive certificates: 3
- negative certificates: 18
- source file: `examples/standalone/storage_view_composition.source.c`
- target file: `examples/standalone/storage_view_composition.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
