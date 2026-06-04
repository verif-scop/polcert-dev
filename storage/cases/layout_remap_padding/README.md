# layout_remap_padding

Classification: same instances / injective physical address remap

Correctness reason: logical public cells are represented by an injective in-bounds physical layout map

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- logical public index
- physical layout map
- injectivity over live logical cells
- padding exclusion from public view

## Required Roles

- logical_to_physical_map
- injective_live_cells
- padding_erasure
- public_view_projection

## Examples

- positive certificates: 4
- negative certificates: 21
- source file: `examples/standalone/layout_remap_padding.source.c`
- target file: `examples/standalone/layout_remap_padding.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
