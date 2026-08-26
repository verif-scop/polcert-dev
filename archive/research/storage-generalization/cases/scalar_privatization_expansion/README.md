# scalar_privatization_expansion

Classification: same instances / scalar storage expansion

Correctness reason: each source temporary live range is represented by a fresh per-instance private cell before public use

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- logical temporary live range
- fresh private cell per instance
- write-before-read evidence
- optional live-out copy

## Required Roles

- fresh_private_cell
- live_range
- def_use_dominance

## Examples

- positive certificates: 3
- negative certificates: 18
- source file: `examples/standalone/scalar_privatization_expansion.source.c`
- target file: `examples/standalone/scalar_privatization_expansion.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
