# overlapped_tiling

Classification: instance-count-changing / private recomputation plus unique commit

Correctness reason: extra computations are private; commit instances exactly cover public live-outs

The validator target for this case is not raw `State.eq`.  It is agreement on the declared public variables after applying the case witness.

## Required Witness Fields

- source-to-target duplicate projection
- halo closure
- commit set
- exact cover of public live-outs

## Required Roles

- duplicate_projection
- halo_closure
- commit_set
- exact_public_cover

## Examples

- positive certificates: 3
- negative certificates: 23
- source file: `examples/standalone/overlapped_tiling.source.c`
- target file: `examples/standalone/overlapped_tiling.target.c`

Negative certificates are expected to fail the generic validator by omitting one required public-view, witness-field, or protocol-role item.
