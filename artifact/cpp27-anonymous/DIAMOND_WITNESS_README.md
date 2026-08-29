# Diamond Tiling without Intra-Tile Rescheduling

A historical Pluto version restored part of a diamond-tiling schedule only
when an optional optimization inside each tile was enabled. Disabling that
optimization could therefore produce an invalid schedule and a wrong
numerical result.

The Pluto version used by the main tests contains the repair. The historical
version kept for this case does not. PolCert rejects its invalid tiling before
code generation. A separate `diamond-stencil` case confirms that PolCert
accepts a valid diamond tiling.

The runner records Pluto's result and PolCert's rejection in
`evidence/rejected-optimizer-outputs/validation.log` from the archive root.
