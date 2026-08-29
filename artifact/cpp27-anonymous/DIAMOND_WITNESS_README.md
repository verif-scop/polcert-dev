# Diamond Tiling without Intra-Tile Rescheduling

A historical phase-dump implementation made restoration of a mandatory
diamond schedule hyperplane conditional on the optional intra-tile locality
pass. With intra-tile rescheduling disabled, the resulting mixed-scalar
schedule changed the numerical result.

The ordinary fixed Pluto snapshot used by the main tests contains the repair;
the historical bug-witness snapshot does not. PolCert rejects the malformed
mixed-scalar tiling candidate before code generation. A separate typed
`diamond-stencil` case confirms that the supported pure diamond route is
accepted.

The runner records the producer result and the checked-pipeline rejection in
`evidence/pluto-bug-witnesses/validation.log` from the archive root.
