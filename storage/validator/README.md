# Storage Validator Prototype

This directory contains a generic OCaml prototype for validating storage
transformation certificates.

The validator does not encode one theorem per concrete example.  It reads
`cases/registry.txt`, then checks every `.cert` file under `cases/*/positive`
and `cases/*/negative` against the same public certificate language.

The first layer checks certificate structure:

- the source and target declare public variables;
- the final observable relation is `public_output_view_eq`;
- the certificate has the witness kind required by the registry;
- all required witness fields and protocol roles are present.

The second layer checks finite semantic facts requested by the registry:

- public-output equality, including target representation cells;
- exact domain cover and unchanged accesses for schedule-only cases;
- unique public commits for copy-out/promotion/reduction cases;
- live-interval non-overlap for reuse, contraction, and versioning cases;
- reduction algebraic laws;
- frame preservation and view-composition bridge equality.

Positive certificates must satisfy every required item.  Negative certificates
are expected to fail either by omitting one required public-view, witness-field,
or protocol-role item, or by providing complete structure with bad finite
semantic facts.

This is intentionally not a proof yet.  Its job is to pin down validation
strength before any Coq theorem is redesigned.

## Current Validation Strength

The prototype checks structural completeness and finite semantic consistency
against a transformation registry:

- public logical variables must be declared from the source-level view;
- target-only storage is representation state, not public output;
- each transformation must name its witness kind;
- every required witness field and protocol role for that transformation must
  be present;
- malformed certificates must be rejected by the same generic checker;
- semantic negatives with complete witness metadata must also be rejected.

This is still not a Coq proof.  It is a finite witness validator meant to fix
the interface and expected validation strength before proving soundness.
