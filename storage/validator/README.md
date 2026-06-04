# Storage Validator Prototype

This directory contains a generic OCaml prototype for validating storage
transformation certificates.

The validator does not encode one theorem per concrete example.  It reads
`cases/registry.txt`, then checks every `.cert` file under `cases/*/positive`
and `cases/*/negative` against the same public certificate language:

- the source and target declare public variables;
- the final observable relation is `public_output_view_eq`;
- the certificate has the witness kind required by the registry;
- all required witness fields and protocol roles are present.

Positive certificates must satisfy every required item.  Negative certificates
are expected to fail by omitting one required public-view, witness-field, or
protocol-role item.

This is intentionally not a proof yet.  Its job is to pin down validation
strength before any Coq theorem is redesigned.

## Current Validation Strength

The prototype checks certificate completeness against a transformation
registry:

- public logical variables must be declared from the source-level view;
- target-only storage is representation state, not public output;
- each transformation must name its witness kind;
- every required witness field and protocol role for that transformation must
  be present;
- malformed certificates must be rejected by the same generic checker.

This is a structural validator, not a semantic theorem.  The next semantic
level should interpret the witness fields over finite CInstr/OpenScop events:
domain cover, access projection, live interval non-overlap, copy-in/copy-out
coverage, commit uniqueness, and final public-output equality.
