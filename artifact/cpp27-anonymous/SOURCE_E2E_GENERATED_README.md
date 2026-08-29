# Generated End-to-End Checks

This suite gives every case in the 62-input strict Loop corpus a uniform
executable check. It reads the materialized baseline and optimized loops,
synthesizes deterministic whole-C wrappers, compiles both programs, and
compares their numerical summaries.

Default CI runs one comparison for all 62 cases. Focused parallel,
second-level, and intra-tile runs additionally require the requested structural
effect. The packaged results are under `evidence/executable-checks/`.

Run the default suite with:

```sh
opam exec -- make test-end-to-end-generated-smoke
```

The wrappers make fragmentary benchmarks executable, but they are auxiliary
tests rather than part of the theorem. The current Loop-to-C lowering agrees
with the checked arithmetic on the positive operands used by this corpus;
diamond cases with negative division numerators remain covered by the verified
route and effect suites instead.
