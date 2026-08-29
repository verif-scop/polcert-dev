# Handwritten C-Level Examples

These examples define typed PolCert programs by hand and include small C
programs that show the intended computation. They test the extracted compiler
without treating C parsing as part of the theorem.

Representative cases cover:

- construction of the polyhedral model and schedule checking;
- ISS, ordinary tiling, two-level tiling, and diamond tiling;
- checked parallel loops;
- constant unrolling and supported unroll-and-jam routes;
- dependent loops that must remain sequential or reject an unsafe rewrite.

Each case directory contains a manifest, the structured `.loop` input, and the
reference C program. Run the suite with:

```sh
opam exec -- make test-end-to-end-c
```

The test runner compiles baseline and optimized programs, compares their
results, and checks that requested transformations occurred. The generated C,
external compiler, and runtime are tested here but are not part of the Rocq
theorem.
