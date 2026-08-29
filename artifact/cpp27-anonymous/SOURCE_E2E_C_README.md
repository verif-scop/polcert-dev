# Handwritten C-Level Examples

These cases instantiate PolCert's typed instruction semantics by hand and use
small C programs as readable reference behavior. They exercise the extracted
compiler and generated C harness without treating C parsing as part of the
formal theorem.

Representative cases cover:

- extraction and affine scheduling;
- ISS, ordinary tiling, two-level tiling, and diamond tiling;
- checked parallel annotation;
- constant unrolling and supported unroll-and-jam routes;
- dependent cases that must remain sequential or reject an unsafe rewrite.

Each case directory contains a manifest, the structured `.loop` input, and the
reference C program. Run the suite with:

```sh
opam exec -- make test-end-to-end-c
```

The harness compiles baseline and optimized programs, compares their numerical
summaries, and checks requested structural effects. This is executable
regression evidence; the parser, emitted C, external compiler, and runtime are
outside the Rocq refinement theorem.
