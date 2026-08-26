# `polopt` Strict-Path Success Summary

Date: 2026-03-07

Scope:
- strict runtime path only
- `polopt` runs the proved path directly
- suite root: `/polcert/tests/polopt-regression`
- result: `53 / 62` succeed

Ten successful cases are effectively unchanged:
- `nodep`
- `noloop`
- `1dloop-invar`
- `dsyr2k`
- `dsyrk`
- `floyd`
- `strmm`
- `tmm`
- `tricky4`
- `wavefront`

So the current strict path produces a nontrivial transformed loop on `43 / 62` cases.

## High-level picture

What `polopt` currently succeeds at is narrower than “general polyhedral optimization”.
The successful cases fall into a few recurring patterns:

1. Schedule-preserving normalization
- bound canonicalization
- guard insertion for non-empty domains
- elimination of some temporary singleton loops in the pretty printer

2. Loop permutation / interchange
- Pluto changes loop order
- codegen regenerates a legal nest with the new iteration order

3. Skewing / wavefronting
- mainly on stencil-like examples
- visible as affine remapping of loop indices and non-rectangular bounds

4. Statement peeling / boundary splitting
- first/last iterations become separate guarded regions
- especially common on imperfect nests and sequence kernels

5. Limited fusion / overlap exploitation
- only a few cases show a real merged execution prefix
- many benchmarks named `fusion*` still only normalize or reorder, rather than fully fusing

What it does not currently demonstrate:
- tiling
- strip-mining
- parallelization
- vectorization
- general reduction-aware rescheduling beyond the cases already accepted by the validator

## Case-by-case summary

- `1dloop-invar`: bound normalization only; no meaningful schedule change.
- `costfunc`: real affine reschedule; 2D nest is skewed/permuted into a wavefront-style band.
- `dsyr2k`: bound normalization only.
- `dsyrk`: bound normalization only.
- `fdtd-1d`: statement-order preserved, but boundary handling is peeled into guarded fragments.
- `fdtd-2d`: same pattern as `fdtd-1d`; imperfect nest is normalized with explicit boundary guards.
- `floyd`: bound normalization only.
- `fusion10`: no meaningful fusion under the strict path; structure is essentially unchanged apart from naming/canonicalization.
- `fusion2`: no actual fusion observed; both loop nests remain separate.
- `fusion3`: same as `fusion2`; no real fusion.
- `fusion4`: same as `fusion2`; no real fusion.
- `fusion5`: no real fusion; mostly guard insertion and canonicalization.
- `fusion6`: partial statement peeling/reordering; scalar initialization is split out, but this is not a clean fused loop nest.
- `fusion7`: no real fusion; independent loops remain separate under guards.
- `fusion9`: partial fusion/peeling; the first statement’s boundary iteration is split, and later work is partially aligned.
- `gemver`: mostly normalization of a multi-statement sequence; no strong loop-permutation effect beyond canonicalization.
- `intratileopt1`: clear interchange/permutation; the two loop dimensions are swapped.
- `intratileopt2`: canonicalization only.
- `intratileopt3`: clear interchange/permutation.
- `intratileopt4`: clear interchange/permutation.
- `matmul`: real loop permutation; order changes from source-style `M,N,K` to generated `K,N,M`.
- `matmul-init`: mostly canonicalization; the init+update structure is preserved.
- `matmul-seq`: multi-stage matrix product stays as separate nests; canonicalized but not fused.
- `matmul-seq3`: same as `matmul-seq`.
- `multi-loop-param`: no meaningful cross-loop optimization; independent loops remain separate with guards.
- `mvt`: mostly normalization of two independent matrix-vector loops.
- `mxv`: canonicalization only.
- `mxv-seq`: two sequential phases remain separate; no real fusion.
- `mxv-seq3`: same as `mxv-seq`.
- `negparam`: domain-guard insertion plus canonicalization.
- `nodep`: unchanged.
- `noloop`: unchanged modulo codegen/pretty-print normalization.
- `polynomial`: two-phase structure preserved; initialization and convolution are separated cleanly under guards.
- `seidel`: real skewing / wavefront transformation; this is one of the clearest nontrivial schedule changes.
- `seq`: canonicalization only.
- `shift`: boundary peeling; first/last positions are separated out from the main interior loop.
- `spatial`: canonicalization only.
- `strmm`: canonicalization only.
- `strsm`: if/branch structure is converted into peeled affine regions; this is a meaningful control-to-schedule normalization.
- `tce`: large perfect nest stays structurally similar; mostly canonicalization.
- `tmm`: canonicalization only.
- `tricky2`: genuine overlap/fusion effect; the common prefix of two loops is merged, with tails peeled separately.
- `tricky3`: scalar/statement scheduling is normalized; several singleton scalar phases are reordered/peeled.
- `tricky4`: bound normalization only.
- `wavefront`: canonicalization only under the current exporter/scheduler path; despite the benchmark name, no strong new skew is visible here.

## What the current strict path has actually demonstrated

The strict proved path has shown that the following kinds of transformations are already achievable end to end:

1. Affine loop permutation / interchange
- `costfunc`
- `intratileopt1`
- `intratileopt3`
- `intratileopt4`
- `matmul`

2. Affine skewing / wavefront rescheduling
- `costfunc`
- `seidel`

3. Statement peeling / guard-based boundary separation
- `fdtd-1d`
- `fdtd-2d`
- `shift`
- `strsm`
- `fusion6`
- `fusion9`
- `tricky3`

4. Partial fusion / overlap merging
- `tricky2`
- `fusion9` (partial)

Everything else currently successful is better described as:
- schedule-preserving normalization
- mild reindexing
- domain-guard insertion
- regeneration of a legal loop nest from the validated schedule

That is still useful, but it is weaker than “all successful cases got a profitability-improving polyhedral reschedule”.
