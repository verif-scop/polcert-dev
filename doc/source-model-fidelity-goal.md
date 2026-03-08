# Source Model Fidelity Goal

Date: 2026-03-07

## New primary objective

The current goal is no longer merely:

- `polopt` runs successfully on a benchmark, and
- the resulting scheduled poly passes validator.

That is necessary, but not sufficient.

The stronger objective is:

- `extractor + to_openscop` should produce a source OpenScop model that is as close as possible to the one produced by the C/Clan/Pluto extraction path, and
- Pluto should therefore solve the same scheduling problem in both paths.

Only under that condition can we reasonably claim:

- `polopt` achieves optimization behavior comparable to Pluto on that benchmark, and
- does so with the project’s verified/validated reliability story.

## Practical acceptance criterion

For a benchmark to count as "aligned with Pluto", the following should hold.

1. Source scop parity
- `polopt --extract-only` output should match the C/Clan `*.beforescheduling.scop` as closely as possible.
- Exact structural equality is ideal.
- If not exact, any remaining difference must be shown to be semantically irrelevant to Pluto’s scheduling problem.

2. Scheduled scop parity
- Pluto's scheduled result on our source scop should match, or be meaningfully equivalent to, Pluto's scheduled result on the C/Clan source scop.

3. Loop-level parity
- The optimized loop produced by `polopt` should reflect the same essential transformation class as Pluto's own generated code.
- Examples:
  - interchange
  - skewing
  - wavefronting
  - fission/fusion

4. Reliability
- The path must still remain on the strict proved pipeline:
  - `SPolOpt.opt = PreparedOpt.Opt`
- No CLI-only fallback or alternate validation view should be required.

## What is no longer sufficient

The following is not enough on its own:

- `validate(extracted, scheduled) = true`
- `polopt` prints an optimized loop

Those only show that the current source model is self-consistent enough to pass the verified/validated path.
They do not show that the source model is the same one that Pluto sees on the original C benchmark.

## Current interpretation of the remaining gap

The main remaining issue is source-model fidelity, not proof closure and not basic runtime correctness.

The likely mismatch dimensions are:

1. Source domain
- especially missing parameter-only guards

2. Source scattering
- especially statement-order skeleton and loop-dimension placement

3. Access/domain alignment
- where C/Clan source extraction may emit a structurally richer source scop than our extractor/export path

## Immediate analysis strategy

The next debugging unit is not the optimized loop first.
It is:

1. extractor internal poly
2. `to_openscop` source scop
3. C/Clan `before.scop`
4. Pluto `after.scop`
5. final optimized loop

The anchor benchmark is `covcol`, because it already demonstrates:

- strict `polopt` success,
- validator success,
- but optimization behavior that still differs materially from Pluto's C path.

## Exporter bug found and fixed

A concrete Coq-level reproducer showed that the source OpenScop exporter was dropping dynamic schedule dimensions.

- `Extractor` internal schedules are correct on a minimal imperfect-nest example.
- The loss occurs in `src/PolyLang.v` inside `schedule_to_source_like_rows`.
- The old Coq pattern
  - `aff1 :: (aff2 :: sched' as tl)`
  caused the recursive call to skip the middle dynamic schedule dimension.
- Therefore, when two adjacent schedule dimensions are both non-constant, the second one is skipped.
- Example:
  - intended: `[a; b; c] -> [a; 0; b; 0; c]`
  - buggy behavior: `[a; b; c] -> [a; 0; c]`

This bug has now been fixed in the working tree. Representative source `before.scop` scattering metadata now matches the C/Clan path on:

- `covcol`
- `matmul`

This does not complete source-model fidelity. It only removes one concrete exporter bug. The current strict `polopt` result after the fix is:

- `56 / 62` success
- remaining failing cases:
  - `corcol`
  - `costfunc`
  - `covcol`
  - `intratileopt3`
  - `shift`
  - `tricky1`

So the remaining gap is now smaller and more specific: the current source-model mismatch is no longer explainable by the dropped-middle-dimension bug alone.

## Current shape of the remaining six failures

After fixing the source-scattering exporter bug, the remaining strict-path failures are:

- `corcol`
- `costfunc`
- `covcol`
- `intratileopt3`
- `shift`
- `tricky1`

At first sight, these six differ from the C/Clan path only in `DOMAIN`: the C-path `before.scop` carries extra parameter-only guards such as:

- `M-1 >= 0`
- `N-1 >= 0`
- `M-2 >= 0`
- `N-2 >= 0`

This initially suggested a "missing implied guards" diagnosis, but a more careful experiment refined the picture.

## Guard-patching experiment on the remaining six cases

A controlled experiment was run on the six remaining failures:

- `corcol`
- `costfunc`
- `covcol`
- `intratileopt3`
- `shift`
- `tricky1`

Method:

1. export our own strict-path source `before.scop`,
2. replace only the `DOMAIN` sections with the C-path `before.scop` `DOMAIN` sections,
3. keep our own `SCATTERING`, access relations, and bodies unchanged,
4. rerun Pluto with `--readscop`.

Observed result:

- Pluto successfully produced optimized `after.scop` for all six,
- the resulting `after.scop` `SCATTERING` metadata matched the C-path `after.scop`,
- and `polcert(patched_before, patched_after)` returned `EQ` on all six.
- however, `polcert(patched_after, cpath_after)` still returned `NE`.

At the same time, the unpatched strict path still fails with:

- `wf1 = true`
- `wf2 = true`
- `eqdom = true`
- `valid_access = true`
- `res = false`

So the remaining failure mode is now very specific:

- Pluto can optimize these programs,
- the optimized schedule is accepted once the source domain includes the C-path parameter-only guards,
- and the only failing validator subcomponent on the unpatched path is the dependence-preservation check `res`.

This showed that source-domain weakness matters, but it did not yet prove that the remaining strict-path failure was *only* about missing guards.

## Refined diagnosis after strengthening the poly model

A new strengthening pass was then inserted on the true proved path:

- `StrengthenDomain.strengthen_pprog`
- invoked inside `driver/PolOptPrepared.v` before `scheduler'`

The pass adds parameter-only constraints that are direct sums of existing iterator constraints, e.g.:

- `i >= 1` and `i <= N` imply `N - 1 >= 0`
- `j >= 1` and `j <= N - 1` imply `N - 2 >= 0`

For `covcol`, debug output confirmed that strengthening is **actually active** on the proved path:

- statement 1 `DOMAIN` grows from 6 rows to 8 rows, adding:
  - `M - 1 >= 0`
  - `N - 1 >= 0`
- statement 2 `DOMAIN` grows from 4 rows to 5 rows, adding:
  - `M - 1 >= 0`

However, even on this strengthened input, strict `polopt` still fails with:

- `wf1 = true`
- `wf2 = true`
- `eqdom = true`
- `valid_access = true`
- `res = false`

So the remaining failure is **not** explained solely by missing parameter guards.

## What actually fails now

On `covcol`, the following experiment isolates the real remaining bug:

1. export the **strengthened** source `before.scop`,
2. run Pluto directly on that file,
3. compare Pluto's raw `after.scop` with the `scheduled` poly re-exported by the strict `polopt` path.

## Why validator is sensitive to schedule shape

The relevant point is not that validator compares "metadata formats". It uses
the schedule rows directly to encode happens-before relations.

For a schedule

- `[f1; f2; f3]`

the timestamp of a point `p` is the vector:

- `[f1(p); f2(p); f3(p)]`

and order is lexicographic on that vector.

`Validator.validate_two_instrs` builds:

- `old_sched_lt_polys := make_poly_lt old_sched1 old_sched2 ...`
- `new_sched_ge_polys := make_poly_ge new_sched1 new_sched2 ...`

Then `validate_lt_ge_pair` checks whether there exists a *single pair of
points* that simultaneously satisfies:

- same-location / in-domain constraints,
- old-before (`old_sched_lt`),
- new-not-before (`new_sched_ge`).

So old/new are linked through the same witness pair of points, not by comparing
two booleans after the fact.

For `mxv`, the important observation is that the "zero rows" are not always
redundant. Example:

- source-like old statement order: `[0; i; 1; j; 0]`
- compact form used internally: `[i; 1; j]`
- optimized schedule may look like: `[1; i; j]`

Dropping the leading zero does not preserve the earliest lexicographic
difference against another statement whose first component is the constant `1`.
In other words, compacting rows changes the actual order relation used by
validation.

This corrects an earlier misconception. The right long-term fix is not to add a
special validation-only pass for `mxv`. The real issue is that the current
compact schedule representation is not semantics-preserving in this class of
multi-statement programs. The design target is therefore:

- repair compact / canonical schedule handling itself,
- keep the strict runtime path equal to the proved path,
- avoid mxv-specific logic,
- and recover the same optimization behaviour as the C-path Pluto flow on all
  benchmark cases.

The current working hypothesis is:

- source-like padded schedules are the safe canonical representation,
- compacting schedule rows must be a global, program-wide transformation that
  preserves lexicographic order across statements,
- and the current per-statement local zero-row removal is too weak for that.

Observed result:

- `polcert(strengthened_before_raw_scop, pluto_raw_after_scop) = EQ`

This is the critical fact. It shows that:

- strengthening is already sufficient for Pluto to produce a validator-accepted optimized scop,
- and the remaining strict-path failure happens after Pluto, during `OpenScop -> PolyLang` import.

For `covcol`, the raw optimized scop from Pluto has:

- statement 1 scattering meta: `4 11 4 3 0 2`
- statement 2 scattering meta: `4 10 4 2 0 2`

But the strict `polopt` path re-imports it and then re-exports a scheduled scop with:

- statement 1 scattering meta: `7 14 7 3 0 2`
- statement 2 scattering meta: `5 11 5 2 0 2`

So the importer is not faithfully preserving Pluto's optimized schedule. It reconstructs the old source-like skeleton instead.

## Schedule-only importer experiment

A direct importer experiment was then run:

- temporarily switch `syntax/SPolIRs.v` from
  - `from_openscop_like_source`
- to
  - `from_openscop_schedule_only`

Result:

- the final six failures all recovered:
  - `corcol`
  - `costfunc`
  - `covcol`
  - `intratileopt3`
  - `shift`
  - `tricky1`
- but `22` previously successful cases regressed

So `from_openscop_schedule_only` is not a global replacement. It proves something more precise:

- the remaining six failures are caused by importer handling of optimized `SCATTERING`,
- but many other cases still require source-template-aware import.

The likely final fix is therefore not "switch importer globally", but:

- make `from_openscop_like_source` detect when Pluto has genuinely changed the schedule family,
- and avoid forcing such optimized schedules back into the old source-like template.

## Hybrid importer checkpoint

A first hybrid importer has now been implemented.

Strategy:

1. try the existing source-template refill,
2. re-export the reconstructed schedule back to source-like scattering rows,
3. compare those rows with the raw optimized `SCATTERING`,
4. if they match, keep the source-like refill,
5. otherwise fall back to compact/schedule-only import.

Result:

- the previous remaining six failures all recover:
  - `corcol`
  - `costfunc`
  - `covcol`
  - `intratileopt3`
  - `shift`
  - `tricky1`

But the strict suite is still not complete. Current strict result is now:

- `54 / 62`

Remaining failures:

- `advect3d`
- `corcol3`
- `dct`
- `fusion1`
- `gemver`
- `multi-stmt-stencil-seq`
- `mxv`
- `pca`

These split into two main buckets, and one of them splits again:

### A. Raw Pluto result is already validator-accepted

For these cases:

- `corcol3`
- `dct`
- `gemver`
- `mxv`
- `pca`

the raw source/exported scop and raw Pluto `after.scop` satisfy:

- `polcert(before, after) = EQ`

So these are still importer/view problems, not Pluto/source-model failures.

Further split:

#### A1. OpenScop view already matches, but source poly still fails

For:

- `corcol3`
- `dct`
- `gemver`
- `pca`

the imported scheduled poly, when re-exported to OpenScop, is already
equivalent to Pluto's raw optimized `after.scop`:

- `polcert(raw_after, imported_after) = EQ`

So for these four, the remaining failure is no longer visible in the OpenScop
projection. The mismatch is in source-side poly payload that OpenScop erases,
most likely in fields such as:

- `pi_transformation`
- the source-facing interpretation of access/instruction payload

#### A2. Leading constant schedule dimensions were still exported incorrectly

The remaining `fusion1`, `multi-stmt-stencil-seq`, and `advect3d` failures were
reduced further by comparing the **fresh** strengthened `before.scop` emitted by
`polopt --debug-scheduler` against the true C-path `beforescheduling.scop`.

The key bug was in source OpenScop export:

- source schedules whose first compact dimension was a nonzero constant
  (coming from `Seq`) were still emitted with an extra leading zero row
- C/Clan emits those as `const, dynamic, ..., tail`, not `0, const, ...`

This was fixed in `src/PolyLang.v` by making the leading zero row conditional:

- prepend a zero row only when the first compact schedule dimension is dynamic
- do **not** prepend it when the first compact dimension is already constant

This immediately restored strict-path validation on:

- `fusion1`
- `multi-stmt-stencil-seq`

and it aligned `advect3d`'s strengthened source `before.scop` with the C-path
source model at the OpenScop level.

### B. Current remaining split

After the leading-constant export fix, the remaining blockers no longer have a
single cause.

#### B1. `mxv`: complete-view valid, raw source-like view invalid

`mxv` is now the clearest representation-sensitive case.

Facts:

- strengthened source `before.scop` is already very close to the C-path one
  (same scattering family; only a duplicated parameter-only domain row remains)
- `validate(complete-before, complete-after)` succeeds
- `validate(strengthened, scheduled)` still fails with `res = false`

The strengthened raw source poly uses compact schedule:

- old: `[i; 1; j]`
- new: `[1; i; j]`

while the complete OpenScop view validates:

- old complete: `[0; i; 1; j; 0]`
- new complete: `[1; i; j]`

So the remaining problem is not Pluto itself, but that validation on the raw
compact/source-like representation is stricter than validation on the complete
OpenScop schedule view.

#### B2. `advect3d`: source model aligned, strict path now slow

For `advect3d`, after the leading-constant export fix:

- strengthened fresh `before.scop` matches the C-path `before.scop` at the
  OpenScop schedule/domain metadata level

However, strict `polopt` no longer fails quickly; it becomes slow enough that a
`timeout 15` run expires. This suggests the problem has moved from source-model
fidelity to runtime complexity in the strengthened/imported strict path.

Observed result:

- `polcert(strengthened_before_raw_scop, pluto_raw_after_scop) = EQ`
- therefore Pluto's raw optimized schedule is valid on the strengthened source model
- but strict `polopt` still fails, because the imported scheduled poly is not the same object as Pluto's raw `after.scop`

This pins the current blocker on:

- `from_openscop_like_source`

not on Pluto, and not on the strengthening pass.

## Concrete importer bug pattern

The failing path is:

- strengthened source `poly`
- `to_openscop`
- Pluto
- raw optimized `after.scop`   **(valid)**
- `from_openscop_like_source`  **(mis-decodes schedule)**
- validator sees the wrong scheduled `poly`
- `res = false`

`covcol` gives a clean witness:

- Pluto raw `after.scop` for `S1` has `SCATTERING` meta:
  - `4 11 4 3 0 2`
  - corresponding to a compact optimized schedule family `(0, i, j1, j2)`
- but `from_openscop_like_source` re-imports and re-exports it as:
  - `7 14 7 3 0 2`
  - i.e. it expands back into the old source-like skeleton

So the current importer is not preserving Pluto's optimized schedule; it is "refilling" it into the original template in a way that destroys the optimization.

## Updated interpretation

The six remaining failures are therefore **two-layer failures**:

1. Without extra parameter guards, Pluto can choose a different schedule family than the C-path one.
2. Even after strengthening restores the right guard information, `from_openscop_like_source` still mis-imports Pluto's optimized `SCATTERING`.

This is stronger and more precise than the earlier "missing parameter-only guards" diagnosis.

The `patched_after` vs `cpath_after` `NE` result should still not be overinterpreted. On `covcol`, a direct diff shows that part of the residual difference is OpenScop encoding detail rather than optimization shape:

- iterator names (`j1/j2/i` vs `$i0/$i1/$i2`)
- array identifiers in access rows
- `<arrays>` extension contents and numbering

But the importer mismatch above is real and semantic: strict `polopt` is currently not validating Pluto's raw optimized schedule, but a distorted source-like re-import of it.
