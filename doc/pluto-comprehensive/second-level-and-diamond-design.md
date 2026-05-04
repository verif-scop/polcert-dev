# Design for Second-Level and Diamond Tiling

This note records the recommended design for supporting `--second-level-tile`
and diamond tiling in the current PolCert witness-centered pipeline.

For the deeper `PolOpt`-facing design, especially the `.v`-level discussion of
phase artifacts, midpoint import, and theorem impact, see:

- [polopt-second-level-diamond-support.md](./polopt-second-level-diamond-support.md)

The goal here is not to restate Pluto's algorithms in full. The goal is to pin
down:

- what the proof object should be
- what should remain outside the trusted core
- which parts need a new external pipeline contract versus only a better
  witness/import path

This note is intentionally narrower than the more exploratory
[tiling-validation-design.md](./tiling-validation-design.md) and the more
paper-facing [diamond-tiling-paper-notes.md](./diamond-tiling-paper-notes.md).

## 1. Scope and Non-Goals

This design assumes the current verified pipeline shape:

```text
before
  -> checked affine phase
mid
  -> checked tiling phase
after
  -> current_view_pprog
  -> existing affine codegen chain
```

The scope of this note is:

- sequential semantic correctness
- reuse of the current witness-centered checked tiling route
- minimal disturbance to the current Coq proof boundary

This note does not try to certify:

- parallel annotations
- concurrent-start optimality
- maximal tile-level parallelism
- load-balance claims from the diamond tiling paper

Those stronger properties may matter for Pluto's optimization rationale, but
they are not required to validate that the transformed sequential program
refines the source.

## 2. Current Fixed Points We Should Preserve

Several parts of the current design are already in the right shape and should
not be replaced.

### 2.1 The checked tiling proof boundary is `mid -> after`

The current verified route is deliberately phase-aligned:

- affine legality is checked on `before -> mid`
- tiling is checked on `mid -> after`

This matters because it keeps tiling-specific proof obligations out of the
older affine validator.

### 2.2 The semantic core is already witness-centered

The checked tiling core does not need Pluto options such as "basic tiling",
"second-level tiling", or "diamond tiling" as separate theorem constructors.

The semantic object is already:

- a statement-level witness
- containing a list of affine floor-links
- checked against the canonical tiled program structure

This is the right abstraction level to keep.

### 2.3 `eval_tile_links` already supports dependent links

The current Coq witness evaluator is prefix-based:

```text
eval_tile_links prefix point params links
```

Each new parent may depend on:

- the original point iterators
- parameters
- earlier recovered tile parents

So the core model already supports link chains such as:

```text
fk3 = floor((2*t + i) / 32)
fk0 = floor(fk3 / 8)
```

This means second-level tiling is not blocked by a lack of expressive power in
the core witness datatype.

### 2.4 The canonical tiled skeleton is the right import boundary

The checked pipeline already does the structurally right thing:

1. infer a witness from `(mid.scop, after.scop)`
2. build the canonical tiled skeleton from `(mid, witness)`
3. import only Pluto's final schedule over that skeleton
4. run the checked tiling validator

This design keeps raw OpenScop quirks at the boundary instead of proving
properties about arbitrary imported after-programs directly.

## 3. One Unifying Design Principle

Both second-level tiling and diamond tiling should be treated as instances of
the same general principle:

- the proof core reasons about an ordered list of affine floor-links
- Pluto-specific option families stay outside the core

In other words:

- `--second-level-tile` is not a new semantic relation
- `--diamond-tile` is not a new tiling relation
- `--full-diamond-tile` is not a third theorem family

They are different producer behaviors that should all land in the same checked
contract whenever possible.

## 4. Second-Level Tiling

## 4.1 What is special about it

Second-level tiling is the first common Pluto case where:

- newly introduced tile parents may depend on other newly introduced tile
  parents
- the dependency order may differ from the raw iterator order seen in
  `after.scop`

So the important distinction is not "one level versus two levels". The
important distinction is:

- independent links versus dependent links

Pluto currently exposes only a boolean `--second-level-tile`, but PolCert
should not hard-code "at most two levels" into the proof object. The right
semantic target is an arbitrary acyclic ordered link list.

## 4.2 Recommended proof-facing model

The proof-facing witness for a statement should continue to be:

- original point dimension
- a list of tile links

But the well-formedness story should be understood more explicitly than before.

For each link in order:

- `tile_size > 0`
- the parent is fresh
- the affine expression may mention only:
  - original point iterators
  - parameters
  - earlier tile parents

Conceptually, the witness list is a topological order of a dependency DAG.

This is the correct generalization for:

- single-level rectangular tiling
- skewed tiling
- second-level tiling
- future multi-stage producers, even if Pluto never exposes them directly

## 4.3 Why the current executable gap appears

The current container-side prototype still has a producer-side mismatch:

- raw link candidates are collected from `after.scop`
- then sorted lexicographically
- but the contract checker expects dependency order

That is why a raw second-level case can fail with an "unresolved iterators"
error even though the Coq witness model itself can express the case.

So the blocker is not the theorem boundary. The blocker is witness
canonicalization at the untrusted import layer.

## 4.4 Separate two different orders

For second-level tiling, we should explicitly distinguish:

1. raw added-dimension order in Pluto's `after.scop`
2. canonical dependency order used by the witness evaluator

Those two orders may coincide for simple tiling. They need not coincide for
second-level tiling.

This distinction is the key design point.

If we force them to be identical, second-level support becomes brittle.
If we keep them separate, the core witness semantics can remain simple.

## 4.5 Recommended engineering split

The recommended split is:

### Untrusted producer / importer side

1. Recover raw link candidates from `after.scop`.
2. Build the dependency graph among candidate parents.
3. Topologically sort the links into canonical dependency order.
4. Derive the permutation from Pluto's raw added-dimension order to the
   canonical order.
5. Apply that permutation when importing Pluto's final schedule over the
   canonical tiled skeleton.

### Checked kernel side

1. Receive the canonicalized witness.
2. Reject any witness whose ordered links still contain unresolved
   dependencies, non-fresh parents, or non-positive tile sizes.
3. Reuse the existing tiling relation and checked validator unchanged, or as
   close to unchanged as possible.

This keeps the hard part of second-level support outside the trusted core while
preserving a small proof kernel.

## 4.6 The important import consequence

The current canonical tiled skeleton is built from the witness order, not from
Pluto's raw iterator names.

That means second-level support is not just "change the sorter".

If Pluto's raw `after.scop` order differs from canonical dependency order, then
the schedule imported from `after.scop` must be aligned to the canonical order.

So the real producer-side task is:

- dependency-aware witness canonicalization
- plus a raw-order to canonical-order bridge for schedule import

Without that bridge, second-level support remains partially accidental.

## 4.7 Theorem impact

The main theorem story should remain:

- `check_pprog_tiling_sourceb` proves the structural tiling relation
- `checked_tiling_validate` closes the schedule bridge through `retiled_old`

The only proof-facing strengthening likely needed is to make the ordered-link
contract more explicit in the witness well-formedness layer, rather than
leaving it only as an executable-side convention.

That is still a refinement of the existing witness-centered design, not a new
formalization family.

## 4.8 Recommended rollout for second-level

1. Keep the Coq witness datatype unchanged.
2. Make dependency order an explicit proof-facing contract.
3. Add producer-side canonicalization that computes a topological order.
4. Add the raw-order to canonical-order schedule bridge.
5. Only then advertise second-level support on the main checked path.

## 5. Diamond Tiling

## 5.1 What is special about it

For sequential correctness, diamond tiling is not special because it creates a
new kind of tile link.

It is special because Pluto does not merely tile the existing band. It first
changes which affine hyperplanes are being tiled.

At a high level, diamond support involves:

- choosing a concurrent-start-friendly face or direction
- replacing or skewing hyperplanes in the first band
- only then applying tiling over that modified affine band

So relative to the current PolCert pipeline, the real issue is not "can the
tiling witness express `floor((2*t-i)/32)`?" It can.

The real issue is:

- where the pre-tiling affine change should live in the verified pipeline

## 5.2 Recommended proof boundary

If we want diamond support while staying consistent with the current
formalization, the right boundary is:

```text
before
  -> mid_diamond
  -> after
```

with the meaning:

- `before -> mid_diamond`
  - checked affine scheduling phase
  - includes any diamond-specific hyperplane replacement or skew
- `mid_diamond -> after`
  - checked tiling phase
  - uses the same affine floor-link witness framework as ordinary tiling

Under this split, diamond tiling is not a new tiling theorem. It is:

- a different kind of affine midpoint
- followed by ordinary checked tiling over that midpoint

It is important not to compress this into the misleading phrase "affine +
ordinary tiling" if "affine" means the default midpoint that Pluto would have
chosen anyway. The paper-backed statement is narrower:

- not default affine + ordinary tiling
- but diamond-aware affine midpoint + ordinary tiling

## 5.3 Why simply enabling `--diamond-tile` is not enough

The current external phase pipeline is arranged as:

- affine-only scheduling
- then tile-only transformation over an identity schedule

That structure works for ordinary tiling because the tiling phase is really
"tile the already-chosen band".

Diamond tiling is different:

- the diamond logic participates in choosing or replacing hyperplanes before
  tiling
- so it cannot be modeled as a pure post-midpoint tiling flag unless the
  external producer exposes that intermediate state

Therefore, "remove `--nodiamond-tile` from the current tile-only flags" is not
a complete design.

## 5.4 Recommended external contract

The clean design is to require an explicit diamond-aware midpoint artifact.

For example, the external pipeline should be able to provide:

- `mid_affine.scop`
  - the ordinary affine midpoint when diamond is off
- `mid_diamond.scop`
  - the pre-tiling diamond/skew midpoint when diamond is on
- `after_tiled.scop`
  - the tiled result after tiling over that midpoint

PolCert then keeps its existing shape:

1. import and validate the midpoint as an affine program
2. infer a tiling witness from `(mid_*, after_tiled)`
3. build the canonical tiled skeleton from `(mid_*, witness)`

This is the right place to stop for sequential correctness. The stronger paper
claims about concurrent start, load balance, or maximal tile-level parallelism
remain an extra layer above this proof boundary.
4. import the final schedule over that skeleton
5. run the existing checked tiling validator

This is the lowest-disturbance way to support diamond.

## 5.5 Why we should not fold diamond into a stronger tiling checker

There is a tempting but much heavier alternative:

- infer both the diamond hyperplane replacement and the tiling witness from
  `(before, after)`
- then build a new composite checker that proves both at once

This would be a mistake for the current project stage.

It would:

- blur the affine and tiling proof boundaries again
- force the tiling checker to reason about a larger transformation class
- duplicate work that the current affine validator already knows how to handle

So the design rule should be:

- do not teach the tiling kernel to prove diamond skew
- instead, expose the skewed affine midpoint and validate it with the affine
  checker

## 5.6 Partial diamond versus full diamond

For the current sequential-correctness target, the distinction between
`--diamond-tile` and `--full-diamond-tile` should not produce two different
proof objects.

They differ primarily in the affine midpoint:

- partial diamond changes enough hyperplanes to preserve only part of the
  concurrent-start structure
- full diamond changes a fuller band so the whole concurrent-start face is
  preserved

But once the midpoint is fixed, the tiling witness remains the same kind of
object:

- a list of affine floor-links over the chosen midpoint hyperplanes

So partial and full diamond should be treated as:

- different producer modes for the affine midpoint
- one shared checked tiling relation for `mid -> after`

## 5.7 What remains out of scope

Even after diamond is integrated into the pipeline, the following are still
outside the current theorem unless explicitly added later:

- the cone-condition reasoning from the paper
- certification of concurrent start
- certification of maximal tile-level parallelism
- certification of load balance
- tile-size-ratio performance claims

Those are stronger optimization properties, not necessary preconditions for the
current sequential refinement theorem.

## 5.8 Recommended rollout for diamond

1. Keep the current tiling witness datatype unchanged.
2. Introduce a diamond-aware midpoint contract in the external pipeline.
3. Validate `before -> mid_diamond` with the affine validator.
4. Reuse the ordinary checked tiling route on `mid_diamond -> after`.
5. Support partial diamond first.
6. Treat full diamond as a stronger producer mode over the same proof
   interface.

## 6. Interaction Between Second-Level and Diamond

These two extensions should compose cleanly if the proof object stays at the
right abstraction level.

The combined case should still be read as:

- an affine midpoint chooses the hyperplanes
- an ordered affine floor-link witness tiles those hyperplanes

So if a future producer emits "second-level diamond tiling", the semantic core
should still be:

- an affine midpoint
- plus an ordered link list

The extra complexity would again live in:

- producer-side canonicalization
- raw-order versus canonical-order alignment

not in a new theorem family.

## 7. Recommended Documentation and Engineering Policy

To keep the project coherent, I recommend the following policy:

1. Document Pluto feature names as producer modes.
2. Document PolCert proof objects as witness-centered relations.
3. Do not let CLI option names dictate theorem structure.
4. When a new Pluto mode appears, first ask:
   - is this a new affine midpoint?
   - or merely a new family of affine floor-links?
5. Only introduce a new verified checker when neither existing affine
   validation nor existing tiling validation can express the case cleanly.

Under that policy:

- second-level tiling is mainly a witness-order and import-alignment problem
- diamond tiling is mainly an external phase-boundary problem

Neither requires abandoning the current witness-centered checked tiling design.

## 8. Prototype Status

There is now a small OCaml design prototype for exactly these two ideas:

- [tools/tiling_ocaml/design_validator_prototype.ml](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/design_validator_prototype.ml)
- [tools/tiling_ocaml/design_validator_core.ml](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/design_validator_core.ml)

Its job is deliberately narrow:

- for second-level tiling, test whether a raw added-dimension order can be
  reconciled with a dependency-ordered canonical witness by a schedule bridge
- for diamond tiling, test whether requiring an explicit midpoint is enough to
  reduce the tiling part back to ordinary affine floor-links

The current synthetic fixture results are:

- second-level positive case: PASS
  - raw order `[f0, f1]`
  - canonical witness order `[f1, f0]`
  - the prototype reconstructs the expected canonical schedule after
    raw-to-canonical reordering
- second-level cycle case: FAIL
  - rejected because the links cannot be topologically ordered
- second-level bad-schedule case: FAIL
  - rejected because the raw-order to canonical-order schedule bridge does not
    reconstruct the claimed canonical schedule
- diamond midpoint case: PASS
  - accepted as "checked affine midpoint + ordinary affine floor-link tiling"
- diamond-without-midpoint case: FAIL
  - rejected immediately because no midpoint hyperplane set is provided
- diamond-missing-hyperplane case: FAIL
  - rejected because one tile link cannot be justified by any midpoint
    hyperplane

This does not prove the final theorem, but it is a useful sanity check that the
recommended proof boundaries are operational rather than purely aspirational.

## 9. Docker Checkpoint: Real Pluto Diamond Artifacts

On 2026-03-26, the first real Docker checkpoint for diamond tiling matched the
recommended proof boundary above.

The key observations came from Pluto's built-in stencil fixtures:

- `/pluto/test/jacobi-1d-imper.c`
- `/pluto/test/diamond-tile-example.c`

using commands of the form:

```sh
pluto --silent --dumpscop --tile --noparallel --nointratileopt \
  --nounrolljam --noprevector --diamond-tile <case.c>
```

### 9.1 The ordinary tiling witness machinery already recognizes the diamond links

For both real cases, PolCert's current witness extractor and OpenScop-side
tiling validator already succeed on `before -> after`:

- `./polopt --extract-tiling-witness-openscop before.scop after.scop`
- `./polopt --validate-tiling-openscop before.scop after.scop`

For `jacobi-1d-imper`, the extracted links were:

- `fk0 = floor((2*t - i) / 32)`
- `fk1 = floor((2*t + i) / 32)`

and similarly offset versions for the second statement.

For `diamond-tile-example`, the extracted links were:

- `fk0 = floor((t + i) / 32)`
- `fk1 = floor((t - i) / 32)`

This is strong evidence that the current affine floor-link witness language is
already expressive enough for the tiling part of sequential diamond tiling.

### 9.1.1 What this does and does not mean semantically

This result should be read precisely.

What the current witness language can express is:

- an ordered list of tile parents
- where each parent is computed as a floor of an affine form over the current
  midpoint coordinates
- for example, non-axis-aligned links such as
  `floor((2*t - i) / 32)` or `floor((t - i) / 32)`

So for the proof boundary

```text
mid_diamond
  -> after
```

the current tiling witness is already the right kind of semantic object.

What it does not express by itself is the full meaning of diamond tiling from
the original schedule:

- it does not prove how Pluto chose or replaced the diamond hyperplanes
- it does not certify concurrent-start or load-balance properties
- it does not turn `before -> after` into a single checked tiling theorem

So the right interpretation is:

- yes, the witness/mapping design is expressive enough for the tiling step of
  diamond
- no, it is not by itself a complete proof object for the whole diamond
  transformation

### 9.2 The missing piece is still the midpoint artifact

Pluto's `--dumpscop` output on these cases only gave the familiar pair:

- `*.beforescheduling.scop`
- `*.afterscheduling.scop`

The debug logs clearly showed a producer-side diamond midpoint, for example:

- `Transformations before concurrent start enable`
- `Transformations after concurrent start enable`

but Pluto did not dump that midpoint as a separate `.scop` artifact.

So the current external producer still does not hand PolCert an explicit
`mid_diamond.scop`.

### 9.3 The current phase-aligned readscop pipeline cannot synthesize diamond afterwards

Trying to retrofit diamond as a tile-only phase on the ordinary `before.scop`
did not work.

In particular, a command of the form:

```sh
pluto --readscop --identity --tile --noparallel --diamond-tile before.scop
```

reported:

- `Outermost tilable bands: 0 bands`

That is exactly the expected failure mode if diamond is not a post-midpoint
tiling flag but rather part of midpoint construction itself.

Likewise:

```sh
pluto --notile --noparallel --diamond-tile case.c
```

did not enter the diamond path at all, so it is not a usable way to dump
`mid_diamond`.

### 9.4 Resulting implementation consequence

These real runs strengthen the design conclusion:

- the checked tiling relation is probably not the first blocker
- the first blocker is the lack of an explicit producer-side
  `mid_diamond` artifact
- therefore the next implementation step should be on the
  scheduler/orchestration boundary, not inside the Coq tiling kernel

### 9.5 Current executable status after midpoint dumping was added

That producer-side blocker is now partially removed in the prototype:

- Pluto was patched to dump:
  - `*.beforescheduling.scop`
  - `*.midtransform.scop`
  - `*.afterscheduling.scop`
- PolCert now has an explicit experimental diamond route and a dedicated
  regression target:
  - `./polopt --diamond-tile file.loop`
  - `./polopt --validate-affine-openscop before.scop mid.scop`
  - `make test-diamond-tiling-suite`

The resulting fixture matrix splits into three categories.

True diamond midpoint change, with OpenScop-side validation passing:

- `diamond-tile-example.c`
- `fdtd-2d.c`
- `heat-3d-imperfect.c`
- `jacobi-1d-imper.c`
- `jacobi-2d-imper.c`
- `jacobi-2d.c`

Accepted by Pluto but with no diamond-specific midpoint change relative to
`--nodiamond-tile`:

- `multi-stmt-stencil-seq.c`
- `seidel.c`

Rejected by the current Pluto/Clan frontend under this route:

- `heat-2d.c`
- `heat-2dp.c`
- `heat-3d.c`
- `jacobi-1d-mod.c`
- `jacobi-1d-periodic-even.c`
- `jacobi-1d-periodic.c`
- `jacobi-2d-17pt.c`
- `jacobi-2d-imper.par2d.c`
- `jacobi-2d-periodic.c`
- `jacobi-3d-25pt.c`
- `jacobi-3d-periodic.c`

So the project now has a real, repeatable diamond fixture suite instead of
single-case experiments.

### 9.6 What the suite proves, and what it still does not prove

The new suite proves two useful things.

First, the producer and OpenScop-side extractor are now good enough to recover
real diamond witnesses on multiple Pluto stencil examples. In particular, the
suite requires that true-diamond cases differ from the corresponding
`--nodiamond-tile` midpoint and that witness extraction exposes nontrivial
affine floor-links.

Second, it exposed the exact remaining validator gap: imperfect multi-statement
diamond cases were no longer failing because of missing midpoint artifacts or
missing witness extraction, but because the common-band checker was using the
same projected schedule for both kinds of obligation:

- cross-statement phase legality
- intra-statement self legality

That projection is good for the first job and wrong for the second one. On the
imperfect cases, it made the cross-statement pairs validate, but it also
collapsed each statement's own internal schedule and rejected `self`
dependencies.

The repaired checker now splits those obligations explicitly:

- each statement validates against its own full tiled schedule
- only cross-statement pairs use the phase-aware common-band projection

This is the first place where diamond really differs from the ordinary tiling
route in a way that matters for validation design.

For ordinary first-level tiling, the checked `mid -> after` edge is usually
well described by one common strip-mined schedule shape plus one witness
family. Diamond tiling is different in two important ways.

First, the producer-side phase structure is richer. Pluto's diamond path is
not just "ordinary tiling with a different tile shape". On the real stencil
cases it has the shape:

```text
before -> mid_diamond -> posttile_plain -> after_rescheduled
```

where:

- `before -> mid_diamond` is an affine scheduling/skew replacement step
- `mid_diamond -> posttile_plain` is the raw tiling step
- `posttile_plain -> after_rescheduled` is a further affine reschedule used to
  restore the desired intra-tile execution order

Second, imperfect multi-statement diamond cases have statement-local tiled
schedules that are still important for `self` legality, while also having
cross-statement phase offsets that are best understood only after projecting to
the common tiling band. A single projected schedule loses too much local
structure for the first job, and a purely local schedule misses the intended
phase relation for the second one.

So the current diamond validator design is intentionally split:

- `affine(before, mid_diamond)`
- `tiling(mid_diamond, posttile_plain)` with a band-aware legality split:
  - full tiled schedule for each statement's own legality
  - common-band phase projection only for cross-statement legality
- `affine(posttile_plain, after_rescheduled)`

That repair was then threaded through both executable fronts:

- `polopt --diamond-tile` now uses the band-aware checker on the real
  `mid -> posttile` edge instead of being stopped early by the old
  canonical/generic tiling gate
- `polcert` now supports the real diamond phase contract
  `before -> mid -> posttile -> after`
  instead of trying to force those cases into a three-file
  `before -> mid -> after` model

So the current state is stronger than the earlier prototype:

- explicit midpoint production exists
- explicit `posttile` production exists
- witness extraction on real diamond cases exists
- the executable checked route now accepts the formerly failing imperfect
  diamond cases
- the regression suite now checks the real four-phase contract and passes on
  all currently supported Pluto diamond fixtures

Concretely, the suite now reports full phase success on:

- `diamond-tile-example.c`
- `fdtd-2d.c`
- `heat-3d-imperfect.c`
- `jacobi-1d-imper.c`
- `jacobi-2d-imper.c`
- `jacobi-2d.c`
- `multi-stmt-stencil-seq.c`
- `seidel.c`

The remaining unsupported bucket is no longer a validator gap; it is still the
same Pluto/Clan frontend rejection bucket (`exit 8`) listed above.

### 9.7 Proof boundary of the current diamond route

The wording above needs one important qualification.

The standard ordinary theorem-backed pipeline is still intact. The existing
top-level Coq driver for the band-aware ordinary route,
`driver/PolOptBandTiling.v`, still proves correctness by composing:

- affine validation on `before -> mid`
- checked strip-mined tiling validation on `mid -> after`
- the band-permutability checker

and then discharging the final semantic preservation theorem.

The current diamond implementation follows the same proof shape, and it reuses
the same proof-oriented components:

- the affine validators on the two affine edges
- the checked tiling witness relation on `mid_diamond -> posttile_plain`
- the band schedule development in
  `src/TilingBandScheduleValidator.v`, including the strong Pluto-style
  band reasoning

But the exact current CLI wiring for diamond is not yet lifted into a matching
top-level theorem in the same way as the ordinary route.

Concretely:

- the executable `polopt --diamond-tile` / `polcert before mid posttile after`
  route is now checked and theorem-aligned
- its special band legality split is implemented in the executable bridge and
  runtime checker path
- the ordinary theorem-backed driver still refers to the older direct
  theorem-level band checker shape

So the precise claim today is:

- yes, the current diamond route is designed to preserve the same proof
  boundary as the ordinary pipeline
- yes, it is using proof-oriented validators rather than ad hoc acceptance
  rules
- no, the exact present diamond CLI path should not yet be described as fully
  theorem-backed end to end

The remaining proof task is now much narrower than before. It is no longer
"invent a new diamond theorem family". It is to lift the current four-phase
diamond bridge and its special band legality split into the top-level theorem
driver, so that the executable route and the proved route become extensionally
the same pipeline.
