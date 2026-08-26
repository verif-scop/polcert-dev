# Diamond Tiling Paper Notes

Source PDF:

- [bondhugula-et-al2017-diamond-tiling.pdf](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/paper-local/bib/pdfs/bondhugula-et-al2017-diamond-tiling.pdf)

Companion stencil-tiling paper:

- [bandishti-pananilath-bondhugula2012-stencil-tiling.pdf](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/paper-local/bib/pdfs/bandishti-pananilath-bondhugula2012-stencil-tiling.pdf)

Paper:

- Uday Bondhugula, Vinayaka Bandishti, Irshad Pananilath
- "Diamond Tiling: Tiling Techniques to Maximize Parallelism for Stencil Computations"
- IEEE TPDS 2017

## 1. One-line takeaway

This paper's notion of diamond tiling is not "just use diamond-shaped tiles"
and it is also not "run the current default affine scheduler, then apply
ordinary tiling". Its central claim is:

- choose tiling hyperplanes so that tiled execution preserves a face of the iteration space along which all tiles can start concurrently

In the paper's formulation, diamond tiling is therefore a constrained way of
choosing tiling hyperplanes, tile schedule, and sometimes tile-size ratios so
that tiled stencil execution avoids pipelined startup and load imbalance.

The 2012 stencil-tiling paper makes the same point from a slightly earlier
angle: legal tiling hyperplanes are not enough; one must choose hyperplanes
that preserve tile-wise concurrent start.

## 2. What problem the paper is solving

Standard affine tiling frameworks can choose legal hyperplanes that are good
for locality, but still produce:

- pipelined startup
- pipelined drain
- load imbalance across processors

The paper's motivating example is a stencil where a point-space face allows
concurrent start, but the chosen tiling hyperplanes destroy that property after
tiling. In the paper's terminology:

- point-wise concurrent start may exist before tiling
- tile-wise concurrent start may be lost after tiling

So the problem is not merely legality of tiling. The problem is preserving the
"good" boundary direction for scalable parallel startup.

This is exactly why "ordinary affine + ordinary tiling" is too weak as a
description if "ordinary affine" means "whatever default affine band Pluto would
already choose". The paper's diamond mode changes that band first.

## 3. The paper's core geometric idea

The paper distinguishes:

- a face normal `f`
- tiling hyperplanes `h1, ..., hn`
- inter-tile dependences
- a tile schedule

For stencils with no communication-free parallelism, the key result is:

- tile-wise concurrent start along face `f` is enabled iff `f` lies strictly
  inside the cone formed by the tiling hyperplanes

The practical interpretation is:

- the tiling hyperplanes must "surround" the concurrent-start face in the right
  way
- otherwise one of the inter-tile dependences will block concurrent startup and
  force a wavefront/pipeline

This is the real meaning of "diamond" in the paper:

- not a single fixed shape template
- but a family of tilings whose hyperplane cone preserves concurrent start

So for this repository the right mental split is:

- ordinary tiling kernel: still floor-link tiling over affine hyperplanes
- diamond-specific step: choose a different affine midpoint/band before tiling

## 4. Why standard Pluto-style tiling can fail

The paper analyzes a case where Pluto's standard cost function chooses
hyperplanes like:

- `(1, 0)`
- `(2, 1)`

These are legal and locality-friendly, but they induce an inter-tile dependence
that blocks concurrent start along the desired face.

The paper then contrasts this with a better pair such as:

- `(2, -1)`
- `(2, 1)`

The important point is:

- both choices are legal
- but only the second choice preserves tile-wise concurrent start

So diamond tiling is not about making an illegal tiling legal. It is about
choosing among already-legal hyperplanes using an extra concurrent-start
criterion.

## 5. Theorem-level picture

The paper builds the story in three steps.

### 5.1 Point-wise concurrent start

A face with normal `f` allows point-wise concurrent start when all dependences
cross that face positively.

For constant dependence vectors `d`, the condition is:

- `f . d >= 1`

This is a property of the original iteration space, before tiling.

### 5.2 Tile-wise concurrent start

Once the program is tiled, there is a new tile space and a new set of
inter-tile dependences.

The paper's first main result is:

- tile-wise concurrent start along `f` holds iff the outer tile schedule is in
  the same direction as `f`

So preserving concurrent start is a statement about the tile schedule, not only
about tile shape.

### 5.3 The cone condition

The second main result is:

- tile-wise concurrent start along `f` holds iff `f` is a strict conic
  combination of all chosen tiling hyperplanes

This gives a concrete synthesis condition for choosing tiling hyperplanes.

## 6. The paper's synthesis algorithm

The paper proposes a modification of Pluto's hyperplane selection.

High-level algorithm:

1. Run the usual Pluto hyperplane search.
2. Find a face `f` that allows point-wise concurrent start.
3. Keep the first `n-1` hyperplanes, but ensure they are linearly independent
   of `f`.
4. Replace one hyperplane with a special "cone complement hyperplane".
5. Solve an ILP so that `f` becomes a strict conic combination of the chosen
   hyperplanes.

The cone-complement hyperplane is the new ingredient. It is chosen so that:

- the final band of hyperplanes is still legal
- the final band is still linearly independent
- the concurrent-start face lies strictly inside the cone of the hyperplanes

This is a direct paper-backed reason not to say "diamond is just ordinary
tiling". The paper changes the affine hyperplane set itself.

The paper gives both:

- a single-statement formulation
- a multi-statement band-level formulation

The multi-statement version is especially relevant to Pluto and to PolCert.

## 7. Full versus partial diamond tiling

This is one of the most important distinctions in the paper.

### 7.1 Full diamond tiling

Full diamond tiling tries to preserve concurrent start along the entire
concurrent-start face.

This gives:

- maximal asymptotic tile-level parallelism

But it also gives:

- more complex tile geometry
- less regular loop width inside the tile
- potentially worse single-thread/vectorization behavior

### 7.2 Partial or lower-dimensional diamond tiling

The paper explicitly advocates a weaker but often more practical version:

- only impose the concurrent-start cone condition on the first few
  hyperplanes

This gives:

- fewer dimensions of concurrent startup
- often enough parallelism for shared-memory multicore
- more freedom to choose remaining tile dimensions for width, prefetching, and
  vectorization

This is directly relevant to the local Pluto options:

- `--diamond-tile` should be understood as the default, not-fully-dimensional
  concurrent-start mode
- `--full-diamond-tile` corresponds to the full-dimensional variant

The local Pluto source confirms this split:

- when `fulldiamondtile` is off, the implementation only enables concurrent
  start along one dimension
- when `fulldiamondtile` is on, it uses the whole band

## 8. Diamond tiling is not the same as intra-tile execution order

The paper separates two concerns:

- the hyperplanes that shape tiles and preserve concurrent start
- the schedule used to scan points inside a tile

This is critical.

The paper explicitly says:

- diamond hyperplanes can be used only to shape the tile
- inside the tile, one can still use the standard Pluto hyperplanes for point
  order

This explains the examples where:

- tile-space coordinates look like diamond-friendly combinations such as
  `t - i`, `t + i`
- but the inner point loops are reordered back to hyperplanes chosen for good
  locality/vectorization

For PolCert, this is an especially useful separation:

- tile shape and tile-space legality belong to the tiling witness
- intra-tile point order belongs to schedule import / schedule validation

So the sequential-correctness story can still reuse ordinary tiling after a
diamond-aware midpoint, even though the full paper-level performance story
cannot be reduced to ordinary tiling alone.

## 9. Tile sizes still matter

The paper is careful not to overclaim.

The hyperplane cone condition is about orientation, but not by itself about the
final tile-size choice. The paper notes:

- certain tile sizes or tile-size ratios can destroy concurrent start
- for one-dimensional concurrent start, equal tile sizes in the first two
  dimensions preserve concurrent start

This matters because "diamond tiling" in the full paper sense is not just:

- choose affine hyperplanes

It is:

- choose hyperplane orientations
- choose a compatible tile schedule
- choose compatible tile sizes or ratios

For our current PolCert setting, this means:

- a witness that only records `parent = floor(phi / T)` is sufficient for
  tiling correctness
- it is not sufficient to certify the stronger paper-level claim of concurrent
  start / load balance

## 10. What the paper means by diamond tiling in concrete examples

For the 2D heat stencil, the paper gives:

- full concurrent start: `T(t,i,j) = (t+i, t+j, t-i-j)`
- partial concurrent start: `T(t,i,j) = (t-i, t+i, t+j)`

The crucial observation is:

- the "diamond" part is the use of combinations like `t-i`, `t+j`, `t-i-j`
- these are affine hyperplanes chosen to preserve concurrent start

After strip-mining, the tile iterators are just floors of those affine
hyperplanes.

So from a witness-centered viewpoint, the resulting tile links are still of the
form:

- `fk = floor(phi / T)`

where `phi` is now a skewed affine expression rather than a raw loop index.

## 11. What this changes in our understanding of Pluto's diamond mode

The right mental model is:

1. Pluto first finds an affine schedule band.
2. If diamond mode is enabled and useful, Pluto changes the band so that a
   concurrent-start face lies in the cone of the selected hyperplanes.
3. Pluto then tiles those hyperplanes.
4. Pluto may then choose a tile schedule and a separate intra-tile point order.

So diamond tiling is not:

- a tiny post-pass after ordinary tiling

And it is also not:

- a completely different semantic notion of tiling

It is:

- an affine hyperplane selection strategy for choosing which directions get
  tiled so that tile startup is concurrent instead of pipelined

Equivalently:

- not "default affine + ordinary tiling"
- but "diamond-aware affine band selection + ordinary tiling"

## 12. Direct implications for PolCert

### 12.1 What does not need to change

If PolCert continues to use the current phase-aligned split:

- `before -> mid`: checked affine scheduling
- `mid -> after`: checked tiling

then the tiling witness model does not need a diamond-specific datatype.

Why:

- by the time we are in the `mid -> after` phase, the skewed/diamond-friendly
  hyperplanes are already present in `mid`
- the tiling step still only needs to explain added tile iterators as
  `floor(phi / T)` links

This matches the current witness-centered formalization very well.

### 12.2 What diamond means in the current proof architecture

Within the current PolCert architecture, supporting diamond tiling should mean:

- allow `phi` in tile links to be arbitrary affine expressions from the `mid`
  schedule space
- keep the checked `mid -> after` tiling relation exactly in the current
  witness-centered style
- continue to compare `retiled_old(mid, ws)` against `after` using the general
  validator

In other words:

- the diamond-specific intelligence belongs in the affine scheduling phase
- the tiling phase remains ordinary floor-link tiling over more general affine
  hyperplanes

### 12.3 What would require stronger formalization later

If we later want to certify the full paper claim, not just tiling-derived
refinement, then additional witness material would be needed for:

- the concurrent-start face
- the tile schedule direction
- the tile-size ratio constraints needed to preserve concurrent start

That is a stronger goal than the current checked tiling relation.

## 13. Practical summary for this repository

For the repository's current goals, the most stable interpretation is:

- diamond tiling is diamond-aware affine scheduling plus ordinary affine
  floor-link tiling
- the new semantic burden for the tiling checker is small
- the larger semantic burden sits in any future attempt to certify
  concurrent-start parallelism itself

This is why, in the current PolCert framing, it is more accurate to say:

- diamond is not a new tiling semantics

and instead say:

- diamond is a different way of choosing the affine hyperplanes that are later
  tiled

That viewpoint is fully consistent with both:

- the paper's algorithm
- the current witness-centered `mid -> after` design in PolCert
