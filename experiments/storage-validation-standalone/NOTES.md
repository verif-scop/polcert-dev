# Case Notes

These notes explain the examples in `run.py`.  They should be read as
case-specific intuition, not as theorem statements.  The shared vocabulary lives
in `PRIMITIVES.md` and `../../doc/STORAGE_AWARE_VALIDATION_OVERVIEW.md`.

## `source_no_alias_abstraction`

This is not an optimization, but it is a required semantic abstraction.  The
validator assumes that distinct source arrays such as `A` and `B` denote
distinct logical blocks.  If the physical call state permits `A == B`, then the
logical footprint model itself is unsound.

## `affine_interchange`

This is the control-only baseline.  Target instances are the same `(i,j)` points
as the source, and the logical accesses are unchanged.  The validator only needs
instance bijection and dependence preservation.

## `index_set_splitting`

The target replaces one conditional domain with two subdomains.  This is still
instance-preserving, but the witness is an exact-cover partition rather than a
single affine schedule map.

## `ordinary_tiling`

Ordinary tiling introduces tile coordinates but projects each target point back
to exactly one source point.  This remains inside the current schedule-oriented
world as long as there is no overlap or recomputation.

## `scalar_privatization_expansion`

The logical computation instances are unchanged, but `tmp` is no longer one
source scalar cell.  It becomes a family `tmp_exp[i]`.  The validator checks
freshness, same-class use-def, and that the expanded storage is not observable.

## `layout_remap_padding`

The logical array domain is unchanged, but physical addresses change.  The
required witness is an address map from logical cells to physical cells.  For
ordinary layout changes it should be bijective over the allocated logical image;
for padding it is injective into a larger physical domain.

## `scratchpad_packing`

The target inserts copy-in traffic into a local buffer.  The main issue is not
schedule legality but copy protocol correctness: every local read must be
covered by a prior copy, and the local buffer must be fresh for the tile.

## `scratchpad_copy_out`

This is the update/commit version of scratchpad use.  The local buffer is first
filled from global storage, then updated locally, then copied back.  The copy-out
relation is part of correctness: local writes are not observable unless the
commit covers the intended global cells exactly once.

## `scalar_promotion`

An array cell is temporarily simulated by a scalar.  This is a local refinement:
entry load, scalar simulation of reads/writes, and exit store-back.  It fails if
there is an interfering write to the same cell inside the promoted region.

## `array_contraction`

Multiple logical values share fewer physical cells.  The storage map is
intentionally non-injective, so injectivity is the wrong validator.  The correct
condition is conflict-aware reuse: two logical values may share a physical cell
only if their live ranges do not overlap.

## `inter_array_reuse`

This is contraction across array names.  The witness must show lifetime
separation across arrays, not just within one array.  Size, type, and alignment
compatibility are side conditions.

## `array_expansion_versioning`

Expansion creates more physical versions than the source.  Each read must select
the version corresponding to the right source dynamic value.  If the original
array is live out, a copy-out/projection commits the final observable version.

## `overlapped_tiling`

The target has more computation instances than the source because halo instances
are recomputed.  The validator needs a projection from target computations to
source instances, a role distinction between `internal` and `commit`, exact
cover of committed outputs, and invisibility of internal writes.

## `reduction_privatization`

The source reduction storage is split into private partial accumulators and then
merged.  The validator needs a partition of the iteration space, fresh local
accumulators, and a merge operator whose algebraic assumptions match the claimed
semantics.  Integer addition is exact here; floating point would need relaxed or
non-bit-exact semantics.

## `double_buffering`

Double buffering is phase-structured contraction.  The key witness is not only
the modulo storage map but also phase separation: `cur` remains live while
`next` is overwritten, and `swap` implements the projection from logical time to
physical buffer identity.
