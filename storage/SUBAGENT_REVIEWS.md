# Subagent Review Notes

Date: 2026-06-04

## Universal Taxonomy Review

Reviewer conclusion:

- The theorem-facing design should be simple:
  `final State.eq` becomes `final public vars contents equal`.
- `MemCell`, concrete loop indices, and concrete CInstr examples should not
  appear in the top theorem API.
- Complexity belongs in pass-specific witnesses and validators.

Recommended theorem shape:

```coq
Record public_interface := {
  public_source_vars : list Var;
  public_target_exports : list Var;
  private_target_vars : list Var;
  var_shapes : Var -> Shape;
}.

Definition public_output_view_eq cert st_src st_tgt : Prop :=
  logical_public_interface_contents_equal cert st_src st_tgt.

Theorem validator_sound :
  forall src tgt cert,
    validator_checkb src tgt cert = true ->
    semantic_refinement_between
      (public_input_view_eq cert)
      (public_output_view_eq cert)
      src tgt.
```

Main warning:

- A concrete theorem about one loop is a smoke test, not the storage-validator
  top theorem.

## Tool / OpenScop Review

Reviewer conclusion:

- Candl scalar expansion is the strongest actual storage-ish external evidence:
  scalar `t` becomes indexed `t[i]` in OpenScop access metadata, and dependence
  count drops.
- Pluto `--scalpriv` exists, but in this source it is a Candl
  dependence-analysis mode, not a complete C storage rewrite.
- OpenScop `private_vars` is loop/codegen metadata, not a storage rewrite
  witness.
- Layout, reuse, scratchpad, contraction, and double buffering are not found as
  directly runnable Pluto storage rewrite passes in the current source.

Design implication:

- Use Pluto/Candl evidence where real, especially Candl `-scalexp`.
- Use the `storage/` toy tools and standalone validator to calibrate the wider
  taxonomy.
- Do not claim Pluto storage coverage unless a transformation is observed in
  generated OpenScop/C and then validated against the public-vars endpoint.

## Universal Representation Review

Reviewer conclusion:

- The public-vars endpoint is right, but it must be a logical public view, not
  raw same-name target/source variable equality.
- `repr : logical_observation -> target_storage_observation` is too weak if it
  is treated as one direct cell map.
- The internal representation witness should have variants for direct layout,
  copy boundary, reuse interval, version selection, reduction merge, and commit
  sets.

Specific risks:

- Layout remap may export source logical `A` through target physical `A_pad`.
- Folding and inter-array reuse require non-injective physical maps plus
  lifetime intervals, producer/consumer events, reuse or kill events, and final
  boundary projection.
- Versioning and double buffering need explicit read selectors and phase
  transitions.
- Reduction privatization needs chunk partition, merge tree, and algebraic laws;
  pointwise storage equality is not enough.
- Overlap and halo need duplicate target computations plus a commit set that
  exactly covers public live-outs.

Design implication:

- Keep `public_output_view_eq cert source_final target_final` as the theorem
  endpoint.
- Put cell/event/phase/version/merge details in certificate witnesses and
  checker obligations.
- Extend generated survey artifacts with required witness fields for each
  transformation.

## Scratchpad Evidence Review

Reviewer conclusion:

- A toy OpenScop skeleton plus structured witness summary is a sensible next
  evidence step for `scratchpad_packing` and `scratchpad_copy_out`.
- It should be described as certificate-shape evidence, not as Pluto support and
  not as OpenScop proving semantic equivalence.

Recommended split:

- `scratchpad_packing`: copy public live-in `B[kk+k]` to private `Bp[k]`, then
  compute public `C[kk+k]` from `A[kk+k]` and `Bp[k]`.  No copy-out is needed
  because the public output is written directly.
- `scratchpad_copy_out`: copy public `A[kk+k]` to private `Al[k]`, update
  `Al[k]`, and commit back to public `A[kk+k]`.  The copy-out is
  correctness-critical.

Required caveats:

- OpenScop access relations encode reads and writes, but copy-in/copy-out roles
  come from the sidecar witness summary.
- Scratchpad buffers such as `Al` and `Bp` are private target storage and are
  excluded from the final public logical view.
- Correctness obligations include local read coverage, live-in copy coverage,
  live-out copy coverage, exact public commits, in-bounds local indices, and
  guarded boundary tiles.
- The skeleton is evidence for validator certificate shape only.  Soundness
  still requires checked obligations connected to `public_output_view_eq`.

## Reuse/Folding Evidence Review

Reviewer conclusion:

- A toy OpenScop skeleton plus structured reuse/folding witness is the right
  evidence shape for `array_contraction`, `inter_array_reuse`, and
  `double_buffering`.
- The `.scop` files should show folded or shared physical storage, while the
  JSON sidecar carries the actual correctness witness.
- This must not be described as Pluto support or as OpenScop itself carrying
  the correctness proof.

Required witness structure:

- public logical view names source-level observations, not target buffer names;
- folded buffers such as `A2` and `Buf` are private target storage unless
  exported by `boundary_projection`;
- `valid_interval` is per logical value, not per array;
- every target read is tied to a still-valid producer event;
- `kill_or_reuse_event` records the physical slot switch from one logical value
  to another;
- `boundary_projection` covers each public live-out, including final parity rows
  and final double-buffer phase;
- double buffering includes initialization, cur/next read/write roles, swap
  transition, and final selector.

Required caveats:

- OpenScop access relations encode reads/writes/schedules, not logical value
  ids, lifetimes, kill/reuse events, or boundary projection.
- Non-injective physical maps are legal only when simultaneous-live logical
  values do not collide.
- Inter-array reuse also needs element type, extent, alignment, and byte-range
  compatibility.
- Double buffering must check that each step reads `cur` and writes `next`; final
  equality alone cannot hide a wrong phase update.
- Missing final projection, reuse before last consumer, odd final parity, and
  bad `cur`/`next` roles are negative cases the validator must reject.

## Advanced Storage Evidence Review

Reviewer conclusion:

- A toy OpenScop skeleton plus validator-facing JSON witness is the right
  evidence shape for `array_expansion_versioning`, `reduction_privatization`,
  `overlapped_tiling`, and `storage_view_composition`.
- The `.scop` files should only carry access/schedule shape.  The JSON sidecar
  must carry statement roles, selectors, merge trees, commit sets, composition
  observables, checked obligations, and negative cases.
- The endpoint remains `public_output_view_eq`, not raw state equality and not
  same-name variable equality.

Required witness structure:

- versioning: definition-to-version map, produced versions, read selectors,
  final selector, copy-out/projection, version bounds, and negative selectors;
- reduction privatization: carrier/operator/identity, source reduction
  semantics, chunk partition, accumulator init, contribution map, local fold
  order, merge tree, and operator laws;
- overlapped tiling: source instance domain, duplicate target domain,
  duplicate projection, halo region and closure, commit set, commit map, exact
  cover, private duplicate storage, and boundary guards;
- view composition: stages, source-to-mid view, mid-to-target view,
  intermediate interface, stage witness refs, composed output view,
  compatibility, and private monotonicity.

Required caveats:

- This is toy OpenScop-shaped evidence, not Pluto support.
- OpenScop access relations encode reads/writes/schedules only; JSON supplies
  roles, selectors, merge trees, commit sets, and composition observables.
- Private versions, accumulators, halo buffers, and intermediate temps are
  excluded from final public observation unless explicitly exported.
- Final equality alone is too weak: every target read contributing to public
  output must be justified by produced-version, halo closure, reduction
  contribution, or composed-witness evidence.
- Negative cases should stay close to the witness schema because these are the
  places a weak universal validator would accidentally accept.

## Private Protocol Evidence Review

Reviewer conclusion:

- A toy OpenScop-shaped skeleton plus validator-facing JSON witness is the right
  way to cover `private_copy_boundary`, `private_access_local_instantiation`,
  and `scalar_promotion`.
- The `.scop` skeleton should only show reads/writes/schedules.  JSON must
  supply copy roles, private declarations, symbolic access instantiation,
  scalar load/update/store-back protocol, and alias/clobber exclusions.
- The theorem endpoint remains `public_output_view_eq`; copy/load/store/alias
  details stay inside internal witness obligations.

Required witness structure:

- private copy boundary: copy-in pairs, copy-out pairs, value relations,
  private storage declarations, compatibility, copy-in dominance, copy-out
  coverage, and commit uniqueness;
- private access instantiation: symbolic private accesses, instantiation map,
  domain guard, target cell declaration, deterministic access function,
  use-def relation, and live-interval compatibility for aliases;
- scalar promotion: promoted logical cell, private scalar, load event, update
  events, store-back event, valid interval, public-live-out flag,
  alias/clobber exclusion, and whether the scalar is per-iteration or carried.

Required caveats:

- This is toy OpenScop-shaped evidence, not Pluto support.
- Private cells/scalars are excluded from final public observation unless
  explicitly copied or stored back.
- Final equality alone is too weak; every private read and public commit must be
  justified.
- Alias/clobber exclusion is a real proof obligation for scalar promotion, not
  prose.
- Thin negative coverage for scalar promotion should be strengthened with
  missing load, missing store-back, clobber, wrong-index store-back, stale use,
  overlapping scalar interval, and scalar escape cases.
