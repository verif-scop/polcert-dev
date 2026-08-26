# Universal Storage Correctness Model

## The Endpoint

The universal endpoint should be stated over variables, not concrete cells:

```coq
Record storage_visibility := {
  public_vars : list ident;
  private_vars : list ident;
}.
```

The final relation is a logical public view relation:

```text
public_output_view_eq cert source_final target_final
```

Meaning:

- every scalar public variable in the logical interface has the same final
  value;
- every public array in the logical interface has the same final contents over
  its declared logical footprint;
- private variables and compiler-introduced helper storage are not observed.
- target physical storage does not have to use the same raw variable names as
  the source.

This is the intended generalization of `State.eq`.  The old theorem used full
state equality:

```text
State.eq target_final source_final
```

The storage-aware theorem should use public logical view equality:

```text
public_output_view_eq cert source_final target_final
```

This is the user-facing boundary.  A certificate may elaborate variables into
cells, events, phases, and physical storage, but the top theorem should only say
which logical variables are externally observable.

## Certificate Layers

A universal storage certificate should have four conceptual layers.

1. Visibility.

```coq
Record public_interface := {
  public_source_vars : list ident;
  public_target_exports : list ident;
  private_target_vars : list ident;
  allowed_writes : list ident;
  protected_frame_vars : list ident;
}.
```

This says what can be observed and what the optimized fragment is allowed to
modify.  `public_source_vars` names the logical source interface.  The target
may export that interface through different physical storage, so
`public_target_exports` should be interpreted through the representation
witness, not by raw variable-name equality.

2. Shapes and footprints.

```coq
Record var_shape := {
  element_type : type;
  logical_bounds : bounds;
}.

var_shapes : ident -> option var_shape
footprint  : var_shape -> finite logical cells
```

This turns a variable-level statement into the finite logical cells needed by
the checker.  It is still derived from variables; users should not have to
write `MemCell` lists in the theorem.

3. Representation.

```coq
Inductive representation_witness :=
| DirectLayout(...)
| CopyBoundary(...)
| ReuseInterval(...)
| VersionSelect(...)
| ReductionMerge(...)
| CommitSet(...).
```

The common payload is:

```text
logical_observation -> target_evidence

logical_observation =
  (source/public variable, logical index, logical time or final boundary)

target_evidence =
  target physical cell/event/phase, or copy/version/merge/commit evidence
```

This is the universal bridge for storage changes.  It may be injective,
phase-dependent, version-dependent, or justified by a merge operator, depending
on the transformation.

4. Obligations.

```text
initialized_before_read
in_bounds
no_forbidden_alias
fresh_or_lifetime_disjoint
copy_in_copy_out_covers_boundary
merge_or_commit_is_exact
```

The validator checks these obligations.  The theorem consumes only
`validator cert source target = true`.

## Theorem Shape

The top theorem should not mention a concrete loop, concrete array `B`, or a
hand-enumerated list such as `[0;1;2;3]`.

The intended shape is:

```coq
forall source target cert,
  storage_validator_check cert source target = true ->
  semantic_refinement_between
    (public_input_view_eq cert)
    (public_output_view_eq cert)
    source
    target.
```

For passes that require initialized private storage, copy-in, or live-in values,
those requirements belong in `public_input_view_eq cert` or in checked witness
obligations.  They should not become ad hoc assumptions in the top theorem.

## Internal Elaboration

Programs are written in terms of variables.  Proofs often need cells.  This
should be a private elaboration step:

```text
public var + type + bounds/domain -> finite logical footprint -> cells
```

The theorem-facing API remains variable based.  Cell-level definitions are
implementation details used by checkers and simulation lemmas.

## Representation Witnesses

One universal cell map is not enough.  Memory folding, reuse, versions, and
double buffering all require time/phase/event information.

A general internal representation should relate logical observations to target
storage events:

```text
(public variable, logical index, logical time/phase)
  represented by
(target storage variable, physical index, target event/phase)
```

Simple transformations can instantiate this with less structure:

- scalar expansion: logical temporary at instance `i` maps to private `tmp_exp[i]`;
- layout remap: logical array element `A[i]` maps to physical `A'[f(i)]`;
- contraction/reuse: logical cell maps to physical cell only during a lifetime;
- versioning: logical final cell maps to a selected target version;
- reduction privatization: final public value is justified by an algebraic merge,
  not by pointwise storage equality.

The useful common type is therefore not "source cell equals target cell".  It is
"a source logical observation is represented by target evidence".  The evidence
can be:

- a direct target cell for pure layout changes;
- a private target cell plus freshness for scalar expansion;
- a copy chain for scratchpad storage;
- a physical cell plus lifetime interval for contraction and folding;
- a version selector for array expansion and double buffering;
- a merge tree for privatized reductions;
- a designated commit event for halo or redundant computation.

This keeps memory folding expressible: the physical map may be non-injective
globally, but it must be injective over simultaneously live logical values, and
each read must be tied to the currently represented logical value.

## Reuse and Folding Witness

Folding is the stress test for the model.  It needs more than a physical index
map.  A reusable internal schema should include:

```text
logical_value_id
logical_var
logical_index
logical_time_or_definition

physical_region =
  target_var, physical_index_or_offset, extent, element_layout

producer_event
consumer_events
valid_interval
kill_or_reuse_event
conflict_class
boundary_projection
storage_compatibility
```

The validator obligations are:

- two logical values in the same conflict class may share a physical region only
  when their valid intervals do not overlap;
- every read is linked to a producer event whose value is still valid at that
  read;
- every reuse or kill event happens after the old logical value's last consumer;
- every final public logical cell is projected, selected, or copied out before
  its physical storage is reused;
- inter-array reuse checks element layout, extent, alignment, and byte-range
  compatibility, not only variable names.

This schema covers array contraction, storage folding, inter-array reuse, and
the non-current rows of double buffering.  Simpler passes can ignore most of
these fields.

## Completion Rule

A storage optimization is accepted when:

1. target execution is matched by a source execution;
2. final public logical views agree;
3. every target read used to produce public values is justified by checked
   representation, initialization, copy, merge, or use-def evidence;
4. internal storage that is not copied out is absent from final public
   observation.
