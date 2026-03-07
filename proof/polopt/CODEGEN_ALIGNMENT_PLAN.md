# CodeGen / PolOpt Alignment Plan

Date: 2026-03-06

## Scope

This note records the current proof position for connecting:

- `polygen/CodeGen.v`
- `driver/PolOpt.v`

It is intentionally a proof-planning note only. No code changes are proposed here.

## Current Theorem Interfaces

### Driver side

In `driver/PolOpt.v`, the current end of the proved driver story is:

- `scheduler'_correct`
- `Extract_Schedule_correct`

The important point is that both are phrased over:

- `PolyLang.instance_list_semantics`

So the driver proof story after extraction and validation is:

- original loop
- extracted poly program
- validated scheduled poly program
- interpreted with explicit instance-list semantics

### Codegen side

In `polygen/CodeGen.v`, the main theorem is:

- `codegen_correct`

Its conclusion is:

- `PolyLang.semantics pol st st'`

not:

- `PolyLang.instance_list_semantics pol st st'`

So the direct interface mismatch is real:

- `PolOpt` consumes `instance_list_semantics`
- `CodeGen` produces `semantics`

## The Critical Correction

The two semantics above should **not** be treated as equivalent in general.

That was the wrong first instinct.

The deeper issue is not merely theorem packaging. It is that the two semantic presentations are built on different dimension disciplines.

## Why They Are Not Equivalent

### `instance_list_semantics` is instruction-wise dimensioned

In `src/PolyLang.v`, `flatten_instrs` characterizes explicit instruction points.

For each instruction point `ip` belonging to `pi`, it requires:

- `length ip.(ip_index) = length envv + pi.(pi_depth)`

So instance enumeration is precise per instruction:

- prefix is the environment
- suffix length is exactly the instruction's own scan depth

This is the semantic style used by:

- validator
- extractor correctness
- current `PolOpt` proof chain

### `semantics` is driven by a global `dim`

Also in `src/PolyLang.v`, the wrapped `semantics` uses:

- `env_poly_semantics env (length vars) pis`

and the scanner predicate is:

- `env_scan poly_instrs env dim n p`

with the key clause:

- `is_eq p (resize dim p) && in_poly p pi.(pi_poly)`

This uses one global `dim`, not the real scan dimension of each instruction.

### Consequence on mixed-dimension programs

If one instruction has smaller real domain/scan dimension than the global `dim`, then:

- `in_poly p pi.(pi_poly)` only constrains the coordinates mentioned by that polyhedron
- the remaining coordinates below `dim` are unconstrained

So `env_scan` admits extra instance points for that instruction.

This is exactly the problem described in the old `test_many` comment:

- low-dimensional instructions acquire spurious instances
- the semantics becomes dependent on the trailing-zero-vector convention
- we lose the intended meaning of "missing coordinate"

By contrast, `instance_list_semantics` does not admit those extra points, because the point length is fixed by `pi_depth`.

So for mixed scan-dimension programs:

- `PolyLang.semantics`
- `PolyLang.instance_list_semantics`

are not merely unproved equivalent; they are describing different behaviors.

## Codegen-Specific Root Cause

The semantic mismatch is visible in the codegen pipeline too.

### Global dimension threaded into codegen

`CodeGen.complete_generate_many` is called with:

- `es = length varctxt`
- `n = length vars`

Then `ASTGen.generate_loop_many` recursively projects each instruction polyhedron with:

- `project ((n - d1), pi.(pi_poly))`

So the code generator is also organized around one global dimension `n`.

### Old multi-instruction failure is consistent with this

The old comment gives a concrete witness:

- one instruction of dimension 1
- one instruction of dimension 2
- same program passed to `complete_generate_many ... 2 ...`

The observed failure mode was:

- projecting a lower-dimensional polyhedron as if it lived at the larger global dimension gives the wrong result
- downstream codegen then fails on the projected polyhedron

This matches the semantic issue above:

- the codegen path assumes a dimension discipline stronger than what `wf_pprog` currently records
- the proof currently hides this under a global `n`

## What This Means For Alignment

The missing link is **not**:

- a generic theorem `PolyLang.semantics <-> PolyLang.instance_list_semantics`

That is the wrong target.

The real problem is:

1. `PolOpt` is stated over the explicit instance-list semantics
2. `CodeGen` is proved over the global-dimension scanning semantics
3. those semantics diverge on heterogeneous scan-dimension programs

So the alignment task has to start by choosing which semantic story is authoritative.

## Recommended Position

Use `instance_list_semantics` as the semantic authority for driver-level correctness.

Reason:

- validator correctness is already there
- extractor correctness is already there
- the definition is instruction-wise dimensioned
- it matches the explicit instance view used elsewhere in the project

Then treat the current `PolyLang.semantics` / `env_scan` story as a codegen-side internal semantics that still needs repair or restriction.

## New Evidence From `PrepareCodegen`

The new adapter proof work in `/polcert/src/PrepareCodegen.v` sharpened the
diagnosis.

What is now proved:

- structural adapter correctness:
  - `prepare_codegen_preserves_ready`
  - `prepare_codegen_preserves_wf`
- execution-list bridge:
  - `prepare_poly_semantics_collect`

This last theorem is important: it already reconstructs a schedule-sorted
source-side execution list from prepared `poly_semantics`.

So the remaining problem is **not** collecting execution points from codegen
semantics.

The remaining problem is the final lift to source
`instance_list_semantics`, because `flatten_instrs` asks for a converse
membership characterization that does not mention the current runtime
environment prefix.

In short:

- current prepared semantics gives current-env points
- current `flatten_instrs` converse expects all `belongs_to` points
- `wf_pprog` does not force those two sets to coincide

## Proof Plan

### Milestone 0: freeze the semantic diagnosis

Before proving anything new, record the following as project facts:

- `PolOpt` and validator are currently tied to `instance_list_semantics`
- `CodeGen.codegen_correct` is tied to `PolyLang.semantics`
- these semantics are not equivalent in general
- the counterexample pattern is heterogeneous scan dimension

Definition of done:

- the project notes explicitly reject the old "bridge theorem first" plan

### Milestone 1: isolate the exact codegen fragment that is currently meaningful

We need a new invariant stronger than `wf_pprog`.

Possible names:

- `uniform_scan_dim`
- `codegen_ready_pprog`
- `wf_codegen_pprog`

This invariant should express at least one of the following two positions:

1. all instructions have the same effective scan/domain dimension
2. or the program has been normalized so each instruction is explicitly padded to a common scan dimension with semantics-preserving constraints

The point is to stop pretending that `wf_pprog` alone is enough.

Definition of done:

- a precise Coq-side predicate describing the fragment on which codegen semantics is supposed to be interpreted

### Milestone 2: decide between restriction and repair

There are two coherent routes.

#### Route A: short-term restriction

Restrict the alignment theorem to codegen-ready programs only.

That means:

- do not change `env_scan` yet
- prove alignment only on a homogeneous or normalized fragment

This is the shortest route to a truthful theorem.

#### Route B: semantic repair

Refactor the codegen-side semantic layer so scanning is instruction-wise dimensioned.

Concretely this likely means:

- replacing the global `dim` use in `env_scan`
- making the scan discipline depend on each instruction's real dimension
- revisiting `complete_generate_many` / `ASTGen.generate_loop_many` projection assumptions

This is the more correct long-term route, but it is no longer "just theorem packaging".

Recommendation:

- take Route A first to get a sound theorem boundary
- keep Route B as the real cleanup milestone

### Milestone 3: state a codegen theorem on the same semantic layer as `PolOpt`

Do **not** attempt a global equivalence theorem.

Instead, target a theorem of the form:

- `codegen_correct_instance_list_ready`

## New Adapter Route

The currently preferred route is now explicit:

1. keep the existing codegen proof as an internal theorem over its current semantics
2. add a `poly -> poly` adapter before codegen
3. prove that the adapter turns explicit-depth semantics into a codegen-ready internal model
4. derive a new end-to-end theorem through that adapter

This avoids rewriting `ASTGen` / `CodeGen` immediately.

## Skeleton Introduced In The Container

Two new skeleton files now exist in `gifted_curie:/polcert`:

- `/polcert/src/PrepareCodegen.v`
- `/polcert/driver/PolOptPrepared.v`

They currently compile on their own, but are not yet wired into the default build.

### `src/PrepareCodegen.v`

This file introduces:

- `prepare_codegen : PolyLang.t -> PolyLang.t`
- `codegen_ready_pprog : PolyLang.t -> Prop`
- `prepared_codegen : PolyLang.t -> imp Loop.t`

Current shape of the adapter:

- compute a common target dimension
- resize schedule / transformation / access rows to that common dimension
- extend each domain with explicit null constraints for the coordinates beyond `env_dim + pi_depth`

So the intended meaning is:

- keep explicit `pi_depth` as the source-level semantic information
- additionally produce a codegen-ready internal model whose extra coordinates are constrained in the domain

Three theorem placeholders are currently left admitted there:

- `prepare_codegen_preserves_ready`
- `prepare_codegen_preserves_wf`
- `prepare_codegen_semantics_correct`

### `driver/PolOptPrepared.v`

This file introduces:

- `Opt_prepared`
- `Extract_Schedule_Prepared_correct`
- `Opt_prepared_correct`

The key point is that the driver-level proof shape is now explicit.

The new composition is:

- `Extractor.extractor`
- `scheduler'`
- `prepare_codegen`
- `CodeGen.codegen`

## Dependency Chain For The Final Proof

The theorem dependency chain is now:

1. `Extractor.extractor_correct`
2. `BaseOpt.scheduler'_correct`
3. `Prepare.prepare_codegen_semantics_correct`
4. `CodeGen.codegen_correct`
5. `Prepare.prepare_codegen_preserves_wf`

From these we get:

- `Prepare.prepared_codegen_correct`
- `Extract_Schedule_Prepared_correct`
- `Opt_prepared_correct`

More concretely:

1. `CodeGen.codegen_correct` gives internal `PolyLang.semantics` on `prepare_codegen pol'`
2. `prepare_codegen_semantics_correct` translates that to source-side `instance_list_semantics pol'`
3. `Extract_Schedule_correct` translates that back to original `Loop.semantics`

That is the current preferred end-to-end proof architecture.

## Why This Addresses The User's Objection

The user objection was:

- if `depth` is not absorbed into the domain, current codegen does not actually see enough information

This is correct.

The adapter route answers it as follows:

- source semantics remains explicit-depth
- codegen still receives a model where the extra coordinates are constrained in the domain
- the adapter theorem is exactly the proof obligation that these two presentations mean the same thing

So we are not claiming the current codegen is already correct for the explicit-depth source model.

We are instead making the missing semantic conversion explicit.

Suggested shape:

- `WHEN loop <- CodeGen.codegen pol THEN`
- `wf_codegen_pprog pol ->`
- `Loop.semantics loop st st' ->`
- `PolyLang.instance_list_semantics pol st st'`

How to get there depends on the route chosen above:

- Route A:
  - prove a restricted bridge only for codegen-ready programs
  - or prove directly that codegen-generated loops realize the flattened instance list
- Route B:
  - reprove codegen over repaired scanning semantics and then connect that to instance-list semantics

Important:

- the theorem target must be the same semantic layer used by validator and `PolOpt`
- otherwise `Opt_correct` will remain syntactically impossible to compose

### Milestone 4: package driver-side well-formedness transport

Independently from the semantic issue, `PolOpt` still needs driver-friendly lemmas such as:

- extraction success implies the required codegen fragment invariant
- scheduler/validator preserve that invariant
- validator preserves `wf_pprog`

The existing library already has part of this:

- `validate_preserve_wf_pprog`
- extractor-local well-formedness lemmas

But they are not yet assembled in the shape the driver theorem needs.

Definition of done:

- a small bundle of driver lemmas that export:
  - `wf_pprog`
  - the stronger codegen-ready invariant

### Milestone 5: prove `Opt_correct` only after semantic alignment

Only after Milestones 1 to 4 does a truthful driver theorem make sense.

Then the target theorem is standard:

- optimized loop semantics
- implies original loop semantics up to `State.eq`

But trying to prove it before Milestone 3 would just bury the semantic mismatch under more lemmas.

## Practical Next Steps

The next proof work should not start in `driver/PolOpt.v`.

It should start with a diagnosis note and a small invariant layer around codegen:

1. define the codegen-ready fragment precisely
2. reproduce the old heterogeneous-dimension witness inside the current tree
3. decide whether the first theorem will be:
   - restricted alignment, or
   - repaired semantic alignment
4. only then derive a codegen theorem on `instance_list_semantics`

## Short Summary

The position is:

- `PolOpt` and `CodeGen` are not blocked by theorem direction
- they are blocked by a genuine semantic mismatch
- that mismatch comes from global-dimension scanning versus instruction-wise instance enumeration
- the old multi-instruction comment is not a side bug; it is the concrete witness of the mismatch

So the proof plan must start from semantic discipline, not from theorem composition.

## Current Adapter Skeleton

The container repo now contains an explicit Route-A skeleton:

- `/polcert/src/PrepareCodegen.v`
- `/polcert/driver/PolOptPrepared.v`

Current factoring is:

1. keep source semantics on explicit-depth `instance_list_semantics`
2. define `prepare_codegen : poly -> poly`
3. reuse existing `CodeGen.codegen_correct` on `prepare_codegen pol`
4. bridge back with `prepare_codegen_semantics_correct`
5. compose end-to-end via `Opt_prepared_correct`

Important implementation correction already made:

- `prepare_codegen` now pads directly to `codegen_target_dim = length vars`
- this matches current `CodeGen.codegen` / `env_scan` exactly
- the adapter route therefore no longer depends on inventing a smaller
  internal common dimension

Current remaining proof obligations:

- `prepare_codegen_preserves_ready`
- `prepare_codegen_preserves_wf`
- `prepare_codegen_semantics_correct`

Current expectation:

- the first two are structural
- the last one is the only real semantic bridge

## Revised judgement on `wf`

`wf_pprog` is not "too strong". It is simply the wrong invariant layer for
codegen.

- `wf_pprog` is source-side: each instruction is well-formed at its own
  explicit dimension `env_dim + pi_depth`.
- codegen needs an internal common-dimension invariant: all instructions live
  in the ambient dimension `length vars`, and padded tail coordinates are
  constrained correctly.

So the right layering is:

- keep `wf_pprog` as the source invariant
- keep a separate internal `wf_codegen_pprog`
  (the current `codegen_wf_pprog`)
- keep `codegen_ready_pprog` as the stronger constructive invariant produced
  by `prepare_codegen`

This is compatible with the intended adapter route, but it does **not** solve
the remaining admitted theorem by itself.

## Revised judgement on the last bridge theorem

The real blocker is semantic, not well-formedness.

- prepared runtime semantics scans only points with the current runtime prefix
  `envv`
- current `flatten_instrs` converse membership does not mention that prefix

This turned out to be repairable without changing outer semantic names:

- after fixing the `flatten_*` family so RHS membership also carries the
  current `envv` prefix, the intended bridge theorem became provable again
- `prepare_codegen_semantics_correct` now closes against the existing
  `instance_list_semantics`
- the key remaining work was not semantic redesign, but rebuilding a
  `flatten_instrs envv pis ipl` witness from collected prepared execution
  points

## Minimal-impact repair if `flatten_instrs` is the real gap

Preferred strategy:

- keep outer semantics names and theorem shapes unchanged
- repair only the internal point-set definition family

The family to change in lockstep is:

- `flatten_instrs`
- `flatten_instr_nth`
- `flatten_instrs_ext`
- `flatten_instr_nth_ext`

The minimal semantic repair is:

- keep the first conjunct unchanged
- strengthen the membership characterization on the right-hand side so it also
  requires the current prefix `envv`

Suggested shape:

`In ip ipl <-> prefix(envv, ip) /\ belongs_to ... /\ length ...`

This is the least disruptive option because:

- it fixes exactly the exposed semantic gap
- it leaves `PolyLang.semantics`, `PolyLang.instance_list_semantics`,
  `Validator.validate_correct`, `Extractor.extractor_correct`,
  `CodeGen.codegen_correct`, and final end-to-end theorem shapes unchanged
- it localizes most proof repair to `src/PolyLang.v`

Recommended repair order:

1. add a helper predicate for env-scoped membership
2. update the four `flatten_*` definitions uniformly
3. prove compatibility projection lemmas so old downstream proof patterns can
   keep dropping the extra prefix premise when going from `In ip ipl`
4. repair `src/PolyLang.v`
5. repair `src/Validator.v`
6. repair `src/Extractor.v`
7. close `prepare_codegen_semantics_correct`

## Current status

This plan is now implemented:

- `src/PolyLang.v`
  - `flatten_instrs`
  - `flatten_instr_nth`
  - `flatten_instrs_ext`
  - `flatten_instr_nth_ext`
  all require the current `envv` prefix on the RHS membership condition
- clause 1 was intentionally kept and commented as redundant, to minimize
  downstream proof breakage
- `src/Validator.v`, `src/Extractor.v`, and `src/PrepareCodegen.v` were
  repaired on top of that change
- `prepare_codegen_semantics_correct` is `Qed`
- `driver/PolOptPrepared.v` compiles
- `check-admitted` reports `Nothing admitted`
- full container build passes
