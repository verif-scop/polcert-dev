# Project Understanding (PolCert / extractor branch)

Last updated: 2026-03-06

## Core Pipeline
- `driver/PolOpt.v`
  - `Opt := Extractor.extractor -> scheduler' (external + Validator.validate) -> CodeGen.codegen`.
  - current proved chain in driver side still effectively stops at
    `Extract_Schedule_correct`; there is still no explicit end-to-end
    `Opt_correct` theorem.

## Core Modules (proof-relevant)
- `src/Extractor.v`
  - defines the affine/SCoP checker, partial polyhedral extractor, and the main
    extractor correctness bridge from PolyLang semantics back to Loop semantics.
  - as of this checkpoint, extractor-side admits are closed.
- `src/PolyLang.v`
  - polyhedral IR semantics (`flatten_instrs`, instance-list semantics, sorted
    instruction-point semantics).
  - this is the semantic source consumed by extractor correctness proofs.
- `polygen/Loop.v`
  - Loop language semantics used as the target of extractor soundness.
  - the `Loop.LLoop` constructor explains the critical env shape:
    body runs under `x :: env`.
- `polygen/CodeGen.v`
  - contains verified codegen theorem(s), but project integration still has the
    known `depth` semantic gap; verified codegen is therefore not yet fully
    connected at the project level.

## Extractor Position
- `extractor_correct`: `Qed`.
- `extract_stmt_to_loop_semantics_core`: `Qed`.
- `extract_stmt_to_loop_semantics_core_sched`: `Qed`.
- `core_sched_stmt_stmts_constrs_prefix_mutual`: `Qed`.
- `loop_slice_to_body_semantics_todo`: `Qed`.
- `src/Extractor.v` now has no `Admitted`.

## How The Final Extractor Proof Is Structured
The final extractor proof is not a single direct induction. It is layered.

1. Wrapper theorems:
- `extractor_correct`
- `extract_stmt_to_loop_semantics_core`
- `extract_stmt_to_loop_semantics_core_sched`

2. Constrained internal bridge:
- `extract_stmt_to_loop_semantics_core_sched_constrs_fuel`
- `extract_stmt_to_loop_semantics_core_sched_constrs`

3. Prefix-aware recursive core:
- `core_sched_stmt_stmts_constrs_prefix_mutual`

4. Specialized wrappers built from that core:
- `loop_slice_to_body_semantics_todo`
- `core_sched_loop_constrs_len_todo`

## Key Proof Insight
The last hole was not an arithmetic problem. It was a theorem-shape problem.

Wrong direction:
- lower a fixed `head_ts = i` slice to a plain unrestricted lowered program and
  try to reuse an ordinary completeness theorem.
- this is unsound for the proof goal because the lowered program still ranges
  over other outer-iterator valuations.

Correct direction:
- keep the theorem slice-aware and prefix-aware all the way through recursion.
- this is why `core_sched_stmt_stmts_constrs_prefix_mutual` is the right final
  theorem shape.

## Env Alignment Intuition
The env convention is consistent once stated correctly.

- outer stmt theorem uses env `rev (envv ++ prefix)`
- in a loop body, `Loop.LLoop` requires body env `x :: rev (envv ++ prefix)`
- recursive IH naturally produces env `rev (envv ++ (prefix ++ [x]))`
- these are equal, but the proof script must normalize them explicitly
- the stable rewrite used in the final proof is:
```coq
symmetry.
rewrite app_assoc.
apply rev_unit.
```

## Current Project-Level Gaps
Extractor is no longer the main proof blocker. The remaining larger gaps are:
- no explicit end-to-end `Opt_correct`
- verified codegen not fully linked because of the `depth` semantic gap
- overflow handling still not integrated into the final correctness story
- extractor definition cleanup is still desirable:
  - stronger `wf_scop` rejection discipline
  - clearer treatment of unsupported constructs
  - depth normalization and interface cleanup

## Syntax-Level Frontend Position
- `TInstr` is not a good frontend target for a practical `polopt` parser.
  - its dynamic semantics being trivial is acceptable for extraction/runtime
  - but its structural interface is currently too empty:
    - `waccess` / `raccess` return `None`
    - `to_openscop` returns `ArrSkip`
- For the extracted optimizer, the important part is not concrete instruction
  execution but structural information carried through the pipeline:
  - extractor keeps `pi_instr` unchanged and derives `pi_waccess/pi_raccess`
  - codegen keeps `pi_instr` unchanged and rebuilds `Loop.Instr i es`
- Therefore a separate syntax instruction instance is the right design move.

## New Syntax IR Instance
- Added a new instruction module:
  - `src/SInstr.v`
- Intent:
  - provide a syntax-oriented instruction language for end-to-end pipeline
    experiments
  - do not disturb existing `TInstr`
- Current `SInstr` design:
  - semantics: still trivial / empty
  - syntax: array assignment language with affine indices
  - structure exposed to the pipeline:
    - real `waccess`
    - real `raccess`
    - real `to_openscop`
    - structural `eqb`
- Added matching instances:
  - `src/SPolIRs.v`
  - `driver/SPolOpt.v`

## Frontend Direction
- The intended `polopt` frontend should not go through `Convert.v`.
- Better route:
  1. parse a restricted Loop-fragment language
  2. elaborate directly to `SPolIRs.Loop.t`
  3. use `SInstr` for leaf statements
  4. call `SPolOpt.opt`
- This isolates frontend experimentation from both:
  - CompCert `Csyntax`
  - placeholder `TInstr`

## Non-goals For This Phase
- `src/Convert.v` integration
- changing `Loop` / `PolyLang` semantic definitions
- proving the PolyGen/depth gap closed without a dedicated normalization story

## Syntax frontend experiment
- The new `syntax/` subtree is intentionally isolated from the old `driver/` validator path.
- `SInstr` is the right abstraction for frontend work: trivial dynamic semantics, real structural interface.
- The new OCaml frontend does not use `Convert.v`; it parses a restricted loop fragment directly to `SPolIRs.Loop.t`.
- The pretty-printer is slot-aware: for `Loop.Instr instr es`, it substitutes `es` back into `instr` instead of pretending `es` is identity.
- This frontend exposed a real integration issue: the generic extracted OpenScop is validator-readable but not Pluto-acceptable. That is upstream of the parser.

## Syntax Frontend Current Position
- The syntax frontend is no longer blocked at Pluto ingestion.
- The syntax path now exercises all three stages in practice:
  1. extractor
  2. scheduler/validator
  3. codegen
- Important integration lessons from this path:
  - OpenScop scattering compatibility matters independently of validator readability.
    - A `.scop` can be self-validated by `polcert` and still be rejected by Pluto.
  - `SInstr.access_function_checker` cannot use strict raw list equality.
    - extractor checks raw access lists
    - validator later checks normalized access lists
    - the checker must accept both representations
  - frontend variable numbering must be chosen for extractor's `normalize_rev`, not for the naive source order.
- The current syntax path reaches codegen only with a syntax-local wrapper in `syntax/SPolOpt.v`.
  - This is evidence that the generic `CodeGen.codegen` / `length vars` integration is not a clean fit for syntax-level `vars` that also store array names.
  - This matches the broader project intuition that verified codegen is present, but not yet fully integrated as a clean end-to-end driver story.

## Generated Loop Shape
- The current `syntax/` path now reaches a final `Loop`, but the output is structurally noisy.
- The main artifacts are:
  - singleton loops
  - mechanical guards
  - unsimplified arithmetic in bounds/tests
- The most important insight is that the singleton loops are really equality constraints in disguise.
  - Example shape:
    - `for i2 in range(i0, i0 + 1)`
  - Intended meaning:
    - `i2 = i0`
- This suggests a later verified cleanup pass on `Loop`, rather than immediate codegen surgery.
- Detailed notes live in:
  - `doc/loop-cleanup-postpass.md`
