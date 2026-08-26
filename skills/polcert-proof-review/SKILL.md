---
name: polcert-proof-review
description: Review the frozen PolCert v9 Rocq proof top down, map paper claims to theorem surfaces, and audit proof structure without changing semantic contracts. Use for proof walkthroughs, theorem-to-paper checks, proof-reading plans, or structural review of long Rocq files.
---

# PolCert Proof Review

Use this skill for the frozen implementation in `work/parallel-interleaving/`.
Before relying on line numbers or theorem inventories, verify:

- branch `artifact/verified-compilation-v9-candidate`;
- commit `604587ecfec9ff3bf6be655dd66e25af6178d604`;
- tag `state-eq-polyhedral-verification-complete-2026-08-26-v9`.

## First Reads

1. `doc/STATE_EQ_CLAIM_LEDGER.md` in the outer workspace.
2. `doc/PROOF_READING_GUIDE.md` in the source worktree.
3. `doc/proof-audits/README.md` in the source worktree.
4. `driver/VerifiedParallelCompilerConfig.v`, starting from `compile_correct`.

Archived outer-workspace proof plans and definition maps predate v9 and are not
current reading guides.

## Review Order

Read from contracts to components:

1. top-level raw and verified configuration theorems;
2. one representative route through extraction, validation, preparation, and
   code generation;
3. the occurrence-correspondence and order-legality lemmas used by that route;
4. specialized tiling layout bridges only after the common band theorem;
5. parallel target semantics, eligibility certificates, generated-event
   origins, and actual-trace serialization as separate layers;
6. concrete extracted wrappers after the generic proof is understood.

Treat large constructor dispatch proofs as coverage plumbing unless a branch
changes the semantic contract.

## Narrative Audit

For each paper claim, record:

- exact theorem and module;
- executable success condition;
- source and target semantic relations;
- refinement direction and state relation;
- assumptions internal to the semantic judgments;
- whether the component is inherited, newly proved, or only supporting breadth;
- explicit rejection and nonclaim boundaries.

Do not infer a paper contribution merely because an executable route exists.
Conversely, flag any narrative claim that lacks a theorem-bearing path to
`VerifiedParallelCompilerConfig.compile_correct`.

## Validation Policy

Proof acceptance uses a clean full Rocq build and the existing project CI. Do
not add or propose a separate proof-kernel gate that the project has rejected.

## Exit Checks

- Re-read the exact theorem statement after inspecting its proof body.
- Check that the paper uses target-to-source refinement, not equivalence or
  progress, unless a stronger theorem is explicitly present.
- Keep raw target interleavings separate from certificate soundness.
- Report stale proof documentation rather than silently reconciling it from
  memory.
