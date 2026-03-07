# Proof TODO Inventory

Date: 2026-03-05
Scope scanned in container `/polcert`: `src/ polygen/ driver/ common/ cfrontend/ cparser/ lib/ VPL/`

## 1) Blocking Incomplete Proofs (project-local)

1. `src/Extractor.v:506` — `Admitted.` (`extractor_correct`)

This is the only direct `Admitted` in the scanned scope and is the current proof bottleneck for end-to-end extractor soundness.

## 2) Untrusted / External Interface Parameters (project integration layer)

1. `polygen/PolIRs.v:16` — external `scheduler` parameter.
2. `driver/PolOpt.v:71` — `print_CompCertC_stmt` parameter (debug/printing).
3. `src/OpenScopAST.v:18` — `location` parameter.
4. `src/OpenScop.v:14-16` — name-binding conversion parameters.
5. `common/AST.v:744-747` — identifier/string conversion parameters.

These are expected TCB surface points, not immediate proof obligations for extractor correctness.

## 3) Large Foundational Axiom Buckets (upstream/infra)

1. `common/Memtype.v` — memory model axioms/parameters (large CompCert-style foundation).
2. `common/Events.v` — external function / inline assembly semantics axioms.
3. `lib/Axioms.v` — proof irrelevance axiom import.
4. `VPL/coq/*.v` — backend oracle/solver-related axioms.
5. `lib/TopoSort.v:26` — untrusted topological sort parameter.

These are global trust assumptions and should be documented as TCB, not solved in extractor milestone.

## 4) Abort Scan

No `Abort.` occurrences found in scanned scope.

## 5) Immediate Actionable Next Steps

1. Close `src/Extractor.v:extractor_correct` using the staged lemma plan in `proof/extractor/PLAN.md`.
2. Keep new extractor-side invariants (depth normalization + wf guard + access-resolution checker) as locked assumptions for proof scripts.
3. When reporting trust story, separate:
   - extractor-local proof debt (`extractor_correct`),
   - external scheduler trust boundary,
   - foundational CompCert/VPL axiom base.
