# Proof TODO Inventory

Date: 2026-03-24
Scope scanned in container `/polcert`: `src/ polygen/ driver/ common/ cfrontend/ cparser/ lib/ VPL/`

## 1) Blocking Incomplete Proofs (project-local)

No direct `Admitted.` or `Abort.` occurrences remain under the scanned
project-local proof scope at the time of this scan.

This file should therefore no longer be read as an active blocker list. It is
now primarily a reminder that the relevant remaining trust boundaries are the
external interfaces and foundational axiom buckets below, not local unfinished
proof scripts.

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

1. Keep the trust story separate across:
   - extractor-side correctness theorems and their current status,
   - external scheduler trust boundary,
   - foundational CompCert/VPL axiom base.
2. When updating status notes, prefer
   [formalization-status.md](/home/hugh/research/polyhedral/polcert/doc/pluto-comprehensive/formalization-status.md)
   as the current source of truth rather than reviving stale blocker lists here.
