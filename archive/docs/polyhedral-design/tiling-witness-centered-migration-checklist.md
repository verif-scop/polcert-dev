# Tiling Witness-Centered Migration Checklist

## Goal

Migrate from the current transitional dual-transformation representation to the
intended witness-centered representation:

- one semantic/source transformation
- one explicit point-space witness

while preserving the existing affine proof architecture as much as possible.

## Phase 1: Core Data Model

Files:

- [PolyLang.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PolyLang.v)

Changes:

- replace transitional:
  - `pi_transformation`
  - `pi_access_transformation`
- with:
  - `pi_transformation`
  - `pi_point_witness`
- do the same for:
  - `PolyInstr_ext`
  - `InstrPoint`
  - `InstrPoint_ext`
- introduce derived functions:
  - current-to-base projection
  - current-space source transformation
  - projected/source argument evaluation

Expected theorem impact:

- `wf_pinstr`
- `wf_pinstr_affine`
- `wf_pinstr_ext`
- `wf_pinstr_ext_affine`
- `eqdom_pinstr`
- `compose_pinstr_ext`
- flattening lemmas that currently mention transformation equality

## Phase 2: Semantics

Files:

- [PolyLang.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PolyLang.v)

Changes:

- make `poly_semantics` use witness-projected source arguments
- do not feed raw current points directly through `pi_transformation`
- access-related semantics should use the same projected/source arguments

Expected theorem impact:

- `poly_semantics` constructors
- `flatten_instr` / `flatten_instrs`
- instruction-point semantic bridge lemmas
- `stable_permut_ext_lists_are_equivalent` prerequisites

## Phase 3: Validator

Files:

- [Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v)

Changes:

- remove dependence on `pi_access_transformation`
- derive current-space access/source arguments via witness projection
- make `check_wf_polyinstr` inspect the new witness field
- keep affine-only validation as the identity-witness specialization

Expected theorem impact:

- `check_wf_polyinstr`
- `check_wf_polyprog_correct`
- ext compose lemmas
- access/dependence correctness lemmas that currently mention
  `pi_access_transformation_ext`

## Phase 4: Tiling

Files:

- [TilingRelation.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingRelation.v)
- [TilingBoolChecker.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingBoolChecker.v)

Changes:

- delete the transitional padded/access-transformation view
- restate relation/checker using:
  - source transformation on base/source space
  - tiling witness on current space
- derive affine subproblem through the witness-projected current-source view

Expected theorem impact:

- all remaining admitted transformation/instr-semantics lemmas
- compiled relation checker soundness
- checked tiling validator theorem

## Phase 5: Upstream Consumers

Files:

- [PrepareCodegen.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PrepareCodegen.v)
- [StrengthenDomain.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/StrengthenDomain.v)
- [Extractor.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Extractor.v)
- [ASTGen.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/polygen/ASTGen.v)
- [SPolIRs.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/syntax/SPolIRs.v)
- [SPolOpt.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/syntax/SPolOpt.v)

Changes:

- preserve/carry the witness field
- stop threading the transitional access-transformation field
- make codegen use the semantic/source transformation view

## Transitional Rule

During the migration:

- the current dual-transformation model should be treated as a temporary proof
  scaffold
- new theorem work should target the witness-centered end-state
- avoid investing further in padded-transformation-specific lemmas unless they
  are needed to keep the build green while migrating
