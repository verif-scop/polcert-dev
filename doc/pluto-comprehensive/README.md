# Pluto Comprehensive Notes

This directory now serves two closely related roles:

1. it remains the internal technical notebook for Pluto-side analysis and
   PolCert/PolOpt proof engineering
2. it now also hosts the paper-facing draft material for the "Full-fledged
   Verified Polyhedral Compilation" story

The point of the directory is therefore no longer just to record engineering
history. It should also support a paper-quality explanation of:

- what the verified compiler/validator stack is
- what semantic relations it proves
- how extraction, affine validation, checked tiling, compatibility bridges, and
  codegen fit into one end-to-end theorem

## Scope

These notes serve three related purposes:

1. explain the real Pluto pipeline as implemented in the artifact, not just as
   described in high-level READMEs or command-line help
2. explain the current verified affine+tiling pipeline in PolCert/PolOpt
3. record the design choices and presentation strategy needed for papers,
   talks, and future proof extensions

## Primary Sources

- the main Pluto implementation analyzed in these notes is the container-side
  source tree `/pluto`
- the main PolCert development discussed here is the `polcert-dev` working tree
  in this repository
- file references inside these notes are therefore intended as technical guide
  rails for developers, not as user-level documentation

## Paper Draft First

If the immediate goal is paper writing rather than engineering archaeology, the
best starting point is:

1. [full-fledged-verified-polyhedral-compilation-draft.md](./full-fledged-verified-polyhedral-compilation-draft.md)
   - current paper-style draft organized around abstract, informal
     development, relation, validator, and correctness
2. [paper-presentation-verification-strategy.md](./paper-presentation-verification-strategy.md)
   - shorter presentation memo for talks, defenses, and paper discussions
   - use this after the main draft, not instead of it
3. [latex/README.md](./latex/README.md)
   - LaTeX paper tree corresponding to the main draft
   - use this when the paper needs actual TeX formatting and local compilation

These two notes are the current paper-facing backbone. The remaining files in
this directory should be read as supporting technical references.

## Parallel Design Entry Point

For the current frozen first-version design of verified `parallel for`
generation, start with:

- [parallel-rfc.md](./parallel-rfc.md)

Then use the following supporting notes only as needed:

- [parallel-coq-skeleton.md](./parallel-coq-skeleton.md)
- [parallel-proof-obligation-checklist.md](./parallel-proof-obligation-checklist.md)
- [parallel-implementation-staging.md](./parallel-implementation-staging.md)

## Current Source Of Truth

If the verified stack changes, these are the files that should usually be
updated first.

### 1. Current factual status

- [formalization-status.md](./formalization-status.md)

Use this for:

- what is currently proved
- what is outside the theorem
- what the present benchmark numbers are

### 2. Current pipeline shape

- [verified-phase-pipeline.md](./verified-phase-pipeline.md)
- [verified-pipeline-design.md](./verified-pipeline-design.md)

Use these for:

- naming of the verified stages
- where fallback happens
- why the current affine+tiling route is layered the way it is

### 2.5 Diamond takeaway

The current settled interpretation of diamond tiling in this repository is:

- not "default affine + ordinary tiling"
- not "a brand-new tiling theorem family"
- but "diamond-aware affine midpoint + ordinary tiling"

For the clearest versions of that conclusion, start with:

- [diamond-tiling-paper-notes.md](./diamond-tiling-paper-notes.md)
- [second-level-and-diamond-design.md](./second-level-and-diamond-design.md)
- [polopt-second-level-diamond-support.md](./polopt-second-level-diamond-support.md)

### 3. Current paper narrative

- [full-fledged-verified-polyhedral-compilation-draft.md](./full-fledged-verified-polyhedral-compilation-draft.md)
- [latex/main.tex](./latex/main.tex)

Use this for:

- the paper-facing mainline story
- the semantics-first explanation of extractor, validators, compatibility
  stages, and codegen
- the LaTeX-formatted paper draft

### 4. Current talk/presentation narrative

- [paper-presentation-verification-strategy.md](./paper-presentation-verification-strategy.md)

Use this for:

- talk-level emphasis
- what to claim and what not to claim
- how to answer likely audience questions

## How To Maintain This Pack

When a future session changes the verified stack, the recommended maintenance
order is:

1. update [formalization-status.md](./formalization-status.md) with the factual
   status
2. update [verified-phase-pipeline.md](./verified-phase-pipeline.md) if stage
   names or routing changed
3. update
   [full-fledged-verified-polyhedral-compilation-draft.md](./full-fledged-verified-polyhedral-compilation-draft.md)
   if the paper-level story changed
4. update
   [paper-presentation-verification-strategy.md](./paper-presentation-verification-strategy.md)
   if the talk-level emphasis changed
5. only then update older design-history notes if they are still worth keeping

This keeps the directory usable as a long-lived research pack rather than a
pile of disconnected scratch notes.

## How To Grow The Main Draft

The main draft should now stay relatively paper-like. Its internal structure is
already stable enough that future sessions should prefer extending existing
sections rather than appending more meta commentary to the draft itself.

The most useful kinds of update are:

- deepening one existing section with cleaner prose
- strengthening one theorem boundary with a clearer explanation
- refining the two running examples (`covcol` and `matmul-init`)
- adding one compact figure/table specification that the eventual paper will
  likely need

The least useful kinds of update are:

- reintroducing long maintenance notes into the main draft
- duplicating the same narrative across multiple paper-facing notes
- adding artifact-only detail that belongs in technical notes instead

As a working rule:

- keep maintenance guidance in this README
- keep paper prose in
  [full-fledged-verified-polyhedral-compilation-draft.md](./full-fledged-verified-polyhedral-compilation-draft.md)
- keep talk tactics in
  [paper-presentation-verification-strategy.md](./paper-presentation-verification-strategy.md)

## When To Create A New Note

This directory already has enough history documents that future sessions should
be conservative about adding new ones.

Create a new note only if at least one of the following is true:

- it captures a genuinely new proof boundary or architecture change
- it is a paper-facing draft with a distinct audience from the existing files
- it records an experiment series that would otherwise pollute the paper-facing
  notes

Do not create a new note merely because:

- one section of an existing draft needs to be expanded
- a theorem list needs to be updated
- a naming change happened in one module

In those cases, update the current source-of-truth files instead.

As a default rule:

- update the draft before creating a sibling draft
- update the status note before creating a new status note
- update the pipeline note before creating a new pipeline note

## Technical Reading Order

1. [source-map.md](./source-map.md)
   - file-level Pluto map and feature inventory
2. [pipeline.md](./pipeline.md)
   - execution order of the external Pluto pipeline
3. [options-and-capabilities.md](./options-and-capabilities.md)
   - which Pluto options are real, live, and relevant to validation
4. [formalization-status.md](./formalization-status.md)
   - what the current proof stack actually covers
5. [verified-phase-pipeline.md](./verified-phase-pipeline.md)
   - naming and layering of the final verified affine+tiling route
6. [verified-pipeline-design.md](./verified-pipeline-design.md)
   - why the current verified pipeline is structured the way it is
7. [paper-presentation-verification-strategy.md](./paper-presentation-verification-strategy.md)
   - how to present the verification story, especially extraction and tiling,
     in a paper or talk
8. [full-fledged-verified-polyhedral-compilation-draft.md](./full-fledged-verified-polyhedral-compilation-draft.md)
   - current paper-style draft for the full extraction + validation + codegen
     story

## Tiling-Focused Notes

The following notes are the main tiling-specific design history:

- [tiling-validation-design.md](./tiling-validation-design.md)
- [second-level-and-diamond-design.md](./second-level-and-diamond-design.md)
- [polopt-second-level-diamond-support.md](./polopt-second-level-diamond-support.md)
- [diamond-tiling-paper-notes.md](./diamond-tiling-paper-notes.md)
- [tiling-coq-bridge.md](./tiling-coq-bridge.md)
- [tiling-coq-checker-interface.md](./tiling-coq-checker-interface.md)
- [tiling-pass-architecture.md](./tiling-pass-architecture.md)
- [tiling-proof-engineering.md](./tiling-proof-engineering.md)
- [tiling-witness-centered-redesign.md](./tiling-witness-centered-redesign.md)
- [tiling-witness-centered-migration-checklist.md](./tiling-witness-centered-migration-checklist.md)

These documents are more detailed and more historical. The
[paper-presentation-verification-strategy.md](./paper-presentation-verification-strategy.md)
file is the distilled talk version, and
[full-fledged-verified-polyhedral-compilation-draft.md](./full-fledged-verified-polyhedral-compilation-draft.md)
is the main paper-facing draft.

For diamond specifically, keep one distinction in mind while reading these
notes:

- sequential correctness can likely reuse the ordinary checked tiling relation
  once a diamond-aware midpoint is exposed
- stronger concurrent-start / load-balance claims are a separate proof target

## ISS-Focused Notes

The following notes are the main ISS-specific design and status references:

- [iss-validation-design.md](./iss-validation-design.md)
- [iss-verified-validator-roadmap.md](./iss-verified-validator-roadmap.md)

Use these for:

- how Pluto ISS actually works in the implementation
- what the validator checks on the Pluto side
- what is now extractable, what is proof-only, and what remains an engineering choice

## Main Current Takeaway

The current verified story should be read as:

- verified extraction from the structured loop frontend into `PolyLang`
- verified affine validation
- verified checked tiling on the phase-aligned `mid -> after` route
- verified compatibility bridges such as strengthening, `current_view_pprog`,
  and `prepare_codegen`
- verified reuse of the affine codegen chain through `current_view_pprog`
- verified fallback to the affine-only path when the tiling route does not
  complete successfully

This is the right top-level message for current presentations. The rest of the
documents in this directory explain how that message is technically justified.
