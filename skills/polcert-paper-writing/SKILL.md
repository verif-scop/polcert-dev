---
name: polcert-paper-writing
description: Draft, revise, and review the PolCert paper workspace under `doc/pluto-comprehensive/paper-local/`, with claim calibration grounded in CompCert, translation validation, and verified polyhedral code generation. Use when writing or reviewing abstract/introduction/related work/correctness prose, theorem statements, scope claims, or paper-facing research notes.
---

# PolCert Paper Writing

Use this skill for paper-facing work in `doc/pluto-comprehensive/paper-local/`.
It is intentionally narrower than a generic academic-writing skill: the goal is
to help write a formal-methods/compiler paper whose claims stay aligned with the
actual PolCert artifact and theorem boundary.

## Core workflow

1. Reconstruct local paper state before editing.
2. Anchor framing to the CompCert / translation-validation / verified-polyhedral
   lineage instead of writing generic systems-paper prose.
3. Keep abstract, introduction, related work, correctness, and conclusion
   mutually consistent on support boundaries.
4. Treat bibliography metadata and predecessor descriptions as audited facts, not
   as things to guess from memory.
5. Prefer small section-local edits over whole-paper rewrites.

## First reads

Before any substantial paper edit, read:

- `doc/pluto-comprehensive/paper-local/STATUS.md`
- `doc/pluto-comprehensive/paper-local/TODO.md`
- `doc/pluto-comprehensive/paper-local/workflow/claims/contribution_contract.md`
- `doc/pluto-comprehensive/paper-local/workflow/story/narrative.md`

For review history, use
`doc/pluto-comprehensive/paper-local/workflow/reviews/paper_review_log.md`.
Historical material under `archive/` does not control current prose.

Then read only the target section files you need.

If the task is about positioning, claims, or theorem wording, also open:

- [references/compcert-paper-anchors.md](references/compcert-paper-anchors.md)

## Community patterns to keep

This skill intentionally borrows two patterns from community skills:

- from Anthropic's `doc-coauthoring`: work section-by-section, ask what a
  section is trying to accomplish, and check whether the prose works for a
  reader who does not share the author's hidden context.
- from Hugging Face's `huggingface-paper-publisher`: keep workflows concrete,
  operational, and scriptable; name exact files and commands; avoid vague
  "write a better paper" instructions.

Do not import those workflows wholesale. This repository needs tighter
claim-discipline than a generic documentation or publishing flow.

## Claim discipline

Always calibrate prose against the narrowest trusted boundary.

- Do not let the abstract or introduction outrun the correctness section.
- Do not let current code paths automatically become theorem claims.
- The headline theorem is the unified structured-loop-to-`ParallelLoop`
  refinement theorem in the frozen v9 source.
- Parallel targets admit raw order-preserving interleavings; safety is supplied
  by checked eligibility certificates and generated-event origin proofs, not by
  a semantic safety gate.
- Vectorization is the innermost restricted parallel case in the paper narrative;
  do not claim machine-SIMD adequacy.
- Distinguish:
  - implemented route
  - checked route
  - theorem-bearing default route
  - future or boundary-setting family

High-risk topics in this workspace include:

- direct-only ordinary, hierarchical, and diamond tiling support
- raw parallel interleavings versus eligibility-filter soundness
- what `li2024affine` directly proves
- inherited affine validation and loop generation versus new composition work
- target-to-source termination-bounded refinement versus equivalence or progress

## Writing style anchors

Follow the rhetorical pattern of the CompCert-adjacent papers, not just their
topic area:

- CompCert-style framing: explain why the compiler is a trust bottleneck, then
  define exactly what is verified.
- Necula-style framing: if the contribution is validation, say what is checked
  per run and what is not globally proved.
- Courant--Leroy-style framing: identify the exact polyhedral subpipeline that
  is mechanized, and name what remains outside scope.

Do not imitate wording mechanically. Preserve the paper's own narrative, but
keep the same standard of scope honesty.

## Related-work discipline

- Use only audited bibliography keys already present in the paper-local
  bibliography.
- Describe each predecessor by its actual technical contribution, not by a
  blurry neighboring topic.
- Prefer "direct predecessor", "nearby system", "boundary-setting reference",
  or "adjacent validation setting" over generic praise.
- If a venue, year, or scope was recently audited, trust the audited local
  bibliography and notes over memory.

## Theorem-writing discipline

When editing theorem prose in `paper/sections/semantics.tex`,
`paper/sections/tiling.tex`, or `paper/sections/composition.tex`:

- bind every semantic object mentioned in a theorem statement
- state the success domain or preconditions of pipeline functions
- distinguish theorem schema from proved instantiated pipeline
- avoid making functions look total if they are only defined on a supported
  fragment
- make refinement contracts explicit where interoperability is the main claim

## Useful command

For quick paper review context, run:

```bash
scripts/claim_audit_scan.sh
```

The script highlights high-risk scope lines, predecessor anchors, and theorem
contract hotspots.

## Exit checks

Before finishing a paper-writing task:

1. Re-read the edited section plus the nearest neighboring section.
2. If you touched abstract/introduction/conclusion, compare them against
   `paper/sections/semantics.tex` and `paper/sections/composition.tex`.
3. If you touched related work, compare prose against the audited bibliography
   notes.
4. If you touched theorem prose, check whether the statement now binds all
   semantic objects it uses.
