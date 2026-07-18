# State.eq Goal Completion Audit

Updated: 2026-07-18

This audit tests the active State.eq publication goal against current evidence.
It distinguishes completed scientific claims from remaining maintenance,
distribution, and paper work. A passing narrow check is not used as evidence
for a broader requirement.

## 1. Frozen implementation milestone

Status: complete.

Required evidence and current result:

- immutable PolCert identity: annotated tag
  `state-eq-polyhedral-verification-complete-2026-05-25-v2`, tag object
  `f9cc209ae597f58e98841a96e13f8b355ee75eb3`, commit
  `13295e741ad62173411882c6d900dd9dc57337a8`, and tree
  `8b83093929e54657c033fa09c5aae73b492c0b67`;
- matching Pluto identity:
  `6f43860b6c4cddeeca09189bf3073f05b78b14a5`;
- clean exact-tag reproduction: recorded in
  `STATE_EQ_BASELINE_REPRODUCTION.md` and
  `evidence/state-eq-baseline-2026-07-18/`;
- proof closure: 178 Coq files scanned with no admitted markers, aborted
  proofs, unrealized extraction axioms, or missing mapped route theorem;
- executable coverage: 18/18 artifact checks, 114/114 Pluto compatibility
  checks, 62/62 strict cases, and the recorded ISS, parallel, vector,
  second-level, diamond, and legacy suites pass.

The tag is not moved by later artifact, proof-cleanup, or paper commits.

## 2. Claim-oriented Docker artifact

Status: scientifically complete and locally reviewed; distribution hardening
is incomplete.

Completed evidence:

- `artifact/state-eq/` exports only the frozen commit with `git archive` and
  validates the tag object, commit, tree, Pluto commit, and Pluto base digest;
- one reviewer workflow builds proofs and executables, checks proof closure,
  regenerates reports, and exercises every claimed transformation family;
- the full review ran with Docker networking disabled and passed 12/12
  top-level gates and 18/18 nested checks;
- the reviewed local image content ID is
  `sha256:573831494258848d553801ee244b9d49ee8f84c2d39716255637b2c8970bfd6f`;
- claims and explicit non-claims are mapped in `artifact/state-eq/claims.json`
  and `STATE_EQ_CLAIM_LEDGER.md`;
- the publication command refuses moving or default-registry targets, checks
  the exact source tag/commit/tree, all zero proof-hole counts, 18/18 artifact
  checks, 114 Pluto compatibility cases, 62/62 strict cases, and all dedicated
  route suites before tagging or pushing;
- its 14 fixture tests and a real local dry run pass without a registry
  operation or publication record.

Remaining requirements:

- publish the reviewed image and record a repository-qualified registry
  digest; the local content ID is not a registry digest;
- lock or archive the opam repository state, non-Coq opam package resolution,
  and apt package closure as reproducible build inputs;
- after changing those build inputs, rebuild and repeat the full offline review
  before describing the new image as the reviewed artifact.

`artifact/state-eq/DEPENDENCY_LOCK_AUDIT.md` is the authoritative gap analysis.

## 3. Controlled affine-proof cleanup

Status: in progress.

Completed evidence:

- cleanup is isolated on `proof-cleanup-affine-batch1`, based exactly on the
  frozen commit;
- commits `50aefe5`, `7a62341`, and `711d10d` change only
  `src/AffineValidator.v` proofs and local presentation;
- the three commits reduce the file by 33 net lines while preserving public
  theorem statements, computational definitions, imports, hints, and the
  extraction surface;
- each accepted slice passed `check-admitted` and rebuilt the directly
  dependent proof modules; the second slice was also independently forced
  through a clean `AffineValidator.vo` rebuild.

Remaining requirements:

- complete or deliberately stop the bounded batches in
  `AFFINE_PROOF_CLEANUP_AUDIT.md` based on readability, not line count;
- run the broader proof, extraction, executable, and route regression gates
  required by the accepted later batches;
- decide whether the paper artifact remains the immutable pre-cleanup tag or a
  separately frozen cleaned revision. The existing tag and image must remain
  available either way.

## 4. Evidence-backed paper

Status: contribution framing and frozen-evidence evaluation are integrated;
final paper preparation is in progress.

Completed evidence:

- `STATE_EQ_CLAIM_LEDGER.md` fixes the contribution hierarchy and non-claims;
- the paper presents inherited affine scheduling as the baseline, end-to-end
  closure first, witness-centered tiling as the central contribution, ISS and
  parallel/multipar as semantic extensions, and the remaining routes as
  supporting capabilities;
- abstract, introduction, validator, conclusion, parallel note, Markdown
  narrative, and artifact report have been reconciled with exact-tag evidence;
- `scripts/generate_evaluation_tables.py` derives the capability summary,
  theorem-route inventory, proof counts, and executable results from four
  archived JSON inputs and rejects inconsistent or stale evidence;
- the generated presentation covers 81 capability rows, 24 theorem-facing
  routes, 178 Coq files, 12/12 top-level checks, 18/18 nested checks, 114/114
  Pluto compatibility checks, and 62/62 strict cases;
- all 27 paper-facing bibliography entries have been manually audited, with a
  documented RefChecker re-audit;
- the current 17-page paper and 5-page artifact-report PDFs build without
  overfull boxes, undefined references, or LaTeX warnings.

Remaining requirements:

- finish the scientific-body revision using the generated evaluation and exact
  theorem anchors;
- keep uncited exploratory related-work candidates outside the curated
  bibliography until each is needed and audited;
- regenerate and re-audit the paper evidence after registry publication or any
  frozen-source change;
- make an explicit title and venue-format decision after the scientific body
  and publication evidence are stable.

## Completion rule

The active goal is complete only when Sections 1-4 have no remaining required
work. In particular, a successful local image review does not prove registry
publication or deterministic networked rebuilds, and a claim-calibrated
abstract does not prove that the whole paper and bibliography are ready.
