# PolCert Release Workspace

This repository is the host-side control workspace for the PolCert v10 release,
paper, and reusable agent workflows. The frozen Rocq/OCaml implementation is
maintained in a separate Git worktree and is not tracked here.

## Current Sources

- Proof and compiler source: `work/verified-compilation-v10-driver/`
  - branch: `artifact/verified-compilation-v10-driver-finalization`
  - commit: `9d612d02ac8f27d46c5ec632f912f8a67939e748`
  - tag: `state-eq-polyhedral-verification-complete-2026-08-29-v10`
- CPP 2027 anonymous supplement: `artifact/cpp27-anonymous/`
- Post-review Zenodo release interface: `artifact/zenodo-v10/`
- Frozen v9 artifact reference: `artifact/state-eq/`
- Paper repository: `doc/pluto-comprehensive/paper-local/`
- Paper-facing claim ledger: `doc/STATE_EQ_CLAIM_LEDGER.md`
- Reusable agent skills: `skills/`

Each source, artifact, and paper directory has its own Git state. Inspect and
commit them separately. The ignored `output/`, `tmp/`, and `work/` directories
contain generated results, temporary files, and independent source worktrees.
The hidden `.work/` directory contains legacy local scratch. `.worktree/`
contains a storage-generalization worktree with uncommitted changes; neither is
part of the active release tree.

## Active Responsibilities

### Anonymous Supplement

`artifact/cpp27-anonymous/` builds the single archive uploaded with the CPP 2027
submission. Its README and offline HTML handbook are the reviewer entry points;
the archive contains source, browsable proof HTML, and frozen evidence.

`artifact/zenodo-v10/` is the publication interface for the complete source,
image, CI, and provenance records.

`artifact/state-eq/` remains a frozen v9 reference. It does not define the v10
release and must not be included in the v10 Zenodo upload.

### Paper

The paper workspace is an independent repository. Its current entry points are:

- `doc/pluto-comprehensive/paper-local/paper/`
- `doc/pluto-comprehensive/paper-local/artifact-report/`
- `doc/pluto-comprehensive/paper-local/workflow/`

Historical paper drafts and plans live under that repository's `archive/`.

### Agent Workflows

Active skills must point to current source and paper locations. Skills tied to
the retired `gifted_curie:/polcert` workflow or completed one-off proof efforts
were removed from the current tree and remain available in Git history.

## Archive

`archive/` preserves superseded development logs, proof plans, design notes,
and possible-bug records. Reproducible outputs, obsolete prototypes, duplicated
research trees, and retired executable workflows were deleted. Archived files
do not define the current artifact, paper narrative, or proof-reading path.

The active v10 source of truth is ordered as follows:

1. frozen implementation and theorem statements;
2. v10 release provenance and complete artifact evidence;
3. paper-local claim and narrative contracts;
4. frozen v9 material and archived notes only for historical explanation.
