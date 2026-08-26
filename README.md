# PolCert Release Workspace

This repository is the host-side control workspace for the frozen PolCert v9
artifact, paper, and reusable agent workflows. The Rocq/OCaml implementation is
maintained in a separate Git worktree and is not tracked here.

## Current Sources

- Proof and compiler source: `work/parallel-interleaving/`
  - branch: `artifact/verified-compilation-v9-candidate`
  - commit: `604587ecfec9ff3bf6be655dd66e25af6178d604`
  - tag: `state-eq-polyhedral-verification-complete-2026-08-26-v9`
- Artifact harness: `artifact/state-eq/`
- Paper repository: `doc/pluto-comprehensive/paper-local/`
- Paper-facing claim ledger: `doc/STATE_EQ_CLAIM_LEDGER.md`
- Reusable agent skills: `skills/`

Each source, artifact, and paper directory has its own Git state. Inspect and
commit them separately. The ignored `output/`, `tmp/`, and `work/` directories
contain generated results, temporary files, and independent source worktrees.
The hidden `.work/` and `.worktree/` directories are legacy local scratch and
registered historical worktrees; they are not part of the active release tree.

## Active Responsibilities

### Artifact

`artifact/state-eq/` builds and validates the reviewed v9 image. Its manifest,
dependency locks, claim catalog, publication guard, compact evidence, and test
suite are the active artifact interface. Do not move files inside this directory
without rerunning its complete tests and evidence validation.

### Paper

The paper workspace is an independent repository. Its current entry points are:

- `doc/pluto-comprehensive/paper-local/paper/`
- `doc/pluto-comprehensive/paper-local/artifact-report/`
- `doc/pluto-comprehensive/paper-local/workflow/`

Historical paper drafts and plans live under that repository's `archive/`.

### Agent Workflows

Active skills must point to current source and paper locations. Skills tied to
the retired `gifted_curie:/polcert` workflow or completed one-off proof efforts
are retained under `archive/skills/` and must not be selected for current work.

## Archive

`archive/` preserves superseded development logs, proof plans, design notes,
Pluto prototypes, storage-generalization experiments, and retired skills. These
files remain available for provenance but do not define the current artifact,
paper narrative, or proof-reading path.

The active source of truth is ordered as follows:

1. frozen implementation and theorem statements;
2. `doc/STATE_EQ_CLAIM_LEDGER.md` and artifact v9 evidence;
3. paper-local claim and narrative contracts;
4. archived notes only for historical explanation.
