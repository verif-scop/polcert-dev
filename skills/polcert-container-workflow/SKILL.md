---
name: polcert-container-workflow
description: Work on the PolCert project (CompCert + polyhedral validation/codegen) in the Docker container `gifted_curie` with image `hughshine/polcert:latest`. Use when tasks involve reading or modifying `/polcert`, running Coq/OCaml build commands, auditing proof gaps (Admitted/Abort/Axiom/Parameter), validating OpenScop cases with `polcert`, or maintaining project logs/plans in the host workspace.
---

# PolCert Container Workflow

Run PolCert tasks from host by operating on the container filesystem and keeping host-side notes.

## Core Workflow

1. Verify target container and repository state.
2. Run commands through Docker into `/polcert`.
3. Load opam switch before build-related commands.
4. Run baseline checks before and after meaningful edits.
5. Keep `LOG.md` and `PLAN.md` in host workspace updated.

## Command Pattern

Use this pattern for almost every project command:

```bash
docker exec gifted_curie sh -lc 'cd /polcert && <command>'
```

Run build and Coq tooling only after:

```bash
eval $(opam env --switch=polcert --set-switch)
```

## Baseline Checks

Use `scripts/baseline_check.sh` for a quick project health snapshot. It checks:
- branch and commit
- presence of `ocamldep` and `coqc` in PATH after opam setup
- `make -s check-admitted`
- one known-good OpenScop validation run

## Proof Gap Audit

Use these scans when creating proof TODOs:

```bash
grep -RInE 'Admitted\.|Abort\.|Axiom ' src polygen driver
grep -RInE '^Parameter |^Axiom ' src polygen driver common cfrontend cparser lib VPL
```

Focus first on pipeline-critical theorem gaps and their immediate dependencies.

## References

- Open [references/project-notes.md](references/project-notes.md) for a compact map of commands, files, and current known gaps.
