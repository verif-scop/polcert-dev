# polcert-dev

This repository is the host-side development workspace for the PolCert project.

It is **not** the main source repository used for Coq/OCaml builds.

The implementation repository lives inside the Docker container:

- container: `gifted_curie`
- repo path: `/polcert`
- active branch used in recent work: `extractor`

## Purpose

This outer workspace is for:

- persistent notes
- proof planning
- memory files for context recovery
- local skills/instructions
- lightweight scratch files

It acts as the research notebook and operational control surface around the real container-side repo.

## Important Files

- [MUST_READ.md](./MUST_READ.md)
  - the quickest context-recovery seed
  - read this first after losing context
- [LOG.md](./LOG.md)
  - chronological working log
  - records important experiments, results, and state transitions
- [PLAN.md](./PLAN.md)
  - higher-level working plan
- [PROJECT_UNDERSTANDING.md](./PROJECT_UNDERSTANDING.md)
  - stable understanding of the project structure and current position

## Main Directories

- [`doc/`](./doc)
  - focused design/proof notes
  - example: `loop-cleanup-postpass.md`
- [`proof/`](./proof)
  - proof-engineering notes and active theorem plans
  - currently centered on `proof/extractor/`
- [`skills/`](./skills)
  - reusable local skills/instructions for recurring workflows
- [`work/`](./work)
  - scratch or copied working files when useful
  - intentionally ignored from version control in this repo
- [`.work/`](./.work)
  - extra hidden scratch area

## Current Focus Areas

As of the latest updates, the main active themes are:

- extractor proof closure and related proof engineering
- syntax-level frontend experimentation
- OpenScop / Pluto compatibility
- output-shape cleanup planning for generated `Loop` programs

## Recommended Workflow

1. Recover context from this outer workspace.
   - start with `MUST_READ.md`
   - then inspect `LOG.md`
2. Do actual code/proof work inside the container repo.
   - use `docker exec gifted_curie sh -lc 'cd /polcert && ...'`
3. After important progress:
   - update `LOG.md`
   - update `MUST_READ.md` if the recovery seed changed
   - update `PROJECT_UNDERSTANDING.md` if the stable mental model changed
   - add or update a skill if a workflow became reusable
4. Keep this outer workspace as the durable memory layer, not the primary build tree.

## Typical Commands

Check container repo state:

```sh
docker exec gifted_curie sh -lc 'cd /polcert && git rev-parse --abbrev-ref HEAD && git rev-parse --short HEAD'
```

Run a full build in the container:

```sh
docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make'
```

Check admitted proofs:

```sh
docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make -s check-admitted'
```

Run the syntax frontend smoke path:

```sh
docker exec gifted_curie sh -lc 'cd /polcert && ./polopt syntax/examples/matadd.loop'
```

## Scope Boundary

Keep the distinction clear:

- this host directory tracks notes, plans, and reusable workflow knowledge
- `/polcert` inside the container is the real implementation and proof repository

Do not assume that git state in this outer workspace reflects git state in the container repo.
