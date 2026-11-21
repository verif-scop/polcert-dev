---
name: pluto-agent-fuzzing
description: Audit Pluto for miscompilations with PolCert as the oracle. Form a hypothesis from Pluto's source or change history, write small targeted loop programs, compile them with Pluto and with PolCert (validators enabled), and compare the source, Pluto's output and PolCert's output by execution. Use when testing Pluto or another polyhedral optimizer, confirming a suspected defect, or preparing an upstream bug report.
---

# Auditing Pluto with PolCert in the Loop

The agent acts as an auditor: it reads one Pluto stage, writes down what could
go wrong, and constructs programs that would expose it. Two oracles accept or
refute each program: PolCert's validators, which name the stage of an illegal
proposal, and differential execution of the source, Pluto's output and
PolCert's output.

## Setup

- Use the PolCert development image with a built PolCert tree mounted at
  `/polcert` (see `ENVIRONMENT.md` there), and run everything from `/polcert`.
- `PLUTO_ROOT` selects the Pluto build. PolCert needs a Pluto with its export
  hooks. The image provides the historical snapshot
  (`/opt/polcert/pluto-buggy`, the default) and the current snapshot
  (`/pluto`). Its `polycc` gives Pluto's own output, and its `tool/pluto` is
  the optimizer that `polopt` calls.
- Scripts: `scripts/check_program.sh` runs one program end to end;
  `scripts/loop_programs.py` turns a `.loop` file into a complete C program.

## Loop

1. **Audit.** Pick one Pluto stage. Read the code, and the recent commits that
   touched it, and write down a concrete hypothesis: the code location, the
   invariant it might break, the expected symptom (wrong sequential result,
   wrong only under OpenMP, a data race, undefined behaviour), and the flags
   that reach it. Places to start:
   - scheduling: `lib/pluto.c`, `lib/framework.cpp`, `lib/framework-dfp.c`;
   - dependences: `lib/program.cpp`, `lib/ddg.c`;
   - tiling and band detection: `lib/tile.c`, `lib/polyloop.c`;
   - index-set splitting: `lib/iss.c`;
   - parallel marking and unroll-and-jam: `tool/ast_transform.c`,
     `tool/pluto_codegen_if.c`;
   - C printing: `cloog-isl/source/clast.c`, `pprint.c`.
2. **Construct programs.** Write small `.loop` programs (PolCert's input
   syntax, see `syntax/README.md`) that would violate the invariant: one to
   three statements, short literal trip counts, affine subscripts in both
   dependence directions. Choose flag sets and a small `TILE_SIZES` file so
   that the suspected path actually runs. Pluto's tests and PolyBench kernels
   are a second source; random programs can be added as a third.
3. **Check.** Run, for each program and flag set:
   ```sh
   TILE_SIZES=tile.sizes scripts/check_program.sh prog.loop --tile --parallel \
     --nodiamond-tile --nointratileopt --nounrolljam --noprevector
   ```
   State `--intratileopt`/`--nointratileopt` and
   `--diamond-tile`/`--nodiamond-tile` explicitly. When `polopt` refuses a
   combination that Pluto needs (e.g. `--prevector` with `--parallel`), pass
   the closest accepted flags in `POLOPT_FLAGS`. Triage the class it prints:

   | Class | Meaning | Next step |
   |---|---|---|
   | `PLUTO-BUG validator` | a validator rejected the proposal and Pluto's output is wrong | the rejecting stage locates the defect; minimize |
   | `PLUTO-BUG reference` | PolCert's output is right and Pluto's is wrong | defect after scheduling (code generation, annotation); minimize |
   | `POLCERT-INCOMPLETE` | PolCert rejected a proposal whose output is right | report it to PolCert as an incompleteness |
   | `SOUNDNESS?` | PolCert's output disagrees with the source | **stop and report immediately** |
   | `OK` / `SKIP` | no defect shown / not applicable | refine the hypothesis or record it as refuted |
4. **Minimize and report.** Shrink statements, loops, trip counts and tile
   sizes while the class stays the same. Then confirm with plain `polycc` on
   upstream Pluto, both the development head and the latest release, outside
   PolCert, since PolCert cannot drive Pluto without the export hooks. Find
   the cause in the source and write the report from `REPORT_TEMPLATE.md`.
   Exclude undefined behaviour in the source: the script already discards
   such programs.
5. **Record refuted hypotheses.** One line each: the hypothesis, the programs
   and flags tried, and why it does not hold. They keep later audits from
   repeating the same work.

`EXAMPLE.md` shows the loop on two known defects.
