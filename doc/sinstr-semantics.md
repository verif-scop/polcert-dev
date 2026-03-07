# `SInstr` Semantics

## Goal

`syntax/SInstr.v` no longer uses an empty instruction semantics. It now instantiates a simple but meaningful state model for the syntax frontend:

- state = total functional store over `MemCell`
- `SSkip` preserves the store
- `SAssign lhs rhs` evaluates `rhs`, computes one target cell from `lhs`, and functionally updates that cell

This keeps the syntax frontend lightweight while giving it real read/write behavior.

## Definition

### State

- `State.t := MemCell -> Z`
- `State.eq` is extensional equality on stores
- `State.dummy_state` maps every cell to `0`

### Instruction semantics

- `SSkip`
  - writes `[]`
  - reads `[]`
  - resulting state is extensionally equal to the input state

- `SAssign lhs rhs`
  - write cell:
    - `exact_cell (access_to_function lhs) p`
  - read cells:
    - syntactically collected from `rhs`
  - resulting state:
    - functional update of the input store at the target cell

### Access discipline

- `valid_access_function` is now non-vacuous
- `access_function_checker_correct` proves that checked accesses overapproximate the dynamic footprint
- `bc_condition_implie_permutbility` is proved by explicit `Skip/Assign` case analysis using the simple store model

## Why this is still lightweight

This is not CompCert memory:

- no blocks
- no alias metadata in the state
- no typing discipline in the store
- no UB model

But it is still semantically meaningful:

- reads and writes correspond to actual cells
- commutation proof is no longer vacuous
- syntax examples are backed by a real state transition system

## Current status

- file changed:
  - `gifted_curie:/polcert/syntax/SInstr.v`
- `opam exec -- make syntax/SInstr.vo` passes
- `opam exec -- make test` passes
- `check-admitted` still reports `Nothing admitted.`
- strict `polopt` batch coverage remains:
  - `45 / 62`

So this change improves the quality of the `SPolIRs` instance without changing the currently observed strict proved-path coverage.
