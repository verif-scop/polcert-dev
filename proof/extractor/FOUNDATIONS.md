# Extractor Foundations

Date: 2026-03-05

## Purpose
This note fixes the shared mental model for extractor work before changing code.

## Pipeline Context
- Current optimization pipeline in Coq:
  - `Extractor.extractor`
  - external scheduler + `Validator.validate`
  - `CodeGen.codegen`
- Proof bottleneck for extractor path:
  - `src/Extractor.v`: `extractor_correct` is still admitted.

## Core IRs (what extractor maps between)
- Loop IR (`Loop.t`): `(stmt, varctxt, vars)`.
  - `stmt`: structured loop program (`Loop`, `Seq`, `Guard`, `Instr`).
  - `varctxt`: symbolic parameters (environment variables for affine forms).
  - `vars`: variable universe used by state typing/init.
- Poly IR (`PolyLang.t`): `(pis, varctxt, vars)`.
  - each `pi` carries `pi_depth`, domain (`pi_poly`), schedule, transformation, accesses.

## Variable/Index Intuition
- `Loop.eval_expr` reads variables by index in runtime `env` (`Var n -> nth n env 0`).
- Extractor builds affine rows over a combined coordinate space:
  - symbolic context coordinates (`varctxt`) + iterator coordinates.
- Therefore, extractor correctness depends on a precise and stable convention for:
  - how `pi_depth` is defined
  - how many columns each affine row has
  - where iterator coordinates are placed.

## Extractor Design (current)
- `expr_to_aff`: affine expression encoder.
  - accepts: `Constant`, `Var`, `Sum`, `Mult`
  - rejects: non-affine/non-supported cases via `Err`
- `test_to_aff`: condition encoder.
  - accepts: `LE`, `EQ`, `And`
  - rejects: unsupported boolean forms via `Err`
- `extract_stmt`:
  - state: `(constrs, env_dim, iter_depth, sched_prefix)`
  - invariant: `cols = env_dim + iter_depth`
  - access handling:
    - use `resolve_access_functions instr` to obtain `(waccess, raccess)`;
    - if one side is `None`, try `[]` for that side;
    - accept only when `Instr.access_function_checker` validates the candidate pair.
  - `Loop`: add bound constraints + one schedule dimension
  - `Seq`: add sequence-position schedule dimension
  - `Guard`: append test constraints
  - `Instr`: emit one `pi`
  - all domain/schedule/transformation/access rows are normalized to `cols`.
- `extractor`:
  - starts from empty constraints/schedule
  - calls `extract_stmt stmt [] (length varctxt) 0 []`
  - runs `check_extracted_wf` before returning success
  - returns `(pis, varctxt, vars)` on success.

## Current Expressive Fragment (practical)
- Supported structural complexity:
  - nested affine loops
  - imperfect nests via `Seq`
  - affine guards via conjunctions (`And`)
  - multi-dimensional affine index/transformation vectors
- Empirical checks in container (`CPolIRs` + `coqtop`) confirm:
  - nested loop + sequence: extractor success (`true`)
  - guard with `And(LE, EQ)`: extractor success (`true`)
  - guard with `Or`: extractor failure (`false`)
  - guard with `Not`: extractor failure (`false`)
  - loop bound with `Div` / `Max`: extractor failure (`false`)
  - index expression with `Mod`: extractor failure (`false`)

## Important Preconditions
- `vars` length must be large enough for all used dimensions:
  - validator check requires `length varctxt + pi_depth <= length vars`.
- instruction metadata must provide access functions:
  - if `waccess` or `raccess` is `None`, extractor can still proceed only if
    filling the missing side with `[]` passes `access_function_checker`;
    otherwise extraction fails.

## What "correct extractor behavior" should mean
- If `extractor loop = Okk pol`, then:
  1. **Well-formedness**:
     - each emitted `pi` satisfies dimension and shape constraints expected by validator/poly semantics.
  2. **Semantic soundness**:
     - poly instance-list semantics for `pol` refines/simulates `Loop.semantics loop`.
  3. **Partiality discipline**:
     - unsupported constructs fail explicitly (`Err`) instead of producing underspecified poly output.

## Current Known Gaps
- Main theorem missing: `extractor_correct`.
- End-to-end extractor soundness proof is still not connected.
- Fragment boundary is now explicit via `wf_scop_stmt` gate in `extractor`;
  remaining gap is to use this predicate as a strong invariant in the structural proof of `extract_stmt`.
