# Loop Cleanup Post-Pass Notes

Date: 2026-03-06

## Purpose
- Record the current shape problems in the generated `Loop` output on the experimental `syntax/` path.
- Record a plausible verified `Loop -> Loop` post-pass design for cleaning those shapes.
- Do not change codegen or implement the pass yet.

## Current status
- As of 2026-03-08, the strict proved-path `polopt` suite is back to `62 / 62`.
- Therefore this cleanup pass is no longer part of the semantic blocker set.
- It is now purely about:
  - improving the readability / normal form of generated `Loop` code
  - keeping the cleanup inside the proved pipeline later, instead of leaving it
    as an OCaml-only pretty-print effect
- This strengthens the engineering recommendation:
  - do not change `CodeGen` first
  - add a separate verified `Loop -> Loop` cleanup pass after codegen

## Current Position
- The experimental path
  - parser/elaboration
  - extractor
  - OpenScop / Pluto scheduling
  - validator
  - codegen
  now runs end-to-end on the `matadd.loop` example.
- The remaining issue is output quality, not pass connectivity.
- A lightweight OCaml-side pretty simplifier now exists on the `polopt` path.
- Its current role is display-only:
  - flatten additive chains and fold constants
  - simplify obvious guards
  - print singleton loops in a let-like style
- This is not a verified pass and should not be treated as part of the formal pipeline.
- The right long-term destination for these rewrites is a verified `Loop -> Loop` cleanup pass after codegen.

## Running Example

Input shape:

```text
context(N, M);

for i in range(0, N) {
  for j in range(0, M) {
    C[i][j] = A[i][j] + B[i][j];
  }
}
```

Observed generated `Loop` shape:

```text
if ((-1 * M) <= -1) {
  for i0 in range(0, (1 + (N + -1))) {
    for i1 in range(0, (1 + (M + -1))) {
      for i2 in range(i0, (i0 + 1)) {
        for i3 in range(i1, (i1 + 1)) {
          C[i2][i3] = (A[i2][i3] + B[i2][i3]);
        }
      }
    }
  }
}
```

## What Is Wrong With This Shape

### 1. Singleton loops remain explicit
- `for i2 in range(i0, i0 + 1)` executes exactly one iteration.
- `for i3 in range(i1, i1 + 1)` executes exactly one iteration.
- Semantically, these loops express equalities:
  - `i2 = i0`
  - `i3 = i1`
- Structurally, they should not survive as full loops in the final cleaned program.

### 2. Mechanical guard survives
- `if ((-1 * M) <= -1)` is just a non-emptiness/domain side condition.
- It is equivalent to `M >= 1` or `0 < M`.
- For simple examples, this guard is mechanically correct but not a good final shape.

### 3. Arithmetic is not normalized
- `1 + (N + -1)` should simplify to `N`.
- `1 + (M + -1)` should simplify to `M`.
- These terms are still carrying codegen artifacts.

### 4. Iterator names expose intermediate construction
- `i0`, `i1`, `i2`, `i3` reflect internal generation order.
- The output is therefore proof-friendly but not human-friendly.

## Main Semantic Observation

The crucial redundancy is not arbitrary. It has a clean interpretation:

- outer loops:
  - `i0` scans the first logical iteration dimension
  - `i1` scans the second logical iteration dimension
- inner singleton loops:
  - `i2` is constrained to equal `i0`
  - `i3` is constrained to equal `i1`

So the essential cleanup is:

1. detect singleton loops of the form `for x in [e, e+1)`,
2. replace them by substitution of `x := e` in the body,
3. simplify the resulting expressions/tests.

For the running example, the intended cleanup is:

```text
for i0 in range(0, N) {
  for i1 in range(0, M) {
    C[i0][i1] = A[i0][i1] + B[i0][i1];
  }
}
```

and then optionally rename `i0 -> i`, `i1 -> j`.

## Recommended Post-Pass Structure

### Phase 1: expression/test simplification
- Define `simpl_expr : Loop.expr -> Loop.expr`.
- Define `simpl_test : Loop.test -> Loop.test`.
- Typical rewrites:
  - `x + 0 -> x`
  - `0 + x -> x`
  - `1 * x -> x`
  - `(-1) * (-1 * x) -> x`
  - `1 + (x + -1) -> x`
  - obvious constant folding
  - guard-level boolean simplifications
- Proof target:
  - `Loop.eval_expr env (simpl_expr e) = Loop.eval_expr env e`
  - `Loop.eval_test env (simpl_test t) = Loop.eval_test env t`

### Phase 2: structural cleanup
- Define `cleanup_stmt : Loop.stmt -> Loop.stmt`.
- Basic structural rewrites:
  - `Seq [] -> Skip`
  - `Seq [s] -> s`
  - flatten nested `Seq`
  - `Guard true s -> s`
  - `Guard false s -> Skip`
  - recursively simplify bounds/tests/bodies
- Proof target:
  - `Loop.semantics (cleanup_stmt s) st1 st2 <-> Loop.semantics s st1 st2`
  - or the project's preferred refinement/`State.eq` form

### Phase 3: singleton loop elimination
- Detect loops of the form:
  - `Loop.Loop lb ub body`
  - where `ub` simplifies to `lb + 1`
- Eliminate them by substituting the loop variable with `lb` in the body.

The key transformation idea is:

```text
for x in range(e, e+1) { body }
  ~~>
body[x := e]
```

This is the main cleanup required for the current example.

## Important Design Choice: substitution vs let

Two plausible implementations:

### Option A: direct substitution
- Define capture-avoiding substitution on `Loop.expr`, `Loop.test`, and `Loop.stmt`.
- Eliminate singleton loops by direct replacement.
- Advantage:
  - no language change
  - easier to keep local to the post-pass
- This is the preferred route if we want to avoid touching core IR definitions.

### Option B: introduce an explicit `let`-style normalization form
- Represent singleton loop elimination as:
  - `let x = e in body`
- Then run a second substitution/elimination pass.
- Advantage:
  - clearer intermediate shape
- Disadvantage:
  - requires either extending `Loop` or introducing another cleanup IR
  - this is too invasive for the current stage

Current recommendation:
- use direct substitution, not `let`

## Why This Should Be A Post-Pass

- The issue is in final `Loop` shape, not in scheduler correctness.
- The issue is local and syntactic enough that a separate proof should be manageable.
- This keeps the engineering split clean:
  - codegen proves it produces a correct `Loop`
  - cleanup proves it preserves `Loop` semantics while improving shape

This is better than immediately reworking PolyGen internals, because it:
- isolates proof obligations,
- avoids destabilizing the existing verified codegen story,
- and directly targets the observed artifacts.

## Proposed Minimal Deliverable

If implemented later, the minimal verified cleanup pass should do:

1. expression simplification
2. test simplification
3. `Seq`/`Guard` cleanup
4. singleton loop elimination by substitution

That is enough to materially improve the current generated shape.

## Recommended proof decomposition

The current implementation experience suggests the pass should be split into
three separately testable and separately provable layers.

### Layer 1: pure expression normalization
- Scope:
  - `Loop.expr`
  - `Loop.test`
- Examples:
  - additive flattening
  - constant folding
  - `1 + (N + -1) -> N`
  - `(-1 * N) <= -1 -> 1 <= N`
- Proof burden:
  - direct semantic preservation of expression/test evaluation
- This is the lowest-risk first step.

### Layer 2: structural cleanup
- Scope:
  - `Seq`
  - trivial `Guard`
  - recursive simplification of loop bounds / tests / bodies
- Examples:
  - flatten nested sequences
  - remove `Guard true`
  - rewrite `Guard false` to `Skip`
- Proof burden:
  - straightforward induction on `Loop.stmt`
- This is also low-risk.

### Layer 3: singleton-loop elimination
- Scope:
  - loops whose upper bound simplifies to lower-bound `+ 1`
- Example:
  - `for x in range(e, e+1) { body } -> body[x := e]`
- Proof burden:
  - substitution lemma for `Loop.expr` / `Loop.test` / `Loop.stmt`
  - loop-semantics equivalence for the singleton case
- This is the first part that is not purely local rewriting, but it is still a
  standard proof-engineering task.

## Practical recommendation

If this is taken on later, the order should be:

1. implement Layer 1 in Coq and prove it
2. implement Layer 2 in Coq and prove it
3. only then implement Layer 3

This keeps the cleanup effort isolated from the now-stable verified optimizer
pipeline and avoids mixing readability work with scheduler/codegen correctness.

## Current OCaml Prototype vs Future Coq Pass

The current pretty-printer already prototypes a small subset of this cleanup:

- additive reassociation / constant folding
- simple comparison normalization
- singleton-loop pretty elimination

This is useful for inspecting optimization results, but it has two strict limits:

- it changes printing, not IR
- it carries no proof

So this prototype should be treated as a guide for a later verified cleanup pass, not as the final implementation strategy.

## Non-goals For The Cleanup Pass

- do not change `Loop` semantics
- do not change `PolyLang` semantics
- do not attempt general loop interchange/fusion/tiling cleanup
- do not solve naming prettification first

The first target should be semantic redundancy, not aesthetics.

## Suggested Future Theorem Shape

For a later implementation, a useful statement would be:

```text
Theorem cleanup_correct :
  forall s st1 st2,
    Loop.semantics (cleanup_stmt s) st1 st2 ->
    Loop.semantics s st1 st2.
```

and ideally also the converse, if the cleanup is fully semantics-preserving:

```text
Theorem cleanup_correct_iff :
  forall s st1 st2,
    Loop.semantics (cleanup_stmt s) st1 st2 <->
    Loop.semantics s st1 st2.
```

## Immediate Takeaway

- Yes: the current ugly shape is largely explained by equalities such as `i2 = i0`.
- Yes: a verified post-pass is the right place to clean it.
- No: this should not be implemented yet before the current pipeline state is documented and stabilized.
