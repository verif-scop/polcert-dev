# Affine Scheduling Proof Cleanup Audit

- Date: 2026-07-18
- Status: audit complete; batches 1--5 executed on a separate proof-only branch
- Baseline tag: `state-eq-polyhedral-verification-complete-2026-05-25-v2`
- Baseline commit: `13295e741ad62173411882c6d900dd9dc57337a8`

## Decision

The affine scheduling proof is complete, but `src/AffineValidator.v` carries
substantial maintenance debt. Cleanup is justified, especially before the
proof is presented in detail in a paper, but it is not a correctness blocker.

Do not start the proof rewrite until the exact baseline above has been built
and archived by the State.eq artifact workflow. Perform the cleanup on a new
branch or worktree, do not move the published tag, and keep the archived image
capable of reproducing the pre-cleanup result.

The first cleanup pass should change proof bodies only. It should not change
validator definitions, theorem statements, extraction roots, accepted inputs,
or generated code.

## Execution Status

Five bounded cleanup batches are committed on
`proof-cleanup-affine-batch1`, which starts from the frozen baseline:

- `50aefe5`: remove duplicate affine list proof;
- `7a62341`: factor affine access noncollision;
- `711d10d`: share affine access shape facts;
- `b5b2c32`: share affine permutation semantics core;
- `c166170`: share affine checker soundness decoding.

Batch 5 factors the common Boolean checker decoder and program-level
`forallb` lift used by affine and tiling soundness. Its final checks passed the
full proof, `check-admitted`, extraction, the second-level suite, and artifact
smoke. A byte-level audit found no change to public theorem statements,
computational definitions, imports, axioms, parameters, hints, or extraction
roots. The frozen tag and reviewed image remain unchanged.

## Audit Method

The implementation repository was inspected in a clean detached worktree at
`/tmp/polcert-affine-proof-audit`. At the end of the audit:

```text
## HEAD (no branch)
13295e741ad62173411882c6d900dd9dc57337a8
state-eq-polyhedral-verification-complete-2026-05-25-v2
```

The current file has 4,706 lines. The inherited affine validator can be seen
at commit `d89da3d` as `src/Validator.v` and has 3,069 lines. The 2026 work
moved that proof into `src/AffineValidator.v` and extended it for witness-aware
current spaces and tiling. Consequently, this audit distinguishes:

- inherited affine scheduling proof structure;
- current-space composition support added for tiling;
- duplicated affine and tiling wrappers at the end-to-end boundary.

Line references below are for commit `13295e7` and will move after cleanup.

## Proof and Dependency Map

The proof core is `src/AffineValidator.v`. Its main layers are:

| Layer | Evidence | Role |
| --- | --- | --- |
| Boolean well-formedness and EqDom | lines 184-636 | Computational validators and access/dependence checks |
| Checker soundness | lines 638-974 | Turns Boolean results into `wf_*` and `eqdom_*` propositions |
| Paired instance construction | lines 976-1958 | Relates old and new instruction instances |
| Dependence and access exclusion | lines 1961-2902 | Establishes no conflicting cells and pairwise permutability |
| List flattening and composition | lines 2905-4085 | Lifts instruction proofs to complete instance lists |
| End-to-end correctness | lines 4087-4704 | Affine and tiling route wrappers ending in `State.eq` |

Important direct dependencies include:

- `src/PolyLang.v`: instance semantics, flattening, schedule order,
  `Permutable_ext`, current-space transformations, and State.eq lifting;
- `src/PolyBase.v`, `src/PolyOperations.v`, and `src/Linalg.v`: polyhedral and
  affine operations used by the validator;
- `src/PointWitness.v` and `src/TilingWitness.v`: point-space dimensions and
  witness equality;
- `src/PolIRs.v`: the semantic module interface;
- `src/Validator.v`: the public facade over the affine core.

Downstream proof consumers make this file a shared boundary:

- `src/Extractor.v:1966-1977,2094` uses `check_wf_polyinstr` and its soundness
  theorem;
- `src/ParallelValidator.v:810-941` uses `validate` and
  `validate_implies_permutability`;
- `src/JamValidator.v:125-180` and `src/LoopJamValidator.v:133-315` use the
  same affine validation interface;
- `src/TilingValidator.v:965-1159` uses `validate_general`,
  `validate_tiling_correct`, and `check_wf_polyprog_tiling_correct`;
- `driver/PolOpt*.v` relies on the facade's well-formedness and correctness
  theorems.

## Interfaces to Preserve

All existing declarations should remain available under their current names
and with definitionally compatible statements during the first cleanup pass.
The following are especially important because they are re-exported or used
outside `AffineValidator.v`:

### Computational interface

- `check_wf_polyinstr`, `check_wf_polyprog`
- `check_wf_polyinstr_tiling`, `check_wf_polyprog_tiling`
- `check_wf_polyinstr_general`, `check_wf_polyprog_general`
- `EqDom`, `check_valid_access`, `validate_instr_list`
- `validate`, `validate_tiling`, `validate_general`

These definitions flow into the extracted compiler. Do not refactor their
bodies as part of proof beautification, even when an equivalent formulation
looks simpler.

### Proof interface

- `check_wf_polyinstr_affine_correct`
- `check_wf_polyinstr_correct`
- `check_wf_polyprog_affine_correct`
- `check_wf_polyprog_correct`
- `check_wf_polyprog_tiling_correct`
- `validate_implies_permutability`
- `validate_tiling_implies_permutability`
- `validate_preserve_wf_pprog`
- `validate_correct`, `validate_tiling_correct`

Keep the remaining helper names as well. A repository search shows that some
are currently file-local, but removing them would still be an unnecessary API
change for external Coq clients.

Proofs closed with `Qed` are erased by extraction, so changing only their
bodies has no runtime effect. Risks arise if the cleanup changes a theorem
statement, changes a computational `Definition`, changes transparency, or
adds global hints that alter downstream proof search.

## Concrete Duplication and Fragility

### 1. Repeated access-cell lifting

`no_w_collision_implies_permutability` contains three nearly identical
derivations that lift access-function noncollision to concrete semantic cells:

- WW at lines 2386-2404;
- WR at lines 2405-2423;
- RW at lines 2424-2442.

Each block unfolds the same validity hypothesis, obtains a source access for a
runtime cell, applies a nested `Forall`, and transports `cell_neq` through cell
equality. The only differences are the write/read projection and orientation.
This is inherited affine proof structure and is the clearest first target for
a named generic lemma.

### 2. Repeated WW, WR, and RW validator obligations

`validate_two_instrs_implies_no_write_collision` is 262 lines. Its three main
branches at lines 2617-2683, 2685-2761, and 2763-2843 repeat:

- instance transformation equalities;
- exact column facts from well-formedness;
- access/transformation matching facts;
- environment and domain product membership;
- old-schedule-lt and new-schedule-ge membership.

The branches differ only in which access lists are selected and whether the
result must be symmetrized. This should become one helper for a validated pair
of access lists, instantiated three times.

### 3. Duplicated direction proofs

`no_write_collision_implies_permutable` repeats the two semantic execution
directions at lines 2466-2523 and 2524-2580. Nested `Forall` symmetry is rebuilt
by hand in both directions.

Likewise,
`validate_instr_and_list_implies_permutability1` at lines 3142-3218 and
`validate_instr_and_list_implies_permutability2` at lines 3821-3898 repeat the
same reverse-list induction. The second changes the selected Boolean result,
swaps the instruction pair, and applies `Permutable_ext_symm`.

### 4. Legacy and current-space composition pairs

There are parallel proofs for `compose_ipl_ext` and `compose_ipl_ext_at`:

- element projections: lines 1002-1058;
- membership inversion: lines 1388-1450;
- `nth_error` inversion and construction: lines 1452-1523;
- old/new list projections: lines 1525-1642;
- append-singleton: lines 1690-1725;
- sortedness: lines 2979-3017;
- NoDup: lines 3240-3294;
- length preservation: lines 3967-4005.

There is also a literal duplicate: `nth_error_compose_ipl_ext_inv_local` at
lines 1452-1470 and `nth_error_compose_ipl_ext_inv` at lines 3220-3238 have the
same statement and proof. The latter is unused at this baseline. Preserve its
name, but prove it by applying the earlier lemma.

Not every old/`_at` pair can be replaced by simple rewriting. The legacy
constructor takes each instance's transformation, while `_at` takes one
explicit access transformation for the whole list. Generic list lemmas should
abstract over the element constructor instead of asserting a false global
equality between the two functions.

### 5. Affine and tiling route duplication

The final section duplicates the same proof skeleton for the two validators:

- correspondence: lines 4087-4112 and 4348-4373;
- permutability witness construction: lines 4135-4259 and 4375-4509;
- semantic State.eq result: lines 4261-4346 and 4511-4596;
- instance-semantics wrapper: lines 4624-4663 and 4665-4704.

The two 86-line primed correctness proofs are identical after substituting the
finite-preservation and permutability lemmas. The two 40-line final wrappers
are also identical after substituting correspondence and primed correctness.
This is high-volume duplication with a relatively clear abstraction boundary.

### 6. Duplicated checker decoding

`check_wf_polyinstr_affine_correct` at lines 653-740 and
`check_wf_polyinstr_tiling_correct` at lines 752-835 destruct the same sequence
of Boolean checks and reconstruct the same common `wf_pinstr` facts. The
program-level lifts at lines 837-897 are similarly parallel.

The affine checker has extra identity-witness and transformation-equality
obligations. A common lemma should return the shared well-formedness facts,
with small route-specific wrappers for the extra conclusions.

### 7. Naming and proof readability

The file contains 258 uses of `eauto`, 122 uses of `simpls`, 87 uses of
`tryfalse`, 24 uses of `firstorder`, and many positional hypotheses such as
`H0` through `H5`. Broad automation is not itself wrong, but it makes large
proofs sensitive to context changes and obscures which invariant closes a
goal.

Public names also contain historical problems:

- `eqdom_perserve_finite_forward` and `eqdom_perserve_finite` misspell
  "preserve";
- `validate_*_implies_permut_no_collision1` uses awkward grammar and an
  unexplained numeric suffix;
- `no_w_collision_implies_permutability` and
  `no_write_collision_implies_permutable` do not communicate their different
  abstraction levels.

Do not rename these declarations outright. Add correctly named internal
helpers or compatibility aliases, migrate local uses, and retain the legacy
names.

## Ordered Cleanup Batches

Each batch should be a separate commit. Stop and investigate if a proof needs
a changed theorem statement or a changed validator definition.

### Batch 1: Structural helper foundation

Risk: low.

1. Add section comments for checker soundness, paired instances, access
   exclusion, list lifting, and end-to-end correctness.
2. Add local generic lemmas for nested `Forall` transport and symmetry of
   `cell_neq`.
3. Add local element-constructor-parametric list lemmas for membership and
   `nth_error`, then use them in the legacy and `_at` wrappers.
4. Replace the proof of `nth_error_compose_ipl_ext_inv` with an application of
   `nth_error_compose_ipl_ext_inv_local` while preserving both names.
5. Replace positional hypotheses in the touched small proofs with descriptive
   names. Do not perform a file-wide renaming pass.

Verification:

```sh
eval "$(opam env --switch=polcert --set-switch)"
make depend
make -j4 src/AffineValidator.vo
make -s check-admitted
git diff --check
```

Review the diff to confirm that no declaration statement before `Proof.` and
no computational definition changed.

### Batch 2: Access validity to concrete-cell noncollision

Risk: low to moderate.

1. Introduce a named lemma that, given `Instr.valid_access_function`, maps a
   runtime write/read cell back to an access function.
2. Introduce one transport lemma that preserves `cell_neq` across the two cell
   equalities returned by validity.
3. Rewrite the WW, WR, and RW blocks in
   `no_w_collision_implies_permutability` as three short instantiations.
4. Use the nested-`Forall` symmetry helper to remove the repeated blocks in
   `no_write_collision_implies_permutable`.

Do not change `no_write_collision`, `Permutable_ext`, or the statements of the
two public lemmas.

Verification:

```sh
eval "$(opam env --switch=polcert --set-switch)"
make -j4 src/AffineValidator.vo
make -j4 src/ParallelValidator.vo src/JamValidator.vo src/LoopJamValidator.vo
make -s check-admitted
git diff --check
```

### Batch 3: One access-pair validator proof, three instantiations

Risk: moderate; this is the semantic center of affine scheduling validation.

1. Factor the common transformation, column, domain, environment, and schedule
   obligations from `validate_two_instrs_implies_no_write_collision` into a
   helper for a selected pair of access lists.
2. Parameterize the helper over write/read selectors and result orientation.
   Prefer explicit arguments over a custom tactic.
3. Instantiate it for WW, WR, and RW, applying the symmetry lemma only for RW.
4. Give all hypotheses semantic names; remove reliance on `firstorder` for
   extracting fixed fields from well-formedness when direct destructuring is
   clearer.

Verification:

```sh
eval "$(opam env --switch=polcert --set-switch)"
make -j4 src/AffineValidator.vo
make -j4 proof
make -s check-admitted
make extraction
make -j4 polopt polcert
make test-parallel-current-suite
```

The extraction step is a guard against accidentally changing a computational
declaration. A proof-only diff should not alter the extracted validator's
behavior.

### Batch 4: Affine/tiling route-neutral semantic core

Risk: moderate.

1. Extract the shared 86-line semantic argument from `validate_correct'` and
   `validate_tiling_correct'`. The helper should consume only:
   - finite existence in both programs;
   - the composed instance-list witness;
   - pairwise `Permutable_ext` for inversions;
   - `NonAlias` and target semantics.
2. Keep each primed theorem as a small wrapper that obtains those facts from
   its validator-specific lemmas.
3. Extract the shared instance-semantics wrapper used by `validate_correct`
   and `validate_tiling_correct`.
4. Preserve the four theorem statements exactly.

Verification:

```sh
eval "$(opam env --switch=polcert --set-switch)"
make -j4 proof
make -s check-admitted
make extraction
make -j4 polopt polcert
make artifact-check
```

### Batch 5: Common well-formedness checker decoding

Risk: moderate.

1. Factor the shared Boolean decoding in
   `check_wf_polyinstr_affine_correct` and
   `check_wf_polyinstr_tiling_correct` into a lemma that establishes the
   common `wf_pinstr` fields.
2. Leave identity-witness and transformation-equality conclusions in the
   affine wrapper.
3. Factor the common `forallb` program lift used by the affine and tiling
   program-level theorems.
4. Do not merge `check_wf_polyinstr` with `check_wf_polyinstr_tiling`; only
   their soundness proofs are in scope.

Verification:

```sh
eval "$(opam env --switch=polcert --set-switch)"
make -j4 src/AffineValidator.vo src/Extractor.vo src/TilingValidator.vo
make -j4 proof
make -s check-admitted
make extraction
make test-second-level-tile-suite
```

### Batch 6: Direction-neutral list permutability traversal

Risk: moderate to high.

Factor the reverse-list induction shared by
`validate_instr_and_list_implies_permutability1` and
`validate_instr_and_list_implies_permutability2`. The common lemma should take
the selected pairwise validator result and orientation as explicit premises.
Keep the two existing declarations as wrappers.

This batch should follow the collision cleanup because the required symmetry
and orientation helpers will already exist. Do not start by introducing a
large Ltac that hides the direction changes.

Verification:

```sh
eval "$(opam env --switch=polcert --set-switch)"
make -j4 proof
make -s check-admitted
make extraction
make -j4 polopt polcert
make test-pluto-compat-suite
make test-parallel-current-suite
```

### Batch 7: Compatibility names and final presentation

Risk: low if aliases are additive; high if old names are removed.

1. Add descriptive aliases for misspelled or opaque helper names only where
   they improve the paper-facing proof path.
2. Retain all legacy declarations.
3. Add short comments stating the mathematical role of the main lemmas; avoid
   narrating individual tactics.
4. Remove an import only in a separate commit and only after a clean build
   demonstrates it is unused.
5. Run the full archived claim suite before considering the cleanup complete.

Verification:

```sh
eval "$(opam env --switch=polcert --set-switch)"
make clean
make depend
make -j4 proof
make -s check-admitted
make extraction
make -j4 polopt polcert
make artifact-check-full
git diff --check
```

## Recommended First Three Batches

The best initial sequence after artifact archival is:

1. **Structural helper foundation.** It removes one literal duplicate and
   establishes small reusable lemmas without touching semantic arguments.
2. **Access validity to concrete-cell noncollision.** It removes the clearest
   inherited WW/WR/RW copy-paste from the original affine proof.
3. **One access-pair validator proof, three instantiations.** It addresses the
   largest repeated block in the dependence validator while reusing the
   helpers proven in batch 2.

After these, the route-neutral State.eq core in batch 4 offers the largest
additional reduction with a clean abstraction boundary. Batches 5 and 6 are
more sensitive to proposition shape and proof orientation and should not be
the first edits.

## Completion Criteria

The cleanup is complete only when:

- the exact pre-cleanup tag remains reproducible by the archived Docker image;
- no computational interface or theorem statement listed above changed;
- the project has no new admitted proof or unrealized extraction axiom;
- the clean full proof and extraction build passes;
- `artifact-check-full` passes from a clean tree;
- the paper can cite a short, named proof chain from Boolean affine validation
  through pairwise permutability to `State.eq`, without relying on duplicated
  route-specific scripts.
