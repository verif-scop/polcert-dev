# Core Definition Map

This note records the current semantic spine of the live PolCert/PolOpt tree in
`gifted_curie:/polcert` at the latest reviewed `end-to-end` HEAD.

The local workspace here is documentation-focused, so the source locations below
refer to the live container tree, not to files vendored into this docs repo.
Line numbers are therefore snapshots and may drift as the Coq files evolve.

## Reading order

If you need to rebuild the mental model of the project quickly, read in this
order:

1. `gifted_curie:/polcert/polygen/Loop.v`
2. `gifted_curie:/polcert/polygen/IterSemantics.v`
3. `gifted_curie:/polcert/polygen/InstanceListSema.v`
4. `gifted_curie:/polcert/src/PolyLang.v`
5. `gifted_curie:/polcert/src/Extractor.v`
6. `gifted_curie:/polcert/src/StrengthenDomain.v`
7. `gifted_curie:/polcert/src/AffineValidator.v`
8. `gifted_curie:/polcert/src/PrepareCodegen.v`
9. `gifted_curie:/polcert/polygen/CodeGen.v`
10. `gifted_curie:/polcert/driver/PolOptCorrect.v`
11. `gifted_curie:/polcert/src/ParallelCodegen.v`
12. `gifted_curie:/polcert/driver/ParallelPolOptCorrect.v`

## Core syntax and semantics

### `Loop` IR

This is the concrete sequential loop language consumed and produced by the main
verified optimizer pipeline.

| Item | Location | Role | Review note |
| --- | --- | --- | --- |
| `expr` | `gifted_curie:/polcert/polygen/Loop.v:55` | Arithmetic expression syntax | Includes `Div`, `Mod`, `Max`, `Min`, not just affine arithmetic. |
| `eval_expr` | `gifted_curie:/polcert/polygen/Loop.v:65` | Expression evaluation | `Var n` uses `nth n env 0`; out-of-bounds variables silently read as `0`. |
| `test` | `gifted_curie:/polcert/polygen/Loop.v:126` | Guard syntax | Includes `Or` and `Not`, which are outside the affine extractor fragment. |
| `stmt` | `gifted_curie:/polcert/polygen/Loop.v:182` | Loop IR syntax | Core constructors are `Loop`, `Instr`, `Seq`, `Guard`. |
| `wf` | `gifted_curie:/polcert/polygen/Loop.v:198` | Intended loop well-formedness predicate | Currently a placeholder returning `True`; this is not yet a meaningful invariant. |
| `loop_semantics` | `gifted_curie:/polcert/polygen/Loop.v:203` | Small-step-style structural semantics over a loop body | Uses `IterSem.iter_semantics` for concrete loop iteration. |
| `loop_semantics_aux` | `gifted_curie:/polcert/polygen/Loop.v:222` | List-oriented auxiliary semantics | Mainly used to connect recursive list execution to `iter_semantics`. |
| `semantics` | `gifted_curie:/polcert/polygen/Loop.v:589` | Whole-program semantics | Wraps `loop_semantics` with environment initialization and state compatibility assumptions. |
| `and_all_correct` | `gifted_curie:/polcert/polygen/Loop.v:690` | Sanity theorem for conjunction construction | Useful when reading generated guard code. |

#### Important review notes for `Loop`

- `Div` and `Mod` carry an arbitrary `Z` divisor in the syntax:
  `gifted_curie:/polcert/polygen/Loop.v:59-60`.
- `eval_expr`, `make_div`, and `make_mod` do not encode a nonzero-divisor side
  condition:
  `gifted_curie:/polcert/polygen/Loop.v:70-71`,
  `gifted_curie:/polcert/polygen/Loop.v:98-112`.
- `Loop.wf` is still vacuous, so it should not be read as an actual syntactic or
  scope discipline:
  `gifted_curie:/polcert/polygen/CodeGen.v:214-223`.

### Generic iteration and point-list semantics

These files define the reusable execution skeleton used by both `Loop` and
`PolyLang`.

| Item | Location | Role | Review note |
| --- | --- | --- | --- |
| `iter_semantics` | `gifted_curie:/polcert/polygen/IterSemantics.v:27` | Generic left-to-right relational list iteration | The base sequencing combinator for loop execution. |
| `iter_semantics_e` | `gifted_curie:/polcert/polygen/IterSemantics.v:33` | Generic iteration with an auxiliary payload list | Used in some staged semantics arguments. |
| `InstrPoint` | `gifted_curie:/polcert/polygen/InstanceListSema.v:37` | Concrete flattened execution point | Packages instruction id, dynamic index, transformation, schedule, and depth. |
| `instr_point_sema` | `gifted_curie:/polcert/polygen/InstanceListSema.v:64` | Single flattened-point semantics | Runs one instruction at one dynamic point. |
| `instr_point_list_semantics` | `gifted_curie:/polcert/polygen/InstanceListSema.v:142` | Sequential semantics of a sorted list of instruction points | This is the core target relation for many refinement proofs. |

### `PolyLang`

This is the semantic polyhedral IR. It is the main verified bridge between
extracted loop syntax and scheduled / transformed programs.

| Item | Location | Role | Review note |
| --- | --- | --- | --- |
| `PolyInstr` | `gifted_curie:/polcert/src/PolyLang.v:48` | One polyhedral instruction with schedule, domain, witness, and accesses | This is the semantic payload that most proofs talk about. |
| `t` | `gifted_curie:/polcert/src/PolyLang.v:79` | Whole polyhedral program | Triple `(pis, varctxt, vars)`. |
| `wf_pinstr` | `gifted_curie:/polcert/src/PolyLang.v:1088` | Structural well-formedness of one polyhedral instruction | Encodes column counts, witness shape, and access widths. |
| `wf_pinstr_affine` | `gifted_curie:/polcert/src/PolyLang.v:1125` | Affine well-formedness | Identity point witness plus matching transformations. |
| `wf_pinstr_general` | `gifted_curie:/polcert/src/PolyLang.v:1132` | Witness-aware well-formedness | Used for tiling and current-view reasoning. |
| `wf_pprog_affine` | `gifted_curie:/polcert/src/PolyLang.v:1148` | Affine program well-formedness | Main precondition for default prepare/codegen theorems. |
| `wf_pprog_general` | `gifted_curie:/polcert/src/PolyLang.v:1160` | General witness-aware program well-formedness | Main precondition for tiled and current-view routes. |
| `current_view_pi` | `gifted_curie:/polcert/src/PolyLang.v:1242` | Converts a witness-aware instruction into current-view form | Key normalization step before general codegen. |
| `current_view_pprog` | `gifted_curie:/polcert/src/PolyLang.v:1256` | Program-level current-view conversion | Used by `prepared_codegen_correct_general`. |
| `scanned` | `gifted_curie:/polcert/src/PolyLang.v:1495` | Removes one dynamic point from a scan predicate | Internal engine step for operational semantics. |
| `env_scan` | `gifted_curie:/polcert/src/PolyLang.v:1508` | Initial dynamic-point membership predicate for one environment | Seeds `poly_semantics`. |
| `poly_semantics` | `gifted_curie:/polcert/src/PolyLang.v:1527` | Main implicit-point operational semantics | Executes the minimum-schedule enabled point at each step. |
| `semantics` | `gifted_curie:/polcert/src/PolyLang.v:1576` | Whole-program polyhedral semantics | Wraps `poly_semantics` with environment initialization. |
| `flatten_instrs` | `gifted_curie:/polcert/src/PolyLang.v:1957` | Declarative flattening relation from poly program to point list | Encodes membership, uniqueness, and sortedness. |
| `instance_list_semantics` | `gifted_curie:/polcert/src/PolyLang.v:3942` | Whole-program flattened semantics | Central target/source relation for extractor, validator, tiling, and ISS proofs. |
| `instance_list_semantics_current_view_iff` | `gifted_curie:/polcert/src/PolyLang.v:3951` | Current-view equivalence lemma | Important bridge for general witness-aware codegen. |

#### Important review notes for `PolyLang`

- `PolyLang` semantics itself is not the issue; the key discipline is external:
  most main theorems assume `wf_pprog_affine` or `wf_pprog_general`.
- `from_openscop_complete` deliberately erases instruction semantics by using
  `Instr.dummy_instr`:
  `gifted_curie:/polcert/src/PolyLang.v:1062-1085`.
  That is correct for validation-only paths, but it should not be read as a
  semantics-preserving import theorem.

### Parallel IR

The explicit-dimension parallel route has its own target language and proof
objects.

| Item | Location | Role | Review note |
| --- | --- | --- | --- |
| `stmt` | `gifted_curie:/polcert/polygen/ParallelLoop.v:34` | Parallel loop/program syntax | This is separate from sequential `Loop.stmt`. |
| `semantics` | `gifted_curie:/polcert/polygen/ParallelLoop.v:209` | Whole-program parallel semantics | Used only by the theorem-aligned explicit parallel route. |
| `trace_safe` | `gifted_curie:/polcert/polygen/ParallelLoop.v:231` | Safety predicate for generated parallel traces | Consumed by `annotated_codegen_correct_general`. |

## Key theorem chain

The most useful way to read the proof stack is as a refinement chain from
generated or transformed artifacts back to the original source loop.

### Extraction and normalization

| Item | Location | Statement intent |
| --- | --- | --- |
| `extractor` | `gifted_curie:/polcert/src/Extractor.v:2002` | Extracts affine SCoP fragments from `Loop.t` into `PolyLang.t`. |
| `extractor_correct` | `gifted_curie:/polcert/src/Extractor.v:10159` | If extracted polyhedral semantics runs, the original loop semantics can match it. This is one-way, not completeness. |
| `strengthen_pprog` | `gifted_curie:/polcert/src/StrengthenDomain.v:87` | Strengthens domains before scheduling/validation. |
| `instance_list_semantics_unstrengthen` | `gifted_curie:/polcert/src/StrengthenDomain.v:474` | Strengthened execution refines back to the original polyhedral program. |

### Validation

| Item | Location | Statement intent |
| --- | --- | --- |
| `validate` | `gifted_curie:/polcert/src/AffineValidator.v:609` | Affine schedule/refinement validator. |
| `validate_tiling` | `gifted_curie:/polcert/src/AffineValidator.v:621` | Tiling-aware validator. |
| `validate_correct` | `gifted_curie:/polcert/src/AffineValidator.v:4624` | If `validate pp1 pp2 = true`, then executions of `pp2` refine back to `pp1`. |
| `validate_tiling_correct` | `gifted_curie:/polcert/src/AffineValidator.v:4665` | Same direction as `validate_correct`, but for the tiling-aware relation. |

### Prepare/codegen/cleanup

| Item | Location | Statement intent |
| --- | --- | --- |
| `prepare_codegen` | `gifted_curie:/polcert/src/PrepareCodegen.v:110` | Normalizes a well-formed polyhedral program into codegen-ready shape. |
| `prepare_codegen_semantics_correct` | `gifted_curie:/polcert/src/PrepareCodegen.v:1718` | Prepared poly semantics implies flattened semantics of the original poly program. |
| `prepared_codegen` | `gifted_curie:/polcert/src/PrepareCodegen.v:1900` | `prepare_codegen` + `CodeGen.codegen` + cleanup wrapper. |
| `prepared_codegen_correct` | `gifted_curie:/polcert/src/PrepareCodegen.v:1904` | Sequential prepared codegen is sound for affine programs. |
| `prepared_codegen_correct_general` | `gifted_curie:/polcert/src/PrepareCodegen.v:2029` | Witness-aware route: codegen on `current_view_pprog pol` refines back to `pol`. |
| `codegen` | `gifted_curie:/polcert/polygen/CodeGen.v:141` | Core sequential code generator. |
| `codegen_correct` | `gifted_curie:/polcert/polygen/CodeGen.v:226` | Generated loop semantics implies source `PolyLang` semantics under explicit shape assumptions. |
| `LoopCleanup.cleanup_correct` | `gifted_curie:/polcert/polygen/LoopCleanup.v:593` | General cleanup preserves sequential loop semantics. |
| `LoopSingletonCleanup.cleanup_correct` | `gifted_curie:/polcert/polygen/LoopSingletonCleanup.v:408` | Singleton-loop cleanup preserves sequential loop semantics. |

### End-to-end sequential theorems

| Item | Location | Statement intent |
| --- | --- | --- |
| `Opt_prepared_correct` | `gifted_curie:/polcert/driver/PolOptCorrect.v:104` | Default prepared pipeline backward refinement theorem. |
| `Opt_prepared_with_iss_correct` | `gifted_curie:/polcert/driver/PolOptCorrect.v:137` | ISS-enabled prepared pipeline theorem. |
| `Opt_correct` | `gifted_curie:/polcert/driver/PolOptCorrect.v:170` | User-facing default theorem: optimized loop execution implies original loop execution up to state equality. |
| `Opt_with_iss_correct` | `gifted_curie:/polcert/driver/PolOptCorrect.v:180` | User-facing ISS theorem in the same backward-refinement shape. |

### Parallel route

| Item | Location | Statement intent |
| --- | --- | --- |
| `checked_annotated_codegen` | `gifted_curie:/polcert/src/ParallelCodegen.v:430` | Generates parallel code and checks trace safety. |
| `annotated_codegen_correct_general` | `gifted_curie:/polcert/src/ParallelCodegen.v:518` | Trace-safe parallel code refines back to witness-aware `PolyLang`. |
| `checked_annotated_codegen_correct_general` | `gifted_curie:/polcert/src/ParallelCodegen.v:560` | Checked parallel codegen theorem; avoids exposing `trace_safe` as an external user obligation. |
| `Opt_parallel_current_correct` | `gifted_curie:/polcert/driver/ParallelPolOptCorrect.v:873` | User-facing theorem-aligned explicit-dimension parallel theorem. |
| `Opt_parallel_current_with_iss_correct` | `gifted_curie:/polcert/driver/ParallelPolOptCorrect.v:921` | ISS-enabled explicit-dimension parallel theorem. |

### Tiling and ISS bridge theorems

These files have many top-level theorems. The most important point is that they
are bridge theorems, not one-shot end-to-end guarantees.

| Item | Location | Statement intent |
| --- | --- | --- |
| `iss_complete_cut_shape_to_before_correct` | `gifted_curie:/polcert/src/ISSCutSemantics.v:1184` | Complete-cut ISS witness execution refines from `after` back to `before`. |
| `tiling_after_to_retiled_old_poly_correct` | `gifted_curie:/polcert/src/TilingRelation.v:6911` | `after` refines to an intermediate `retiled_old` representation under an explicit `Permutable_ext` side condition. |
| `tiling_after_to_before_poly_correct_via_retiled_old` | `gifted_curie:/polcert/src/TilingRelation.v:8274` | Composes `after -> retiled_old -> before` under both permutability and a bridge-layer hypothesis. |
| `tiling_after_to_before_instance_correct_via_retiled_old` | `gifted_curie:/polcert/src/TilingRelation.v:8317` | Whole-program version of the previous theorem. |

## Theorem intent notes

### The dominant theorem shape is backward refinement

For the user-facing optimizer theorems, the standard shape is:

- the optimizer returns a transformed artifact
- the transformed artifact has a terminating semantics derivation
- therefore the original artifact also has a terminating semantics derivation
- final states are related by `State.eq`

This is the shape of:

- `extractor_correct`
- `validate_correct`
- `prepared_codegen_correct`
- `Opt_correct`
- `Opt_parallel_current_correct`

This is intentional. These are not equivalence theorems and they are not
completeness theorems.

### The most important “bridge” lemmas

If you are reading proofs bottom-up, these are the lemmas that most often matter
for understanding why the big theorems compose:

- `instance_list_semantics_unstrengthen`
  - `gifted_curie:/polcert/src/StrengthenDomain.v:474`
- `instance_list_semantics_current_view_iff`
  - `gifted_curie:/polcert/src/PolyLang.v:3951`
- `prepare_codegen_semantics_correct`
  - `gifted_curie:/polcert/src/PrepareCodegen.v:1718`
- `checked_annotated_codegen_correct_general`
  - `gifted_curie:/polcert/src/ParallelCodegen.v:560`

### Theorems whose names are slightly broader than their statements

These are not wrong, but they are easier to overread than the actual theorem
statement warrants:

- `Extract_Schedule_Prepared_correct`
  - `gifted_curie:/polcert/driver/PolOpt.v:380`
  - still assumes `PolyLang.wf_pprog_affine pol'` for the scheduled result
- `tiling_after_to_retiled_old_poly_correct`
  - `gifted_curie:/polcert/src/TilingRelation.v:6911`
  - still assumes explicit `Permutable_ext` conditions
- `tiling_after_to_before_poly_correct_via_retiled_old`
  - `gifted_curie:/polcert/src/TilingRelation.v:8274`
  - still assumes both permutability and a bridge-layer theorem

## Suggested renaming plan

These are documentation-level recommendations first. If any rename is adopted,
prefer adding aliases and migrating proof call sites gradually.

| Current name | Proposed name | Priority | Reason |
| --- | --- | --- | --- |
| `Loop.wf` | `wf_placeholder` or a real `wf_loop` replacement | High | The current name suggests a real invariant, but the definition is `True`. |
| `Extract_Schedule_Prepared_correct` | `Prepared_from_scheduled_poly_correct` | Medium | The theorem is about a scheduled polyhedral artifact plus a wf assumption, not a closed scheduler theorem. |
| `prepared_codegen_correct_general` | `prepared_codegen_current_view_correct` | Medium | “general” is vague; the theorem is specifically about codegen on `current_view_pprog`. |
| `validate_correct` | `validate_refines_backward` | Low | Makes the direction `pp2 -> pp1` explicit. |
| `validate_tiling_correct` | `validate_tiling_refines_backward` | Low | Same reason as `validate_correct`. |
| `tiling_after_to_retiled_old_poly_correct` | `tiling_after_refines_retiled_old_under_permutability` | Medium | Makes the extra side condition visible in the theorem name. |
| `tiling_after_to_before_poly_correct_via_retiled_old` | `tiling_after_refines_before_via_retiled_old` | Medium | Shorter and clearer about theorem direction. |

## Review notes that should remain visible in docs

These are not renames, but they are easy to forget and should be kept close to
the semantic source map.

1. `Loop.Var n` evaluates with `nth n env 0`, so out-of-bounds variables are not
   rejected by core semantics:
   `gifted_curie:/polcert/polygen/Loop.v:72`.
2. `Loop.Div` and `Loop.Mod` do not encode nonzero-divisor well-formedness in
   the AST or semantic judgment:
   `gifted_curie:/polcert/polygen/Loop.v:59-60`,
   `gifted_curie:/polcert/polygen/Loop.v:70-71`.
3. Raw `Loop` syntax is richer than the verified affine extraction fragment; the
   actual affine gate is `wf_scop_stmt`:
   `gifted_curie:/polcert/src/Extractor.v:64-100`.

## Refresh recipe

When line numbers drift, the following commands are enough to rebuild this file:

```sh
docker exec gifted_curie sh -lc 'cd /polcert && grep -RIn "^Theorem " polygen src driver syntax samples'
docker exec gifted_curie sh -lc 'cd /polcert && grep -n "Inductive expr :=\|Inductive test :=\|Inductive stmt :=\|Inductive loop_semantics :" polygen/Loop.v'
docker exec gifted_curie sh -lc 'cd /polcert && grep -n "Record PolyInstr\|Definition wf_pinstr\|Inductive poly_semantics\|Inductive instance_list_semantics:" src/PolyLang.v'
docker exec gifted_curie sh -lc 'cd /polcert && grep -n "Definition extractor\|Theorem extractor_correct" src/Extractor.v'
docker exec gifted_curie sh -lc 'cd /polcert && grep -n "Definition prepare_codegen\|Theorem prepared_codegen_correct" src/PrepareCodegen.v'
docker exec gifted_curie sh -lc 'cd /polcert && grep -n "Definition validate\|Theorem validate_correct:" src/AffineValidator.v'
docker exec gifted_curie sh -lc 'cd /polcert && grep -n "Theorem Opt_correct\|Theorem Opt_parallel_current_correct" driver/PolOptCorrect.v driver/ParallelPolOptCorrect.v'
```

That should be treated as the minimum maintenance script for this document.
