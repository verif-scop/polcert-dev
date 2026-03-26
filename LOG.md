# PolCert Project Log

Date: 2026-03-08

## Environment
- Container: `gifted_curie`
- Code repo: `gifted_curie:/polcert`
- Active branch: `end-to-end`
- Host notes/context repo: `/home/hugh/research/polyhedral/polcert`
- Host repo remote: `git@github.com:verif-scop/polcert-dev.git`

## Repo handling note
- `polcert-dev` and `gifted_curie:/polcert` are separate git repositories and must be committed/pushed separately.
- `work/container-overlay/polcert` is an overlay/edit mirror used to sync files into the container repo; it is not the container repo itself.
- `polcert-dev` now keeps `work/` ignored and untracked; host-side overlay edits should not appear in this repo's normal status anymore.
- If host-side staging accidentally includes `work/container-overlay/polcert/**` while the intent is to commit container-side code, unstage it in `polcert-dev` and stage the real files inside `gifted_curie:/polcert` instead.

## Current proved state
- `src/Extractor.v`: `extractor_correct` is `Qed`
- `src/PrepareCodegen.v`: `prepare_codegen_semantics_correct` is `Qed`
- `driver/PolOpt.v`: final `Opt_correct` is `Qed`
- `driver/PolOptPrepared.v`: now just re-exports `PolOpt`
- `opam exec -- make -s check-admitted`: `Nothing admitted.`

## Clean-build fact
- The earlier clean-build failure was not a VPL issue.
- Root cause:
  - `make depend` had been run outside `opam exec`
  - `coqdep` was missing from PATH
- Current clean rebuild procedure that succeeds:
  - `make clean`
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`

## Current runtime status
- `opam exec -- make test`: green
- strict proved-path `polopt` suite: `62 / 62`
- `syntax/SPolOpt.v`: `opt = CoreOpt.Opt`, so the CLI now runs the same final `Opt` defined in `driver/PolOpt.v`
- Clean acceptance rerun completed successfully with:
  - `make clean`
  - `opam exec -- make depend`
  - `opam exec -- make proof`
  - `opam exec -- make -s check-admitted`
  - `opam exec -- make extraction`
  - `opam exec -- make polopt`
  - `opam exec -- make polcert.ini`
  - `opam exec -- make polcert`
  - strict generated-suite rerun: `62 / 62`

## `PolOpt.v` consolidation
- `driver/PolOpt.v` now contains the final verified optimizer definition.
- The old raw pipeline was renamed to `Opt_raw`.
- The final strengthened+prepared optimizer is now:
  - `Opt_prepared`
  - `Opt = Opt_prepared`
- `driver/PolOptPrepared.v` was reduced to a compatibility wrapper that re-exports `PolOpt`.

## Runtime fixes that survived

### 1. Extractor access normalization
- File: `src/Extractor.v`
- `normalize_access_list_rev` was wrong for extracted accesses.
- Fixed to `normalize_access_list`.
- Result:
  - `CInstr` tests recovered
  - `CSample2/covcol` recovered
  - `make test` returned to green

### 2. Source scattering exporter bug
- File: `src/PolyLang.v`
- `schedule_to_source_like_rows` used to drop a middle dynamic schedule row.
- This made source `before.scop` differ from the C-path scheduling problem.
- Fix is in place and survives the full suite.

### 3. Domain strengthening
- Statement domains are strengthened with parameter-only rows logically implied
  by iterator bounds.
- These are not treated as global program assumptions.
- This is needed so Pluto sees the intended guarded scheduling problem.

### 4. `mxv` / `mxv-seq3` schedule representation repair
- Root cause:
  - compaction was local per statement
  - zero rows were dropped without preserving the program-wide shared schedule
    skeleton
- Effective repair:
  - preserve source-like schedule structure for export
  - import optimized schedules with `from_openscop_schedule_only`
  - canonicalize schedules with a program-wide row mask
- Important:
  - this is a schedule representation fix
  - not a `Validator` fix
  - not a validation-only branch

### 5. `advect3d` status
- `advect3d` is not a semantic blocker.
- Temporary timing experiment showed:
  - `strengthen + scheduler + validate`: about `1.6s`
  - `CodeGen.codegen`: about `38.5s`
  - total `polopt`: about `40.7s`
- Conclusion:
  - parser/printer/validator/Pluto are not the issue
  - `CodeGen.codegen` dominates runtime on this corner case

## Oracle discipline
- C-path Pluto remains the optimization oracle.
- Do not use cross-source `polcert(our_before, c_before)` or
  `polcert(our_after, c_after)` as equality oracles.
- OpenScop names, IDs, and metadata differ by origin.
- Valid structural oracle:
  - compare raw Pluto `before.scop` / `after.scop`
  - compare `SCATTERING` family / schedule shape
  - require strict proved-path `polopt` to succeed on our route

## Current raw structural comparison
- Checked-in report:
  - `doc/pluto-raw-family-compare.md`
  - `doc/pluto-raw-family-compare.json`
- Scope warning:
  - the current report uses `polopt --extract-only`
  - it compares pure extractor output, not the strict proved-path source model
    after `StrengthenDomain`
- Current summary:
  - `62 / 62` source `before.scop` `SCATTERING` metadata match the C-path

## 2026-03-11 tiling proof boundary
- The recent `wf_pinstr` split was still the right refactor:
  - common `wf_pinstr` is now weaker
  - affine/codegen-specific obligations live in `wf_pinstr_affine`
- But that refactor did not eliminate the remaining generic tiling blocker.

### Concrete blocker
- The affine validator does not just require a stronger `wf` checker.
- In `src/Validator.v`, the access-collision core uses:
  - `exact_cell a (affine_product tf p)`
  - `make_poly_eq (matrix_product loc tf) ...`
- This means validator-side `pi_transformation` is not only an instruction-argument map.
- It is also used as the point-space map for access equality / dependence reasoning.

### Why this matters for tiling
- For source semantics, a natural tiled transformation is row-preserving:
  - from `env ++ tiles ++ point`
  - to the original source arguments `env ++ point`
- For validator-side access reasoning, the lifted accesses live on the tiled point space.
- So the validator-side transformation still needs to expose the tiled coordinates.
- A single `pi_transformation` field cannot play both roles generically.

### Current conclusion
- The remaining generic tiling proof issue is not just an over-strong `wf` side condition.
- It is a deeper modeling conflict:
  - source/instruction semantics want a source-argument transformation
  - affine validation wants an access/dependence-space transformation
- If we want the generic tiling proof to close cleanly, the likely minimal model repair is to split these roles explicitly instead of forcing both through one `pi_transformation`.

## Progress Update (2026-03-09, tiling proof bridge)
- Container-side Coq work in `gifted_curie:/polcert/src/TilingRelation.v` now proves:
  - single-link lower/upper row soundness after env insertion
  - witness-derived `link_domain` compilation
  - recursive/link-list soundness for the compiled `link_domain`
  - a lifted after-domain membership theorem under compiled-domain compatibility
- Current new bridge objects/theorems include:
  - `compile_link_domain_after_env_from`
  - `compile_link_domain_after_env`
  - `compile_link_domain_after_env_from_sound`
  - `compile_link_domain_after_env_sound`
  - `witness_matches_compiled_link_domain`
  - `tiling_rel_pinstr_structure_domain_lifted_compiled`
- Runtime status after this proof work remains green:
  - `opam exec -- make src/TilingRelation.vo`
  - `opam exec -- make polopt`
  - `./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop`
    still reports `PASS`
  - `62 / 62` raw Pluto `after.scop` `SCATTERING` metadata match the C-path
  - residual mismatch is concentrated in source `DOMAIN` metadata
- Sampled row-level `DOMAIN` comparisons (`covcol`, `tricky1`, `mxv`, `matmul`,
  `advect3d`, `costfunc`) show a stable pattern:
  - our exporter emits iterator bound rows only
  - the C-path adds one parameter-only row per iterator, expressing the
    non-emptiness consequence of the bound interval
  - examples:
    - `N-1 >= 0`
    - `N-2 >= 0`
    - `M-1 >= 0`
    - `K-1 >= 0`
    - `nz+2 >= 0`
- Current interpretation:
  - the remaining source-model fidelity gap is statement-domain strengthening
  - it is no longer a source `SCATTERING` problem
- `covcol` spot-check with `./polopt --debug-scheduler` confirms that the
  strict-path strengthened source OpenScop already reaches the C-path `DOMAIN`
  row counts, so `--extract-only` underreports current fidelity.

## Progress Update (2026-03-10, tiling after-based list bridge)
- Container-side Coq work in `gifted_curie:/polcert/src/TilingRelation.v` now also proves an after-based list bridge for the schedule gap.
- Newly compiled objects/theorems include:
  - `retiled_old_of_after_point`
  - `after_point_of_retiled_old`
  - `compose_tiling_instr_point_ext_from_after`
  - `retiled_old_ipl_from_after`
  - `compose_tiling_ipl_ext_from_after`
  - `retiled_old_pinstr_eqdom_after`
  - `flatten_instr_nth_after_implies_flatten_instr_nth_retiled_old`
  - `flatten_instr_nth_after_implies_flatten_instr_nth_tiling_ext`
- Practical meaning:
  - we can now start from the canonical after-side flattened instance list
  - build a flattened list for `retiled_old_pinstr`
  - and build a flattened ext list on the same after-domain
- This is the first container-compiled route that avoids relying on direct monotonicity from before-side lexicographic index order to tiled index order.
- That matters especially for skewed / diamond tiling, where a direct `before -> tiled` map is the wrong proof shape.
- Runtime/build regression remains green after this proof work:
  - `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make src/TilingRelation.vo'`
  - `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make polopt'`
  - `docker exec gifted_curie sh -lc 'cd /polcert && ./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop'`
    still reports `overall: PASS`

## Progress Update (2026-03-10, tiling whole-program flattened assembly)
- `gifted_curie:/polcert/src/TilingRelation.v` now also compiles a whole-program existential assembly theorem:
  - `flatten_instrs_after_implies_tiling_ext_exists`
- Supporting program-level list plumbing now compiled:
  - `retiled_old_pinstrs`
  - `compose_tiling_pinstrs_ext_from_after`
  - `retiled_old_pinstrs_preserve_length`
  - `compose_tiling_pinstrs_ext_from_after_preserve_length`
  - `retiled_old_pinstrs_app_singleton`
  - `compose_tiling_pinstrs_ext_from_after_app_singleton`
  - `nth_error_retiled_old_pinstrs`
  - `nth_error_compose_tiling_pinstrs_ext_from_after`
- Meaning:
  - from a whole-program after-side flattened list, the proof can now assemble
    - a whole-program flattened list for `retiled_old_pinstrs`
    - a whole-program flattened ext list
  - and it keeps the list projections aligned:
    - `old_of_ext_list ipl_ext = ipl_old`
    - `new_of_ext_list ipl_ext = ipl_after`
- This closes the list-bookkeeping part of the schedule-aware route.
- The remaining proof gap is no longer flattened-list assembly.
- It is now the final semantics-level use of this assembled ext witness.

## Progress Update (2026-03-10, tiling top-down semantics bridge)
- `gifted_curie:/polcert/src/TilingRelation.v` now also compiles a first top-down whole-program theorem:
  - `tiling_after_to_retiled_old_poly_correct`
- Shape of the theorem:
  - assumes a whole-program ext-level permutability condition on the assembled
    tiling ext list
  - starts from `PolyLang.poly_instance_list_semantics` for `after`
  - concludes `PolyLang.poly_instance_list_semantics` for `retiled_old_pinstrs`
  - preserves final state up to `Instr.State.eq`
- Practical meaning:
  - the decomposition
    - `before <-> retiled_old <-> after`
    is no longer just a design claim
  - one full layer, `after -> retiled_old`, now exists as a compiled Coq theorem
  - the proof route is explicitly:
    - assemble whole-program `ipl_old` / `ipl_ext` from the after-side list
    - move to an old-schedule-stable ext list via `SelectionSort`
    - invoke `PolyLang.stable_permut_ext_lists_are_equivalent`
- Important boundary:
  - this theorem still assumes the relevant tiled-schedule legality/permutability
    fact
  - it does not yet derive that fact from an executable checker
  - it also does not yet compose with the opposite `retiled_old -> before`
    layer into a final end-to-end tiling correctness theorem
- Container regression remains green after this proof step:
  - `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make src/TilingRelation.vo'`
  - `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make polopt'`
  - `docker exec gifted_curie sh -lc 'cd /polcert && ./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop'`
    still reports `overall: PASS`

## Progress Update (2026-03-10, tiling top-level composition theorem)
- `gifted_curie:/polcert/src/TilingRelation.v` now also compiles the next wrapper layer:
  - `tiling_retiled_old_to_before_poly_layer`
  - `tiling_after_to_before_poly_correct_via_retiled_old`
  - `tiling_after_to_before_instance_correct_via_retiled_old`
- Meaning:
  - the top-level theorem shape for tiling is no longer implicit
  - we now have an actual compiled composition theorem from `after` to `before`
  - but it is still parameterized by the missing left layer
    `retiled_old -> before`
- This is useful because it narrows the remaining proof debt:
  - no more uncertainty about how the top theorem should compose
  - the remaining nontrivial theorem is now exactly the concrete realization of
    `tiling_retiled_old_to_before_poly_layer`
- Container regression remains green after adding this wrapper layer:
  - `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make src/TilingRelation.vo'`
  - `docker exec gifted_curie sh -lc 'cd /polcert && opam exec -- make polopt'`
  - `docker exec gifted_curie sh -lc 'cd /polcert && ./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop'`
    still reports `overall: PASS`

## Current conclusion
- The generated-suite semantic blockers are closed.
- The strict proved path is currently:
  - proof-complete
  - clean-buildable
  - `62 / 62` on the regression suite
- Remaining work, if any, is now about:
  - strengthening the source-model fidelity argument
  - or broadening the benchmark set

## Precise strengthening repair
- The final strengthening change that survived is not the earlier broad
  parameter-only guard collection.
- Current `StrengthenDomain` now derives extra rows only by:
  - canceling the current innermost iterator between two constraints
  - keeping the resulting guard only if it depends on outer iterators +
    parameters
- This precise strengthening was recompiled, re-extracted, and revalidated
  through a clean rebuild.

## Follow-up TODOs
- Add GitHub CI to the source repo:
  - run the README/opam build flow
  - run `check-admitted`
  - run `make test`
  - run the strict `polopt` generated-suite regression
- Evaluate moving the current OCaml-only post-codegen simplification into a verified Coq cleanup pass:
  - expr/test simplification
  - guard/seq cleanup
  - singleton-loop elimination via verified substitution

## Cleanup pass integration
- `polygen/LoopCleanup.v` is now implemented and compiled.
- `src/PrepareCodegen.v` now wraps codegen with:
  - `Cleanup.cleanup`
- Current clean build + strict rerun confirms the cleanup pass is in the proved
  path:
  - `Nothing admitted`
  - README clean build succeeds
  - strict suite remains `62 / 62`
- Implemented cleanup layers:
  - expression/test simplification
  - structural cleanup for `Seq` / trivial `Guard`
  - singleton-loop elimination by substitution
- The singleton layer was added in:
  - `polygen/LoopSingletonCleanup.v`
- `src/PrepareCodegen.v` now instantiates cleanup from `LoopSingletonCleanup`
  rather than the earlier two-layer module.
- `syntax/SLoopPretty.ml` has now been reduced to display-layer duties:
  - formatting / indentation
  - fresh loop-variable naming
  - raw loop / instr / test rendering
  - no OCaml-side semantic cleanup remains

## Strengthened-before / raw-after comparison
- Full-suite strict-path comparison was run using strengthened source `before.scop` extracted from `polopt --debug-scheduler`, then raw `pluto --readscop`.
- Results:
  - strengthened `before.scop` scattering metadata match: `62 / 62`
  - strengthened `before.scop` domain metadata match: `52 / 62`
  - raw Pluto `after.scop` scattering metadata match: `62 / 62`
- Residual domain-only mismatches are limited to:
  - `fusion10`, `fusion2`, `fusion3`, `fusion4`, `fusion8`, `lu`, `nodep`, `ssymm`, `strsm`, `trisolv`
- For those `10`, raw Pluto `after.scop` still lands in the same scattering family as the C-path raw `after.scop`.
- Therefore the current residual source-model fidelity gap is domain-shape only; on the regression suite it is no longer changing the observed optimization family.

## Residual domain mismatch classes
- Residual `DOMAIN` metadata mismatches now split into:
  - tautological / clearly redundant extras on our side:
    - `fusion10`, `fusion2`, `fusion3`, `fusion4`, `fusion8`, `nodep`
  - still-nontrivial strengthening mismatches:
    - `lu`, `ssymm`, `strsm`, `trisolv`
- Even for the second class, the raw Pluto `after.scop` scattering family currently still matches the C-path on the regression suite.

- The residual nontrivial domain mismatches are now better understood:
  - `lu`, `ssymm`, `trisolv` are mainly inner-range non-emptiness strengthening differences
  - `strsm` is mainly a guard/singleton normalization difference (`k == i+1` represented as equality in the C-path)
- This refines the remaining debt: it is a domain-normalization mismatch, not a schedule mismatch.

## Next strengthening direction
- Current `StrengthenDomain` only emits parameter-only guards.
- The remaining nontrivial source-domain mismatches suggest the next principled extension:
  - eliminate the innermost iterator from a lower/upper bound pair
  - keep guards that depend on outer iterators + parameters
  - normalize singleton domains / guard equalities as equality rows when appropriate
- Representative targets:
  - `lu`: derive `N-k-2 >= 0`
  - `ssymm`: derive `j-2 >= 0`
  - `trisolv`: derive `j-1 >= 0`
  - `strsm`: normalize `k == i+1` as equality

- 2026-03-08: Ported affine simplification from `SLoopPretty.ml` into Coq `LoopCleanup` and rebuilt `polopt`. The proved cleanup now normalizes additive affine forms and simple affine guards; representative output (`intratileopt1`) again prints `if (1 <= N)` and `range(0, M)` from the Coq pass, not from OCaml pretty simplification. Strict suite rerun remains `62/62`, `changed=52`, `unchanged=10`.

- 2026-03-08: refreshed /polcert README, syntax README, and polopt suite README to describe the consolidated verified PolOpt pipeline, proof boundary, and current 62/62 strict-suite status.

- 2026-03-08: split /polcert user docs into README, POLCERT.md, and POLOPT.md; emphasized polopt pipeline, proof boundary, benchmark status, and CI workflow.

- 2026-03-09: added an experimental OCaml tiling validator entry to `gifted_curie:/polcert/syntax/SLoopMain.ml`:
  - `./polopt --extract-tiling-witness-openscop before.scop after.scop`
  - `./polopt --validate-tiling-openscop before.scop after.scop`
  - implemented in `gifted_curie:/polcert/syntax/PlutoTilingValidator.ml`
  - current structure is explicit:
    - witness extraction
    - witness checking
    - `validate = extract + check`
  - validated real Pluto tiled OpenScop for:
    - basic tiling (`matmul`)
    - second-level tiling (`matmul --second-level-tile`)
    - skewed tiling (`jacobi-1d-imper`)
    - diamond tiling (`jacobi-1d-imper --diamond-tile`)
- 2026-03-09: patched `gifted_curie:/polcert/lib/OpenScopParser.mly` to consume Pluto `<loop> ... </loop>` extensions as ignored global extensions so diamond/parallel Pluto outputs can be read by `OpenScopReader`.
- 2026-03-09: added a first Coq tiling witness sandbox file `gifted_curie:/polcert/src/TilingWitness.v` and compiled it with:
  - `eval $(opam env --switch=polcert --set-switch) && coqc $(cat _CoqProject) src/TilingWitness.v`
  - current contents only cover:
    - affine expression evaluation
    - tile-parent computation by division
    - interval soundness for one tile link
    - list-length / suffix properties for lifted points
- 2026-03-09: extended `gifted_curie:/polcert/src/TilingWitness.v` and recompiled it.
  - current Coq coverage now also includes:
    - statement-level witness packaging
    - lower/upper tile-link row semantics
    - a trace-level theorem that ordered link evaluation satisfies the witness-generated Pluto-style tile-link rows
  - this is the first Coq layer that directly matches the OCaml checker's `link_rows_ok` obligation
- 2026-03-09: extended `gifted_curie:/polcert/src/TilingWitness.v` again and recompiled it.
  - current Coq coverage now also includes:
    - lifting a before-domain row by zero-prefixing tile variables
    - a statement-level theorem that any before-domain row satisfied by the source point remains satisfied by the lifted base row on the tiled point
  - this is the first Coq layer that directly matches the OCaml checker's `base_domain_ok` preservation story
- 2026-03-09: extended `gifted_curie:/polcert/src/TilingWitness.v` further and recompiled it.
  - current Coq coverage now also includes:
    - lifting access rows by zero-prefixing added tile inputs
    - a statement-level theorem that preserved access rows remain valid on the tiled point
    - a packaged `statement_tiling_core_sound` theorem combining:
      - tile-link row soundness
      - lifted base-row preservation
      - lifted access-row preservation
  - this is the first clear Coq boundary where tiling lifting correctness is mostly separate from schedule legality
- 2026-03-09: corrected the proof-boundary story for tiling.
  - OpenScop should be treated as Pluto witness/import carrier
  - the real proof target should be a `PolyLang.PolyInstr` / `PolyLang.t` tiling relation
  - future bridge work should therefore connect `statement_tiling_core_sound` to PolyLang, not directly to OpenScop matrices
- 2026-03-09: extended `gifted_curie:/polcert/src/TilingWitness.v` again and recompiled it.
  - generalized lifting from naive prefix-zero form toward the real PolyLang embedding shape
  - added inserted-after-env variants for base/access lifting
- 2026-03-09: added and compiled `gifted_curie:/polcert/src/TilingRelation.v`.
  - this file introduces:
    - `tiling_rel_pinstr_structure`
    - `tiling_rel_pprog_structure`
  - these are structural PolyLang-side tiling relations for the new independent tiling pass
  - they intentionally leave schedule legality out of scope for now
- 2026-03-09: added a host-side standalone OCaml tiling checker in [tools/tiling_ocaml/README.md](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/README.md).
  - local build path:
    - `cd tools/tiling_ocaml && dune build pluto_tiling_ocaml.exe`
  - executable interface:
    - `extract`
    - `check`
    - `validate`
  - minimal smoke fixture now lives in:
    - [basic_before.scop](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/basic_before.scop)
    - [basic_after.scop](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/basic_after.scop)
  - local execution status:
    - `extract` PASS
    - `validate` PASS
    - `validate --check-bounded-coverage` PASS
    - tampered witness (`tile_size 32 -> 31`) FAIL
    - Python `extract` -> OCaml `check` PASS
    - OCaml `extract` -> Python `check` PASS
    - second-level synthetic fixture PASS
    - second-level Python/OCaml mutual check PASS
    - [smoke.sh](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/smoke.sh) PASS
  - this further stabilizes the proof boundary:
    - untrusted witness extraction
    - verified witness checking
  - current checker output now also exposes two more proof-facing bits:
    - `shape`
    - `transformation_contract`
  - the important semantic correction is:
    - tile links are now canonicalized by dependency order
    - not by plain lexicographic sorting
  - current executable checker core is now also named in phase form:
    - `check_pinstr_shape`
    - `check_pinstr_links`
    - `check_pinstr_accesses`
    - `check_pinstr_schedule_sanity`
    - `check_pinstr_transformation_contract`
    - `check_pinstr_tiling`
  - second-level bad witness fixture now also exists and is rejected:
    - [second_level_bad_witness.json](/home/hugh/research/polyhedral/polcert/tools/tiling_ocaml/fixtures/second_level_bad_witness.json)
  - host-side OCaml `--json` output now emits a full structured validation report instead of only `ok + rendered`
  - host-side OCaml `--json` failure path now also emits structured `{ ok=false, error=... }`
- 2026-03-09: the reverse/completeness side of the compiled tiling relation advanced materially in `gifted_curie:/polcert/src/TilingRelation.v`.
  - the link-domain reverse theorems now compile:
    - `compile_link_domain_after_env_from_complete`
    - `compile_link_domain_after_env_complete`
  - the compiled relation now also has reverse/domain packaging:
    - `tiling_rel_pinstr_structure_compiled_domain_complete`
    - `tiling_rel_pinstr_structure_compiled_index_complete`
    - `tiling_rel_pinstr_structure_compiled_domain_iff`
  - practical meaning:
    - statement-level compiled-domain characterization is no longer only forward
    - after-domain membership now recovers the canonical tile-link trace and before-domain membership
  - the proof also now reaches the first program-facing selection layer:
    - `tiling_rel_pinstr_list_compiled_nth`
    - `tiling_rel_pprog_structure_compiled_nth`
    - `tiling_rel_pprog_structure_compiled_domain_iff_nth`
    - `tiling_rel_pprog_structure_compiled_transformation_lifted_nth`
    - `tiling_rel_pprog_structure_compiled_waccess_lifted_nth`
    - `tiling_rel_pprog_structure_compiled_raccess_lifted_nth`
    - `tiling_rel_pprog_structure_compiled_instr_semantics_lifted_iff_nth`
    - `tiling_rel_pprog_structure_compiled_effects_nth`
    - `compose_tiling_pinstr_ext`
    - `compose_tiling_instr_point_ext`
    - `tiling_rel_pinstr_structure_compiled_old_schedule_lifted`
    - `tiling_rel_pprog_structure_compiled_old_schedule_lifted_nth`
    - `tiling_rel_pprog_structure_compiled_belongs_to_ext_nth`
  - container regression stayed green:
    - `opam exec -- make src/TilingRelation.vo`
    - `opam exec -- make polopt`
    - `./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop`
- 2026-03-10: the left-layer assembly moved from statement-local theorems to a compiled whole-program flatten bridge.
  - newly compiled helpers in `src/TilingRelation.v`:
    - `Forall_nth_error`
    - `Forall2_nth_error`
    - `tiling_rel_pinstr_list_lengths`
    - `tiling_rel_pprog_structure_compiled_lengths`
    - `tiling_rel_pinstr_list_app_singleton_inv`
    - `tiling_rel_pprog_structure_compiled_app_singleton_inv`
    - `Forall2_app_singleton_inv`
    - `flatten_instr_nth_retiled_old_implies_before_flatten_instr_nth_exists_perm`
    - `flatten_instrs_retiled_old_implies_before_exists_perm`
    - `instr_point_list_semantics_map_preserved`
    - `HdRel_sched_map_time_stamp_preserved`
    - `sorted_sched_map_time_stamp_preserved`
  - practical meaning:
    - the proof now has a compiled whole-program theorem turning a flattened `retiled_old` program into a flattened `before` program plus a permutation witness to the program-wide `before_of_retiled_old` map
    - this removes the last major gap in the flatten/list assembly layer of `retiled_old -> before`
    - the remaining debt is now above this layer:
      - global pointwise semantics/time-stamp preservation for the program-wide `before_of_retiled_old_pprog_point`
      - then the concrete `tiling_retiled_old_to_before_poly_layer` theorem
  - container regression stayed green:
    - `opam exec -- make src/TilingRelation.vo`
    - `opam exec -- make polopt`
    - `./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop`
- 2026-03-10: tiling now has concrete end-to-end theorems and a Coq bool checker layer.
  - newly compiled in `src/TilingRelation.v`:
    - `tiling_retiled_old_to_before_poly_correct_with_env_len`
    - `tiling_retiled_old_to_before_instance_correct`
    - `tiling_after_to_before_instance_correct_concrete`
    - `tiling_after_to_before_poly_correct_concrete`
  - newly compiled in `src/TilingBoolChecker.v`:
    - `check_statement_tiling_witnessb_sound`
    - `check_pinstr_tiling_compiledb_sound`
    - `check_pinstr_list_tiling_compiledb_sound`
    - `check_pprog_tiling_compiledb_sound`
  - newly compiled in concrete driver instantiations:
    - `driver/TPolOpt.v`
      - `tiling_validate_correct`
      - `tiling_checked_validate_correct`
    - `driver/CPolOpt.v`
      - `tiling_validate_correct`
      - `tiling_checked_validate_correct`
  - practical meaning:
    - there is now a concrete `after -> before` theorem path, not just the older abstract `via_retiled_old` wrapper
    - there is now also a checker-facing theorem shape:
      - `check_pprog_tiling_compiledb before after ws = true`
      - `mayReturn (validate (retiled_old before after ws) after) true`
      - `after` semantics
      - implies `before` semantics up to final-state equality
  - container regression stayed green:
    - `opam exec -- make src/TilingRelation.vo`
    - `opam exec -- make src/TilingBoolChecker.vo`
    - `opam exec -- make driver/TPolOpt.vo`
    - `opam exec -- make driver/CPolOpt.vo`
    - `opam exec -- make polopt`
    - `./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop`
      still reports `overall: PASS`
- 2026-03-10: tiling now has an actual syntax-side checked pass theorem and modular extraction hook.
  - newly compiled in `syntax/STilingOpt.v`:
    - `tiling_validate_correct`
    - `tiling_checked_validate_correct`
    - `checked_tiling_validate_correct`
  - `syntax/STilingOpt.v` packages the actual `SPolIRs` side into one executable Coq function:
    - `checked_tiling_validate before after ws`
    - which runs the Coq bool checker first
    - then runs `Validator.validate` on `retiled_old before after ws` versus `after`
  - the practical meaning is that the syntax/frontend side now has the same checked theorem shape as the earlier `TPolOpt`/`CPolOpt` instances, but no longer only as a pair of assumptions:
    - `mayReturn (checked_tiling_validate before after ws) true`
    - `after` semantics
    - implies `before` semantics
  - `driver/TPolOpt.v` and `driver/CPolOpt.v` were also strengthened with matching:
    - `checked_tiling_validate`
    - `checked_tiling_validate_correct`
  - modular extraction was tested with `tiling_separate_extraction.v`:
    - it successfully generated `extraction/STilingOpt.ml`
    - plus fresh `extraction/TilingBoolChecker.ml` and `extraction/TilingRelation.ml`
  - runtime/build note:
    - a full `make polopt` rebuild in the container is currently blocked by a pre-existing extraction compatibility issue in `extraction/BinInt.ml` / `extraction/Zbits.ml` (`Z.iter` and related API surface), not by the new tiling theorems themselves
    - the already-built `./polopt --validate-tiling-openscop ...` path still runs and still reports `overall: PASS`
- 2026-03-10: extraction-side investigation was narrowed to `extraction.v` directives, not generated files.
  - confirmed from the project's own [extraction script] that the current pipeline:
    - directly extracts `Coq.ZArith.BinInt.Z`
    - does not provide extraction directives for `Z.pred`, `Z.iter`, `Z.odd`, `Z.div2`, `Z.log2`, `Z.log2_up`
  - a minimal container experiment showed that fixing this at the extraction-directive layer is viable:
    - `Extract Constant Z.pred => "fun x -> add x (Zneg XH)"`
    - `Extract Constant Z.iter => "fun n f x -> match n with | Zpos p -> Coq_Pos.iter f x p | _ -> x"`
    - `Extract Constant Z.odd => "function | Z0 -> False | Zpos (XO _) -> False | Zneg (XO _) -> False | _ -> True"`
    - `Extract Constant Z.div2 => "function | Z0 -> Z0 | Zpos XH -> Z0 | Zpos p -> Zpos (Coq_Pos.div2 p) | Zneg p -> Zneg (Coq_Pos.div2_up p)"`
    - `Extract Constant Z.log2 => "function | Zpos (XI p) -> Zpos (Coq_Pos.size p) | Zpos (XO p) -> Zpos (Coq_Pos.size p) | _ -> Z0"`
    - `Extract Constant Z.log2_up => "fun a -> match compare (Zpos XH) a with | Lt -> succ (log2 (pred a)) | _ -> Z0"`
  - importantly, these strings were chosen to compile inside the extracted `BinInt.Z` module itself; a first attempt using OCaml's external `Z.*` names was rejected because it produced self-unbound references
  - I patched only extraction scripts:
    - `extraction/extraction.v`
    - `extraction/tiling_extraction.v`
    - `tiling_separate_extraction.v`
  - both tiling extraction scripts still compile after the directive changes
  - caveat:
    - the legacy main `extraction/extraction.v` script is awkward to rerun in isolation because it contains `Cd "extraction".`
    - so the directive fix itself is validated, but re-running the full legacy extraction script cleanly will likely need either:
      - invoking it through the existing full extraction build path, or
      - a small cleanup of the script's `Cd` behavior
- 2026-03-10: extraction compatibility fix is now applied at the correct layer and the main build is green again.
  - only extraction scripts were changed:
    - `extraction/extraction.v`
    - `extraction/tiling_extraction.v`
    - `tiling_separate_extraction.v`
  - the fix was to provide explicit extraction directives for:
    - `Z.pred`
    - `Z.iter`
    - `Z.odd`
    - `Z.div2`
    - `Z.log2`
    - `Z.log2_up`
  - the final directives use the actual names produced by this project's extraction pipeline:
    - positive constructors: `Coq_xH`, `Coq_xO`, `Coq_xI`
    - positive helper module: `Pos`
    - booleans: `true` / `false`
  - validation path:
    - `opam exec -- make extraction`
    - `opam exec -- make polopt`
    - `./polopt --validate-tiling-openscop /tmp/tv_matmul.beforescheduling.scop /tmp/tv_matmul.afterscheduling.scop`
  - result:
    - the previous extraction breakage in `BinInt` / `Zbits` / `IEEE754_extra` is gone
    - `polopt` rebuilds successfully again
    - tiling runtime validation still reports `overall: PASS`
- 2026-03-10: verified tiling validation is now actually consumed by the runtime `polcert` / `polopt` paths.
  - the decisive checker-side change was to replace the old row-preserving transformation lift with a padded transformation lift:
    - column-lift the old transformation
    - then insert identity rows for the added tile dimensions after the environment rows
  - the current Coq files changed at the definition/checker boundary are:
    - `src/TilingRelation.v`
    - `src/TilingBoolChecker.v`
  - several transformation-lifted theorems are temporarily `Admitted` while the new relation is stabilized:
    - `tiling_rel_pinstr_structure_transformation_sound`
    - `tiling_rel_pinstr_structure_transformation_lifted`
    - `tiling_rel_pinstr_structure_instr_semantics_lifted_iff`
    - `tiling_rel_pinstr_structure_compiled_transformation_lifted`
    - `tiling_rel_pinstr_structure_compiled_instr_semantics_lifted_iff`
    - `tiling_rel_pprog_structure_compiled_transformation_lifted_nth`
  - runtime `polcert` now uses the verified tiling checker by:
    - inferring a witness
    - building a canonical tiled skeleton from `before + witness`
    - importing only the raw tiled schedule from `after.scop`
    - padding `vars` on both sides so the current validator well-formedness checks accept the tiled program
  - container validation results:
    - `./polcert --kind tiling /tmp/matmul.mid.scop /tmp/matmul.after.scop` -> `TILING-OK`
    - `./polcert --kind tiling /tmp/jac1.mid.scop /tmp/jac1.after.scop` -> `TILING-OK`
    - `./polcert --kind tiling /tmp/matadd_mid.scop matadd_mid.scop.afterscheduling.scop` -> `TILING-OK`
    - `./polcert /tmp/matadd_before.scop /tmp/matadd_mid.scop matadd_mid.scop.afterscheduling.scop` -> phase-aligned `OK`
  - `polopt` now also consumes the verified tiling gate in its two-phase Pluto path:
    - affine-only Pluto
    - tile-only Pluto
    - affine validate(before, mid)
    - verified tiling validate(mid, after)
  - current remaining runtime issue is no longer validation:
    - `polopt` no longer falls back on the tiling gate
    - but syntax/codegen consumption of the validated tiled model is still not fully aligned
- 2026-03-11: syntax/codegen-side tiled model consumption is now aligned enough to emit correct tiled loop bodies on the current syntax examples.
  - the crucial runtime finding is that validator-side and codegen-side `pi_transformation` are not the same object:
    - validator-side checked tiling uses the padded transformation relation
    - syntax/codegen must instead keep a source-argument transformation, lifted onto tiled point space
  - concrete symptom:
    - `matadd.loop` initially validated but code-generated `C[i0][0] = A[i0][0] + B[i0][0]`
    - after padding `vars`, loop structure became correct but the body still used tile iterators (`i0`, `i1`) instead of point iterators (`i2`, `i3`)
  - concrete cause:
    - `PrepareCodegen.prepare_codegen` chooses `cols = length vars`
    - tiled syntax programs had `env_dim + depth = 6` but only `vars = 5`
    - this truncated the last tiled column during `resize_affine_list`
  - runtime repair:
    - syntax-side `vars` are now padded before codegen to satisfy the required column bound
    - syntax-side `pi_transformation` is now rebuilt from the pre-tiling source transformation by a row-preserving after-env lift
    - concretely, codegen keeps the original source argument shape `env ++ point` while reading values from the tiled point-space `env ++ tiles ++ point`
    - raw imported tiled `pi_transformation` is no longer used for codegen
  - validated runtime results:
    - `./polopt syntax/examples/matadd.loop` now emits
      - outer tile loops `i0`, `i1`
      - point loops `i2`, `i3`
      - body `C[i2][i3] = (A[i2][i3] + B[i2][i3])`
    - `./polopt syntax/examples/covariance.loop` emits a tiled body using `data[i3][i4]` / `data[i3][i5]`
    - `./polopt syntax/examples/covariance_outer.loop` emits a tiled body using `data[i5][i3]` / `data[i5][i4]`
  - remaining runtime caveat:
    - `polopt` still prints `isl_map.c:12117: number of columns too small`
    - this warning no longer blocks validation or code generation, but it is still worth a later cleanup pass
- 2026-03-11: confirmed a generic-layer blocker in the tiling proof architecture. The current
  `INSTR` interface only exposes `instr_semantics_stable_under_state_eq`; it does not provide any
  generic extensionality principle relating `instr_semantics i p ...` and
  `instr_semantics i p' ...` when `p` and `p'` differ by extra coordinates. At the same time,
  `PolyLang.poly_semantics` feeds `affine_product pi_transformation p` directly into
  `Instr.instr_semantics`. This means any generic tiling theorem that changes the shape of
  `pi_transformation` rows but still wants to conclude source-level semantic equivalence is blocked
  unless we either:
  (1) strengthen the generic instruction interface with a suitable argument-extensionality property,
  or
  (2) weaken/split the theorem boundary so the generic layer only proves checker/schedule facts and
      leaves source-semantics bridging to a more specialized layer.
  This is no longer a missing-lemma issue; it is an abstraction-boundary issue.
- 2026-03-11: audited the current `wf_pinstr` / `Validator` dependency surface to see whether the
  transformation-length equality can be moved out of the common well-formedness layer.
  - the concrete strong clause is `length pi_transformation = env_dim + pi_depth`, currently baked
    into:
    - `PolyLang.wf_pinstr`
    - `PolyLang.wf_pinstr_ext`
    - `Validator.check_wf_polyinstr`
  - the current affine validator proofs mostly consume the transformation **column** fact
    `exact_listzzs_cols cols pi_transformation`, not the transformation **row-count** equality
  - the most visible current consumers of the row-count equality are:
    - `PrepareCodegen` / `codegen_ready_pi`
    - `StrengthenDomain` (only because it currently preserves the full old `wf_pinstr`)
    - the executable checker path in `Validator.check_wf_polyinstr`
  - working hypothesis:
    - the row-count equality belongs in an affine/codegen-specific strengthening, not in the common
      `wf_pinstr`
    - a more principled split is:
      - common `wf_pinstr`: column alignment / bounds / domain/schedule/access exactness
      - `wf_pinstr_affine`: common `wf_pinstr` plus transformation row-count equality
      - `wf_pinstr_tiling`: likely just the common `wf_pinstr`, with tiling-specific structure
        expressed in the tiling relation rather than in `wf`
  - this still leaves one independent issue:
    - even after weakening the common `wf`, the generic tiling proof still needs either a source
      view / affine view bridge or a stronger generic instruction interface
2026-03-11

- Reached a generic-model blocker in tiling closure: current `INSTR.valid_access_function`
  still forces instruction semantics arguments and access-checking arguments to be the same
  vector. This is affine-friendly but tiling-hostile.
- Designed a witness-centered replacement direction in
  [doc/pluto-comprehensive/tiling-witness-centered-redesign.md](doc/pluto-comprehensive/tiling-witness-centered-redesign.md):
  keep one semantic transformation, add an explicit point-space witness, and
  define source/access views through projection from current point-space to
  base/source point-space.
- Added a Coq sketch file
  [work/container-overlay/polcert/src/PointWitness.v](work/container-overlay/polcert/src/PointWitness.v)
  to pin down the intended witness relation independently of the current
  implementation.
- Refined the redesign into a concrete target interface:
  - one `pi_transformation`
  - one `pi_point_witness`
  - `pi_poly` / `pi_schedule` stay on current point-space
  - instruction semantics and access interpretation are both defined through
    witness projection to base/source point-space
- Wrote the more concrete design in
  [doc/pluto-comprehensive/tiling-witness-centered-redesign.md](doc/pluto-comprehensive/tiling-witness-centered-redesign.md)
  and a matching Coq record sketch in
  [work/container-overlay/polcert/src/WitnessedPolyLangDesign.v](work/container-overlay/polcert/src/WitnessedPolyLangDesign.v).
- Current assessment:
  - the high-level proof decomposition (`before -> mid -> after`) survives
  - the main change is not the proof idea but the generic interface boundary
  - the existing dual-transformation split should be treated as transitional,
    not the final model
- Refined the blocker diagnosis again:
  - the previous conclusion "generic closure requires changing `INSTR`" was too
    strong
  - a better witness-centered design makes both source semantics and access
    validity use the same projected source-argument vector
  - this means `INSTR.valid_access_function` can likely stay unchanged
  - the actual required redesign target is `PolyLang`'s current-to-source
    projection, not the instruction interface itself
- 2026-03-11: started the real witness-centered migration in the overlay, not
  just in sketches.
  - `PointWitness.v`
    - generalized `projected_base_point_of_current_eval_tiled` to arbitrary
      `params`
    - added `related_by_point_witness_src_args`
    - moved witness equality infrastructure here:
      - `list_Z_eqb`
      - `affine_expr_eqb`
      - `tile_link_eqb`
      - `tile_link_list_eqb`
      - `statement_tiling_witness_eqb`
      - `point_space_witness_eqb`
  - `PolyLang.v`
    - added real current-space helpers:
      - `current_env_dim_of`
      - `current_base_point_of`
      - `current_src_args_of`
    - switched `poly_semantics`, `poly_semantics_k`, and `poly_lex_semantics`
      to feed `Instr.instr_semantics` with `current_src_args_of`
    - kept the stronger affine checker layer intact for now
  - `Validator.v`
    - fixed an inconsistency introduced by the new witness field:
      `check_wf_polyinstr` now checks
      `witness_current_point_dim pi_point_witness = pi_depth`
    - the corresponding proof now discharges the new `wf_pinstr` conjunct
  - `TilingRelation.v`
    - rewrote the source-side tiling relation to be witness-centered:
      - source view now keeps the before-side transformation/access functions
      - the after/source object carries `PSWTiling ...`
      - source-side instruction-semantics bridge now talks about
        `PL.current_src_args_of after ...`
    - added `current_src_transformation_of_pinstr` and started routing tiling
      ext views through it
  - `TilingBoolChecker.v`
    - added a source-side checker family:
      - `check_pinstr_tiling_sourceb`
      - `check_pinstr_list_tiling_sourceb`
      - `check_pprog_tiling_sourceb`
    - and corresponding soundness lemmas against the new source-side tiling
      relation
  - status:
    - the codebase now contains both the old compiled/padded tiling relation
      and the new witness-centered source relation
    - next step is to finish migrating the verified checked path from the old
      compiled relation to the new source relation, then collapse the
      transitional dual-transformation machinery

- 2026-03-11 23:xx
  - validated a deeper blocker in the remaining `Validator.v` admits:
    the old `compose_pinstr_ext` shape is stale after witness-centered
    `current_src_args_of`
    - `flatten_instr_nth` points now carry `current_transformation_of pi index`
    - but `compose_pinstr_ext` still freezes ext-pinstr transformation to the
      raw stored `pi_transformation`
    - this mismatch is exactly why the old ext-compose theorems stop being
      naturally provable
  - added generic current-space helpers in
    [work/container-overlay/polcert/src/PolyLang.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PolyLang.v):
    - `current_transformation_at`
    - `current_access_transformation_at`
    - `current_access_transformation_of`
  - rewired
    [work/container-overlay/polcert/src/TilingRelation.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingRelation.v)
    `current_src_transformation_of_pinstr`
    to reuse the new `PolyLang` helper
  - added env-sized ext-composition scaffolding in
    [work/container-overlay/polcert/src/Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v):
    - `compose_pinstr_ext_at`
    - `compose_pinstrs_ext_at`
  - next step:
    migrate `Validator.validate` and the ext-compose proof chain from
    `PolyLang.compose_pinstrs_ext` to the env-sized current-space composition
2026-03-11

- Continued the witness-centered tiling/validator convergence work.
- Added `Validator`-side helper lemmas for current-space reasoning:
  - `current_env_dim_of_eq`
  - `current_transformation_of_eq_at`
  - `current_access_transformation_of_eq_at`
  - `expand_ip_instr_eq_current_tf_at`
  - `expand_ip_instr_eq_current_access_tf_at`
  - `in_compose_ipl_ext_inv`
- Re-read the actual runtime bridge in [work/container-overlay/polcert/driver/Entry.ml](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/Entry.ml) and confirmed a key structural fact:
  - `build_canonical_tiled_after` now stores the **source** transformation (`pi_transformation := before_pi.pi_transformation`) together with `pi_point_witness := PSWTiling w`.
  - Therefore the current object model is witness-centered at runtime.
- This gives a concrete explanation for the remaining `Validator.v` blocker:
  - `flatten_instr_nth` / source semantics use `current_transformation_of`.
  - `Validator` still assumes ext composition over raw stored transformations.
  - Under witness-centered tiling, that assumption is no longer generic.
- The next refactor target is therefore more fundamental than just patching the two old admits:
  - weaken the generic/well-formedness side so stored transformations can live on the base/source point-space,
  - and weaken the affine validator obligations so they only require the transformation properties actually used by `matrix_product` / `make_poly_eq`, not the older row-count coincidence.

- Continued by carving out a dedicated tiling-side validator path rather than
  forcing witness-centered programs through the old affine-only `validate`.
- Added tiling-side well-formedness predicates in
  [work/container-overlay/polcert/src/PolyLang.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/PolyLang.v):
  - `wf_pinstr_tiling`
  - `wf_pprog_tiling`
  - `wf_pinstr_ext_tiling`
- Added tiling-side checker/validator entry points in
  [work/container-overlay/polcert/src/Validator.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/Validator.v):
  - `check_wf_polyinstr_tiling`
  - `check_wf_polyprog_tiling`
  - `validate_tiling`
- Added the first ext-at bridge lemma:
  - `wf_pinstr_tiling_implies_wf_pinstr_ext_tiling_at`
- Fixed a stale current-space bug in `compose_pinstr_ext_at`:
  `pi_access_transformation_ext` now comes from
  `current_access_transformation_at`, not `current_transformation_at`.
- Switched the Coq checked tiling path to the new entry point:
  - `syntax/STilingOpt.v`
  - `driver/TPolOpt.v`
  - `driver/CPolOpt.v`
  now call `TilingVal.validate_tiling`.
- Switched the OCaml/runtime tiling debug path in
  [work/container-overlay/polcert/driver/Entry.ml](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/Entry.ml)
  to `validate_tiling` as well, and updated its statement-level debug
  expectations from the old padded relation to the witness-centered source
  relation.
- Current status:
  - the checked tiling pipeline is now structurally routed through a dedicated
    validator entry point;
  - `validate_tiling_correct` is still admitted;
  - the next proof work is concentrated in weakening the dependence-side
    theorems around `validate_two_accesses...` so they use the transformation
    properties actually needed by access composition, rather than the older
    affine row-count coincidence.

2026-03-13

- Closed the remaining tiling proof chain and rebuilt the full Coq/OCaml
  pipeline in the container.
- The key final direction was:
  - keep witness-centered `PolyLang`,
  - stop pushing tiling directly through the old codegen theorems,
  - route codegen through `current_view_pprog`,
  - and compose the already-proved affine codegen chain on that affine/current
    view.
- Renamed the witness-aware well-formedness layer to the more accurate
  `wf_pinstr_general` / `wf_pprog_general` (with compatibility aliases kept for
  the old `*_tiling` names).
- Added/used the top-down bridge:
  - `PrepareCodegen.prepared_codegen_correct_general`
  - `driver/TPolOpt.v` / `driver/CPolOpt.v`
    `checked_tiling_prepared_codegen_correct`
- Fixed the final module-instantiation issue by using
  `PrepareCodegen TilingPolIRs` in the tiling-side drivers, instead of reusing
  the old `CoreOpt.Prepare` instance.
- Rebuilt successfully in the container:
  - `src/PolyLang.vo`
  - `src/PrepareCodegen.vo`
  - `src/Validator.vo`
  - `src/TilingRelation.vo`
  - `src/TilingBoolChecker.vo`
  - `syntax/STilingOpt.vo`
  - `driver/TPolOpt.vo`
  - `driver/CPolOpt.vo`
  - `polopt`
  - `polcert`
- Verified there are no remaining `Admitted.` occurrences under:
  - `src`
  - `driver`
  - `syntax`
  - `polygen`
- Runtime confirmations in the container:
  - `./polopt syntax/examples/matadd.loop`
    now produces tiled optimized loops through the verified tiling path.
  - `./polcert --kind tiling /tmp/matmul.mid.scop /tmp/matmul.mid.scop.afterscheduling.scop`
    succeeds on real Pluto phase-2 tiling output.
  - `./polcert /tmp/matmul.beforescheduling.scop /tmp/matmul.mid.scop /tmp/matmul.mid.scop.afterscheduling.scop`
    succeeds in phase-aligned mode with:
    - affine(before, mid): OK
    - tiling(mid, after): OK

2026-03-25

- Continued the Pluto-bug investigation from the host-side notes/code mirror,
  focusing on the `matmul --parallel` `--readscop` case.
- Strengthened the local diagnosis in
  [doc/possible-bugs/pluto-parallel-hint-matmul-readscop.md](/home/hugh/research/polyhedral/polcert/doc/possible-bugs/pluto-parallel-hint-matmul-readscop.md):
  - `driver/Scheduler.ml` only parses raw `<loop>` + `<scatnames>` and maps
    `t1 -> current_dim 0`, so the mismatch does not look like a PolCert hint
    parser bug.
  - `src/ParallelValidator.v` makes the `dim 0` rejection explainable from the
    checked semantics itself:
    - for dim `0`, same-prefix checking is vacuous
    - so different `K/32` tiles for the same `(i, j)` accumulation are forced
      to permute
    - that is exactly the unsafe case for `matmul`
  - the accepted fallback dim `1` lines up with fixing `K/32` and
    parallelizing across `N/32`, which is the safe blocked-column parallelism
    the frontend emits.
- Also recorded the practical consequence:
  `tests/end-to-end-generated/BEST_PIPELINES.md` still picks the `--parallel`
  route for `matmul` with real emitted parallelism and a strong speedup, so the
  fallback is not just conservative bookkeeping; it appears to recover useful
  safe parallelism.
- Limitation of this session:
  the container/runtime path was not directly executable from the current
  environment because `docker` was unavailable here, so this update is based on
  the checked-in reproducer, the mirrored code under
  `work/container-overlay/polcert`, and existing project notes rather than a
  fresh container rerun.

2026-03-26

- Closed the follow-up "second bug" investigation for `matmul --parallel`.
- Final diagnosis:
  this was not another new Pluto upstream bug; it was a PolCert-side
  integration/configuration bug in the tile-stage `--parallel` path.
- What was wrong:
  - `driver/Scheduler.ml` used the tile-stage Pluto flags
    `--identity --tile ... --parallel`
  - on `matmul`, Pluto's default tiled `--parallel` mode produced a
    wavefront/skewed tile schedule rather than the canonical strip-mined tiled
    order expected by the current phase-aligned witness path
  - concretely, the outer tile schedule changed from a canonical first tile
    dimension `fk0` to a skewed dimension `fk0+fk1`
  - that made the checked frontend fail at:
    - `[debug-parallel] phase tiling validate=false(ok=true)`
    - followed by a checked fallback to the sequential optimized loop
- Confirmed in Docker that this was a configuration mismatch rather than a new
  Pluto implementation bug:
  - both the patched local Pluto and current upstream Pluto still produce the
    same wavefront-style tile schedule by default under
    `--readscop --identity --tile --parallel`
  - adding `--innerpar` keeps the tiled schedule canonical on the same input
- Fixed PolCert by adding `--innerpar` to
  [work/container-overlay/polcert/driver/Scheduler.ml](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/driver/Scheduler.ml)
  `tile_only_parallel_flags`.
- Also strengthened the whole-C harness so this behavior is easy to regression
  test:
  - [work/container-overlay/polcert/tools/end_to_end_c/run_case.py](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/tools/end_to_end_c/run_case.py)
    now supports:
    - extra `polopt` arguments via `--polopt-arg`
    - `--require-parallelized`
    - `parallelized_loop` reporting
  - [work/container-overlay/polcert/Makefile](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/Makefile)
    now provides:
    - `test-end-to-end-c-matmul-parallel`
- Post-fix Docker validation:
  - `./polopt --parallel tests/end-to-end-c/cases/matmul/matmul.loop`
    now emits verified `parallel for i1 ...`
  - `./polopt --parallel --parallel-strict ...`
    also succeeds instead of falling back
  - debug output now shows:
    - `phase affine validate=true(ok=true)`
    - `phase tiling validate=true(ok=true)`
    - `checked_tiling_validate=true(ok=true)`
  - `opam exec -- make test-end-to-end-c-matmul-parallel`
    passes with:
    - `parallelized_loop=true`
    - `exact_match=true`
- Recorded the detailed note in
  [doc/possible-bugs/polcert-parallel-tile-innerpar.md](/home/hugh/research/polyhedral/polcert/doc/possible-bugs/polcert-parallel-tile-innerpar.md).

- Started Stage 1 of the diamond-tiling track in Docker, using Pluto's real
  stencil fixtures:
  - `/pluto/test/jacobi-1d-imper.c`
  - `/pluto/test/diamond-tile-example.c`
- Real-producer observation:
  Pluto's `--dumpscop --tile --noparallel --diamond-tile` path only dumps:
  - `*.beforescheduling.scop`
  - `*.afterscheduling.scop`
  while the debug log shows a diamond-aware midpoint internally via:
  - `Transformations before concurrent start enable`
  - `Transformations after concurrent start enable`
  So the current producer still does not expose an explicit
  `mid_diamond.scop`.
- Important positive result:
  the existing OpenScop-side witness extractor/checker already accepts the
  diamond tiling links on these real fixtures:
  - `./polopt --extract-tiling-witness-openscop before after`
  - `./polopt --validate-tiling-openscop before after`
  both succeed on the dumped `before/after` files.
- Concrete extracted links included:
  - `jacobi-1d-imper`:
    - `fk0 = floor((2*t - i) / 32)`
    - `fk1 = floor((2*t + i) / 32)`
  - `diamond-tile-example`:
    - `fk0 = floor((t + i) / 32)`
    - `fk1 = floor((t - i) / 32)`
- Important negative result:
  attempting to retrofit diamond as a tile-only post-midpoint phase with
  `pluto --readscop --identity --tile --noparallel --diamond-tile before.scop`
  reported `0 bands`, which strongly supports the current design claim that
  diamond cannot be treated as "ordinary midpoint + tile-only flag".
- The implementation consequence is now sharper:
  the first engineering target should be an explicit scheduler/orchestration
  contract for `mid_diamond`, not an early rewrite of the checked tiling
  relation.
