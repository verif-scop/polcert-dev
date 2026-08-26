# PrepareCodegen Stack

## Current checkpoint
- The minimal `flatten_*` repair is in place.
- Downstream proof repair was pushed through:
  - `src/PolyLang.v`
  - `src/Validator.v`
  - `src/Extractor.v`
  - `src/PrepareCodegen.v`
- `PrepareCodegen.prepare_codegen_semantics_correct` is now `Qed`.

## What closed the theorem
- Added a reverse domain lemma:
  - `encode_depth_in_domain_from_source`
- Added a reverse scan lemma:
  - `source_ip_props_imply_prepare_env_scan_true`
- Added the point reconstruction lemma:
  - `source_ip_of_self`
- Added a local uniqueness bridge for `SelectionSort` output:
  - `source_like_points_imply_NoDupA_np`

## Final proof shape
1. Invert `PolyLang.semantics (prepare_codegen pol)` to get:
   - `Compat`
   - `NonAlias`
   - `InitEnv varctxt envv st`
   - prepared `env_poly_semantics`
2. Use `prepare_poly_semantics_collect` to extract a schedule-sorted execution list `exec_ipl`.
3. Sort `exec_ipl` by `np` using `SelectionSort` to obtain `ipl`.
4. Rebuild `flatten_instrs envv pis ipl`:
   - forward direction from collected execution points via
     `prepare_env_scan_true_implies_source_ip_props`
   - backward direction via
     `source_ip_props_imply_prepare_env_scan_true`
     and `source_ip_of_self`
5. Package the result with `PolyPointListSema` and `PIPSemaIntro`.

## Current result
- `prepare_codegen_preserves_ready`: `Qed`
- `prepare_codegen_preserves_wf`: `Qed`
- `prepare_codegen_semantics_correct`: `Qed`
- `prepared_codegen_correct`: compiles unchanged on top
- `driver/PolOptPrepared.v`: compiles
- `driver/PolOptPrepared.v` now exposes public aliases:
  - `Opt`
  - `Opt_correct`
- `check-admitted`: `Nothing admitted.`
- full `opam exec -- make -j2`: passes
