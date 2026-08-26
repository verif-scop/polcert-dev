# PolCert Project Notes

## Scope
- Project goal: validated/verified polyhedral scheduling and codegen in Coq, aligned with CompCert-related IR flow.
- Main runtime environment: Docker container `gifted_curie` (`hughshine/polcert:latest`).
- Repository path inside container: `/polcert`.

## Known Practical Facts
- `coqc` and `ocamldep` may be missing from default PATH in non-opam shells.
- Run `eval $(opam env --switch=polcert --set-switch)` before build/test commands.
- `polcert` executable validates two OpenScop files and outputs one of `EQ`, `GT`, `LT`, `NE`.

## Critical Files
- Pipeline composition: `driver/PolOpt.v`
- Extractor theorem gap: `src/Extractor.v` (`extractor_correct`)
- Validator theorem: `src/Validator.v` (`validate_correct`)
- PolyGen codegen theorem: `polygen/CodeGen.v` (`codegen_correct`)
- OpenScop/Csyntax conversion utilities: `src/Convert.v`

## Baseline Commands
```bash
docker exec gifted_curie sh -lc 'cd /polcert && eval $(opam env --switch=polcert --set-switch) && make -s check-admitted'
docker exec gifted_curie sh -lc 'cd /polcert && ./polcert tests/csample3/polcert46ff92.scop.beforescheduling.scop tests/csample3/polcert46ff92.scop.afterscheduling.scop'
```

## Proof/TODO Scan Commands
```bash
docker exec gifted_curie sh -lc "cd /polcert && grep -RInE 'Admitted\\.|Abort\\.|Axiom ' src polygen driver || true"
docker exec gifted_curie sh -lc "cd /polcert && grep -RInE '^Parameter |^Axiom ' src polygen driver common cfrontend cparser lib VPL || true"
```
