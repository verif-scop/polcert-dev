# Repro Commands (Extractor Status)

## Commit and theorem scan
```bash
docker exec gifted_curie sh -lc 'cd /polcert && git log --oneline --decorate -n 20'
docker exec gifted_curie sh -lc 'cd /polcert && grep -RIn --include="*.v" "Theorem extractor_correct\\|Admitted\\." src/Extractor.v driver/PolOpt.v'
```

## Baseline checks
```bash
docker exec gifted_curie sh -lc 'cd /polcert && eval $(opam env --switch=polcert --set-switch) && make -s check-admitted'
docker exec gifted_curie sh -lc 'cd /polcert && ./polcert tests/csample3/polcert46ff92.scop.beforescheduling.scop tests/csample3/polcert46ff92.scop.afterscheduling.scop'
```

## Coq probing pattern
Use:
```bash
docker exec gifted_curie sh -lc "cd /polcert && eval \$(opam env --switch=polcert --set-switch) && coqtop \$(cat _CoqProject) -quiet < /tmp/<probe>.v"
```

Notes:
- Keep probes small; full `cbv` over converter-heavy terms can explode.
- Prefer focused `Eval cbv in` of dimension and wf booleans.
