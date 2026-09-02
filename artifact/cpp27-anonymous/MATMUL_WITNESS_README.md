# Matrix-Multiplication Parallel Hint

This is a coordinate-mapping regression, not a demonstrated Pluto
miscompilation. With explicit read-after-read dependences, Pluto's hint names a
raw scattering coordinate that corresponds to a safe generated parallel loop.

PolCert maps that raw coordinate through schedule canonicalization before
validation. Strict and permissive modes therefore certify and parallelize the
same intended loop. The recorded test also checks that the obsolete compact-C
loop-depth interpretation is not used.

Files:

- `matmul.loop`: structured-loop input;
- `run.py`: test runner;
- `../validation.log`: recorded result from the complete reliability run.
