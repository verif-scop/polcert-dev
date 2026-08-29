# Matrix-Multiplication Parallel Hint

This is a conservative-validation example, not a demonstrated Pluto
miscompilation. With explicit read-after-read dependences, Pluto's hint names a
schedule coordinate that PolCert cannot certify as a safe generated parallel
loop for this matrix-multiplication schedule.

Strict mode rejects the requested optimization and emits no optimized loop.
Permissive mode ignores the non-certifiable hint and chooses a different
dimension that passes the parallel-loop check. The recorded test requires both
outcomes.

Files:

- `matmul.loop`: structured-loop input;
- `run.py`: test runner;
- `../validation.log`: recorded result from the complete witness run.
