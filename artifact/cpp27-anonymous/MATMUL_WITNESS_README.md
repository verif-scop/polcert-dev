# Matrix-Multiplication Parallel Hint

This case records a loop dimension that Pluto proposes to run in parallel for
matrix multiplication when read-after-read dependences are included. PolCert
rejects that dimension because it cannot prove it safe. A permissive
configuration may choose a different, verified dimension; a strict
configuration keeps the loop sequential.

Files:

- `matmul.loop`: structured-loop input;
- `run.py`: test runner;
- `../validation.log`: recorded result from the complete witness run.
