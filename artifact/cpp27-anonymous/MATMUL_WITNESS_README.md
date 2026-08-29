# Matrix-Multiplication Parallel Hint

This case records a candidate parallel dimension proposed for matrix
multiplication when read-after-read dependences are explicitly included. The
checked parallel route rejects that dimension. The non-strict frontend can
select a different certified dimension, while the strict route leaves the loop
sequential.

Files:

- `matmul.loop`: structured-loop input;
- `run.py`: witness runner;
- `../validation.log`: recorded result from the complete witness run.
