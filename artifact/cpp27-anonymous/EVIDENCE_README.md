# Evidence

| Reviewer question | Start here | What it shows |
| --- | --- | --- |
| What do the optimized loops look like? | `optimized-loop-examples/index.html` | Side-by-side source and accepted Loop programs, with a diff for each case. |
| Which transformations and options were tested? | `results/test-catalog.html` | Every case has its own page. Accepted cases show the source and optimized Loop programs, the observed optimization, the run settings, and whether both produced the same result. Other cases explain why no before/after run applies. |
| Which compiler paths have end-to-end theorems? | `results/proof-report.md` | The theorem attached to each public route, plus checks for unfinished proofs and unrealized extraction axioms. |
| Do accepted Loop programs produce the same result? | `results/test-catalog.html` | The audit covers every accepted pair record by executing each unique program and parameter configuration; duplicate records reuse that run. Each applicable page reports the parameters, run count, thread count where relevant, and whether the results agree. |
| What performance did the accepted programs show? | `performance-comparisons/index.html` | Baseline and optimized times for all 62 generated whole-C kernels, with the selected checked route and measurement limits. |
| What happens when the optimizer proposes an unsafe or non-certifiable result? | `rejected-optimizer-outputs/index.html` | Why each proposal cannot be accepted and whether PolCert rejects it or uses a certified fallback. |

Machine-readable summaries are in `summary.json`, `results/test-catalog.json`,
and `results/run-results.json`. Command output is retained under `results/raw/`
for diagnosis, but is not the primary presentation.
