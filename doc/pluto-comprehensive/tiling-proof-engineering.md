# Tiling Proof Engineering Notes

This note records proof-engineering patterns that became important while pushing the tiling proof from local row lemmas toward whole-program correctness.

## 1. Split executable extraction from verified checking

For tiling, `infer witness` and `check witness` should stay separate.

- The executable extractor can recover witness structure from Pluto output.
- The Coq target should be the checker, not the extractor.
- This keeps the proof target stable even when extraction heuristics change.

## 2. Pull pure list lemmas out of giant proof files

Small list-manipulation lemmas can become fragile when proved inside a very large file with many preceding proofs.

- `skipn_eval_tile_links_suffix` was easier to stabilize once moved into its own file: [TilingList.v](/home/hugh/research/polyhedral/polcert/work/container-overlay/polcert/src/TilingList.v)
- This reduces focus/shelving noise from unrelated proofs.
- It also makes the helper reusable from multiple tiling relations.

## 3. Prefer `assert + rewrite` over brittle `rewrite ... by ...`

When a proof step depends on arithmetic or list-length equalities, it is often safer to first name the equality.

- Good pattern:
  - prove `Hlen_eval`
  - prove `Hskip_links`
  - use `replace ... by exact Hskip_links`
- This avoids hidden subgoals left by aggressive `rewrite ... by ...` scripts.

## 4. Normalize list shape before using `skipn_app` / `firstn_app`

Many failures came from applying list lemmas before the target was in the intended syntactic shape.

- Do not assume the current `++` association shape.
- Inspect the exact goal first if a rewrite unexpectedly fails.
- Prefer proving a small intermediate equality such as `Htiled` and then rewriting the main goal with it.

## 5. Avoid overusing `simpl` around symbolic `length` / `skipn`

`simpl` can be too strong when the same symbolic structure appears in both:

- the index `length (stw_links w)`
- the list `eval_tile_links ... (stw_links w)`

In that situation, `simpl` may destroy the precise `skipn (...) ( ... ++ ... )` shape you were about to discharge with a helper theorem.

- Use the minimum local simplification needed.
- Prefer targeted rewrites like `app_nil_l`, `app_nil_r`, or explicit `replace`.

## 6. Prove an index equality first, then rewrite whole records

For statement-level tiling lemmas, a robust shape is:

1. prove an index equation like `Hidx`
2. rewrite the record with `Hidx`
3. let `ip_index` and `ip_time_stamp` normalize together

This is more stable than separately rewriting:

- `ip_index`
- the same index embedded under `affine_product`

## 7. Use source-level debugging, not just imported `.vo` debugging

A standalone debug script that imports an already-compiled `.vo` can be misleading.

- If the current source file no longer compiles, debugging against the old `.vo` only shows the previous state.
- When in doubt, debug by truncating the current source file and inserting `Show.` at the exact point of failure.

## 8. When a local subgoal is the real blocker, isolate it as its own theorem

Several stuck steps turned out not to be semantic blockers but shape blockers.

- If a subgoal has a stable mathematical statement, extract it into a helper theorem.
- This makes the main theorem shorter and gives the small theorem its own compile/debug cycle.

## 9. Prefer proof shapes that match later program-level composition

The tiling proof is heading toward:

- `before <-> retiled_old`
- `retiled_old <-> after`

So local proofs should expose reusable bridges:

- index reconstruction
- timestamp preservation
- membership preservation
- effect preservation

This is better than proving monolithic local facts that cannot be composed upward.
