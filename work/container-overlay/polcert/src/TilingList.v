Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Require Import TilingWitness.

Lemma skipn_eval_tile_links_suffix :
  forall point params links,
    skipn
      (List.length links)
      (eval_tile_links [] point params links ++ point) = point.
Proof.
  intros point params links.
  rewrite skipn_app.
  assert (Hlen_eval :
    List.length (eval_tile_links [] point params links) = List.length links).
  {
    rewrite eval_tile_links_length.
    simpl.
    lia.
  }
  assert (Hskip_links :
    skipn (List.length links) (eval_tile_links [] point params links) = []).
  {
    apply skipn_all2.
    lia.
  }
  assert (Hlen_links :
    (List.length links - List.length (eval_tile_links [] point params links))%nat = 0%nat).
  {
    lia.
  }
  replace
    (skipn (List.length links) (eval_tile_links [] point params links))
    with ([] : list Z) by exact Hskip_links.
  replace
    (List.length links - List.length (eval_tile_links [] point params links))%nat
    with 0%nat by exact Hlen_links.
  simpl.
  reflexivity.
Qed.
