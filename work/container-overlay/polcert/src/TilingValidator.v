Require Import Bool.
Require Import List.
Require Import String.
Require Import Sorting.Sorted.
Require Import Sorting.Permutation.
Import ListNotations.
Require Import Result.
Require Import PolyBase.
Require Import PolyLang.
Require Import PolyLoop.
Require Import Loop.
Require Import ZArith.
Require Import TilingRelation.
Require Import TilingBoolChecker.
Require Import TilingWitness.
Require Import PointWitness.
Require Import ISSWitness.
Require Import AffineValidator.
Require Import PrepareCodegen.
Require Import PolIRs.
Require Import OpenScop.
Require Import ImpureAlarmConfig.
Require Import Vpl.Impure.

Module TilingValidator (PolIRs: POLIRS).

Module Instr := PolIRs.Instr.
Module State := PolIRs.State.
Module TilingCheck := TilingBoolChecker Instr.
Module Tiling := TilingCheck.Tiling.

Module TilingPolIRs <: POLIRS with Module Instr := Instr.
  Module Instr := Instr.
  Module State := Instr.State.
  Module Ty := Instr.Ty.
  Module PolyLang := Tiling.PL.
  Module PolyLoop := PolyLoop Instr.
  Module Loop := Loop Instr.
  Definition scheduler (_: PolyLang.t) : result PolyLang.t := Err EmptyString.
  Definition affine_scheduler := scheduler.
  Definition export_for_phase_scheduler (_: PolyLang.t) : option OpenScop := None.
  Definition export_for_pluto_phase_pipeline := export_for_phase_scheduler.
  Definition to_phase_openscop := export_for_phase_scheduler.
  Definition phase_scop_scheduler (_: OpenScop) : result (OpenScop * OpenScop) :=
    Err EmptyString.
  Definition run_pluto_phase_pipeline := phase_scop_scheduler.
  Definition phase_scop_scheduler_with_iss
      (_: OpenScop) : result (OpenScop * OpenScop) :=
    Err EmptyString.
  Definition run_pluto_phase_pipeline_with_iss :=
    phase_scop_scheduler_with_iss.
  Definition infer_iss_from_source_scop
      (_: PolyLang.t) (_: OpenScop)
      : result (option (PolyLang.t * iss_witness)) :=
    Err EmptyString.
  Definition infer_tiling_witness_scops
      (_ _ : OpenScop) : result (list statement_tiling_witness) :=
    Err EmptyString.
End TilingPolIRs.

Module GeneralValidator := AffineValidator TilingPolIRs.
Module TilingVal := GeneralValidator.
Module CurrentViewPrepare := PrepareCodegen TilingPolIRs.
Module TPrepare := CurrentViewPrepare.

Definition outer_to_tiling_pinstr
    (pi : PolIRs.PolyLang.PolyInstr) : Tiling.PL.PolyInstr :=
  {|
    Tiling.PL.pi_depth := PolIRs.PolyLang.pi_depth pi;
    Tiling.PL.pi_instr := PolIRs.PolyLang.pi_instr pi;
    Tiling.PL.pi_poly := PolIRs.PolyLang.pi_poly pi;
    Tiling.PL.pi_schedule := PolIRs.PolyLang.pi_schedule pi;
    Tiling.PL.pi_point_witness := PolIRs.PolyLang.pi_point_witness pi;
    Tiling.PL.pi_transformation := PolIRs.PolyLang.pi_transformation pi;
    Tiling.PL.pi_access_transformation :=
      PolIRs.PolyLang.pi_access_transformation pi;
    Tiling.PL.pi_waccess := PolIRs.PolyLang.pi_waccess pi;
    Tiling.PL.pi_raccess := PolIRs.PolyLang.pi_raccess pi;
  |}.

Definition outer_to_tiling_pprog
    (pp : PolIRs.PolyLang.t) : Tiling.PL.t :=
  let '(pis, varctxt, vars) := pp in
  (List.map outer_to_tiling_pinstr pis, varctxt, vars).

(** Explicit name for the representation change from a generic PolyLang program
    to the internal tiling-model program used by the checked tiling validator. *)
Definition to_tiling_pprog := outer_to_tiling_pprog.

Definition outer_to_tiling_ip
    (ip : PolIRs.PolyLang.InstrPoint) : Tiling.PL.InstrPoint :=
  {|
    Tiling.PL.ip_nth := PolIRs.PolyLang.ip_nth ip;
    Tiling.PL.ip_index := PolIRs.PolyLang.ip_index ip;
    Tiling.PL.ip_transformation := PolIRs.PolyLang.ip_transformation ip;
    Tiling.PL.ip_time_stamp := PolIRs.PolyLang.ip_time_stamp ip;
    Tiling.PL.ip_instruction := PolIRs.PolyLang.ip_instruction ip;
    Tiling.PL.ip_depth := PolIRs.PolyLang.ip_depth ip;
  |}.

Definition outer_to_tiling_ipl
    (ipl : list PolIRs.PolyLang.InstrPoint) : list Tiling.PL.InstrPoint :=
  List.map outer_to_tiling_ip ipl.

Definition tiling_to_outer_ip
    (ip : Tiling.PL.InstrPoint) : PolIRs.PolyLang.InstrPoint :=
  {|
    PolIRs.PolyLang.ip_nth := Tiling.PL.ip_nth ip;
    PolIRs.PolyLang.ip_index := Tiling.PL.ip_index ip;
    PolIRs.PolyLang.ip_transformation := Tiling.PL.ip_transformation ip;
    PolIRs.PolyLang.ip_time_stamp := Tiling.PL.ip_time_stamp ip;
    PolIRs.PolyLang.ip_instruction := Tiling.PL.ip_instruction ip;
    PolIRs.PolyLang.ip_depth := Tiling.PL.ip_depth ip;
  |}.

Definition tiling_to_outer_ipl
    (ipl : list Tiling.PL.InstrPoint) : list PolIRs.PolyLang.InstrPoint :=
  List.map tiling_to_outer_ip ipl.

Definition tiling_to_outer_pinstr
    (pi : Tiling.PL.PolyInstr) : PolIRs.PolyLang.PolyInstr :=
  {|
    PolIRs.PolyLang.pi_depth := Tiling.PL.pi_depth pi;
    PolIRs.PolyLang.pi_instr := Tiling.PL.pi_instr pi;
    PolIRs.PolyLang.pi_poly := Tiling.PL.pi_poly pi;
    PolIRs.PolyLang.pi_schedule := Tiling.PL.pi_schedule pi;
    PolIRs.PolyLang.pi_point_witness := Tiling.PL.pi_point_witness pi;
    PolIRs.PolyLang.pi_transformation := Tiling.PL.pi_transformation pi;
    PolIRs.PolyLang.pi_access_transformation :=
      Tiling.PL.pi_access_transformation pi;
    PolIRs.PolyLang.pi_waccess := Tiling.PL.pi_waccess pi;
    PolIRs.PolyLang.pi_raccess := Tiling.PL.pi_raccess pi;
  |}.

Definition tiling_to_outer_pprog
    (pp : Tiling.PL.t) : PolIRs.PolyLang.t :=
  let '(pis, varctxt, vars) := pp in
  (List.map tiling_to_outer_pinstr pis, varctxt, vars).

Definition from_tiling_pprog := tiling_to_outer_pprog.

Lemma outer_to_tiling_wf_pinstr_affine :
  forall varctxt vars pi,
    PolIRs.PolyLang.wf_pinstr_affine varctxt vars pi ->
    Tiling.PL.wf_pinstr_affine varctxt vars (outer_to_tiling_pinstr pi).
Proof.
  intros varctxt vars
         [depth instr poly sched pw tf tfacc wacc racc] Hwf.
  simpl in *.
  exact Hwf.
Qed.

Lemma outer_to_tiling_wf_pprog_affine :
  forall pp,
    PolIRs.PolyLang.wf_pprog_affine pp ->
    Tiling.PL.wf_pprog_affine (outer_to_tiling_pprog pp).
Proof.
  intros [[pis varctxt] vars] Hwf.
  unfold outer_to_tiling_pprog.
  simpl in *.
  destruct Hwf as [Hvars Hwf_pis].
  split; [exact Hvars|].
  intros pi Hin.
  apply List.in_map_iff in Hin.
  destruct Hin as [pi0 [Hpi_eq Hin0]].
  subst pi.
  eapply outer_to_tiling_wf_pinstr_affine.
  eapply Hwf_pis; eauto.
Qed.

Lemma outer_to_tiling_wf_pinstr_general :
  forall varctxt vars pi,
    PolIRs.PolyLang.wf_pinstr_general varctxt vars pi ->
    Tiling.PL.wf_pinstr_general varctxt vars (outer_to_tiling_pinstr pi).
Proof.
  intros varctxt vars
         [depth instr poly sched pw tf tfacc wacc racc] Hwf.
  simpl in *.
  exact Hwf.
Qed.

Lemma outer_to_tiling_wf_pprog_general :
  forall pp,
    PolIRs.PolyLang.wf_pprog_general pp ->
    Tiling.PL.wf_pprog_general (outer_to_tiling_pprog pp).
Proof.
  intros [[pis varctxt] vars] Hwf.
  unfold outer_to_tiling_pprog.
  simpl in *.
  destruct Hwf as [Hvars Hwf_pis].
  split; [exact Hvars|].
  intros pi Hin.
  apply List.in_map_iff in Hin.
  destruct Hin as [pi0 [Hpi_eq Hin0]].
  subst pi.
  eapply outer_to_tiling_wf_pinstr_general.
  eapply Hwf_pis; eauto.
Qed.

Lemma tiling_to_outer_wf_pinstr_general :
  forall varctxt vars pi,
    Tiling.PL.wf_pinstr_general varctxt vars pi ->
    PolIRs.PolyLang.wf_pinstr_general varctxt vars (tiling_to_outer_pinstr pi).
Proof.
  intros varctxt vars
         [depth instr poly sched pw tf tfacc wacc racc] Hwf.
  simpl in *.
  exact Hwf.
Qed.

Lemma tiling_to_outer_wf_pprog_general :
  forall pp,
    Tiling.PL.wf_pprog_general pp ->
    PolIRs.PolyLang.wf_pprog_general (tiling_to_outer_pprog pp).
Proof.
  intros [[pis varctxt] vars] Hwf.
  unfold tiling_to_outer_pprog.
  simpl in *.
  destruct Hwf as [Hvars Hwf_pis].
  split; [exact Hvars|].
  intros pi Hin.
  apply List.in_map_iff in Hin.
  destruct Hin as [pi0 [Hpi_eq Hin0]].
  subst pi.
  eapply tiling_to_outer_wf_pinstr_general.
  eapply Hwf_pis; eauto.
Qed.

Lemma nth_error_map_inv :
  forall (A B : Type) (f : A -> B) xs n y,
    nth_error (List.map f xs) n = Some y ->
    exists x,
      nth_error xs n = Some x /\
      y = f x.
Proof.
  induction xs as [|x xs IH]; intros n y Hnth.
  - destruct n; simpl in Hnth; discriminate.
  - destruct n; simpl in Hnth.
    + inversion Hnth. subst. exists x. split; reflexivity.
    + eapply IH in Hnth.
      destruct Hnth as [x' [Hxs Hy]].
      exists x'. split; exact Hxs || exact Hy.
Qed.

Lemma nth_error_map :
  forall (A B : Type) (f : A -> B) xs n x,
    nth_error xs n = Some x ->
    nth_error (List.map f xs) n = Some (f x).
Proof.
  induction xs as [|x0 xs IH]; intros n x Hnth.
  - destruct n; discriminate.
  - destruct n; simpl in *.
    + inversion Hnth. subst. reflexivity.
    + eapply IH. exact Hnth.
Qed.

Lemma outer_to_tiling_belongs_to_iff :
  forall ip pi,
    Tiling.PL.belongs_to (outer_to_tiling_ip ip) (outer_to_tiling_pinstr pi) <->
    PolIRs.PolyLang.belongs_to ip pi.
Proof.
  intros ip
         [depth instr poly sched pw tf tfacc wacc racc].
  unfold Tiling.PL.belongs_to, PolIRs.PolyLang.belongs_to.
  simpl.
  tauto.
Qed.

Lemma outer_to_tiling_np_lt_iff :
  forall ip1 ip2,
    Tiling.PL.np_lt (outer_to_tiling_ip ip1) (outer_to_tiling_ip ip2) <->
    PolIRs.PolyLang.np_lt ip1 ip2.
Proof.
  intros ip1 ip2.
  unfold Tiling.PL.np_lt, PolIRs.PolyLang.np_lt.
  simpl.
  tauto.
Qed.

Lemma tiling_to_outer_np_lt_iff :
  forall ip1 ip2,
    PolIRs.PolyLang.np_lt (tiling_to_outer_ip ip1) (tiling_to_outer_ip ip2) <->
    Tiling.PL.np_lt ip1 ip2.
Proof.
  intros ip1 ip2.
  unfold Tiling.PL.np_lt, PolIRs.PolyLang.np_lt.
  simpl.
  tauto.
Qed.

Lemma outer_to_tiling_instr_point_sched_le_iff :
  forall ip1 ip2,
    Tiling.PL.instr_point_sched_le
      (outer_to_tiling_ip ip1) (outer_to_tiling_ip ip2) <->
    PolIRs.PolyLang.instr_point_sched_le ip1 ip2.
Proof.
  intros ip1 ip2.
  unfold Tiling.PL.instr_point_sched_le, PolIRs.PolyLang.instr_point_sched_le.
  simpl.
  tauto.
Qed.

Lemma tiling_to_outer_instr_point_sched_le_iff :
  forall ip1 ip2,
    Tiling.PL.instr_point_sched_le ip1 ip2 <->
    PolIRs.PolyLang.instr_point_sched_le
      (tiling_to_outer_ip ip1) (tiling_to_outer_ip ip2).
Proof.
  intros [nth1 idx1 tf1 ts1 instr1 depth1]
         [nth2 idx2 tf2 ts2 instr2 depth2].
  unfold Tiling.PL.instr_point_sched_le, PolIRs.PolyLang.instr_point_sched_le.
  simpl.
  tauto.
Qed.

Lemma outer_to_tiling_instr_point_sema_iff :
  forall ip st1 st2,
    Tiling.PL.instr_point_sema (outer_to_tiling_ip ip) st1 st2 <->
    PolIRs.PolyLang.instr_point_sema ip st1 st2.
Proof.
  intros ip st1 st2.
  split; intro Hsema.
  - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
    econstructor.
    simpl in *.
    exact Hsem.
  - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
    econstructor.
    simpl in *.
    exact Hsem.
Qed.

Lemma tiling_to_outer_instr_point_sema_iff :
  forall ip st1 st2,
    PolIRs.PolyLang.instr_point_sema (tiling_to_outer_ip ip) st1 st2 <->
    Tiling.PL.instr_point_sema ip st1 st2.
Proof.
  intros ip st1 st2.
  split; intro Hsema.
  - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
    econstructor.
    simpl in *.
    exact Hsem.
  - inversion Hsema as [wcs rcs Hsem]; clear Hsema.
    econstructor.
    simpl in *.
    exact Hsem.
Qed.

Lemma tiling_to_outer_ipl_outer_to_tiling :
  forall ipl,
    List.map tiling_to_outer_ip (outer_to_tiling_ipl ipl) = ipl.
Proof.
  induction ipl as [|ip ipl IH]; simpl.
  - reflexivity.
  - destruct ip; simpl.
    f_equal; exact IH.
Qed.

Lemma outer_to_tiling_ipl_tiling_to_outer :
  forall ipl,
    outer_to_tiling_ipl (List.map tiling_to_outer_ip ipl) = ipl.
Proof.
  induction ipl as [|ip ipl IH]; simpl.
  - reflexivity.
  - destruct ip; simpl.
    f_equal; exact IH.
Qed.

Lemma outer_to_tiling_instr_point_list_semantics :
  forall ipl st1 st2,
    PolIRs.PolyLang.instr_point_list_semantics ipl st1 st2 ->
    Tiling.PL.instr_point_list_semantics (outer_to_tiling_ipl ipl) st1 st2.
Proof.
  intros ipl st1 st2 Hsema.
  induction Hsema.
  - simpl.
    econstructor.
    exact H.
  - simpl.
    econstructor.
    + apply (proj2 (outer_to_tiling_instr_point_sema_iff ip st1 st2)).
      exact H.
    + exact IHHsema.
Qed.

Lemma tiling_to_outer_instr_point_list_semantics :
  forall ipl st1 st2,
    Tiling.PL.instr_point_list_semantics ipl st1 st2 ->
    PolIRs.PolyLang.instr_point_list_semantics (List.map tiling_to_outer_ip ipl) st1 st2.
Proof.
  intros ipl st1 st2 Hsema.
  induction Hsema.
  - simpl.
    econstructor.
    exact H.
  - simpl.
    econstructor.
    + apply (proj2 (tiling_to_outer_instr_point_sema_iff ip st1 st2)).
      exact H.
    + exact IHHsema.
Qed.

Lemma outer_to_tiling_instr_point_list_semantics_iff :
  forall ipl st1 st2,
    Tiling.PL.instr_point_list_semantics (outer_to_tiling_ipl ipl) st1 st2 <->
    PolIRs.PolyLang.instr_point_list_semantics ipl st1 st2.
Proof.
  intros ipl st1 st2.
  split; intro Hsema.
  - pose proof
      (tiling_to_outer_instr_point_list_semantics
         (outer_to_tiling_ipl ipl) st1 st2 Hsema) as Houter.
    now rewrite tiling_to_outer_ipl_outer_to_tiling in Houter.
  - exact (outer_to_tiling_instr_point_list_semantics ipl st1 st2 Hsema).
Qed.

Lemma NoDup_outer_to_tiling_ipl :
  forall ipl,
    NoDup ipl ->
    NoDup (outer_to_tiling_ipl ipl).
Proof.
  intros ipl Hnodup.
  induction Hnodup as [|ip ipl Hnotin Hnodup IH].
  - constructor.
  - simpl.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [ip' [Heq Hin']].
      assert (ip = ip').
      { destruct ip, ip'; simpl in Heq; inversion Heq; subst; reflexivity. }
      subst.
      contradiction.
    + exact IH.
Qed.

Lemma NoDup_tiling_to_outer_ipl :
  forall ipl,
    NoDup ipl ->
    NoDup (List.map tiling_to_outer_ip ipl).
Proof.
  intros ipl Hnodup.
  induction Hnodup as [|ip ipl Hnotin Hnodup IH].
  - constructor.
  - simpl.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [ip' [Heq Hin']].
      assert (ip = ip').
      { destruct ip, ip'; simpl in Heq; inversion Heq; subst; reflexivity. }
      subst.
      contradiction.
    + exact IH.
Qed.

Lemma Sorted_outer_to_tiling_ipl :
  forall ipl,
    Sorted PolIRs.PolyLang.np_lt ipl ->
    Sorted Tiling.PL.np_lt (outer_to_tiling_ipl ipl).
Proof.
  intros ipl Hsorted.
  induction Hsorted.
  - constructor.
  - simpl.
    constructor.
    + exact IHHsorted.
    + induction H.
      * constructor.
      * constructor.
        apply (proj2 (outer_to_tiling_np_lt_iff a b)).
        exact H.
Qed.

Lemma Sorted_tiling_to_outer_ipl :
  forall ipl,
    Sorted Tiling.PL.np_lt ipl ->
    Sorted PolIRs.PolyLang.np_lt (List.map tiling_to_outer_ip ipl).
Proof.
  intros ipl Hsorted.
  induction Hsorted.
  - constructor.
  - simpl.
    constructor.
    + exact IHHsorted.
    + induction H.
      * constructor.
      * constructor.
        apply (proj2 (tiling_to_outer_np_lt_iff a b)).
        exact H.
Qed.

Lemma outer_to_tiling_flatten_instr_nth_iff :
  forall envv nth pi ipl,
    Tiling.PL.flatten_instr_nth envv nth (outer_to_tiling_pinstr pi)
      (outer_to_tiling_ipl ipl) <->
    PolIRs.PolyLang.flatten_instr_nth envv nth pi ipl.
Proof.
  intros envv nth pi ipl.
  split; intros Hflat.
  - destruct Hflat as [Henv [Hbel [Hnodup Hsorted]]].
    split.
    + intros ip Hin.
      change
        (firstn (Datatypes.length envv)
           (Tiling.PL.ILSema.ip_index (outer_to_tiling_ip ip)) = envv).
      apply Henv.
      apply in_map_iff.
      exists ip.
      split; [reflexivity|exact Hin].
    + split.
      * intros ip.
        specialize (Hbel (outer_to_tiling_ip ip)).
        destruct Hbel as [Hfwd Hbwd].
        split; intro Hin.
        -- assert (Hmap : In (outer_to_tiling_ip ip) (outer_to_tiling_ipl ipl)).
           { apply in_map_iff.
             exists ip.
             split; [reflexivity|exact Hin]. }
           specialize (Hfwd Hmap).
           destruct Hfwd as [Hpref [Hbel' [Hnth Hlen]]].
           split; [simpl in Hpref; exact Hpref|].
           split.
           { apply (proj1 (outer_to_tiling_belongs_to_iff ip pi)); exact Hbel'. }
           split; [simpl in Hnth; exact Hnth|].
           simpl in Hlen.
           exact Hlen.
        -- assert (Hmap_in : In (outer_to_tiling_ip ip) (outer_to_tiling_ipl ipl)).
           {
             apply Hbwd.
             destruct Hin as [Hpref [Hbel' [Hnth Hlen]]].
             split; [simpl; exact Hpref|].
             split.
             { apply (proj2 (outer_to_tiling_belongs_to_iff ip pi)); exact Hbel'. }
             split; [simpl; exact Hnth|].
             simpl.
             exact Hlen.
           }
           apply in_map_iff in Hmap_in.
           destruct Hmap_in as [ip' [Hip_eq Hin0]].
           destruct ip, ip'; simpl in Hip_eq; inversion Hip_eq; subst.
           exact Hin0.
      * split.
        -- pose proof (NoDup_tiling_to_outer_ipl _ Hnodup) as Hnodup0.
           now rewrite tiling_to_outer_ipl_outer_to_tiling in Hnodup0.
        -- pose proof (Sorted_tiling_to_outer_ipl _ Hsorted) as Hsorted0.
           now rewrite tiling_to_outer_ipl_outer_to_tiling in Hsorted0.
  - destruct Hflat as [Henv [Hbel [Hnodup Hsorted]]].
    split.
    + intros ip_t Hin.
      apply in_map_iff in Hin.
      destruct Hin as [ip [Hip_eq Hin0]].
      subst ip_t.
      pose proof (Henv _ Hin0) as Henv0.
      simpl in Henv0.
      exact Henv0.
    + split.
      * intros ip_t.
        split; intro Hin.
        -- apply in_map_iff in Hin.
           destruct Hin as [ip [Hip_eq Hin0]].
           subst ip_t.
           specialize (Hbel ip).
           destruct Hbel as [Hfwd _].
           destruct (Hfwd Hin0) as [Hpref [Hbel' [Hnth Hlen]]].
           split; [simpl in Hpref; exact Hpref|].
           split.
           { apply (proj2 (outer_to_tiling_belongs_to_iff ip pi)).
             exact Hbel'. }
           split; [simpl in Hnth; exact Hnth|].
           simpl in Hlen.
           exact Hlen.
        -- apply in_map_iff.
           exists
             {| PolIRs.PolyLang.ip_nth := Tiling.PL.ip_nth ip_t;
                PolIRs.PolyLang.ip_index := Tiling.PL.ip_index ip_t;
                PolIRs.PolyLang.ip_transformation := Tiling.PL.ip_transformation ip_t;
                PolIRs.PolyLang.ip_time_stamp := Tiling.PL.ip_time_stamp ip_t;
                PolIRs.PolyLang.ip_instruction := Tiling.PL.ip_instruction ip_t;
                PolIRs.PolyLang.ip_depth := Tiling.PL.ip_depth ip_t |}.
           split; [destruct ip_t; reflexivity|].
           specialize
             (Hbel
                {| PolIRs.PolyLang.ip_nth := Tiling.PL.ip_nth ip_t;
                   PolIRs.PolyLang.ip_index := Tiling.PL.ip_index ip_t;
                   PolIRs.PolyLang.ip_transformation := Tiling.PL.ip_transformation ip_t;
                   PolIRs.PolyLang.ip_time_stamp := Tiling.PL.ip_time_stamp ip_t;
                   PolIRs.PolyLang.ip_instruction := Tiling.PL.ip_instruction ip_t;
                   PolIRs.PolyLang.ip_depth := Tiling.PL.ip_depth ip_t |}).
           destruct Hbel as [_ Hbwd].
           apply Hbwd.
           destruct Hin as [Hpref [Hbel' [Hnth Hlen]]].
           split; [simpl; exact Hpref|].
           split.
           { apply (proj1 (outer_to_tiling_belongs_to_iff _ pi)).
             exact Hbel'. }
           split; [simpl; exact Hnth|].
           simpl.
           exact Hlen.
      * split.
        -- apply NoDup_outer_to_tiling_ipl; exact Hnodup.
        -- apply Sorted_outer_to_tiling_ipl; exact Hsorted.
Qed.

Lemma outer_to_tiling_flatten_instrs_iff :
  forall envv pis ipl,
    Tiling.PL.flatten_instrs envv (List.map outer_to_tiling_pinstr pis)
      (outer_to_tiling_ipl ipl) <->
    PolIRs.PolyLang.flatten_instrs envv pis ipl.
Proof.
  intros envv pis ipl.
  split; intros Hflat.
  - destruct Hflat as [Henv [Hbel [Hnodup Hsorted]]].
    split.
    + intros ip Hin.
      change
        (firstn (Datatypes.length envv)
           (Tiling.PL.ILSema.ip_index (outer_to_tiling_ip ip)) = envv).
      apply Henv.
      apply in_map_iff.
      exists ip.
      split; [reflexivity|exact Hin].
    + split.
      * intros ip.
        specialize (Hbel (outer_to_tiling_ip ip)).
        destruct Hbel as [Hfwd Hbwd].
        split; intro Hin.
        -- assert (Hmap : In (outer_to_tiling_ip ip) (outer_to_tiling_ipl ipl)).
           { apply in_map_iff.
             exists ip.
             split; [reflexivity|exact Hin]. }
           specialize (Hfwd Hmap).
           destruct Hfwd as [pi_t [Hnth [Hpref [Hbel' Hlen]]]].
           destruct (nth_error_map_inv _ _ outer_to_tiling_pinstr _ _ _ Hnth)
             as [pi [Hnth0 Hpi_t]].
           subst pi_t.
           exists pi.
           split; [exact Hnth0|].
           split; [exact Hpref|].
           split.
           { apply (proj1 (outer_to_tiling_belongs_to_iff ip pi)); exact Hbel'. }
           exact Hlen.
        -- assert (Hmap_in : In (outer_to_tiling_ip ip) (outer_to_tiling_ipl ipl)).
           {
             apply Hbwd.
             destruct Hin as [pi [Hnth [Hpref [Hbel' Hlen]]]].
             exists (outer_to_tiling_pinstr pi).
             split.
             { eapply nth_error_map. exact Hnth. }
             split; [exact Hpref|].
             split.
             { apply (proj2 (outer_to_tiling_belongs_to_iff ip pi)); exact Hbel'. }
             exact Hlen.
           }
           apply in_map_iff in Hmap_in.
           destruct Hmap_in as [ip' [Hip_eq Hin0]].
           destruct ip, ip'; simpl in Hip_eq; inversion Hip_eq; subst.
           exact Hin0.
      * split.
        -- pose proof (NoDup_tiling_to_outer_ipl _ Hnodup) as Hnodup0.
           now rewrite tiling_to_outer_ipl_outer_to_tiling in Hnodup0.
        -- pose proof (Sorted_tiling_to_outer_ipl _ Hsorted) as Hsorted0.
           now rewrite tiling_to_outer_ipl_outer_to_tiling in Hsorted0.
  - destruct Hflat as [Henv [Hbel [Hnodup Hsorted]]].
    split.
    + intros ip_t Hin.
      apply in_map_iff in Hin.
      destruct Hin as [ip [Hip_eq Hin0]].
      subst ip_t.
      pose proof (Henv _ Hin0) as Henv0.
      simpl in Henv0.
      exact Henv0.
    + split.
      * intros ip_t.
        split; intro Hin.
        -- apply in_map_iff in Hin.
           destruct Hin as [ip [Hip_eq Hin0]].
           subst ip_t.
           specialize (Hbel ip).
           destruct Hbel as [Hfwd _].
           destruct (Hfwd Hin0) as [pi [Hnth [Hpref [Hbel' Hlen]]]].
           exists (outer_to_tiling_pinstr pi).
           split.
           { eapply nth_error_map. exact Hnth. }
           split; [exact Hpref|].
           split.
           { apply (proj2 (outer_to_tiling_belongs_to_iff ip pi)); exact Hbel'. }
           exact Hlen.
        -- apply in_map_iff.
           destruct ip_t as [nth idx tf ts instr depth].
           exists
             {| PolIRs.PolyLang.ip_nth := nth;
                PolIRs.PolyLang.ip_index := idx;
                PolIRs.PolyLang.ip_transformation := tf;
                PolIRs.PolyLang.ip_time_stamp := ts;
                PolIRs.PolyLang.ip_instruction := instr;
                PolIRs.PolyLang.ip_depth := depth |}.
           split; [reflexivity|].
           specialize
             (Hbel
                {| PolIRs.PolyLang.ip_nth := nth;
                   PolIRs.PolyLang.ip_index := idx;
                   PolIRs.PolyLang.ip_transformation := tf;
                   PolIRs.PolyLang.ip_time_stamp := ts;
                   PolIRs.PolyLang.ip_instruction := instr;
                   PolIRs.PolyLang.ip_depth := depth |}).
           destruct Hbel as [_ Hbwd].
           apply Hbwd.
           destruct Hin as [pi_t [Hnth [Hpref [Hbel' Hlen]]]].
           destruct (nth_error_map_inv _ _ outer_to_tiling_pinstr _ _ _ Hnth)
             as [pi [Hnth0 Hpi_t]].
           subst pi_t.
           exists pi.
           split; [exact Hnth0|].
           split; [exact Hpref|].
           split.
           { apply (proj1 (outer_to_tiling_belongs_to_iff _ pi)); exact Hbel'. }
           exact Hlen.
      * split.
        -- apply NoDup_outer_to_tiling_ipl; exact Hnodup.
        -- apply Sorted_outer_to_tiling_ipl; exact Hsorted.
Qed.

Lemma outer_to_tiling_poly_instance_list_semantics_iff :
  forall envv pp st1 st2,
    Tiling.PL.poly_instance_list_semantics
      envv (outer_to_tiling_pprog pp) st1 st2 <->
    PolIRs.PolyLang.poly_instance_list_semantics envv pp st1 st2.
Proof.
  intros envv [[pis varctxt] vars] st1 st2.
  unfold outer_to_tiling_pprog.
  split; intro Hsem.
  - inversion Hsem as
      [envv' pprog pis' varctxt' vars' st1' st2' ipl sorted_ipl
         Hpprog Hflat Hperm Hsorted Hipl];
      subst envv' st1' st2'.
    simpl in Hpprog.
    inversion Hpprog; subst pprog pis' varctxt' vars'; clear Hpprog.
    econstructor.
    + reflexivity.
    + pose proof
        (proj1
           (outer_to_tiling_flatten_instrs_iff
              envv pis (tiling_to_outer_ipl ipl))) as Hflat0.
      rewrite outer_to_tiling_ipl_tiling_to_outer in Hflat0.
      apply Hflat0.
      exact Hflat.
    + apply Permutation_map.
      exact Hperm.
    + clear Hperm Hipl.
      induction Hsorted.
      * constructor.
      * simpl.
        constructor.
        -- exact IHHsorted.
        -- induction H.
           ++ constructor.
           ++ constructor.
              ** apply (proj1 (tiling_to_outer_instr_point_sched_le_iff a b)).
                 exact H.
    + pose proof
        (proj1
           (outer_to_tiling_instr_point_list_semantics_iff
              (tiling_to_outer_ipl sorted_ipl) st1 st2)) as Hipl0.
      rewrite outer_to_tiling_ipl_tiling_to_outer in Hipl0.
      apply Hipl0.
      exact Hipl.
  - inversion Hsem as
      [envv' pprog pis' varctxt' vars' st1' st2' ipl sorted_ipl
         Hpprog Hflat Hperm Hsorted Hipl];
      subst envv' st1' st2'.
    simpl in Hpprog.
    inversion Hpprog; subst pprog pis' varctxt' vars'; clear Hpprog.
    econstructor.
    + reflexivity.
    + apply (proj2 (outer_to_tiling_flatten_instrs_iff envv pis ipl)).
      exact Hflat.
    + eapply Permutation_sym.
      apply Permutation_map.
      eapply Permutation_sym.
      exact Hperm.
    + clear Hperm Hipl.
      induction Hsorted.
      * constructor.
      * simpl in *.
        constructor.
        -- exact IHHsorted.
        -- induction H.
           ++ constructor.
           ++ constructor.
              ** apply (proj2 (outer_to_tiling_instr_point_sched_le_iff a b)).
                 exact H.
    + pose proof
        (proj2
           (outer_to_tiling_instr_point_list_semantics_iff
              sorted_ipl st1 st2)) as Hipl0.
      apply Hipl0.
      exact Hipl.
Qed.

Lemma outer_to_tiling_instance_list_semantics_iff :
  forall pp st1 st2,
    Tiling.PL.instance_list_semantics (outer_to_tiling_pprog pp) st1 st2 <->
    PolIRs.PolyLang.instance_list_semantics pp st1 st2.
Proof.
  intros [[pis varctxt] vars] st1 st2.
  unfold outer_to_tiling_pprog.
  split; intro Hsem.
  - inversion Hsem as
      [pprog pis' varctxt' vars' envv st1' st2' Hpprog Hcompat Hnalias Hinit Hpoly];
      subst st1' st2'.
    simpl in Hpprog.
    inversion Hpprog; subst pprog pis' varctxt' vars'; clear Hpprog.
    constructor 1 with
      (pprog := (pis, varctxt, vars))
      (pis := pis)
      (varctxt := varctxt)
      (vars := vars)
      (envv := envv);
      try assumption.
    + reflexivity.
    + apply (proj1
               (outer_to_tiling_poly_instance_list_semantics_iff
                  envv ((pis, varctxt), vars) st1 st2)).
      exact Hpoly.
  - inversion Hsem as
      [pprog pis' varctxt' vars' envv st1' st2' Hpprog Hcompat Hnalias Hinit Hpoly];
      subst st1' st2'.
    simpl in Hpprog.
    inversion Hpprog; subst pprog pis' varctxt' vars'; clear Hpprog.
    constructor 1 with
      (pprog := (List.map outer_to_tiling_pinstr pis, varctxt, vars))
      (pis := List.map outer_to_tiling_pinstr pis)
      (varctxt := varctxt)
      (vars := vars)
      (envv := envv);
      try assumption.
    + reflexivity.
    + apply (proj2
               (outer_to_tiling_poly_instance_list_semantics_iff
                  envv ((pis, varctxt), vars) st1 st2)).
      exact Hpoly.
Qed.

Lemma tiling_to_outer_pprog_outer_to_tiling :
  forall pp,
    tiling_to_outer_pprog (outer_to_tiling_pprog pp) = pp.
Proof.
  intros [[pis varctxt] vars].
  unfold outer_to_tiling_pprog, tiling_to_outer_pprog.
  simpl.
  assert (Hmap :
    List.map tiling_to_outer_pinstr (List.map outer_to_tiling_pinstr pis) = pis).
  {
    induction pis as [|pi pis IH]; simpl.
    - reflexivity.
    - assert (tiling_to_outer_pinstr (outer_to_tiling_pinstr pi) = pi) as Hpi.
      { destruct pi; reflexivity. }
      rewrite Hpi, IH.
      reflexivity.
  }
  rewrite Hmap.
  reflexivity.
Qed.

Definition build_canonical_tiled_after_pinstr
    (env_size: nat)
    (before_pi: Tiling.PL.PolyInstr)
    (w: statement_tiling_witness) : Tiling.PL.PolyInstr :=
  let cw := Tiling.compiled_pinstr_tiling_witness w in
  {|
    Tiling.PL.pi_depth :=
      (Tiling.PL.pi_depth before_pi + List.length (stw_links w))%nat;
    Tiling.PL.pi_instr := Tiling.PL.pi_instr before_pi;
    Tiling.PL.pi_poly :=
      Tiling.ptw_link_domain cw ++
      Tiling.lifted_base_domain_after_env
        env_size cw (Tiling.PL.pi_poly before_pi);
    Tiling.PL.pi_schedule :=
      Tiling.lift_schedule_after_env
        (Tiling.ptw_added_dims cw) env_size
        (Tiling.PL.pi_schedule before_pi);
    Tiling.PL.pi_point_witness := PSWTiling w;
    Tiling.PL.pi_transformation := Tiling.PL.pi_transformation before_pi;
    Tiling.PL.pi_access_transformation :=
      Tiling.PL.pi_access_transformation before_pi;
    Tiling.PL.pi_waccess := Tiling.PL.pi_waccess before_pi;
    Tiling.PL.pi_raccess := Tiling.PL.pi_raccess before_pi;
  |}.

Definition build_canonical_tiled_after
    (before: Tiling.PL.t)
    (ws: list statement_tiling_witness) : Tiling.PL.t :=
  let '(before_pis, varctxt, vars) := before in
  (List.map
     (fun '(before_pi, w) =>
        build_canonical_tiled_after_pinstr
          (List.length varctxt) before_pi w)
     (List.combine before_pis ws),
   varctxt,
   vars).

Definition import_canonical_tiled_after
    (before: Tiling.PL.t)
    (after_scop: OpenScop)
    (ws: list statement_tiling_witness) : result Tiling.PL.t :=
  Tiling.PL.from_openscop_schedule_only
    (build_canonical_tiled_after before ws)
    after_scop.

Definition import_canonical_tiled_after_outer
    (before: PolIRs.PolyLang.t)
    (after_scop: OpenScop)
    (ws: list statement_tiling_witness) : result PolIRs.PolyLang.t :=
  match import_canonical_tiled_after (outer_to_tiling_pprog before) after_scop ws with
  | Okk after => Okk (tiling_to_outer_pprog after)
  | Err msg => Err msg
  end.

(** Public outer-PolyLang import API: build the canonical tiled skeleton from
    the input program and witness, then import the final Pluto after.scop
    schedule over that skeleton. *)
Definition import_canonical_tiled_after_poly := import_canonical_tiled_after_outer.

Lemma tiling_validate_correct :
  forall before_pis after_pis ws varctxt vars st1 st2,
    List.length before_pis = List.length after_pis ->
    List.length after_pis = List.length ws ->
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, varctxt, vars)
      (after_pis, varctxt, vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws) ->
    Forall
      (fun before_pi =>
         Tiling.PL.pi_point_witness before_pi =
         PSWIdentity (Tiling.PL.pi_depth before_pi))
      before_pis ->
    Forall
      (Tiling.wf_statement_tiling_witness_with_param_dim
         (List.length varctxt))
      ws ->
    Forall
      (fun w => Forall (fun link => (0 < tl_tile_size link)%Z) (stw_links w))
      ws ->
    Forall2
      (fun before_pi w => stw_point_dim w = Tiling.PL.pi_depth before_pi)
      before_pis ws ->
    mayReturn
      (GeneralValidator.validate_general
         (Tiling.retiled_old_pinstrs
            (List.length varctxt) before_pis after_pis ws,
          varctxt, vars)
         (after_pis, varctxt, vars))
      true ->
    Tiling.PL.instance_list_semantics
      (after_pis, varctxt, vars) st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics
        (before_pis, varctxt, vars) st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before_pis after_pis ws varctxt vars st1 st2
         Hlen_after Hlen_ws Htiling Hbefore_ids Hwf_ws Hsizes_ws Hdepths.
  intros Hval Hsem_after.
  pose proof
    (GeneralValidator.validate_tiling_correct
       (Tiling.retiled_old_pinstrs
          (List.length varctxt) before_pis after_pis ws,
        varctxt, vars)
       (after_pis, varctxt, vars)
       st1 st2 true Hval eq_refl Hsem_after)
    as Hchecked.
  destruct Hchecked as [st_mid [Hretiled Heq_mid]].
  destruct
    (Tiling.tiling_retiled_old_to_before_instance_correct_source
       before_pis after_pis ws varctxt vars st1 st_mid
       Htiling Hbefore_ids Hwf_ws Hsizes_ws Hdepths Hretiled)
    as [st2' [Hbefore Heq_before]].
  exists st2'.
  split.
  - exact Hbefore.
  - eapply TilingPolIRs.State.eq_trans.
    + exact Heq_mid.
    + exact Heq_before.
Qed.

Lemma tiling_checked_validate_correct :
  forall before after ws st1 st2,
    TilingCheck.check_pprog_tiling_sourceb before after ws = true ->
    mayReturn
      (let '(before_pis, varctxt, vars) := before in
       let '(after_pis, _, _) := after in
       GeneralValidator.validate_general
         (Tiling.retiled_old_pinstrs
            (List.length varctxt) before_pis after_pis ws,
          varctxt, vars)
         after)
      true ->
    Tiling.PL.instance_list_semantics after st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics before st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hcheck Hval Hsem_after.
  destruct before as [[before_pis varctxt] vars].
  destruct after as [[after_pis after_ctxt] after_vars].
  simpl in *.
  pose proof
    (TilingCheck.check_pprog_tiling_sourceb_sound
       (before_pis, varctxt, vars)
       (after_pis, after_ctxt, after_vars) ws Hcheck)
    as [Hprog [Hbefore_ids [Hwf [Hsizes Hdepths]]]].
  unfold Tiling.tiling_rel_pprog_structure_source in Hprog.
  simpl in Hprog.
  destruct Hprog as [Hctxt [Hvars Hrel]].
  subst after_ctxt after_vars.
  pose proof
    (Tiling.tiling_rel_pinstr_list_source_lengths
       (List.length varctxt) before_pis after_pis
       (List.map Tiling.compiled_pinstr_tiling_witness ws) Hrel)
    as [Hlen_after Hlen_ws_map].
  assert (Hlen_ws : List.length after_pis = List.length ws).
  {
    rewrite List.map_length in Hlen_ws_map.
    exact Hlen_ws_map.
  }
  assert (Hprog_full :
    Tiling.tiling_rel_pprog_structure_source
      (before_pis, varctxt, vars)
      (after_pis, varctxt, vars)
      (List.map Tiling.compiled_pinstr_tiling_witness ws)).
  {
    unfold Tiling.tiling_rel_pprog_structure_source.
    simpl.
    split; [reflexivity|].
    split; [reflexivity|].
    exact Hrel.
  }
  eapply tiling_validate_correct; eauto.
Qed.

Definition checked_tiling_validate
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp bool :=
  if TilingCheck.check_pprog_tiling_sourceb before after ws then
    let '(before_pis, varctxt, vars) := before in
    let '(after_pis, _, _) := after in
    GeneralValidator.validate_general
      (Tiling.retiled_old_pinstrs
         (List.length varctxt) before_pis after_pis ws,
       varctxt, vars)
      after
  else pure false.

Definition checked_tiling_validate_outer
    (before after: PolIRs.PolyLang.t)
    (ws: list statement_tiling_witness) : imp bool :=
  checked_tiling_validate
    (outer_to_tiling_pprog before)
    (outer_to_tiling_pprog after)
    ws.

(** Public checked tiling validator on the generic outer PolyLang type. *)
Definition checked_tiling_validate_poly := checked_tiling_validate_outer.

Lemma checked_tiling_validate_correct :
  forall before after ws st1 st2,
    mayReturn (checked_tiling_validate before after ws) true ->
    Tiling.PL.instance_list_semantics after st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics before st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hcheck Hsem_after.
  unfold checked_tiling_validate in Hcheck.
  destruct (TilingCheck.check_pprog_tiling_sourceb before after ws) eqn:Hstruct.
  - eapply tiling_checked_validate_correct; eauto.
  - eapply mayReturn_pure in Hcheck. discriminate.
Qed.

Lemma checked_tiling_validate_outer_correct :
  forall before after ws st1 st2,
    mayReturn (checked_tiling_validate_outer before after ws) true ->
    PolIRs.PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolIRs.PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 Hcheck Hsem_after.
  unfold checked_tiling_validate_outer in Hcheck.
  pose proof
    (proj2 (outer_to_tiling_instance_list_semantics_iff after st1 st2) Hsem_after)
    as Hsem_after_t.
  pose proof
    (checked_tiling_validate_correct
       (outer_to_tiling_pprog before)
       (outer_to_tiling_pprog after)
       ws st1 st2 Hcheck Hsem_after_t)
    as Hcorr.
  destruct Hcorr as [st2' [Hbefore_t Heq]].
  exists st2'.
  split.
  - apply (proj1 (outer_to_tiling_instance_list_semantics_iff before st1 st2')).
    exact Hbefore_t.
  - exact Heq.
Qed.

Lemma checked_tiling_validate_poly_correct :
  forall before after ws st1 st2,
    mayReturn (checked_tiling_validate_poly before after ws) true ->
    PolIRs.PolyLang.instance_list_semantics after st1 st2 ->
    exists st2',
      PolIRs.PolyLang.instance_list_semantics before st1 st2' /\
      State.eq st2 st2'.
Proof.
  exact checked_tiling_validate_outer_correct.
Qed.

Lemma checked_tiling_validate_implies_wf_after :
  forall before after ws,
    mayReturn (checked_tiling_validate before after ws) true ->
    Tiling.PL.wf_pprog_general after.
Proof.
  intros before after ws Hcheck.
  unfold checked_tiling_validate in Hcheck.
  destruct (TilingCheck.check_pprog_tiling_sourceb before after ws) eqn:Hstruct.
  2: {
    eapply mayReturn_pure in Hcheck.
    discriminate.
  }
  destruct before as ((before_pis, varctxt), vars).
  destruct after as ((after_pis, after_ctxt), after_vars).
  simpl in *.
  unfold GeneralValidator.validate_general, TilingVal.validate_tiling in Hcheck.
  bind_imp_destruct Hcheck wf1 Hwf1.
  bind_imp_destruct Hcheck wf2 Hwf2.
  bind_imp_destruct Hcheck eqdom Heqdom.
  bind_imp_destruct Hcheck res Hres.
  eapply mayReturn_pure in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [[[[Hwf1_true Hwf2_true] _] _] _].
  pose proof
    (TilingVal.check_wf_polyprog_tiling_correct
       (after_pis, after_ctxt, after_vars) wf2 Hwf2 Hwf2_true)
    as Hwf_after.
  exact Hwf_after.
Qed.

Lemma checked_tiling_validate_outer_implies_wf_after :
  forall before after ws,
    mayReturn (checked_tiling_validate_outer before after ws) true ->
    PolIRs.PolyLang.wf_pprog_general after.
Proof.
  intros before after ws Hcheck.
  unfold checked_tiling_validate_outer in Hcheck.
  pose proof
    (checked_tiling_validate_implies_wf_after
       (outer_to_tiling_pprog before)
       (outer_to_tiling_pprog after)
       ws Hcheck)
    as Hwf_t.
  pose proof
    (tiling_to_outer_wf_pprog_general
       (outer_to_tiling_pprog after) Hwf_t)
    as Hwf_outer.
  rewrite tiling_to_outer_pprog_outer_to_tiling in Hwf_outer.
  exact Hwf_outer.
Qed.

Lemma checked_tiling_validate_poly_implies_wf_after :
  forall before after ws,
    mayReturn (checked_tiling_validate_poly before after ws) true ->
    PolIRs.PolyLang.wf_pprog_general after.
Proof.
  exact checked_tiling_validate_outer_implies_wf_after.
Qed.

Definition checked_tiling_prepared_codegen
    (before after: Tiling.PL.t)
    (ws: list statement_tiling_witness) : imp TilingPolIRs.Loop.t :=
  BIND ok <- checked_tiling_validate before after ws -;
  if ok then
    TPrepare.prepared_codegen (Tiling.PL.current_view_pprog after)
  else
    res_to_alarm TilingPolIRs.Loop.dummy (Err "Tiling validation failed.").

Lemma checked_tiling_prepared_codegen_correct :
  forall before after ws st1 st2,
    forall loop,
    mayReturn
      (checked_tiling_prepared_codegen before after ws)
      loop ->
    TilingPolIRs.Loop.semantics loop st1 st2 ->
    exists st2',
      Tiling.PL.instance_list_semantics before st1 st2' /\
      TilingPolIRs.State.eq st2 st2'.
Proof.
  intros before after ws st1 st2 loop Hcodegen Hloop.
  unfold checked_tiling_prepared_codegen in Hcodegen.
  bind_imp_destruct Hcodegen ok Hchecked.
  destruct ok.
  2: {
    eapply mayReturn_alarm in Hcodegen.
    contradiction.
  }
  pose proof
    (checked_tiling_validate_implies_wf_after
       before after ws Hchecked)
    as Hwf_after.
  pose proof
    (TPrepare.prepared_codegen_correct_general
       after st1 st2 loop Hcodegen Hwf_after Hloop)
    as Hsem_after.
  eapply checked_tiling_validate_correct; eauto.
Qed.

End TilingValidator.
