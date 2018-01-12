From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export lang lang_erased.
From iris.algebra Require Export ofe.
From stdpp Require Import gmap.

Record Proph_equiv  p p' :=
  { PrA_eq : PrA p = PrA p';
    PrP_eq :  match PrA_eq in _ = z return z → Stream expr with
                eq_refl => PrP p end = PrP p' }.

Lemma Proph_equiv_refl p : Proph_equiv p p.
Proof.
  unshelve econstructor; eauto.
Qed.

Definition have_same_proph
           (σ : language.state P_lang) (σ' : language.state PE_lang)
  := σ.1 = σ'.1 ∧ dom (gset loc) σ.2 = dom (gset loc) σ'.2 ∧
     ∀ x, x ∈ dom (gset loc) σ.2 →
          ∃ v v', Proph_equiv v v' ∧
                  σ.2 !! x = Some v ∧ σ'.2 !! x = Some v'.

Lemma have_same_proph_refl σ : have_same_proph σ σ.
Proof.
  destruct σ as [h p].
  repeat split; simpl; auto.
  intros x [v Hv]%elem_of_dom.
  exists v, v; repeat split; auto using Proph_equiv_refl.
Qed.

Program Definition Proph_go_back p p' z w
           (H : Proph_equiv p (Proph_tail p'))
           (H' : to_val (Shead (PrP p' z)) = Some w)
  :=
{|PrS := {|Shead := w; Stail := PrS p |};
  PrA := PrA p'; PrP := PrP p'; PrP_ent := PrP_ent p'; PrPvals := PrPvals p' |}.
Next Obligation.
Proof.
  intros p p' z w Pe Pt.
  destruct p as [pS pA pP pPv pP_ent pPSI].
  destruct p' as [p'S p'A p'P p'Pv p'P_ent p'PSI].
  simpl in *.
  destruct Pe as [Pe1 Pe2]; simpl in *. destruct Pe1; subst.
  destruct pPSI as [u Hu].
  destruct (p'Pv u) as [y Hy].
  destruct (p'Pv z) as [q Hq].
  destruct (p'P_ent 0 q y) as [x Hx]; auto.
  rewrite Hq; by eexists.
  rewrite Hy; by eexists.
  exists x. rewrite Hx; simpl.
  destruct y as [yh yt]; simpl in *.
  rewrite -Hy in Hu; simpl in *.
  apply proph_to_expr_inj in Hu; subst.
  destruct q as [qh qt]; simpl in *.
  rewrite -Hq in Pt; simpl in *.
  rewrite to_of_val in Pt.
  by inversion Pt; subst.
Qed.

Lemma Proph_tail_Proph_go_back p p' z w Heq Heq' :
  Proph_tail (Proph_go_back p p' z w Heq Heq') = p.
Proof.
  destruct p as [pS pA pP pPv pPe pPSI].
  destruct p' as [p'S p'A p'P p'Pv p'Pe p'PSI].
  destruct Heq as [Heq1 Heq2].
  simpl in *.
  destruct Heq1.
  match goal with
    |- ?A = ?B =>
            eapply (Prohp_eq_simplify A B eq_refl)
  end; auto.
Qed.

Lemma erased_reachable_reachable th1 h1 th2 σ2:
  rtc (@step PE_lang) (th1, (h1, ∅)) (th2, σ2) →
  ∀ σ2', have_same_proph σ2' σ2 → rtc (@step P_lang) (th1, (h1, ∅)) (th2, σ2').
Proof.
  remember (th1, (h1, ∅)) as cfg.
  remember (th2, σ2) as cfg'.
  rewrite {2}Heqcfg.
  intros Hrtc.
  revert th1 h1 th2 σ2 Heqcfg Heqcfg'.
  eapply (rtc_ind_r_weak (λ z z', ∀ (th1 : list (language.expr PE_lang)) (h1 : gmap loc val)
                                    (th2 : list (language.expr PE_lang))
                                    (σ2 : language.state PE_lang),
                             z = (th1, (h1, ∅))
                             → z' = (th2, σ2) →
                             ∀ σ2' : language.state P_lang,
                               have_same_proph σ2' σ2 →
                               rtc (@step P_lang) (th1, (h1, ∅)) (th2, σ2')));
  last eauto.
  - intros x th1 h1 th2 σ2 Heqcfg Heqcfg'; simplify_eq.
    intros [σ2 σ2p] [Hh [Hsp _]]; simpl in *.
    rewrite dom_empty_L in Hsp. apply dom_empty_inv_L in Hsp. rewrite Hsp.
    rewrite Hh.  econstructor.
  - intros x y z Hxy Hyz IH th1 h1 th2 σ2 Heqcfg Heqcfg' σ2' Hsp;
      simplify_eq; simpl in *.
    destruct y as [yh yp].
    inversion Hyz as [? ? ? ? ? ? ? ? ? Hpr]; simplify_eq.
    inversion Hpr as [? ? ? ? ? Hestp]; simpl in *; simplify_eq.
    inversion Hestp; simplify_eq;
      try (eapply rtc_r; first (by eapply IH; eauto); by repeat (econstructor; eauto)).
    all: destruct σ2' as [σ2'h σ2'p]; destruct Hsp as [Hsp1 Hsp2]; simpl in *; simplify_eq.
    + eapply (rtc_r _ (_ ++ fill K (Alloc _) :: _, (σ, σ2'p)));
        [unshelve eapply (IH _ _ _ (_, σp) _ _ (σ, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + match goal with A : ?X.1 !! _ = _ |- _ => destruct X as [σmh σmp]; simpl in * end.
      eapply (rtc_r _ (_ ++ fill K (Load (Loc _)) :: _, (_, σ2'p)));
        [unshelve eapply (IH _ _ _ (σmh, σmp) _ _ (_, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + eapply (rtc_r _ (_ ++ fill K (Store (Loc _) _) :: _, (_, σ2'p)));
        [unshelve eapply (IH _ _ _ (_, σp) _ _ (_, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + match goal with A : ?X.1 !! _ = _ |- _ => destruct X as [σmh σmp]; simpl in * end.
      eapply (rtc_r _ (_ ++ fill K (CAS (Loc _) _ _) :: _, (_, σ2'p)));
        [unshelve eapply (IH _ _ _ (_, σmp) _ _ (_, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + eapply (rtc_r _ (_ ++ fill K (CAS (Loc _) _ _) :: _, (_, σ2'p)));
        [unshelve eapply (IH _ _ _ (_, σp) _ _ (_, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + destruct Hsp2 as [Hsp21 Hsp22].
      assert (dom (gset loc) (delete (fresh (dom (gset loc) σp)) σ2'p)
                = dom (gset loc) σp) as Hfr.
      { rewrite dom_delete_L Hsp21 dom_insert_L difference_union_distr_l_L
                  difference_diag_L left_id_L difference_disjoint_L //=.
          apply disjoint_singleton_r, is_fresh. }
      eapply (rtc_r _ (_ ++ fill K (Create_Pr A P) :: _, (σ, delete (fresh (dom (gset loc) σp)) σ2'p)));
        [unshelve eapply (IH _ _ _ (σ, σp) _ _ (_, _)); eauto; simpl; eauto|
         repeat (econstructor; eauto)].
      * repeat split; auto; simpl.
        intros x Hx. rewrite dom_delete_L in Hx.
        apply elem_of_difference in Hx; destruct Hx as [Hx1 Hx2].
        edestruct Hsp22 as (v1 & v2 & Hvv & Hv1 & Hv2); eauto.
        apply not_elem_of_singleton in Hx2.
        exists v1, v2; split; auto. split.
        ++ rewrite lookup_delete_ne; auto.
        ++ rewrite lookup_insert_ne in Hv2; auto.
      * destruct (elem_of_dom (D := gset loc) σ2'p (fresh (dom (gset loc) σp))) as [[p Hp]].
        { rewrite Hsp21 dom_insert.  by apply elem_of_union_l, elem_of_singleton. }
        simpl.
        replace σ2'p with (<[fresh (dom (gset loc) (delete (fresh (dom (gset loc) σp)) σ2'p)) := p]> (delete (fresh (dom (gset loc) σp)) σ2'p)) at 2; last first.
        { rewrite Hfr. by rewrite insert_delete insert_id. }
        rewrite -{2}Hfr.
        destruct p as [str sA sP sSI].
        destruct (Hsp22 (fresh (dom (gset loc) σp))) as (v1 & v2 & Hvv & Hv1 & Hv2); eauto.
        rewrite lookup_insert in Hv2. rewrite Hp in Hv1.
        inversion Hv1; inversion Hv2; simplify_eq.
        destruct Hvv as [Hvv1 Hvv2]; simpl in *.
        destruct Hvv1; simplify_eq.
        apply Create_PrS.
    + destruct Hsp2 as [Hsp21 Hsp22].
      assert (∃ str, σ2'p !! l = Some str) as [str Hstr].
      { apply (elem_of_dom (D := gset loc)).
        rewrite Hsp21 dom_insert. by apply elem_of_union_l, elem_of_singleton. }
      destruct (Hsp22 l) as (v1 & v2 & Hvv & Hv1 & Hv2); first apply elem_of_dom; eauto.
      rewrite Hv1 in Hstr; inversion Hstr; subst; clear Hstr.
      rewrite lookup_insert in Hv2; inversion Hv2; subst; clear Hv2.
      eapply (rtc_r _ (_ ++ fill K (Assign_Pr (Pr _) _) :: _,
                       (_, <[l:= (Proph_go_back _ _ _ _ Hvv H0)]> σ2'p)));
        [unshelve eapply (IH _ _ _ (_, σp) _ _ (_, _)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
      * assert (dom (gset loc) (<[l:=p]> σ2'p) = dom (gset loc) σ2'p) as Hσ2'p.
        { rewrite dom_insert_L Hsp21 dom_insert_L assoc_L idemp_L.
           rewrite subseteq_union_1_L //.
           apply elem_of_subseteq_singleton, elem_of_dom; eauto. }
        split; auto.
        ++ rewrite dom_insert_L Hsp21 dom_insert_L assoc_L idemp_L.
           rewrite subseteq_union_1_L //.
           apply elem_of_subseteq_singleton, elem_of_dom; eauto.
        ++ intros x. rewrite dom_insert_L. rewrite dom_insert_L in Hσ2'p.
           rewrite Hσ2'p. intros Hx.
           destruct (Hsp22 _ Hx) as (w1 & w2 & Hww & Hw1 & Hw2).
           destruct (decide (x = l)); subst.
           -- eexists (Proph_go_back str p _ _ Hvv H0), p; repeat split; auto;
                last by rewrite lookup_insert.
              unshelve econstructor; auto.
           -- exists w1, w2; repeat split; auto; rewrite -?Hw2 lookup_insert_ne //.
      * replace σ2'p with (<[l:= (Proph_tail (Proph_go_back str p _ _ Hvv H0))]>(<[l:= Proph_go_back str p _ _ Hvv H0]> σ2'p)) at 2; last first.
        { apply map_eq => i. destruct (decide (i = l)); subst.
          - rewrite lookup_insert Hv1. f_equal.
            apply Proph_tail_Proph_go_back.
          - do 2 rewrite lookup_insert_ne //=. }
        econstructor; eauto.
        by rewrite lookup_insert.
Qed.

Definition safe e :=
  ∀ th2 σ2,
    rtc (@step P_lang) ([e], (∅, ∅)) (th2, σ2) →
    ∀ e, e ∈ th2 → AsVal e ∨ reducible e σ2.

Definition erased_safe e :=
  ∀ th2 σ2,
    rtc (@step PE_lang) ([e], (∅, ∅)) (th2, σ2) →
    ∀ e, e ∈ th2 → AsVal e ∨ reducible e σ2.

Lemma reducible_erase_reducible e σ :
  @language.reducible P_lang e σ →
  @language.reducible PE_lang e σ.
Proof.
  intros (e'&σ2&efs&Hrd); simpl in *.
  inversion Hrd as [K e1' e2' ? ? Hhrd]; simpl in *; subst.
  destruct σ as [σh σp]; simpl in *; simplify_eq.
  inversion Hhrd; subst;
    try (solve [unshelve (repeat econstructor; eauto)]).
  + match goal with A : is_Some _ |- _ => destruct A as [? ?] end.
    repeat econstructor; eauto.
  + do 3 eexists. econstructor; eauto. unshelve econstructor; eauto.
  + destruct (PrSI p) as [x Hx].
    do 3 eexists. econstructor; eauto. econstructor; eauto.
    by apply of_to_val in H6; rewrite -H6.
Qed.

Lemma soundness_prophecies e :
  safe e → erased_safe e.
Proof.
  intros Hs th2 σ2 Hrtc re Hre.
  assert (rtc step ([e], (∅, ∅)) (th2, σ2)) as Hrtc'.
  { eapply erased_reachable_reachable;
      eauto using have_same_proph_refl. }
  edestruct Hs as [?|Hred]; eauto.
  right. by eapply reducible_erase_reducible.
Qed.
