From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export lang lang_erased.
From iris.algebra Require Export ofe.
From stdpp Require Import gmap.

Definition have_same_proph
           (σ : language.state P_lang) (σ' : language.state PE_lang)
  := σ.1 = σ'.1 ∧ dom (gset loc) σ.2 = σ'.2.

Definition conjure_prophecies (σ : language.state PE_lang) :
  language.state P_lang :=
  match σ with
    (σh, σp) => (σh,  to_gmap (Sconst UnitV) σp)
  end.

Lemma conjure_prophecies_have_same_proph σ :
  have_same_proph (conjure_prophecies σ) σ.
Proof.
  destruct σ; split; first done; simpl.
  apply mapset.mapset_eq => x; split => Hx.
  - destruct (decide (x ∈ m)); first done.
    apply elem_of_dom in Hx. destruct Hx as [y Hy].
    rewrite lookup_to_gmap option_guard_False //= in Hy.
  - apply elem_of_dom. rewrite lookup_to_gmap option_guard_True; eauto.
Qed.

Lemma erased_reachable_reachable th1 h1 th2 σ2:
  rtc (@step PE_lang) (th1, (h1, ∅)) (th2, σ2) →
  ∀ σ2', have_same_proph σ2' σ2 →
         rtc (@step P_lang) (th1, (h1, ∅)) (th2, σ2').
Proof.
  remember (th1, (h1, ∅)) as cfg.
  remember (th2, σ2) as cfg'.
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
    intros [σ2 σ2p] [Hh Hsp]; simpl in *.
    rewrite Hh. rewrite (dom_empty_inv_L (D := gset loc) σ2p); last done.
    econstructor.
  - intros x y z Hxy Hyz IH th1 h1 th2 σ2 Heqcfg Heqcfg' σ2' Hsp;
      simplify_eq; simpl in *.
    destruct y as [yh yp].
    inversion Hyz as [? ? ? ? ? ? ? ? ? Hpr]; simplify_eq.
    inversion Hpr as [? ? ? ? ? Hestp]; simpl in *; simplify_eq.
    inversion Hestp; simplify_eq;
      try (eapply rtc_r; first (by eapply IH; eauto); by repeat (econstructor; eauto)).
    all: destruct σ2' as [σ2'h σ2'p]; destruct Hsp as [Hsp1 Hsp2]; simpl in *; simplify_eq.
    + eapply (rtc_r _ (_ ++ fill K (Alloc _) :: _, (σ, σ2'p)));
        [unshelve eapply (IH _ _ _ (_, _) _ _ (σ, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + match goal with A : ?X.1 !! _ = _ |- _ => destruct X as [σmh σmp]; simpl in * end.
      eapply (rtc_r _ (_ ++ fill K (Load (Loc _)) :: _, (_, σ2'p)));
        [unshelve eapply (IH _ _ _ (σmh, σmp) _ _ (_, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + eapply (rtc_r _ (_ ++ fill K (Store (Loc _) _) :: _, (_, σ2'p)));
        [unshelve eapply (IH _ _ _ (_, _) _ _ (_, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + match goal with A : ?X.1 !! _ = _ |- _ => destruct X as [σmh σmp]; simpl in * end.
      eapply (rtc_r _ (_ ++ fill K (CAS (Loc _) _ _) :: _, (_, σ2'p)));
        [unshelve eapply (IH _ _ _ (_, _) _ _ (_, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + eapply (rtc_r _ (_ ++ fill K (CAS (Loc _) _ _) :: _, (_, σ2'p)));
        [unshelve eapply (IH _ _ _ (_, _) _ _ (_, σ2'p)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
    + assert (({[fresh σp]} ∪ σp) ∖ {[fresh σp]} = σp) as Hfr.
      { rewrite difference_union_distr_l_L difference_diag_L left_id_L.
        apply difference_disjoint_L.
        symmetry. apply disjoint_singleton_l, is_fresh. }
      eapply (rtc_r _ (_ ++ fill K (Create_Pr) :: _, (_, delete (fresh σp) σ2'p)));
        [unshelve eapply (IH _ _ _ (_, _) _ _ (_, _)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
      * by rewrite (dom_delete_L (D := gset loc)) Hsp2 Hfr.
      * destruct (elem_of_dom (D := gset loc) σ2'p (fresh σp)) as [[str Hstr]].
        { rewrite Hsp2. by apply elem_of_union_l, elem_of_singleton. }
        replace σ2'p with (<[fresh (dom (gset loc) (delete (fresh σp) σ2'p)) := str]> (delete (fresh σp) σ2'p)) at 2; last first.
        { rewrite dom_delete_L Hsp2 Hfr insert_delete. by apply insert_id. }
        rewrite -{2}Hfr -Hsp2 -dom_delete_L.
        econstructor.
    + assert (∃ str, σ2'p !! l = Some str) as [str Hstr]
          by by apply (elem_of_dom (D := gset loc)).
      eapply (rtc_r _ (_ ++ fill K (Assign_Pr (Pr _) _) :: _,
                       (_, <[l:={| Shead := v; Stail := str|}]> σ2'p)));
        [unshelve eapply (IH _ _ _ (_, _) _ _ (_, _)); eauto; split; simpl; eauto|
         repeat (econstructor; eauto)].
      * rewrite dom_insert_L. by apply subseteq_union_1_L, elem_of_subseteq_singleton.
      * replace σ2'p with (<[l:= Stail {| Shead := v; Stail := str |}]>(<[l:={| Shead := v; Stail := str |}]> σ2'p)) at 2; last first.
        { rewrite /= insert_insert. by apply insert_id. }
        econstructor; auto.
        rewrite lookup_insert //.
Qed.

Definition safe e :=
  ∀ th2 σ2,
    rtc (@step P_lang) ([e], (∅, ∅)) (th2, σ2) →
    ∀ e, e ∈ th2 → AsVal e ∨ reducible e σ2.

Definition erased_safe e :=
  ∀ th2 σ2,
    rtc (@step PE_lang) ([e], (∅, ∅)) (th2, σ2) →
    ∀ e, e ∈ th2 → AsVal e ∨ reducible e σ2.

Lemma reducible_erase_reducible e σ σ' :
  have_same_proph σ σ' →
  reducible e σ →
  @language.reducible PE_lang e σ'.
Proof.
  intros Hsp (e'&σ2&efs&Hrd); simpl in *.
  inversion Hrd as [K e1' e2' ? ? Hhrd]; simpl in *; subst.
  destruct σ as [σh σp]; destruct σ' as [σ'h σ'p];
    destruct Hsp as [? ?]; simpl in *; simplify_eq.
  inversion Hhrd; subst; try (unshelve (repeat econstructor; eauto); fail).
  + match goal with A : is_Some _ |- _ => destruct A as [? ?] end.
    repeat econstructor; eauto.
  + repeat econstructor; eauto.
    apply elem_of_dom; eauto.
  + repeat econstructor; eauto.
    apply elem_of_dom; eauto.
  + by unshelve (repeat econstructor).
Qed.

Lemma soundness_prophecies e :
  safe e → erased_safe e.
Proof.
  intros Hs th2 σ2 Hrtc re Hre.
  assert (rtc step ([e], (∅, ∅)) (th2, conjure_prophecies σ2)) as Hrtc'.
  { eapply erased_reachable_reachable;
      eauto using conjure_prophecies_have_same_proph. }
  edestruct Hs as [?|Hred]; eauto.
  right. eapply reducible_erase_reducible;
           eauto using conjure_prophecies_have_same_proph.
Qed.