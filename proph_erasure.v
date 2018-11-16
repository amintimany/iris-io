From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export lang lang_proph_erased.
From stdpp Require Import gmap.

Definition have_same_proph
           (σ : language.state P_lang) (σ' : language.state PE_lang)
  := (Heap σ) = (EHeap σ') ∧ dom (gset loc) (Proph σ) = (EProph σ') ∧
     (ioState σ) = (EioState σ').

Definition conjure_prophecies (σ : language.state PE_lang) :
  language.state P_lang :=
  {| Heap := EHeap σ; Proph := to_gmap (Sconst UnitV) (EProph σ);
     ioState := EioState σ |}.

Lemma conjure_prophecies_have_same_proph σ :
  have_same_proph (conjure_prophecies σ) σ.
Proof.
  destruct σ as [h p i]; split; first done; simpl.
  split; last done.
  apply mapset.mapset_eq => x; split => Hx.
  - destruct (decide (x ∈ p)); first done.
    apply elem_of_dom in Hx. destruct Hx as [y Hy].
    rewrite lookup_to_gmap option_guard_False //= in Hy.
  - apply elem_of_dom. rewrite lookup_to_gmap option_guard_True; eauto.
Qed.

Definition erased_safe_tp tp M :=
  ∀ th2 σ2,
    rtc (@step PE_lang) (tp, {| EHeap := ∅; EProph := ∅; EioState := M |})
        (th2, σ2) →
    ∀ e, e ∈ th2 → AsVal e ∨ reducible e σ2.

Lemma erased_reachable_reachable th1 h1 th2 σ2 M:
  rtc (@step PE_lang) (th1, {| EHeap := h1; EProph := ∅; EioState := M |})
(th2, σ2) →
  ∀ σ2', have_same_proph σ2' σ2 →
         rtc (@step P_lang)
             (th1, {| Heap := h1; Proph := ∅; ioState := M |})
             (th2, σ2').
Proof.
  remember (th1, {| EHeap := h1; EProph := ∅; EioState := M |}) as cfg.
  remember (th2, σ2) as cfg'.
  intros Hrtc.
  revert th1 h1 th2 σ2 Heqcfg Heqcfg'.
  eapply (rtc_ind_r_weak (λ z z', ∀ (th1 : list (language.expr PE_lang)) (h1 : gmap loc val)
                                    (th2 : list (language.expr PE_lang))
                                    (σ2 : language.state PE_lang),
                             z = (th1, {| EHeap := h1; EProph := ∅; EioState := M |})
                             → z' = (th2, σ2) →
                             ∀ σ2' : language.state P_lang,
                               have_same_proph σ2' σ2 →
                               rtc (@step P_lang)
                                   (th1, {| Heap := h1; Proph := ∅;
                                            ioState := M |}) (th2, σ2')));
  last eauto.
  - intros x th1 h1 th2 σ2 Heqcfg Heqcfg'; simplify_eq.
    intros [σ2 σ2p σ2i] [Hh [Hsp Hi]]; simpl in *; simplify_eq.
    rewrite (dom_empty_inv_L (D := gset loc) σ2p); last done.
    econstructor.
  - intros x y z Hxy Hyz IH th1 h1 th2 σ2 Heqcfg Heqcfg' σ2' Hsp;
      simplify_eq; simpl in *.
    destruct y as [yh yp].
    inversion Hyz as [? ? ? ? ? ? ? ? ? Hpr]; simplify_eq.
    inversion Hpr as [? ? ? ? ? Hestp]; simpl in *; simplify_eq.
    inversion Hestp; simplify_eq;
      try (eapply rtc_r; first (by eapply IH; eauto);
             by repeat (econstructor; eauto)).
    all: destruct σ2' as [σ2'h σ2'p σ2'i]; destruct Hsp as [Hsp1 [Hsp2 Hi]];
      simpl in *; simplify_eq;
    repeat match goal with
      | H : is_Some _ |- _ => destruct H
           end;
    try (by (eapply (rtc_r _ (_ ++ fill K _ :: _, {| Proph := σ2'p; |}));
             [eapply IH; by eauto |repeat econstructor; eauto])).
    + assert (({[fresh (EProph σ1)]} ∪ (EProph σ1)) ∖ {[fresh (EProph σ1)]} =
              (EProph σ1)) as Hfr.
      { rewrite difference_union_distr_l_L difference_diag_L left_id_L.
        apply difference_disjoint_L.
        symmetry. apply disjoint_singleton_l, is_fresh. }
      eapply (rtc_r _ (_ ++ fill K (Create_Pr) :: _,
                       {|Proph := delete (fresh (EProph σ1)) σ2'p |})).
      * eapply IH; eauto.
        repeat split; eauto.
          by rewrite (dom_delete_L (D := gset loc)) Hsp2 Hfr.
      * destruct (elem_of_dom (D := gset loc) σ2'p (fresh (EProph σ1)))
          as [[str Hstr]].
        { rewrite Hsp2. by apply elem_of_union_l, elem_of_singleton. }
        replace σ2'p with
            (<[fresh (dom (gset loc) (delete (fresh (EProph σ1)) σ2'p))
               := str]> (delete (fresh (EProph σ1)) σ2'p)) at 2; last first.
        { rewrite dom_delete_L Hsp2 Hfr insert_delete. by apply insert_id. }
        rewrite -{2}Hfr -Hsp2 -dom_delete_L.
        repeat econstructor; eauto.
    + assert ((∃ l, v = PrV l) ∨ (∀ l, v ≠ PrV l)) as Hl.
      { destruct v; eauto. }
      destruct Hl as [[l Hl]|Hl].
      * destruct (σ2'p !! l) as [str|] eqn:Hstr.
        -- eapply (rtc_r _ (_ ++ fill K (Assign_Pr _ _) :: _,
                            {| Proph := <[l:={| Shead := v'; Stail := str|}]> σ2'p|})).
           ++ eapply IH; eauto.
           repeat split; simpl; eauto.
           rewrite dom_insert_L.
           rewrite subseteq_union_1_L; first by auto.
             by apply elem_of_subseteq_singleton; eapply elem_of_dom_2.
           ++ replace σ2'p with
                  (<[l:= Stail {| Shead := v'; Stail := str |}]>
                   (<[l:={| Shead := v'; Stail := str |}]> σ2'p)) at 2; last first.
              { rewrite /= insert_insert. by apply insert_id. }
              apply of_to_val in H; subst.
              repeat econstructor; simpl; auto.
              rewrite lookup_insert //.
        -- eapply (rtc_r _ (_ ++ fill K (Assign_Pr _ _) :: _,
                            {| Heap := EHeap σ0; Proph := σ2'p; ioState := EioState σ0 |})).
           ++ eapply IH; eauto; repeat split; simpl; eauto.
           ++ repeat econstructor; simpl; eauto.
              by intros ? ?; simplify_eq.
      * eapply (rtc_r _ (_ ++ fill K (Assign_Pr _ _) :: _,
                            {| Proph := σ2'p|})).
           ++ eapply IH; eauto.
           repeat split; simpl; eauto.
           ++ repeat econstructor; eauto.
              by intros ? ?%Hl.
Qed.

Definition safe e M :=
  ∀ th2 σ2,
    rtc (@step P_lang) ([e], {| Heap := ∅; Proph := ∅; ioState := M |})
        (th2, σ2) →
    ∀ e, e ∈ th2 → AsVal e ∨ reducible e σ2.

Definition erased_safe e M :=
  ∀ th2 σ2,
    rtc (@step PE_lang) ([e], {| EHeap := ∅; EProph := ∅; EioState := M |})
        (th2, σ2) →
    ∀ e, e ∈ th2 → AsVal e ∨ reducible e σ2.

Lemma reducible_erase_reducible e σ σ' :
  have_same_proph σ σ' →
  reducible e σ →
  @language.reducible PE_lang e σ'.
Proof.
  intros Hsp (e'&σ2&efs&Hrd); simpl in *.
  inversion Hrd as [K e1' e2' ? ? Hhrd]; simpl in *; subst.
  destruct σ as [σh σp]; destruct σ' as [σ'h σ'p];
    destruct Hsp as [? [? ?]]; simpl in *; simplify_eq.
  inversion Hhrd; subst; try (unshelve (repeat econstructor; eauto); fail);
    repeat match goal with A : is_Some _ |- _ => destruct A as [? ?] end;
    simpl in *.
  - repeat econstructor; eauto.
  - eexists _, _, _; econstructor; eauto. eapply (ERandS true).
Qed.

Lemma soundness_prophecies e M :
  safe e M → erased_safe e M.
Proof.
  intros Hs th2 σ2 Hrtc re Hre.
  assert (rtc step ([e], {| Heap := ∅; Proph := ∅; ioState := M |})
              (th2, conjure_prophecies σ2)) as Hrtc'.
  { eapply erased_reachable_reachable;
      eauto using conjure_prophecies_have_same_proph. }
  edestruct Hs as [?|Hred]; eauto.
  right. eapply reducible_erase_reducible;
           eauto using conjure_prophecies_have_same_proph.
Qed.
