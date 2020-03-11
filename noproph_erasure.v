From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export proph_erasure lang_noproph
     lang_fully_erased full_erasure lang_ghost.
From stdpp Require Import gmap.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.Classical.

(* Definition heap_instr hG := (λ v, Ghostlang.instr (of_val v)) <$> hG. *)

Definition heap_erases_to (hI h : gmap loc val) :=
  dom (gset loc) hI = dom (gset loc) h ∧
  ∀ i vI,
    h !! i = Some vI → ∃ v, h !! i = Some v ∧ val_erases_to vI v.

Definition trace_erases_to τI τ :=
  Forall2 (λ (aI a : ioTag * val * val), match aI, a with
                     (tI, v1I, v2I), (t, v1, v2) =>
                     tI = t ∧ val_erases_to v1I v1 ∧ val_erases_to v2I v2
                   end) τI τ.

Definition erase_to esI es := Forall2 (λ eI e, ∃ n, erases_to n [] eI e) esI es.

Definition state_erases_to σI σ :=
  heap_erases_to (FEHeap σI) (NPHeap σ) ∧
  trace_erases_to (FEIO σI) (NPIO σ).

Definition cfg_erases_to cfgI cfg :=
  erase_to cfgI.1 cfg.1 ∧ state_erases_to cfgI.2 cfg.2.

Definition prim_step_no_fork μcfg μcfg' :=
  @language.prim_step PFE_lang μcfg.1 μcfg.2 μcfg'.1 μcfg'.2 [].

Definition ghost_steps h ρ τ e ρ' e' :=
  rtc prim_step_no_fork
      (e, {|FEHeap := h; FEProph := ρ; FEIO := τ |})
      (e', {|FEHeap := h; FEProph := ρ'; FEIO := τ |}).

Lemma prim_step_no_fork_ectx K e σ e' σ' :
  rtc prim_step_no_fork (e, σ) (e', σ') →
  rtc prim_step_no_fork (fill K e, σ) (fill K e', σ').
Proof.
  rewrite /prim_step_no_fork /=. intros [n Hstp]%rtc_nsteps.
  apply (nsteps_rtc n).
  revert K e σ e' σ' Hstp; induction n; intros K e σ e' σ' Hstp.
  - inversion Hstp; subst; econstructor.
  - inversion Hstp as [|? ? [] ? []]; simpl in *; simplify_eq.
    eapply (nsteps_l _ _ _ (_, _)).
    rewrite -fill_app; eapply Ectx_step; simpl; eauto.
    rewrite fill_app.
    by apply IHn.
Qed.

Lemma ghost_steps_ectx K h ρ τ e ρ' e' :
  ghost_steps h ρ τ e ρ' e' →
  ghost_steps h ρ τ (fill K e) ρ' (fill K e').
Proof.
  apply prim_step_no_fork_ectx.
Qed.

Lemma ghost_no_fork K e h ρ τ :
  (∀ f, e.[f] = e) →
  ghost_ok e → ∃ v ρ', ghost_steps h ρ τ (fill K e) ρ' (fill K (of_val v)) ∧
                       (∀ f, (of_val v).[f] = (of_val v)) ∧ ghost_ok (of_val v).
Proof.
  revert K ρ.
  induction e => K ρ Hcl; try inversion 1.
  - specialize (Hcl (λ _, Unit)); inversion Hcl.
  - eexists (RecV _), _; split; first by eapply rtc_refl.
    simpl; eauto.
  - eexists (LamV _), _; split; first by eapply rtc_refl.
    simpl; eauto.
  - eexists (UnitV), _; split; first by eapply rtc_refl.
    simpl; eauto.
  - eexists (NatV _), _; split; first by eapply rtc_refl.
    simpl; eauto.
  - eexists (BoolV _), _; split; first by eapply rtc_refl.
    simpl; eauto.
  - edestruct (IHe1 (PairLCtx e2 :: K)) as (v1 & ? & ? & Hcl1 & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    edestruct (IHe2 (PairRCtx v1 :: K)) as (? & ? & ? & Hcl2 & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists (PairV _ _), _; repeat split;
      first (by simpl in *; eapply rtc_transitive; eauto); auto.
    asimpl; intros; rewrite Hcl1 Hcl2; eauto.
  - intros.
    edestruct (IHe (InjLCtx :: K)) as (v1 & ? & ? & Hcl1 & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists (InjLV _), _. repeat split; first (by simpl in *; eauto); auto.
    asimpl; intros; rewrite Hcl1; eauto.
  - intros.
    edestruct (IHe (InjRCtx :: K)) as (v1 & ? & ? & Hcl1 & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists (InjRV _), _; repeat split; first (by simpl in *; eauto);
      simpl; auto.
    asimpl; intros; rewrite Hcl1; eauto.
  - intros.
    edestruct (IHe (FoldCtx :: K)) as (v1 & ? & ? & Hcl1 & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists (FoldV _), _; repeat split; first (by simpl in *; eauto); auto.
    asimpl; intros; rewrite Hcl1; eauto.
  - eexists (TLamV _), _; split; first by eapply rtc_refl.
    simpl; eauto.
  - eexists (LocV _), _; split; first by eapply rtc_refl.
    simpl; eauto.
  - eexists (PrV _), _; split; first by eapply rtc_refl.
    simpl; eauto.
  - eexists (PrV _), _; repeat econstructor; simpl; eauto.
    econstructor.
  - edestruct (IHe1 (Assign_PrLCtx e2 :: K)) as (v1 & ? & He1 & Hcl1); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    edestruct (IHe2 (Assign_PrRCtx v1 :: K)) as (v2 & ? & He2 & Hcl2); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists UnitV, _; split; last done.
    eapply rtc_transitive; first apply He1.
    eapply rtc_transitive; first apply He2.
    apply rtc_once; repeat econstructor; eauto using to_of_val.
Qed.

Lemma erases_to_val_inv n e v h ρ τ :
  erases_to n [] e (of_val v) →
  ∃ w ρ1, ghost_steps h ρ τ e ρ1 (of_val w) ∧ val_erases_to w v.
Proof.
  pose (m := S n). assert (n < m) as Hle by by subst; auto.
  clearbody m.
  revert n Hle e v h ρ τ; induction m; intros n Hle e v h ρ τ Hev;
    simpl in *; first lia.
  inversion Hev; simpl in *; simplify_eq; try by destruct v.
  - destruct v; simpl in *; simplify_eq.
    eexists (RecV _), _; split; first by eapply rtc_refl.
    econstructor; eauto.
  - destruct v; simpl in *; simplify_eq.
    eexists (LamV _), _; split; first by eapply rtc_refl.
    econstructor; eauto.
  - destruct (ghost_no_fork [] e1 h ρ τ) as (w & ρ' & Hgs & Hwcl & Hwok);
      simpl in *; auto.
    pose proof (erases_to_subst [] [] _ _ _ _ H1 Hwok Hwcl); simpl in *.
    assert (n0 < m) as Hn0 by lia.
    edestruct (IHm n0 Hn0 _ _ h ρ' τ H2) as (? & ? & ? & ?); eauto with lia.
    eexists _, _; split; eauto.
    eapply rtc_transitive.
    { eapply (ghost_steps_ectx [GRLetInCtx _]); eauto. }
    eapply (rtc_l _ _ (_, _));
      first by apply head_prim_step; econstructor; eauto using to_of_val.
    by eauto.
  - destruct (ghost_no_fork [] e1 h ρ τ) as (w & ρ' & Hgs & Hwcl & Hwok);
      simpl in *; auto.
    assert (n0 < m) as Hn0 by lia.
    edestruct (IHm n0 Hn0 _ _ h ρ' τ H1) as (? & ? & ? & ?); eauto.
    eexists _, _; split; eauto.
    eapply rtc_transitive.
    { eapply (ghost_steps_ectx [GRSeqCtx _]); eauto. }
    eapply (rtc_l _ _ (_, _));
      first (apply head_prim_step; simpl; econstructor; eauto using to_of_val).
    by eauto.
  - destruct v; simpl in *; simplify_eq.
    eexists (UnitV), _; split; first by eapply rtc_refl.
    econstructor; eauto.
  - destruct v; simpl in *; simplify_eq.
    eexists (NatV _), _; split; first by eapply rtc_refl.
    econstructor; eauto.
  - destruct v; simpl in *; simplify_eq.
    eexists (BoolV _), _; split; first by eapply rtc_refl.
    econstructor; eauto.
  - destruct v; simpl in *; simplify_eq.
    assert (n0 < m) as Hn0 by lia.
    edestruct (IHm _ Hn0 _ _ h ρ τ H0) as (w1 & ρ1 & ? & ?); eauto.
    assert (m0 < m) as Hm0 by lia.
    edestruct (IHm _ Hm0 _ _ h ρ1 τ H4) as (w2 & ρ2 & ? & ?); eauto.
    eexists (PairV _ _), _; split; last econstructor; eauto.
    eapply rtc_transitive.
    { eapply (ghost_steps_ectx [PairLCtx _]); eauto. }
    { eapply (ghost_steps_ectx [PairRCtx _]); eauto. }
  - destruct v; simpl in *; simplify_eq.
    assert (n0 < m) as Hn0 by lia.
    edestruct (IHm _ Hn0 _ _ h ρ τ H3) as (w1 & ρ1 & ? & ?); eauto.
    eexists (InjLV _), _; split; last econstructor; eauto.
    eapply (ghost_steps_ectx [InjLCtx]); eauto.
  - destruct v; simpl in *; simplify_eq.
    assert (n0 < m) as Hn0 by lia.
    edestruct (IHm _ Hn0 _ _ h ρ τ H3) as (w1 & ρ1 & ? & ?); eauto.
    eexists (InjRV _), _; split; last econstructor; eauto.
    eapply (ghost_steps_ectx [InjRCtx]); eauto.
  - destruct v; simpl in *; simplify_eq.
    assert (n0 < m) as Hn0 by lia.
    edestruct (IHm _ Hn0 _ _ h ρ τ H3) as (w1 & ρ1 & ? & ?); eauto.
    eexists (FoldV _), _; split; last econstructor; eauto.
    eapply (ghost_steps_ectx [FoldCtx]); eauto.
  - destruct v; simpl in *; simplify_eq.
    eexists (TLamV _), _; split; first by eapply rtc_refl.
    econstructor; eauto.
  - destruct v; simpl in *; simplify_eq.
    eexists (LocV _), _; split; first by eapply rtc_refl.
    econstructor; eauto.
  - destruct v; simpl in *; simplify_eq.
    eexists (IOtagV _), _; split; first by eapply rtc_refl.
    econstructor; eauto.
Qed.

(* Lemma erases_to_head_step n e1 σ1 σ2 σI1 eI1 σI2 eI2 efsI : *)
(*   erases_to n [] eI1 e1 → *)
(*   state_erases_to σI1 σ1 → *)
(*   state_erases_to σI2 σ2 → *)
(*   @ectx_language.head_step PNP_ectx_lang eh1 σh1 eh2 σh2 efsh *)
(*   → ∃ e2 efs, @prim_step PFE_ectx_lang e1 σ1 e2 σ2 efs *)
(*               ∧ (erases_to n [] e2 eh2) ∧ *)
(*               forall i ef, efs !! i = Some ef → (∃ efh, efsh !! i = Some efh ∧ *)
(*                                                    erases_to n [] ef efh). *)
(* Proof. *)
(*   pose (m := S n). assert (n < m) as Hle by by subst; auto. *)
(*   clearbody m. *)
(*   revert n Hle e σ1 eh1 σ2 eh2 efs. *)
(*   induction m; intros n Hle e σ1 eh1 σ2 eh2 efs He Hhstp; first lia. *)
(*   inversion Hhstp; simplify_eq. *)
(*   - *)


Lemma erases_to_fill_inv n : ∀ eI hI h ρ τI τ K e e' σ' efs,
  erases_to n [] eI (fill K e) →
  heap_erases_to hI h →
  trace_erases_to τI τ →
  @ectx_language.head_step PNP_ectxi_lang e {| NPHeap := h; NPIO := τ|}
                           e' σ' efs →
  ∃ m eI' eI'' ρ' σI'' efsI,
    ghost_steps h ρ τ eI ρ' eI' ∧
    @prim_step PFE_ectxi_lang eI' {|FEHeap := hI; FEProph := ρ'; FEIO := τI|}
               eI'' σI'' efsI ∧
    state_erases_to σI'' σ' ∧
    erases_to m [] eI'' (fill K e') ∧
    erase_to efsI efs.
Proof.
  pose (m := S n). assert (n < m) as Hle by by subst; auto.
  clearbody m. revert n Hle.
  induction m; intros n Hle eI hI h ρ τI τ K e e' σ' efs Hee Heh Heτ Hhstp;
    first by omega.
  inversion Hee; simpl in *; simplify_eq.
  - inversion H3.
  - induction K using rev_ind; auto.
    + simpl in *; simplify_eq.
      inversion Hhstp.
    + rewrite fill_app in H; simpl in *.
      destruct x; simplify_eq.
  - induction K using rev_ind; auto.
    + simpl in *; simplify_eq.
      inversion Hhstp.
    + rewrite fill_app in H; simpl in *.
      destruct x; simplify_eq.
  - destruct K using rev_ind; simpl in *; simplify_eq.
    + destruct erases_to_val_inv

      eexists _, (LetIn e1 e2), _, _, _, _; repeat split;
        first apply rtc_refl.
      apply 

      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H; simpl in *.
      destruct x; simpl in *; simplify_eq.
      assert (n0 < m) as Hn0 by omega.
      edestruct (IHm) as (e11 & ρ1 & He11 & (K & eh & m1 & HK & Heh & He11eq));
        eauto; subst.
      eexists (fill (K ++ [LetInCtx _]) eh), ρ1; split; eauto.
      rewrite fill_app; simpl.
      apply (ghost_steps_ectx [LetInCtx _]); eauto.
      eexists (K ++ [LetInCtx e2]), eh, _; repeat split; eauto.
      apply Forall2_app; auto.
      repeat econstructor; eauto.
  - destruct (ghost_no_fork [GRLetInCtx e2] e1 h ρ τ) as (v & ρ' & Hv & Hvcl & Hvgo);
      auto.
    assert (ghost_steps h ρ τ (fill [GRLetInCtx e2] e1) ρ' (e2.[of_val v/]))
      as Hv'.
    { eapply rtc_r; eauto; simpl.
      apply head_prim_step; econstructor; eauto using to_of_val. }
    pose proof (erases_to_subst [] [] _ _ _ _ H1 Hvgo Hvcl) as H1'; asimpl in *.
    assert (n0 < m) as Hn0 by lia.
    destruct (IHm _ Hn0 _ h ρ' τ _ _ H1') as
        (e11 & ρ11 & He11 & K11 & eh11 & m11 & HK11 & Heh11 & He11');
      simplify_eq.
    exists (fill K11 eh11), ρ11; split.
    { eapply rtc_transitive; eauto. }
    eexists _, _, _; repeat split; eauto.
  -  destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Seq e1 e2), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H; simpl in *.
      destruct x; simpl in *; simplify_eq.
      assert (n0 < m) as Hn0 by omega.
      edestruct (IHm) as (e11 & ρ1 & He11 & (K & eh & m1 & HK & Heh & He11eq));
        eauto; subst.
      eexists (fill (K ++ [SeqCtx _]) eh), ρ1; split; eauto.
      rewrite fill_app; simpl.
      apply (ghost_steps_ectx [SeqCtx _]); eauto.
      eexists (K ++ [SeqCtx e2]), eh, _; repeat split; eauto.
      apply Forall2_app; auto.
      repeat econstructor; eauto.
  - destruct (ghost_no_fork [GRSeqCtx e2] e1 h ρ τ) as (v & ρ' & Hv & Hvcl & Hvgo);
      auto.
    assert (ghost_steps h ρ τ (fill [GRSeqCtx e2] e1) ρ' e2)
      as Hv'.
    { eapply rtc_r; eauto; simpl.
      apply head_prim_step; econstructor; eauto using to_of_val. }
    assert (n0 < m) as Hn0 by lia.
    destruct (IHm _ Hn0 _ h ρ' τ _ _ H1) as
        (e11 & ρ11 & He11 & K11 & eh11 & m11 & HK11 & Heh11 & He11');
      simplify_eq.
    exists (fill K11 eh11), ρ11; split.
    { eapply rtc_transitive; eauto. }
    eexists _, _, _; repeat split; eauto.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (App e1 e2), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H; simpl in *.
      destruct x; simpl in *; simplify_eq.
      * assert (n0 < m) as Hn0 by omega.
        edestruct (IHm) as (e11 & ρ1 & He11 & (K & eh & m1 & HK & Heh & He11eq));
          eauto; subst.
        eexists (fill (K ++ [AppLCtx _]) eh), ρ1; split; eauto.
        rewrite fill_app; simpl.
        apply (ghost_steps_ectx [AppLCtx _]); eauto.
        eexists (K ++ [AppLCtx e2]), eh, _; repeat split; eauto.
        apply Forall2_app; auto.
        repeat econstructor; eauto.
      * destruct (erases_to_val_inv _ _ _ h ρ τ H0) as (w1 & ρ1 & Hw1 & Hvet).
        assert (m0 < m) as Hm0 by omega.
        edestruct (IHm _ Hm0 _ h ρ1 τ _ _ H4) as
            (e11 & ρ2 & He11 & (K & eh & m1 & HK & Heh & He11eq));
          eauto; subst.
        eexists (fill (K ++ [AppRCtx w1]) eh), ρ2; split; eauto.
        { rewrite fill_app; simpl.
          eapply rtc_transitive.
          - apply (ghost_steps_ectx [AppLCtx _]); eauto.
          - apply (ghost_steps_ectx [AppRCtx _]); eauto. }
        eexists (K ++ [AppRCtx w1]), eh, _; repeat split; eauto.
        apply Forall2_app; auto.
        repeat econstructor; eauto.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists Unit, ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Nat _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Bool _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Fork _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H; simpl in *.
      by destruct x.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Loc _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (IOtag _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists Rand, ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - admit.
Admitted.


Lemma erases_to_fill_inv n : ∀ e h ρ τ K' eh',
  erases_to n [] e (fill K' eh') →
  ∃ e1 ρ1, ghost_steps h ρ τ e ρ1 e1 ∧
           ∃ K eh m, ectx_erases_to K K' ∧ erases_to m [] eh eh' ∧ e1 = fill K eh.
Proof.
  pose (m := S n). assert (n < m) as Hle by by subst; auto.
  clearbody m. revert n Hle.
  induction m; intros n Hle e h ρ τ K' eh' He; first by omega.
  inversion He; simpl in *; simplify_eq.
  - inversion H3.
  - assert (K' = []); subst; simpl in *.
    { clear -H; induction K' using rev_ind; auto.
      rewrite fill_app in H; simpl in *.
      destruct x; simplify_eq. }
    simplify_eq.
    eexists _, _; split; first apply rtc_refl.
    eexists [], _, _; split; eauto.
    constructor.
  - assert (K' = []); subst; simpl in *.
    { clear -H; induction K' using rev_ind; auto.
      rewrite fill_app in H; simpl in *.
      destruct x; simplify_eq. }
    simplify_eq.
    eexists _, _; split; first apply rtc_refl.
    eexists [], _, _; split; eauto.
    constructor.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (LetIn e1 e2), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H; simpl in *.
      destruct x; simpl in *; simplify_eq.
      assert (n0 < m) as Hn0 by omega.
      edestruct (IHm) as (e11 & ρ1 & He11 & (K & eh & m1 & HK & Heh & He11eq));
        eauto; subst.
      eexists (fill (K ++ [LetInCtx _]) eh), ρ1; split; eauto.
      rewrite fill_app; simpl.
      apply (ghost_steps_ectx [LetInCtx _]); eauto.
      eexists (K ++ [LetInCtx e2]), eh, _; repeat split; eauto.
      apply Forall2_app; auto.
      repeat econstructor; eauto.
  - destruct (ghost_no_fork [GRLetInCtx e2] e1 h ρ τ) as (v & ρ' & Hv & Hvcl & Hvgo);
      auto.
    assert (ghost_steps h ρ τ (fill [GRLetInCtx e2] e1) ρ' (e2.[of_val v/]))
      as Hv'.
    { eapply rtc_r; eauto; simpl.
      apply head_prim_step; econstructor; eauto using to_of_val. }
    pose proof (erases_to_subst [] [] _ _ _ _ H1 Hvgo Hvcl) as H1'; asimpl in *.
    assert (n0 < m) as Hn0 by lia.
    destruct (IHm _ Hn0 _ h ρ' τ _ _ H1') as
        (e11 & ρ11 & He11 & K11 & eh11 & m11 & HK11 & Heh11 & He11');
      simplify_eq.
    exists (fill K11 eh11), ρ11; split.
    { eapply rtc_transitive; eauto. }
    eexists _, _, _; repeat split; eauto.
  -  destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Seq e1 e2), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H; simpl in *.
      destruct x; simpl in *; simplify_eq.
      assert (n0 < m) as Hn0 by omega.
      edestruct (IHm) as (e11 & ρ1 & He11 & (K & eh & m1 & HK & Heh & He11eq));
        eauto; subst.
      eexists (fill (K ++ [SeqCtx _]) eh), ρ1; split; eauto.
      rewrite fill_app; simpl.
      apply (ghost_steps_ectx [SeqCtx _]); eauto.
      eexists (K ++ [SeqCtx e2]), eh, _; repeat split; eauto.
      apply Forall2_app; auto.
      repeat econstructor; eauto.
  - destruct (ghost_no_fork [GRSeqCtx e2] e1 h ρ τ) as (v & ρ' & Hv & Hvcl & Hvgo);
      auto.
    assert (ghost_steps h ρ τ (fill [GRSeqCtx e2] e1) ρ' e2)
      as Hv'.
    { eapply rtc_r; eauto; simpl.
      apply head_prim_step; econstructor; eauto using to_of_val. }
    assert (n0 < m) as Hn0 by lia.
    destruct (IHm _ Hn0 _ h ρ' τ _ _ H1) as
        (e11 & ρ11 & He11 & K11 & eh11 & m11 & HK11 & Heh11 & He11');
      simplify_eq.
    exists (fill K11 eh11), ρ11; split.
    { eapply rtc_transitive; eauto. }
    eexists _, _, _; repeat split; eauto.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (App e1 e2), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H; simpl in *.
      destruct x; simpl in *; simplify_eq.
      * assert (n0 < m) as Hn0 by omega.
        edestruct (IHm) as (e11 & ρ1 & He11 & (K & eh & m1 & HK & Heh & He11eq));
          eauto; subst.
        eexists (fill (K ++ [AppLCtx _]) eh), ρ1; split; eauto.
        rewrite fill_app; simpl.
        apply (ghost_steps_ectx [AppLCtx _]); eauto.
        eexists (K ++ [AppLCtx e2]), eh, _; repeat split; eauto.
        apply Forall2_app; auto.
        repeat econstructor; eauto.
      * destruct (erases_to_val_inv _ _ _ h ρ τ H0) as (w1 & ρ1 & Hw1 & Hvet).
        assert (m0 < m) as Hm0 by omega.
        edestruct (IHm _ Hm0 _ h ρ1 τ _ _ H4) as
            (e11 & ρ2 & He11 & (K & eh & m1 & HK & Heh & He11eq));
          eauto; subst.
        eexists (fill (K ++ [AppRCtx w1]) eh), ρ2; split; eauto.
        { rewrite fill_app; simpl.
          eapply rtc_transitive.
          - apply (ghost_steps_ectx [AppLCtx _]); eauto.
          - apply (ghost_steps_ectx [AppRCtx _]); eauto. }
        eexists (K ++ [AppRCtx w1]), eh, _; repeat split; eauto.
        apply Forall2_app; auto.
        repeat econstructor; eauto.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists Unit, ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Nat _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Bool _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Fork _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H; simpl in *.
      by destruct x.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (Loc _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists (IOtag _), ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct K' using rev_ind; simpl in *; simplify_eq.
    + eexists Rand, ρ; split; first apply rtc_refl.
      eexists [], _, _; repeat split; eauto.
      constructor.
    + rewrite fill_app in H3; simpl in *.
      by destruct x.
  - admit.
Admitted.


Lemma noproph_step cfg cfgI cfg' :
  cfg_erases_to cfgI cfg →
  @language.step PNP_lang cfg cfg' →
  ∃ cfgI', cfg_erases_to cfgI' cfg' ∧ rtc (@language.step PFE_lang) cfgI cfgI'.
Proof.
  destruct cfgI as [thpI σI].
  intros [Her1 Her2] Hstp.
  inversion Hstp as [? ? ? ? ? ? ? ? ? Hpstp]; subst.
  inversion Hpstp as [? ? ? ? ? Hhstp]; simpl in *; simplify_eq.
  inversion Hhstp; simplify_eq.
  - apply List.Forall2_app_inv_r in Her1.
    destruct Her1 as
        (t1I & restI & Ht1I & (er & t2I & (n & Her) & Ht2I & Hrest)%Forall2_cons_inv_r & Heq);
      simplify_eq.
    destruct (erases_to_fill_inv _ _ (FEHeap σI) (FEProph σI) (FEIO σI) _ _ Her)
    as (er' & ρr & Herstp & Kr & ehr & m & HKr & Hehr & Her'); simplify_eq.
    exists (t1I ++ (fill Kr e1.[Rec e1,e2/]) :: t2I ++ [], σI); split.
    { split; simpl; auto. apply Forall2_app; auto.
      apply Forall2_cons; eauto using Forall2_app.
      








eexists (_, {| FEHeap := _;  FEProph := _;  FEIO := _|}); repeat split; simpl; eauto.
    



Theorem fully_erased_noproph e M : fully_erased_safe e M → noproph_safe e M.
Proof.
  