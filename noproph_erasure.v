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
  ghost_ok e → ∃ v ρ', ghost_steps h ρ τ (fill K e) ρ' (fill K (of_val v)).
Proof.
  revert K ρ.
  induction e => K ρ Hcl; try inversion 1.
  - specialize (Hcl (λ _, Unit)); inversion Hcl.
  - eexists (RecV _), _; eapply rtc_refl.
  - eexists (LamV _), _; eapply rtc_refl.
  - eexists (UnitV), _; eapply rtc_refl.
  - eexists (NatV _), _; eapply rtc_refl.
  - eexists (BoolV _), _; eapply rtc_refl.
  - edestruct (IHe1 (PairLCtx e2 :: K)) as (v1 & ? & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    edestruct (IHe2 (PairRCtx v1 :: K)) as (? & ? & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists (PairV _ _), _. simpl in *; eapply rtc_transitive; eauto.
  - intros.
    edestruct (IHe (InjLCtx :: K)) as (v1 & ? & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists (InjLV _), _. simpl in *; eauto.
  - intros.
    edestruct (IHe (InjRCtx :: K)) as (v1 & ? & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists (InjRV _), _. simpl in *; eauto.
  - intros.
    edestruct (IHe (FoldCtx :: K)) as (v1 & ? & ?); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists (FoldV _), _. simpl in *; eauto.
  - eexists (TLamV _), _; eapply rtc_refl.
  - eexists (LocV _), _; eapply rtc_refl.
  - eexists (PrV _), _; eapply rtc_refl.
  - eexists (PrV _), _; repeat econstructor; simpl; eauto.
    econstructor.
  - edestruct (IHe1 (Assign_PrLCtx e2 :: K)) as (v1 & ? & He1); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    edestruct (IHe2 (Assign_PrRCtx v1 :: K)) as (v2 & ? & He2); eauto.
    { by intros f; specialize (Hcl f); asimpl in Hcl; simplify_eq. }
    eexists UnitV, _.
    eapply rtc_transitive; first apply He1.
    eapply rtc_transitive; first apply He2.
    apply rtc_once; repeat econstructor; eauto using to_of_val.
Qed.

Lemma erases_to_fill_inv n : ∀ e h ρ τ K' eh',
  erases_to n [] e (fill K' eh') →
  ∃ e1 ρ1, ghost_steps h ρ τ e ρ1 e1 ∧
           ∃ K eh m, ectx_erases_to K K' ∧ erases_to m [] eh eh' ∧ e1 = fill K eh.
Proof.
  pose (m := S n). assert (n < m) as Hle by by subst; auto.
  clearbody m. revert n Hle.
  induction m; intros n Hle e h ρ τ K' eh' He; first by omega.
  inversion He; simplify_eq.
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
  - 
    


    assert (K' = []); subst; simpl in *.
    { clear -H; induction K' using rev_ind; auto.
      rewrite fill_app in H; simpl in *.
      destruct x; simplify_eq. }
    simplify_eq.
    eexists _, _; split; first apply rtc_refl.
    eexists [], _, _; split; eauto.
    constructor.




  set (Kl := length K'); set (HKl := eq_refl : Kl = length K' );
    clearbody Kl HKl.
  revert K' HKl e h ρ τ eh'.
  induction Kl as [|a K']=> e h ρ τ eh'.
  - simpl; intros ?; eexists [], _; repeat split; eauto; try apply Forall2_nil.
  - simpl; intros (K1 & eh1 & HK & He & Heq)%IHK'; simpl in *; subst.
    induction He.
    + 



-
  revert e eh'. induction K' as [|a K']=> e eh'.
  + simpl; intros ?; eexists [], _; repeat split; eauto; try apply Forall2_nil.
  + simpl; intros (K1 & eh1 & HK & He & Heq)%IHK'; simpl in *; subst.

erases_to e e' → ∃ K e1, e = fill C e1 ∧ all_ghost C ∧ erases_to_core e1 e'

    destruct a; simpl in *.
    *


Lemma noproph_step cfg cfgI cfg' :
  cfg_erases_to cfgI cfg →
  @language.step PNP_lang cfg cfg' →
  ∃ cfgI', cfg_erases_to cfgI' cfg' ∧ rtc (@language.step PFE_lang) cfgI cfgI'.
Proof.
  destruct cfgI as [thpI σI].
  intros [Her1 [Her2 Her3]] Hstp.
  inversion Hstp as [? ? ? ? ? ? ? ? ? Hpstp]; subst.
  inversion Hpstp as [? ? ? ? ? Hhstp]; simpl in *; simplify_eq.
  inversion Hhstp; simplify_eq.
  - apply List.Forall2_app_inv_r in Her1.
    destruct Her1 as
        (t1I & restI & Ht1I & (er & t2I & Her & Ht2I & Hrest)%Forall2_cons_inv_r & Heq).
    subst.
    








eexists (_, {| FEHeap := _;  FEProph := _;  FEIO := _|}); repeat split; simpl; eauto.
    



Theorem fully_erased_noproph e M : fully_erased_safe e M → noproph_safe e M.
Proof.
  