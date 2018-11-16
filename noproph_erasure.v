From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export proph_erasure lang_noproph
     lang_fully_erased full_erasure lang_ghost.
From stdpp Require Import gmap.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.Classical.

(* Definition heap_instr hG := (λ v, Ghostlang.instr (of_val v)) <$> hG. *)

Definition val_erases_to vI v := erases_to [] (of_val vI) (of_val v).

Definition heap_erases_to (hI h : gmap loc val) :=
  dom (gset loc) hI = dom (gset loc) h ∧
  ∀ i vI,
    h !! i = Some vI → ∃ v, h !! i = Some v ∧ val_erases_to vI v.

Definition trace_erases_to τI τ :=
  Forall2 (λ (aI a : ioTag * val * val), match aI, a with
                     (tI, v1I, v2I), (t, v1, v2) =>
                     tI = t ∧ val_erases_to v1I v1 ∧ val_erases_to v2I v2
                   end) τI τ.

Definition erase_to esI es := Forall2 (erases_to []) esI es.

Definition state_erases_to σI σ :=
  heap_erases_to (FEHeap σI) (NPHeap σ) ∧
  trace_erases_to (FEIO σI) (NPIO σ).

Definition cfg_erases_to cfgI cfg :=
  erase_to cfgI.1 cfg.1 ∧ state_erases_to cfgI.2 cfg.2.

Definition prim_step_no_fork μcfg μcfg' :=
  @language.prim_step PFE_lang μcfg.1 μcfg.2 μcfg'.1 μcfg'.2 [].

Lemma ghost_no_fork K e h ρ τ :
  (∀ f, e.[f] = e) →
  ghost_ok e → ∃ v ρ', rtc prim_step_no_fork
                   (fill K e, {|FEHeap := h; FEProph := ρ; FEIO := τ |})
                   (fill K (of_val v), {|FEHeap := h; FEProph := ρ'; FEIO := τ |}).
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
  - 

Lemma noproph_step M cfg cfgI cfg' :
  cfg_erases_to cfgI cfg →
  @language.step PNP_lang cfg cfg' →
  cfg_not_failed M cfgI.1 cfgI.2 →
  ∃ cfgI', cfg_erases_to cfgI' cfg' ∧ rtc (@language.step PFE_lang) cfgI cfgI'.
Proof.
  

Theorem fully_erased_noproph e M : fully_erased_safe e M → noproph_safe e M.
Proof.
  