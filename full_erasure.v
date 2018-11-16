From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export proph_erasure lang_proph_erased
     lang_fully_erased.
From stdpp Require Import gmap.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.Classical.

Definition prefix_closed (M : ioSpec) :=
  ∀ τ τ', M (τ ++ τ') → M τ.

Definition IO_performed
           (σ : language.state PE_lang) (σ' : language.state PFE_lang) M
  := (EHeap σ) = (FEHeap σ') ∧ (EProph σ) = (FEProph σ') ∧
     (EioState σ) = (λ τ, M ((FEIO σ') ++ τ)) ∧ (∃ τ, M ((FEIO σ') ++ τ)).

Definition make_ioSpec (σ : language.state PFE_lang) M :
  language.state PE_lang :=
  {| EHeap := FEHeap σ; EProph := FEProph σ;
     EioState := λ τ, M ((FEIO σ) ++ τ) |}.

Lemma make_ioSpec_IO_performed σ (M : ioSpec):
  M (FEIO σ) → IO_performed (make_ioSpec σ M) σ M.
Proof.
  destruct σ as [h p i]; repeat split; simpl in *; eauto.
  by eexists nil; rewrite app_nil_r.
Qed.

Lemma fully_erased_reachable_reachable th1 h1 th2 σ2 (M : ioSpec) :
  prefix_closed M →
  M (FEIO σ2) →
  erased_safe e M →
  rtc (@step PFE_lang) (th1, {| FEHeap := h1; FEProph := ∅; FEIO := [] |})
      (th2, σ2) →
  rtc (@step PE_lang)
      (th1, {| EHeap := h1; EProph := ∅; EioState := M |})
      (th2, make_ioSpec σ2 M).
Proof.
  intros Mpc.
  remember (th1, {| FEHeap := h1; FEProph := ∅; FEIO := [] |}) as cfg.
  remember (th2, σ2) as cfg'.
  intros HM Hrtc; revert HM.
  revert th1 h1 th2 σ2 Heqcfg Heqcfg'.
  simpl in *.
  eapply (rtc_ind_r_weak
            (λ z z', ∀ (th1 : list (language.expr PFE_lang))
                       (h1 : gmap loc val)
                       (th2 : list (language.expr PFE_lang))
                       (σ2 : language.state PFE_lang),
                z = (th1,
                     {| FEHeap := h1; FEProph := ∅; FEIO := [] |})
                → z' = (th2, σ2) →
                M (FEIO σ2) →
                rtc (@step PE_lang)
                    (th1, {| EHeap := h1; EProph := ∅; EioState := M |})
                    (th2, make_ioSpec σ2 M)));
    last eauto.
  - intros x th1 h1 th2 σ2 Heqcfg Heqcfg'; simplify_eq.
    left; split; simpl; eauto; econstructor.
  - intros x y z Hxy Hyz IH th1 h1 th2 σ2 Heqcfg Heqcfg' HM;
      simplify_eq; simpl in *.
    destruct y as [yh yp].
    inversion Hyz as [? ? ? ? ? ? ? ? ? Hpr]; simplify_eq.
    inversion Hpr as [? ? ? ? ? Hestp]; simpl in *; simplify_eq.
    inversion Hestp; simplify_eq;
      repeat match goal with
      | H : is_Some _ |- _ => destruct H
      end;
      try (by eapply rtc_r; first (by apply IH); repeat econstructor; eauto).
    eapply rtc_r; first apply IH; eauto.
    + simpl in HM; eapply Mpc; eauto.
    + unfold make_ioSpec; simpl.
      replace (λ τ, M ((FEIO σ1 ++ [(t, v, v')]) ++ τ)) with
        (λ τ, M (FEIO σ1 ++ [(t, v, v')] ++ τ)); last first.
    { extensionality τ. by rewrite -assoc. }
    repeat econstructor; eauto; simpl.
    apply (EIOS t e v v' {| EioState := λ τ, M (FEIO σ1 ++ τ) |}); eauto.
Qed.

Instance fully_erased_safe_impl e :
  Proper ((≡) ==> impl) (fully_erased_safe e).
Proof.
  rewrite /fully_erased_safe /IO_reducible /cfg_not_failed /IO_not_failed.
  intros M M' HMM HM th2 σ2 HM' Hrtc e' He'.
  destruct (HM th2 σ2 (proj2 (HMM _) HM') Hrtc e' He') as
      [| (e'' & σ'' & efs & Hstp & Hrd)];
    first auto.
  right. eexists _, _, _; split; eauto.
  intros t v v' Hvv'. destruct (Hrd _ _ _ Hvv') as [v'' Hrd'].
  eexists; eapply HMM; eauto.
Qed.

Instance fully_erased_safe_equiv e :
  Proper ((≡) ==> iff) (fully_erased_safe e).
Proof.
  intros M M' HMM; split => HL.
  - eapply fully_erased_safe_impl; eauto.
  - symmetry in HMM. eapply fully_erased_safe_impl; eauto.
Qed.

Lemma fully_erased_safe_union e (F : ioSpec → Prop) :
  (∀ M, F M → fully_erased_safe e M) →
  fully_erased_safe e (λ io, ∃ M, F M ∧ M io).
Proof.
  rewrite /fully_erased_safe /IO_reducible /cfg_not_failed /IO_not_failed.
  intros Hfa th2 σ2 [M [HFM HMσ2]] Hrtc e' He'.
  destruct (Hfa M HFM th2 σ2 HMσ2 Hrtc e' He') as
      [?|(e'' & σ'' & efs & Hstp & Hrd)];
    first auto; simpl in *.
  right; do 3 eexists; split; eauto.
  intros t v v' Ht.
  destruct (Hrd t v v' Ht) as [v'' HM].
  exists v'', M; split; auto.
Qed.

Lemma reducible_fully_erase_reducible e σ σ' M :
  IO_performed σ σ' M →
  @language.reducible PE_lang e σ →
  ∃ e' σ'' efs,
    @language.prim_step PFE_lang e σ' e' σ'' efs
    ∧ ∀ t v v', FEIO σ'' = FEIO σ' ++ [(t, v, v')] →
                ∃ v'', M (FEIO σ' ++ [(t, v, v'')]).
Proof.
  intros Hsp (e'&σ2&efs&Hrd); simpl in *.
  inversion Hrd as [K e1' e2' ? ? Hhrd]; simpl in *; subst.
  destruct σ as [σh σp]; destruct σ' as [σ'h σ'p];
    destruct Hsp as [? [? [? ?]]]; simpl in *; simplify_eq.
  inversion Hhrd; subst;
    repeat match goal with A : is_Some _ |- _ => destruct A as [? ?] end;
    simpl in *;
    try (by (unshelve (repeat econstructor; eauto)); simpl in *;
            try match goal with
                | H : ?A = ?A ++ [_] |- _ =>
                  let H' := fresh in
                  pose proof (f_equal length H) as H';
                  rewrite app_length in H'; simpl in H'; omega
                end).
  - eexists _, _, _; split; first by unshelve (repeat econstructor; eauto).
    intros ? ? ? ?; simpl in *;
      match goal with
      | H: ?A ++ [_] = ?A ++ [_] |- _ =>
        apply app_inv_head in H; simplify_eq; simpl in *; eauto
      end.
Qed.

Lemma soundness_io e M :
  prefix_closed M → erased_safe e M → fully_erased_safe e M.
Proof.
  rewrite /fully_erased_safe /IO_reducible /cfg_not_failed /IO_not_failed.
  intros Hpc Hs th2 σ2 HMσ2 Hrtc re Hre.
  assert (rtc (@language.step PE_lang)
              ([e], {| EHeap := ∅; EProph := ∅; EioState := M |})
              (th2, make_ioSpec σ2 M)) as Hrtc'.
  { eapply fully_erased_reachable_reachable; eauto. }
  edestruct Hs as [?|Hred]; eauto.
  right. eapply reducible_fully_erase_reducible; eauto.
  by apply make_ioSpec_IO_performed.
Qed.
