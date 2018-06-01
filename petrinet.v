From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris_io Require Export lang rules.
From iris.proofmode Require Import tactics.

Require Import Coq.Logic.FunctionalExtensionality.

Section PetriNet.

  Class PlacesC := places
      { Places : Type;
        ThePlaces_eqdec :> EqDecision Places;
      }.

  Context `{PlacesC}.

  Inductive Transition : Type :=
    IOTr (p : Places) (t : ioTag) (v v' : val) (q : Places)
  | SplitTr (p q q': Places)
  | JoinTr (p p' q: Places)
  | NoOpTr (p q : Places).

  Definition PetriNet := Transition → Prop.

  (** The CMRA for petrinet valuations. *)
  Class petrinetIG Σ := PetriNetIG {
    γPN : gname;
    PNI_exclG :> inG Σ (authUR (ofe_funUR (λ p : Places, natUR)));
    ThePetriNet : PetriNet
  }.

  Implicit Types N : PetriNet.
  Implicit Types p q : Places.

  Definition Valuation := Places → nat.

  Implicit Types V : Valuation.

  Definition singVAL p := (λ q, if decide (p = q) then 1 else 0).

  Definition ValPlus V V' := λ p, V p + V' p.

  Global Instance : Comm eq ValPlus.
  Proof.
    intros x y. extensionality u; unfold ValPlus; omega.
  Qed.

  Notation "V ⊎ W" := (ValPlus V W) (at level 50, left associativity).

  Inductive Traces N : Valuation → ioSpec :=
  | EmpTR V : Traces N V []
  | IOTR V p t v v' q τ :
      N (IOTr p t v v' q) →
      Traces N ((singVAL q) ⊎ V) τ →
      Traces N ((singVAL p) ⊎ V) ((t, v, v') :: τ)
  | SplitTR V p q q' τ :
      N (SplitTr p q q') →
      Traces N (singVAL q ⊎ singVAL q' ⊎ V) τ →
      Traces N (singVAL p ⊎ V) τ
  | JoinTR V p p' q τ :
      N (JoinTr p p' q) →
      Traces N (singVAL q ⊎ V) τ →
      Traces N (singVAL p ⊎ singVAL p' ⊎ V) τ
  | NoOpTR V p q τ :
      N (NoOpTr p q) →
      Traces N (singVAL q ⊎ V) τ →
      Traces N (singVAL p ⊎ V) τ.

  Definition ResultDet (T : ioSpec) :=
    ∀ t v v' v'' τ τ' τ'',
      T (τ ++ (t, v, v') :: τ') →
      T (τ ++ (t, v, v'') :: τ'') → v' = v''.

  Context `{heapIG Σ, petrinetIG Σ}.

  Program Definition FullVAL V :=
    @own Σ (authUR (ofe_funUR (λ p, natUR))) _ γPN (● V).

  Definition ownVAL V :=
    @own Σ (authUR (ofe_funUR (λ p, natUR))) _ γPN (◯ V).

  Lemma ownVAL_split V V' : ownVAL (V ⊎ V') ⊣⊢ ownVAL V ∗  ownVAL V'.
  Proof. by rewrite /ownVAL -own_op -auth_frag_op. Qed.

  Global Instance of_fun_CmraDiscrete (A : Type) (f : A → ucmraT) :
    (∀ x, CmraDiscrete (f x)) → CmraDiscrete (ofe_funUR f).
  Proof.
    intros Hfx; split.
    - intros z z' Heq u.
      destruct (Hfx u) as [Hfxo _].
      apply Hfxo; apply Heq.
    - intros x Hx0 u.
      destruct (Hfx u) as [_ Hfxv].
      apply Hfxv.
      apply Hx0.
  Qed.

  Lemma ownVAL_Full V V' : ownVAL V -∗ FullVAL V' -∗ ⌜∃ V'', V' = V ⊎ V''⌝.
  Proof.
    iIntros "H1 H2".
    iCombine "H1" "H2" as "H".
    iDestruct (own_valid with "H") as "Hvl".
    iDestruct "Hvl" as %Hvl.
    rewrite auth_valid_eq in Hvl; simpl in *; destruct Hvl as [Hvl _].
    specialize (Hvl 0).
    apply cmra_discrete_included_iff in Hvl.
    revert Hvl; rewrite right_id; intros [V'' Hvl].
    iPureIntro.
    exists V''. extensionality p.
    apply Hvl.
  Qed.

  Definition PetriNetN := (nroot .@ "PetriNet").

  Definition PetriNetInv : iProp Σ :=
    inv PetriNetN (∃ V T, ownIO T ∗ FullVAL V ∗
                                ⌜∀ τ, Traces ThePetriNet V τ → T τ⌝ ∗ ⌜ResultDet T⌝)%I.

  Definition Token p := (ownVAL (singVAL p) ∗ PetriNetInv)%I.

  Lemma PetriNet_delete V V' : FullVAL (V ⊎ V') -∗ ownVAL V' -∗ |==> FullVAL V.
  Proof.
    iIntros "Hf Ho".
    rewrite /FullVAL /ownVAL.
    iCombine "Hf" "Ho" as "Hfo".
    iMod (own_update with "Hfo") as "Hf".
    { apply auth_update_dealloc.
      apply (local_update_unital_discrete _ _ (V : (ofe_funUR (λ p, natUR)))).
      intros z Hvl Heq; split ; first done.
      rewrite left_id; intros u.
      specialize (Heq u); simpl in *.
      apply leibniz_equiv in Heq.
      assert (V u + V' u = V' u + z u) as Heq' by apply Heq.
      assert (V u = z u) by omega.
      done. }
    done.
  Qed.

  Lemma PetriNet_alloc V V' : FullVAL V -∗ |==> FullVAL (V ⊎ V') ∗ ownVAL V'.
  Proof.
    iIntros "Hf".
    iMod (own_update with "Hf") as "Hfo".
    { apply auth_update_alloc.
      apply (local_update_unital_discrete
               _ _ (V ⊎ V' : (ofe_funUR (λ p, natUR))) V').
      intros z Hvl Heq; split ; first done.
      revert Heq; rewrite left_id => Heq.
      by intros u; rewrite (comm _ _ z) /ValPlus; rewrite (Heq u). }
    iDestruct "Hfo" as "[Hf Ho]".
    by iFrame.
  Qed.

  Lemma wp_petrinet_io t e v p v' q :
    IntoVal e v →
    ThePetriNet (IOTr p t v v' q) →
    {{{Token p}}} IO t e {{{RET v'; Token q}}}.
  Proof.
    iIntros (<-%of_to_val HIO Φ) "[Htk #Hinv] HΦ".
    iApply wp_atomic.
    iInv PetriNetN as "Hpt" "Hcl".
    iDestruct "Hpt" as (V T) "(HT & HV & >Hinc & >Hrd)".
    iDestruct "Hinc" as %Hinc. iDestruct "Hrd" as %Hrd.
    iModIntro.
    iMod "HV".
    iDestruct (ownVAL_Full with "Htk HV") as (V'') "#HV''".
    iDestruct "HV''" as %HV''; subst.
    iApply (wp_io with "[$HT]"); eauto.
    { apply Hinc. repeat econstructor; eauto. }
    iNext. iIntros (w) "[HT HTw]". iDestruct "HTw" as %HTw.
    rewrite (comm _ _ V'').
    iMod (PetriNet_delete with "HV Htk") as "HV".
    iMod (PetriNet_alloc _ (singVAL q) with "HV") as "[HV Htk]".
    assert (w = v'); subst.
    { eapply (Hrd _ _ _ _ [] [] []).
      - by apply HTw.
      - apply Hinc. repeat econstructor; eauto. }
    iMod ("Hcl" with "[HT HV]") as "_".
    iNext; iExists _, _; iFrame; iSplit; iPureIntro.
    - intros τ Hτ.
      apply Hinc.
      econstructor; eauto.
      by rewrite (comm _ _ V'').
    - intros t' u u' u'' τ τ' τ'' HT1 HT2.
      eapply (Hrd _ _ _ _ (_ :: _)); eauto.
    - iModIntro. by iApply ("HΦ" with "[$Htk]").
  Qed.

End PetriNet.

Arguments PetriNet _, {_}.

Section PetriNetInv.

  Context `{heapIG Σ, PlacesC}.

  Lemma PetriNetInv_alloc (N : PetriNet) E (V : (ofe_funUR (λ p, natUR))) :
    inG Σ (authUR (ofe_funUR (λ p : Places, natUR))) →
    ResultDet (Traces N V) →
    ownIO (Traces N V) ⊢
          |={E}=> ∃ `{PIG : !petrinetIG Σ}, PetriNetInv ∗ ownVAL V.
  Proof.
    iIntros (Hing Hrd) "HIO".
    iMod (@own_alloc Σ (authUR (ofe_funUR (λ p, natUR))) _ ((◯ V) ⋅ (● V)))
      as (γpn) "[Hofrag Hofull]".
    { rewrite auth_valid_eq; simpl; split; last done.
        by intros; rewrite right_id. }
    set (HIG := {| PNI_exclG := Hing; γPN := γpn; ThePetriNet := N|}).
    iMod (inv_alloc
            PetriNetN _
            (∃ V T, ownIO T ∗ FullVAL V ∗
                          ⌜∀ τ, Traces N V τ → T τ⌝ ∗ ⌜ResultDet T⌝)%I
            with "[Hofull HIO]") as "Hinv".
    { iNext; iExists _, _; iFrame; iSplit; iPureIntro; auto. }
    iModIntro; iExists _; iFrame.
  Qed.

End PetriNetInv.

Notation "V ⊎ W" := (ValPlus V W) (at level 50, left associativity).