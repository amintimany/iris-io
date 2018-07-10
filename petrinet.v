From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris_io Require Export lang rules full_erasure.
From iris.proofmode Require Import tactics.

Require Import Coq.Logic.FunctionalExtensionality.

Section PetriNet.

  Class PlacesC := placesC
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

  Definition petrinetΣ := #[GFunctor (authUR (ofe_funUR (λ p : Places, natUR)))].

  Global Instance subG_petrinetΣ Σ :
    subG petrinetΣ Σ →
    inG Σ (authUR (ofe_funUR (λ p : Places, natUR))).
  Proof. solve_inG. Qed.

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

  Global Instance : Assoc eq ValPlus.
  Proof.
    intros x y z. extensionality u; unfold ValPlus; omega.
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

  Lemma Traces_prefix_closed N V : prefix_closed (Traces N V).
  Proof.
    intros τ τ' Htr.
    remember (τ ++ τ') as ττ'. revert τ τ' Heqττ'.
    induction Htr; intros τ1 τ2 Heqττ.
    - destruct τ1; inversion Heqττ; econstructor.
    - destruct τ1.
      + destruct τ2; inversion Heqττ; subst; econstructor.
      + inversion Heqττ; subst.
        econstructor; eauto.
    - econstructor; eauto.
    - econstructor; eauto.
    - econstructor 5; eauto.
  Qed.

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

  Lemma petrinet_split p q1 q2 :
    ThePetriNet (SplitTr p q1 q2) → Token p ={⊤}=∗ Token q1 ∗ Token q2.
  Proof.
    iIntros (Hsp) "[Htk #Hinv]".
    iInv PetriNetN as ">Hpt" "Hcl".
    iDestruct "Hpt" as (V T) "(HT & HV & Hinc & Hrd)".
    iDestruct "Hinc" as %Hinc. iDestruct "Hrd" as %Hrd.
    iDestruct (ownVAL_Full with "Htk HV") as %[V'' ?]; subst.
    rewrite (comm _ _ V'').
    iMod (PetriNet_delete with "HV Htk") as "HV".
    iMod (PetriNet_alloc _ (singVAL q1) with "HV") as "[HV Hq1]".
    iMod (PetriNet_alloc _ (singVAL q2) with "HV") as "[HV Hq2]".
    iMod ("Hcl" with "[HT HV]") as "_".
    { iNext. iExists _, _; iFrame. iSplit; iPureIntro; auto.
      rewrite -assoc (comm _ V'').
      intros τ Hτ. apply Hinc. eapply SplitTR; eauto. }
    by iFrame; iFrame "#".
  Qed.

  Lemma petrinet_join p1 p2 q :
    ThePetriNet (JoinTr p1 p2 q) → Token p1 ∗ Token p2 ={⊤}=∗ Token q.
  Proof.
    iIntros (Hjn) "[[Hp1 #Hinv] [Hp2 _]]".
    iInv PetriNetN as ">Hpt" "Hcl".
    iDestruct "Hpt" as (V T) "(HT & HV & Hinc & Hrd)".
    iDestruct "Hinc" as %Hinc. iDestruct "Hrd" as %Hrd.
    iDestruct (ownVAL_Full with "Hp1 HV") as %[V'' ?]; subst.
    rewrite (comm _ _ V'').
    iMod (PetriNet_delete with "HV Hp1") as "HV".
    iDestruct (ownVAL_Full with "Hp2 HV") as %[V3 ?]; subst.
    rewrite (comm _ _ V3).
    iMod (PetriNet_delete with "HV Hp2") as "HV".
    iMod (PetriNet_alloc _ (singVAL q) with "HV") as "[HV Hq]".
    iMod ("Hcl" with "[HT HV]") as "_".
    { iNext. iExists _, _; iFrame. iSplit; iPureIntro; auto.
      rewrite comm.
      intros τ Hτ. apply Hinc. rewrite assoc. eapply JoinTR; eauto. }
    by iFrame; iFrame "#".
  Qed.

  Lemma petrinet_noop p q : ThePetriNet (NoOpTr p q) → Token p ={⊤}=∗ Token q.
  Proof.
    iIntros (Hjn) "[Hp1 #Hinv]".
    iInv PetriNetN as ">Hpt" "Hcl".
    iDestruct "Hpt" as (V T) "(HT & HV & Hinc & Hrd)".
    iDestruct "Hinc" as %Hinc. iDestruct "Hrd" as %Hrd.
    iDestruct (ownVAL_Full with "Hp1 HV") as %[V'' ?]; subst.
    rewrite (comm _ _ V'').
    iMod (PetriNet_delete with "HV Hp1") as "HV".
    iMod (PetriNet_alloc _ (singVAL q) with "HV") as "[HV Hq]".
    iMod ("Hcl" with "[HT HV]") as "_".
    { iNext. iExists _, _; iFrame. iSplit; iPureIntro; auto.
      rewrite comm.
      intros τ Hτ. apply Hinc. eapply NoOpTR; eauto. }
    by iFrame; iFrame "#".
  Qed.

  Lemma wp_petrinet_io t e v p v' q :
    IntoVal e v →
    ThePetriNet (IOTr p t v v' q) →
    {{{Token p}}} IO (IOtag t) e {{{RET v'; Token q}}}.
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

  Lemma PetriNetInv_alloc
        `{inG Σ (authUR (ofe_funUR (λ p : Places, natUR)))} (N : PetriNet)
        E (V : (ofe_funUR (λ p, natUR))) :
    ResultDet (Traces N V) →
    ownIO (Traces N V) ⊢
          |={E}=> ∃ γpn, let _ := {| γPN := γpn; ThePetriNet := N |} in
                        PetriNetInv ∗ ownVAL V.
  Proof.
    iIntros (Hrd) "HIO".
    iMod (@own_alloc Σ (authUR (ofe_funUR (λ p, natUR))) _ ((◯ V) ⋅ (● V)))
      as (γpn) "[Hofrag Hofull]".
    { rewrite auth_valid_eq; simpl; split; last done.
        by intros; rewrite right_id. }
    set (HIG := {| PNI_exclG := _; γPN := γpn; ThePetriNet := N|}).
    iMod (inv_alloc
            PetriNetN _
            (∃ V T, ownIO T ∗ FullVAL V ∗
                          ⌜∀ τ, Traces N V τ → T τ⌝ ∗ ⌜ResultDet T⌝)%I
            with "[Hofull HIO]") as "Hinv".
    { iNext; iExists _, _; iFrame; iSplit; iPureIntro; auto. }
    iModIntro. iExists _; iFrame.
  Qed.

End PetriNetInv.

Notation "V ⊎ W" := (ValPlus V W) (at level 50, left associativity).