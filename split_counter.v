From iris.algebra Require Export auth gmap excl big_op.
From iris.base_logic.lib Require Export saved_prop.
From iris.program_logic Require Export weakestpre lifting.
From iris.proofmode Require Import tactics.
From iris_io Require Import lang rules.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Definition create_counter :=
 Lam (Pair (Alloc (Nat 0)) (Alloc (Nat 0))).

Definition atomic_increment :=
 Rec (LetIn (Load (Var 1)) (If (CAS (Var 2) (Var 0) (BinOp Add (Var 0) (Nat 1))) Unit (App (Var 1) (Var 2)))).

Definition incr_left :=
 Lam (App atomic_increment (Fst (Var 0))).

Definition incr_right :=
 Lam (App atomic_increment (Snd (Var 0))).

Definition read :=
 Lam
   (LetIn Create_Pr
      (LetIn (Load (Fst (Var 1)))
         (LetIn (Load (Snd (Var 2)))
            (Seq
               (Assign_Pr (Var 2) (Var 0))
               (BinOp Add (Var 1) (Var 0)))))).

Class SplitIG Σ := splitIG {
   split_inG :> inG Σ (authUR (gmapUR positive (exclR (leibnizC (gname * nat)))));
   split_monotone_inG :> inG Σ (authUR (mnatUR));
}.

Definition splitΣ :=
  #[GFunctor (authUR (gmapUR positive (exclR (leibnizC (gname * nat)))));
      GFunctor (authUR (mnatUR))].

Global Instance subG_splitΣ Σ : subG splitΣ Σ → SplitIG Σ.
Proof. solve_inG. Qed.

Section counter.
  Context `{SplitIG Σ, heapIG Σ, savedPredG Σ nat}.

  Implicit Types split_name : (gname * (gname * gname)).

  Definition of_Readers (M : gmap positive (gname * nat)) :
    gmap positive (excl (leibnizC (gname * nat))) :=
    (λ r, Excl (r)) <$> M.

  Definition ownReaders split_name M := own split_name.1 (● (of_Readers M)).

  Definition ownReader split_name i γ n := own split_name.1 (◯ {[i := Excl (γ, n)]}).

  Definition counterN := nroot .@ "counter".

  Definition fullLeft split_name n := own split_name.2.1 (● n).

  Definition fragLeft split_name n := own split_name.2.1 (◯ n).

  Definition fullRight split_name n := own split_name.2.2 (● n).

  Definition fragRight split_name n := own split_name.2.2 (◯ n).

  Lemma update_fullLeft split_name n m :
    n ≤ m →
    fullLeft split_name n ==∗ fullLeft split_name m ∗ fragLeft split_name m.
  Proof.
    iIntros (Hnm) "Ho".
    iMod (own_update (A := authUR mnatUR) _ _ (● m ⋅ ◯ m) with "Ho") as "H";
    first by eapply (auth_update_alloc (A := mnatUR)), mnat_local_update.
    by rewrite own_op; iDestruct "H" as "[$ $]".
  Qed.

  Lemma update_fullRight split_name n m :
    n ≤ m →
    fullRight split_name n ==∗ fullRight split_name m ∗ fragRight split_name m.
  Proof.
    iIntros (Hnm) "Ho".
    iMod (own_update (A := authUR mnatUR) _ _ (● m ⋅ ◯ m) with "Ho") as "H";
    first by eapply (auth_update_alloc (A := mnatUR)), mnat_local_update.
    by rewrite own_op; iDestruct "H" as "[$ $]".
  Qed.

  Lemma left_frag_less split_name n m :
    fullLeft split_name n -∗ fragLeft split_name m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as
        %[Hrv%mnat_included _]%auth_valid_discrete; simpl in *.
    rewrite -> left_id_L in Hrv; last typeclasses eauto; trivial.
  Qed.

  Lemma right_frag_less split_name n m :
    fullRight split_name n -∗ fragRight split_name m -∗ ⌜m ≤ n⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as
        %[Hrv%mnat_included _]%auth_valid_discrete; simpl in *.
    rewrite -> left_id_L in Hrv; last typeclasses eauto; trivial.
  Qed.

  Definition except_counterN := ⊤ ∖ nclose counterN.
  Lemma except_counterN_eq : except_counterN = ⊤ ∖ nclose counterN.
  Proof. trivial. Qed.
  Typeclasses Opaque except_counterN.
  Opaque except_counterN.

  Definition reader_inv r v I :=
    (∃ ψ, saved_pred_own (fst r) ψ ∗
         if (decide (snd r < v)) then
           ψ (snd r)
         else
           I (snd r) ={except_counterN}=∗ ψ (snd r) ∗ I (snd r))%I.

  Definition CounterInv split_name l r I :=
    (∃ (lv rv : mnatUR) M, l ↦ (NatV lv) ∗ r ↦ (NatV rv) ∗
                  fullLeft split_name lv ∗ fullRight split_name rv ∗
                  I (lv + rv) ∗ ownReaders split_name M
                  ∗ [∗ map] i ↦ r ∈ M, reader_inv r (lv + rv) I)%I.

  Definition Counter split_name (c : val) (I : nat → iProp Σ) : iProp Σ:=
  (∃ l r, ⌜c = PairV (LocV l) (LocV r)⌝ ∗ inv counterN (CounterInv split_name l r I))%I.

  Lemma of_Readers_alloc split_name M γ n :
    ownReaders split_name M ==∗
    ∃ i, ⌜i ∉ dom (gset _) M⌝ ∗
           ownReaders split_name (<[i := (γ, n)]>M) ∗ ownReader split_name i γ n.
  Proof.
    iIntros "HM".
    set (fresh (dom (gset _) M)) as i.
    iMod (@own_update _ _ _ _ _ (● (of_Readers (<[ i := (γ, n)]>M)) ⋅
                                   ◯ ({[i := Excl (γ, n)]}))
            with "HM") as "[? ?]".
    { apply auth_update_alloc.
      rewrite /of_Readers fmap_insert /=.
      apply @alloc_singleton_local_update; last done.
      eapply (not_elem_of_dom (D := gset positive)).
      rewrite -> dom_fmap_L.
      apply is_fresh. }
    iModIntro; iExists _; iFrame.
    iPureIntro. apply is_fresh.
  Qed.

  Lemma of_Readers_dealloc split_name M i γ n :
    ownReaders split_name M -∗ ownReader split_name i γ n ==∗
    ownReaders split_name (delete i M).
  Proof.
    iIntros "HM Hi".
    iDestruct (own_valid_2 with "HM Hi") as %[HI HIvl]%auth_valid_discrete_2.
    specialize (HIvl i).
    apply @singleton_included in HI.
    destruct HI as [y [Hy1%leibniz_equiv Hy2]].
    rewrite Hy1 in HIvl. destruct y; last done.
    apply @Excl_included, leibniz_equiv in Hy2; subst.
    iCombine "HM" "Hi" as "HMi".
    iMod (@own_update _ _ _ _ _ (● (of_Readers (delete i M))) with "HMi")
      as "$"; auto.
    apply auth_update_dealloc.
    rewrite /of_Readers fmap_delete.
    apply @delete_singleton_local_update; typeclasses eauto.
  Qed.

  Lemma in_of_Readers split_name M i γ n :
    ownReaders split_name M -∗ ownReader split_name i γ n -∗
               ⌜M !! i = Some (γ, n)⌝.
  Proof.
    iIntros "HM Hi".
    iDestruct (own_valid_2 with "HM Hi") as %[HI HIvl]%auth_valid_discrete_2.
    iPureIntro.
    specialize (HIvl i).
    apply @singleton_included in HI.
    destruct HI as [y [Hy1%leibniz_equiv Hy2]].
    rewrite Hy1 in HIvl. destruct y; last done.
    apply @Excl_included, leibniz_equiv in Hy2; subst.
    rewrite /of_Readers lookup_fmap in Hy1; destruct (M !!i); by inversion Hy1.
  Qed.

  Theorem wp_create_counter I :
    {{{I 0}}} App create_counter Unit {{{v split_name, RET v; Counter split_name v I}}}.
  Proof.
    iIntros (F) "HI HF".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [PairLCtx _])); simpl.
    iApply wp_alloc; auto.
    iNext. iIntros (l) "Hl".
    iApply (wp_bind (fill [PairRCtx _])); simpl.
    iApply wp_alloc; auto.
    iNext. iIntros (r) "Hr".
    iMod (own_alloc (A := authUR (gmapUR positive (exclR (leibnizC (gname * nat))))) (● ∅))
      as (γ1) "He"; first done.
    iMod (own_alloc (A := authUR mnatUR) (● 0)) as (γ2) "He'"; first done.
    iMod (own_alloc (A := authUR mnatUR) (● 0)) as (γ3) "He''"; first done.
    iMod (inv_alloc counterN _ (CounterInv (γ1, (γ2, γ3)) l r I) with "[-HF]") as "HI".
    { iExists _, _, ∅; rewrite /ownReaders /of_Readers big_sepM_empty fmap_empty
                       /=; iFrame. }
    iApply wp_value.
    iApply "HF". iExists _, _; eauto.
  Qed.

  Lemma big_sepM_update `{!invG Σ} `{!EqDecision K} `{!Countable K}
        E (A : Type) (Φ Ψ : K → A → iProp Σ) (m : gmap K A) P :
    □ (∀ i x, P -∗ Φ i x ={E}=∗ P ∗ Ψ i x) -∗
      P -∗ ([∗ map] i ↦ x ∈ m, Φ i x) ={E}=∗ P ∗ [∗ map] i ↦ x ∈ m, Ψ i x.
  Proof.
    iIntros "#Hupd HP Hb".
    rewrite -(map_of_to_list m).
    pose proof (NoDup_fst_map_to_list m) as Hm.
    iInduction (map_to_list m) as [|[i x] m'] "IH" forall (Hm).
    - rewrite !big_sepM_empty; eauto.
    - rewrite map_of_list_cons.
      assert (map_of_list (M := gmap K A) m' !! i = None).
      { apply not_elem_of_map_of_list_1. by apply NoDup_cons_11 in Hm. }
      rewrite !big_sepM_insert //.
      iDestruct "Hb" as "[HΦ Hb]".
      iMod ("Hupd" with "HP HΦ") as "[HP $]".
      iApply ("IH" with "[] HP [$]").
      iPureIntro.
      eapply NoDup_cons_12; eauto.
  Qed.

  Theorem wp_incr_left split_name c I Q :
    {{{Counter split_name c I ∗ ∀ v, I v ={except_counterN}=∗ I (v +1) ∗ Q}}}
      App incr_left (of_val c)
    {{{RET UnitV; Q}}}.
  Proof.
    iIntros (F) "[#HInv Hvs] HF". iDestruct "HInv" as (l r ->) "HInv".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [AppRCtx (RecV _)])); simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    iLöb as "IH".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])); simpl.
    iInv counterN as (lv rv M) "(Hl & Hr & HI & HM & Hri)" "Hcl".
    iApply (wp_load with "Hl"). iNext. iIntros "Hl".
    iMod ("Hcl" with "[Hl Hr HI HM Hri]") as "_".
    { iNext; iExists _, _, _; iFrame. }
    iModIntro.
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [IfCtx _ _])); simpl.
    iApply (wp_bind (fill [CasRCtx (LocV _) (NatV _)])); simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    clear rv M.
    iInv counterN as (lv' rv M) "(Hl & Hr & Hlv & Hrv & HI & HM & Hri)" "Hcl".
    destruct (decide (lv = lv')); first subst.
    - iApply (wp_cas_suc with "Hl"); iNext; iIntros "Hl".
      iAssert (I (lv' + rv) ={⊤ ∖ ↑counterN}=∗ I (lv' + rv) ∗
               [∗ map] r ∈ M, reader_inv r ((lv' + 1) + rv) I)%I
        with "[Hri]" as "Hri'".
      { iIntros "HI".
        iMod (@big_sepM_update with "[] HI Hri") as "[$ $]"; eauto.
        iAlways. iIntros (_ x) "HI Hx". iDestruct "Hx" as (ψ) "[Hψ Hx]".
        rewrite /reader_inv /=.
        repeat destruct decide; simpl; try (by iFrame; eauto with omega).
        replace (x.2) with (lv' + rv) by omega.
        rewrite !except_counterN_eq.
        iMod ("Hx" with "HI") as "[Hx $]"; eauto. }
      iMod (update_fullLeft _ _ (lv' + 1) with "Hlv") as "[Hlv _]";
        auto with omega.
      iMod ("Hri'" with "HI") as "[HI Hri]".
      rewrite !except_counterN_eq.
      iMod ("Hvs" with "HI") as "[HI HQ]".
      iMod ("Hcl" with "[Hl Hr Hlv Hrv HI HM Hri]") as "_".
      { replace (lv' + rv + 1) with (lv' + 1 + rv) by omega.
        iNext; iExists _, _, _; iFrame. }
      iModIntro.
      iApply wp_pure_step_later; auto. iNext.
      by iApply wp_value; iApply "HF".
    - iApply (wp_cas_fail with "Hl"); first congruence; iNext; iIntros "Hl".
      iMod ("Hcl" with "[Hl Hr Hlv Hrv HI HM Hri]") as "_".
      { iNext; iExists _, _, _; iFrame. }
      iModIntro.
      iApply wp_pure_step_later; auto. iNext.
      iApply ("IH" with "Hvs"); eauto.
  Qed.

  Theorem wp_incr_right split_name c I Q :
    {{{Counter split_name c I ∗ ∀ v, I v ={except_counterN}=∗ I (v +1) ∗ Q}}}
      App incr_right (of_val c)
    {{{RET UnitV; Q}}}.
  Proof.
    iIntros (F) "[#HInv Hvs] HF". iDestruct "HInv" as (l r ->) "HInv".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [AppRCtx (RecV _)])); simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    iLöb as "IH".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])); simpl.
    iInv counterN as (lv rv M) "(Hl & Hr & HI & HM & Hri)" "Hcl".
    iApply (wp_load with "Hr"). iNext. iIntros "Hr".
    iMod ("Hcl" with "[Hl Hr HI HM Hri]") as "_".
    { iNext; iExists _, _, _; iFrame. }
    iModIntro.
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [IfCtx _ _])); simpl.
    iApply (wp_bind (fill [CasRCtx (LocV _) (NatV _)])); simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    clear lv M.
    iInv counterN as (lv rv' M) "(Hl & Hr & Hlv & Hrv & HI & HM & Hri)" "Hcl".
    destruct (decide (rv = rv')); first subst.
    - iApply (wp_cas_suc with "Hr"); iNext; iIntros "Hr".
      iAssert (I (lv + rv') ={⊤ ∖ ↑counterN}=∗ I (lv + rv') ∗
               [∗ map] r ∈ M, reader_inv r (lv + (rv' + 1)) I)%I
        with "[Hri]" as "Hri'".
      { iIntros "HI".
        iMod (@big_sepM_update with "[] HI Hri") as "[$ $]"; eauto.
        iAlways. iIntros (_ x) "HI Hx". iDestruct "Hx" as (ψ) "[Hψ Hx]".
        rewrite /reader_inv /=.
        repeat destruct decide; simpl; try (by iFrame; eauto with omega).
        replace (x.2) with (lv + rv') by omega.
        rewrite !except_counterN_eq.
        iMod ("Hx" with "HI") as "[Hx $]"; eauto. }
      iMod (update_fullRight _ _ (rv' + 1) with "Hrv") as "[Hrv _]";
        auto with omega.
      iMod ("Hri'" with "HI") as "[HI Hri]".
      rewrite !except_counterN_eq.
      iMod ("Hvs" with "HI") as "[HI HQ]".
      iMod ("Hcl" with "[Hl Hr Hlv Hrv HI HM Hri]") as "_".
      { replace (lv + rv' + 1) with (lv + (rv' + 1)) by omega.
        iNext; iExists _, _, _; iFrame. }
      iModIntro.
      iApply wp_pure_step_later; auto. iNext.
      by iApply wp_value; iApply "HF".
    - iApply (wp_cas_fail with "Hr"); first congruence; iNext; iIntros "Hr".
      iMod ("Hcl" with "[Hl Hr Hlv Hrv HI HM Hri]") as "_".
      { iNext; iExists _, _, _; iFrame. }
      iModIntro.
      iApply wp_pure_step_later; auto. iNext.
      iApply ("IH" with "Hvs"); eauto.
  Qed.

  Theorem wp_read split_name c I ψ :
    {{{Counter split_name c I ∗ ∀ v, I v ={except_counterN}=∗ ψ v ∗ I v}}}
      App read (of_val c)
    {{{v, RET (NatV v); ψ v}}}.
  Proof.
    iIntros (F) "[#HInv Hvs] HF". iDestruct "HInv" as (l r ->) "HInv".
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])); simpl.
    iApply (wp_create_pr _ (λ μ, ∃ n, Shead μ = (NatV n))); trivial.
    { by exists (Sconst (NatV 0)), 0. }
    iNext; iIntros (p). iDestruct 1 as (μ) "Hμ".
    iDestruct (cpvar_contains with "Hμ") as %[n Hμ].
    iApply wp_pure_step_later; auto. iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])); simpl.
    iApply (wp_bind (fill [LoadCtx])); simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    iInv counterN as (lv rv M) "(Hl & Hr & Hlv & Hrv & HI & HM & Hri)" "Hcl".
    iApply (wp_load with "Hl"). iNext. iIntros "Hl".
    iMod (saved_pred_alloc ψ) as (γ) "#Hψ".
    iMod (of_Readers_alloc _ _ γ (lv + max n rv) with "HM")
      as (m Hm) "[HM Hreader]".
    iAssert (reader_inv (γ, lv + max n rv) (lv + rv) I)%I with "[Hvs]" as "Hrinv".
    { rewrite /reader_inv /=; destruct decide; try lia.
      iExists _; iFrame "#". iApply "Hvs". }
    iMod (update_fullRight _ rv rv with "Hrv") as "[Hrv Hrvfrag]"; auto.
    iMod (update_fullLeft _ lv lv with "Hlv") as "[Hlv Hlvfrag]"; auto.
    iMod ("Hcl" with "[Hl Hr Hlv Hrv HI HM Hri Hrinv]") as "_".
    { iNext; iExists _, _, (<[_ := _]>M); iFrame.
      rewrite big_sepM_insert; first by iFrame.
      eapply (not_elem_of_dom (D := gset positive)); trivial. }
    iModIntro.
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [LetInCtx _])); simpl.
    iApply (wp_bind (fill [LoadCtx])); simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    iInv counterN as (lv' rv' M') "(Hl & Hr & Hlv & Hrv & HI & HM & Hri)" "Hcl".
    iApply (wp_load with "Hr"). iNext. iIntros "Hr".
    iDestruct (left_frag_less with "Hlv Hlvfrag") as %Hlv.
    iDestruct (right_frag_less with "Hrv Hrvfrag") as %Hrv.
    iDestruct (in_of_Readers with "HM Hreader") as %Hrd.
    rewrite (big_sepM_delete _ M' m (γ, lv + n `max` rv)) //.
    iMod (of_Readers_dealloc with "HM Hreader") as "HM".
    iDestruct "Hri" as "[Hm Hri]".
    iDestruct "Hm" as (ψ') "[#Hψ' Hm]"; simpl.
    iDestruct (saved_pred_agree _ _ _ (lv + n `max` rv) with "Hψ Hψ'") as "Hψeq".
    destruct decide.
    - iMod ("Hcl" with "[Hl Hr Hlv Hrv HI HM Hri]") as "_".
      { iNext; iExists _, _, (delete m M'); iFrame. }
      iModIntro.
      iApply wp_pure_step_later; auto. iNext. asimpl.
      iApply (wp_bind (fill [SeqCtx _])); simpl.
      iApply (wp_assign_pr with "[$Hμ]").
      { iExists (Sconst (NatV 0)); iPureIntro. by exists rv'. }
      iNext.
      iIntros "[Heq _]". iDestruct "Heq" as %Heq. rewrite Hμ in Heq; simplify_eq.
      iApply wp_pure_step_later; auto. iNext.
      iApply wp_pure_step_later; auto. iNext.
      iApply wp_value. iApply "HF". replace (max n rv) with n by lia.
      by iRewrite "Hψeq".
    - destruct (decide (n = rv')); subst.
      + replace (max rv' rv) with rv' by by rewrite PeanoNat.Nat.max_l.
        assert (lv' = lv :> nat) by lia; subst.
        rewrite except_counterN_eq.
        iMod ("Hm" with "HI") as "[Hv HI]".
        iMod ("Hcl" with "[Hl Hr Hlv Hrv HI HM Hri]") as "_".
        { iNext; iExists _, _, (delete m M'); iFrame. }
        iModIntro.
        iApply wp_pure_step_later; auto. iNext. asimpl.
        iApply (wp_bind (fill [SeqCtx _])); simpl.
        iApply (wp_assign_pr with "[$Hμ]").
        { iExists (Sconst (NatV 0)); iPureIntro. by exists rv'. }
        iNext.
        iIntros "[Heq _]". iDestruct "Heq" as %Heq. rewrite Hμ in Heq; simplify_eq.
        iApply wp_pure_step_later; auto. iNext.
        iApply wp_pure_step_later; auto. iNext.
        iApply wp_value. iApply "HF".
        by iRewrite "Hψeq".
      + iMod ("Hcl" with "[Hl Hr Hlv Hrv HI HM Hri]") as "_".
        { iNext; iExists _, _, (delete m M'); iFrame. }
        iModIntro.
        iApply wp_pure_step_later; auto. iNext. asimpl.
        iApply (wp_bind (fill [SeqCtx _])); simpl.
        iApply (wp_assign_pr with "[$Hμ]").
        { iExists (Sconst (NatV 0)); iPureIntro. by exists rv'. }
        iNext.
        iIntros "[Heq _]". iDestruct "Heq" as %Heq. rewrite Hμ in Heq; simplify_eq.
Qed.

End counter.