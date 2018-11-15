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
   split_inG :> inG Σ (authUR (gmapUR nat (exclR (leibnizC (gname * nat)))));
   split_monotone_inG :> inG Σ (authUR (mnatUR));
}.

Definition splitΣ :=
  #[GFunctor (authUR (gmapUR nat (exclR (leibnizC (gname * nat)))));
      GFunctor (authUR (mnatUR))].

Global Instance subG_splitΣ Σ : subG splitΣ Σ → SplitIG Σ.
Proof. solve_inG. Qed.

Section counter.
  Context `{SplitIG Σ, heapIG Σ, savedPredG Σ nat}.

  Implicit Types split_name : (gname * gname).

  Fixpoint of_Readers_rec (M : list (gname * nat)) i :
    gmap nat (excl (leibnizC (gname * nat))) :=
    match M with
    | [] => ∅
    | r :: M' => {[i := Excl r]} ⋅ (of_Readers_rec M' (S i))
    end.

  Lemma of_Readers_dom M i n : n ∈ dom (gset _) (of_Readers_rec M i) → i ≤ n.
  Proof.
    revert i; induction M => i;
    rewrite /= ?dom_empty; first done.
    rewrite dom_op elem_of_union dom_singleton elem_of_singleton.
    intros [Hn|Hn]; subst; auto.
    cut (S i ≤ n); first omega; auto.
  Qed.

  Lemma of_Readers_dom' M i n :
    n ∈ dom (gset _) (of_Readers_rec M i) → n < i + length M.
  Proof.
    revert i; induction M => i;
    rewrite /= ?dom_empty; first done.
    rewrite dom_op elem_of_union dom_singleton elem_of_singleton.
    intros [Hn|Hn]; subst; auto with omega.
    cut (n < S i + length M); first omega; auto.
  Qed.

  Lemma of_Readers_app M N i :
    of_Readers_rec (M ++ N) i = (of_Readers_rec N (i + length M)) ⋅ (of_Readers_rec M i).
  Proof.
    revert N i.
    induction M => N i.
    - by rewrite /= right_id_L; replace (i + 0) with i by omega.
    - rewrite /= IHM. replace (S i + length M) with (i + S (length M)) by omega.
      rewrite !assoc_L. f_equal. rewrite (comm_L op) //.
  Qed.

  Definition of_Readers M := of_Readers_rec M 0.

  Definition ownReaders split_name M := own split_name.1 (● (of_Readers M)).

  Definition ownReader split_name i γ n := own split_name.1 (◯ {[i := Excl (γ, n)]}).

  Definition counterN := nroot .@ "counter".

  Definition fullRight split_name n := own split_name.2 (● n).

  Definition fragRight split_name n := own split_name.2 (◯ n).

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
    (∃ lv (rv : mnatUR) M, l ↦ (NatV lv) ∗ r ↦ (NatV rv) ∗ fullRight split_name rv ∗
                  I (lv + rv) ∗ ownReaders split_name M
                  ∗ [∗ list] r ∈ M, reader_inv r (lv + rv) I)%I.

  Definition Counter split_name (c : val) (I : nat → iProp Σ) : iProp Σ:=
  (∃ l r, ⌜c = PairV (LocV l) (LocV r)⌝ ∗ inv counterN (CounterInv split_name l r I))%I.

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
    iMod (own_alloc (A := authUR (gmapUR nat (exclR (leibnizC (gname * nat))))) (● ∅))
      as (γ1) "He"; first done.
    iMod (own_alloc (A := authUR mnatUR) (● 0)) as (γ2) "He'"; first done.
    iMod (inv_alloc counterN _ (CounterInv (γ1, γ2) l r I) with "[-HF]") as "HI".
    { iExists _, _, []; rewrite /ownReaders /=; iFrame. }
    iApply wp_value.
    iApply "HF". iExists _, _; eauto.
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
    iInv counterN as (lv' rv M) "(Hl & Hr & Hrv & HI & HM & Hri)" "Hcl".
    destruct (decide (lv = lv')); first subst.
    - iApply (wp_cas_suc with "Hl"); iNext; iIntros "Hl".
      iAssert (I (lv' + rv) ={⊤ ∖ ↑counterN}=∗ I (lv' + rv) ∗
               [∗ list] r ∈ M, reader_inv r ((lv' + 1) + rv) I)%I
        with "[Hri]" as "Hri'".
      { iIntros "HI".
        iInduction M as [|x M] "IHM"; simpl; first by iFrame.
        iDestruct "Hri" as "[Hx HM]". iDestruct "Hx" as (ψ) "[Hψ Hx]".
        iMod ("IHM" with "HM HI") as "[HI $]".
        rewrite /reader_inv /=.
        repeat destruct decide; simpl; try (by iFrame; eauto with omega).
        replace (x.2) with (lv' + rv) by omega.
        rewrite !except_counterN_eq.
        iMod ("Hx" with "HI") as "[Hx $]"; eauto. }
      iMod ("Hri'" with "HI") as "[HI Hri]".
      rewrite !except_counterN_eq.
      iMod ("Hvs" with "HI") as "[HI HQ]".
      iMod ("Hcl" with "[Hl Hr Hrv HI HM Hri]") as "_".
      { replace (lv' + rv + 1) with (lv' + 1 + rv) by omega.
        iNext; iExists _, _, _; iFrame. }
      iModIntro.
      iApply wp_pure_step_later; auto. iNext.
      by iApply wp_value; iApply "HF".
    - iApply (wp_cas_fail with "Hl"); first congruence; iNext; iIntros "Hl".
      iMod ("Hcl" with "[Hl Hr Hrv HI HM Hri]") as "_".
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
    iInv counterN as (lv rv M) "(Hl & Hr & Hrv & HI & HM & Hri)" "Hcl".
    iApply (wp_load with "Hl"). iNext. iIntros "Hl".
    iMod (saved_pred_alloc ψ) as (γ) "#Hψ".
    iMod (@own_update _ _ _ _ _ (● (of_Readers (M ++ [(γ, lv + max n rv)])) ⋅
                                   ◯ ({[length M := Excl (γ, lv + max n rv)]}))
            with "HM") as "HM".
    { rewrite /of_Readers of_Readers_app /= right_id_L.
      apply auth_update_alloc.
      rewrite -insert_singleton_op; last first.
      - eapply (not_elem_of_dom (D := gset _)).
        intros ?%of_Readers_dom'; omega.
      - apply: alloc_singleton_local_update; last done.
        eapply (not_elem_of_dom (D := gset _)).
        intros ?%of_Readers_dom'; omega. }
    iDestruct "HM" as "[HM Hreader]".
    iAssert (reader_inv (γ, lv + max n rv) (lv + rv) I)%I with "[Hvs]" as "Hrinv".
    { rewrite /reader_inv /=; destruct decide; try lia.
      iExists _; iFrame "#". iApply "Hvs". }
    iMod (@own_update _ _ _ _ _ (● rv ⋅ ◯ rv) with "Hrv") as "Hrv".
    { apply (auth_update_alloc).
      cut ((rv, ε) ~l~> (max rv rv, max rv ε));
        first replace (max rv rv) with rv by (by rewrite Nat.max_id);
        first replace (max rv ε) with rv by (by rewrite PeanoNat.Nat.max_0_r);
        trivial.
      apply (@op_local_update mnatUR) => ?. admit. }
    iDestruct "Hrv" as "[Hrv Hrvfrag]".
    iMod ("Hcl" with "[Hl Hr Hrv HI HM Hri Hrinv]") as "_".
    { by iNext; iExists _, _, (M ++ [_]); iFrame. }
    iModIntro.
    iApply wp_pure_step_later; auto. iNext.
    iApply (wp_bind (fill [LetInCtx _])); simpl.
    iApply (wp_bind (fill [LoadCtx])); simpl.
    iApply wp_pure_step_later; auto. iNext.
    iApply wp_value; simpl.
    iInv counterN as (lv' rv' M') "(Hl & Hr & Hrv & HI & HM & Hri)" "Hcl".
    iApply (wp_load with "Hr"). iNext. iIntros "Hr".
    iDestruct (own_valid_2 with "Hrvfrag Hrv") as
        %[Hrv%mnat_included _]%auth_valid_discrete; simpl in *.
    rewrite -> right_id_L in Hrv; last typeclasses eauto.
    
