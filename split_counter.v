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
}.

Definition splitΣ :=
  #[GFunctor (authUR (gmapUR nat (exclR (leibnizC (gname * nat)))))].

Global Instance subG_splitΣ Σ :
  subG splitΣ Σ → inG Σ (authUR (gmapUR nat (exclR (leibnizC (gname * nat))))).
Proof. solve_inG. Qed.

Section counter.
  Context `{SplitIG Σ, heapIG Σ, savedPredG Σ nat}.

  Fixpoint of_Readers_rec (M : list (gname * nat)) i :
    gmap nat (excl (leibnizC (gname * nat))) :=
    match M with
    | [] => ∅
    | r :: M' => <[i := Excl r]>(of_Readers_rec M' (S i))
    end.

  Definition of_Readers M := of_Readers_rec M 0.

  Definition ownReaders split_name M := own split_name (● (of_Readers M)).

  Definition ownReader split_name i γ n := own split_name (◯ {[i := Excl (γ, n)]}).

  Definition counterN := nroot .@ "counter".

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
    (∃ lv rv M, l ↦ (NatV lv) ∗ r ↦ (NatV rv) ∗ I (lv + rv)
                  ∗ ownReaders split_name M
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
      as (split_name) "He"; first done.
    iMod (inv_alloc counterN _ (CounterInv split_name l r I) with "[-HF]") as "HI".
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
    iInv counterN as (lv' rv M) "(Hl & Hr & HI & HM & Hri)" "Hcl".
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
      iMod ("Hcl" with "[Hl Hr HI HM Hri]") as "_".
      { replace (lv' + rv + 1) with (lv' + 1 + rv) by omega.
        iNext; iExists _, _, _; iFrame. }
      iModIntro.
      iApply wp_pure_step_later; auto. iNext.
      by iApply wp_value; iApply "HF".
    - iApply (wp_cas_fail with "Hl"); first congruence; iNext; iIntros "Hl".
      iMod ("Hcl" with "[Hl Hr HI HM Hri]") as "_".
      { iNext; iExists _, _, _; iFrame. }
      iModIntro.
      iApply wp_pure_step_later; auto. iNext.
      iApply ("IH" with "Hvs"); eauto.
  Qed.

