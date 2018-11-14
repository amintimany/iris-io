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
 Rec (LetIn (Load (Var 0)) (If (CAS (Var 1) (Var 0) (BinOp Add (Var 0) (Nat 1))) Unit (App (Var 2) (Var 1)))).

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

  Definition of_Readers (M : gmap nat (gname * nat)) :
    gmap nat (excl (leibnizC (gname * nat))) :=
    (λ r, Excl (r)) <$> M.

  Definition ownReaders split_name M := own split_name (● (of_Readers M)).

  Definition ownReader split_name i γ n := own split_name (◯ {[i := Excl (γ, n)]}).

  Definition counterN := nroot .@ "counter".

  Definition reader_inv r v I :=
    (∃ ψ, saved_pred_own (fst r) ψ ∗
         if (decide (snd r < v)) then
           I (snd r) ={⊤ ∖ nclose counterN}=∗ ψ (snd r) ∗ I (snd r)
         else
           ψ (snd r))%I.

  Definition CounterInv split_name l r I :=
    (∃ lv rv M, l ↦ (NatV lv) ∗ r ↦ (NatV rv) ∗ I (lv + rv)
                  ∗ ownReaders split_name M
                  ∗ [∗ map] i ↦ r ∈ M, reader_inv r (lv + rv) I)%I.

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
    { iExists _, _, ∅; rewrite /ownReaders /of_Readers fmap_empty big_sepM_empty;
        iFrame. }
    iApply wp_value.
    iApply "HF". iExists _, _; eauto.
  Qed.





