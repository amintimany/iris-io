From iris_io Require Export lang rules.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre lifting.


Fixpoint of_list (l : list val) :=
  match l with
    [] => InjLV Plang.UnitV
  | v :: l' => InjRV (PairV v (of_list l'))
  end.

Global Instance of_list_inj : Inj eq eq of_list.
Proof.
  intros x.
  induction x => y Heq; first by destruct y.
  destruct y; first done.
  inversion Heq; subst.
  f_equal. by apply IHx.
Qed.


Definition append :=
  Rec
    (Lam
       (Case
          (Var 2) (Var 1)
          (InjR
             (Pair (Fst (Var 0)) (App (App (Var 2) (Snd (Var 0))) (Var 1)))
          )
       )
    ).

Lemma append_closed f : append.[f] = append.
Proof. by asimpl. Qed.

Hint Rewrite append_closed : autosubst.

Lemma append_eq :
  append = Rec
             (Lam
                (Case
                   (Var 2) (Var 1)
                   (InjR
                      (Pair (Fst (Var 0)) (App (App (Var 2) (Snd (Var 0))) (Var 1)))
                   )
                )
             ).
Proof. trivial. Qed.

Typeclasses Opaque append.
Global Opaque append.

Lemma wp_append `{heapIG Σ} l l' :
  {{{True}}} (App (App append (of_val (of_list l))) (of_val (of_list l')))
          {{{w, RET w; ⌜w = of_list (l ++ l')⌝}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iLöb as "IH" forall (Φ l).
  rewrite append_eq.
  iApply (wp_bind (fill [AppLCtx _])).
  iApply wp_pure_step_later; auto.
  rewrite -append_eq.
  iNext. asimpl.
  iApply wp_value. simpl.
  iApply wp_pure_step_later; auto.
  iNext. asimpl.
  destruct l.
  - simpl. iApply wp_pure_step_later; eauto.
    iNext. asimpl. iApply wp_value. by iApply "HΦ".
  - simpl. iApply wp_pure_step_later; auto.
    iNext. asimpl.
    iApply (wp_bind (fill [InjRCtx])).
    iApply (wp_bind (fill [PairLCtx _])).
    iApply wp_pure_step_later; auto.
    iNext; iApply wp_value. simpl.
    iApply (wp_bind (fill [PairRCtx _])).
    rewrite append_eq.
    iApply (wp_bind (fill [AppRCtx (RecV _); AppLCtx _])).
    iApply wp_pure_step_later; auto.
    iNext; iApply wp_value; simpl.
    iApply wp_wand_r; iSplitR.
    { iApply ("IH" $! (λ s, ⌜s = of_list (l ++ l')⌝))%I. iNext.
        by iIntros (w Hw); subst w. }
    simpl.
    iIntros (w) "%"; subst; simpl.
    do 2 iApply wp_value.
      by iApply "HΦ".
Qed.

Definition snoc :=
  Rec
    (Lam
       (Case
          (Var 2) (InjR (Pair (Var 1) (InjL Plang.Unit)))
          (InjR
             (Pair (Fst (Var 0)) (App (App (Var 2) (Snd (Var 0))) (Var 1)))
          )
       )
    ).

Lemma snoc_closed f : snoc.[f] = snoc.
Proof. by asimpl. Qed.

Hint Rewrite snoc_closed : autosubst.

Lemma snoc_eq :
  snoc =
  Rec
    (Lam
       (Case
          (Var 2) (InjR (Pair (Var 1) (InjL Plang.Unit)))
          (InjR
             (Pair (Fst (Var 0)) (App (App (Var 2) (Snd (Var 0))) (Var 1)))
          )
       )
    ).
Proof. trivial. Qed.

Typeclasses Opaque snoc.
Global Opaque snoc.

Lemma wp_snoc `{heapIG Σ} l u :
  {{{True}}} (App (App snoc (of_val (of_list l))) (of_val u))
          {{{w, RET w; ⌜w = of_list (l ++ [u])⌝}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iLöb as "IH" forall (Φ l).
  rewrite snoc_eq.
  iApply (wp_bind (fill [AppLCtx _])).
  iApply wp_pure_step_later; auto.
  rewrite -snoc_eq.
  iNext. asimpl.
  iApply wp_value. simpl.
  iApply wp_pure_step_later; auto.
  iNext. asimpl.
  destruct l.
  - simpl. iApply wp_pure_step_later; eauto.
    iNext. asimpl. iApply wp_value. by iApply "HΦ".
  - simpl. iApply wp_pure_step_later; auto.
    iNext. asimpl.
    iApply (wp_bind (fill [InjRCtx])).
    iApply (wp_bind (fill [PairLCtx _])).
    iApply wp_pure_step_later; auto.
    iNext; iApply wp_value. simpl.
    iApply (wp_bind (fill [PairRCtx _])).
    rewrite snoc_eq.
    iApply (wp_bind (fill [AppRCtx (RecV _); AppLCtx _])).
    iApply wp_pure_step_later; auto.
    iNext; iApply wp_value; simpl.
    iApply wp_wand_r; iSplitR.
    { iApply ("IH" $! (λ s, ⌜s = of_list (l ++ [u])⌝))%I. iNext.
        by iIntros (w Hw); subst w. }
    simpl.
    iIntros (w) "%"; subst; simpl.
    do 2 iApply wp_value. by iApply "HΦ".
Qed.

Definition list_length :=
  Rec
    (Case
       (Var 1)
       (#n 0)
       (BinOp Plang.Add (#n 1) (App (Var 1) (Snd (Var 0))))
    ).

Lemma list_length_closed f : list_length.[f] = list_length.
Proof. by asimpl. Qed.

Hint Rewrite list_length_closed : autosubst.

Lemma list_length_eq :
  list_length =
  Rec
    (Case
       (Var 1)
       (#n 0)
       (BinOp Plang.Add (#n 1) (App (Var 1) (Snd (Var 0))))
    ).
Proof. trivial. Qed.

Typeclasses Opaque list_length.
Global Opaque list_length.

Lemma wp_list_length `{heapIG Σ} l :
  {{{True}}} (App list_length (of_val (of_list l)))
          {{{w, RET w; ⌜w = (#nv (length l))⌝}}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iLöb as "IH" forall (Φ l).
  rewrite list_length_eq.
  iApply wp_pure_step_later; auto.
  rewrite -list_length_eq.
  iNext. asimpl.
  destruct l.
  - simpl. iApply wp_pure_step_later; eauto.
    iNext. asimpl. iApply wp_value. by iApply "HΦ".
  - simpl. iApply wp_pure_step_later; auto.
    iNext. asimpl.
    iApply (wp_bind (fill [BinOpRCtx _ (#nv _)])).
    rewrite list_length_eq.
    iApply (wp_bind (fill [AppRCtx (RecV _)])).
    rewrite -list_length_eq.
    iApply wp_pure_step_later; auto.
    iNext; iApply wp_value; simpl.
    rewrite -list_length_eq.
    iApply wp_wand_r; iSplitR.
    { iApply ("IH" $! (λ s, ⌜s = #nv (length l)⌝))%I. iNext.
        by iIntros (w Hw); subst w. }
    simpl.
    iIntros (w) "%"; subst; simpl.
    iApply wp_pure_step_later; auto.
    iNext.
    iApply wp_value. by iApply "HΦ".
Qed.
