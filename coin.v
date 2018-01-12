From iris.program_logic Require Export weakestpre lifting.
From iris.proofmode Require Import tactics.
From iris_io Require Import lang rules.
Require Import Coq.Logic.FunctionalExtensionality.


CoFixpoint str_boolV (s : Stream bool) :=
  {| Shead := BoolV (Shead s); Stail := str_boolV (Stail s) |}.

CoFixpoint str_bool (s : Stream bool) :=
  {| Shead := Bool (Shead s); Stail := str_bool (Stail s) |}.

Lemma str_bool_vals (x : Stream bool) :
  ∃ s : Stream val, proph_to_expr s = str_bool x.
Proof.
  exists (str_boolV x).
  apply Seq_eq.
  revert x. cofix IH => x.
  rewrite [str_bool _]Stream_unfold; rewrite [proph_to_expr _]Stream_unfold.
  destruct x; simpl.
  econstructor; auto.
Qed.

Lemma str_bool_ent (n : nat) (s s' : Stream val) :
    Elem (proph_to_expr s) str_bool →
    Elem (proph_to_expr s') str_bool →
    Elem (proph_to_expr (take_nth_from n s s')) str_bool.
Proof.
  intros [x Hx] [y Hy].
  exists (take_nth_from n x y).
  revert s s' x y Hx Hy; induction n => s s' x y.
  - destruct x as [xh xt]; destruct y as [yh yt];
      destruct s as [sh st]; destruct s' as [s'h s't]; simpl in *.
    rewrite [str_bool _]Stream_unfold [proph_to_expr _]Stream_unfold => Hx.
    rewrite [str_bool _]Stream_unfold [proph_to_expr _]Stream_unfold => Hy.
    rewrite [str_bool _]Stream_unfold [proph_to_expr _]Stream_unfold.
    simpl in *.
    by inversion Hx; inversion Hy; simplify_eq.
  - destruct x as [xh xt]; destruct y as [yh yt];
      destruct s as [sh st]; destruct s' as [s'h s't]; simpl in *.
    rewrite [str_bool _]Stream_unfold [proph_to_expr _]Stream_unfold => Hx.
    rewrite [str_bool _]Stream_unfold [proph_to_expr _]Stream_unfold => Hy.
    rewrite [str_bool _]Stream_unfold [proph_to_expr _]Stream_unfold.
    simpl in *.
    inversion Hx; inversion Hy; simplify_eq.
    f_equal; auto.
Qed.

Lemma after_nth_const n b :
  Nat.iter n Stail (str_bool (Sconst b)) = Sconst (#♭ b).
Proof.
  induction n.
  - simpl.
    apply Seq_eq.
    cofix IH.
    rewrite [Sconst (#♭ _)]Stream_unfold [str_bool _]Stream_unfold; simpl.
    econstructor; auto.
  - by simpl; rewrite IHn.
Qed.

Lemma str_bool_inh : ∃ p : Stream val, Elem (proph_to_expr p) str_bool.
Proof.
  exists (Sconst (BoolV true)), (Sconst true).
  etrans; first apply (after_nth_const 0 true).
  apply Seq_eq.
  cofix IH.
  rewrite [Sconst _]Stream_unfold; rewrite [proph_to_expr _]Stream_unfold; simpl.
  econstructor; auto.
Qed.

Definition proph_after_nth_toss p n :=
  PrP_eq (PrA p) (PrP p) (Stream bool) (λ x, Nat.iter n Stail (str_bool x)).

Definition can_toss p b :=
  ∃ z s, (PrP p z = s) ∧ (Shead s = (Bool b)).

Lemma can_toss_after_nth p n b :
  proph_after_nth_toss p n → can_toss p b.
Proof.
  intros [Heq1 Heq2].
  destruct p as [pS pA pP pPv pPe pPSI]; simpl in *.
  subst.
  exists (Sconst b). exists (Sconst (Bool b)); simpl; split; auto.
  rewrite Heq2.  apply after_nth_const.
Qed.

Lemma head_after_nth_toos p n :
  proph_after_nth_toss p n → ∃ b, Shead (PrS p) = BoolV b.
Proof.
  intros [Heq1 Heq2].
  destruct p as [pS pA pP pPv pPe pPSI]; simpl in *.
  subst.
  destruct pPSI as [x Hx].
  destruct (pPv x) as [u Hu].
  exists (Shead (Nat.iter n Stail x)).
  rewrite Heq2 in Hx.
  clear -Hx.
  revert pS x Hx.
  induction n => pS x Hx; simpl in *.
  - destruct pS as [h t]; simpl in *.
    apply (f_equal Shead) in Hx; simpl in *.
    apply (f_equal to_val) in Hx; simpl in *.
    by rewrite to_of_val in Hx; simplify_eq.
  - rewrite -Nat_iter_S Nat_iter_S_r in Hx.
    destruct x as [xh xt]; simpl in *.
    apply IHn in Hx. rewrite Hx.
    by rewrite -Nat_iter_S Nat_iter_S_r.
Qed.

Lemma proph_after_Snth_toss_tail p n :
  proph_after_nth_toss p n →
  proph_after_nth_toss (Proph_tail p) (S n).
Proof.
  intros [Heq1 Heq2].
  destruct p as [pS pA pP pPv pPe pPSI]; simpl in *.
  subst.
  unshelve econstructor; eauto; simpl.
  extensionality z.
  by rewrite Heq2.
Qed.

Section coin.
  Context `{heapIG Σ}.

  Definition make_coin :=
    Rec (Pair (Alloc (InjR Plang.Unit)) (Create_Pr _ str_bool)).

  Definition flip :=
    Rec (Rec ((Store (Var 3) (InjR Plang.Unit)))).

  Definition read :=
    Rec
      (Rec
         (Case
            (Load (Var 3))
            (Var 0)
            (App
               (Rec
                  (App
                     (Rec (App (Rec (Var 5)) (Assign_Pr (Var 6) (Var 3))))
                     (Store (Var 6) (InjL (Var 1))))
               )
               Rand))).

  Definition Coin (b : bool) (c l : loc) : iProp Σ :=
    (∃ p, l ↦ₚ p ∗ ⌜ ∃ n, proph_after_nth_toss p n ⌝ ∗
            (c ↦ (InjLV (BoolV b)) ∨ (c ↦ (InjRV UnitV)) ∗ ⌜Shead (PrS p) = BoolV b⌝))%I.

  Lemma wp_make_coin :
    {{{ True }}}
      App make_coin Plang.Unit
    {{{c l, RET PairV (LocV c) (PrV l); ∃ b, Coin b c l }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_pure_step_later; auto; iNext.
    asimpl.
    iApply (wp_bind (fill [PairLCtx _])).
    iApply wp_alloc; auto.
    iNext. iIntros (c) "Hc"; simpl.
    iApply (wp_bind (fill [PairRCtx (LocV _)])).
    iApply wp_create_pr; auto using str_bool_vals, str_bool_ent, str_bool_inh.
    iNext. iIntros (l) "Hl"; simpl. iDestruct "Hl" as (p) "[Hl Heq]".
    iDestruct "Heq" as %Heq.
    iApply wp_value. iApply "HΦ".
    destruct (PrSI p) as [y Hy].
    destruct (head_after_nth_toos p 0) as [b Hb]; auto.
    iExists b.
    iExists p; iFrame. iSplit; auto.
    { iPureIntro. exists 0; simpl; auto. }
  Qed.

  Lemma wp_flip b c l :
    {{{ Coin b c l }}} App (App flip (Loc c)) (Pr l) {{{RET UnitV; ∃ b, Coin b c l }}}.
  Proof.
    iIntros (Φ) "HC HΦ".
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; auto; iNext. asimpl.
    iApply wp_value.
    iApply wp_pure_step_later; auto; iNext. asimpl.
    iDestruct "HC" as (p) "(Hl & HP & Hc)".
    iDestruct "HP" as %[n HP].
    pose proof (can_toss_after_nth _ n true HP).
    iDestruct "Hc" as "[Hc|[Hc Hh]]".
    - iApply (wp_store with "[$Hc]"). iNext. iIntros "Hc".
      destruct (head_after_nth_toos p n) as [r Hr]; auto.
      iApply "HΦ". iExists r.
      iExists p; iFrame.
      iSplit; eauto.
    - iDestruct "Hh" as %Hh.
      iApply (wp_store with "[$Hc]"). iNext. iIntros "Hc".
      iApply "HΦ". iExists b.
      iExists p; iFrame.
      iSplit; eauto.
  Qed.

  Lemma wp_read b c l :
    {{{ Coin b c l }}} App (App read (Loc c)) (Pr l) {{{RET (BoolV b); Coin b c l }}}.
  Proof.
    iIntros (Φ) "HC HΦ".
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; auto; iNext. asimpl.
    iApply wp_value.
    iApply wp_pure_step_later; auto; iNext. asimpl.
    iDestruct "HC" as (p) "(Hl & HP & Hc)".
    iDestruct "HP" as %[n HP].
    iDestruct "Hc" as "[Hc|[Hc Hh]]".
    - iApply (wp_bind (fill [CaseCtx _ _])).
      iApply (wp_load with "[$Hc]"). iNext. iIntros "Hc". simpl.
      iApply wp_pure_step_later; auto; iNext. asimpl.
      iApply wp_value.
      iApply "HΦ".
      iExists p; iFrame.
      iSplit; eauto.
    - iDestruct "Hh" as %Hh.
      iApply (wp_bind (fill [CaseCtx _ _])).
      iApply (wp_load with "[$Hc]"). iNext. iIntros "Hc". simpl.
      iApply wp_pure_step_later; auto; iNext. asimpl.
      iApply (wp_bind (fill [AppRCtx (RecV _)])).
      iApply wp_rand. iNext. iIntros (r) "!> /=".
      iApply wp_pure_step_later; auto; iNext. asimpl.
      iApply (wp_bind (fill [AppRCtx (RecV _)])).
      iApply (wp_store with "[$Hc]"). iNext. iIntros "Hc". simpl.
      iApply wp_pure_step_later; auto; iNext. asimpl.
      iApply (wp_bind (fill [AppRCtx (RecV _)])).
      iApply (wp_assign_pr with "[$Hl]").
      { destruct (can_toss_after_nth p n r) as (z & s & Hz & Hs); eauto. }
      iNext. iIntros "[HP Hl]". iDestruct "HP" as %HnP.
      simpl.
      iApply wp_pure_step_later; auto; iNext. asimpl.
      iApply wp_value.
      rewrite Hh in HnP. simplify_eq.
      iApply "HΦ".
      iExists _; iFrame.
      iSplit; eauto.
      iPureIntro.
      exists (S n). by apply proph_after_Snth_toss_tail.
  Qed.

End coin.