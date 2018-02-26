From iris.program_logic Require Export weakestpre lifting.
From iris.proofmode Require Import tactics.
From iris_io Require Import lang rules.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Definition coin_proph (s : Stream val) :=
  ∀ n, ∃ v, Snth n s = #♭v v.

Lemma coin_proph_after_read_eq b : with_head coin_proph (#♭v b) = coin_proph.
Proof.
  extensionality s.
  apply propositional_extensionality; split.
  - intros Hr n; destruct (Hr (S n)) as [p Hp]; simpl in *; eauto.
  - intros Hc n. destruct n as [|n]; first eauto.
    destruct (Hc n) as [p Hp]; eauto.
Qed.

Lemma coin_proph_inh : ∃ s : Stream val, coin_proph s.
Proof.
  exists (Sconst (#♭v true)).
  intros n; induction n; eauto.
Qed.

Section coin.
  Context `{heapIG Σ}.

  Definition make_coin :=
    Rec (Pair (Alloc (InjR Plang.Unit)) Create_Pr).

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
    (∃ p, cpvar l coin_proph p ∗
            (c ↦ (InjLV (BoolV b)) ∨ ((c ↦ (InjRV UnitV)) ∗ ⌜Shead p = #♭v b⌝)))%I.

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
    iApply (wp_create_pr _ coin_proph); auto using coin_proph_inh.
    iNext. iIntros (l) "Hl"; simpl. iDestruct "Hl" as (p) "Hl".
    iApply wp_value. iApply "HΦ".
    unfold cpvar.
    iDestruct (cpvar_contains with "Hl") as %Hac.
    destruct (Hac 0) as [b Hb].
    iExists b, p; iFrame. iRight; iFrame.
    { by iPureIntro. }
  Qed.

  Lemma wp_flip b c l :
    {{{ Coin b c l }}} App (App flip (Loc c)) (Pr l) {{{RET UnitV; ∃ b, Coin b c l }}}.
  Proof.
    iIntros (Φ) "HC HΦ".
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; auto; iNext. asimpl.
    iApply wp_value.
    iApply wp_pure_step_later; auto; iNext. asimpl.
    iDestruct "HC" as (p) "(Hl & Hc)".
    iDestruct "Hc" as "[Hc|[Hc Hh]]".
    - iApply (wp_store with "[$Hc]"). iNext. iIntros "Hc".
      iApply "HΦ".
      iDestruct (cpvar_contains with "Hl") as %Hac.
      destruct (Hac 0) as [r Hr].
      iExists r, p; iFrame. iRight; iFrame.
      { by iPureIntro. }
    - iDestruct "Hh" as %Hh.
      iApply (wp_store with "[$Hc]"). iNext. iIntros "Hc".
      iApply "HΦ". iExists b.
      iExists p; iFrame. iRight; eauto.
  Qed.

  Lemma wp_read b c l :
    {{{ Coin b c l }}} App (App read (Loc c)) (Pr l) {{{RET (BoolV b); Coin b c l }}}.
  Proof.
    iIntros (Φ) "HC HΦ".
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; auto; iNext. asimpl.
    iApply wp_value.
    iApply wp_pure_step_later; auto; iNext. asimpl.
    iDestruct "HC" as (p) "(Hl & Hc)".
    iDestruct "Hc" as "[Hc|[Hc Hh]]".
    - iApply (wp_bind (fill [CaseCtx _ _])).
      iApply (wp_load with "[$Hc]"). iNext. iIntros "Hc". simpl.
      iApply wp_pure_step_later; auto; iNext. asimpl.
      iApply wp_value.
      iApply "HΦ".
      iExists p; iFrame.
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
      { iExists (Sconst (#♭v r)). iPureIntro.
        intros n; exists r. destruct n; first done. apply (Snth_Sconst (S n)). }
      iNext. iIntros "[HP Hl]". iDestruct "HP" as %HnP.
      simpl.
      iApply wp_pure_step_later; auto; iNext. asimpl.
      iApply wp_value.
      rewrite Hh in HnP. simplify_eq.
      iApply "HΦ".
      rewrite coin_proph_after_read_eq.
      iExists _; iFrame.
  Qed.

End coin.