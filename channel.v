From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris_io Require Export lang rules.
From iris.proofmode Require Import tactics.
From iris_io Require Import lang rules.
From iris Require Import proofmode.tactics.
From iris.program_logic Require Import weakestpre lifting.
From iris.algebra Require Import agree frac.

CoInductive interleaving {A} : Stream A → Stream A → Stream A → Prop :=
  interL v μ1 μ2 μ : interleaving μ1 μ2 μ →
                     interleaving {|Shead := v; Stail := μ1 |} μ2
                                  {|Shead := v; Stail := μ |}
| interR v μ1 μ2 μ : interleaving μ1 μ2 μ →
                     interleaving μ1 {|Shead := v; Stail := μ2 |}
                                  {|Shead := v; Stail := μ |}.

Lemma interleaving_inh {A} (μ1 μ2 : Stream A) : (interleaving μ1 μ2) μ1.
Proof.
  revert μ1 μ2.
  cofix.
  destruct μ1.
  by constructor.
Qed.

Fixpoint append_l_s {A} (l : list A) (s : Stream A) :=
  match l with
  | [] => s
  | a :: l' => {|Shead := a; Stail := append_l_s l' s |}
  end.

Class ChannelIG Σ := channelIG {
   stream_inG :> inG Σ (prodR (fracR) (agreeR (leibnizC (Stream val))));
   streams_inG :> inG Σ (prodR (fracR) (agreeR (leibnizC ((Stream val) → Prop))))
}.

Fixpoint of_list (l : list val) :=
  match l with
    [] => InjLV Plang.UnitV
  | v :: l' => InjRV (PairV v (of_list l'))
  end.

Section channels.

  Context `{!ChannelIG Σ, !heapIG Σ}.

  Definition own_stream γ q μ :=
    own γ (q, to_agree μ : (agreeR (leibnizC (Stream val)))).

  Definition own_streams γ q M :=
    own γ (q, to_agree M : (agreeR (leibnizC ((Stream val) → Prop)))).

  Definition channel_inv queue γs1 γs2 γR : iProp Σ :=
        (∃ vs (μ1 μ2 : Stream val) M,
            queue ↦ (of_list vs) ∗
                  own_stream γs1 (1/2)%Qp μ1 ∗
                  own_stream γs2 (1/2)%Qp μ2 ∗
                  own_streams γR (1/2)%Qp M ∗
                  ⌜∀ μ', interleaving μ1 μ2 μ' → M (append_l_s vs μ')⌝
        )%I.

  Definition sender queue μ :=
    (∃ γs γs1 γs2 γR,
        inv (nroot .@ "channel") (channel_inv queue γs1 γs2 γR) ∗
            own_stream γs (1/2)%Qp μ ∗ ⌜γs = γs1 ∨ γs = γs2⌝)%I.

  Definition receiver queue l μ :=
    (∃ γs1 γs2 γR M, inv (nroot .@ "channel") (channel_inv queue γs1 γs2 γR)
                         ∗ own_streams γR (1/2)%Qp M ∗ cpvar l M μ)%I.

  Definition new_channel :=
    Lam (Pair Create_Pr (Alloc (InjL Plang.Unit))).

  Lemma wp_new_channel μ1 μ2 :
    {{{True}}}
      App new_channel Plang.Unit
    {{{q l, RET (PairV (PrV l) (LocV q));
       sender q μ1 ∗ sender q μ2 ∗
              ∃ μ, ⌜interleaving μ1 μ2 μ⌝ ∗ receiver q l μ
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_pure_step_later; auto.
    iNext. asimpl.
    iApply (wp_bind (fill [PairLCtx _])); simpl.
    iApply (wp_create_pr _ (interleaving μ1 μ2)); eauto using interleaving_inh.
    iNext.
    iIntros (l); iDestruct 1 as (μ) "Hμ".
    iApply (wp_bind (fill [PairRCtx _])); simpl.
    iApply wp_alloc; auto.
    iNext. iIntros (q) "Hq".
    iApply wp_value_fupd.
    iMod (own_alloc (1%Qp, to_agree μ1 : (agreeR (leibnizC (Stream val)))))
      as (γs1) "[Hμ11 Hμ12]";
      first done.
    iMod (own_alloc (1%Qp, to_agree μ2 : (agreeR (leibnizC (Stream val)))))
      as (γs2) "[Hμ21 Hμ22]";
      first done.
    iMod (own_alloc (1%Qp, to_agree (interleaving μ1 μ2)
                     : (agreeR (leibnizC (Stream val → Prop)))))
      as (γR) "[HM1 HM2]";
      first done.
    iMod (inv_alloc (nroot .@ "channel") _ (channel_inv q γs1 γs2 γR)
            with "[Hμ11 Hμ21 HM1 Hq]") as "#Hinv".
    { iNext. unfold channel_inv.
      iExists [], _, _, _; iFrame; auto. }
    iModIntro.
    iApply "HΦ".
    iSplitL "Hμ12"; first by iExists _, _, _, _; iFrame; iFrame "#"; eauto.
    iSplitL "Hμ22"; first by iExists _, _, _, _; iFrame; iFrame "#"; eauto.
    iExists μ; iSplit; first by iApply cpvar_contains.
    iExists _, _, _, _; iFrame "#"; iFrame.
  Qed.

  Definition Append :=
    Lam
      (Rec
         (Case
            (Var 1) (Var 3)
            (InjR (Pair (Fst (Var 0)) (App (Var 1) (Snd (Var 0)))) ))
      ).

  Lemma wp_Append `{heapIG Σ} l l' :
    WP (App (App Append (of_val (of_list l))) (of_val (of_list l')))
       {{w, ⌜w = of_list (l' ++ l)⌝}}%I.
  Proof.
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; auto.
    iNext.
    asimpl.
    iApply wp_value. simpl.
    iLöb as "IH" forall (l').
                   iApply wp_pure_step_later; auto.
                   iNext.
                   asimpl.
                   destruct l'.
                   - simpl. iApply wp_pure_step_later; auto.
                     iNext. asimpl. by iApply wp_value.
                   - simpl. iApply wp_pure_step_later; auto.
                     iNext. asimpl.
                     iApply (wp_bind (fill [InjRCtx])).
                     iApply (wp_bind (fill [PairLCtx _])).
                     iApply wp_pure_step_later; auto.
                     iNext; iApply wp_value. simpl.
                     iApply (wp_bind (fill [PairRCtx _])).
                     iApply (wp_bind (fill [AppRCtx (RecV _)])).
                     iApply wp_pure_step_later; auto.
                     iNext; iApply wp_value. simpl.
                     iApply wp_wand_r; iSplitR.
                     { iApply "IH". }
                     iIntros (w) "%"; subst; simpl.
                       by do 2 iApply wp_value.
  Qed.

  Definition send :=
    Lam
      (Rec
         (LetIn (Load (Snd (Var 2)))
                (If
                   (CAS (Snd (Var 3)) (Var 0) (App (App Append (Var 2)) (Var 3)))
                   (Plang.Unit)
                   (App (Var 1) (Var 2))
                )
         )
      ).


End channels.



