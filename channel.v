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

Lemma append_l_s_app {A} (vs : list A) v μ :
  append_l_s (vs ++ [v]) μ = append_l_s vs {| Shead := v; Stail := μ |}.
Proof.
  induction vs; simpl; first done.
  by rewrite IHvs.
Qed.

Class ChannelIG Σ := channelIG {
   stream_inG :> inG Σ (prodR (fracR) (agreeR (leibnizC (Stream val))));
   streams_inG :> inG Σ (prodR (fracR) (agreeR (leibnizC ((Stream val) → Prop))))
}.

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

Section channels.

  Context `{!ChannelIG Σ, !heapIG Σ}.

  Definition own_stream γ q μ :=
    own γ (q, to_agree μ : (agreeR (leibnizC (Stream val)))).

  Definition own_streams γ q M :=
    own γ (q, to_agree M : (agreeR (leibnizC ((Stream val) → Prop)))).

  Definition channel_inv chan γs1 γs2 γR : iProp Σ :=
        (∃ vs (μ1 μ2 : Stream val) M queue l,
            ⌜chan = (PairV (PrV l) (LocV queue))⌝ ∗
            queue ↦ (of_list vs) ∗
            own_stream γs1 (1/2)%Qp μ1 ∗
            own_stream γs2 (1/2)%Qp μ2 ∗
            own_streams γR (1/2)%Qp M ∗
            ⌜∀ μ', interleaving μ1 μ2 μ' → M (append_l_s vs μ')⌝
        )%I.

  Definition sender chan μ :=
    (∃ γs γs1 γs2 γR,
        inv (nroot .@ "channel") (channel_inv chan γs1 γs2 γR) ∗
            own_stream γs (1/2)%Qp μ ∗ ⌜γs = γs1 ∨ γs = γs2⌝)%I.

  Definition receiver chan μ :=
    (∃ γs1 γs2 γR M queue l,
        ⌜chan = (PairV (PrV l) (LocV queue))⌝ ∗
        inv (nroot .@ "channel") (channel_inv chan γs1 γs2 γR)
            ∗ own_streams γR (1/2)%Qp M ∗ cpvar l M μ)%I.

  Definition new_channel :=
    Lam (Pair Create_Pr (Alloc (InjL Plang.Unit))).

  Lemma wp_new_channel μ1 μ2 :
    {{{True}}}
      App new_channel Plang.Unit
    {{{w, RET w;
       sender w μ1 ∗ sender w μ2 ∗
              ∃ μ, ⌜interleaving μ1 μ2 μ⌝ ∗ receiver w μ
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
    iMod (inv_alloc (nroot .@ "channel") _
                    (channel_inv (PairV (PrV l) (LocV q)) γs1 γs2 γR)
            with "[Hμ11 Hμ21 HM1 Hq]") as "#Hinv".
    { iNext. unfold channel_inv.
      iExists [], _, _, _, _, _; iFrame; eauto. }
    iModIntro.
    iApply "HΦ".
    iSplitL "Hμ12"; first by iExists _, _, _, _; iFrame; iFrame "#"; eauto.
    iSplitL "Hμ22"; first by iExists _, _, _, _; iFrame; iFrame "#"; eauto.
    iExists μ; iSplit; first by iApply cpvar_contains.
    iExists _, _, _, _, _, _; iFrame "#"; iFrame; eauto.
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
      rewrite /= -append_eq.
      iApply wp_pure_step_later; auto.
      iNext; iApply wp_value.
      iApply wp_wand_r; iSplitR.
      { iApply ("IH" $! (λ s, ⌜s = of_list (l ++ l')⌝))%I. iNext.
        by iIntros (w Hw); subst w. }
      simpl.
      iIntros (w) "%"; subst; simpl.
      do 2 iApply wp_value.
      by iApply "HΦ".
  Qed.

  Definition send :=
    Lam
      (Rec
         (LetIn
            (Snd (Var 2))
            (LetIn
               (Load (Var 0))
               (If
                  (CAS (Var 1) (Var 0)
                       (App (App append.[ren (+5)]
                                          (Var 0))
                            (InjR (Pair (Var 3) (InjL Unit)))))
                  Unit
                  (App (Var 2) (Var 3))
               )
            )
         )
      ).

  Lemma wp_send chan v μ :
    {{{sender chan {| Shead := v; Stail := μ|} }}}
      App (App send (of_val chan)) (of_val v)
      {{{RET UnitV;  sender chan μ }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iDestruct "HP" as (γs γs1 γs2 γR) "(#chinv & Hγs & #Hγseq)".
    iApply fupd_wp.
    iInv (nroot.@"channel") as "Hinv" "Hcl".
    iDestruct "Hinv" as (ws μ1 μ2 M queue l) "(>% & ? & ? & ? & ? & ?)";
      simplify_eq.
    iMod ("Hcl" with "[- Hγs HΦ]") as "_";
      first by iExists _, _, _, _, _, _; iNext; iFrame.
    iModIntro.
    clear ws μ1 μ2 M.
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply wp_value; simpl.
    iLöb as "IH".
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_pure_step_later; trivial.
    iNext; iApply wp_value; simpl.
    iApply wp_pure_step_later; trivial.
    iNext; asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iInv (nroot.@"channel") as "Hinv" "Hcl".
    iDestruct "Hinv" as (ws μ1 μ2 M queue' l') "(>% & Hq & ? & ? & ? & ?)";
      simplify_eq.
    iApply (wp_load with "Hq"); first iFrame.
    iNext. iIntros "Hq".
    iMod ("Hcl" with "[- Hγs HΦ]") as "_";
      first by iExists _, _, _, _, _, _; iNext; iFrame.
    clear μ1 μ2 M.
    iModIntro.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [IfCtx _ _])).
    iApply (wp_bind (fill [CasRCtx (LocV _) _])); simpl.
    iApply (wp_append _ [v]); trivial.
    iNext; simpl.
    iIntros (w ?); subst w.
    iInv (nroot.@"channel") as "Hinv" "Hcl".
    iDestruct "Hinv" as (ws' μ1 μ2 M queue l)
                          "(>% & Hq & Hγs1 & Hγs2 & HγR & >Hintr)"; simplify_eq.
    iDestruct "Hintr" as %Hintr.
    destruct (decide (ws' = ws)) as [|Hneq]; first subst ws'.
    - iApply (wp_cas_suc with "Hq").
      iNext. iIntros "Hq".
      iAssert (|={⊤ ∖ ↑nroot.@"channel",⊤}=>
              own_stream γs (1 / 2)%Qp μ)%I with "[-HΦ]" as "Hcl".
      { iDestruct "Hγseq" as %[]; subst γs.
        - iDestruct (own_valid_2 with "Hγs Hγs1") as %[_ ?%agree_op_invL'];
          simpl in *; simplify_eq.
          iCombine "Hγs" "Hγs1" as "Hγs".
          iMod (own_update _ _ ((1%Qp, to_agree μ : agreeR (leibnizC _)))
                  with "Hγs") as "[Hγs Hγys1]".
          { by apply cmra_update_exclusive. }
          iMod ("Hcl" with "[- Hγs]") as "_"; last by iFrame.
          { iExists _, _, _, _, _, _; iNext; iFrame.
            iSplit; first by eauto.
            iPureIntro. intros; rewrite append_l_s_app.
            apply Hintr; by econstructor. }
        - iDestruct (own_valid_2 with "Hγs Hγs2") as %[_ ?%agree_op_invL'];
          simpl in *; simplify_eq.
          iCombine "Hγs" "Hγs2" as "Hγs".
          iMod (own_update _ _ ((1%Qp, to_agree μ : agreeR (leibnizC _)))
                  with "Hγs") as "[Hγs Hγs2]".
          { by apply cmra_update_exclusive. }
          iMod ("Hcl" with "[- Hγs]") as "_"; last by iFrame.
          { iExists _, _, _, _, _, _; iNext; iFrame.
            iSplit; first by eauto.
            iPureIntro. intros; rewrite append_l_s_app.
            apply Hintr; by econstructor. }
      }
      iMod "Hcl" as "Hγs".
      iModIntro.
      iApply wp_pure_step_later; trivial.
      iNext. asimpl.
      iApply wp_value.
      iApply "HΦ".
      iExists _, _, _, _; iFrame "#"; iFrame.
    - iApply (wp_cas_fail with "Hq").
      { intros ?; apply Hneq; eapply (@inj _ _ eq eq of_list _); eauto. }
      iNext. iIntros "Hq".
      iMod ("Hcl" with "[- Hγs HΦ]") as "_";
      first by iExists _, _, _, _, _, _; iNext; iFrame.
      iModIntro.
      iApply wp_pure_step_later; trivial.
      iNext. by iApply ("IH" with "Hγs").
  Qed.

  Definition receive :=
    Lam
      (LetIn
         (Fst (Var 0))
         (LetIn
            (Snd (Var 1))
            (App
               (Rec
                  (LetIn
                     (Load (Var 2))
                     (Case
                        (Var 0)
                        (App (Var 2) Unit)
                        (If
                           (CAS (Var 4) (Var 1) (Snd (Var 0)))
                           (LetIn
                              (Fst (Var 0))
                              (Seq
                                 (Assign_Pr (Var 6) (Var 0))
                                 (Var 0)
                              )
                           )
                           (App (Var 2) Unit)
                        )
                     )
                  )
               )
               Unit
            )
         )
      ).

  Lemma wp_receive chan v μ :
    {{{receiver chan {| Shead := v; Stail := μ|} }}}
      App receive (of_val chan)
      {{{RET v;  receiver chan μ }}}.
  Proof.
    iIntros (Φ) "HP HΦ".
    iDestruct "HP" as (γs1 γs2 γR M q l Hcn) "(#chinv & HR & Hpr)"; subst.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_pure_step_later; trivial.
    iNext; iApply wp_value; simpl.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_pure_step_later; trivial.
    iNext; iApply wp_value; simpl.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iLöb as "IH".
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iInv (nroot.@"channel") as "Hinv" "Hcl".
    iDestruct "Hinv" as (ws μ1 μ2 M' queue' l') "(>% & Hq & ? & ? & ? & ?)";
      simplify_eq.
    iApply (wp_load with "Hq"); first iFrame.
    iNext. iIntros "Hq".
    iMod ("Hcl" with "[- HR Hpr HΦ]") as "_";
      first by iExists _, _, _, _, _, _; iNext; iFrame.
    clear μ1 μ2 M'.
    iModIntro.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    destruct ws as [|w ws]; simpl.
    { iApply wp_pure_step_later; trivial.
      iNext. asimpl.
      by iApply ("IH" with "HR Hpr"). }
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [IfCtx _ _])).
    iApply (wp_bind (fill [CasRCtx (LocV _) (InjRV (PairV _ _))])); simpl.
    iApply wp_pure_step_later; trivial.
    iNext; iApply wp_value; simpl.
    iInv (nroot.@"channel") as "Hinv" "Hcl".
    iDestruct "Hinv" as (ws' μ1 μ2 M' queue l)
                          "(>% & Hq & Hγs1 & Hγs2 & HγR & >Hintr)"; simplify_eq.
    iDestruct "Hintr" as %Hintr.
    destruct (decide (ws' = w :: ws)) as [|Hneq]; first subst ws'.
    - iApply (wp_cas_suc with "Hq").
      iNext. iIntros "Hq".
      iDestruct (own_valid_2 with "HR HγR") as %[_ ?%agree_op_invL'];
        simpl in *; simplify_eq.
      iCombine "HR" "HγR" as "HR".
      iMod (own_update
              _ _
              ((1%Qp, to_agree (λ μ, M' {| Shead := w; Stail := μ |})
                : agreeR (leibnizC _)))
              with "HR") as "[HR HγR]".
      { by apply cmra_update_exclusive. }
      iMod ("Hcl" with "[- HR Hpr HΦ]") as "_".
      { iExists _, _, _, _, _, _; iNext; iFrame; eauto. }
      iModIntro.
      iApply wp_pure_step_later; trivial.
      iNext.
      iApply (wp_bind (fill [LetInCtx _])).
      iApply wp_pure_step_later; trivial.
      iNext; iApply wp_value; simpl.
      iApply wp_pure_step_later; trivial.
      iNext. asimpl.
      iApply (wp_bind (fill [SeqCtx _])).
      iApply (wp_assign_pr with "[$Hpr]").
      { iExists (append_l_s ws _); iPureIntro.
        eapply Hintr, interleaving_inh. }
      iNext. iIntros "[% Hpr]"; subst; simpl.
      iApply wp_pure_step_later; trivial.
      iNext; iApply wp_value.
      iApply "HΦ".
      iExists _, _, _, _, _, _; iFrame "#"; iFrame; eauto.
    - iApply (wp_cas_fail with "Hq").
      { intros ?; apply Hneq; eapply (@inj _ _ eq eq of_list _); eauto. }
      iNext. iIntros "Hq".
      iMod ("Hcl" with "[- HR Hpr HΦ]") as "_";
      first by iExists _, _, _, _, _, _; iNext; iFrame.
      iModIntro.
      iApply wp_pure_step_later; trivial.
      iNext. by iApply ("IH" with "HR Hpr").
  Qed.

End channels.



