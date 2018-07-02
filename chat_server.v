From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre lifting.
From iris_io Require Import lang rules petrinet channel.


Section chat_server.
  Context `{heapIG Σ, channelIG Σ, petrinetIG Σ}.

  Variable ReceiveFromNick : iProp Σ → val → Stream val → iProp Σ.
  Variable SendToNick : iProp Σ → val → Stream val → iProp Σ.

  Definition token P : iProp Σ := P.

  Variables send_to_nick receive_from_nick : expr.

  Hypothesis send_to_nick_closed : ∀ f, send_to_nick.[f] = send_to_nick.
  Hypothesis receive_from_nick_closed :
    ∀ f, receive_from_nick.[f] = receive_from_nick.

  Hint Rewrite send_to_nick_closed receive_from_nick_closed : autosubst.

  Hypothesis wp_receive_from_nick : ∀ r n m μ,
    {{{ token r ∗ ReceiveFromNick r n {| Shead := m; Stail := μ|} }}}
      App receive_from_nick (of_val n)
    {{{ RET m; ∃ r', token r' ∗ ReceiveFromNick r' n μ }}}.

  Hypothesis wp_send_to_nick : ∀ s n m μ,
    {{{ token s ∗ SendToNick s n {| Shead := m; Stail := μ|} }}}
      App (App send_to_nick (of_val n)) (of_val m)
    {{{ RET UnitV; ∃ s', token s' ∗ SendToNick s' n μ }}}.

  Definition pumpFromNick :=
    Lam
      (Rec
         (LetIn
            (App receive_from_nick (Var 2))
            (Seq
               (App (App send (Var 2)) (Var 0))
               (App (Var 1) (Var 2))
            )
         )
      ).

  Lemma pumpFromNick_closed f : pumpFromNick.[f] = pumpFromNick.
  Proof. by asimpl. Qed.

  Hint Rewrite pumpFromNick_closed : autosubst.

  Lemma wp_pumpFromNick r roomCh n μ :
    {{{ token r ∗ ReceiveFromNick r n μ ∗ sender roomCh μ }}}
      App (App pumpFromNick (of_val n)) (of_val roomCh)
    {{{RET UnitV; False}}}.
  Proof.
    iIntros (Φ) "(Hr & Hrfn & Hsnd) HΦ".
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply wp_value; simpl.
    iLöb as "IH" forall (r μ).
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    destruct μ as [m μ].
    iApply (wp_receive_from_nick with "[$Hr $Hrfn]").
    iNext. iDestruct 1 as (r') "[Hr' Hrfn]"; simpl.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_send with "Hsnd").
    iNext. iIntros "Hsnd"; simpl.
    iApply wp_pure_step_later; trivial.
    iNext. by iApply ("IH" with "Hr' Hrfn Hsnd").
  Qed.

  Typeclasses Opaque pumpFromNick.
  Global Opaque pumpFromNick.

  Definition pumpRoom :=
    Lam (
        Lam
          (Rec(
               LetIn
                 (App receive (Var 1))
                 (Seq
                    (App (App send_to_nick (Var 4)) (Var 0))
                    (Seq
                       (App (App send_to_nick (Var 3)) (Var 0))
                       (App (Var 1) (Var 2))
                    )
                 )
             )
          )
      ).

  Lemma pumpRoom_closed f : pumpRoom.[f] = pumpRoom.
  Proof. by asimpl. Qed.

  Hint Rewrite pumpRoom_closed : autosubst.

  Lemma wp_pumpRoom roomCh s1 s2 n1 n2 μ :
    {{{ token s1 ∗ SendToNick s1 n1 μ ∗ token s2 ∗ SendToNick s2 n2 μ
              ∗ receiver roomCh μ }}}
      App (App (App pumpRoom (of_val n1)) (of_val n2)) (of_val roomCh)
    {{{RET UnitV; False}}}.
  Proof.
    iIntros (Φ) "(Hs1& Hn1 & Hs2 & Hn2 & Hrc) HΦ".
    iApply (wp_bind (fill [AppLCtx _])).
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; trivial.
    iNext. asimpl. iApply wp_value.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl. iApply wp_value; simpl.
    iLöb as "IH" forall (s1 s2 μ).
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    destruct μ as [m μ].
    iApply (wp_receive with "[$Hrc]").
    iNext. iIntros "Hrc".
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_send_to_nick with "[$Hs1 $Hn1]").
    iNext. iDestruct 1 as (s1') "[Hs1' Hn1]"; simpl.
    iApply wp_pure_step_later; trivial.
    iNext.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_send_to_nick with "[$Hs2 $Hn2]").
    iNext. iDestruct 1 as (s2') "[Hs2' Hn2]"; simpl.
    iApply wp_pure_step_later; trivial.
    iNext. by iApply ("IH" with "Hs1' Hn1 Hs2' Hn2 Hrc").
  Qed.

  Typeclasses Opaque pumpRoom.
  Global Opaque pumpRoom.

  Definition serveChatRoom n1 n2 :=
    LetIn
      (App new_channel Plang.Unit)
      (Seq
         (Fork (App (App pumpFromNick (of_val n1)) (Var 0)))
         (Seq
            (Fork (App (App pumpFromNick (of_val n2)) (Var 0)))
            (App (App (App pumpRoom (of_val n1)) (of_val n2)) (Var 0))
         )
      ).

  Definition SendToNicks s n1 n2 μ :=
    (∃ s1 s2, (token s ==∗ token s1 ∗ token s2)
                ∗ SendToNick s1 n1 μ ∗ SendToNick s2 n2 μ)%I.

  Theorem wp_serverChatRoom n1 n2 r1 r2 s μ1 μ2 :
    (∀ f, (of_val n1).[f] = (of_val n1)) →
    (∀ f, (of_val n2).[f] = (of_val n2)) →
    {{{ token r1 ∗ ReceiveFromNick r1 n1 μ1 ∗
        token r2 ∗ ReceiveFromNick r2 n2 μ2 ∗
        token s ∗ ∀ μ, ⌜interleaving μ1 μ2 μ⌝ → SendToNicks s n1 n2 μ }}}
      serveChatRoom n1 n2
  {{{RET UnitV; False}}}.
  Proof.
    iIntros (Hn1c Hn2c Φ) "(Hr1 & Hrc1 & Hr2 & Hrc2 & Hs & Hsnd) HΦ".
    iApply (wp_bind (fill [LetInCtx _])).
    iApply (wp_new_channel μ1 μ2); auto.
    iNext; simpl.
    iIntros (ch) "(Hsn1 & Hsn2 & Hsr)".
    iDestruct "Hsr" as (μ) "[Hint Hrc]".
    iDestruct "Hint" as %Hint.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl; rewrite Hn1c Hn2c.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply wp_fork; simpl; iSplitR "Hr1 Hrc1 Hsn1"; last first.
    { by iApply (wp_pumpFromNick r1 with "[-]"); iFrame. }
    iNext; iModIntro.
    iApply wp_pure_step_later; trivial. iNext.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply wp_fork; simpl; iSplitR "Hr2 Hrc2 Hsn2"; last first.
    { by iApply (wp_pumpFromNick r2 with "[-]"); iFrame. }
    iNext; iModIntro.
    iApply wp_pure_step_later; trivial. iNext.
    iDestruct ("Hsnd" $! μ Hint) as (s1 s2) "(Hsplit & Hsnd1 & Hsnd2)".
    iMod ("Hsplit" with "Hs") as "[Hs1 Hs2]".
    iApply (wp_pumpRoom _ s1 s2 with "[-HΦ]"); iFrame.
  Qed.

End chat_server.

Hint Rewrite pumpFromNick_closed : autosubst.

Hint Rewrite pumpRoom_closed : autosubst.
