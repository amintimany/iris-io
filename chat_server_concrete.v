From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import fixpoint.
From iris.program_logic Require Import weakestpre lifting.
From iris_io Require Import lang rules abstract_petrinet petrinet
     chat_server channel adequacy.

Section conrete_chat_server.
  Context `{heapIG Σ, petrinetIG Σ, channelIG Σ}.

  Definition read_nick1 := 1%positive.
  Definition read_nick2 := 2%positive.

  Definition write_nick1 := 1%positive.
  Definition write_nick2 := 2%positive.

  Definition bool_to_write_tag (b : bool) :=
    if b then write_nick1 else write_nick2.

  Definition to_write_tag :=
    Lam (If (Var 0) (IOtag write_nick1) (IOtag write_nick2)).

  Lemma wp_to_write_tag b :
    {{{ True }}}
      App to_write_tag (Bool b)
    {{{ RET (IOtagV (bool_to_write_tag b)); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    by destruct b;
      iApply wp_pure_step_later; trivial; iNext;
        iApply wp_value; iApply "HΦ".
  Qed.

  Definition bool_to_read_tag (b : bool) :=
    if b then read_nick1 else read_nick2.

  Definition to_read_tag :=
    Lam (If (Var 0) (IOtag read_nick1) (IOtag read_nick2)).

  Lemma wp_to_read_tag b :
    {{{ True }}}
      App to_read_tag (Bool b)
    {{{ RET (IOtagV (bool_to_read_tag b)); True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    by destruct b;
      iApply wp_pure_step_later; trivial; iNext;
        iApply wp_value; iApply "HΦ".
  Qed.

  Definition send_to_nick :=
    Lam (Lam (Seq (IO (App to_write_tag (Var 1)) (Var 0)) Unit)).

  Lemma send_to_nick_closed : ∀ f, send_to_nick.[f] = send_to_nick.
  Proof. done. Qed.

  Definition receive_from_nick :=
    Lam ((IO (App to_read_tag (Var 0)) Unit)).

  Lemma receive_from_nick_closed :
    ∀ f, receive_from_nick.[f] = receive_from_nick.
  Proof. done. Qed.

  Definition place_stream :=
    (prodC (leibnizC Places) (leibnizC (Stream val))).

  Definition IO_pre_sequence
             (io_gen : val → Places → Places -> Transition)
             (f : place_stream → iProp Σ)
             (pμ : place_stream) : iProp Σ :=
    (∃ q, ⌜ThePetriNet (io_gen (Shead (pμ.2)) (pμ.1) q)⌝ ∧
          f (q, Stail (pμ.2)))%I.

  Global Instance IO_pre_sequence_BIMonoPred io_gen :
           BIMonoPred (IO_pre_sequence io_gen).
  Proof.
    split.
    - iIntros (Φ Ψ) "#HΦΨ"; iIntros ([p μ]).
      iDestruct 1 as (q) "[% HPhi]"; simpl in *.
      iExists q; iSplit; first trivial.
      by iApply "HΦΨ".
    - by intros Φ HΦ k [p μ] [p' μ'] [Hp%leibniz_equiv Hμ%leibniz_equiv];
      simpl in *; subst.
  Qed.

  Definition IO_sequence io_gen :=
    uPred_greatest_fixpoint (IO_pre_sequence io_gen).

  Definition ReceiveFromNick :=
    λ p n μ,
    match n with
    | BoolV b =>
      (IO_sequence (λ v p q, IOTr p (bool_to_read_tag b) UnitV v q) (p, μ))%I
    | _ => False%I
    end.

  Definition SendToNick :=
    λ p n μ,
    match n with
    | BoolV b =>
      (IO_sequence (λ v p q, IOTr p (bool_to_write_tag b) v UnitV q) (p, μ))%I
    | _ => False%I
    end.

  Lemma wp_receive_from_nick : ∀ r n m μ,
    {{{ token r ∗ ReceiveFromNick r n {| Shead := m; Stail := μ|} }}}
      App receive_from_nick (of_val n)
    {{{ RET m; ∃ r', token r' ∗ ReceiveFromNick r' n μ }}}.
  Proof.
    iIntros (r n m μ Φ) "[Hr Hrfn] HΦ".
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    destruct n; simpl; try done.
    rewrite {1}/IO_sequence greatest_fixpoint_unfold.
    iDestruct "Hrfn" as (q) "/= [% Hrfn]".
    iApply (wp_bind (fill [IOLCtx _])).
    iApply wp_to_read_tag; trivial.
    iNext; iIntros "_"; simpl.
    iApply (wp_petrinet_io with "Hr"); eauto.
    iNext. iIntros "Hq".
    iApply "HΦ". iExists _; iFrame.
  Qed.

  Lemma wp_send_to_nick : ∀ s n m μ,
    {{{ token s ∗ SendToNick s n {| Shead := m; Stail := μ|} }}}
      App (App send_to_nick (of_val n)) (of_val m)
    {{{ RET UnitV; ∃ s', token s' ∗ SendToNick s' n μ }}}.
  Proof.
    iIntros (r n m μ Φ) "[Hr Hrfn] HΦ".
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; trivial.
    iNext. asimpl. iApply wp_value; simpl.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    destruct n; simpl; try done.
    rewrite {1}/IO_sequence greatest_fixpoint_unfold.
    iDestruct "Hrfn" as (q) "/= [% Hrfn]".
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_bind (fill [IOLCtx _])).
    iApply wp_to_read_tag; trivial.
    iNext; iIntros "_"; simpl.
    iApply (wp_petrinet_io with "Hr"); eauto.
    iNext. iIntros "Hq".
    iApply wp_pure_step_later; trivial.
    iNext. iApply wp_value.
    iApply "HΦ". iExists _; iFrame.
  Qed.

  Global Program Instance concrete_nick_comm_prog : abstract_nick_comm_prog :=
    {|
      chat_server.send_to_nick := send_to_nick;
      chat_server.receive_from_nick := receive_from_nick;
    |}.
  Solve Obligations with eauto.

  Global Program Instance concrete_nick_comm : abstract_nick_comm :=
    {|
      chat_server.ReceiveFromNick := ReceiveFromNick;
      chat_server.SendToNick := SendToNick;
    |}.
  Solve Obligations with eauto using wp_receive_from_nick, wp_send_to_nick.

  Program Definition concrete_serveChatRoom :=
    serveChatRoom (BoolV true) (BoolV false).

  Theorem wp_concrete_serverChatRoom r1 r2 s μ1 μ2 :
    {{{ token r1 ∗ ReceiveFromNick r1 (BoolV true) μ1 ∗
        token r2 ∗ ReceiveFromNick r2 (BoolV false) μ2 ∗
        token s ∗ ∀ μ, ⌜interleaving μ1 μ2 μ⌝ →
                       SendToNicks s (BoolV true) (BoolV false) μ }}}
      concrete_serveChatRoom
  {{{RET UnitV; False}}}.
  Proof.
    iIntros (Φ) "(Hr1 & Hrf1 & Hr2 & Hrf2 & Hs & Hsnd) HΦ".
    iApply (wp_serverChatRoom _ _ r1 r2 s with "[-HΦ]"); simpl; eauto.
    iFrame.
  Qed.

End conrete_chat_server.

(* Definition make_input_io (tg : ioTag) (μ : Stream val):= *)
(*   Smap (λ x, (tg, UnitV, x)) μ. *)

(* Definition make_output_io (tg : ioTag) (μ : Stream val):= *)
(*   Smap (λ x, (tg, x, UnitV)) μ. *)

(* Definition chat_server_io mixer μ1 μ2 μ := *)
(*   ∃ μwr, *)
(*     interleaving (make_output_io write_nick1 (Smix mixer μ1 μ2)) *)
(*                  (make_output_io write_nick2 (Smix mixer μ1 μ2)) μwr ∧ *)
(*     interleaving (Smix mixer (make_input_io read_nick1 μ1) *)
(*                        (make_input_io read_nick2 μ2)) μwr μ. *)

(* Definition chat_server_ioSpec mixer μ1 μ2 : ioSpec := *)
(*   λ l, ∃ μ, chat_server_io mixer μ1 μ2 (append_l_s l μ). *)

Inductive chat_server_petri_places :=
  CHPP_Start
| CHPP_input
| CHPP_input1 (n : nat)
| CHPP_input2 (n : nat)
| CHPP_output
| CHPP_output1 (n : nat)
| CHPP_output2 (n : nat).

Global Instance chat_server_petri_places_eqdec :
  EqDecision chat_server_petri_places.
Proof. solve_decision. Qed.

Instance chat_server_petri_placesC : PlacesC :=
  {| Places := chat_server_petri_places |}.

Inductive chat_server_petri_base mixer μ1 μ2 : PetriNet :=
| chat_server_petri_start_split :
    chat_server_petri_base mixer μ1 μ2 (SplitTr CHPP_Start CHPP_input CHPP_output)
| chat_server_petri_input_split :
    chat_server_petri_base mixer μ1 μ2
                      (SplitTr CHPP_input (CHPP_input1 0) (CHPP_input2 0))
| chat_server_petri_output_split :
    chat_server_petri_base mixer μ1 μ2
                      (SplitTr CHPP_output (CHPP_output1 0) (CHPP_output2 0))
| chat_server_petri_input1 n :
    chat_server_petri_base mixer μ1 μ2
                      (IOTr (CHPP_input1 n) read_nick1 UnitV (Snth n μ1)
                            (CHPP_input1 (S n)))
| chat_server_petri_input2 n :
    chat_server_petri_base mixer μ1 μ2
                      (IOTr (CHPP_input2 n) read_nick2 UnitV (Snth n μ2)
                            (CHPP_input2 (S n)))
| chat_server_petri_output1 n :
    chat_server_petri_base mixer μ1 μ2
                      (IOTr (CHPP_output1 n) write_nick1
                            (Snth n (Smix mixer μ1 μ2))
                            UnitV
                            (CHPP_output1 (S n)))
| chat_server_petri_output2 n :
    chat_server_petri_base mixer μ1 μ2
                      (IOTr (CHPP_output2 n) write_nick2
                            (Snth n (Smix mixer μ1 μ2))
                            UnitV
                            (CHPP_output2 (S n))).

Definition chat_server_petri μ1 μ2 : PetriNet :=
  λ T, ∃ mixer, chat_server_petri_base mixer μ1 μ2 T.

(* Lemma chat_server_petri_det_io mixer μ1 μ2 : *)
(*   (∀ p t v v' q, *)
(*       chat_server_petri mixer μ1 μ2 (IOTr p t v v' q) → *)
(*       (∀ t1 v1 v1' q1, chat_server_petri mixer μ1 μ2 (IOTr p t1 v1 v1' q1) → *)
(*                        t1 = t ∧ v1 = v ∧ v1' = v' ∧ q1 = q) ∧ *)
(*       (∀ q1 q2, chat_server_petri mixer μ1 μ2 (SplitTr p q1 q2) → False) ∧ *)
(*       (∀ p2 q, chat_server_petri mixer μ1 μ2 (JoinTr p p2 q) → False)). *)
(* Proof. *)
(*   intros ? ? ? ? ? Hp; inversion Hp; clear Hp; subst; (split; [|split]); *)
(*     intros; *)
(*     match goal with *)
(*     | H : chat_server_petri _ _ _ _ |- _ => inversion H; subst; auto *)
(*     end. *)
(* Qed. *)

(* Lemma chat_server_petri_det_split mixer μ1 μ2 : *)
(*   (∀ p q1 q2, *)
(*       chat_server_petri mixer μ1 μ2 (SplitTr p q1 q2) → *)
(*       (∀ t1 v1 v1' q1, chat_server_petri mixer μ1 μ2 (IOTr p t1 v1 v1' q1) → False) *)
(*       ∧ (∀ q1' q2', chat_server_petri mixer μ1 μ2 (SplitTr p q1' q2') → *)
(*                     q1' = q1 ∧ q2' = q2) ∧ *)
(*       (∀ p2 q, chat_server_petri mixer μ1 μ2 (JoinTr p p2 q) → False)). *)
(* Proof. *)
(*   intros ? ? ? Hp; inversion Hp; clear Hp; subst; (split; [|split]); *)
(*     intros; *)
(*     match goal with *)
(*     | H : chat_server_petri _ _ _ _ |- _ => inversion H; subst; auto *)
(*     end. *)
(* Qed. *)

(* Definition chat_server_petri_start_val := *)
(*   λ p, match p with CHPP_Start => 1 | _ => 0 end. *)

(* correct the statement, p must be reachable from start! *)
Lemma chat_server_petri_ResultDet μ1 μ2 p :
  ResultDet (Traces (chat_server_petri μ1 μ2) p).
Proof.
  (* intros t v v' v'' τ τ' τ'' Hτ. *)
  (* remember (τ ++ (t, v, v') :: τ') as io. *)
  (* revert τ t v v' v'' τ' Heqio. *)
  (* induction Hτ as [| ? ? ? ? ? ? ? Hτio | | |] => τ1 t1 v1 v1' v1'' τ1' Heqio Hτ''. *)
  (* - by destruct τ1. *)
  (* - inversion Hτ''. *)
  (*   + by destruct τ1. *)
  (*   + destruct τ1 as [|[[? ?] ?] τ1]; simpl in *; inversion Heqio; simplify_eq. *)
  (*     * admit. *)
  (*     *  *)
Admitted.

Lemma Recive_from_nick (b : bool) `{inG Σ (authUR (ofe_funUR (λ _ : Places, natUR)))}
      γ μ1 μ2 :
  let _ := {| γPN := γ; ThePetriNet := chat_server_petri μ1 μ2 |}in
  (ReceiveFromNick (if b then (CHPP_input1 0) else (CHPP_input2 0))
                   (BoolV b) (if b then μ1 else μ2))%I.
Proof.
  pose ({| γPN := γ; PNI_exclG := H;
           ThePetriNet := chat_server_petri μ1 μ2 |}).
  set (Φ := (λ pμ : @place_stream chat_server_petri_placesC,
                      ∃ n, ⌜pμ.1 = (if b then CHPP_input1 n else CHPP_input2 n)
                           ∧ pμ.2 = Sdrop n (if b then μ1 else μ2)⌝)%I
            : place_stream → iProp Σ).
  assert (NonExpansive Φ).
  { by intros n [? ?] [? ?] [?%leibniz_equiv ?%leibniz_equiv];
      simpl in *; subst. }
  iApply (greatest_fixpoint_coind _ Φ); simpl; eauto.
  iAlways. iIntros ([? ?]); iDestruct 1 as %[n [Hn Hμ]]; simpl in *; subst.
  rewrite /IO_pre_sequence.
  iExists (if b then CHPP_input1 (S n) else CHPP_input2 (S n)); iSplit; simpl.
  + iPureIntro. rewrite Snth_Sdrop; destruct b; exists (Sconst true); constructor.
  + iExists (S n); iPureIntro; split; simpl; auto.
Qed.

Lemma Send_to_nick (b : bool) `{inG Σ (authUR (ofe_funUR (λ _ : Places, natUR)))}
      γ μ1 μ2 μ :
  interleaving μ1 μ2 μ →
  let _ := {| γPN := γ; ThePetriNet := chat_server_petri μ1 μ2 |}in
  (SendToNick (if b then (CHPP_output1 0) else (CHPP_output2 0)) (BoolV b) μ)%I.
Proof.
  pose ({| γPN := γ; PNI_exclG := H;
           ThePetriNet := chat_server_petri μ1 μ2 |}).
  set (Φ := (λ pμ : @place_stream chat_server_petri_placesC,
                      ∃ n, ⌜pμ.1 = (if b then CHPP_output1 n else CHPP_output2 n)
                           ∧ pμ.2 = Sdrop n μ⌝)%I
            : place_stream → iProp Σ).
  assert (NonExpansive Φ).
  { by intros n [? ?] [? ?] [?%leibniz_equiv ?%leibniz_equiv];
      simpl in *; subst. }
  intros Hinr; simpl.
  iApply (greatest_fixpoint_coind _ Φ); simpl; eauto.
  iAlways. iIntros ([? ?]); iDestruct 1 as %[n [Hn Hμ]]; simpl in *; subst.
  rewrite /IO_pre_sequence.
  iExists (if b then CHPP_output1 (S n) else CHPP_output2 (S n)); iSplit; simpl.
  + iPureIntro. rewrite Snth_Sdrop. destruct Hinr as [mixer <-].
    destruct b; exists mixer; econstructor.
  + iExists (S n); iPureIntro; split; simpl; auto.
Qed.

Theorem wp_closed_concrete_serverChatRoom
        `{heapIPreIOG Σ}
        `{channelIG Σ}
        `{inG Σ (authUR (ofe_funUR (λ p : Places, natUR)))}
        μ1 μ2 :
  (|={⊤}=> ∃ γio, let _ := make_heapIG γio in
                 |={⊤}=> ∃ _ : petrinetIG Σ,
     FullIO (Traces (chat_server_petri μ1 μ2)
                    (singVAL CHPP_Start))
            ∗ WP concrete_serveChatRoom {{ _, False }})%I.
Proof.
  iIntros "".
  pose (Traces (chat_server_petri μ1 μ2)
                (singVAL CHPP_Start)) as ios.
  iMod (@own_alloc _ io_monoid _
                   (● Excl' (ios : leibnizC ioSpec) ⋅
                      ◯ Excl' (ios : leibnizC ioSpec))) as (γio) "[HFI HOI]";
    first done.
  iModIntro. iExists _. pose (make_heapIG γio). iFrame.
  iMod (PetriNetInv_alloc with "HOI") as (γpn) "[#HPi HOV]".
  { apply chat_server_petri_ResultDet. }
  pose ({| PNI_exclG := _; γPN := γpn; ThePetriNet := chat_server_petri μ1 μ2|})
    as PN.
  iModIntro. iExists PN.
  iAssert (@Token chat_server_petri_placesC _ _ _ CHPP_Start) with "[$HOV]"
    as "HOS"; first done.
  iMod (petrinet_split with "[HOS]") as "[HI HO]"; [| by iFrame |].
  { exists (Sconst true); apply chat_server_petri_start_split. }
  iMod (petrinet_split with "[HI]") as "[HI1 HI2]"; [| by iFrame |].
  { exists (Sconst true); apply chat_server_petri_input_split. }
  iPoseProof (Recive_from_nick true γpn μ1 μ2) as "HRFN1".
  iPoseProof (Recive_from_nick false γpn μ1 μ2) as "HRFN2".
  iApply (@wp_concrete_serverChatRoom
            _ _ chat_server_petri_placesC _ _
            (CHPP_input1 0) (CHPP_input2 0) CHPP_output μ1 μ2 with "[-]");
    last done.
  iFrame; iFrame "#".
  iIntros (μ Hintr).
  iExists _, _; simpl.
  iSplit.
  { iPureIntro. eexists (Sconst true); econstructor. }
  iSplitL.
  by iApply (Send_to_nick true).
  by iApply (Send_to_nick false).
Qed.

Theorem concrete_serverChatRoom_safe :
        fully_erased_safe
          concrete_serveChatRoom
          (λ T, ∃ μ1 μ2, (@Traces
                            chat_server_petri_placesC
                            (chat_server_petri μ1 μ2) (singVAL CHPP_Start)) T).
Proof.
  eapply fully_erased_safe_equiv;
    last apply (fully_erased_safe_union concrete_serveChatRoom
         (λ M, ∃ μ1 μ2 : Stream val, M ≡
                        Traces (chat_server_petri μ1 μ2)
                                (@singVAL chat_server_petri_placesC
                                          CHPP_Start))).
  - intros T; split.
    + intros (μ1 & μ2 & ?).
      exists (λ T, Traces (chat_server_petri μ1 μ2)
                   (@singVAL chat_server_petri_placesC CHPP_Start) T).
      split; eauto.
    + intros [M [(μ1 & μ2 & HMeq) HM]]. eexists _, _; by apply HMeq.
  - intros M (μ1 & μ2 & HM).
    apply leibniz_equiv in HM; subst.
    pose (#[IoΣ; petrinetΣ; channelΣ]) as Σ.
    apply (adequacy Σ _ ((λ _, False))%I).
    { admit. }
    intros Hig.
    iIntros "".
    iMod (wp_closed_concrete_serverChatRoom μ1 μ2) as (γio) "Hlm".
    iMod ("Hlm") as (HIG) "[HFIO HWP]".
    iModIntro; iExists _; iFrame.
Admitted.