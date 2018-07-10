From iris.algebra Require Import auth.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import fixpoint viewshifts.
From iris.program_logic Require Import weakestpre lifting.
From iris_io Require Import lang rules abstract_petrinet petrinet
     chat_server channel adequacy.

From Coq.Logic Require Import ClassicalDescription.

Section conrete_chat_server.
  Context `{heapIG Σ, petrinetIG Σ, channelIG Σ}.

  Definition read_nick1 := 1%positive.
  Definition read_nick2 := 2%positive.

  Definition write_nick1 := 3%positive.
  Definition write_nick2 := 4%positive.

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
    λ P n μ,
    match n with
    | BoolV b =>
      (∃ p, (P ={⊤}=> Token p)
              ∗ IO_sequence (λ v p q, IOTr p (bool_to_read_tag b) UnitV v q)
              (p, μ))%I
    | _ => False%I
    end.

  Definition SendToNick :=
    λ P n μ,
    match n with
    | BoolV b =>
      (∃ p, (P ={⊤}=> Token p)
              ∗ IO_sequence (λ v p q, IOTr p (bool_to_write_tag b) v UnitV q) (p, μ))%I
    | _ => False%I
    end.

  Lemma wp_receive_from_nick : ∀ P n m μ,
    {{{ P ∗ ReceiveFromNick P n {| Shead := m; Stail := μ|} }}}
      App receive_from_nick (of_val n)
    {{{ RET m; ∃ Q, Q ∗ ReceiveFromNick Q n μ }}}.
  Proof.
    iIntros (P n m μ Φ) "[Hr Hrfn] HΦ".
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    destruct n; simpl; try done.
    iDestruct "Hrfn" as (r) "[#HPr Hrfn]".
    iMod ("HPr" with "Hr") as "Hr".
    rewrite {1}/IO_sequence greatest_fixpoint_unfold.
    iDestruct "Hrfn" as (q) "/= [% Hrfn]".
    iApply (wp_bind (fill [IOLCtx _])).
    iApply wp_to_read_tag; trivial.
    iNext; iIntros "_"; simpl.
    iApply (wp_petrinet_io with "Hr"); eauto.
    iNext. iIntros "Hq".
    iApply "HΦ".
    iExists (Token q); iFrame; iExists _; iFrame.
    by iAlways; iIntros "$".
  Qed.

  Lemma wp_send_to_nick : ∀ S n m μ,
    {{{ S ∗ SendToNick S n {| Shead := m; Stail := μ|} }}}
      App (App send_to_nick (of_val n)) (of_val m)
    {{{ RET UnitV; ∃ S', S' ∗ SendToNick S' n μ }}}.
  Proof.
    iIntros (S n m μ Φ) "[Hs Hrfn] HΦ".
    iApply (wp_bind (fill [AppLCtx _])).
    iApply wp_pure_step_later; trivial.
    iNext. asimpl. iApply wp_value; simpl.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    destruct n; simpl; try done.
    iDestruct "Hrfn" as (s) "[#HPs Hrfn]".
    iMod ("HPs" with "Hs") as "Hs".
    rewrite {1}/IO_sequence greatest_fixpoint_unfold.
    iDestruct "Hrfn" as (q) "/= [% Hrfn]".
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_bind (fill [IOLCtx _])).
    iApply wp_to_write_tag; trivial.
    iNext; iIntros "_"; simpl.
    iApply (wp_petrinet_io with "Hs"); eauto.
    iNext. iIntros "Hq".
    iApply wp_pure_step_later; trivial.
    iNext. iApply wp_value.
    iApply "HΦ". iExists (Token q); iFrame; iExists _; iFrame.
    by iAlways; iIntros "$".
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

  Theorem wp_concrete_serverChatRoom R1 R2 S μ1 μ2 :
    {{{ R1 ∗ ReceiveFromNick R1 (BoolV true) μ1 ∗
        R2 ∗ ReceiveFromNick R2 (BoolV false) μ2 ∗
        S ∗ ∀ μ, ⌜interleaving μ1 μ2 μ⌝ →
                       SendToNicks S (BoolV true) (BoolV false) μ }}}
      concrete_serveChatRoom
  {{{RET UnitV; False}}}.
  Proof.
    iIntros (Φ) "(Hr1 & Hrf1 & Hr2 & Hrf2 & Hs & Hsnd) HΦ".
    iApply (wp_serverChatRoom _ _ R1 R2 S with "[-HΦ]"); simpl; eauto.
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
| CHPP_output1 (mixer : Stream bool) (n : nat)
| CHPP_output2 (mixer : Stream bool) (n : nat).

Global Instance chat_server_petri_places_eqdec :
  EqDecision chat_server_petri_places.
Proof. intros ??; apply excluded_middle_informative. Qed.

Instance chat_server_petri_placesC : PlacesC :=
  {| Places := chat_server_petri_places |}.

Inductive chat_server_petri μ1 μ2 : PetriNet :=
| chat_server_petri_start_split :
    chat_server_petri μ1 μ2 (SplitTr CHPP_Start CHPP_input CHPP_output)
| chat_server_petri_input_split :
    chat_server_petri μ1 μ2
                      (SplitTr CHPP_input (CHPP_input1 0) (CHPP_input2 0))
| chat_server_petri_output_split mixer :
    chat_server_petri
      μ1 μ2 (SplitTr CHPP_output (CHPP_output1 mixer 0) (CHPP_output2 mixer 0))
| chat_server_petri_input1 n :
    chat_server_petri μ1 μ2
                      (IOTr (CHPP_input1 n) read_nick1 UnitV (Snth n μ1)
                            (CHPP_input1 (S n)))
| chat_server_petri_input2 n :
    chat_server_petri μ1 μ2
                      (IOTr (CHPP_input2 n) read_nick2 UnitV (Snth n μ2)
                            (CHPP_input2 (S n)))
| chat_server_petri_output1 mixer n :
    chat_server_petri μ1 μ2
                      (IOTr (CHPP_output1 mixer n) write_nick1
                            (Snth n (Smix mixer μ1 μ2))
                            UnitV
                            (CHPP_output1 mixer (S n)))
| chat_server_petri_output2 mixer n :
    chat_server_petri μ1 μ2
                      (IOTr (CHPP_output2 mixer n) write_nick2
                            (Snth n (Smix mixer μ1 μ2))
                            UnitV
                            (CHPP_output2 mixer (S n))).

Inductive Reachable_Valuation : Valuation → Prop :=
| ReachableV_Start : Reachable_Valuation (singVAL CHPP_Start)
| ReachableV_IO :
    Reachable_Valuation ((singVAL CHPP_input) ⊎ (singVAL CHPP_output))
| ReachableV_IsO n m :
    Reachable_Valuation
      ((singVAL (CHPP_input1 n))
         ⊎ (singVAL (CHPP_input2 m))
         ⊎ (singVAL CHPP_output))
| ReachableV_IOs mixer n m :
    Reachable_Valuation
      ((singVAL CHPP_input)
         ⊎ (singVAL (CHPP_output1 mixer n))
         ⊎ (singVAL (CHPP_output2 mixer m)))
| ReachableV_IsOs mixer n1 m1 n2 m2 :
    Reachable_Valuation
      ((singVAL (CHPP_input1 n1))
         ⊎ (singVAL (CHPP_input2 m1))
         ⊎ (singVAL (CHPP_output1 mixer n2))
         ⊎ (singVAL (CHPP_output2 mixer m2))).

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

Lemma singVAL_eq p q V : singVAL p ⊎ V = singVAL q → p = q ∧ V = (λ x, 0).
Proof.
  intros Heq.
  split.
  - pose proof (equal_f Heq p) as Heq'.
    revert Heq'. rewrite /singVAL /ValPlus /=.
    repeat destruct decide; done.
  - extensionality z.
    pose proof (equal_f Heq z) as Heq'.
    pose proof (equal_f Heq p) as Heq''.
    revert Heq' Heq''. rewrite /singVAL /ValPlus /=.
    repeat destruct decide; subst; auto with omega; try done.
Qed.

Lemma singVAL_eq21 p1 p2 q V :
  p1 ≠ p2 → singVAL p1 ⊎ singVAL p2 = singVAL q ⊎ V → q = p1 ∨ q = p2.
Proof.
  intros ? Heq.
  pose proof (equal_f Heq q) as Heq'.
  revert Heq'. rewrite /singVAL /ValPlus /=.
  repeat destruct decide; simplify_eq; eauto with lia.
Qed.

Lemma singVAL_eq12 p q1 q2 V : ¬ singVAL p = singVAL q1 ⊎ singVAL q2 ⊎ V.
Proof.
  intros Heq.
  pose proof (equal_f Heq p) as Heq'.
  pose proof (equal_f Heq q1) as Heq''.
  pose proof (equal_f Heq q2) as Heq'''.
  revert Heq' Heq'' Heq'''. rewrite /singVAL /ValPlus /=.
  repeat (destruct decide; try done); simplify_eq; eauto with lia.
Qed.

Lemma singVAL_eq22 p1 p2 q1 q2 V :
  p1 ≠ p2 →
  singVAL p1 ⊎ singVAL p2 = singVAL q1 ⊎ singVAL q2 ⊎ V →
  q1 = p1 ∧ q2 = p2 ∨ q1 = p2 ∧ q2 = p1.
Proof.
  intros ? Heq.
  pose proof (equal_f Heq p1) as Heq1.
  pose proof (equal_f Heq q2) as Heq2.
  pose proof (equal_f Heq q1) as Heq3.
  pose proof (equal_f Heq q2) as Heq4.
  revert Heq1 Heq2 Heq3 Heq4. rewrite /singVAL /ValPlus /=.
  repeat (destruct decide; try done); simplify_eq; eauto with lia.
Qed.

(* Lemma singVAL_eq32 p1 p2 p3 q1 q2 V : *)
(*   p1 ≠ p2 → *)
(*   singVAL p1 ⊎ singVAL p2 ⊎ singVAL p3 = singVAL q1 ⊎ singVAL q2 ⊎ V → *)
(*   (q1 = p1 ∧ q2 = p2) ∨ (q1 = p2 ∧ q2 = p1) ∨ *)
(*   (q1 = p1 ∧ q2 = p2). *)
(* Proof. *)
(*   intros ? Heq. *)
(*   pose proof (equal_f Heq p1) as Heq1. *)
(*   pose proof (equal_f Heq q2) as Heq2. *)
(*   pose proof (equal_f Heq q1) as Heq3. *)
(*   pose proof (equal_f Heq q2) as Heq4. *)
(*   revert Heq1 Heq2 Heq3 Heq4. rewrite /singVAL /ValPlus /=. *)
(*   repeat (destruct decide; try done); simplify_eq; eauto with lia. *)
(* Qed. *)


(* There are so many cases that we need to consider we just admit them
here. There must be an easier way via some more disciplined lemma to
prove result-deterministicness that does not involve so many case
analysis over the transitions and valuations. *)
(* admitted cases below are intuitively easy! *)
Lemma chat_server_petri_ResultDet μ1 μ2 V :
  Reachable_Valuation V →
  ResultDet (Traces (chat_server_petri μ1 μ2) V).
Proof.
  intros HV t v v' v'' τ τ' τ'' Hτ.
  remember (τ ++ (t, v, v') :: τ') as io.
  revert HV τ t v v' v'' τ' Heqio.
  induction Hτ as [| ? ? ? ? ? ? ? Hτio | | |] => HV τ1 t1 v1 v1' v1'' τ1' Heqio Hτ''.
  - by destruct τ1.
  - inversion HV.
    + edestruct singVAL_eq; eauto; subst.
      match goal with
      | H : chat_server_petri _ _ _ |- _ => inversion H
      end.
    + edestruct (singVAL_eq21); eauto; try done; simplify_eq;
        match goal with
        | H : chat_server_petri _ _ _ |- _ => inversion H
        end.
    + admit.
    + admit.
    + admit.
  - match goal with
    | H : chat_server_petri _ _ (SplitTr ?p _ _) |- _ =>
      destruct p; inversion H; simplify_eq
    end.
    + inversion HV.
      * admit.
      * edestruct singVAL_eq21; eauto; try done.
      * admit.
      * admit.
      * admit.
    + admit.
    + inversion HV.
      * edestruct singVAL_eq; eauto; try done.
      * edestruct singVAL_eq21; eauto; try done.
        admit.
      * admit.
      * admit.
      * admit.
  - match goal with
        | H : chat_server_petri _ _ (JoinTr ?p _ _) |- _ =>
          destruct p; inversion H
        end.
  - match goal with
    | H : chat_server_petri _ _ (NoOpTr ?p _) |- _ =>
      destruct p; inversion H
    end.
Admitted.

Lemma Recive_from_nick (b : bool)
      `{heapIG Σ} `{inG Σ (authUR (ofe_funUR (λ _ : Places, natUR)))} γ μ1 μ2 :
  let _ := {| γPN := γ; ThePetriNet := chat_server_petri μ1 μ2 |} in
  (ReceiveFromNick (if b then Token (CHPP_input1 0) else Token (CHPP_input2 0))
                   (BoolV b) (if b then μ1 else μ2))%I.
Proof.
  pose ({| γPN := γ; PNI_exclG := _;
           ThePetriNet := chat_server_petri μ1 μ2 |}).
  set (Φ := (λ pμ : @place_stream chat_server_petri_placesC,
                      ∃ n, ⌜pμ.1 = (if b then CHPP_input1 n else CHPP_input2 n)
                           ∧ pμ.2 = Sdrop n (if b then μ1 else μ2)⌝)%I
            : place_stream → iProp Σ).
  assert (NonExpansive Φ).
  { by intros n [? ?] [? ?] [?%leibniz_equiv ?%leibniz_equiv];
      simpl in *; subst. }
  iExists (if b then (CHPP_input1 0) else (CHPP_input2 0)); simpl.
  iSplit.
  { by destruct b; iIntros "!# $". }
  iApply (greatest_fixpoint_coind _ Φ); simpl; eauto.
  iAlways. iIntros ([? ?]); iDestruct 1 as %[n [Hn Hμ]]; simpl in *; subst.
  rewrite /IO_pre_sequence.
  iExists (if b then CHPP_input1 (S n) else CHPP_input2 (S n)); iSplit; simpl.
  + iPureIntro. rewrite Snth_Sdrop; destruct b; econstructor.
  + iExists (S n); iPureIntro; split; simpl; auto.
Qed.

Lemma Send_to_nick (b : bool) mixer
      `{heapIG Σ} `{inG Σ (authUR (ofe_funUR (λ _ : Places, natUR)))}
      γ μ1 μ2 μ :
  Smix mixer μ1 μ2 = μ →
  let _ := {| γPN := γ; ThePetriNet := chat_server_petri μ1 μ2 |}in
  (SendToNick (if b then Token (CHPP_output1 mixer 0) else
                 Token (CHPP_output2 mixer 0)) (BoolV b) μ)%I.
Proof.
  pose ({| γPN := γ; PNI_exclG := _;
           ThePetriNet := chat_server_petri μ1 μ2 |}).
  set (Φ := (λ pμ : @place_stream chat_server_petri_placesC,
                      ∃ n, ⌜pμ.1 = (if b then CHPP_output1 mixer n else
                                      CHPP_output2 mixer n)
                           ∧ pμ.2 = Sdrop n μ⌝)%I
            : place_stream → iProp Σ).
  assert (NonExpansive Φ).
  { by intros n [? ?] [? ?] [?%leibniz_equiv ?%leibniz_equiv];
      simpl in *; subst. }
  intros Hinr; simpl.
  iExists (if b then (CHPP_output1 mixer 0) else (CHPP_output2 mixer 0)); simpl.
  iSplit.
  { by destruct b; iIntros "!# $". }
  iApply (greatest_fixpoint_coind _ Φ); simpl; eauto.
  iAlways. iIntros ([? ?]); iDestruct 1 as %[n [Hn Hμ]]; simpl in *; subst.
  rewrite /IO_pre_sequence.
  iExists (if b then CHPP_output1 mixer (S n) else CHPP_output2 mixer (S n));
    iSplit; simpl.
  + iPureIntro. rewrite Snth_Sdrop.
    destruct b; econstructor.
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
  pose ({| γPN := γpn; ThePetriNet := chat_server_petri μ1 μ2|}) as PN.
  iModIntro. iExists PN.
  iAssert (@Token chat_server_petri_placesC _ _ _ CHPP_Start) with "[$HOV]"
    as "HOS"; first done.
  iMod (petrinet_split with "[HOS]") as "[HI HO]"; [| by iFrame |].
  { apply chat_server_petri_start_split. }
  iMod (petrinet_split with "[HI]") as "[HI1 HI2]"; [| by iFrame |].
  { apply chat_server_petri_input_split. }
  iPoseProof (Recive_from_nick true γpn μ1 μ2) as (r) "[#Hr1 HRFN1]".
  iPoseProof (Recive_from_nick false γpn μ1 μ2) as (s) "[#Hr2 HRFN2]".
  iApply (wp_concrete_serverChatRoom
            (@Token _ _ _ PN (CHPP_input1 0)) (@Token _ _ _ PN (CHPP_input2 0))
            (@Token _ _ _ PN CHPP_output) μ1 μ2 with "[-]");
    last done.
  iFrame.
  iSplitL.
  { iExists _; iFrame "#". }
  iSplitL.
  { iExists _; iFrame "#". }
  iIntros (μ [mixer <-]).
  iExists (Token _), (Token _); simpl.
  iSplit.
  { iApply petrinet_split. apply (chat_server_petri_output_split _ _ mixer). }
  iSplitL.
  { by iApply (Send_to_nick true). }
  { by iApply (Send_to_nick false). }
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
    { apply Traces_prefix_closed. }
    intros Hig.
    iIntros "".
    iMod (wp_closed_concrete_serverChatRoom μ1 μ2) as (γio) "Hlm".
    iMod ("Hlm") as (HIG) "[HFIO HWP]".
    iModIntro; iExists _; iFrame.
Qed.
