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

Inductive chat_server_petri_places :=
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
| chat_server_petri_output_split mixer :
    chat_server_petri μ1 μ2
      (SplitTr CHPP_output (CHPP_output1 mixer 0) (CHPP_output2 mixer 0))
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

Definition V0 :=
  singVAL (CHPP_input1 0) ⊎ singVAL (CHPP_input2 0) ⊎ singVAL CHPP_output.

Inductive Traces1 μ1 μ2 : nat -> nat -> ioSpec :=
| EmpTR1 i1 i2: Traces1 μ1 μ2 i1 i2 nil
| Input1TR1 i1 i2 tr:
  Traces1 μ1 μ2 (S i1) i2 tr ->
  Traces1 μ1 μ2 i1 i2 ((read_nick1, UnitV, Snth i1 μ1)::tr)
| Input2TR1 i1 i2 tr:
  Traces1 μ1 μ2 i1 (S i2) tr ->
  Traces1 μ1 μ2 i1 i2 ((read_nick2, UnitV, Snth i2 μ2)::tr)
| Output1TR i1 i2 v tr:
  Traces1 μ1 μ2 i1 i2 tr ->
  Traces1 μ1 μ2 i1 i2 ((write_nick1, v, UnitV)::tr)
| Output2TR i1 i2 v tr:
  Traces1 μ1 μ2 i1 i2 tr ->
  Traces1 μ1 μ2 i1 i2 ((write_nick2, v, UnitV)::tr).

Definition val_of_state i1 i2 (o: option (Stream bool * nat * nat)) : Valuation :=
  singVAL (CHPP_input1 i1) ⊎ singVAL (CHPP_input2 i2) ⊎
  match o with
    None => singVAL CHPP_output
  | Some (m, o1, o2) => singVAL (CHPP_output1 m o1) ⊎ singVAL (CHPP_output2 m o2)
  end.

Arguments val_of_state _ _ /_.

Lemma ValPlus_cancel V V1 V2: V ⊎ V1 = V ⊎ V2 -> V1 = V2.
Proof.
  intros Heq.
  extensionality z.
  pose proof (equal_f Heq z) as Heq'.
  unfold ValPlus in Heq'. omega.
Qed.

Derive Inversion Traces_inv with (∀ x y tr, (Traces x y tr)).
Derive Inversion CSP_inv with (∀ μ1 μ2 tr, chat_server_petri μ1 μ2 tr).

Lemma Traces_Traces1_aftersplit μ1 μ2 tr:
  forall i1 i2 m o1 o2,
  Traces (chat_server_petri μ1 μ2) (val_of_state i1 i2 (Some (m, o1, o2))) tr ->
  Traces1 μ1 μ2 i1 i2 tr.
Proof.
  induction tr as [|a tr]; first by econstructor.
  intros i1 i2 m o1 o2 HT.
  destruct a as [[t v] v'].
  inversion HT using Traces_inv; try done.
  - (* IOTr *)
    intros _ V p t' w w' q τ Hpt Htr Hvl Hios; simplify_eq.
    inversion Hpt using CSP_inv; try done; simplify_eq.
    + intros _ n Hsp; simpl in *.
      pose proof (equal_f Hvl (CHPP_input1 n)) as Hvl';
        unfold singVAL, ValPlus in Hvl';
        repeat destruct decide; simplify_eq.
      constructor.
      apply (IHtr _ _ m o1 o2).
      rewrite -assoc in Hvl;
        apply ValPlus_cancel in Hvl; subst.
      by rewrite -assoc.
    + intros _ n Hsp; simpl in *; simplify_eq.
      pose proof (equal_f Hvl (CHPP_input2 n)) as Hvl';
        unfold singVAL, ValPlus in Hvl';
        repeat destruct decide; simplify_eq.
      constructor.
      apply (IHtr _ _ m o1 o2).
      rewrite (comm_L _ (_ (CHPP_input1 i1))) in Hvl.
      rewrite -assoc in Hvl;
        apply ValPlus_cancel in Hvl; subst.
      rewrite (comm_L _ (_ (CHPP_input1 i1))).
      by rewrite -assoc.
    + intros _ mixer n Hsp; simpl in *; simplify_eq.
      pose proof (equal_f Hvl (CHPP_output1 mixer n)) as Hvl';
        unfold singVAL, ValPlus in Hvl';
        repeat destruct decide; simplify_eq.
      constructor.
      apply (IHtr _ _ mixer (S n) o2).
      rewrite -assoc (comm_L _ (_ (CHPP_input2 i2)))
                     assoc (comm_L _ (_ (CHPP_input1 i1))) in Hvl.
      rewrite -!assoc in Hvl;
        apply ValPlus_cancel in Hvl; subst.
      rewrite -assoc (comm_L _ (_ (CHPP_input2 i2)))
                     assoc (comm_L _ (_ (CHPP_input1 i1))).
      by rewrite -!assoc.
    + intros _ mixer n Hsp; simpl in *; simplify_eq.
      pose proof (equal_f Hvl (CHPP_output2 mixer n)) as Hvl';
        unfold singVAL, ValPlus in Hvl';
        repeat destruct decide; simplify_eq.
      constructor.
      apply (IHtr _ _ mixer o1 (S n)).
      rewrite -assoc (comm_L _ (_ (CHPP_output1 _ _)))
                     (assoc _ (_ (CHPP_input2 i2)))
                     (comm_L _ (_ (CHPP_input2 i2))) assoc
                     (comm_L _ (_ (CHPP_input1 i1))) in Hvl.
      rewrite -!assoc in Hvl;
        apply ValPlus_cancel in Hvl; subst.
      rewrite -assoc (comm_L _ (_ (CHPP_output1 _ _)))
                     (assoc _ (_ (CHPP_input2 i2)))
                     (comm_L _ (_ (CHPP_input2 i2))) assoc
                     (comm_L _ (_ (CHPP_input1 i1))).
      by rewrite -!assoc.
  - (* SplitTR *)
    intros _ V p q q' τ Hpt Htr Hvl Hios; simplify_eq.
    inversion Hpt using CSP_inv; try done.
    intros _ mixer Hsp; simpl in *; simplify_eq.
    pose proof (equal_f Hvl CHPP_output) as Hvl';
      unfold singVAL, ValPlus in Hvl';
      repeat destruct decide; simplify_eq.
  - (* JoinTR *)
    intros _ V p p' q τ Hpt Htr Hvl Hios; simplify_eq.
    inversion Hpt.
  - (* NoOpTR *)
    intros _ V p q τ Hpt Htr Hvl Hios; simplify_eq.
    inversion Hpt.
Qed.

Lemma Traces_Traces1_beforesplit μ1 μ2 tr:
  forall i1 i2,
  Traces (chat_server_petri μ1 μ2) (val_of_state i1 i2 None) tr ->
  Traces1 μ1 μ2 i1 i2 tr.
Proof.
  induction tr as [|a tr]; first by constructor.
  intros i1 i2 HT.
  destruct a as [[t v] v'].
  inversion HT using Traces_inv; try done.
  - (* IOTr *)
    intros _ V p t' w w' q τ Hpt Htr Hvl Hios; simplify_eq.
    inversion Hpt using CSP_inv; try done; simplify_eq.
    + intros _ n Hsp; simpl in *.
      pose proof (equal_f Hvl (CHPP_input1 n)) as Hvl';
        unfold singVAL, ValPlus in Hvl';
        repeat destruct decide; simplify_eq.
      constructor.
      apply IHtr.
      rewrite -assoc in Hvl;
        apply ValPlus_cancel in Hvl; subst.
      by rewrite -assoc.
    + intros _ n Hsp; simpl in *; simplify_eq.
      pose proof (equal_f Hvl (CHPP_input2 n)) as Hvl';
        unfold singVAL, ValPlus in Hvl';
        repeat destruct decide; simplify_eq.
      constructor.
      apply IHtr.
      rewrite (comm_L _ (_ (CHPP_input1 i1))) in Hvl.
      rewrite -assoc in Hvl;
        apply ValPlus_cancel in Hvl; subst.
      rewrite (comm_L _ (_ (CHPP_input1 i1))).
      by rewrite -assoc.
    + intros _ mixer n Hsp; simpl in *; simplify_eq.
      pose proof (equal_f Hvl (CHPP_output1 mixer n)) as Hvl';
        unfold singVAL, ValPlus in Hvl';
        repeat destruct decide; simplify_eq.
    + intros _ mixer n Hsp; simpl in *; simplify_eq.
      pose proof (equal_f Hvl (CHPP_output2 mixer n)) as Hvl';
        unfold singVAL, ValPlus in Hvl';
        repeat destruct decide; simplify_eq.
  - (* SplitTR *)
    intros _ V p q q' τ Hpt Htr Hvl Hios; simplify_eq.
    inversion Hpt using CSP_inv; try done.
    intros _ mixer Hsp; simpl in *; simplify_eq.
    rewrite (comm_L _ _ (_ CHPP_output)) in Hvl.
    apply ValPlus_cancel in Hvl; simplify_eq.
    apply (Traces_Traces1_aftersplit _ _ _ i1 i2 mixer 0 0); simpl.
    by rewrite comm_L.
  - (* JoinTR *)
    intros _ V p p' q τ Hpt Htr Hvl Hios; simplify_eq.
    inversion Hpt.
  - (* NoOpTR *)
    intros _ V p q τ Hpt Htr Hvl Hios; simplify_eq.
    inversion Hpt.
Qed.

Lemma ResultDet_Traces1 μ1 μ2 t v v' v'' tr' tr'' tr:
  forall i1 i2,
  Traces1 μ1 μ2 i1 i2 (tr ++ (t, v, v') :: tr') ->
  Traces1 μ1 μ2 i1 i2 (tr ++ (t, v, v'') :: tr'') ->
  v' = v''.
Proof.
  induction tr as [|[[t0 v0] v'0] tr1]; simpl.
  - intros i1 i2 Hv' Hv''.
    by destruct t; inversion Hv'; inversion Hv''; simplify_eq.
- intros i1 i2 Hv' Hv''.
  destruct t0; inversion Hv'; inversion Hv''; simplify_eq; eapply IHtr1; eauto.
Qed.

Theorem chat_server_petri_ResultDet μ1 μ2 :
  ResultDet (Traces (chat_server_petri μ1 μ2) V0).
Proof.
  change V0 with (val_of_state 0 0 None).
  intros ? ? ? ? ? ? ? Hτ1 Hτ2.
  apply Traces_Traces1_beforesplit in Hτ1.
  apply Traces_Traces1_beforesplit in Hτ2.
  eapply ResultDet_Traces1; eauto.
Qed.

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
     FullIO (Traces (chat_server_petri μ1 μ2) V0)
            ∗ WP concrete_serveChatRoom {{ _, False }})%I.
Proof.
  iIntros "".
  pose (Traces (chat_server_petri μ1 μ2) V0) as ios.
  iMod (@own_alloc _ io_monoid _
                   (● Excl' (ios : leibnizC ioSpec) ⋅
                      ◯ Excl' (ios : leibnizC ioSpec))) as (γio) "[HFI HOI]";
    first done.
  iModIntro. iExists _. pose (make_heapIG γio). iFrame.
  iMod (PetriNetInv_alloc with "HOI") as (γpn) "[#HPi HOV]".
  { apply chat_server_petri_ResultDet. }
  pose ({| γPN := γpn; ThePetriNet := chat_server_petri μ1 μ2|}) as PN.
  iModIntro. iExists PN.
  rewrite /V0 !ownVAL_split.
  iDestruct "HOV" as "[[Hi1 Hi2] Ho]".
  iAssert (@Token chat_server_petri_placesC _ _ _ (CHPP_input1 0)) with "[$Hi1]"
    as "Hi1"; first done.
  iAssert (@Token chat_server_petri_placesC _ _ _ (CHPP_input2 0)) with "[$Hi2]"
    as "Hi2"; first done.
  iAssert (@Token chat_server_petri_placesC _ _ _ (CHPP_output)) with "[$Ho]"
    as "Ho"; first done.
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
                            (chat_server_petri μ1 μ2) V0) T).
Proof.
  eapply fully_erased_safe_equiv;
    last apply (fully_erased_safe_union concrete_serveChatRoom
         (λ M, ∃ μ1 μ2 : Stream val, M ≡
                        Traces (chat_server_petri μ1 μ2) V0)).
  - intros T; split.
    + intros (μ1 & μ2 & ?).
      exists (λ T, Traces (chat_server_petri μ1 μ2) V0 T).
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
