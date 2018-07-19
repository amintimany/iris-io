From iris.algebra Require Import auth.
From iris_io Require Import lang rules list.
From iris_io Require Import petrinet adequacy.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre lifting.
From iris.base_logic Require Import viewshifts.

Section buffered_io.
  Context `{heapIG Σ, petrinetIG Σ}.

  Definition beep_tag := 1%positive.
  Definition write_char_tag := 2%positive.

  Definition beep := IO (IOtag beep_tag) Plang.Unit.

  Lemma beep_eq : beep = IO (IOtag beep_tag) Plang.Unit.
  Proof. done. Qed.

  Lemma beep_closed : ∀ f, beep.[f] = beep.
  Proof. done. Qed.

  Hint Rewrite beep_closed : autosubst.

  Typeclasses Opaque beep.
  Global Opaque beep.

  Definition beep_ P Q :=
    (∃ p q R,
        (P ={⊤}=> Token p ∗ R)
          ∗ ⌜ThePetriNet (IOTr p beep_tag Plang.UnitV Plang.UnitV q)⌝
          ∗ (Token q ∗ R ={⊤}=> Q)
    )%I.

  Lemma beep_frame P Q R :
    beep_ P Q -∗ beep_ (P ∗ R) (Q ∗ R).
  Proof.
    iDestruct 1 as (p q R') "(#Hp & % & #Hq)".
    iExists p, q, (R ∗ R')%I.
    repeat iSplit; trivial.
    - iIntros "!# [HP HR]".
      by iMod ("Hp" with "HP") as "[$ $]".
    - iIntros "!# (HQ & $ & HR')".
      by iMod ("Hq" with "[$HQ $HR']") as "$".
  Qed.

  Lemma wp_beep P Q :
    {{{ P ∗ beep_ P Q }}} beep {{{ RET UnitV; Q }}}.
  Proof.
    iIntros (Φ) "[HP Hbp] HΦ".
    iDestruct "Hbp" as (p q R) "(#Hp & % & #Hq)".
    iMod ("Hp" with "HP") as "[Htp HR]".
    iApply wp_fupd.
    rewrite beep_eq.
    iApply (wp_petrinet_io with "Htp"); eauto.
    iNext. iIntros "Htq".
    iMod ("Hq" with "[$Htq $HR]") as "HQ".
    by iModIntro; iApply ("HΦ" with "[$HQ]").
  Qed.

  Definition write :=
    Rec
      (Case
         (Var 1)
         Plang.Unit
         (Seq
            (IO (IOtag write_char_tag) (Fst (Var 0)))
            (LetIn (Snd (Var 0)) (App (Var 2) (Var 0)))
         )
      ).

  Lemma write_closed : ∀ f, write.[f] = write.
  Proof. done. Qed.

  Lemma write_eq :
    write =
    Rec
      (Case
         (Var 1)
         Plang.Unit
         (Seq
            (IO (IOtag write_char_tag) (Fst (Var 0)))
            (LetIn (Snd (Var 0)) (App (Var 2) (Var 0)))
         )
      ).
  Proof. trivial. Qed.

  Hint Rewrite write_closed : autosubst.

  Typeclasses Opaque write.
  Global Opaque write.

  Fixpoint write_prim_ p c q :=
    match c with
    | [] => p = q
    | v :: c' =>
      ∃ s, ThePetriNet (IOTr p write_char_tag v Plang.UnitV s)
           ∧ write_prim_ s c' q
    end.

  Definition write_char_ P v Q :=
    (∃ p q R, (P ={⊤}=> Token p ∗ R)
                ∗ ⌜ThePetriNet (IOTr p write_char_tag v Plang.UnitV q)⌝
                ∗ (Token q ∗ R ={⊤}=> Q))%I.

  Lemma write_char_frame P v Q R P' Q' :
    write_char_ P v Q -∗ (P' ={⊤}=> P ∗ R) -∗ (Q ∗ R ={⊤}=> Q') -∗
    write_char_ P' v Q'.
  Proof.
    iDestruct 1 as (p q R') "(#Hp & % & #Hq)".
    iIntros "#HP' #HQ'".
    iExists p, q, (R ∗ R')%I; repeat iSplit; eauto.
    - iIntros "!# Hp'". iMod ("HP'" with "Hp'") as "[HP $]".
      by iMod ("Hp" with "HP") as "[$ $]".
    - iIntros "!# (HQ & HR & HR')". iMod ("Hq" with "[$HQ $HR']") as "HQ".
      by iApply "HQ'"; iFrame.
  Qed.

  Fixpoint write_ P c Q :=
    match c with
    | [] => P ={⊤}=> Q
    | v :: c' =>
      ∃ S, write_char_ P v S ∗ write_ S c' Q
    end%I.

  Global Instance write_pers P c Q : Persistent (write_ P c Q).
  Proof.
    rewrite /Persistent.
    iIntros "Hwr".
    iInduction c as [|v c] "IH" forall (P Q).
    - by iDestruct "Hwr" as "#Hwr".
    - simpl. iDestruct "Hwr" as (S) "[#Hwv Hwr]".
      iExists S; iSplit; eauto.
      by iApply "IH".
  Qed.

  Lemma write_frame P c Q R P' Q' :
    write_ P c Q -∗ (P' ={⊤}=> P ∗ R) -∗ (Q ∗ R ={⊤}=> Q') -∗
    write_ P' c Q'.
  Proof.
    iIntros "#Hwr #HP #HQ".
    iInduction c as [|v c] "IH" forall (P' P Q) "Hwr HP HQ".
    - iIntros "!# Hp". iMod ("HP" with "Hp") as "[Hp HR]".
      iMod ("Hwr" with "Hp") as "Hq".
      iApply "HQ"; iFrame.
    - simpl. iDestruct "Hwr" as (S) "[Hwv Hwr]".
      iExists (S ∗ R)%I; iSplit.
      + iApply (write_char_frame with "[] []"); eauto.
        by iIntros "!# [$ $]".
      + iApply ("IH" with "[] [] []"); eauto.
  Qed.

  Lemma write_prim_extend p c q v q' :
    write_prim_ p c q → ThePetriNet (IOTr q write_char_tag v Plang.UnitV q') →
    write_prim_ p (c ++ [v]) q'.
  Proof.
    revert p q v; induction c => p q v Hc Hv.
    - simpl in *; simplify_eq.
      eexists _; repeat split; eauto.
    - destruct Hc as [s [Hs Hw]]; eexists _; eauto.
  Qed.

  Lemma write_extend P c Q c' Q' :
    write_ P c Q -∗ write_ Q c' Q' -∗ write_ P (c ++ c') Q'.
  Proof.
    iIntros "#Hwr #Hwr'".
    iInduction c as [|v c] "IH" forall (P).
    - simpl. iApply (write_frame _ _ _ True); eauto; rewrite !right_id; eauto.
      by iIntros "!# $".
    - simpl. iDestruct "Hwr" as (S) "[Hwv Hc]".
      iExists S; iFrame "#".
      iApply "IH"; eauto.
  Qed.

  Lemma wp_write p c q :
    write_prim_ p c q →
    {{{ Token p }}}
      (App write (of_val (of_list c)))
    {{{RET  UnitV; Token q }}}.
  Proof.
  iIntros (Hwr Φ) "Hp HΦ".
  iInduction c as [|x c] "IH" forall (p q Hwr).
  - simpl in *; subst.
    rewrite write_eq.
    iApply wp_pure_step_later; auto.
    rewrite -write_eq.
    iNext. asimpl.
    iApply wp_pure_step_later; auto.
    asimpl. iNext. iApply wp_value.
    by iApply "HΦ"; iFrame.
  - destruct Hwr as [s [Hs Hwr]]; simpl in *.
    rewrite write_eq.
    iApply wp_pure_step_later; auto.
    rewrite -write_eq.
    iNext. asimpl.
    iApply wp_pure_step_later; auto.
    asimpl. iNext.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_bind (fill [IORCtx (IOtagV _)])).
    iApply wp_pure_step_later; auto.
    iNext. iApply wp_value; simpl.
    iApply (wp_petrinet_io with "Hp"); eauto.
    iIntros "!> Hs".
    iApply wp_pure_step_later; auto.
    iNext. asimpl.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply wp_pure_step_later; auto.
    iNext. iApply wp_value; simpl.
    iApply wp_pure_step_later; auto.
    iNext. asimpl.
    iApply ("IH" with "[] Hs"); eauto.
  Qed.
 
  Section main.
    Variable buffer : loc.

    Definition main_ctx := scons (Loc buffer) ids.

    Definition putchar :=
      Lam
        (If
           (BinOp Eq (#n 1000) (App list_length (Load (Var 1))))
           (Seq (LetIn (Load (Var 1)) (App write (Var 0)))
                (Store (Var 1) (InjR (Pair (Var 0) (InjL Plang.Unit)))))
           (LetIn (Load (Var 1))
                  (Store (Var 2) (App (App snoc (Var 0)) (Var 1))))).

    Lemma putchar_closed :
      ∀ f, putchar.[up f] = putchar.
    Proof. by intros f; rewrite /putchar; asimpl. Qed.

    Hint Rewrite putchar_closed : autosubst.

    Lemma putchar_eq :
      putchar =
      Lam
        (If
           (BinOp Eq (#n 1000) (App list_length (Load (Var 1))))
           (Seq (LetIn (Load (Var 1)) (App write (Var 0)))
                (Store (Var 1) (InjR (Pair (Var 0) (InjL Plang.Unit)))))
           (LetIn (Load (Var 1))
                  (Store (Var 2) (App (App snoc (Var 0)) (Var 1))))).
    Proof. trivial. Qed.

    Typeclasses Opaque putchar.
    Global Opaque putchar.

    Definition buffer_token P :=
      (∃ c P0, buffer ↦ (of_list c) ∗ P0 ∗ write_ P0 c P)%I.

    Definition putchar_ p1 v p2 :=
      (∃ p'1 p'2 R,
          (p1 ={⊤}=> buffer_token p'1 ∗ R)
          ∧ (write_ p'1 [v] p'2)
          ∧ (buffer_token p'2 ∗ R ={⊤}=> p2) )%I.

  Lemma wp_putchar P v Q :
    {{{ P ∗ putchar_ P v Q }}}
      App (putchar.[main_ctx]) (of_val v)
    {{{RET UnitV; Q }}}.
  Proof.
    iIntros (Φ) "[HP Hpc] HΦ".
    iDestruct "Hpc" as (p1 p2 R) "(#Hp1 & #Hwr & #Hp2)".
    iMod ("Hp1" with "HP") as "[HP HR]".
    iDestruct "HP" as (c q) "(Hl & Hq & #Hwr')".
    rewrite putchar_eq.
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_bind (fill [IfCtx _ _])).
    iApply (wp_bind (fill [BinOpRCtx _ (#nv _)])).
    rewrite list_length_eq.
    iApply (wp_bind (fill [AppRCtx (RecV _)])); simpl.
    rewrite -list_length_eq.
    iApply (wp_load with "Hl"); iIntros "!> Hl".
    iApply wp_list_length; auto.
    iNext. iIntros (w Hw); subst.
    iApply wp_pure_step_later; trivial.
    rewrite /binop_eval.
    destruct PeanoNat.Nat.eq_dec.
    - iApply wp_value. iNext.
      iApply wp_pure_step_later; trivial.
      iNext.
      iApply (wp_bind (fill [SeqCtx _])).
      iApply (wp_bind (fill [LetInCtx _])).
      iApply (wp_load with "Hl"); iIntros "!> Hl /=".
      iApply wp_pure_step_later; trivial.
      iNext. asimpl.
      iApply (wp_write with "Hq"); eauto.
      iNext. iIntros "Hpt1"; simplify_eq.
      iApply wp_pure_step_later; trivial.
      iNext.
      iApply wp_fupd.
      iApply (wp_store with "Hl"); iIntros "!> Hl /=".
      iMod ("Hp2" with "[$HR Hpt1 Hl]") as "HQ".
      { iExists [_], _; iFrame; simpl; eauto. }
      by iModIntro; iApply "HΦ"; iFrame.
    - iApply wp_value.
      iNext.
      iApply wp_pure_step_later; trivial.
      iNext.
      iApply (wp_bind (fill [LetInCtx _])).
      iApply (wp_load with "Hl"); iIntros "!> Hl /=".
      iApply wp_pure_step_later; trivial. iNext. asimpl.
      iApply (wp_bind (fill [StoreRCtx (LocV _)])).
      iApply wp_snoc; auto.
      iNext. iIntros (w ?); simplify_eq; simpl.
      iApply wp_fupd.
      iApply (wp_store with "Hl"); iIntros "!> Hl /=".
      iMod ("Hp2" with "[$HR Hq Hl]") as "HQ".
      { iExists (_ ++ [_]), _; iFrame; simpl; eauto using write_extend. }
      by iModIntro; iApply "HΦ"; iFrame.
  Qed.

  Definition flush :=
    Seq (LetIn (Load (Var 0)) (App write (Var 0)))
        (Store (Var 0) (InjL Plang.Unit)).

  Lemma flush_closed : ∀ f, flush.[up f] = flush.
  Proof. done. Qed.

  Hint Rewrite flush_closed : autosubst.

  Lemma flush_eq :
    flush =
    Seq (LetIn (Load (Var 0)) (App write (Var 0)))
        (Store (Var 0) (InjL Plang.Unit)).
  Proof. trivial. Qed.

  Typeclasses Opaque flush.
  Global Opaque flush.

  Definition flush_ P Q :=
    (∃ p' R, (P ={⊤}=> buffer_token p' ∗ R)
               ∗ (Token p' ∗ buffer ↦ (InjLV UnitV) ∗ R ={⊤}=> Q))%I.

  Lemma wp_flush P Q :
    {{{ P ∗ flush_ P Q }}} flush.[main_ctx] {{{ RET UnitV; Q }}}.
  Proof.
    iIntros (Φ) "[HP Hfl] HΦ".
    iDestruct "Hfl" as (p' R) "(#Hp & #HQ)".
    iMod ("Hp" with "HP") as "[HP HR]".
    iDestruct "HP" as (c q) "(Hl & Hq & %)".
    rewrite flush_eq. asimpl.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_bind (fill [LetInCtx _])).
    iApply (wp_load with "Hl"); iIntros "!> Hl /=".
    iApply wp_pure_step_later; trivial.
    iNext. asimpl.
    iApply (wp_write with "Hq"); eauto.
    iNext. iIntros "Hp'"; subst.
    iApply wp_pure_step_later; trivial.
    iNext.
    iApply wp_fupd.
    iApply (wp_store with "Hl"); iIntros "!> Hl /=".
    iMod ("HQ" with "[$HR $Hp' $Hl]") as "Hq".
    by iModIntro; iApply "HΦ"; iFrame.
  Qed.

  Definition main :=
      (Seq beep (Seq (App (putchar) (#n 1)) flush)).

  Lemma wp_main Q1 Q2 Q3 Q4 :
    {{{ Q1 ∗ beep_ Q1 Q2 ∗ putchar_ Q2 (#nv 1) Q3 ∗ flush_ Q3 Q4 }}}
      main.[main_ctx]
    {{{RET UnitV; Q4 }}}.
  Proof.
    iIntros (Φ) "(HQ1 & #Hbp & #Hwr & #Hfl) HΦ".
    asimpl.
    iApply (wp_bind (fill [SeqCtx _])); simpl.
    iApply (wp_beep with "[HQ1]"); first by iFrame "#".
    iNext. iIntros "HQ2".
    iApply wp_pure_step_later; trivial.
    iNext.
    iApply (wp_bind (fill [SeqCtx _])); simpl.
    iApply (wp_putchar _ (NatV _) with "[HQ2] [HΦ]"); first by iFrame "#".
    iNext. iIntros "HQ3".
    iApply wp_pure_step_later; trivial.
    iNext.
    iApply (wp_flush with "[HQ3] [HΦ]"); by iFrame "#".
  Qed.

  End main.

  Definition start :=
    LetIn (Alloc (InjL Plang.Unit)) main.

  Lemma wp_start p1 p2 p3 :
    {{{ (Token p1) ∗ beep_ (Token p1) (Token p2) ∗ write_ (Token p2) [(#nv 1)] (Token p3) }}}
      start
    {{{RET UnitV; Token p3 }}}.
  Proof.
    iIntros (Φ) "(Hp1 & #Hbp & #Hwr) HΦ".
    iDestruct "Hwr" as (p2' p3' R) "(Hp2 & Hwr & Hp3)"; simpl in *.
    iDestruct "Hwr" as %[s [Hwr ?]]; simpl in *; simplify_eq.
    iApply (wp_bind (fill [LetInCtx _])).
    iApply (wp_alloc); auto; iNext; iIntros (l) "Hl /=".
    iApply wp_pure_step_later; trivial.
    iNext.
    iApply (wp_main _ (P1 ∗ l ↦ InjLV UnitV) (P2 ∗ l ↦ InjLV UnitV)
              (buffer_token l P3) (l ↦ InjLV UnitV ∗ P3)  with "[Hp1 Hl] [HΦ]")%I.

asimpl.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_beep with "[Hp1]")%I.
    { by iFrame "#". }
    iNext. iIntros "HP2". simpl.
    iApply wp_pure_step_later; trivial.
    iNext.
    iApply (wp_bind (fill [SeqCtx _])).
    iApply (wp_putchar _ (P2 ∗ l ↦ InjLV UnitV) (#nv _)
                       (buffer_token l p3 ∗ R)%I
              with "[HP2 Hl] [HΦ]").
    { iFrame. iExists _, _, R.
      repeat iSplit; eauto.
      - iIntros "!# [HP2 Hl]".
        iMod ("Hp2" with "HP2") as "[HP2 HR]".
        iFrame. iModIntro. iExists [], _; iFrame; eauto.
      -  by iIntros "!# [$ $]". }
    iNext. iIntros "[Hbt HR] /=".
    iApply wp_pure_step_later; trivial.
    iNext.
    iApply wp_fupd.
    iApply (wp_flush _ (buffer_token l p3 ∗ R) (Token p3 ∗ l ↦ InjLV UnitV ∗ R)
              with "[$Hbt $HR]")%I; eauto.
    { iExists _, R. iSplit.
      - by iIntros "!# [$ $]".
      - by iIntros "!# ($ & $ & $)". }
    iNext. iIntros "(HP3 & Hl & HR)".
    iMod ("Hp3" with "[$HP3 $HR]") as "HP3".
    by iApply "HΦ".
  Qed.


End buffered_io.

Inductive bufferedIO_places :=
  BIO_Start
| BIO_beep_done
| BIO_write_done.

Global Instance bufferedIO_places_eqdec :
  EqDecision bufferedIO_places.
Proof. solve_decision. Qed.

Instance bufferedIO_petri_placesC : PlacesC :=
  {| Places := bufferedIO_places |}.

Inductive bufferedIO_petri : PetriNet :=
| BIO_beepTR :
    bufferedIO_petri (IOTr BIO_Start beep_tag UnitV UnitV BIO_beep_done)
| BIO_writeTR :
    bufferedIO_petri (IOTr BIO_beep_done write_tag (#nv 1) UnitV BIO_write_done).

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

Lemma Valuation_unit V : V ⊎ (λ _, 0) = V.
Proof. extensionality z. rewrite /ValPlus; omega. Qed.

Ltac trvial_petri := match goal with
| H : bufferedIO_petri (SplitTr ?p _ _) |- _ => destruct p; inversion H
| H : bufferedIO_petri (JoinTr ?p _ _) |- _ => destruct p; inversion H
| H : bufferedIO_petri (NoOpTr ?p _) |- _ => destruct p; inversion H
end.

Lemma Traces_bufferedIO_petri τ :
  Traces bufferedIO_petri (singVAL BIO_Start) τ →
  τ = [] ∨ τ = [(beep_tag, UnitV, UnitV)] ∨
  τ = [(beep_tag, UnitV, UnitV); (write_tag, (#nv 1), UnitV)].
Proof.
  inversion 1; eauto; try trvial_petri.
  edestruct singVAL_eq; eauto; simplify_eq.
  match goal with
  | H: bufferedIO_petri (IOTr BIO_Start _ _ _ _) |- _ => inversion H; subst
  end.
  repeat match goal with
         | H : context [(λ _, 0)] |- _ =>
           rewrite Valuation_unit in H
         end.
  match goal with
  | H: Traces bufferedIO_petri (singVAL BIO_beep_done) _ |- _ =>
    inversion H; subst; eauto; try trvial_petri
  end.
  right; right.
  edestruct singVAL_eq; eauto; simplify_eq.
  match goal with
  | H: bufferedIO_petri (IOTr BIO_beep_done _ _ _ _) |- _ => inversion H; subst
  end.
  repeat match goal with
         | H : context [(λ _, 0)] |- _ =>
           rewrite Valuation_unit in H
         end.
  match goal with
  | H: Traces bufferedIO_petri (singVAL BIO_write_done) _ |- _ =>
    inversion H; subst; eauto; try trvial_petri
  end.
  edestruct singVAL_eq; eauto; simplify_eq.
  match goal with
  | H: bufferedIO_petri (IOTr BIO_write_done _ _ _ _) |- _ => inversion H; subst
  end.
Qed.

Lemma app_not_nil {A} (l l' : list A) x :
  l ++ x :: l' ≠ [].
Proof. induction l; auto. Qed.

Lemma bufferedIO_petri_ResultDet :
  ResultDet (Traces bufferedIO_petri (singVAL BIO_Start)).
Proof.
  intros t v v' v'' τ τ' τ'' Hτ Hτ'.
  apply Traces_bufferedIO_petri in Hτ;
    apply Traces_bufferedIO_petri in Hτ'.
  destruct τ as [|? []]; simpl in *; intuition; simplify_eq; auto.
  exfalso; eapply app_not_nil; eauto.
Qed.

Theorem wp_closed_start
        `{heapIPreIOG Σ}
        `{inG Σ (authUR (ofe_funUR (λ p : Places, natUR)))} :
  (|={⊤}=> ∃ γio, let _ := make_heapIG γio in
                 |={⊤}=> ∃ _ : petrinetIG Σ,
     FullIO (Traces bufferedIO_petri (singVAL BIO_Start))
            ∗ WP start {{v, ⌜v = UnitV⌝ }})%I.
Proof.
  iIntros "".
  pose (Traces bufferedIO_petri (singVAL BIO_Start)) as ios.
  iMod (@own_alloc _ io_monoid _
                   (● Excl' (ios : leibnizC ioSpec) ⋅
                      ◯ Excl' (ios : leibnizC ioSpec))) as (γio) "[HFI HOI]";
    first done.
  iModIntro. iExists _. pose (make_heapIG γio). iFrame.
  iMod (PetriNetInv_alloc with "HOI") as (γpn) "[#HPi HOV]".
  { apply bufferedIO_petri_ResultDet. }
  pose ({| γPN := γpn; ThePetriNet := bufferedIO_petri|}) as PN.
  iModIntro. iExists PN.
  set (tk := @Token bufferedIO_petri_placesC _ _ _).
  iAssert (tk BIO_Start) with "[$HOV]" as "HOS"; first done.
  iApply (wp_start (tk BIO_Start) (tk BIO_beep_done) (tk BIO_write_done)
            with "[$HOS]").
  { iSplit.
    - iExists _, _, True%I; repeat iSplit.
      + by iIntros "!# $".
      + iPureIntro; econstructor.
      + by iIntros "!# [$ _]".
    - iExists BIO_beep_done, BIO_write_done, True%I; repeat iSplit.
      + by iIntros "!# $".
      + iPureIntro. eexists _; simpl; split; eauto using bufferedIO_petri.
      + by iIntros "!# [$ _]". }
  by iIntros "!> _".
Qed.

Theorem start_safe :
  fully_erased_safe start (Traces bufferedIO_petri (singVAL BIO_Start)).
Proof.
  pose (#[IoΣ; petrinetΣ]) as Σ.
  apply (adequacy Σ _ ((λ _, True))%I).
  { apply Traces_prefix_closed. }
  intros Hig.
  iIntros "".
  iMod (wp_closed_start) as (γio) "Hlm".
  iMod ("Hlm") as (HIG) "[HFIO HWP]".
  iModIntro; iExists _; iFrame.
  by iApply @wp_wand_l; iFrame.
Qed.
