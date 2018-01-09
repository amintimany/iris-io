From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants big_op.
From iris.algebra Require Import auth frac agree gmap.
From iris_io Require Export lang.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.
Import uPred.

(** The CMRA for the heap of the implementation. This is linked to the
    physical heap. *)
Class heapIG Σ := HeapIG {
  heapI_invG : invG Σ;
  heapI_gen_heapG :> gen_heapG loc val Σ;
  prophI_gen_heapG :> gen_heapG loc Proph Σ;
}.

Instance heapIG_irisG `{heapIG Σ} : irisG P_lang Σ := {
  iris_invG := heapI_invG;
  state_interp := λ σ, ((gen_heap_ctx σ.1) ∗ (gen_heap_ctx σ.2))%I
}.
Global Opaque iris_invG.

Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : uPred_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=val) l 1 v) (at level 20) : uPred_scope.

Notation "l ↦ₚ v" := (mapsto (L:=loc) (V:=Proph) l 1 v) (at level 20) : uPred_scope.

Section lang_rules.
  Context `{heapIG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v w : val.

  Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : _ = of_val ?v |- _ =>
     is_var v; destruct v; first[discriminate H|injection H as H]
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

  Local Hint Extern 0 (atomic _) => solve_atomic.
  Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _; simpl.

  Local Hint Constructors head_step.
  Local Hint Resolve alloc_fresh.
  Local Hint Resolve to_of_val.

  (** Base axioms for core primitives of the language: Stateful reductions. *)
  Lemma wp_alloc E e v :
    IntoVal e v →
    {{{ True }}} Alloc e @ E {{{ l, RET (LocV l); l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros ([σ1 σ1p]) "[Hσ Hσp] /= !>"; iSplit.
    { iPureIntro. eexists _, _, _; by apply alloc_fresh. }
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_alloc with "Hσ") as "[Hσ Hl]"; first done.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_load E l q v :
  {{{ ▷ l ↦{q} v }}} Load (Loc l) @ E {{{ RET v; l ↦{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros ([σ1 σ1p]) "[Hσ Hσp] !>".
    iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto.
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_store E l v' e v :
    IntoVal e v →
    {{{ ▷ l ↦ v' }}} Store (Loc l) e @ E
    {{{ RET UnitV; l ↦ v }}}.
  Proof.
    iIntros (<-%of_to_val Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros ([σ1 σ1p]) "[Hσ Hσp] !>".
    iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit.
    { iPureIntro. eexists _, _, _; simpl. econstructor; eauto. }
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
    iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_cas_fail E l q v' e1 v1 e2 v2 :
    IntoVal e1 v1 → IntoVal e2 v2 → v' ≠ v1 →
    {{{ ▷ l ↦{q} v' }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV false); l ↦{q} v' }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val ? Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros ([σ1 σ1p]) "[Hσ Hσp] !>".
    iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto.
    iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_cas_suc E l e1 v1 e2 v2 :
    IntoVal e1 v1 → IntoVal e2 v2 →
    {{{ ▷ l ↦ v1 }}} CAS (Loc l) e1 e2 @ E
    {{{ RET (BoolV true); l ↦ v2 }}}.
  Proof.
    iIntros (<-%of_to_val <-%of_to_val Φ) ">Hl HΦ".
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros ([σ1 σ1p]) "[Hσ Hσp] !>".
    iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
    iSplit.
    { iPureIntro. eexists _, _, _; simpl. econstructor; done. }
    iNext; iIntros (v2' σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
    iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_create_pr E :
    {{{ True }}} Create_Pr @ E {{{ l, RET (PrV l); ∃ p, l ↦ₚ p }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros ([σ1 σ1p]) "[Hσ Hσp] /= !>"; iSplit.
    { iPureIntro. eexists _, _, _; simpl. apply create_pr. }
    iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
    iMod (@gen_heap_alloc with "Hσp") as "[Hσp Hl]".
    eapply (not_elem_of_dom (D := gset loc)), is_fresh.
    iModIntro; iSplit=> //. iFrame. iApply "HΦ"; eauto.
  Qed.

  Lemma wp_assign_pr E l e v p :
    IntoVal e v →
    {{{ l ↦ₚ p }}} Assign_Pr (Pr l) e @ E
                   {{{ RET UnitV; ⌜v = Shead p⌝ ∗ l ↦ₚ Stail p}}}.
  Proof.
    iIntros (<-%of_to_val Φ) "Hpr HΦ".
    destruct (decide (v = (Shead p))); first simplify_eq.
    - iApply wp_lift_atomic_head_step_no_fork; auto.
      iIntros ([σ1 σ1p]) "[Hσ Hσp] /= !>".
      iDestruct (@gen_heap_valid with "Hσp Hpr") as %?.
      iSplit.
      { iPureIntro. eexists _, _, _; simpl. econstructor; eauto. }
      iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
      iMod (@gen_heap_update with "Hσp Hpr") as "[$ Hpr]".
      iModIntro; iSplit=> //. iFrame. iApply "HΦ"; auto.
    - iClear "HΦ".
      iLöb as "IH".
      iApply wp_lift_head_step; auto.
      iIntros ([σ1 σ1p]) "[Hσ Hσp] /=".
      iDestruct (@gen_heap_valid with "Hσp Hpr") as %?.
      iMod (fupd_intro_mask') as "HM"; last iModIntro; first set_solver.
      iSplit.
      { iPureIntro. eexists _, _, _; simpl. eapply AssignFailS; eauto. }
      iNext; iIntros (v2 σ2 efs Hstep); inv_head_step.
      iMod "HM" as "_". iModIntro.
      iFrame. iSplit; last done. iApply "IH"; auto.
  Qed.

  Lemma wp_fork E e Φ :
    ▷ (|={E}=> Φ UnitV) ∗ ▷ WP e {{ _, True }} ⊢ WP Fork e @ E {{ Φ }}.
  Proof.
  rewrite -(wp_lift_pure_det_head_step (Fork e) Unit [e]) //=; eauto.
  - iIntros "[H1 H2]"; iModIntro; iNext; iModIntro; iFrame.
      by iApply wp_value_fupd.
  - intros; inv_head_step; eauto.
  Qed.

  Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
  Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
  Local Ltac solve_pure_exec :=
    unfold IntoVal, AsVal in *; subst;
    repeat match goal with H : is_Some _ |- _ => destruct H as [??] end;
    apply det_head_step_pure_exec; [ solve_exec_safe | solve_exec_puredet ].

  Global Instance pure_rec e1 e2 `{!AsVal e2} :
    PureExec True (App (Rec e1) e2) e1.[(Rec e1), e2 /].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_tlam e : PureExec True (TApp (TLam e)) e.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fold e `{!AsVal e}:
    PureExec True (Unfold (Fold e)) e.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_fst e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True (Fst (Pair e1 e2)) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_snd e1 e2 `{!AsVal e1, !AsVal e2} :
    PureExec True (Snd (Pair e1 e2)) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inl e0 e1 e2 `{!AsVal e0}:
    PureExec True (Case (InjL e0) e1 e2) e1.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance pure_case_inr e0 e1 e2 `{!AsVal e0}:
    PureExec True (Case (InjR e0) e1 e2) e2.[e0/].
  Proof. solve_pure_exec. Qed.

  Global Instance wp_if_true e1 e2 :
    PureExec True (If (#♭ true) e1 e2) e1.
  Proof. solve_pure_exec. Qed.

  Global Instance wp_if_false e1 e2 :
    PureExec True (If (#♭ false) e1 e2) e2.
  Proof. solve_pure_exec. Qed.

  Global Instance wp_nat_binop op a b :
    PureExec True (BinOp op (#n a) (#n b)) (of_val (binop_eval op a b)).
  Proof. solve_pure_exec. Qed.

End lang_rules.
