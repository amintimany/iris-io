From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export lang_proph_erased.
From iris.algebra Require Export ofe.
From stdpp Require Import gmap.

Module Plang_fully_erased.

  Record fully_erased_state : Type :=
    { FEHeap : gmap loc val;
      FEProph : (gset loc);
      FEIO : list (ioTag * val * val)
    }.

  Definition update_FEheap σ h :=
    {| FEHeap := h; FEProph := FEProph σ; FEIO := FEIO σ |}.

  Definition update_FEproph σ ι :=
    {| FEHeap := FEHeap σ; FEProph := ι; FEIO := FEIO σ |}.

   Definition update_FEIO σ τ :=
    {| FEHeap := FEHeap σ; FEProph := FEProph σ; FEIO := τ |}.

  Inductive fully_erased_head_step :
    expr → fully_erased_state → expr → fully_erased_state → list expr → Prop :=
  (* β *)
  | FEBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      fully_erased_head_step (App (Rec e1) e2) σ e1.[(Rec e1), e2/] σ []
  | FEZetaS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      fully_erased_head_step (LetIn e1 e2) σ e2.[e1/] σ []
  | FEGRZetaS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      fully_erased_head_step (GRLetIn e1 e2) σ e2.[e1/] σ []
  | FELamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      fully_erased_head_step (App (Lam e1) e2) σ e1.[e2/] σ []
  | FESeqS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      fully_erased_head_step (Seq e1 e2) σ e2 σ []
  | FEGRSeqS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      fully_erased_head_step (GRSeq e1 e2) σ e2 σ []
  (* Products *)
  | FEFstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      fully_erased_head_step (Fst (Pair e1 e2)) σ e1 σ []
  | FESndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      fully_erased_head_step (Snd (Pair e1 e2)) σ e2 σ []
  (* Sums *)
  | FECaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      fully_erased_head_step (Case (InjL e0) e1 e2) σ e1.[e0/] σ []
  | FECaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      fully_erased_head_step (Case (InjR e0) e1 e2) σ e2.[e0/] σ []
    (* nat bin op *)
  | FEBinOpS op a b σ :
      fully_erased_head_step (BinOp op (#n a) (#n b)) σ (of_val (binop_eval op a b)) σ []
  (* If then else *)
  | FEIfFalse e1 e2 σ :
      fully_erased_head_step (If (#♭ false) e1 e2) σ e2 σ []
  | FEIfTrue e1 e2 σ :
      fully_erased_head_step (If (#♭ true) e1 e2) σ e1 σ []
  (* Recursive Types *)
  | FEUnfold_Fold e v σ :
      to_val e = Some v →
      fully_erased_head_step (Unfold (Fold e)) σ e σ []
  (* Polymorphic Types *)
  | FETBeta e σ :
      fully_erased_head_step (TApp (TLam e)) σ e σ []
  (* Concurrency *)
  | FEForkS e σ:
      fully_erased_head_step (Fork e) σ Unit σ [e]
  (* Reference Types *)
  | FEAllocS e v σ l :
     to_val e = Some v → (FEHeap σ) !! l = None →
     fully_erased_head_step (Alloc e) σ (Loc l) (update_FEheap σ (<[l:=v]>(FEHeap σ))) []
  | FELoadS l v σ :
     (FEHeap σ) !! l = Some v →
     fully_erased_head_step (Load (Loc l)) σ (of_val v) σ []
  | FEStoreS l e v σ :
     to_val e = Some v → is_Some ((FEHeap σ) !! l) →
     fully_erased_head_step (Store (Loc l) e) σ Unit (update_FEheap σ (<[l:=v]>(FEHeap σ))) []
  (* Compare and swap *)
  | FECasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     (FEHeap σ) !! l = Some vl → vl ≠ v1 →
     fully_erased_head_step (CAS (Loc l) e1 e2) σ (#♭ false) σ []
  | FECasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     (FEHeap σ) !! l = Some v1 →
     fully_erased_head_step (CAS (Loc l) e1 e2) σ (#♭ true) (update_FEheap σ (<[l:=v2]>(FEHeap σ))) []
  (* Prophecy operational semantics *)
  | FECreate_PrS σ :
      fully_erased_head_step Create_Pr σ (Pr (fresh (FEProph σ)))
                       (update_FEproph σ ({[fresh (FEProph σ)]} ∪ (FEProph σ))) []
  | FEAssignS e v e' v' σ :
      to_val e = Some v → to_val e' = Some v' →
     fully_erased_head_step (Assign_Pr e e') σ Unit σ []
  | FERandS b σ : fully_erased_head_step Rand σ (Bool b) σ []
  | FEIOS t e v v' σ : to_val e = Some v →
                    fully_erased_head_step (IO (IOtag t) e) σ (of_val v')
                              (update_FEIO σ ((FEIO σ) ++ [(t, v, v')])) [].

  (** Basic properties about the language *)
  Lemma val_stuck e1 σ1 e2 σ2 ef :
    fully_erased_head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
    fully_erased_head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom (gset loc) (FEHeap σ)) in
    to_val e = Some v → fully_erased_head_step (Alloc e) σ (Loc l)
                                         (update_FEheap σ (<[l:=v]>(FEHeap σ))) [].
  Proof. by intros; apply FEAllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

  Lemma val_head_stuck e1 σ1 e2 σ2 efs : fully_erased_head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item
                                        fully_erased_head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

End Plang_fully_erased.

Canonical Structure PFE_ectxi_lang :=
  EctxiLanguage Plang_fully_erased.lang_mixin.
Canonical Structure PFE_ectx_lang :=
  EctxLanguageOfEctxi PFE_ectxi_lang.
Canonical Structure PFE_lang :=
  LanguageOfEctx PFE_ectx_lang.

Export Plang_fully_erased.

Definition IO_reducible M e σ :=
  ∃ e' σ'' efs,
    @language.prim_step PFE_lang e σ e' σ'' efs
    ∧ ∀ t v v', FEIO σ'' = FEIO σ ++ [(t, v, v')] →
                ∃ v'', M (FEIO σ ++ [(t, v, v'')]).

Definition IO_not_failed M e σ := AsVal e ∨ IO_reducible M e σ.

Definition cfg_not_failed M (th : list expr) σ :=
  ∀ e, e ∈ th → IO_not_failed M e σ.

Definition fully_erased_safe e (M : ioSpec) :=
  ∀ th2 σ2,
    M (FEIO σ2) →
    rtc (@step PFE_lang) ([e], {| FEHeap := ∅; FEProph := ∅; FEIO := [] |})
        (th2, σ2) → cfg_not_failed M th2 σ2.

