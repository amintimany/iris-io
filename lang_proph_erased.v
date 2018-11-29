From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export lang.
From iris.algebra Require Export ofe.
From stdpp Require Import gmap.

Module Plang_erased.

  Record erased_state : Type :=
    { EHeap : gmap loc val;
      EProph : (gset loc);
      EioState : ioSpec
    }.

  Definition update_Eheap σ h :=
    {| EHeap := h; EProph := EProph σ; EioState := EioState σ |}.

  Definition update_Eproph σ ι :=
    {| EHeap := EHeap σ; EProph := ι; EioState := EioState σ |}.

  Definition update_EioState σ T :=
    {| EHeap := EHeap σ; EProph := EProph σ; EioState := T |}.

  Inductive erased_head_step :
    expr → erased_state → expr → erased_state → list expr → Prop :=
  (* β *)
  | EBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      erased_head_step (App (Rec e1) e2) σ e1.[(Rec e1), e2/] σ []
  | EZetaS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      erased_head_step (LetIn e1 e2) σ e2.[e1/] σ []
  | ELamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      erased_head_step (App (Lam e1) e2) σ e1.[e2/] σ []
  | ESeqS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      erased_head_step (Seq e1 e2) σ e2 σ []
  (* Products *)
  | EFstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      erased_head_step (Fst (Pair e1 e2)) σ e1 σ []
  | ESndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      erased_head_step (Snd (Pair e1 e2)) σ e2 σ []
  (* Sums *)
  | ECaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      erased_head_step (Case (InjL e0) e1 e2) σ e1.[e0/] σ []
  | ECaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      erased_head_step (Case (InjR e0) e1 e2) σ e2.[e0/] σ []
    (* nat bin op *)
  | EBinOpS op a b σ :
      erased_head_step (BinOp op (#n a) (#n b)) σ (of_val (binop_eval op a b)) σ []
  (* If then else *)
  | EIfFalse e1 e2 σ :
      erased_head_step (If (#♭ false) e1 e2) σ e2 σ []
  | EIfTrue e1 e2 σ :
      erased_head_step (If (#♭ true) e1 e2) σ e1 σ []
  (* Recursive Types *)
  | EUnfold_Fold e v σ :
      to_val e = Some v →
      erased_head_step (Unfold (Fold e)) σ e σ []
  (* Polymorphic Types *)
  | ETBeta e σ :
      erased_head_step (TApp (TLam e)) σ e σ []
  (* Concurrency *)
  | EForkS e σ:
      erased_head_step (Fork e) σ Unit σ [e]
  (* Reference Types *)
  | EAllocS e v σ l :
     to_val e = Some v → (EHeap σ) !! l = None →
     erased_head_step (Alloc e) σ (Loc l) (update_Eheap σ (<[l:=v]>(EHeap σ))) []
  | ELoadS l v σ :
     (EHeap σ) !! l = Some v →
     erased_head_step (Load (Loc l)) σ (of_val v) σ []
  | EStoreS l e v σ :
     to_val e = Some v → is_Some ((EHeap σ) !! l) →
     erased_head_step (Store (Loc l) e) σ Unit (update_Eheap σ (<[l:=v]>(EHeap σ))) []
  (* Compare and swap *)
  | ECasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     (EHeap σ) !! l = Some vl → vl ≠ v1 →
     erased_head_step (CAS (Loc l) e1 e2) σ (#♭ false) σ []
  | ECasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     (EHeap σ) !! l = Some v1 →
     erased_head_step (CAS (Loc l) e1 e2) σ (#♭ true) (update_Eheap σ (<[l:=v2]>(EHeap σ))) []
  (* Prophecy operational semantics *)
  | ECreate_PrS σ :
      erased_head_step Create_Pr σ (Pr (fresh (EProph σ)))
                       (update_Eproph σ ({[fresh (EProph σ)]} ∪ (EProph σ))) []
  | EAssignS v l e σ :
      to_val e = Some v → erased_head_step (Assign_Pr (Pr l) e) σ Unit σ []
  | ERandS b σ : erased_head_step Rand σ (Bool b) σ []
  | EIOS t e v v' σ : to_val e = Some v → (EioState σ) [(t, v, v')] →
                    erased_head_step (IO (IOtag t) e) σ (of_val v')
                              (update_EioState σ (λ τ, (EioState σ) ((t, v, v') :: τ))) [].

  (** Basic properties about the language *)
  Lemma val_stuck e1 σ1 e2 σ2 ef :
    erased_head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
    erased_head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom (gset loc) (EHeap σ)) in
    to_val e = Some v → erased_head_step (Alloc e) σ (Loc l)
                                         (update_Eheap σ (<[l:=v]>(EHeap σ))) [].
  Proof. by intros; apply EAllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

  Lemma val_head_stuck e1 σ1 e2 σ2 efs : erased_head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item erased_head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

End Plang_erased.

Canonical Structure PE_ectxi_lang :=
  EctxiLanguage Plang_erased.lang_mixin.
Canonical Structure PE_ectx_lang :=
  EctxLanguageOfEctxi PE_ectxi_lang.
Canonical Structure PE_lang :=
  LanguageOfEctx PE_ectx_lang.

Export Plang_erased.
