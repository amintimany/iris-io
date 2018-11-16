From iris.program_logic Require Export language ectx_language ectxi_language.
From iris_io.prelude Require Export base.
From iris_io Require Export lang_proph_erased.
From iris.algebra Require Export ofe.
From stdpp Require Import gmap.

Module Plang_noproph.

  Record noproph_state : Type :=
    { NPHeap : gmap loc val;
      NPIO : list (ioTag * val * val)
    }.

  Definition update_NPheap σ h :=
    {| NPHeap := h; NPIO := NPIO σ |}.

   Definition update_NPIO σ τ :=
    {| NPHeap := NPHeap σ; NPIO := τ |}.

  Inductive noproph_head_step :
    expr → noproph_state → expr → noproph_state → list expr → Prop :=
  (* β *)
  | NPBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      noproph_head_step (App (Rec e1) e2) σ e1.[(Rec e1), e2/] σ []
  | NPZetaS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      noproph_head_step (LetIn e1 e2) σ e2.[e1/] σ []
  | NPLamBetaS e1 e2 v2 σ :
      to_val e2 = Some v2 →
      noproph_head_step (App (Lam e1) e2) σ e1.[e2/] σ []
  | NPSeqS e1 e2 v1 σ :
      to_val e1 = Some v1 →
      noproph_head_step (Seq e1 e2) σ e2 σ []
  (* Products *)
  | NPFstS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      noproph_head_step (Fst (Pair e1 e2)) σ e1 σ []
  | NPSndS e1 v1 e2 v2 σ :
      to_val e1 = Some v1 → to_val e2 = Some v2 →
      noproph_head_step (Snd (Pair e1 e2)) σ e2 σ []
  (* Sums *)
  | NPCaseLS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      noproph_head_step (Case (InjL e0) e1 e2) σ e1.[e0/] σ []
  | NPCaseRS e0 v0 e1 e2 σ :
      to_val e0 = Some v0 →
      noproph_head_step (Case (InjR e0) e1 e2) σ e2.[e0/] σ []
    (* nat bin op *)
  | NPBinOpS op a b σ :
      noproph_head_step (BinOp op (#n a) (#n b)) σ (of_val (binop_eval op a b)) σ []
  (* If then else *)
  | NPIfFalse e1 e2 σ :
      noproph_head_step (If (#♭ false) e1 e2) σ e2 σ []
  | NPIfTrue e1 e2 σ :
      noproph_head_step (If (#♭ true) e1 e2) σ e1 σ []
  (* Recursive Types *)
  | NPUnfold_Fold e v σ :
      to_val e = Some v →
      noproph_head_step (Unfold (Fold e)) σ e σ []
  (* Polymorphic Types *)
  | NPTBeta e σ :
      noproph_head_step (TApp (TLam e)) σ e σ []
  (* Concurrency *)
  | NPForkS e σ:
      noproph_head_step (Fork e) σ Unit σ [e]
  (* Reference Types *)
  | NPAllocS e v σ l :
     to_val e = Some v → (NPHeap σ) !! l = None →
     noproph_head_step (Alloc e) σ (Loc l) (update_NPheap σ (<[l:=v]>(NPHeap σ))) []
  | NPLoadS l v σ :
     (NPHeap σ) !! l = Some v →
     noproph_head_step (Load (Loc l)) σ (of_val v) σ []
  | NPStoreS l e v σ :
     to_val e = Some v → is_Some ((NPHeap σ) !! l) →
     noproph_head_step (Store (Loc l) e) σ Unit (update_NPheap σ (<[l:=v]>(NPHeap σ))) []
  (* Compare and swap *)
  | NPCasFailS l e1 v1 e2 v2 vl σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     (NPHeap σ) !! l = Some vl → vl ≠ v1 →
     noproph_head_step (CAS (Loc l) e1 e2) σ (#♭ false) σ []
  | NPCasSucS l e1 v1 e2 v2 σ :
     to_val e1 = Some v1 → to_val e2 = Some v2 →
     (NPHeap σ) !! l = Some v1 →
     noproph_head_step (CAS (Loc l) e1 e2) σ (#♭ true) (update_NPheap σ (<[l:=v2]>(NPHeap σ))) []
  (* Prophecy operational semantics *)
  | NPCreate_PrS σ :
      noproph_head_step Create_Pr σ Unit σ []
  | NPAssignS v v' e e' σ : to_val e = Some v → to_val e' = Some v' →
     noproph_head_step (Assign_Pr e e') σ Unit σ []
  | NPRandS b σ : noproph_head_step Rand σ (Bool b) σ []
  | NPIOS t e v v' σ : to_val e = Some v →
                    noproph_head_step (IO (IOtag t) e) σ (of_val v')
                              (update_NPIO σ ((NPIO σ) ++ [(t, v, v')])) [].

  (** Basic properties about the language *)
  Lemma val_stuck e1 σ1 e2 σ2 ef :
    noproph_head_step e1 σ1 e2 σ2 ef → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma head_ctx_step_val Ki e σ1 e2 σ2 ef :
    noproph_head_step (fill_item Ki e) σ1 e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma alloc_fresh e v σ :
    let l := fresh (dom (gset loc) (NPHeap σ)) in
    to_val e = Some v → noproph_head_step (Alloc e) σ (Loc l)
                                         (update_NPheap σ (<[l:=v]>(NPHeap σ))) [].
  Proof. by intros; apply NPAllocS, (not_elem_of_dom (D:=gset loc)), is_fresh. Qed.

  Lemma val_head_stuck e1 σ1 e2 σ2 efs : noproph_head_step e1 σ1 e2 σ2 efs → to_val e1 = None.
  Proof. destruct 1; naive_solver. Qed.

  Lemma lang_mixin : EctxiLanguageMixin of_val to_val fill_item
                                        noproph_head_step.
  Proof.
    split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
           fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
  Qed.

End Plang_noproph.

Canonical Structure PNP_ectxi_lang :=
  EctxiLanguage Plang_noproph.lang_mixin.
Canonical Structure PNP_ectx_lang :=
  EctxLanguageOfEctxi PNP_ectxi_lang.
Canonical Structure PNP_lang :=
  LanguageOfEctx PNP_ectx_lang.

Export Plang_noproph.

Definition noproph_safe e (M : ioSpec) :=
  ∀ th2 σ2,
    M (NPIO σ2) →
    rtc (@step PNP_lang) ([e], {| NPHeap := ∅; NPIO := [] |})
        (th2, σ2) →
    ∀ e, e ∈ th2 → AsVal e ∨
                   (∃ e' σ'' efs,
                       @language.prim_step PNP_lang e σ2 e' σ'' efs
                       ∧ ∀ t v v', NPIO σ'' = NPIO σ2 ++ [(t, v, v')] →
                                   ∃ v'', M (NPIO σ2 ++ [(t, v, v'')])).