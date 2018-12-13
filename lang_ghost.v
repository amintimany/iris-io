From iris_io Require Export lang.

Section Autosubst_Lemmas.
  Context {term : Type} {Ids_term : Ids term}
          {Rename_term : Rename term} {Subst_term : Subst term}
          {SubstLemmas_term : SubstLemmas term}.

  Lemma iter_up (m x : nat) (f : var → term) :
    upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
  Proof.
    revert x; induction m as [|m IH]=> -[|x];
      repeat (case_match || asimpl || rewrite IH); auto with omega.
  Qed.
End Autosubst_Lemmas.

Fixpoint ghost_ok (e: expr): Prop :=
  match e with
  | Var x => True
  | Unit => True
  | Bool b => True
  | Nat n => True
  | Pr p => True
  | Loc l => True
  | Rec e => True
  | Lam e => True
  | TLam e => True
  | Pair e1 e2 => ghost_ok e1 /\ ghost_ok e2
  | InjL e => ghost_ok e
  | InjR e => ghost_ok e
  | Fold e => ghost_ok e
  | Create_Pr => True
  | Assign_Pr e1 e2 => ghost_ok e1 /\ ghost_ok e2
  | _ => False
  end.

Lemma ghost_ok_subst e f : (forall x, ghost_ok (f x)) → ghost_ok e → ghost_ok e.[f].
Proof. revert f; induction e; intros f Hf; asimpl; intuition auto. Qed.


Inductive var_erases_to: list bool -> var -> var -> Prop :=
| var_erases_to_real_O gs:
    var_erases_to (false :: gs) O O
| var_erases_to_real_S gs x x':
    var_erases_to gs x x' ->
    var_erases_to (false :: gs) (S x) (S x')
| var_erases_to_ghost_S gs x x':
    var_erases_to gs x x' ->
    var_erases_to (true :: gs) (S x) x'.

Lemma var_erases_to_not_ghost gs x y :
  var_erases_to gs x y → gs !! x = Some false.
Proof. induction 1; auto. Qed.


  Lemma var_erases_to_closed gb x x' f :
    var_erases_to gb x x' → (Var x).[upn (length gb) f] = Var x.
  Proof.
    induction 1; asimpl in *; auto.
    - by rewrite IHvar_erases_to.
    - by rewrite IHvar_erases_to.
  Qed.

Inductive erases_to : nat → list bool -> expr -> expr -> Prop :=
  | Var_erases_to gs x x':
    var_erases_to gs x x' ->
    erases_to 0 gs (Var x) (Var x')
  | Rec_erases_to n gs e e':
    erases_to n (false :: false :: gs) e e' ->
    erases_to (S n) gs (Rec e) (Rec e')
  | Lam_erases_to n gs e e':
    erases_to n (false :: gs) e e' ->
    erases_to (S n) gs (Lam e) (Lam e')
  | LetIn_erases_to n m gs e1 e2 e1' e2':
    erases_to n gs e1 e1' ->
    erases_to m (false :: gs) e2 e2' ->
    erases_to  (S n + m) gs (LetIn e1 e2) (LetIn e1' e2')
  | GRLetIn_erases_to n gs e1 e2 e2':
    ghost_ok e1 ->
    (∀ f, e1.[upn (length gs) f] = e1) →
    erases_to n (true :: gs) e2 e2' ->
    erases_to (S n) gs (GRLetIn e1 e2) e2'
  | Seq_erases_to n m gs e1 e2 e1' e2':
    erases_to n gs e1 e1' ->
    erases_to m gs e2 e2' ->
    erases_to (S n + m) gs (Seq e1 e2) (Seq e1' e2')
  | GRSeq_erases_to n gs e1 e2 e2':
    ghost_ok e1 ->
    (∀ f, e1.[upn (length gs) f] = e1) →
    erases_to n gs e2 e2' ->
    erases_to (S n) gs (GRSeq e1 e2) e2'
  | App_erases_to n m gs e1 e2 e1' e2':
    erases_to n gs e1 e1' ->
    erases_to m gs e2 e2' ->
    erases_to (S n + m) gs (App e1 e2) (App e1' e2')
  | Unit_erases_to gs:
    erases_to 0 gs Unit Unit
  | Nat_erases_to gs n:
    erases_to 0 gs (Nat n) (Nat n)
  | Bool_erases_to gs b:
    erases_to 0 gs (Bool b) (Bool b)
  | BinOp_erases_to n m gs op e1 e2 e1' e2':
    erases_to n gs e1 e1' ->
    erases_to m gs e2 e2' ->
    erases_to (S n + m) gs (BinOp op e1 e2) (BinOp op e1' e2')
  | If_erases_to n m k gs e0 e1 e2 e0' e1' e2':
    erases_to n gs e0 e0' ->
    erases_to m gs e1 e1' ->
    erases_to k gs e2 e2' ->
    erases_to (S n + m + k) gs (If e0 e1 e2) (If e0' e1' e2')
  | Pair_erases_to n m gs e1 e2 e1' e2':
    erases_to n gs e1 e1' ->
    erases_to m gs e2 e2' ->
    erases_to (S n + m) gs (Pair e1 e2) (Pair e1' e2')
  | Fst_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (Fst e) (Fst e')
  | Snd_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (Snd e) (Snd e')
  | InjL_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (InjL e) (InjL e')
  | InjR_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (InjR e) (InjR e')
  | Case_erases_to n m k gs e0 e1 e2 e0' e1' e2':
    erases_to n gs e0 e0' ->
    erases_to m (false :: gs) e1 e1' ->
    erases_to k (false :: gs) e2 e2' ->
    erases_to (S n + m + k) gs (Case e0 e1 e2) (Case e0' e1' e2')
  | Fold_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (Fold e) (Fold e')
  | Unfold_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (Unfold e) (Unfold e')
  | TLam_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (TLam e) (TLam e')
  | TApp_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (TApp e) (TApp e')
  | Fork_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (Fork e) (Fork e')
  | Loc_erases_to gs l:
    erases_to 0 gs (Loc l) (Loc l)
  | IOtag_erases_to gs t:
    erases_to 0 gs (IOtag t) (IOtag t)
  | Alloc_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (Alloc e) (Alloc e')
  | Load_erases_to n gs e e':
    erases_to n gs e e' ->
    erases_to (S n) gs (Load e) (Load e')
  | Store_erases_to n m gs e1 e2 e1' e2':
    erases_to n gs e1 e1' ->
    erases_to m gs e2 e2' ->
    erases_to (S n + m) gs (Store e1 e2) (Store e1' e2')
  | CAS_erases_to n m k gs e0 e1 e2 e0' e1' e2':
    erases_to n gs e0 e0' ->
    erases_to m gs e1 e1' ->
    erases_to k gs e2 e2' ->
    erases_to (S n + m + k) gs (CAS e0 e1 e2) (CAS e0' e1' e2')
  | Rand_erases_to gs:
    erases_to 0 gs Rand Rand
  | IO_erases_to n m gs e1 e2 e1' e2':
    erases_to n gs e1 e1' ->
    erases_to m gs e2 e2' ->
    erases_to (S n + m) gs (IO e1 e2) (IO e1' e2')
  .

  Lemma erases_to_closed n gb e e' f :
    erases_to n gb e e' → e.[upn (length gb) f] = e.
  Proof.
    induction 1; eauto using var_erases_to_closed; asimpl in *;
    repeat match goal with
           | H : _ = _ :> expr |- _ => progress (rewrite H; clear H)
           | H : forall _, _ = _ :> expr |- _ => progress (rewrite H; clear H)
           end; auto.
  Qed.

  Inductive val_erases_to: val -> val -> Prop :=
  | RecV_erases_to n e e':
    erases_to n (false :: false :: []) e e' ->
    val_erases_to (RecV e) (RecV e')
  | LamV_erases_to n e e':
    erases_to n (false :: []) e e' ->
    val_erases_to (LamV e) (LamV e')
  | UnitV_erases_to:
    val_erases_to UnitV UnitV
  | NatV_erases_to n:
    val_erases_to (NatV n) (NatV n)
  | BoolV_erases_to b:
    val_erases_to (BoolV b) (BoolV b)
  | PairV_erases_to v1 v2 v1' v2':
    val_erases_to v1 v1' ->
    val_erases_to v2 v2' ->
    val_erases_to (PairV v1 v2) (PairV v1' v2')
  | InjLV_erases_to v v':
    val_erases_to v v' ->
    val_erases_to (InjLV v) (InjLV v')
  | InjRV_erases_to v v':
    val_erases_to v v' ->
    val_erases_to (InjRV v) (InjRV v')
  | FoldV_erases_to v v':
    val_erases_to v v' ->
    val_erases_to (FoldV v) (FoldV v')
  | TLamV_erases_to n e e':
    erases_to n [] e e' ->
    val_erases_to (TLamV e) (TLamV e')
  | LocV_erases_to l:
    val_erases_to (LocV l) (LocV l)
  | IOtagV_erases_to t:
    val_erases_to (IOtagV t) (IOtagV t).

  Lemma upn_plus n m f : upn n (upn m f) = upn (n + m) f.
  Proof.
    revert f. induction m => f; asimpl; auto.
    replace (upn (S m) f) with (upn m (up f)) by by asimpl.
    by rewrite IHm; asimpl.
  Qed.

  Lemma closed_ren e k n m :
    (∀ f : var → expr, e.[upn n f] = e) →
    (∀ f : var → expr, e.[upn k (ren (+m))].[upn (m + n) f] = e.[upn k (ren (+m))]).
  Proof.
    revert k n m; induction e; intros k n' m He f.
    - asimpl.
      rewrite iter_up.
      destruct lt_dec.
      + asimpl.
        rewrite iter_up.
        destruct lt_dec; auto.
        specialize (He (λ _, Unit)); asimpl in *.
        rewrite iter_up in He.
        destruct lt_dec; by try omega.
      + asimpl.
        rewrite iter_up.
        destruct lt_dec; auto.
        specialize (He (λ _, Unit)); asimpl in *.
        rewrite iter_up in He.
        destruct lt_dec; by try omega.
    - assert (∀ f : var → expr, e.[upn (2 + n') f] = e) as He'.
      { intros f'; specialize (He f'); asimpl in *; by simplify_eq. }
      specialize (IHe (2 + k) (2 + n') m He' f).
      asimpl; rewrite upn_plus; erewrite <- IHe; asimpl; eauto.
    - assert (∀ f : var → expr, e.[upn (1 + n') f] = e) as He'.
      { intros f'; specialize (He f'); asimpl in *; by simplify_eq. }
      specialize (IHe (1 + k) (1 + n') m He' f).
      simpl in *.
      asimpl. erewrite <- IHe; asimpl; eauto.
    - asimpl. admit.
  Admitted.

  Lemma subst_closed e e' n m:
    (∀ f : var → expr, e.[upn (S n + m) f] = e) →
    (∀ f : var → expr, e'.[upn m f] = e') →
    ∀ f : var → expr, e.[upn n (e' .: ids)].[upn (n + m) f] = e.[upn n (e' .: ids)].
  Proof.
    revert n m e'; induction e; intros n' m e' He He' f.
    - asimpl.
      unfold var in *.
      rewrite iter_up; destruct lt_dec.
      + asimpl. rewrite iter_up. destruct lt_dec; try omega; auto.
      + asimpl.
        destruct (x - n') eqn:Heqx.
        * asimpl in *.
          transitivity e'.[ren (+n')].[upn (n' + m) f]; first by asimpl.
          eapply (closed_ren _ 0); eauto.
        * asimpl.
          rewrite iter_up; destruct lt_dec; auto.
          specialize (He (λ _, Unit)).
          asimpl in *.
          rewrite iter_up in He.
          destruct lt_dec; by try omega.
    - asimpl.
      assert (∀ f : var → expr, e.[upn (3 + n' + m) f] = e) as He''.
      { intros f'; specialize (He f'); asimpl in *; by simplify_eq. }
      specialize (IHe (2 + n') m e' He'' He' f).
      asimpl; rewrite upn_plus; erewrite <- IHe; asimpl; eauto.
  Admitted.

  Lemma erases_to_subst gs gs' n e e' e'':
    erases_to n (gs ++ true :: gs') e e' →
    ghost_ok e'' →
    (forall f, e''.[upn (length gs') f] = e'') →
    erases_to n (gs ++ gs') e.[upn (length gs) (e'' .: ids)] e'.
  Proof.
    remember (gs ++ true :: gs') as GS.
    intros Her.
    revert gs gs' HeqGS.
    induction Her; intros gs1 gs2 HeqGS Hgok He''cl; subst; asimpl;
      try by (constructor; try apply (IHHer (_ :: _));
           try apply (IHHer (_ :: _ :: _));
           try apply (IHHer2 (_ :: _));
           try apply (IHHer3 (_ :: _)); eauto).
    - clear He''cl.
      rewrite iter_up.
      destruct lt_dec as [Hlt|Hn].
      + constructor.
        revert x x' H Hlt.
        induction gs1; intros x x' H Hlt; simpl in *; first omega.
        destruct x; inversion H; simplify_eq.
        * constructor.
        * constructor. apply IHgs1; eauto with omega.
        * constructor. apply IHgs1; eauto with omega.
      + destruct (decide (x = length gs1)); subst.
        * apply var_erases_to_not_ghost in H.
          rewrite lookup_app_r in H; auto with omega.
          replace (length gs1 - length gs1) with 0 in H by omega.
          done.
        * unfold var in *.
          destruct (x - length gs1) eqn:Heqx; first omega.
          asimpl.
          constructor.
          replace (length gs1 + n0) with (pred x) by omega.
          assert (length gs1 < x) as Hgt by omega.
          clear -Hgt H.
          revert x x' gs2 H Hgt.
          induction gs1; intros x x' gs2 H Hgt; simpl in *.
          -- by inversion H; subst; simpl.
          -- inversion H; simplify_eq; try omega.
             ++ replace ((pred (S x0))) with (S (pred x0)) by omega.
                constructor; auto with omega.
             ++ replace ((pred (S x0))) with (S (pred x0)) by omega.
                constructor; auto with omega.
    - constructor.
      + apply ghost_ok_subst; auto.
        intros x.
        rewrite iter_up; destruct lt_dec; simpl; auto.
        asimpl. destruct (x - length gs1) eqn:Heqx.
        asimpl.
        by apply ghost_ok_subst; eauto; asimpl.
        by asimpl.
      + intros f.
        rewrite app_length.
        apply subst_closed; auto.
        revert H0. rewrite app_length /=.
        by replace (length gs1 + S (length gs2)) with (S (length gs1) + (length gs2))
          by omega.
      + apply (IHHer (_ :: _)); eauto.
    - constructor.
      + apply ghost_ok_subst; auto.
        intros x.
        rewrite iter_up; destruct lt_dec; simpl; auto.
        asimpl. destruct (x - length gs1) eqn:Heqx.
        asimpl.
        by apply ghost_ok_subst; eauto; asimpl.
        by asimpl.
      + intros f.
        rewrite app_length.
        apply subst_closed; auto.
        revert H0. rewrite app_length /=.
        by replace (length gs1 + S (length gs2)) with (S (length gs1) + (length gs2))
          by omega.
      + apply (IHHer _); eauto.
  Qed.

  Inductive ectx_item_erases_to: ectx_item -> ectx_item -> Prop :=
  | AppLCtx_erases_to n e e' :
      erases_to n [] e e' →
      ectx_item_erases_to (AppLCtx e) (AppLCtx e')
  | AppRCtx_erases_to v v' :
      val_erases_to v v' →
      ectx_item_erases_to (AppRCtx v) (AppRCtx v')
  | LetInCtx_erases_to n e e' :
      erases_to n [false] e e' →
      ectx_item_erases_to (LetInCtx e) (LetInCtx e')
  | SeqCtx_erases_to n e e' :
      erases_to n [] e e' →
      ectx_item_erases_to (SeqCtx e) (SeqCtx e')
  | TAppCtx_erases_to :
      ectx_item_erases_to TAppCtx TAppCtx
  | PairLCtx_erases_to n e e' :
      erases_to n [] e e' →
      ectx_item_erases_to (PairLCtx e) (PairLCtx e')
  | PairRCtx_erases_to v v' :
      val_erases_to v v' →
      ectx_item_erases_to (PairRCtx v) (PairRCtx v')
  | BinOpLCtx_erases_to n op e e' :
      erases_to n [] e e' →
      ectx_item_erases_to (BinOpLCtx op e) (BinOpLCtx op e')
  | BinOpRCtx_erases_to op v v' :
      val_erases_to v v' →
      ectx_item_erases_to (BinOpRCtx op v) (BinOpRCtx op v')
  | FstCtx_erases_to :
      ectx_item_erases_to FstCtx FstCtx
  | SndCtx_erases_to :
      ectx_item_erases_to SndCtx SndCtx
  | InjLCtx_erases_to :
      ectx_item_erases_to InjLCtx InjLCtx
  | InjRCtx_erases_to :
      ectx_item_erases_to InjRCtx InjRCtx
  | CaseCtx_erases_to n m e1 e1' e2 e2' :
      erases_to n (false :: []) e1 e1' →
      erases_to m (false :: []) e2 e2' →
      ectx_item_erases_to (CaseCtx e1 e2) (CaseCtx e1' e2')
  | IfCtx_erases_to n m e1 e1' e2 e2' :
      erases_to n [] e1 e1' →
      erases_to m [] e2 e2' →
      ectx_item_erases_to (IfCtx e1 e2) (IfCtx e1' e2')
  | FoldCtx_erases_to :
      ectx_item_erases_to FoldCtx FoldCtx
  | UnfoldCtx_erases_to :
      ectx_item_erases_to UnfoldCtx UnfoldCtx
  | AllocCtx_erases_to :
      ectx_item_erases_to AllocCtx AllocCtx
  | LoadCtx_erases_to :
      ectx_item_erases_to LoadCtx LoadCtx
  | StoreLCtx_erases_to n e e' :
      erases_to n [] e e' →
      ectx_item_erases_to (StoreLCtx e) (StoreLCtx e')
  | StoreRCtx_erases_to v v' :
      val_erases_to v v' →
      ectx_item_erases_to (StoreRCtx v) (StoreRCtx v')
  | CasLCtx_erases_to n m e2 e2' e3 e3' :
      erases_to n [] e2 e2' →
      erases_to m [] e3 e3' →
      ectx_item_erases_to (CasLCtx e2 e3) (CasLCtx e2' e3')
  | CasMCtx_erases_to n v1 v1' e3 e3' :
      val_erases_to v1 v1' →
      erases_to n [] e3 e3' →
      ectx_item_erases_to (CasMCtx v1 e3) (CasMCtx v1' e3')
  | CasRCtx_erases_to v1 v1' v2 v2' :
      val_erases_to v1 v1' →
      val_erases_to v2 v2' →
      ectx_item_erases_to (CasRCtx v1 v2) (CasRCtx v1' v2')
  | IOLCtx_erases_to n e e' :
      erases_to n [] e e' →
      ectx_item_erases_to (IOLCtx e) (IOLCtx e')
  | IORCtx_erases_to v v' :
      val_erases_to v v' →
      ectx_item_erases_to (IORCtx v) (IORCtx v').

  Definition ectx_erases_to K K' :=
    Forall2 ectx_item_erases_to K K'.