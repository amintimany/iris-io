From iris_io Require Export lang.

Fixpoint ghost_ok(e: expr): Prop :=
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

  Inductive var_erases_to: list bool -> var -> var -> Prop :=
  | var_erases_to_real_O gs:
    var_erases_to (false :: gs) O O
  | var_erases_to_real_S gs x x':
    var_erases_to gs x x' ->
    var_erases_to (false :: gs) (S x) (S x')
  | var_erases_to_ghost_S gs x x':
    var_erases_to gs x x' ->
    var_erases_to (true :: gs) (S x) x'
  .

  Inductive erases_to: list bool -> expr -> expr -> Prop :=
  | Var_erases_to gs x x':
    var_erases_to gs x x' ->
    erases_to gs (Var x) (Var x')
  | Rec_erases_to gs e e':
    erases_to (false :: false :: gs) e e' ->
    erases_to gs (Rec e) (Rec e')
  | Lam_erases_to gs e e':
    erases_to (false :: gs) e e' ->
    erases_to gs (Lam e) (Lam e')
  | LetIn_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to (false :: gs) e2 e2' ->
    erases_to gs (LetIn e1 e2) (LetIn e1' e2')
  | GRLetIn_erases_to gs e1 e2 e2':
    ghost_ok e1 ->
    erases_to (true :: gs) e2 e2' ->
    erases_to gs (GRLetIn e1 e2) e2'
  | Seq_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (Seq e1 e2) (Seq e1' e2')
  | GRSeq_erases_to gs e1 e2 e2':
    ghost_ok e1 ->
    erases_to gs e2 e2' ->
    erases_to gs (GRSeq e1 e2) e2'
  | App_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (App e1 e2) (App e1' e2')
  | Unit_erases_to gs:
    erases_to gs Unit Unit
  | Nat_erases_to gs n:
    erases_to gs (Nat n) (Nat n)
  | Bool_erases_to gs b:
    erases_to gs (Bool b) (Bool b)
  | BinOp_erases_to gs op e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (BinOp op e1 e2) (BinOp op e1' e2')
  | If_erases_to gs e0 e1 e2 e0' e1' e2':
    erases_to gs e0 e0' ->
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (If e0 e1 e2) (If e0' e1' e2')
  | Pair_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (Pair e1 e2) (Pair e1' e2')
  | Fst_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Fst e) (Fst e')
  | Snd_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Snd e) (Snd e')
  | InjL_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (InjL e) (InjL e')
  | InjR_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (InjR e) (InjR e')
  | Case_erases_to gs e0 e1 e2 e0' e1' e2':
    erases_to gs e0 e0' ->
    erases_to (false :: gs) e1 e1' ->
    erases_to (false :: gs) e2 e2' ->
    erases_to gs (Case e0 e1 e2) (Case e0' e1' e2')
  | Fold_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Fold e) (Fold e')
  | Unfold_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Unfold e) (Unfold e')
  | TLam_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (TLam e) (TLam e')
  | TApp_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (TApp e) (TApp e')
  | Fork_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Fork e) (Fork e')
  | Loc_erases_to gs l:
    erases_to gs (Loc l) (Loc l)
  | IOtag_erases_to gs t:
    erases_to gs (IOtag t) (IOtag t)
  | Alloc_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Alloc e) (Alloc e')
  | Load_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Load e) (Load e')
  | Store_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (Store e1 e2) (Store e1' e2')
  | CAS_erases_to gs e0 e1 e2 e0' e1' e2':
    erases_to gs e0 e0' ->
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (CAS e0 e1 e2) (CAS e0' e1' e2')
  | Rand_erases_to gs:
    erases_to gs Rand Rand
  | IO_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (IO e1 e2) (IO e1' e2')
  .

  Inductive val_erases_to: val -> val -> Prop :=
  | RecV_erases_to e e':
    erases_to (false :: false :: []) e e' ->
    val_erases_to (RecV e) (RecV e')
  | LamV_erases_to e e':
    erases_to (false :: []) e e' ->
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
  | TLamV_erases_to e e':
    erases_to [] e e' ->
    val_erases_to (TLamV e) (TLamV e')
  | LocV_erases_to l:
    val_erases_to (LocV l) (LocV l)
  | IOtagV_erases_to t:
    val_erases_to (IOtagV t) (IOtagV t).

  Inductive ectx_item_erases_to: ectx_item -> ectx_item -> Prop :=
  | AppLCtx_erases_to e e' :
      erases_to [] e e' →
      ectx_item_erases_to (AppLCtx e) (AppLCtx e')
  | AppRCtx_erases_to v v' :
      val_erases_to v v' →
      ectx_item_erases_to (AppRCtx v) (AppRCtx v')
  | LetInCtx_erases_to e e' :
      erases_to [] e e' →
      ectx_item_erases_to (LetInCtx e) (LetInCtx e')
  | SeqCtx_erases_to e e' :
      erases_to [] e e' →
      ectx_item_erases_to (SeqCtx e) (SeqCtx e')
  | TAppCtx_erases_to :
      ectx_item_erases_to TAppCtx TAppCtx
  | PairLCtx_erases_to e e' :
      erases_to [] e e' →
      ectx_item_erases_to (PairLCtx e) (PairLCtx e')
  | PairRCtx_erases_to v v' :
      val_erases_to v v' →
      ectx_item_erases_to (PairRCtx v) (PairRCtx v')
  | BinOpLCtx_erases_to op e e' :
      erases_to [] e e' →
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
  | CaseCtx_erases_to e1 e1' e2 e2' :
      erases_to (false :: []) e1 e1' →
      erases_to (false :: []) e2 e2' →
      ectx_item_erases_to (CaseCtx e1 e2) (CaseCtx e1' e2')
  | IfCtx_erases_to e1 e1' e2 e2' :
      erases_to [] e1 e1' →
      erases_to [] e2 e2' →
      ectx_item_erases_to (IfCtx e1 e2) (IfCtx e1' e2')
  | FoldCtx_erases_to :
      ectx_item_erases_to FoldCtx FoldCtx
  | UnfoldCtx_erases_to :
      ectx_item_erases_to UnfoldCtx UnfoldCtx
  | AllocCtx_erases_to :
      ectx_item_erases_to AllocCtx AllocCtx
  | LoadCtx_erases_to :
      ectx_item_erases_to LoadCtx LoadCtx
  | StoreLCtx_erases_to e e' :
      erases_to [] e e' →
      ectx_item_erases_to (StoreLCtx e) (StoreLCtx e')
  | StoreRCtx_erases_to v v' :
      val_erases_to v v' →
      ectx_item_erases_to (StoreRCtx v) (StoreRCtx v')
  | CasLCtx_erases_to e2 e2' e3 e3' :
      erases_to [] e2 e2' →
      erases_to [] e3 e3' →
      ectx_item_erases_to (CasLCtx e2 e3) (CasLCtx e2' e3')
  | CasMCtx_erases_to v1 v1' e3 e3' :
      val_erases_to v1 v1' →
      erases_to [] e3 e3' →
      ectx_item_erases_to (CasMCtx v1 e3) (CasMCtx v1' e3')
  | CasRCtx_erases_to v1 v1' v2 v2' :
      val_erases_to v1 v1' →
      val_erases_to v2 v2' →
      ectx_item_erases_to (CasRCtx v1 v2) (CasRCtx v1' v2')
  | IOLCtx_erases_to e e' :
      erases_to [] e e' →
      ectx_item_erases_to (IOLCtx e) (IOLCtx e')
  | IORCtx_erases_to v v' :
      val_erases_to v v' →
      ectx_item_erases_to (IORCtx v) (IORCtx v').