From iris_io Require Export lang.

Module Ghostlang.
  Inductive expr :=
  | Var (x : var)
  | Rec (e : {bind 2 of expr})
  | Lam (e : {bind expr})
  | LetIn (e : expr) (e : {bind expr})
  | GRLetIn (e : expr) (e : {bind expr})
  | Seq (e1 e2 : expr)
  | GRSeq (e1 e2 : expr)
  | App (e1 e2 : expr)
  (* Base Types *)
  | Unit
  | Nat (n : nat)
  | Bool (b : bool)
  | BinOp (op : binop) (e1 e2 : expr)
  (* If then else *)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : {bind expr}) (e2 : {bind expr})
  (* Recursive Types *)
  | Fold (e : expr)
  | Unfold (e : expr)
  (* Polymorphic Types *)
  | TLam (e : expr)
  | TApp (e : expr)
  (* Concurrency *)
  | Fork (e : expr)
  (* Reference Types *)
  | Loc (l : loc)
  | IOtag (t : ioTag)
  | Alloc (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  (* Compare and swap used for fine-grained concurrency *)
  | CAS (e0 : expr) (e1 : expr) (e2 : expr)
  (* Instrumenting Prophecies *)
  | Pr (l : loc)
  | Create_Pr
  | Assign_Pr (e1 e2 : expr)
  (* Random bit *)
  | Rand
  (* I/O *)
  | IO (e1 e2 : expr).

  Fixpoint instr(e: expr): Plang.expr :=
    match e with
      Var x => Plang.Var x
    | Rec e => Plang.Rec (instr e)
    | Lam e => Plang.Lam (instr e)
    | LetIn e1 e2 => Plang.LetIn (instr e1) (instr e2)
    | GRLetIn e1 e2 => Plang.LetIn (instr e1) (instr e2)
    | Seq e1 e2 => Plang.Seq (instr e1) (instr e2)
    | GRSeq e1 e2 => Plang.Seq (instr e1) (instr e2)
    | App e1 e2 => Plang.App (instr e1) (instr e2)
    | Unit => Plang.Unit
    | Nat n => Plang.Nat n
    | Bool b => Plang.Bool b
    | BinOp op e1 e2 => Plang.BinOp op (instr e1) (instr e2)
    | If e0 e1 e2 => Plang.If (instr e0) (instr e1) (instr e2)
    | Pair e1 e2 => Plang.Pair (instr e1) (instr e2)
    | Fst e => Plang.Fst (instr e)
    | Snd e => Plang.Snd (instr e)
    | InjL e => Plang.InjL (instr e)
    | InjR e => Plang.InjR (instr e)
    | Case e0 e1 e2 => Plang.Case (instr e0) (instr e1) (instr e2)
    | Fold e => Plang.Fold (instr e)
    | Unfold e => Plang.Unfold (instr e)
    | TLam e => Plang.TLam (instr e)
    | TApp e => Plang.TApp (instr e)
    | Fork e => Plang.Fork (instr e)
    | Loc l => Plang.Loc l
    | IOtag t => Plang.IOtag t
    | Alloc e => Plang.Alloc (instr e)
    | Load e => Plang.Load (instr e)
    | Store e1 e2 => Plang.Store (instr e1) (instr e2)
    | CAS e0 e1 e2 => Plang.CAS (instr e0) (instr e1) (instr e2)
    | Pr l => Plang.Pr l
    | Create_Pr => Plang.Create_Pr
    | Assign_Pr e1 e2 => Plang.Assign_Pr (instr e1) (instr e2)
    | Rand => Plang.Rand
    | IO e1 e2 => Plang.IO (instr e1) (instr e2)
    end.

  Fixpoint ghost_ok(e: expr): Prop :=
    match e with
    | Var x => True
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

  Inductive erases_to: list bool -> expr -> Plang.expr -> Prop :=
  | Var_erases_to gs x x':
    var_erases_to gs x x' ->
    erases_to gs (Var x) (Plang.Var x')
  | Rec_erases_to gs e e':
    erases_to (false :: false :: gs) e e' ->
    erases_to gs (Rec e) (Plang.Rec e')
  | Lam_erases_to gs e e':
    erases_to (false :: gs) e e' ->
    erases_to gs (Lam e) (Plang.Lam e')
  | LetIn_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to (false :: gs) e2 e2' ->
    erases_to gs (LetIn e1 e2) (Plang.LetIn e1' e2')
  | GRLetIn_erases_to gs e1 e2 e2':
    ghost_ok e1 ->
    erases_to (true :: gs) e2 e2' ->
    erases_to gs (GRLetIn e1 e2) e2'
  | Seq_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (Seq e1 e2) (Plang.Seq e1' e2')
  | GRSeq_erases_to gs e1 e2 e2':
    ghost_ok e1 ->
    erases_to gs e2 e2' ->
    erases_to gs (GRSeq e1 e2) e2'
  | App_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (App e1 e2) (Plang.App e1' e2')
  | Unit_erases_to gs:
    erases_to gs Unit Plang.Unit
  | Nat_erases_to gs n:
    erases_to gs (Nat n) (Plang.Nat n)
  | Bool_erases_to gs b:
    erases_to gs (Bool b) (Plang.Bool b)
  | BinOp_erases_to gs op e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (BinOp op e1 e2) (Plang.BinOp op e1' e2')
  | If_erases_to gs e0 e1 e2 e0' e1' e2':
    erases_to gs e0 e0' ->
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (If e0 e1 e2) (Plang.If e0' e1' e2')
  | Pair_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (Pair e1 e2) (Plang.Pair e1' e2')
  | Fst_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Fst e) (Plang.Fst e')
  | Snd_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Snd e) (Plang.Snd e')
  | InjL_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (InjL e) (Plang.InjL e')
  | InjR_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (InjR e) (Plang.InjR e')
  | Case_erases_to gs e0 e1 e2 e0' e1' e2':
    erases_to gs e0 e0' ->
    erases_to (false :: gs) e1 e1' ->
    erases_to (false :: gs) e2 e2' ->
    erases_to gs (Case e0 e1 e2) (Plang.Case e0' e1' e2')
  | Fold_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Fold e) (Plang.Fold e')
  | Unfold_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Unfold e) (Plang.Unfold e')
  | TLam_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (TLam e) (Plang.TLam e')
  | TApp_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (TApp e) (Plang.TApp e')
  | Fork_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Fork e) (Plang.Fork e')
  | Loc_erases_to gs l:
    erases_to gs (Loc l) (Plang.Loc l)
  | IOtag_erases_to gs t:
    erases_to gs (IOtag t) (Plang.IOtag t)
  | Alloc_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Alloc e) (Plang.Alloc e')
  | Load_erases_to gs e e':
    erases_to gs e e' ->
    erases_to gs (Load e) (Plang.Load e')
  | Store_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (Store e1 e2) (Plang.Store e1' e2')
  | CAS_erases_to gs e0 e1 e2 e0' e1' e2':
    erases_to gs e0 e0' ->
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (CAS e0 e1 e2) (Plang.CAS e0' e1' e2')
  | Rand_erases_to gs:
    erases_to gs Rand Plang.Rand
  | IO_erases_to gs e1 e2 e1' e2':
    erases_to gs e1 e1' ->
    erases_to gs e2 e2' ->
    erases_to gs (IO e1 e2) (Plang.IO e1' e2')
  .

End Ghostlang.