From iris.algebra Require Export base.
From Autosubst Require Export Autosubst.

CoInductive Stream (A : Type) : Type :=
  { Shead : A; Stail : Stream A }.

Arguments Shead {_} _.
Arguments Stail {_} _.

Lemma Stream_unfold {A} (p : Stream A) : p = {|Shead := Shead p; Stail := Stail p|}.
Proof. by destruct p. Qed.

CoFixpoint Sconst {A : Type} (a : A) := {| Shead := a; Stail := Sconst a |}.

CoInductive Seq {A : Type} : Stream A → Stream A → Prop :=
  Seq_refl : forall x y t1 t2,
    x = y → Seq t1 t2 → Seq {|Shead := x; Stail := t1|} {|Shead := y; Stail := t2|}.

Lemma eq_Seq {A : Type} (x y : Stream A) : x = y → Seq x y.
Proof.
  intros ->; revert y.
  cofix IH => y.
  destruct y.
  econstructor; auto.
Qed.

Axiom Seq_eq : ∀ {A : Type} (x y : Stream A), Seq x y → x = y.

Fixpoint Stake {A : Type} n (s : Stream A) : list A :=
  match n with
    O => []
  | S n' => (Shead s) :: (Stake n' (Stail s))
  end.

Fixpoint Snth {A : Type} n (s : Stream A) : A :=
  match n with
  | O => Shead s
  | S n' => Snth n' (Stail s)
  end.

Lemma Snth_Sconst {A : Type} n (a : A) :
  Snth n (Sconst a) = a.
Proof.
  induction n; auto.
Qed.

Fixpoint prepend_n_from {A : Type} n (s s' : Stream A) :=
  match n with
    O => s'
  | S n' => {| Shead := Shead s;
              Stail := prepend_n_from n' (Stail s) s' |}
  end.

Lemma prepend_n_from_Snth {A : Type} n {s s' : Stream A} :
  prepend_n_from (S n) s s' =
  prepend_n_from n s {| Shead := Snth n s; Stail := s' |}.
Proof.
  simpl; revert s s'.
  induction n as [|n] => s s'; simpl; auto.
  f_equal.
  by rewrite IHn.
Qed.

Lemma prepen_n_from_same {A} n (μ : Stream A) :
  prepend_n_from n μ (Nat.iter n Stail μ) = μ.
Proof.
  revert μ. induction n => μ; auto.
  rewrite Nat_iter_S_r.
  destruct μ as [h t]; simpl.
  by rewrite IHn.
Qed.
