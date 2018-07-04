From iris.algebra Require Export base.
From Autosubst Require Export Autosubst.

Global Instance Prop_inh : Inhabited Prop.
Proof. exact {| inhabitant := False |}. Qed.

Global Instance fun_inh `{∀ x : A, Inhabited (B x)} : Inhabited (∀ x, B x).
Proof. exact {| inhabitant := (λ x, inhabitant) |}. Qed.

CoInductive Stream (A : Type) : Type :=
  { Shead : A; Stail : Stream A }.

Arguments Shead {_} _.
Arguments Stail {_} _.

Lemma Stream_unfold {A} (p : Stream A) : p = {|Shead := Shead p; Stail := Stail p|}.
Proof. by destruct p. Qed.

CoFixpoint Sconst {A : Type} (a : A) := {| Shead := a; Stail := Sconst a |}.

Global Instance Stream_inh `{Inhabited A} : Inhabited (Stream A).
Proof. exact {| inhabitant := Sconst inhabitant |}. Qed.

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

Definition Sdrop {A : Type} n (s : Stream A) : Stream A :=
  Nat.iter n Stail s.

Fixpoint Snth {A : Type} n (s : Stream A) : A :=
  match n with
  | O => Shead s
  | S n' => Snth n' (Stail s)
  end.

Lemma Snth_Sdrop {A : Type} n (s : Stream A) :
    Shead (Sdrop n s) = Snth n s.
Proof.
  revert s; induction n => s; simpl; first done.
  by rewrite -IHn /Sdrop -Nat_iter_S_r.
 Qed.

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

Fixpoint append_l_s {A} (l : list A) (s : Stream A) :=
  match l with
  | [] => s
  | a :: l' => {|Shead := a; Stail := append_l_s l' s |}
  end.

Lemma append_l_s_app {A} (vs : list A) v μ :
  append_l_s (vs ++ [v]) μ = append_l_s vs {| Shead := v; Stail := μ |}.
Proof.
  induction vs; simpl; first done.
  by rewrite IHvs.
Qed.

CoFixpoint Smap {A B} (f : A → B) (μ : Stream A) : Stream B :=
  {|
    Shead := f (Shead μ);
    Stail := Smap f (Stail μ)
  |}.

CoFixpoint Smix {A} (mixer : Stream bool) (μ μ' : Stream A) : Stream A :=
  {|
    Shead := if Shead mixer then Shead μ else Shead μ';
    Stail := Smix (Stail mixer)
                    (if Shead mixer then Stail μ else μ)
                    (if Shead mixer then μ' else Stail μ')
  |}.

Lemma Smix_trues {A} (μ1 μ2 : Stream A) : Smix (Sconst true) μ1 μ2 = μ1.
Proof.
  apply Seq_eq.
  revert μ1 μ2; cofix => μ1 μ2.
  rewrite [Smix _ _ _]Stream_unfold.
  destruct μ1; simpl; constructor; eauto.
Qed.

Lemma Smix_falses {A} (μ1 μ2 : Stream A) : Smix (Sconst false) μ1 μ2 = μ2.
Proof.
  apply Seq_eq.
  revert μ1 μ2; cofix => μ1 μ2.
  rewrite [Smix _ _ _]Stream_unfold.
  destruct μ2; simpl; constructor; eauto.
Qed.

Definition interleaving {A} (μ1 μ2 : Stream A) : Stream A → Prop :=
  λ μ, ∃ mixer, Smix mixer μ1 μ2 = μ.

Lemma interR {A} v (μ1 μ2 μ : Stream A) :
  interleaving μ1 μ2 μ →
  interleaving {|Shead := v; Stail := μ1 |} μ2
               {|Shead := v; Stail := μ |}.
Proof.
  intros [mixer <-].
  exists {| Shead := true ; Stail := mixer |}.
  by rewrite [Smix {| Shead := true |} _ _]Stream_unfold /=.
Qed.

Lemma interL {A} v (μ1 μ2 μ : Stream A) :
  interleaving μ1 μ2 μ →
  interleaving μ1 {|Shead := v; Stail := μ2 |}
               {|Shead := v; Stail := μ |}.
Proof.
  intros [mixer <-].
  exists {| Shead := false ; Stail := mixer |}.
  by rewrite [Smix {| Shead := false |} _ _]Stream_unfold /=.
Qed.

Lemma interleaving_inh {A} (μ1 μ2 : Stream A) : (interleaving μ1 μ2) μ1.
Proof.
  exists (Sconst true); apply Smix_trues.
Qed.

Lemma Smix_Smap {A B} mixer (f : A → B) (μ μ' : Stream A) :
  Smap f (Smix mixer μ μ') = Smix mixer (Smap f μ) (Smap f μ').
Proof.
  apply Seq_eq.
  revert mixer μ μ'; cofix => mixer μ μ'.
  destruct mixer as [[] mixer].
  - destruct μ as [x μ].
    do 2 rewrite [Smix {| Shead := true |} _ _]Stream_unfold /=.
    rewrite [Smap _ _]Stream_unfold; simpl.
    constructor; auto.
  - destruct μ' as [x μ'].
    do 2 rewrite [Smix {| Shead := false |} _ _]Stream_unfold /=.
    rewrite [Smap _ _]Stream_unfold; simpl.
    constructor; auto.
Qed.
