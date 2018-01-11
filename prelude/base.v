From iris.algebra Require Export base.
From iris.base_logic Require Import upred.
From iris.program_logic Require Import weakestpre.
From iris.base_logic Require Import invariants.
From Autosubst Require Export Autosubst.
Import uPred.

Canonical Structure varC := leibnizC var.

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

Ltac properness :=
  repeat match goal with
  | |- (∃ _: _, _)%I ≡ (∃ _: _, _)%I => apply exist_proper =>?
  | |- (∀ _: _, _)%I ≡ (∀ _: _, _)%I => apply forall_proper =>?
  | |- (_ ∧ _)%I ≡ (_ ∧ _)%I => apply and_proper
  | |- (_ ∨ _)%I ≡ (_ ∨ _)%I => apply or_proper
  | |- (_ → _)%I ≡ (_ → _)%I => apply impl_proper
  | |- (WP _ {{ _ }})%I ≡ (WP _ {{ _ }})%I => apply wp_proper =>?
  | |- (▷ _)%I ≡ (▷ _)%I => apply later_proper
  | |- (□ _)%I ≡ (□ _)%I => apply persistently_proper
  | |- (_ ∗ _)%I ≡ (_ ∗ _)%I => apply sep_proper
  | |- (inv _ _)%I ≡ (inv _ _)%I => apply (contractive_proper _)
  end.

Ltac solve_proper_alt :=
  repeat intro; (simpl + idtac);
  by repeat match goal with H : _ ≡{_}≡ _|- _ => rewrite H end.

Reserved Notation "⟦ τ ⟧" (at level 0, τ at level 70).
Reserved Notation "⟦ τ ⟧ₑ" (at level 0, τ at level 70).
Reserved Notation "⟦ Γ ⟧*" (at level 0, Γ at level 70).

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

Fixpoint Snth {A : Type} n (s : Stream A) : A :=
  match n with
  | O => Shead s
  | S n' => Snth n' (Stail s)
  end.

Fixpoint take_nth_from {A : Type} n (s s' : Stream A) :=
  match n with
    O => {| Shead := Shead s; Stail := Stail s' |}
  | S n' => {| Shead := Shead s';
              Stail := take_nth_from n' (Stail s) (Stail s') |}
  end.
