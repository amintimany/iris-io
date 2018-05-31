From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris_io Require Export lang rules.
From iris.proofmode Require Import tactics.

Section PetriNet.

  Context `{EqDecision Pl}.

  Inductive Transition : Type :=
    IOTr (p : Pl) (t : ioTag) (v v' : val) (q : Pl)
  | SplitTr (p q q': Pl)
  | JoinTr (p p' q: Pl)
  | NoOpTr (p q : Pl).

  Definition PetriNet := Transition → Prop.

  Definition Valuation := Pl → nat.

  Implicit Types N : PetriNet.
  Implicit Types V : Valuation.
  Implicit Types p q : Pl.

  Definition singVAL p := (λ q, if decide (p = q) then 1 else 0).

  Definition ValPlus V V' := λ p, V p + V' p.

  Notation "V ⊎ W" := (ValPlus V W) (at level 50, left associativity).

  Inductive Traces N : Valuation → ioSpec :=
  | EmpTR V : Traces N V []
  | IOTR V p t v v' q τ :
      N (IOTr p t v v' q) →
      Traces N ((singVAL q) ⊎ V) τ →
      Traces N ((singVAL p) ⊎ V) ((t, v, v') :: τ)
  | SplitTR V p q q' τ :
      N (SplitTr p q q') →
      Traces N (singVAL q ⊎ singVAL q' ⊎ V) τ →
      Traces N (singVAL p ⊎ V) τ
  | JoinTR V p p' q τ :
      N (JoinTr p p' q) →
      Traces N (singVAL q ⊎ V) τ →
      Traces N (singVAL p ⊎ singVAL p' ⊎ V) τ
  | NoOpTR V p q τ :
      N (NoOpTr p q) →
      Traces N (singVAL q ⊎ V) τ →
      Traces N (singVAL p ⊎ V) τ.

  Definition ResultDet N V :=
    ∀ t v v' v'' τ,
      Traces N V (τ ++ [(t, v, v')]) →
      Traces N V (τ ++ [(t, v, v'')]) → v' = v''.

  (** The CMRA for petrinet valuations. *)
  Class petrinetIG Σ := PetriNetIG {
    PNI_exclG :> inG Σ (authUR (ofe_funUR (λ p : Pl, natUR)));
    γPN : gname
  }.

  Context `{petrinetIG Σ}.

  Program Definition FullVAL V :=
    @own Σ (authUR (ofe_funUR (λ p, natUR))) _ γPN (● V).

  Definition ownVAL V :=
    @own Σ (authUR (ofe_funUR (λ p, natUR))) _ γPN (◯ V).

  Definition Token p := ownVAL (singVAL p).

  Lemma OwnVAL_split V V' : ownVAL (V ⊎ V') ⊣⊢ ownVAL V ∗  ownVAL V'.
  Proof. by rewrite /ownVAL -own_op -auth_frag_op. Qed.

  Context {N}.

  

End PetriNet.

Notation "V ⊎ W" := (ValPlus V W) (at level 50, left associativity).

