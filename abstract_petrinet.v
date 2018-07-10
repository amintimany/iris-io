From iris.base_logic Require Import invariants viewshifts.
From iris.proofmode Require Import tactics.
From iris_io Require Import petrinet.

Section AbsPetrinet.
  Context `{invG Σ}.

  Definition abs_place := iProp Σ.

  Definition abs_token (P : abs_place) : iProp Σ := P.

  Definition abs_split P Q1 Q2 :=
    (abs_token P ={⊤}=> abs_token Q1 ∗ abs_token Q2)%I.

  Definition abs_join P1 P2 Q :=
    (abs_token P1 -∗ abs_token P2 ={⊤}=> abs_token Q)%I.

  Definition abs_noop P Q := (abs_token P ={⊤}=> abs_token Q)%I.

End AbsPetrinet.
