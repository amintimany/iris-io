From iris.base_logic Require Import invariants.
From iris.proofmode Require Import tactics.
From iris_io Require Import petrinet.

Section AbsPetrinet.
  Context `{invG Σ}.

  Class abstract_petrinet :=
    Abstract_Petrinet {
        places : Type;
        token : places → iProp Σ;
        Split : places → places → places → iProp Σ;
        Split_pers P Q1 Q2 :> Persistent (Split P Q1 Q2);
        Split_ws P Q1 Q2 :
          (Split P Q1 Q2 -∗ token P ={⊤}=∗ token Q1 ∗ token Q2)%I;
        Join : places → places → places → iProp Σ;
        Join_pers P1 P2 Q :> Persistent (Join P1 P2 Q);
        Join_ws P1 P2 Q :
          (Join P1 P2 Q -∗ token P1 -∗ token P2 ={⊤}=∗ token Q)%I;
        NoOp : places → places → iProp Σ;
        NoOp_pers P Q :> Persistent (NoOp P Q);
        NooP_ws P Q :
          (NoOp P Q -∗ token P ={⊤}=∗ token Q)%I;
      }.

End AbsPetrinet.

Global Arguments places {_ _} _.

Section ConcPetrinet.
  Context `{heapIG, petrinetIG Σ}.

  Global Program Instance concrete_petrinet : abstract_petrinet :=
    {|
      places := Places;
      token p := Token p;
      Split p q1 q2 := ⌜ThePetriNet (SplitTr p q1 q2)⌝%I;
      Join p q1 q2 := ⌜ThePetriNet (JoinTr p q1 q2)⌝%I;
      NoOp p q := ⌜ThePetriNet (NoOpTr p q)⌝%I;
    |}.

  Next Obligation.
  Proof.
    by iIntros (? ? ? ?) "?"; iApply petrinet_split.
  Qed.

  Next Obligation.
  Proof.
    iIntros (? ? ? ?) "? ?"; iApply petrinet_join; first by eauto.
    iFrame.
  Qed.

  Next Obligation.
  Proof.
    iIntros (? ? ?) "?"; iApply petrinet_noop; eauto.
  Qed.

End ConcPetrinet.

