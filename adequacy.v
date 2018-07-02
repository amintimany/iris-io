From iris.program_logic Require Export weakestpre adequacy.
From iris.program_logic Require Import ectx_lifting.
From iris.base_logic Require Export invariants.
From iris.algebra Require Import auth frac agree gmap.
From iris_io Require Export lang rules proph_erasure full_erasure.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap.

Class heapIPreG Σ := HeapIPreG {
  heapI_invG :> invPreG Σ;
  heapI_gen_heapG :> gen_heapPreG loc val Σ;
  prophI_gen_heapG :> gen_heapPreG loc (Stream val) Σ;
  ioI_exclG :> inG Σ io_monoid;
}.

Definition IoΣ := #[invΣ; gen_heapΣ loc val; gen_heapΣ loc (Stream val);
                      GFunctor io_monoid].

Global Instance subG_io_monoid Σ : subG IoΣ Σ → inG Σ io_monoid.
Proof. solve_inG. Qed.

Theorem adequacy_instrumented Σ `{heapIPreG Σ} e Φ M :
  (∀ `{Hig : heapIG Σ}, (WP e @ NotStuck; ⊤ {{ Φ }})%I) → safe e M.
Proof.
  intros Hwp.
  cut (adequate NotStuck e {| Heap := ∅; Proph := ∅; ioState := M |} (λ _, True)).
  { intros [Hrc Hns]; simpl in *.
    intros th2 σ2 Hrtc e' He'.
    specialize (Hns th2 σ2 e' eq_refl Hrtc He'); eauto. }
  eapply wp_adequacy; first apply _.
  iIntros (Hinv) "".
  iMod (@own_alloc _ io_monoid _ (● Excl' (M : leibnizC ioSpec)))
    as (γio) "HGI".
  { split; last done. intros n; eapply ucmra_unit_leastN. }
  iMod (gen_heap_init (∅ : gmap loc val)) as (Hheap) "Hheap".
  iMod (gen_heap_init (∅ : gmap loc (Stream val))) as (Hproph) "Hproph".
  set (HIG := {| γio := γio |} : heapIG Σ).
  iModIntro.
  iExists heapIG_stateI.
  iSplitL; first by iFrame.
    by (iApply wp_mono; last iApply Hwp; eauto).
Qed.

Theorem adequacy Σ `{heapIPreG Σ} (e : expr) Φ M :
  prefix_closed M →
  (∀ `{Hig : heapIG Σ}, (WP e @ NotStuck; ⊤ {{ Φ }})%I) → fully_erased_safe e M.
Proof.
  intros HPC Hig.
  apply soundness_io; eauto.
  apply soundness_prophecies.
  eapply adequacy_instrumented; eauto.
Qed.
