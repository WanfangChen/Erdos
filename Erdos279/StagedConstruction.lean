import Erdos279.ConstructionCore
import Erdos279.Stabilization

/-!
# Staged construction interface

This connects a genuinely staged, coordinatewise stabilizing construction
to `PaperConstructionCore`.  Coverage is required only eventually at the
finite stages; the theorem proves that it holds for the one final
assignment.
-/

namespace Erdos279

structure StagedPaperConstruction (k : Nat) where
  hub : Prime
  hub_gt_level : k < hub.1
  assignments : StabilizingAssignments
  threshold : Nat
  final_hub_residue :
    (assignments.final hub : Nat) = 1
  final_outside_zero :
    ∀ q : Prime, q ≠ hub →
      ¬ InControllerProgression hub q →
      (assignments.final q : Nat) = 0
  hardForm_eventually :
    ∀ m : Nat, threshold ≤ m →
      HasHardForm hub m →
      assignments.EventuallyCovers k m
  primeTarget_eventually :
    ∀ m : Nat, threshold ≤ m →
      IsPrime m →
      assignments.EventuallyCovers k m

def StagedPaperConstruction.toCore
    {k : Nat} (D : StagedPaperConstruction k) (hk : 0 < k) :
    PaperConstructionCore k where
  hub := D.hub
  hub_gt_level := D.hub_gt_level
  shifted := D.assignments.final
  threshold := D.threshold
  hub_residue := D.final_hub_residue
  outside_zero := D.final_outside_zero
  hardForm := by
    intro m hm hhard
    exact D.assignments.eventuallyCovers_final hk
      (D.hardForm_eventually m hm hhard)
  primeTarget := by
    intro m hm hprime
    exact D.assignments.eventuallyCovers_final hk
      (D.primeTarget_eventually m hm hprime)

theorem P_of_stagedPaperConstruction
    {k : Nat} (hk : 3 ≤ k) (D : StagedPaperConstruction k) :
    P k :=
  P_of_paperConstructionCore hk (D.toCore (by omega))

def RemainingStagedPaperConstruction : Prop :=
  ∀ k : Nat, 3 ≤ k → Nonempty (StagedPaperConstruction k)

theorem globalAffirmative_of_stagedPaperConstruction
    (build : RemainingStagedPaperConstruction) :
    GlobalAffirmative := by
  intro k hk
  rcases build k hk with ⟨D⟩
  exact P_of_stagedPaperConstruction hk D

end Erdos279
