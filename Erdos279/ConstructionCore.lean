import Erdos279.ElementaryCompletion

/-!
# Exact remaining construction interface

This file does not assume analytic theorems as axioms.  Instead it packages
the precise common-assignment object that the prime matching and multiscale
sieve portions of the paper still have to construct.
-/

namespace Erdos279

/--
The faithfully reduced construction object for one fixed level `k`.

Both infinite coverage fields refer to the same `shifted` assignment and
the same `threshold`; this prevents the two main construction layers from
silently choosing incompatible residues or moving thresholds.
-/
structure PaperConstructionCore (k : Nat) where
  hub : Prime
  hub_gt_level : k < hub.1
  shifted : ShiftedAssignment
  threshold : Nat
  hub_residue : (shifted hub : Nat) = 1
  outside_zero :
    ∀ q : Prime, q ≠ hub →
      ¬ InControllerProgression hub q →
      (shifted q : Nat) = 0
  hardForm :
    ∀ m : Nat, threshold ≤ m →
      HasHardForm hub m →
      ShiftedMatureCovers k m shifted
  primeTarget :
    ∀ m : Nat, threshold ≤ m →
      IsPrime m →
      ShiftedMatureCovers k m shifted

/--
Every completed construction core gives the five-field completion object;
all remaining cases and all threshold adjustments are elementary.
-/
def PaperConstructionCore.toCompletionData
    {k : Nat} (D : PaperConstructionCore k) (hk : 3 ≤ k) :
    CompletionData k :=
  completionData_of_hardForm_and_prime
    hk D.hub D.hub_gt_level D.shifted D.threshold
    D.hub_residue D.outside_zero D.hardForm D.primeTarget

theorem P_of_paperConstructionCore
    {k : Nat} (hk : 3 ≤ k) (D : PaperConstructionCore k) :
    P k :=
  P_of_completionData (D.toCompletionData hk)

/--
The exact remaining problem-specific obligation after the kernel-checked
elementary and compactness layers.
-/
def RemainingPaperConstruction : Prop :=
  ∀ k : Nat, 3 ≤ k → Nonempty (PaperConstructionCore k)

theorem globalAffirmative_of_paperConstructionCore
    (build : RemainingPaperConstruction) :
    GlobalAffirmative := by
  intro k hk
  rcases build k hk with ⟨D⟩
  exact P_of_paperConstructionCore hk D

end Erdos279
