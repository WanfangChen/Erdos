import Erdos279.Shifted

/-!
# Four-case completion architecture

This file formalizes the final case split of the paper.  It deliberately
separates the independent inputs supplied by the prime-target construction,
the multiscale hard-target construction, and the elementary classification.
No one field below states that all targets are covered.
-/

namespace Erdos279

/-- The controller progression `p ≡ 1 (mod h)`. -/
def InControllerProgression (h p : Prime) : Prop :=
  p.1 % h.1 = 1

/-- Every prime divisor belongs to `{h} ∪ G`. -/
def SmoothFor (h : Prime) (m : Nat) : Prop :=
  ∀ q : Prime, q.1 ∣ m →
    q = h ∨ InControllerProgression h q

/-- The difficult semigroup case: smooth and divisible by the hub. -/
def HardTarget (h : Prime) (m : Nat) : Prop :=
  SmoothFor h m ∧ h.1 ∣ m

/-- Case 3 of the paper: a mature prime factor outside `{h} ∪ G`. -/
def HasSmallOutsideFactor (k : Nat) (h : Prime) (m : Nat) : Prop :=
  ∃ q : Prime,
    q.1 ∣ m ∧ q ≠ h ∧
    ¬ InControllerProgression h q ∧
    k * q.1 ≤ m

/--
The five independent conclusions needed by the final four-case split.

`outsideLarge_isPrime` is isolated because its future proof uses the
factorization argument and the inequalities `m > k^2`, `h > k`.
-/
structure CompletionData (k : Nat) where
  hub : Prime
  shifted : ShiftedAssignment
  threshold : Nat
  smooth_noHub :
    ∀ m : Nat, threshold ≤ m →
      SmoothFor hub m → ¬ hub.1 ∣ m →
      ShiftedMatureCovers k m shifted
  hard :
    ∀ m : Nat, threshold ≤ m →
      HardTarget hub m →
      ShiftedMatureCovers k m shifted
  smallOutside :
    ∀ m : Nat, threshold ≤ m →
      HasSmallOutsideFactor k hub m →
      ShiftedMatureCovers k m shifted
  outsideLarge_isPrime :
    ∀ m : Nat, threshold ≤ m →
      ¬ SmoothFor hub m →
      ¬ HasSmallOutsideFactor k hub m →
      IsPrime m
  primeTarget :
    ∀ m : Nat, threshold ≤ m →
      IsPrime m →
      ShiftedMatureCovers k m shifted

theorem CompletionData.shiftedCoversTail
    {k : Nat} (D : CompletionData k) :
    ShiftedCoversTail k D.shifted := by
  refine ⟨D.threshold, ?_⟩
  intro m hm
  by_cases hsmooth : SmoothFor D.hub m
  · by_cases hhub : D.hub.1 ∣ m
    · exact D.hard m hm ⟨hsmooth, hhub⟩
    · exact D.smooth_noHub m hm hsmooth hhub
  · by_cases houtside : HasSmallOutsideFactor k D.hub m
    · exact D.smallOutside m hm houtside
    · exact D.primeTarget m hm
        (D.outsideLarge_isPrime m hm hsmooth houtside)

/-- Kernel-checked final implication from the five construction obligations. -/
theorem P_of_completionData {k : Nat} (D : CompletionData k) :
    P k :=
  P_of_shiftedCoversTail D.shiftedCoversTail

/--
The exact remaining construction obligation for the global theorem:
produce `CompletionData k` separately for each `k ≥ 3`.
-/
theorem globalAffirmative_of_completionData
    (build : ∀ k : Nat, 3 ≤ k → CompletionData k) :
    GlobalAffirmative := by
  intro k hk
  exact P_of_completionData (build k hk)

end Erdos279
