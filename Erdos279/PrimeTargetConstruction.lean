import Erdos279.AsymptoticPrimeMatching

/-!
# Completion of the isolated-prime-target construction

This file combines the matching from (3.7) with the initial classes
`a_h = 1`, `a_ℓ = 1` for `ℓ ∈ H`, and zero elsewhere.  It proves that the
single resulting assignment covers every sufficiently large prime target,
while preserving the hub value and all required outside-zero coordinates.
-/

namespace Erdos279

/-- The assignment before the periodic matching is installed. -/
def hubOldPrimeAssignment
    (h : Prime) (H : Finset Prime) :
    ShiftedAssignment :=
  fun p =>
    if _hp : p = h ∨ p ∈ H then
      ⟨1, p.one_lt⟩
    else
      ⟨0, p.pos⟩

@[simp]
theorem hubOldPrimeAssignment_hub
    (h : Prime) (H : Finset Prime) :
    (hubOldPrimeAssignment h H h : Nat) = 1 := by
  simp [hubOldPrimeAssignment]

@[simp]
theorem hubOldPrimeAssignment_old
    (h : Prime) (H : Finset Prime)
    {p : Prime} (hp : p ∈ H) :
    (hubOldPrimeAssignment h H p : Nat) = 1 := by
  simp [hubOldPrimeAssignment, hp]

theorem hubOldPrimeAssignment_zero
    (h : Prime) (H : Finset Prime)
    {p : Prime} (hph : p ≠ h) (hpH : p ∉ H) :
    (hubOldPrimeAssignment h H p : Nat) = 0 := by
  simp [hubOldPrimeAssignment, hph, hpH]

/-- A bound dominating `kℓ` for every old prime `ℓ ∈ H`. -/
def oldPrimeMaturityBound
    (k : Nat) (H : Finset Prime) : Nat :=
  H.sup fun ℓ => k * ℓ.1

theorem oldPrimeMaturity_le
    (k : Nat) (H : Finset Prime)
    {ℓ : Prime} (hℓ : ℓ ∈ H) :
    k * ℓ.1 ≤ oldPrimeMaturityBound k H := by
  simpa [oldPrimeMaturityBound] using
    (Finset.le_sup
      (s := H) (f := fun q : Prime => k * q.1) hℓ)

/-- The complete output of §3.1, isolated from the later hard-target
construction. -/
structure IsolatedPrimeTargetConstruction
    (k : Nat) (h : Prime) where
  shifted : ShiftedAssignment
  threshold : Nat
  hub_residue : (shifted h : Nat) = 1
  outside_zero :
    ∀ q : Prime, q ≠ h →
      ¬ InControllerProgression h q →
      (shifted q : Nat) = 0
  primeTarget :
    ∀ m : Nat, threshold ≤ m →
      IsPrime m →
      ShiftedMatureCovers k m shifted

namespace PeriodicComplementaryEnumerations

/-- The one assignment obtained by installing the tail matching on top of
the hub/old-prime assignment. -/
noncomputable def primeTargetAssignment
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k) :
    ShiftedAssignment :=
  T.matching.assignment (hubOldPrimeAssignment h H)

theorem primeTargetAssignment_hub
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k) :
    (E.primeTargetAssignment T h : Nat) = 1 := by
  rw [primeTargetAssignment,
    T.matching.assignment_at_hub
      (hubOldPrimeAssignment h H) h
      (E.tailMatching_controllersIn T)]
  exact hubOldPrimeAssignment_hub h H

/-- Matching uses only `T = T₀ \ H`, so every old-prime coordinate remains
equal to one. -/
theorem primeTargetAssignment_old
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k)
    {ℓ : Prime} (hℓ : ℓ ∈ H) :
    (E.primeTargetAssignment T ℓ : Nat) = 1 := by
  rw [primeTargetAssignment]
  rw [T.matching.assignment_of_unmatched
    (hubOldPrimeAssignment h H) ℓ]
  · exact hubOldPrimeAssignment_old h H hℓ
  · intro i hi
    have hnotOld :=
      (E.periodic_mem (T.offset + i)).not_mem_old
    rw [T.pair_eq i] at hi
    change E.periodic (T.offset + i) = ℓ at hi
    exact hnotOld (hi.symm ▸ hℓ)

/-- The matching changes only controller primes; hence every prime outside
the controller progression retains the initial zero class. -/
theorem primeTargetAssignment_outside_zero
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    (hH : ∀ ℓ ∈ H, InControllerProgression h ℓ)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k)
    (q : Prime) (hqh : q ≠ h)
    (hqG : ¬ InControllerProgression h q) :
    (E.primeTargetAssignment T q : Nat) = 0 := by
  rw [primeTargetAssignment,
    T.matching.assignment_of_not_in_progression
      (hubOldPrimeAssignment h H)
      (E.tailMatching_controllersIn T) hqG]
  apply hubOldPrimeAssignment_zero h H hqh
  intro hqH
  exact hqG (hH q hqH)

/-- A large prime target in the hub progression is covered by the hub
coordinate, whose residue remains one. -/
theorem primeTargetAssignment_covers_hubClass
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k)
    (q : Prime)
    (hqG : InControllerProgression h q)
    (hqLarge : k * h.1 ≤ q.1) :
    ShiftedMatureCovers k q.1
      (E.primeTargetAssignment T) := by
  refine ⟨h, hqLarge.trans (Nat.le_add_right q.1 1), ?_⟩
  rw [E.primeTargetAssignment_hub T]
  exact hqG

/-- A large prime target congruent to one modulo an old prime is covered by
that unchanged old-prime coordinate. -/
theorem primeTargetAssignment_covers_oldClass
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k)
    (q ℓ : Prime) (hℓ : ℓ ∈ H)
    (hqℓ : q.1 % ℓ.1 = 1)
    (hqLarge : oldPrimeMaturityBound k H ≤ q.1) :
    ShiftedMatureCovers k q.1
      (E.primeTargetAssignment T) := by
  refine ⟨ℓ, ?_, ?_⟩
  · exact
      (oldPrimeMaturity_le k H hℓ).trans hqLarge
        |>.trans (Nat.le_add_right q.1 1)
  · rw [E.primeTargetAssignment_old T hℓ]
    exact hqℓ

/-- Combining the hub classes, the old classes, and the complementary
matching yields coverage of every prime beyond one explicit threshold. -/
noncomputable def toIsolatedPrimeTargetConstruction
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    (hH : ∀ ℓ ∈ H, InControllerProgression h ℓ)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k) :
    IsolatedPrimeTargetConstruction k h where
  shifted := E.primeTargetAssignment T
  threshold :=
    max
      (primePrefixBound E.complementary T.offset)
      (max (k * h.1) (oldPrimeMaturityBound k H))
  hub_residue := E.primeTargetAssignment_hub T
  outside_zero := by
    intro q hqh hqG
    exact E.primeTargetAssignment_outside_zero hH T q hqh hqG
  primeTarget := by
    intro m hm hmPrime
    let q : Prime := ⟨m, hmPrime⟩
    have hprefix :
        primePrefixBound E.complementary T.offset ≤ q.1 := by
      exact (le_max_left _ _).trans hm
    have hhub : k * h.1 ≤ q.1 := by
      exact
        (le_max_left (k * h.1)
          (oldPrimeMaturityBound k H)).trans
          ((le_max_right
            (primePrefixBound E.complementary T.offset)
            (max (k * h.1)
              (oldPrimeMaturityBound k H))).trans hm)
    have hold :
        oldPrimeMaturityBound k H ≤ q.1 := by
      exact
        (le_max_right (k * h.1)
          (oldPrimeMaturityBound k H)).trans
          ((le_max_right
            (primePrefixBound E.complementary T.offset)
            (max (k * h.1)
              (oldPrimeMaturityBound k H))).trans hm)
    by_cases hcomp : IsComplementaryPrimeTarget h H q
    · exact
        E.tailMatching_assignment_covers_large_complementary
          T (hubOldPrimeAssignment h H) q hcomp hprefix
    · by_cases hqG : InControllerProgression h q
      · exact E.primeTargetAssignment_covers_hubClass
          T q hqG hhub
      · have hnotAll :
          ¬ ∀ ℓ ∈ H, q.1 % ℓ.1 ≠ 1 := by
          intro hall
          exact hcomp ⟨hqG, hall⟩
        push_neg at hnotAll
        obtain ⟨ℓ, hℓ, hqℓ⟩ := hnotAll
        exact E.primeTargetAssignment_covers_oldClass
          T q ℓ hℓ hqℓ hold

end PeriodicComplementaryEnumerations

end Erdos279
