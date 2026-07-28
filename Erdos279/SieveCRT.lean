import Erdos279.DeterministicOldPrimeSieve

/-!
# CRT compression of sieve fibres

Every common fibre in the finite upper sieve is a single arithmetic
progression modulo the product of its (distinct prime) moduli.  This file
proves that fact and rewrites the right side of equation (2.16) using the
progression mass `controllerProgressionMass`.
-/

namespace Erdos279

open Finset

/-- The squarefree modulus attached to a finite set of prime moduli. -/
def primeSubsetModulus (d : Finset Prime) : Nat :=
  ∏ p ∈ d, p.1

theorem primeValues_ne_zero (d : Finset Prime) :
    ∀ p ∈ d, p.1 ≠ 0 := by
  intro p _hp
  exact Nat.ne_of_gt p.pos

theorem primeValues_pairwise_coprime (d : Finset Prime) :
    Set.Pairwise (d : Set Prime)
      (fun p q : Prime => p.1.Coprime q.1) := by
  intro p _hp q _hq hpq
  exact (Nat.coprime_primes p.natPrime q.natPrime).mpr fun hpqval =>
    hpq (Subtype.ext hpqval)

/--
Congruence modulo a product of distinct prime moduli is equivalent to the
family of congruences modulo each prime.
-/
theorem modEq_primeSubsetModulus_iff
    (u b : Nat) (d : Finset Prime) :
    u ≡ b [MOD primeSubsetModulus d] ↔
      ∀ p ∈ d, u ≡ b [MOD p.1] := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      simp [primeSubsetModulus, Nat.modEq_one]
  | @insert p d hpd ih =>
      have hcop :
          p.1.Coprime (∏ q ∈ d, q.1) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hqd
        exact
          (Nat.coprime_primes p.natPrime q.natPrime).mpr fun hpqval =>
            hpd (by
              have hpq : p = q := Subtype.ext hpqval
              simpa [hpq] using hqd)
      rw [primeSubsetModulus, Finset.prod_insert hpd,
        ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
      change
        (u ≡ b [MOD p.1] ∧
          u ≡ b [MOD primeSubsetModulus d]) ↔
          ∀ q ∈ insert p d, u ≡ b [MOD q.1]
      rw [ih]
      simp [hpd]

/-- The canonical CRT class for the translated residues indexed by `d`. -/
noncomputable def translatedSubsetClass
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z)
    (d : Finset Prime) : Nat :=
  (Nat.chineseRemainderOfFinset
    (fun p : Prime =>
      (translatedPrimeClass h p e (a.residue p) : Nat))
    (fun p : Prime => p.1)
    d
    (primeValues_ne_zero d)
    (primeValues_pairwise_coprime d)).1

theorem translatedSubsetClass_modEq
    {h : Prime} {z e : Nat}
    (a : OldPrimeClasses h z)
    {d : Finset Prime} {p : Prime}
    (hp : p ∈ d) :
    translatedSubsetClass e a d ≡
      (translatedPrimeClass h p e (a.residue p) : Nat)
        [MOD p.1] := by
  simpa [translatedSubsetClass] using
    (Nat.chineseRemainderOfFinset
      (fun q : Prime =>
        (translatedPrimeClass h q e (a.residue q) : Nat))
      (fun q : Prime => q.1)
      d
      (primeValues_ne_zero d)
      (primeValues_pairwise_coprime d)).2 p hp

theorem translatedSubsetClass_lt
    {h : Prime} {z e : Nat}
    (a : OldPrimeClasses h z)
    (d : Finset Prime) :
    translatedSubsetClass e a d < primeSubsetModulus d := by
  simpa [translatedSubsetClass, primeSubsetModulus] using
    Nat.chineseRemainderOfFinset_lt_prod
      (fun p : Prime =>
        (translatedPrimeClass h p e (a.residue p) : Nat))
      (fun p : Prime => p.1)
      (primeValues_ne_zero d)
      (primeValues_pairwise_coprime d)

/-- The simultaneous translated congruences are exactly one product congruence. -/
theorem modEq_translatedSubsetClass_iff
    {h : Prime} {z e u : Nat}
    (a : OldPrimeClasses h z)
    (d : Finset Prime) :
    u ≡ translatedSubsetClass e a d
        [MOD primeSubsetModulus d] ↔
      ∀ p ∈ d,
        u ≡ (translatedPrimeClass h p e (a.residue p) : Nat)
          [MOD p.1] := by
  rw [modEq_primeSubsetModulus_iff]
  constructor
  · intro hu p hp
    exact (hu p hp).trans (translatedSubsetClass_modEq a hp)
  · intro hu p hp
    exact (hu p hp).trans (translatedSubsetClass_modEq a hp).symm

/-- Semigroup elements in one combined progression. -/
noncomputable def combinedProgressionElements
    (h : Prime) (d b Y Z : Nat) : Finset Nat := by
  classical
  exact (controllerElements h Y Z).filter fun u =>
    u % d = b % d

@[simp]
theorem mem_combinedProgressionElements
    {h : Prime} {d b Y Z u : Nat} :
    u ∈ combinedProgressionElements h d b Y Z ↔
      Y < u ∧ u ≤ Z ∧ ControllerSemigroup h u ∧
        u % d = b % d := by
  classical
  simp [combinedProgressionElements, and_assoc]

/-- The cardinality form of the paper's progression mass `A_d(I,b)`. -/
theorem combinedProgressionElements_card
    (h : Prime) (d b Y Z : Nat) :
    (combinedProgressionElements h d b Y Z).card =
      controllerProgressionMass h d b Y Z := by
  classical
  rw [controllerProgressionMass]
  calc
    (combinedProgressionElements h d b Y Z).card =
        ∑ u ∈ natIoc Y Z with u % d = b % d,
          if ControllerSemigroup h u then 1 else 0 := by
      have hswap :
          combinedProgressionElements h d b Y Z =
            ((natIoc Y Z).filter fun u => u % d = b % d).filter
              (ControllerSemigroup h) := by
        ext u
        simp [combinedProgressionElements, controllerElements,
          and_comm, and_left_comm]
      rw [hswap]
      simp
    _ = ∑ u ∈ natIoc Y Z with u % d = b % d,
          controllerIndicator h u := by
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases huG : ControllerSemigroup h u <;>
        simp [controllerIndicator, huG]

/-- Each common violation fibre is the CRT-compressed progression fibre. -/
theorem violationFiber_translated_eq_combined
    {h : Prime} {z e Y Z : Nat}
    (a : OldPrimeClasses h z)
    (d : Finset Prime) :
    violationFiber
        (controllerElements h Y Z) d (translatedBad e a) =
      combinedProgressionElements h
        (primeSubsetModulus d)
        (translatedSubsetClass e a d) Y Z := by
  classical
  ext u
  rw [mem_violationFiber, mem_combinedProgressionElements,
    mem_controllerElements]
  constructor
  · rintro ⟨⟨hYu, huZ, huG⟩, hall⟩
    refine ⟨hYu, huZ, huG, ?_⟩
    have hall' :
        ∀ p ∈ d,
          u ≡ (translatedPrimeClass h p e (a.residue p) : Nat)
            [MOD p.1] := by
      intro p hp
      change u % p.1 =
        (translatedPrimeClass h p e (a.residue p) : Nat) % p.1
      simpa [translatedBad,
        Nat.mod_eq_of_lt
          (translatedPrimeClass h p e (a.residue p)).isLt] using
        hall p hp
    exact (modEq_translatedSubsetClass_iff a d).mpr hall'
  · rintro ⟨hYu, huZ, huG, hcombined⟩
    refine ⟨⟨hYu, huZ, huG⟩, ?_⟩
    have hall :=
      (modEq_translatedSubsetClass_iff a d).mp hcombined
    intro p hp
    have hpmod := hall p hp
    change u % p.1 =
      (translatedPrimeClass h p e (a.residue p) : Nat) % p.1 at hpmod
    simpa [translatedBad,
      Nat.mod_eq_of_lt
        (translatedPrimeClass h p e (a.residue p)).isLt] using hpmod

/--
Equation (2.16) with each common fibre rewritten as the arithmetic
progression mass `A_d(I,b)`.
-/
theorem translatedLayer_upperSieve_bound_crt
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat)
    (W : UpperSubsetSieveWeights (oldControllerPrimes h z)) :
    ((translatedLayerSurvivors h z e a Y Z).card : Int) ≤
      ∑ d ∈ (oldControllerPrimes h z).powerset,
        W.weight d *
          controllerProgressionMass h
            (primeSubsetModulus d)
            (translatedSubsetClass e a d) Y Z := by
  calc
    ((translatedLayerSurvivors h z e a Y Z).card : Int) ≤
        ∑ d ∈ (oldControllerPrimes h z).powerset,
          W.weight d *
            (violationFiber
              (controllerElements h Y Z) d
              (translatedBad e a)).card :=
      translatedLayer_upperSieve_bound h z e a Y Z W
    _ = ∑ d ∈ (oldControllerPrimes h z).powerset,
          W.weight d *
            controllerProgressionMass h
              (primeSubsetModulus d)
              (translatedSubsetClass e a d) Y Z := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [violationFiber_translated_eq_combined,
        combinedProgressionElements_card]

end Erdos279
