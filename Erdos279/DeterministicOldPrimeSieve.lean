import Erdos279.UpperSieveCombinatorics

/-!
# The finite deterministic old-prime sieve

This file instantiates the abstract upper-sieve combinatorics with the
controller semigroup and the translated residue classes from Section 2.
Everything here is an exact identity or finite inequality.
-/

namespace Erdos279

open Finset

/-- Controller primes at most `z`, represented as the project's prime subtype. -/
noncomputable def oldControllerPrimes
    (h : Prime) (z : Nat) : Finset Prime := by
  classical
  exact
    ((Finset.range (z + 1)).subtype IsPrime).filter
      (InControllerProgression h)

@[simp]
theorem mem_oldControllerPrimes
    {h p : Prime} {z : Nat} :
    p ∈ oldControllerPrimes h z ↔
      InControllerProgression h p ∧ p.1 ≤ z := by
  classical
  simp [oldControllerPrimes, Nat.lt_succ_iff, and_comm]

/-- The actual semigroup elements in the natural interval `(Y,Z]`. -/
noncomputable def controllerElements
    (h : Prime) (Y Z : Nat) : Finset Nat := by
  classical
  exact (natIoc Y Z).filter (ControllerSemigroup h)

@[simp]
theorem mem_controllerElements
    {h : Prime} {Y Z u : Nat} :
    u ∈ controllerElements h Y Z ↔
      Y < u ∧ u ≤ Z ∧ ControllerSemigroup h u := by
  classical
  simp [controllerElements, natIoc, and_assoc]

/-- The `{0,1}` mass is literally the cardinality of the semigroup elements. -/
theorem controllerElements_card
    (h : Prime) (Y Z : Nat) :
    (controllerElements h Y Z).card = controllerMass h Y Z := by
  classical
  rw [controllerMass]
  calc
    (controllerElements h Y Z).card =
        ∑ u ∈ natIoc Y Z,
          if ControllerSemigroup h u then 1 else 0 := by
      simp [controllerElements]
    _ = ∑ u ∈ natIoc Y Z, controllerIndicator h u := by
      apply Finset.sum_congr rfl
      intro u _hu
      by_cases hu : ControllerSemigroup h u <;>
        simp [controllerIndicator, hu]

/-- The forbidden translated congruence attached to one old prime. -/
def translatedBad
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z)
    (u : Nat) (p : Prime) : Prop :=
  u % p.1 = (translatedPrimeClass h p e (a.residue p) : Nat)

/-- The semigroup elements in `(Y,Z]` surviving every translated old class. -/
noncomputable def translatedLayerSurvivors
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat) : Finset Nat :=
  sieveSurvivors
    (controllerElements h Y Z)
    (oldControllerPrimes h z)
    (translatedBad e a)

@[simp]
theorem mem_translatedLayerSurvivors
    {h : Prime} {z e Y Z u : Nat}
    {a : OldPrimeClasses h z} :
    u ∈ translatedLayerSurvivors h z e a Y Z ↔
      Y < u ∧ u ≤ Z ∧
      ControllerSemigroup h u ∧
      AvoidsOldClasses (translatedOldPrimeClasses e a) u := by
  classical
  rw [translatedLayerSurvivors, mem_sieveSurvivors]
  constructor
  · rintro ⟨hu, hav⟩
    have hu' := mem_controllerElements.mp hu
    refine ⟨hu'.1, hu'.2.1, hu'.2.2, ?_⟩
    intro p hp hpz
    exact hav p (mem_oldControllerPrimes.mpr ⟨hp, hpz⟩)
  · rintro ⟨hYu, huZ, huG, hav⟩
    refine
      ⟨mem_controllerElements.mpr ⟨hYu, huZ, huG⟩, ?_⟩
    intro p hp
    exact hav p
      (mem_oldControllerPrimes.mp hp).1
      (mem_oldControllerPrimes.mp hp).2

/--
The original hard-form layer, expressed in its semigroup coordinate `u`.
This definition retains the old classes on the product `h^e u`.
-/
noncomputable def hardLayerUnits
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat) : Finset Nat := by
  classical
  exact (controllerElements h Y Z).filter fun u =>
    AvoidsOldClasses a (h.1 ^ e * u)

/--
Exact translation of a complete layer: the original hard survivors and the
translated sieve survivors are the same finite set of `u`-coordinates.
-/
theorem hardLayerUnits_eq_translated
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat) :
    hardLayerUnits h z e a Y Z =
      translatedLayerSurvivors h z e a Y Z := by
  classical
  ext u
  simp only [hardLayerUnits, Finset.mem_filter,
    mem_controllerElements, mem_translatedLayerSurvivors]
  rw [avoidsOldClasses_hubPower_mul_iff]
  tauto

/--
Equation (2.16) in subset-indexed form.  Each right-hand fibre consists of
semigroup elements lying in all translated residue classes indexed by `d`.
-/
theorem translatedLayer_upperSieve_bound
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat)
    (W : UpperSubsetSieveWeights (oldControllerPrimes h z)) :
    ((translatedLayerSurvivors h z e a Y Z).card : Int) ≤
      ∑ d ∈ (oldControllerPrimes h z).powerset,
        W.weight d *
          (violationFiber
            (controllerElements h Y Z) d
            (translatedBad e a)).card := by
  exact upperSubsetSieve_bound
    (controllerElements h Y Z)
    (oldControllerPrimes h z)
    (translatedBad e a) W

end Erdos279
