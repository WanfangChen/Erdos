import Erdos279.LocalDensity

/-!
# Interval form of the exact local-density identity

The cited Selberg--Delange estimate is applied at both endpoints of an
interval.  This file performs that subtraction exactly and identifies the
result with the finite masses used by the sieve.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

/-- A generic integer-valued sum on `(Y,Z]` as a difference of prefix sums. -/
theorem sum_natIoc_eq_range_sub
    (f : Nat → Int) {Y Z : Nat} (hYZ : Y ≤ Z) :
    (∑ u ∈ natIoc Y Z, f u) =
      (∑ u ∈ Finset.range (Z + 1), f u) -
        ∑ u ∈ Finset.range (Y + 1), f u := by
  classical
  have hsubset :
      Finset.range (Y + 1) ⊆ Finset.range (Z + 1) := by
    intro u hu
    simp only [Finset.mem_range] at hu ⊢
    omega
  have hdiff :
      Finset.range (Z + 1) \ Finset.range (Y + 1) =
        natIoc Y Z := by
    ext u
    simp [natIoc]
    omega
  have hsum :=
    Finset.sum_sdiff hsubset (f := f)
  rw [hdiff] at hsum
  omega

/-- Controller-semigroup mass on `(Y,Z]`, expressed as a prefix difference. -/
noncomputable def controllerIntervalSummatory
    (h : Prime) (Y Z : Nat) : Int :=
  controllerSummatory h Z - controllerSummatory h Y

/-- Coprime controller mass on `(Y,Z]`, expressed as a prefix difference. -/
noncomputable def controllerCoprimeIntervalSummatory
    (h : Prime) (d Y Z : Nat) : Int :=
  controllerCoprimeSummatory h d Z -
    controllerCoprimeSummatory h d Y

/-- The interval prefix difference is exactly the finite mass `F((Y,Z])`. -/
theorem controllerIntervalSummatory_eq_mass
    (h : Prime) {Y Z : Nat} (hYZ : Y ≤ Z) :
    controllerIntervalSummatory h Y Z =
      (controllerMass h Y Z : Int) := by
  rw [controllerIntervalSummatory, controllerSummatory,
    controllerSummatory]
  rw [← sum_natIoc_eq_range_sub
    (fun u => (controllerIndicator h u : Int)) hYZ]
  rw [controllerMass]
  push_cast
  rfl

/-- The coprime interval prefix difference is exactly `F_d((Y,Z])`. -/
theorem controllerCoprimeIntervalSummatory_eq_mass
    (h : Prime) (d : Nat) {Y Z : Nat} (hYZ : Y ≤ Z) :
    controllerCoprimeIntervalSummatory h d Y Z =
      (controllerCoprimeMass h d Y Z : Int) := by
  classical
  rw [controllerCoprimeIntervalSummatory,
    controllerCoprimeSummatory, controllerCoprimeSummatory]
  calc
    (∑ u ∈ (Finset.range (Z + 1)).filter (·.Coprime d),
          (controllerIndicator h u : Int)) -
        ∑ u ∈ (Finset.range (Y + 1)).filter (·.Coprime d),
          (controllerIndicator h u : Int) =
        (∑ u ∈ Finset.range (Z + 1),
            if u.Coprime d then (controllerIndicator h u : Int) else 0) -
          ∑ u ∈ Finset.range (Y + 1),
            if u.Coprime d then (controllerIndicator h u : Int) else 0 := by
      simp only [Finset.sum_filter]
    _ = ∑ u ∈ natIoc Y Z,
          if u.Coprime d then (controllerIndicator h u : Int) else 0 := by
      rw [sum_natIoc_eq_range_sub
        (fun u =>
          if u.Coprime d then (controllerIndicator h u : Int) else 0)
        hYZ]
    _ = (controllerCoprimeMass h d Y Z : Int) := by
      rw [controllerCoprimeMass]
      push_cast
      simp only [Finset.sum_filter]

/--
Interval version of exact Möbius inversion, corresponding to subtracting
equation (2.9) at the two endpoints.
-/
theorem controllerCoprimeIntervalSummatory_eq_moebius
    {h : Prime} {d Y Z : Nat}
    (hd : ControllerSemigroup h d) :
    controllerCoprimeIntervalSummatory h d Y Z =
      ∑ r ∈ d.divisors,
        ArithmeticFunction.moebius r *
          controllerIntervalSummatory h (Y / r) (Z / r) := by
  rw [controllerCoprimeIntervalSummatory,
    controllerCoprimeSummatory_eq_moebius hd,
    controllerCoprimeSummatory_eq_moebius hd]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [controllerIntervalSummatory]
  ring

/--
Finite-mass form of interval Möbius inversion.  Division preserves the
endpoint order, so every interval difference can be replaced by its exact
finite mass.
-/
theorem controllerCoprimeMass_eq_moebius
    {h : Prime} {d Y Z : Nat}
    (hd : ControllerSemigroup h d)
    (hYZ : Y ≤ Z) :
    (controllerCoprimeMass h d Y Z : Int) =
      ∑ r ∈ d.divisors,
        ArithmeticFunction.moebius r *
          (controllerMass h (Y / r) (Z / r) : Int) := by
  rw [← controllerCoprimeIntervalSummatory_eq_mass h d hYZ,
    controllerCoprimeIntervalSummatory_eq_moebius hd]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [controllerIntervalSummatory_eq_mass h
    (Nat.div_le_div_right hYZ)]

end Erdos279
