import Erdos279.LocalDensityMain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Constants and logarithmic factors from Section 2

This file fixes the exact Lean definitions of

`δ = 1/(h-1)` and `Aδ = exp(-γδ)/Γ(δ)`,

and records the elementary range and positivity facts used throughout the
analytic argument.
-/

namespace Erdos279

/-- Density of primes congruent to `1 mod h`. -/
noncomputable def controllerDensity (h : Prime) : Real :=
  1 / ((h.1 : Real) - 1)

/-- The constant `A_δ` from equations (2.1) and (2.20). -/
noncomputable def paperA (δ : Real) : Real :=
  Real.exp (-Real.eulerMascheroniConstant * δ) / Real.Gamma δ

/-- The slowly varying factor `(log x)^(δ-1)`. -/
noncomputable def selbergSlow (δ : Real) (x : Nat) : Real :=
  Real.log (x : Real) ^ (δ - 1)

/-- Exact Selberg--Delange-shaped main term used for the controller mass. -/
noncomputable def controllerSelbergMain
    (h : Prime) (Kh : Real) (x : Nat) : Real :=
  scaledSummatoryMain
    (Kh / Real.Gamma (controllerDensity h))
    (selbergSlow (controllerDensity h)) x

/-- The controller density is positive. -/
theorem controllerDensity_pos (h : Prime) :
    0 < controllerDensity h := by
  rw [controllerDensity]
  apply one_div_pos.mpr
  exact sub_pos.mpr (by exact_mod_cast h.one_lt)

/-- The controller density is below one. -/
theorem controllerDensity_lt_one (h : Prime) :
    3 ≤ h.1 → controllerDensity h < 1 := by
  intro hh
  rw [controllerDensity]
  apply (div_lt_one (sub_pos.mpr (by exact_mod_cast h.one_lt))).mpr
  have hhR : (3 : Real) ≤ h.1 := by exact_mod_cast hh
  linarith

/-- For the paper's assumption `h ≥ 5`, the key exponent satisfies `2δ < 1`. -/
theorem two_mul_controllerDensity_lt_one
    (h : Prime) (hh : 5 ≤ h.1) :
    2 * controllerDensity h < 1 := by
  rw [controllerDensity]
  have hden : (0 : Real) < (h.1 : Real) - 1 := by
    have : (1 : Real) < h.1 := by exact_mod_cast h.one_lt
    linarith
  have hhR : (5 : Real) ≤ h.1 := by exact_mod_cast hh
  calc
    2 * (1 / ((h.1 : Real) - 1)) =
        2 / ((h.1 : Real) - 1) := by ring
    _ < 1 := (div_lt_one hden).mpr (by linarith)

/-- The paper's constant is positive for positive density. -/
theorem paperA_pos {δ : Real} (hδ : 0 < δ) :
    0 < paperA δ := by
  rw [paperA]
  exact div_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hδ)

/-- `A_δ` is positive at every controller density. -/
theorem paperA_controllerDensity_pos (h : Prime) :
    0 < paperA (controllerDensity h) :=
  paperA_pos (controllerDensity_pos h)

/--
Functional-equation form used in Lemma 2.3:
`Aδ / δ = exp(-γδ) / Γ(1+δ)`.
-/
theorem paperA_div_eq
    {δ : Real} (hδ : δ ≠ 0) :
    paperA δ / δ =
      Real.exp (-Real.eulerMascheroniConstant * δ) /
        Real.Gamma (δ + 1) := by
  rw [paperA, Real.Gamma_add_one hδ]
  field_simp

/-- The logarithmic factor is nonnegative. -/
theorem selbergSlow_nonneg (δ : Real) (x : Nat) :
    0 ≤ selbergSlow δ x := by
  rw [selbergSlow]
  apply Real.rpow_nonneg
  cases x with
  | zero => simp
  | succ x =>
      apply Real.log_nonneg
      norm_num

/-- The logarithmic factor is positive once `x > 1`. -/
theorem selbergSlow_pos
    (δ : Real) {x : Nat} (hx : 1 < x) :
    0 < selbergSlow δ x := by
  rw [selbergSlow]
  apply Real.rpow_pos_of_pos
  exact Real.log_pos (by exact_mod_cast hx)

/-- Unfolding the exact controller Selberg--Delange main term. -/
theorem controllerSelbergMain_eq
    (h : Prime) (Kh : Real) (x : Nat) :
    controllerSelbergMain h Kh x =
      (Kh / Real.Gamma (controllerDensity h)) *
        (x : Real) *
          selbergSlow (controllerDensity h) x :=
  rfl

end Erdos279
