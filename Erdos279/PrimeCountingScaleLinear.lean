import Erdos279.ControllerReservoirPNT
import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Linear rescaling of the shifted prime-counting scale

For fixed positive natural numbers `a,b`, natural division satisfies

`(aX / b) / X → a / b`.

This file propagates that exact floor limit through the shifted
normalization `(x+2)/log(x+2)`.
-/

namespace Erdos279

open Filter

theorem nat_mul_div_eq_floor
    (a b X : Nat) :
    a * X / b =
      ⌊((a : Real) / (b : Real)) * (X : Real)⌋₊ := by
  have hReal :
      ((a : Real) / (b : Real)) * (X : Real) =
        ((a * X : Nat) : Real) / (b : Real) := by
    push_cast
    ring
  rw [hReal, Nat.floor_div_eq_div]

/-- Natural-number division has the expected linear ratio limit. -/
theorem natCast_mul_div_ratio_tendsto
    (a b : Nat) (hb : 0 < b) :
    Tendsto
      (fun X : Nat =>
        ((a * X / b : Nat) : Real) /
          (X : Real))
      atTop
      (nhds ((a : Real) / (b : Real))) := by
  have hnonneg :
      0 ≤ (a : Real) / (b : Real) := by
    positivity
  have hFloor :=
    tendsto_nat_floor_mul_div_atTop
      (R := Real) hnonneg
  have hFloorNat :=
    hFloor.comp
      tendsto_natCast_atTop_atTop
  have hEq :
      (fun X : Nat =>
        (⌊((a : Real) / (b : Real)) *
            (X : Real)⌋₊ : Real) /
          (X : Real)) =ᶠ[atTop]
      (fun X : Nat =>
        ((a * X / b : Nat) : Real) /
          (X : Real)) := by
    apply Eventually.of_forall
    intro X
    change
      (⌊((a : Real) / (b : Real)) *
          (X : Real)⌋₊ : Real) /
          (X : Real) =
        ((a * X / b : Nat) : Real) /
          (X : Real)
    congr 1
    exact_mod_cast
      (nat_mul_div_eq_floor a b X).symm
  simpa using hFloorNat.congr' hEq

/-- A positive natural linear quotient tends to infinity. -/
theorem nat_mul_div_tendsto_atTop
    (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun X : Nat => a * X / b)
      atTop atTop := by
  have hpos :
      0 < (a : Real) / (b : Real) := by
    positivity
  have hFloor :=
    tendsto_nat_floor_mul_atTop
      (α := Real)
      ((a : Real) / (b : Real))
      hpos
  apply hFloor.congr'
  apply Eventually.of_forall
  intro X
  exact (nat_mul_div_eq_floor a b X).symm

/-- Adding fixed shifts to numerator and denominator does not alter the
linear quotient limit. -/
theorem natCast_mul_div_add_ratio_tendsto
    (a b c d : Nat) (hb : 0 < b) :
    Tendsto
      (fun X : Nat =>
        ((a * X / b + c : Nat) : Real) /
          ((X + d : Nat) : Real))
      atTop
      (nhds ((a : Real) / (b : Real))) := by
  have hLinear :=
    natCast_mul_div_ratio_tendsto a b hb
  have hConstSmall :
      Tendsto
        (fun X : Nat =>
          (c : Real) / (X : Real))
        atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop
      |>.const_div_atTop (c : Real)
  have hNumerator :
      Tendsto
        (fun X : Nat =>
          ((a * X / b + c : Nat) : Real) /
            (X : Real))
        atTop
        (nhds
          ((a : Real) / (b : Real) + 0)) := by
    have hAdd := hLinear.add hConstSmall
    apply hAdd.congr'
    filter_upwards
      [eventually_ne_atTop 0] with X hX
    push_cast
    field_simp [hX]
  have hDenominator :
      Tendsto
        (fun X : Nat =>
          (X : Real) /
            ((X : Real) + d))
        atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop
      (d : Real)
  have hProduct :=
    hNumerator.mul hDenominator
  have hEq :
      (fun X : Nat =>
        ((a * X / b + c : Nat) : Real) /
            (X : Real) *
          ((X : Real) /
            ((X : Real) + d))) =ᶠ[atTop]
      (fun X : Nat =>
        ((a * X / b + c : Nat) : Real) /
          ((X + d : Nat) : Real)) := by
    filter_upwards
      [eventually_ne_atTop 0] with X hX
    push_cast
    have hXd :
        (X : Real) + d ≠ 0 := by
      have hXR : (X : Real) ≠ 0 := by
        exact_mod_cast hX
      positivity
    field_simp [hX, hXd]
  simpa using hProduct.congr' hEq

/-- The logarithm of a positive fixed linear rescaling is asymptotic to the
logarithm of the original variable. -/
theorem log_nat_mul_div_add_ratio_tendsto_one
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun X : Nat =>
        Real.log
            ((a * X / b + c + 2 : Nat) : Real) /
          Real.log ((X + 2 : Nat) : Real))
      atTop (nhds 1) := by
  have hValueRatio :=
    natCast_mul_div_add_ratio_tendsto
      a b (c + 2) 2 hb
  have hValueTop :
      Tendsto
        (fun X : Nat =>
          ((a * X / b + c + 2 : Nat) : Real))
        atTop atTop := by
    have hLinearTop :=
      nat_mul_div_tendsto_atTop
        a b ha hb
    have hShiftTop :
        Tendsto
          (fun X : Nat =>
            a * X / b + (c + 2))
          atTop atTop :=
      (tendsto_add_atTop_nat
        (c + 2)).comp hLinearTop
    have hCastTop :
        Tendsto
          (fun X : Nat =>
            ((a * X / b + (c + 2) : Nat) : Real))
          atTop atTop :=
      (tendsto_natCast_atTop_atTop
        (R := Real)).comp hShiftTop
    simpa [Nat.add_assoc] using hCastTop
  have hBaseTop :
      Tendsto
        (fun X : Nat =>
          ((X + 2 : Nat) : Real))
        atTop atTop := by
    exact
      tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 2)
  have hLogBaseTop :
      Tendsto
        (fun X : Nat =>
          Real.log
            ((X + 2 : Nat) : Real))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hBaseTop
  have hLogQuotient :
      Tendsto
        (fun X : Nat =>
          Real.log
            (((a * X / b + c + 2 : Nat) : Real) /
              ((X + 2 : Nat) : Real)))
        atTop
        (nhds
          (Real.log
            ((a : Real) / (b : Real)))) := by
    exact hValueRatio.log (by positivity)
  have hDifference :
      Tendsto
        (fun X : Nat =>
          Real.log
              ((a * X / b + c + 2 : Nat) : Real) -
            Real.log ((X + 2 : Nat) : Real))
        atTop
        (nhds
          (Real.log
            ((a : Real) / (b : Real)))) := by
    apply hLogQuotient.congr'
    apply Eventually.of_forall
    intro X
    change
      Real.log
          (((a * X / b + c + 2 : Nat) : Real) /
            ((X + 2 : Nat) : Real)) =
        Real.log
            ((a * X / b + c + 2 : Nat) : Real) -
          Real.log ((X + 2 : Nat) : Real)
    rw [Real.log_div (by positivity)
      (by positivity)]
  have hDifferenceSmall :
      Tendsto
        (fun X : Nat =>
          (Real.log
              ((a * X / b + c + 2 : Nat) : Real) -
            Real.log ((X + 2 : Nat) : Real)) /
              Real.log ((X + 2 : Nat) : Real))
        atTop (nhds 0) :=
    hDifference.div_atTop hLogBaseTop
  have hOneAdd :
      Tendsto
        (fun X : Nat =>
          (1 : Real) +
            (Real.log
                ((a * X / b + c + 2 : Nat) : Real) -
              Real.log ((X + 2 : Nat) : Real)) /
                Real.log ((X + 2 : Nat) : Real))
        atTop (nhds (1 + 0)) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : Nat => (1 : Real))
        atTop (nhds 1)).add hDifferenceSmall
  have hEq :
      (fun X : Nat =>
        1 +
          (Real.log
              ((a * X / b + c + 2 : Nat) : Real) -
            Real.log ((X + 2 : Nat) : Real)) /
              Real.log ((X + 2 : Nat) : Real)) =ᶠ[atTop]
      (fun X : Nat =>
        Real.log
            ((a * X / b + c + 2 : Nat) : Real) /
          Real.log ((X + 2 : Nat) : Real)) := by
    apply Eventually.of_forall
    intro X
    have hlogNe :
        Real.log ((X + 2 : Nat) : Real) ≠ 0 := by
      exact
        (Real.log_pos
          (by
            exact_mod_cast
              (by omega : 1 < X + 2))).ne'
    field_simp [hlogNe]
    ring
  simpa using hOneAdd.congr' hEq

/-- The shifted `x / log x` scale has the expected fixed linear scaling
law even with natural-number division. -/
theorem primeCountingScale_mul_div_add_ratio_tendsto
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun X : Nat =>
        primeCountingScale
            (a * X / b + c) /
          primeCountingScale X)
      atTop
      (nhds ((a : Real) / (b : Real))) := by
  have hValueRatio :=
    natCast_mul_div_add_ratio_tendsto
      a b (c + 2) 2 hb
  have hLogRatio :=
    log_nat_mul_div_add_ratio_tendsto_one
      a b c ha hb
  have hProduct :=
    hValueRatio.mul
      (hLogRatio.inv₀ one_ne_zero)
  have hEq :
      (fun X : Nat =>
        ((a * X / b + c + 2 : Nat) : Real) /
            ((X + 2 : Nat) : Real) *
          (Real.log
              ((a * X / b + c + 2 : Nat) : Real) /
            Real.log ((X + 2 : Nat) : Real))⁻¹) =ᶠ[atTop]
      (fun X : Nat =>
        primeCountingScale
            (a * X / b + c) /
          primeCountingScale X) := by
    apply Eventually.of_forall
    intro X
    unfold primeCountingScale
    push_cast
    have hlogBase :
        Real.log ((X : Real) + 2) ≠ 0 := by
      exact
        (Real.log_pos
          (by
            have hX :
                (0 : Real) ≤ X := by positivity
            linarith)).ne'
    have hlogValue :
      Real.log
            (((a * X / b : Nat) : Real) +
              (c : Real) + 2) ≠
          0 := by
      exact
        (Real.log_pos
          (by
            have hnonneg :
                (0 : Real) ≤
                  (a * X / b : Nat) := by
              positivity
            linarith)).ne'
    field_simp [hlogBase, hlogValue]
  simpa using hProduct.congr' hEq

end Erdos279
