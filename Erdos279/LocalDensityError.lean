import Erdos279.LocalDensityInterval
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Propagation of a summatory error through Möbius inversion

This is the analytic bookkeeping step in Lemma 2.2.  It is deliberately
stated for an arbitrary proposed main term and arbitrary pointwise error
bound.  A future Selberg--Delange theorem can therefore be plugged into the
result without repeating any divisor-sum algebra.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

/-- Real-valued version of the controller summatory function. -/
noncomputable def controllerSummatoryReal
    (h : Prime) (x : Nat) : Real :=
  (controllerSummatory h x : Real)

/-- Real-valued version of the coprime interval prefix difference. -/
noncomputable def controllerCoprimeIntervalReal
    (h : Prime) (d Y Z : Nat) : Real :=
  (controllerCoprimeIntervalSummatory h d Y Z : Real)

/-- Exact real-valued interval Möbius identity. -/
theorem controllerCoprimeIntervalReal_eq_moebius
    {h : Prime} {d Y Z : Nat}
    (hd : ControllerSemigroup h d) :
    controllerCoprimeIntervalReal h d Y Z =
      ∑ r ∈ d.divisors,
        ((ArithmeticFunction.moebius r : Int) : Real) *
          (controllerSummatoryReal h (Z / r) -
            controllerSummatoryReal h (Y / r)) := by
  rw [controllerCoprimeIntervalReal,
    controllerCoprimeIntervalSummatory_eq_moebius hd]
  push_cast
  simp only [controllerIntervalSummatory, controllerSummatoryReal,
    Int.cast_sub]

/--
Any pointwise approximation for `M(x)` propagates through exact Möbius
inversion.  The right side records both endpoint errors for every divisor.
-/
theorem controllerCoprimeInterval_error_bound
    {h : Prime} {d Y Z : Nat}
    (hd : ControllerSemigroup h d)
    (main errorBound : Nat → Real)
    (herror :
      ∀ x : Nat,
        |controllerSummatoryReal h x - main x| ≤ errorBound x) :
    |controllerCoprimeIntervalReal h d Y Z -
        ∑ r ∈ d.divisors,
          ((ArithmeticFunction.moebius r : Int) : Real) *
            (main (Z / r) - main (Y / r))| ≤
      ∑ r ∈ d.divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| *
          (errorBound (Z / r) + errorBound (Y / r)) := by
  rw [controllerCoprimeIntervalReal_eq_moebius hd,
    ← Finset.sum_sub_distrib]
  calc
    |∑ r ∈ d.divisors,
        (((ArithmeticFunction.moebius r : Int) : Real) *
            (controllerSummatoryReal h (Z / r) -
              controllerSummatoryReal h (Y / r)) -
          ((ArithmeticFunction.moebius r : Int) : Real) *
            (main (Z / r) - main (Y / r)))| ≤
        ∑ r ∈ d.divisors,
          |((ArithmeticFunction.moebius r : Int) : Real) *
              (controllerSummatoryReal h (Z / r) -
                controllerSummatoryReal h (Y / r)) -
            ((ArithmeticFunction.moebius r : Int) : Real) *
              (main (Z / r) - main (Y / r))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ r ∈ d.divisors,
          |((ArithmeticFunction.moebius r : Int) : Real)| *
            (errorBound (Z / r) + errorBound (Y / r)) := by
      apply Finset.sum_le_sum
      intro r _hr
      let mob : Real :=
        ((ArithmeticFunction.moebius r : Int) : Real)
      let upperError : Real :=
        controllerSummatoryReal h (Z / r) - main (Z / r)
      let lowerError : Real :=
        controllerSummatoryReal h (Y / r) - main (Y / r)
      have hrearrange :
          mob *
              (controllerSummatoryReal h (Z / r) -
                controllerSummatoryReal h (Y / r)) -
            mob * (main (Z / r) - main (Y / r)) =
            mob * (upperError - lowerError) := by
        simp only [mob, upperError, lowerError]
        ring
      rw [hrearrange, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg mob)
      calc
        |upperError - lowerError| ≤
            |upperError| + |lowerError| := abs_sub _ _
        _ ≤ errorBound (Z / r) + errorBound (Y / r) := by
          apply add_le_add
          · simpa [upperError] using herror (Z / r)
          · simpa [lowerError] using herror (Y / r)

end Erdos279
