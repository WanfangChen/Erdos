import Erdos279.LocalDensityError
import Erdos279.MobiusMainTerm

/-!
# Local density from a pointwise summatory approximation

This module combines:

* exact interval Möbius inversion;
* propagation of the pointwise summatory error;
* natural-division rounding;
* variation of the slowly varying factor;
* the exact Möbius--totient density.

It is the algebraic core of Lemma 2.2.  The only input left abstract is the
actual Selberg--Delange estimate and a bound on the variation of its
logarithmic factor.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

/-- A Selberg--Delange-shaped main term with arbitrary coefficient and factor. -/
noncomputable def scaledSummatoryMain
    (coefficient : Real) (slow : Nat → Real) (x : Nat) : Real :=
  coefficient * (x : Real) * slow x

/-- The Möbius-weighted main sum evaluated at natural quotients. -/
noncomputable def mobiusScaledSum
    (n x : Nat) (slow : Nat → Real) : Real :=
  ∑ r ∈ n.divisors,
    ((ArithmeticFunction.moebius r : Int) : Real) *
      (x / r : Nat) * slow (x / r)

/-- Explicit endpoint rounding-and-variation error. -/
noncomputable def mobiusVariationError
    (n x : Nat) (slow : Nat → Real) : Real :=
  ∑ r ∈ n.divisors,
    |((ArithmeticFunction.moebius r : Int) : Real)| *
      ((x / r : Nat) * |slow (x / r) - slow x| + |slow x|)

/-- Explicit propagated Selberg--Delange error at both interval endpoints. -/
noncomputable def mobiusSummatoryError
    (n Y Z : Nat) (errorBound : Nat → Real) : Real :=
  ∑ r ∈ n.divisors,
    |((ArithmeticFunction.moebius r : Int) : Real)| *
      (errorBound (Z / r) + errorBound (Y / r))

/-- Endpoint form of the natural-quotient main-term estimate. -/
theorem mobiusScaledSum_totient_error_bound
    {n : Nat} (hn : n ≠ 0) (hsq : Squarefree n)
    (x : Nat) (slow : Nat → Real) :
    |mobiusScaledSum n x slow -
        ((Nat.totient n : Real) / (n : Real)) *
          (x : Real) * slow x| ≤
      mobiusVariationError n x slow := by
  exact mobius_scaledMain_totient_error_bound hn hsq x slow

/-- Difference of two approximations is bounded by the sum of their errors. -/
theorem abs_sub_sub_le_of_le
    {a b A B εa εb : Real}
    (ha : |a - A| ≤ εa)
    (hb : |b - B| ≤ εb) :
    |(a - b) - (A - B)| ≤ εa + εb := by
  calc
    |(a - b) - (A - B)| = |(a - A) - (b - B)| := by
      congr 1
      ring
    _ ≤ |a - A| + |b - B| := abs_sub _ _
    _ ≤ εa + εb := add_le_add ha hb

/--
The sum of scaled main-term differences is the coefficient times the
difference of the two natural-quotient Möbius sums.
-/
theorem sum_scaledSummatoryMain_sub_eq
    (n Y Z : Nat) (coefficient : Real) (slow : Nat → Real) :
    (∑ r ∈ n.divisors,
        ((ArithmeticFunction.moebius r : Int) : Real) *
          (scaledSummatoryMain coefficient slow (Z / r) -
            scaledSummatoryMain coefficient slow (Y / r))) =
      coefficient *
        (mobiusScaledSum n Z slow - mobiusScaledSum n Y slow) := by
  calc
    (∑ r ∈ n.divisors,
        ((ArithmeticFunction.moebius r : Int) : Real) *
          (scaledSummatoryMain coefficient slow (Z / r) -
            scaledSummatoryMain coefficient slow (Y / r))) =
        ∑ r ∈ n.divisors,
          (coefficient *
              (((ArithmeticFunction.moebius r : Int) : Real) *
                (Z / r : Nat) * slow (Z / r)) -
            coefficient *
              (((ArithmeticFunction.moebius r : Int) : Real) *
                (Y / r : Nat) * slow (Y / r))) := by
      apply Finset.sum_congr rfl
      intro r _hr
      simp only [scaledSummatoryMain]
      ring
    _ = coefficient * mobiusScaledSum n Z slow -
          coefficient * mobiusScaledSum n Y slow := by
      rw [Finset.sum_sub_distrib]
      simp only [mobiusScaledSum, Finset.mul_sum]
    _ = coefficient *
          (mobiusScaledSum n Z slow - mobiusScaledSum n Y slow) := by
      ring

/--
The natural-quotient interval main term differs from the exact totient
density times the global interval main term by the two endpoint
rounding-and-variation errors.
-/
theorem scaledMobiusInterval_totient_error_bound
    {n : Nat} (hn : n ≠ 0) (hsq : Squarefree n)
    (Y Z : Nat) (coefficient : Real) (slow : Nat → Real) :
    |coefficient *
          (mobiusScaledSum n Z slow - mobiusScaledSum n Y slow) -
        ((Nat.totient n : Real) / (n : Real)) *
          (scaledSummatoryMain coefficient slow Z -
            scaledSummatoryMain coefficient slow Y)| ≤
      |coefficient| *
        (mobiusVariationError n Z slow +
          mobiusVariationError n Y slow) := by
  have hZ :=
    mobiusScaledSum_totient_error_bound hn hsq Z slow
  have hY :=
    mobiusScaledSum_totient_error_bound hn hsq Y slow
  have hdiff :=
    abs_sub_sub_le_of_le hZ hY
  have hscaled :
      |coefficient *
          ((mobiusScaledSum n Z slow - mobiusScaledSum n Y slow) -
            (((Nat.totient n : Real) / (n : Real)) *
                (Z : Real) * slow Z -
              ((Nat.totient n : Real) / (n : Real)) *
                (Y : Real) * slow Y))| ≤
        |coefficient| *
          (mobiusVariationError n Z slow +
            mobiusVariationError n Y slow) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg coefficient)
  unfold scaledSummatoryMain
  convert hscaled using 1 <;> ring

/--
Abstract local-density theorem.  A pointwise estimate for the global
summatory function yields an explicit interval estimate for every nonzero
squarefree controller-semigroup modulus.
-/
theorem controllerCoprimeInterval_localDensity_bound
    {h : Prime} {n Y Z : Nat}
    (hnSemigroup : ControllerSemigroup h n)
    (hsq : Squarefree n)
    (coefficient : Real)
    (slow errorBound : Nat → Real)
    (herror :
      ∀ x : Nat,
        |controllerSummatoryReal h x -
          scaledSummatoryMain coefficient slow x| ≤ errorBound x) :
    |controllerCoprimeIntervalReal h n Y Z -
        ((Nat.totient n : Real) / (n : Real)) *
          (scaledSummatoryMain coefficient slow Z -
            scaledSummatoryMain coefficient slow Y)| ≤
      mobiusSummatoryError n Y Z errorBound +
        |coefficient| *
          (mobiusVariationError n Z slow +
            mobiusVariationError n Y slow) := by
  let divisorMain : Real :=
    ∑ r ∈ n.divisors,
      ((ArithmeticFunction.moebius r : Int) : Real) *
        (scaledSummatoryMain coefficient slow (Z / r) -
          scaledSummatoryMain coefficient slow (Y / r))
  have hprop :
      |controllerCoprimeIntervalReal h n Y Z - divisorMain| ≤
        mobiusSummatoryError n Y Z errorBound := by
    exact controllerCoprimeInterval_error_bound
      hnSemigroup
      (scaledSummatoryMain coefficient slow)
      errorBound herror
  have hmain :
      |divisorMain -
          ((Nat.totient n : Real) / (n : Real)) *
            (scaledSummatoryMain coefficient slow Z -
              scaledSummatoryMain coefficient slow Y)| ≤
        |coefficient| *
            (mobiusVariationError n Z slow +
              mobiusVariationError n Y slow) := by
    dsimp only [divisorMain]
    rw [sum_scaledSummatoryMain_sub_eq]
    exact scaledMobiusInterval_totient_error_bound
      hnSemigroup.pos.ne' hsq Y Z coefficient slow
  calc
    |controllerCoprimeIntervalReal h n Y Z -
        ((Nat.totient n : Real) / (n : Real)) *
          (scaledSummatoryMain coefficient slow Z -
            scaledSummatoryMain coefficient slow Y)| =
        |(controllerCoprimeIntervalReal h n Y Z - divisorMain) +
          (divisorMain -
            ((Nat.totient n : Real) / (n : Real)) *
              (scaledSummatoryMain coefficient slow Z -
                scaledSummatoryMain coefficient slow Y))| := by
      congr 1
      ring
    _ ≤ |controllerCoprimeIntervalReal h n Y Z - divisorMain| +
        |divisorMain -
          ((Nat.totient n : Real) / (n : Real)) *
            (scaledSummatoryMain coefficient slow Z -
              scaledSummatoryMain coefficient slow Y)| :=
      abs_add_le _ _
    _ ≤ mobiusSummatoryError n Y Z errorBound +
        |coefficient| *
          (mobiusVariationError n Z slow +
            mobiusVariationError n Y slow) :=
      add_le_add hprop hmain

end Erdos279
