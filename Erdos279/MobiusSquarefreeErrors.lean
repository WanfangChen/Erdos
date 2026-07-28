import Erdos279.DivisorEulerSums
import Erdos279.LocalDensityMain

/-!
# Absolute Möbius weights on squarefree sieve moduli

Every divisor of a squarefree modulus is squarefree, so its Möbius value has
absolute value one.  This removes the formal Möbius weights from all
nonnegative error sums in Lemma 2.2.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

theorem abs_moebius_real_eq_one_of_squarefree
    {r : Nat} (hr : Squarefree r) :
    |((ArithmeticFunction.moebius r : Int) : Real)| = 1 := by
  rw [← Int.cast_abs,
    ArithmeticFunction.abs_moebius_eq_one_of_squarefree hr]
  norm_num

theorem abs_moebius_real_eq_one_of_divisor
    {n r : Nat} (hsq : Squarefree n) (hr : r ∣ n) :
    |((ArithmeticFunction.moebius r : Int) : Real)| = 1 :=
  abs_moebius_real_eq_one_of_squarefree
    (hsq.squarefree_of_dvd hr)

/-- Absolute Möbius weights disappear from any real divisor sum over a
nonzero squarefree modulus. -/
theorem sum_abs_moebius_mul_of_squarefree
    {n : Nat} (hn : n ≠ 0) (hsq : Squarefree n)
    (f : Nat → Real) :
    (∑ r ∈ n.divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| * f r) =
      ∑ r ∈ n.divisors, f r := by
  apply Finset.sum_congr rfl
  intro r hr
  have hrd : r ∣ n := (Nat.mem_divisors.mp hr).1
  rw [abs_moebius_real_eq_one_of_divisor hsq hrd, one_mul]

/-- Absolute Möbius reciprocal mass is the squarefree Euler product. -/
theorem abs_moebius_reciprocal_sum_primeSubsetModulus
    (d : Finset Prime) :
    (∑ r ∈ (primeSubsetModulus d).divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| /
          (r : Real)) =
      ∏ p ∈ d, (1 + (p.1 : Real)⁻¹) := by
  calc
    (∑ r ∈ (primeSubsetModulus d).divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| /
          (r : Real)) =
        ∑ r ∈ (primeSubsetModulus d).divisors,
          (r : Real)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrd : r ∣ primeSubsetModulus d :=
        (Nat.mem_divisors.mp hr).1
      rw [abs_moebius_real_eq_one_of_divisor
        (primeSubsetModulus_squarefree d) hrd]
      simp [div_eq_mul_inv]
    _ = ∏ p ∈ d, (1 + (p.1 : Real)⁻¹) :=
      reciprocal_divisor_sum_primeSubsetModulus d

/-- Absolute Möbius logarithmic reciprocal mass is the corresponding
Euler-product logarithmic derivative. -/
theorem abs_moebius_log_reciprocal_sum_primeSubsetModulus
    (d : Finset Prime) :
    (∑ r ∈ (primeSubsetModulus d).divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| *
          (Real.log (r : Real) / (r : Real))) =
      (∏ p ∈ d, (1 + (p.1 : Real)⁻¹)) *
        ∑ p ∈ d,
          Real.log (p.1 : Real) / (p.1 + 1 : Real) := by
  calc
    (∑ r ∈ (primeSubsetModulus d).divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| *
          (Real.log (r : Real) / (r : Real))) =
        ∑ r ∈ (primeSubsetModulus d).divisors,
          Real.log (r : Real) / (r : Real) := by
      exact sum_abs_moebius_mul_of_squarefree
        (primeSubsetModulus_ne_zero d)
        (primeSubsetModulus_squarefree d)
        (fun r => Real.log (r : Real) / (r : Real))
    _ =
        (∏ p ∈ d, (1 + (p.1 : Real)⁻¹)) *
          ∑ p ∈ d,
            Real.log (p.1 : Real) / (p.1 + 1 : Real) :=
      log_reciprocal_divisor_sum_primeSubsetModulus d

/-- The explicit propagated summatory error loses all Möbius absolute
weights on a project-prime modulus. -/
theorem mobiusSummatoryError_primeSubsetModulus
    (d : Finset Prime) (Y Z : Nat)
    (errorBound : Nat → Real) :
    mobiusSummatoryError
        (primeSubsetModulus d) Y Z errorBound =
      ∑ r ∈ (primeSubsetModulus d).divisors,
        (errorBound (Z / r) + errorBound (Y / r)) := by
  unfold mobiusSummatoryError
  exact sum_abs_moebius_mul_of_squarefree
    (primeSubsetModulus_ne_zero d)
    (primeSubsetModulus_squarefree d)
    (fun r => errorBound (Z / r) + errorBound (Y / r))

/-- The explicit rounding-and-variation error also loses all Möbius
absolute weights on a project-prime modulus. -/
theorem mobiusVariationError_primeSubsetModulus
    (d : Finset Prime) (x : Nat)
    (slow : Nat → Real) :
    mobiusVariationError (primeSubsetModulus d) x slow =
      ∑ r ∈ (primeSubsetModulus d).divisors,
        ((x / r : Nat) * |slow (x / r) - slow x| +
          |slow x|) := by
  unfold mobiusVariationError
  exact sum_abs_moebius_mul_of_squarefree
    (primeSubsetModulus_ne_zero d)
    (primeSubsetModulus_squarefree d)
    (fun r =>
      (x / r : Nat) * |slow (x / r) - slow x| +
        |slow x|)

end Erdos279
