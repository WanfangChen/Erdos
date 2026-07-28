import Erdos279.SieveArithmetic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The Möbius density equals the totient density

For a nonzero squarefree modulus,

`∑_{r ∣ d} μ(r) / r = φ(d) / d`.

This is the exact main-term identity used in Lemma 2.2.  It is proved through
mathlib's multiplicative Euler-product theorem, not by assuming an analytic
estimate.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

/-- The completely multiplicative arithmetic function `n ↦ 1/n` over `ℚ`. -/
noncomputable def reciprocalArithmetic : ArithmeticFunction Rat where
  toFun n := ((n : Rat)⁻¹)
  map_zero' := by simp

@[simp]
theorem reciprocalArithmetic_apply (n : Nat) :
    reciprocalArithmetic n = (n : Rat)⁻¹ :=
  rfl

/-- The reciprocal arithmetic function is multiplicative. -/
theorem reciprocalArithmetic_isMultiplicative :
    ArithmeticFunction.IsMultiplicative reciprocalArithmetic := by
  constructor
  · simp [reciprocalArithmetic]
  · intro m n _hmn
    simp [reciprocalArithmetic, Nat.cast_mul, mul_comm]

/-- Euler-product form of the squarefree Möbius divisor sum. -/
theorem sum_moebius_div_eq_primeFactorProduct
    {n : Nat} (hsq : Squarefree n) :
    (∑ r ∈ n.divisors,
        ((ArithmeticFunction.moebius r : Int) : Rat) / (r : Rat)) =
      ∏ p ∈ n.primeFactors, (1 - (p : Rat)⁻¹) := by
  have heuler :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      reciprocalArithmetic reciprocalArithmetic_isMultiplicative hsq
  simpa [reciprocalArithmetic, div_eq_mul_inv] using heuler.symm

/-- The squarefree Möbius divisor density is exactly `φ(n)/n`. -/
theorem sum_moebius_div_eq_totientRatio
    {n : Nat} (hn : n ≠ 0) (hsq : Squarefree n) :
    (∑ r ∈ n.divisors,
        ((ArithmeticFunction.moebius r : Int) : Rat) / (r : Rat)) =
      (Nat.totient n : Rat) / (n : Rat) := by
  rw [sum_moebius_div_eq_primeFactorProduct hsq]
  have htot :
      (Nat.totient n : Rat) =
        (n : Rat) *
          ∏ p ∈ n.primeFactors, (1 - (p : Rat)⁻¹) :=
    Nat.totient_eq_mul_prod_factors n
  have hnq : (n : Rat) ≠ 0 := by exact_mod_cast hn
  rw [htot]
  field_simp

/--
Specialization to the product of any finite set of distinct project primes,
the precise moduli occurring in the old-prime sieve.
-/
theorem sum_moebius_primeSubsetModulus_eq_totientRatio
    (d : Finset Prime) :
    (∑ r ∈ (primeSubsetModulus d).divisors,
        ((ArithmeticFunction.moebius r : Int) : Rat) / (r : Rat)) =
      (Nat.totient (primeSubsetModulus d) : Rat) /
        (primeSubsetModulus d : Rat) := by
  exact sum_moebius_div_eq_totientRatio
    (primeSubsetModulus_ne_zero d)
    (primeSubsetModulus_squarefree d)

/--
The divisor-indexed Möbius density agrees with the subset-indexed density
already used by the deterministic sieve.
-/
theorem sum_moebius_primeSubsetModulus_eq_subsetDensity
    (d : Finset Prime) :
    (∑ r ∈ (primeSubsetModulus d).divisors,
        ((ArithmeticFunction.moebius r : Int) : Rat) / (r : Rat)) =
      ∑ s ∈ d.powerset, subsetMobiusDensity s := by
  rw [sum_moebius_primeSubsetModulus_eq_totientRatio,
    sum_subsetMobiusDensity_eq_totientRatio]

/-- Real-valued form of the squarefree Möbius--totient density identity. -/
theorem sum_moebius_div_eq_totientRatio_real
    {n : Nat} (hn : n ≠ 0) (hsq : Squarefree n) :
    (∑ r ∈ n.divisors,
        ((ArithmeticFunction.moebius r : Int) : Real) / (r : Real)) =
      (Nat.totient n : Real) / (n : Real) := by
  have hq := sum_moebius_div_eq_totientRatio hn hsq
  have hr := congrArg (fun q : Rat => (q : Real)) hq
  push_cast at hr
  exact hr

/-- Real-valued specialization to the sieve's prime-subset moduli. -/
theorem sum_moebius_primeSubsetModulus_eq_totientRatio_real
    (d : Finset Prime) :
    (∑ r ∈ (primeSubsetModulus d).divisors,
        ((ArithmeticFunction.moebius r : Int) : Real) / (r : Real)) =
      (Nat.totient (primeSubsetModulus d) : Real) /
        (primeSubsetModulus d : Real) := by
  exact sum_moebius_div_eq_totientRatio_real
    (primeSubsetModulus_ne_zero d)
    (primeSubsetModulus_squarefree d)

end Erdos279
