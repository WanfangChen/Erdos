import Erdos279.DivisionRounding

/-!
# Frozen main term in the local-density divisor sum

After freezing a slowly varying factor at `x`, the remaining divisor sum is
exactly the totient density times the global main term.  Together with
`mobius_scaledMain_error_bound`, this isolates all variation and rounding
errors from the exact density constant.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

/--
For a nonzero squarefree modulus, the frozen divisor main term equals
`(φ(n)/n) * x * slow(x)`.
-/
theorem mobius_realDiv_frozen_eq_totientMain
    {n : Nat} (hn : n ≠ 0) (hsq : Squarefree n)
    (x : Nat) (slow : Nat → Real) :
    (∑ r ∈ n.divisors,
        ((ArithmeticFunction.moebius r : Int) : Real) *
          ((x : Real) / (r : Real)) * slow x) =
      ((Nat.totient n : Real) / (n : Real)) *
        (x : Real) * slow x := by
  calc
    (∑ r ∈ n.divisors,
        ((ArithmeticFunction.moebius r : Int) : Real) *
          ((x : Real) / (r : Real)) * slow x) =
        ((x : Real) * slow x) *
          ∑ r ∈ n.divisors,
            ((ArithmeticFunction.moebius r : Int) : Real) /
              (r : Real) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = ((x : Real) * slow x) *
          ((Nat.totient n : Real) / (n : Real)) := by
      rw [sum_moebius_div_eq_totientRatio_real hn hsq]
    _ = ((Nat.totient n : Real) / (n : Real)) *
          (x : Real) * slow x := by ring

/--
The natural-quotient main term differs from the exact totient main term by
only the explicit rounding-and-variation sum.
-/
theorem mobius_scaledMain_totient_error_bound
    {n : Nat} (hn : n ≠ 0) (hsq : Squarefree n)
    (x : Nat) (slow : Nat → Real) :
    |(∑ r ∈ n.divisors,
          ((ArithmeticFunction.moebius r : Int) : Real) *
            (x / r : Nat) * slow (x / r)) -
        ((Nat.totient n : Real) / (n : Real)) *
          (x : Real) * slow x| ≤
      ∑ r ∈ n.divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| *
          ((x / r : Nat) * |slow (x / r) - slow x| + |slow x|) := by
  rw [← mobius_realDiv_frozen_eq_totientMain hn hsq x slow]
  exact mobius_scaledMain_error_bound hn x slow

end Erdos279
