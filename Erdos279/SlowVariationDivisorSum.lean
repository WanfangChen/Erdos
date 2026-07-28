import Erdos279.SlowVariation
import Erdos279.MobiusSquarefreeErrors

/-!
# Summing slow variation over squarefree divisors

This combines the pointwise logarithmic variation bound with the exact
Euler-product logarithmic derivative from Lemma 2.2.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

/--
For a squarefree project-prime modulus `d` with `d² ≤ x`, the complete
Möbius-weighted real-quotient slow-variation sum is bounded by the exact
Euler product and logarithmic prime-factor sum from the paper.
-/
theorem real_divisor_slowVariation_sum_le_euler
    (d : Finset Prime) {x : Nat} {δ : Real}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : 1 < x)
    (hmodSq : (primeSubsetModulus d) ^ 2 ≤ x) :
    (∑ r ∈ (primeSubsetModulus d).divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| *
          ((x : Real) / (r : Real)) *
            |realSelbergSlow δ ((x : Real) / (r : Real)) -
              selbergSlow δ x|) ≤
      (2 * (x : Real) * selbergSlow δ x /
          Real.log (x : Real)) *
        (∏ p ∈ d, (1 + (p.1 : Real)⁻¹)) *
          ∑ p ∈ d,
            Real.log (p.1 : Real) / (p.1 + 1 : Real) := by
  have hxR : (1 : Real) < (x : Real) := by
    exact_mod_cast hx
  have hlogx : 0 < Real.log (x : Real) :=
    Real.log_pos hxR
  calc
    (∑ r ∈ (primeSubsetModulus d).divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| *
          ((x : Real) / (r : Real)) *
            |realSelbergSlow δ ((x : Real) / (r : Real)) -
              selbergSlow δ x|) ≤
        ∑ r ∈ (primeSubsetModulus d).divisors,
          (2 * (x : Real) * selbergSlow δ x /
              Real.log (x : Real)) *
            (Real.log (r : Real) / (r : Real)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrd : r ∣ primeSubsetModulus d :=
        (Nat.mem_divisors.mp hr).1
      have hrpos : 0 < r :=
        Nat.pos_of_dvd_of_pos hrd
          (primeSubsetModulus_pos d)
      have hrone : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrpos.ne'
      have hrle : r ≤ primeSubsetModulus d :=
        Nat.le_of_dvd (primeSubsetModulus_pos d) hrd
      have hrsq :
          r ^ 2 ≤ x :=
        (Nat.pow_le_pow_left hrle 2).trans hmodSq
      have hvariation :=
        realSelbergSlow_nat_div_variation_of_sq_le
          hδ0 hδ1 hx hrone hrsq
      have hquotNonneg :
          0 ≤ (x : Real) / (r : Real) := by positivity
      have habsMob :
          |((ArithmeticFunction.moebius r : Int) : Real)| = 1 :=
        abs_moebius_real_eq_one_of_divisor
          (primeSubsetModulus_squarefree d) hrd
      rw [habsMob, one_mul]
      calc
        ((x : Real) / (r : Real)) *
            |realSelbergSlow δ ((x : Real) / (r : Real)) -
              selbergSlow δ x| ≤
            ((x : Real) / (r : Real)) *
              (2 *
                  (Real.log (r : Real) /
                    Real.log (x : Real)) *
                selbergSlow δ x) :=
          mul_le_mul_of_nonneg_left hvariation hquotNonneg
        _ =
            (2 * (x : Real) * selbergSlow δ x /
                Real.log (x : Real)) *
              (Real.log (r : Real) / (r : Real)) := by
          have hrRne : (r : Real) ≠ 0 := by
            exact_mod_cast hrpos.ne'
          field_simp [hrRne, hlogx.ne']
          <;> ring
    _ =
        (2 * (x : Real) * selbergSlow δ x /
            Real.log (x : Real)) *
          (∑ r ∈ (primeSubsetModulus d).divisors,
            Real.log (r : Real) / (r : Real)) := by
      rw [Finset.mul_sum]
    _ =
        (2 * (x : Real) * selbergSlow δ x /
            Real.log (x : Real)) *
          ((∏ p ∈ d, (1 + (p.1 : Real)⁻¹)) *
            ∑ p ∈ d,
              Real.log (p.1 : Real) /
                (p.1 + 1 : Real)) := by
      rw [log_reciprocal_divisor_sum_primeSubsetModulus]
    _ =
        (2 * (x : Real) * selbergSlow δ x /
            Real.log (x : Real)) *
          (∏ p ∈ d, (1 + (p.1 : Real)⁻¹)) *
            ∑ p ∈ d,
              Real.log (p.1 : Real) /
                (p.1 + 1 : Real) := by
      ring

end Erdos279
