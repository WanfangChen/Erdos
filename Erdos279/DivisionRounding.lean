import Erdos279.MobiusTotient
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Natural-division rounding in divisor main terms

Selberg--Delange is evaluated at the natural endpoint `x / r`, whereas its
main term is compared with the real quotient `x/r`.  This file proves the
rounding error explicitly and packages the resulting divisor-sum estimate
for an arbitrary slowly varying factor.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

/-- The real quotient lies strictly below the next integer after `x / r`. -/
theorem realDiv_lt_natCast_div_add_one
    (x r : Nat) (hr : 0 < r) :
    (x : Real) / (r : Real) < (x / r : Nat) + 1 := by
  have hrR : (0 : Real) < (r : Real) := by exact_mod_cast hr
  apply (div_lt_iff₀ hrR).mpr
  norm_cast
  exact (Nat.div_lt_iff_lt_mul hr).mp (Nat.lt_succ_self (x / r))

/-- Natural division differs from real division by less than one. -/
theorem abs_realDiv_sub_natCast_div_lt_one
    (x r : Nat) (hr : 0 < r) :
    |(x : Real) / (r : Real) - (x / r : Nat)| < 1 := by
  rw [abs_of_nonneg]
  · apply sub_lt_iff_lt_add.mpr
    simpa [add_comm] using realDiv_lt_natCast_div_add_one x r hr
  · exact sub_nonneg.mpr Nat.cast_div_le

/-- Non-strict form convenient for finite error sums. -/
theorem abs_realDiv_sub_natCast_div_le_one
    (x r : Nat) (hr : 0 < r) :
    |(x : Real) / (r : Real) - (x / r : Nat)| ≤ 1 :=
  (abs_realDiv_sub_natCast_div_lt_one x r hr).le

/--
Generic rounding-and-variation bound for a Möbius-weighted main term.

The first summand is evaluated at the natural quotient.  The comparison
summand freezes the slowly varying factor at `x` and replaces the natural
quotient by the real quotient.  The right side separates these two errors.
-/
theorem mobius_scaledMain_error_bound
    {n : Nat} (hn : n ≠ 0)
    (x : Nat) (slow : Nat → Real) :
    |(∑ r ∈ n.divisors,
          ((ArithmeticFunction.moebius r : Int) : Real) *
            (x / r : Nat) * slow (x / r)) -
        ∑ r ∈ n.divisors,
          ((ArithmeticFunction.moebius r : Int) : Real) *
            ((x : Real) / (r : Real)) * slow x| ≤
      ∑ r ∈ n.divisors,
        |((ArithmeticFunction.moebius r : Int) : Real)| *
          ((x / r : Nat) * |slow (x / r) - slow x| + |slow x|) := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ r ∈ n.divisors,
        (((ArithmeticFunction.moebius r : Int) : Real) *
              (x / r : Nat) * slow (x / r) -
          ((ArithmeticFunction.moebius r : Int) : Real) *
              ((x : Real) / (r : Real)) * slow x)| ≤
        ∑ r ∈ n.divisors,
          |((ArithmeticFunction.moebius r : Int) : Real) *
                (x / r : Nat) * slow (x / r) -
            ((ArithmeticFunction.moebius r : Int) : Real) *
                ((x : Real) / (r : Real)) * slow x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤
        ∑ r ∈ n.divisors,
          |((ArithmeticFunction.moebius r : Int) : Real)| *
            ((x / r : Nat) * |slow (x / r) - slow x| + |slow x|) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrd : r ∣ n := (Nat.mem_divisors.mp hr).1
      have hrpos : 0 < r :=
        Nat.pos_of_dvd_of_pos hrd (Nat.pos_of_ne_zero hn)
      let mob : Real :=
        ((ArithmeticFunction.moebius r : Int) : Real)
      let floorQ : Real := (x / r : Nat)
      let realQ : Real := (x : Real) / (r : Real)
      let slowQ : Real := slow (x / r)
      let slowX : Real := slow x
      have hround : |floorQ - realQ| ≤ 1 := by
        simpa [floorQ, realQ, abs_sub_comm] using
          abs_realDiv_sub_natCast_div_le_one x r hrpos
      have hfloor : 0 ≤ floorQ := by
        simp [floorQ]
      have hrearrange :
          mob * floorQ * slowQ - mob * realQ * slowX =
            mob *
              (floorQ * (slowQ - slowX) +
                (floorQ - realQ) * slowX) := by
        ring
      change
        |mob * floorQ * slowQ - mob * realQ * slowX| ≤
          |mob| * (floorQ * |slowQ - slowX| + |slowX|)
      rw [hrearrange, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg mob)
      calc
        |floorQ * (slowQ - slowX) +
            (floorQ - realQ) * slowX| ≤
            |floorQ * (slowQ - slowX)| +
              |(floorQ - realQ) * slowX| := abs_add_le _ _
        _ = floorQ * |slowQ - slowX| +
              |floorQ - realQ| * |slowX| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hfloor]
        _ ≤ floorQ * |slowQ - slowX| + 1 * |slowX| := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_right hround (abs_nonneg slowX))
        _ = floorQ * |slowQ - slowX| + |slowX| := by ring

end Erdos279
