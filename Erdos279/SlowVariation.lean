import Erdos279.AnalyticConstants
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit slow variation of the logarithmic Selberg factor

For `0 ≤ δ ≤ 1` and `0 ≤ t ≤ 1/2`, the elementary comparison

`1 ≤ (1-t)^(δ-1) ≤ (1-t)⁻¹`

gives the quantitative bound needed in Lemma 2.2 without invoking a
mean-value theorem.
-/

namespace Erdos279

/-- The normalized negative-power variation is at most `2t`. -/
theorem abs_one_sub_rpow_sub_one_le_two_mul
    {δ t : Real}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    |(1 - t) ^ (δ - 1) - 1| ≤ 2 * t := by
  have hbpos : 0 < 1 - t := by linarith
  have hble : 1 - t ≤ 1 := by linarith
  have hexpNonpos : δ - 1 ≤ 0 := by linarith
  have hexpLower : (-1 : Real) ≤ δ - 1 := by linarith
  have hlower :
      1 ≤ (1 - t) ^ (δ - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hbpos hble hexpNonpos
  have hupper :
      (1 - t) ^ (δ - 1) ≤ (1 - t) ^ (-1 : Real) :=
    Real.rpow_le_rpow_of_exponent_ge hbpos hble hexpLower
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  calc
    (1 - t) ^ (δ - 1) - 1 ≤
        (1 - t) ^ (-1 : Real) - 1 :=
      sub_le_sub_right hupper 1
    _ = t / (1 - t) := by
      rw [Real.rpow_neg_one]
      field_simp
      <;> ring
    _ ≤ 2 * t := by
      rw [div_le_iff₀ hbpos]
      have hnonneg : 0 ≤ t * (1 - 2 * t) :=
        mul_nonneg ht0 (by linarith)
      nlinarith

/-- Scaled form of the normalized slow-variation bound. -/
theorem abs_mul_one_sub_rpow_sub_rpow_le
    {δ L t : Real}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hL : 0 ≤ L)
    (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    |(L * (1 - t)) ^ (δ - 1) - L ^ (δ - 1)| ≤
      2 * t * L ^ (δ - 1) := by
  have hb : 0 ≤ 1 - t := by linarith
  rw [Real.mul_rpow hL hb]
  have hbase :
      |(1 - t) ^ (δ - 1) - 1| ≤ 2 * t :=
    abs_one_sub_rpow_sub_one_le_two_mul
      hδ0 hδ1 ht0 htHalf
  have hLpow : 0 ≤ L ^ (δ - 1) :=
    Real.rpow_nonneg hL (δ - 1)
  calc
    |L ^ (δ - 1) * (1 - t) ^ (δ - 1) -
        L ^ (δ - 1)| =
        |L ^ (δ - 1) *
          ((1 - t) ^ (δ - 1) - 1)| := by
      congr 1
      ring
    _ =
        |L ^ (δ - 1)| *
          |(1 - t) ^ (δ - 1) - 1| := by
      rw [abs_mul]
    _ ≤ L ^ (δ - 1) * (2 * t) := by
      rw [abs_of_nonneg hLpow]
      exact mul_le_mul_of_nonneg_left hbase hLpow
    _ = 2 * t * L ^ (δ - 1) := by ring

/-- Real-variable version of the logarithmic slow factor. -/
noncomputable def realSelbergSlow
    (δ x : Real) : Real :=
  Real.log x ^ (δ - 1)

/--
Explicit logarithmic slow variation.  The hypotheses on
`log r / log x` are exactly what follows from `1 ≤ r ≤ √x`.
-/
theorem realSelbergSlow_div_variation
    {δ x r : Real}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : 1 < x) (hr : 0 < r)
    (hratio0 : 0 ≤ Real.log r / Real.log x)
    (hratioHalf : Real.log r / Real.log x ≤ 1 / 2) :
    |realSelbergSlow δ (x / r) -
        realSelbergSlow δ x| ≤
      2 * (Real.log r / Real.log x) *
        realSelbergSlow δ x := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hfactor :
      Real.log x - Real.log r =
        Real.log x *
          (1 - Real.log r / Real.log x) := by
    field_simp [hlogx.ne']
    <;> ring
  rw [realSelbergSlow, realSelbergSlow,
    Real.log_div (by positivity) hr.ne', hfactor]
  exact abs_mul_one_sub_rpow_sub_rpow_le
    hδ0 hδ1 hlogx.le hratio0 hratioHalf

/-- A number at least one has a nonnegative logarithmic ratio. -/
theorem log_ratio_nonneg
    {x r : Real} (hx : 1 < x) (hr : 1 ≤ r) :
    0 ≤ Real.log r / Real.log x := by
  exact div_nonneg (Real.log_nonneg hr) (Real.log_pos hx).le

/--
If `r² ≤ x`, then its logarithmic ratio is at most one half.
-/
theorem log_ratio_le_half_of_sq_le
    {x r : Real}
    (hx : 1 < x) (hr : 0 < r)
    (hsq : r ^ 2 ≤ x) :
    Real.log r / Real.log x ≤ 1 / 2 := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hlog :
      Real.log (r ^ 2) ≤ Real.log x :=
    Real.log_le_log hrsq hsq
  rw [Real.log_pow] at hlog
  rw [div_le_iff₀ hlogx]
  norm_num at hlog ⊢
  linarith

/--
Slow variation in the standard square-root range `1 ≤ r` and `r² ≤ x`.
-/
theorem realSelbergSlow_div_variation_of_sq_le
    {δ x r : Real}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : 1 < x) (hr : 1 ≤ r)
    (hsq : r ^ 2 ≤ x) :
    |realSelbergSlow δ (x / r) -
        realSelbergSlow δ x| ≤
      2 * (Real.log r / Real.log x) *
        realSelbergSlow δ x := by
  exact realSelbergSlow_div_variation
    hδ0 hδ1 hx (lt_of_lt_of_le zero_lt_one hr)
    (log_ratio_nonneg hx hr)
    (log_ratio_le_half_of_sq_le
      hx (lt_of_lt_of_le zero_lt_one hr) hsq)

/-- Natural-number specialization of the square-root-range bound. -/
theorem realSelbergSlow_nat_div_variation_of_sq_le
    {δ : Real} {x r : Nat}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : 1 < x) (hr : 1 ≤ r)
    (hsq : r ^ 2 ≤ x) :
    |realSelbergSlow δ ((x : Real) / (r : Real)) -
        selbergSlow δ x| ≤
      2 *
          (Real.log (r : Real) / Real.log (x : Real)) *
        selbergSlow δ x := by
  simpa [selbergSlow, realSelbergSlow] using
    (realSelbergSlow_div_variation_of_sq_le
      hδ0 hδ1
      (by exact_mod_cast hx)
      (by exact_mod_cast hr)
      (by exact_mod_cast hsq))

/-- The natural and real definitions agree after casting the endpoint. -/
theorem selbergSlow_eq_realSelbergSlow
    (δ : Real) (x : Nat) :
    selbergSlow δ x = realSelbergSlow δ (x : Real) :=
  rfl

end Erdos279
