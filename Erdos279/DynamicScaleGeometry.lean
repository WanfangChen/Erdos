import Erdos279.DynamicCutoffReadiness
import Erdos279.UniformHardSieve

/-!
# Geometry of the dynamic old-prime cutoff

For the paper's cutoff `z = floor(X^(1/v))`, with `v ≥ 2`, the cutoff
lies below `sqrt X`.  On a sufficiently large integral geometric scale
this is below the lower endpoint of every future controller annulus.
The same square-root estimate also supplies the maturity inequality
`k * z ≤ X`.
-/

namespace Erdos279

/-- Every integral `v`-th root with `v ≥ 2` is at most the integral
square root. -/
theorem nthRoot_le_sqrt
    {v X : Nat} (hv : 2 ≤ v) :
    Nat.nthRoot v X ≤ Nat.sqrt X := by
  let r := Nat.nthRoot v X
  by_cases hr : r = 0
  · simp [r, hr]
  · have hrOne : 1 ≤ r :=
      Nat.one_le_iff_ne_zero.mpr hr
    have hpow :
        r ^ v ≤ X := by
      exact Nat.pow_nthRoot_le (Or.inl (by omega : v ≠ 0))
    have hpowMono :
        r ^ 2 ≤ r ^ v :=
      Nat.pow_le_pow_right hrOne hv
    exact Nat.le_sqrt'.2 (hpowMono.trans hpow)

/-- If the scale is at least `k²`, the dynamic cutoff is mature:
`k * floor(X^(1/v)) ≤ X`. -/
theorem mul_nthRoot_le_of_sq_le
    {k v X : Nat}
    (hv : 2 ≤ v)
    (hkX : k ^ 2 ≤ X) :
    k * Nat.nthRoot v X ≤ X := by
  let r := Nat.nthRoot v X
  have hrSqrt : r ≤ Nat.sqrt X :=
    nthRoot_le_sqrt hv
  have hrSq : r ^ 2 ≤ X :=
    Nat.le_sqrt'.mp hrSqrt
  rcases le_total r k with hrk | hkr
  · calc
      k * r ≤ k * k :=
        Nat.mul_le_mul_left k hrk
      _ = k ^ 2 := by simp [pow_two]
      _ ≤ X := hkX
  · calc
      k * r ≤ r * r := by
        exact Nat.mul_le_mul_right r hkr
      _ = r ^ 2 := by simp [pow_two]
      _ ≤ X := hrSq

/-- A convenient sufficient condition for placing `sqrt X` below the
next integral geometric lower endpoint. -/
theorem sqrt_lt_mul_div
    {h B C X : Nat}
    (hh : 0 < h)
    (hC : C ^ 2 ≤ X)
    (hBC : 2 * h ≤ B * C) :
    Nat.sqrt X < (B * X) / h := by
  have hCroot : C ≤ Nat.sqrt X :=
    Nat.le_sqrt'.2 hC
  have hBCpos : 0 < B * C := by
    exact (Nat.mul_pos (by omega) hh).trans_le hBC
  have hCpos : 0 < C := by
    exact Nat.pos_of_ne_zero (fun hCzero => by
      subst C
      simp at hBCpos)
  have hrootPos : 0 < Nat.sqrt X :=
    hCpos.trans_le hCroot
  have hCsqrt :
      C * Nat.sqrt X ≤ X := by
    calc
      C * Nat.sqrt X ≤ Nat.sqrt X * Nat.sqrt X :=
        Nat.mul_le_mul_right (Nat.sqrt X) hCroot
      _ ≤ X := Nat.sqrt_le X
  apply Nat.lt_iff_add_one_le.mpr
  apply (Nat.le_div_iff_mul_le hh).2
  calc
    (Nat.sqrt X + 1) * h =
        h * Nat.sqrt X + h := by ring
    _ ≤ h * Nat.sqrt X + h * Nat.sqrt X := by
      exact Nat.add_le_add_left
        (Nat.le_mul_of_pos_right h hrootPos) _
    _ = (2 * h) * Nat.sqrt X := by ring
    _ ≤ (B * C) * Nat.sqrt X :=
      Nat.mul_le_mul_right (Nat.sqrt X) hBC
    _ = B * (C * Nat.sqrt X) := by ring
    _ ≤ B * X := Nat.mul_le_mul_left B hCsqrt

/-- Consequently the dynamic old-prime cutoff lies below the next
geometric controller lower endpoint. -/
theorem stageOldPrimeCutoff_lt_mul_div
    {h v B C X : Nat}
    (hv : 2 ≤ v)
    (hh : 0 < h)
    (hC : C ^ 2 ≤ X)
    (hBC : 2 * h ≤ B * C) :
    stageOldPrimeCutoff v X < (B * X) / h :=
  (nthRoot_le_sqrt hv).trans_lt
    (sqrt_lt_mul_div hh hC hBC)

end Erdos279
