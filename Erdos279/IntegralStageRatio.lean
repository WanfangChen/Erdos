import Erdos279.HardCapacityCoefficient

/-!
# An integral geometric ratio attached to a large hub

The paper first chooses a real geometric ratio of order `sqrt (h / k)`.
For the actual scale `X j = base * B ^ j` we need an integer ratio.
Here we use

`B = 2 * Nat.sqrt (h / k)`.

Once `h ≥ 256 * k`, this single choice has all three properties needed
later:

* the controller annulus has positive width, `k * B < h`;
* consecutive hard annuli are separated, `h ≤ k * B ^ 2`;
* the geometric loss is at most `4 * sqrt (k * h)`.
-/

namespace Erdos279

/-- Integral replacement for the paper's real geometric scale ratio. -/
def integralStageRatio (k h : Nat) : Nat :=
  2 * Nat.sqrt (h / k)

theorem integralStageRatio_spec
    {k h : Nat} (hk : 0 < k) (hlarge : 256 * k ≤ h) :
    2 ≤ integralStageRatio k h ∧
      k * integralStageRatio k h < h ∧
      h ≤ k * integralStageRatio k h ^ 2 ∧
      0 <
        1 / (k : Real) -
          (integralStageRatio k h : Real) / (h : Real) ∧
      ((integralStageRatio k h : Real) - 1) /
          (1 / (k : Real) -
            (integralStageRatio k h : Real) / (h : Real)) ≤
        4 * Real.sqrt ((k * h : Nat) : Real) := by
  let q := h / k
  let s := Nat.sqrt q
  let B := 2 * s
  have hq : 256 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hk).2 (by
      simpa [mul_comm] using hlarge)
  have hs : 16 ≤ s := by
    rw [show s = Nat.sqrt q by rfl]
    exact Nat.le_sqrt.mpr (by
      norm_num
      exact hq)
  have hspos : 0 < s := by omega
  have hsq_le_q : s * s ≤ q := by
    exact Nat.sqrt_le q
  have hqk_le_h : q * k ≤ h := by
    dsimp [q]
    exact Nat.div_mul_le_self h k
  have hksq_le_h : k * (s * s) ≤ h := by
    calc
      k * (s * s) = (s * s) * k := by
        simp [mul_comm]
      _ ≤ q * k := Nat.mul_le_mul_right k hsq_le_q
      _ ≤ h := hqk_le_h
  have hfourks_le_h : 4 * k * s ≤ h := by
    have hfour_s : 4 * s ≤ s * s := by nlinarith
    calc
      4 * k * s = k * (4 * s) := by ring
      _ ≤ k * (s * s) := Nat.mul_le_mul_left k hfour_s
      _ ≤ h := hksq_le_h
  have hkB_lt_h : k * B < h := by
    dsimp [B]
    have htwo_s_lt_four_s : 2 * s < 4 * s := by omega
    exact
      ((Nat.mul_lt_mul_left hk).2 htwo_s_lt_four_s) |>.trans_le
        (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hfourks_le_h)
  have hh_lt_kqsucc : h < k * (q + 1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ h hk
  have hqsucc_le_four_sq : q + 1 ≤ 4 * (s * s) := by
    have hqsucc_le :
        q + 1 ≤ (s + 1) * (s + 1) := by
      simpa [s] using Nat.succ_le_succ_sqrt q
    have hsquare :
        (s + 1) * (s + 1) ≤ 4 * (s * s) := by
      nlinarith
    exact hqsucc_le.trans hsquare
  have hh_le_kBsq : h ≤ k * B ^ 2 := by
    have hh_lt : h < k * (4 * (s * s)) :=
      hh_lt_kqsucc.trans_le
        (Nat.mul_le_mul_left k hqsucc_le_four_sq)
    have hrewrite : k * B ^ 2 = k * (4 * (s * s)) := by
      dsimp [B]
      ring
    rw [hrewrite]
    exact hh_lt.le
  have hhpos : 0 < h := lt_of_lt_of_le
    (by positivity : 0 < 256 * k) hlarge
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hhR : 0 < (h : Real) := by exact_mod_cast hhpos
  have hkB_R : (k : Real) * (B : Real) < (h : Real) := by
    exact_mod_cast hkB_lt_h
  have hwidth :
      0 <
        1 / (k : Real) - (B : Real) / (h : Real) := by
    rw [sub_pos]
    exact (div_lt_div_iff₀ hhR hkR).2 (by
      simpa [mul_comm] using hkB_R)
  have hwidth_eq :
      1 / (k : Real) - (B : Real) / (h : Real) =
        ((h : Real) - (k : Real) * (B : Real)) /
          ((k : Real) * (h : Real)) := by
    field_simp
    <;> ring
  have hfourks_R :
      (4 : Real) * (k : Real) * (s : Real) ≤ (h : Real) := by
    exact_mod_cast hfourks_le_h
  have hratio_le_fourks :
      ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h : Real)) ≤
        4 * (k : Real) * (s : Real) := by
    rw [hwidth_eq]
    have hratio_eq :
        ((B : Real) - 1) /
            (((h : Real) - (k : Real) * (B : Real)) /
              ((k : Real) * (h : Real))) =
          (((B : Real) - 1) * ((k : Real) * (h : Real))) /
            ((h : Real) - (k : Real) * (B : Real)) := by
      field_simp
      <;> ring
    rw [hratio_eq]
    apply (div_le_iff₀ (sub_pos.mpr hkB_R)).2
    dsimp [B]
    push_cast
    have hdiff :
        0 ≤
          (h : Real) - 4 * (k : Real) * (s : Real) :=
      sub_nonneg.mpr hfourks_R
    have hnonneg :
        0 ≤
          2 * (k : Real) * (s : Real) *
            ((h : Real) - 4 * (k : Real) * (s : Real)) +
            (k : Real) * (h : Real) := by
      exact add_nonneg
        (mul_nonneg (by positivity) hdiff)
        (by positivity)
    have hidentity :
        4 * (k : Real) * (s : Real) *
              ((h : Real) -
                (k : Real) * (2 * (s : Real))) -
            ((2 * (s : Real)) - 1) *
              ((k : Real) * (h : Real)) =
          2 * (k : Real) * (s : Real) *
              ((h : Real) -
                4 * (k : Real) * (s : Real)) +
            (k : Real) * (h : Real) := by
      ring
    exact sub_nonneg.mp (by
      rw [hidentity]
      exact hnonneg)
  have hks_sq_nat :
      (k * s) ^ 2 ≤ k * h := by
    calc
      (k * s) ^ 2 = k * (k * (s * s)) := by ring
      _ ≤ k * h := Nat.mul_le_mul_left k hksq_le_h
  have hks_sq_real :
      ((k * s : Nat) : Real) ^ 2 ≤ ((k * h : Nat) : Real) := by
    exact_mod_cast hks_sq_nat
  have hks_le_sqrt :
      (k : Real) * (s : Real) ≤
        Real.sqrt ((k * h : Nat) : Real) := by
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((k * h : Nat) : Real) :=
      Real.sqrt_nonneg _
    have hsqrt_sq :
        (Real.sqrt ((k * h : Nat) : Real)) ^ 2 =
          ((k * h : Nat) : Real) := by
      exact Real.sq_sqrt (by positivity)
    have hks_nonneg :
        0 ≤ (k : Real) * (s : Real) := by positivity
    have hcast :
        (((k * s : Nat) : Real)) =
          (k : Real) * (s : Real) := by norm_num
    rw [hcast] at hks_sq_real
    nlinarith
  have hratio :
      ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h : Real)) ≤
        4 * Real.sqrt ((k * h : Nat) : Real) :=
    hratio_le_fourks.trans (by
      have hmul :=
        mul_le_mul_of_nonneg_left hks_le_sqrt
          (show (0 : Real) ≤ 4 by norm_num)
      simpa [mul_assoc] using hmul)
  change
    2 ≤ B ∧
      k * B < h ∧
      h ≤ k * B ^ 2 ∧
      0 < 1 / (k : Real) - (B : Real) / (h : Real) ∧
      ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h : Real)) ≤
        4 * Real.sqrt ((k * h : Nat) : Real)
  exact ⟨by dsimp [B]; omega, hkB_lt_h, hh_le_kBsq, hwidth, hratio⟩

end Erdos279
