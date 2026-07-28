import Erdos279.GammaStrictConvex
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Choosing a hub prime with strict controller capacity

This formalizes the elementary limiting argument in (3.1).  The strict
Gamma bound reduces the coefficient to a constant times
`√h / (h-1)`, and Euclid's theorem supplies an arbitrarily large prime.
-/

namespace Erdos279

/-- The leading capacity coefficient on the left side of (3.1). -/
noncomputable def hubCapacityCoefficient
    (Csv : Real) (v k : Nat) (h : Prime) : Real :=
  2 * Csv *
    (v : Real) ^ (controllerDensity h) *
      Real.sqrt ((k * h.1 : Nat) : Real) *
        paperA (controllerDensity h)

/--
For every nonnegative constant `D`, arbitrarily large project primes make
`D √h / (h-1)` smaller than one.
-/
theorem exists_prime_sqrt_div_sub_one_lt
    (D : Real) (hD : 0 ≤ D) (k : Nat) :
    ∃ h : Prime,
      k < h.1 ∧
        D * Real.sqrt (h.1 : Real) /
            ((h.1 : Real) - 1) < 1 := by
  obtain ⟨N : Nat, hN⟩ :=
    exists_nat_gt
      (max (k : Real) (max 4 (4 * D ^ 2)))
  obtain ⟨p, hpPrime, hNp, _hpmod⟩ :=
    Nat.exists_prime_gt_modEq_one
      (k := 1) N one_ne_zero
  let h : Prime :=
    ⟨p, (isPrime_iff_natPrime p).2 hpPrime⟩
  have hkN : (k : Real) < (N : Real) :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hfourN : (4 : Real) < (N : Real) :=
    lt_of_le_of_lt
      (le_trans (le_max_left 4 (4 * D ^ 2))
        (le_max_right (k : Real) _))
      hN
  have hDN : 4 * D ^ 2 < (N : Real) :=
    lt_of_le_of_lt
      (le_trans (le_max_right 4 (4 * D ^ 2))
        (le_max_right (k : Real) _))
      hN
  have hNpR : (N : Real) < (p : Real) := by
    exact_mod_cast hNp
  have hkp : k < p := by
    exact_mod_cast hkN.trans hNpR
  have hpFour : (4 : Real) < (p : Real) :=
    hfourN.trans hNpR
  have hpD : 4 * D ^ 2 < (p : Real) :=
    hDN.trans hNpR
  have htwoD : 0 ≤ 2 * D := mul_nonneg (by norm_num) hD
  have hsquare :
      (2 * D) ^ 2 < (p : Real) := by
    nlinarith [sq_nonneg D]
  have hsqrt :
      2 * D < Real.sqrt (p : Real) := by
    have hs :=
      Real.sqrt_lt_sqrt (sq_nonneg (2 * D)) hsquare
    simpa [Real.sqrt_sq htwoD] using hs
  have hsqrtPos :
      0 < Real.sqrt (p : Real) := by positivity
  have hsqrtMul :=
    mul_lt_mul_of_pos_right hsqrt hsqrtPos
  have hsqrtSq :
      Real.sqrt (p : Real) *
          Real.sqrt (p : Real) = (p : Real) :=
    Real.mul_self_sqrt (by positivity)
  rw [mul_assoc, hsqrtSq] at hsqrtMul
  have hnum :
      D * Real.sqrt (p : Real) <
        (p : Real) - 1 := by
    nlinarith
  have hden :
      0 < (p : Real) - 1 := by linarith
  refine ⟨h, hkp, ?_⟩
  exact (div_lt_one hden).mpr hnum

/-- The coefficient in (3.1) is bounded by a constant times
`√h/(h-1)`. -/
theorem hubCapacityCoefficient_le_sqrt_bound
    (Csv : Real) (hCsv : 0 ≤ Csv)
    (v k : Nat) (hv : 1 ≤ v)
    (h : Prime) (hh : 3 ≤ h.1) :
    hubCapacityCoefficient Csv v k h ≤
      (2 * Csv * (v : Real) * Real.sqrt (k : Real)) *
        Real.sqrt (h.1 : Real) /
          ((h.1 : Real) - 1) := by
  have hδpos : 0 < controllerDensity h :=
    controllerDensity_pos h
  have hδle : controllerDensity h ≤ 1 :=
    (controllerDensity_lt_one h hh).le
  have hvR : (1 : Real) ≤ (v : Real) := by
    exact_mod_cast hv
  have hvpow :
      (v : Real) ^ controllerDensity h ≤ (v : Real) :=
    Real.rpow_le_self_of_one_le hvR hδle
  have hA :
      paperA (controllerDensity h) ≤
        controllerDensity h :=
    (paperA_controllerDensity_lt_density h).le
  have hAnonneg :
      0 ≤ paperA (controllerDensity h) :=
    (paperA_controllerDensity_pos h).le
  unfold hubCapacityCoefficient
  calc
    2 * Csv *
          (v : Real) ^ controllerDensity h *
          Real.sqrt (↑(k * h.1)) *
          paperA (controllerDensity h) ≤
        2 * Csv * (v : Real) *
          Real.sqrt (↑(k * h.1)) *
          controllerDensity h := by
      gcongr
    _ =
        (2 * Csv * (v : Real) * Real.sqrt (k : Real)) *
          Real.sqrt (h.1 : Real) /
            ((h.1 : Real) - 1) := by
      rw [controllerDensity]
      rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
      ring

/--
The hub-capacity choice can be made above an arbitrary natural threshold.
This strengthened form is what lets us impose the integral-scale condition
`256 * k ≤ h` after the analytic coefficient has already been fixed.
-/
theorem exists_hub_prime_capacity_above
    (Csv : Real) (hCsv : 0 ≤ Csv)
    (v k : Nat) (hv : 1 ≤ v) (hk : 3 ≤ k)
    (N : Nat) :
    ∃ h : Prime,
      N < h.1 ∧
        k < h.1 ∧
        hubCapacityCoefficient Csv v k h < 1 := by
  let D : Real :=
    2 * Csv * (v : Real) * Real.sqrt (k : Real)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  obtain ⟨h, hlarge, hratio⟩ :=
    exists_prime_sqrt_div_sub_one_lt D hD (max N k)
  have hNh : N < h.1 :=
    (le_max_left N k).trans_lt hlarge
  have hkh : k < h.1 :=
    (le_max_right N k).trans_lt hlarge
  have hh : 3 ≤ h.1 := by omega
  refine ⟨h, hNh, hkh, ?_⟩
  exact
    (hubCapacityCoefficient_le_sqrt_bound
      Csv hCsv v k hv h hh).trans_lt hratio

/--
Formal version of the hub choice in (3.1): for fixed `Csv`, `v`, and `k`,
there is a prime `h > k` with strict capacity coefficient below one.
-/
theorem exists_hub_prime_capacity
    (Csv : Real) (hCsv : 0 ≤ Csv)
    (v k : Nat) (hv : 1 ≤ v) (hk : 3 ≤ k) :
    ∃ h : Prime,
      k < h.1 ∧
        hubCapacityCoefficient Csv v k h < 1 := by
  obtain ⟨h, _hk, hkh, hcap⟩ :=
    exists_hub_prime_capacity_above
      Csv hCsv v k hv hk k
  exact ⟨h, hkh, hcap⟩

end Erdos279
