import Erdos279.UniformHardSieve
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Aggregating uniform main-layer bounds

The analytic sieve is naturally proved one `h`-adic layer at a time,
at the local scale `X / h^e`.  This file converts such bounds into the
single stage estimate needed by the recursive construction.

The conversion is deliberately coarse but completely uniform in `e`.
For every main exponent, the shifted prime-counting scales satisfy

`primeCountingScale (X / h^e) ≤ 4 h⁻ᵉ primeCountingScale X`.

The sum of `h⁻ᵉ` over all positive exponents is exactly `1 / (h - 1)`,
which is `controllerDensity h`.
-/

namespace Erdos279

open Filter Finset

/-- A finite sum of positive powers of `h⁻¹`, indexed only by positive
exponents, is bounded by the full geometric tail `1 / (h - 1)`. -/
theorem sum_inv_prime_powers_le_controllerDensity
    (h : Prime) (s : Finset Nat)
    (hs : ∀ e ∈ s, 1 ≤ e) :
    (∑ e ∈ s, (((h.1 ^ e : Nat) : Real)⁻¹)) ≤
      controllerDensity h := by
  let r : Real := ((h.1 : Real)⁻¹)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast h.one_lt)
  have hzero : 0 ∉ s := by
    intro h0
    have := hs 0 h0
    omega
  have hsum :=
    (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum
      (insert 0 s) (fun _ _ => pow_nonneg hr0 _)
  rw [tsum_geometric_of_lt_one hr0 hr1] at hsum
  simp only [sum_insert hzero, pow_zero] at hsum
  have hreindex :
      (∑ e ∈ s, (((h.1 ^ e : Nat) : Real)⁻¹)) =
        ∑ e ∈ s, r ^ e := by
    apply sum_congr rfl
    intro e he
    dsimp [r]
    push_cast
    rw [inv_pow]
  rw [hreindex]
  have hhpos : (0 : Real) < (h.1 : Real) := by
    exact_mod_cast h.pos
  have hhne : (h.1 : Real) ≠ 0 := hhpos.ne'
  have hden : (h.1 : Real) - 1 ≠ 0 := by
    have : (1 : Real) < (h.1 : Real) := by
      exact_mod_cast h.one_lt
    linarith
  calc
    ∑ e ∈ s, r ^ e ≤ (1 - r)⁻¹ - 1 := by
      linarith
    _ = controllerDensity h := by
      rw [controllerDensity]
      dsimp [r]
      field_simp [hhne, hden]
      ring

/-- Main exponents are positive, as required by the geometric tail. -/
theorem one_le_of_mem_hardMainExponentRange
    {h : Prime} {X Z e : Nat}
    (he : e ∈ hardMainExponentRange h X Z) :
    1 ≤ e := by
  exact (Finset.mem_Icc.mp
    (Finset.mem_filter.mp he).1).1

/-- On a main layer the natural quotient is large enough to force the
denominator `h^e` below `X/2`, once `X ≥ 4`. -/
theorem twice_prime_power_le_of_mem_hardMainExponentRange
    {h : Prime} {X Z e : Nat}
    (hX : 4 ≤ X)
    (he : e ∈ hardMainExponentRange h X Z) :
    2 * h.1 ^ e ≤ X := by
  have hmain :
      Nat.sqrt X ≤ X / h.1 ^ e :=
    (Finset.mem_filter.mp he).2
  have hsqrt : 2 ≤ Nat.sqrt X := by
    rw [Nat.le_sqrt]
    omega
  have hpowpos : 0 < h.1 ^ e := Nat.pow_pos h.pos
  have hmul :
      Nat.sqrt X * h.1 ^ e ≤ X :=
    (Nat.le_div_iff_mul_le hpowpos).1 hmain
  exact (Nat.mul_le_mul_right (h.1 ^ e) hsqrt).trans hmul

/-- The value part of the shifted prime-counting scale loses at most
`2 h⁻ᵉ` on every main layer. -/
theorem shifted_value_ratio_le_twice_inv_prime_power
    {h : Prime} {X Z e : Nat}
    (hX : 4 ≤ X)
    (he : e ∈ hardMainExponentRange h X Z) :
    (((X / h.1 ^ e + 2 : Nat) : Real) /
        ((X + 2 : Nat) : Real)) ≤
      2 * (((h.1 ^ e : Nat) : Real)⁻¹) := by
  have hpowposN : 0 < h.1 ^ e := Nat.pow_pos h.pos
  have hpowposR : (0 : Real) < ((h.1 ^ e : Nat) : Real) := by
    exact_mod_cast hpowposN
  have hXposR : (0 : Real) < ((X + 2 : Nat) : Real) := by
    positivity
  have hdivmul :
      h.1 ^ e * (X / h.1 ^ e) ≤ X := by
    simpa [Nat.mul_comm] using
      Nat.div_mul_le_self X (h.1 ^ e)
  have htwice :
      2 * h.1 ^ e ≤ X :=
    twice_prime_power_le_of_mem_hardMainExponentRange hX he
  have hNat :
      h.1 ^ e * (X / h.1 ^ e + 2) ≤
        2 * (X + 2) := by
    calc
      h.1 ^ e * (X / h.1 ^ e + 2) =
          h.1 ^ e * (X / h.1 ^ e) +
            2 * h.1 ^ e := by
              simp only [Nat.mul_add]
              omega
      _ ≤ X + X := Nat.add_le_add hdivmul htwice
      _ ≤ 2 * (X + 2) := by omega
  have hReal :
      ((h.1 ^ e : Nat) : Real) *
          ((X / h.1 ^ e + 2 : Nat) : Real) ≤
        2 * ((X + 2 : Nat) : Real) := by
    exact_mod_cast hNat
  rw [div_le_iff₀ hXposR]
  calc
    ((X / h.1 ^ e + 2 : Nat) : Real) ≤
        (2 * ((X + 2 : Nat) : Real)) /
          ((h.1 ^ e : Nat) : Real) := by
      apply (le_div_iff₀ hpowposR).2
      nlinarith
    _ =
        2 * (((h.1 ^ e : Nat) : Real)⁻¹) *
          ((X + 2 : Nat) : Real) := by
      rw [inv_eq_one_div]
      field_simp [hpowposR.ne']

/-- The logarithmic part of the shifted scale loses at most a factor two
on every main layer. -/
theorem shifted_log_ratio_le_two_of_mem_hardMainExponentRange
    {h : Prime} {X Z e : Nat}
    (he : e ∈ hardMainExponentRange h X Z) :
    Real.log ((X + 2 : Nat) : Real) /
        Real.log ((X / h.1 ^ e + 2 : Nat) : Real) ≤
      2 := by
  let Y := X / h.1 ^ e
  have hmain : Nat.sqrt X ≤ Y := by
    simpa [Y] using (Finset.mem_filter.mp he).2
  have hsqrt :
      X < (Nat.sqrt X + 1) ^ 2 :=
    by
      simpa [pow_two, Nat.succ_eq_add_one] using
        Nat.lt_succ_sqrt X
  have hsquare :
      X + 2 ≤ (Y + 2) ^ 2 := by
    nlinarith
  have hcast :
      ((X + 2 : Nat) : Real) ≤
        (((Y + 2 : Nat) : Real) ^ 2) := by
    exact_mod_cast hsquare
  have hpositive :
      (0 : Real) < ((X + 2 : Nat) : Real) := by
    positivity
  have hlogLe :
      Real.log ((X + 2 : Nat) : Real) ≤
        Real.log (((Y + 2 : Nat) : Real) ^ 2) :=
    Real.log_le_log hpositive hcast
  rw [Real.log_pow] at hlogLe
  have hden :
      0 < Real.log ((Y + 2 : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < Y + 2)
  apply (div_le_iff₀ hden).2
  simpa only [Nat.cast_ofNat] using hlogLe

/-- Uniform comparison of the shifted prime-counting scales on every main
`h`-adic layer. -/
theorem primeCountingScale_div_le_four_inv_prime_power
    {h : Prime} {X Z e : Nat}
    (hX : 4 ≤ X)
    (he : e ∈ hardMainExponentRange h X Z) :
    primeCountingScale (X / h.1 ^ e) /
        primeCountingScale X ≤
      4 * (((h.1 ^ e : Nat) : Real)⁻¹) := by
  have hValue :=
    shifted_value_ratio_le_twice_inv_prime_power hX he
  have hLog :=
    shifted_log_ratio_le_two_of_mem_hardMainExponentRange he
  have hValueNonneg :
      0 ≤
        (((X / h.1 ^ e + 2 : Nat) : Real) /
          ((X + 2 : Nat) : Real)) := by
    positivity
  push_cast at hValue hLog hValueNonneg
  have hLogNumeratorPos :
      0 < Real.log ((X : Real) + 2) := by
    apply Real.log_pos
    have hXnonneg : (0 : Real) ≤ X := by positivity
    linarith
  have hLogDenominatorPos :
      0 <
        Real.log (((X / h.1 ^ e : Nat) : Real) + 2) := by
    apply Real.log_pos
    have hYnonneg :
        (0 : Real) ≤ (X / h.1 ^ e : Nat) := by
      positivity
    linarith
  have hLogNonneg :
      0 ≤
        Real.log ((X : Real) + 2) /
          Real.log (((X / h.1 ^ e : Nat) : Real) + 2) := by
    exact (div_pos hLogNumeratorPos hLogDenominatorPos).le
  have hmul :=
    mul_le_mul hValue hLog
      hLogNonneg
      (by positivity)
  unfold primeCountingScale
  push_cast
  have hlogX :
      Real.log ((X : Real) + 2) ≠ 0 := by
    exact hLogNumeratorPos.ne'
  have hlogY :
      Real.log (((X / h.1 ^ e : Nat) : Real) + 2) ≠ 0 := by
    exact hLogDenominatorPos.ne'
  have hXtwo : (X : Real) + 2 ≠ 0 := by positivity
  have hYtwo :
      ((X / h.1 ^ e : Nat) : Real) + 2 ≠ 0 := by
    positivity
  calc
    ((((X / h.1 ^ e : Nat) : Real) + 2) /
          Real.log (((X / h.1 ^ e : Nat) : Real) + 2) /
        (((X : Real) + 2) / Real.log ((X : Real) + 2))) =
        ((((X / h.1 ^ e : Nat) : Real) + 2) /
          ((X : Real) + 2)) *
        (Real.log ((X : Real) + 2) /
          Real.log (((X / h.1 ^ e : Nat) : Real) + 2)) := by
      field_simp [hlogX, hlogY, hXtwo, hYtwo]
    _ ≤
        (2 * (((h.1 : Real) ^ e)⁻¹)) * 2 :=
      hmul
    _ = 4 * (((h.1 : Real) ^ e)⁻¹) := by ring

/-- A genuinely uniform one-layer upper bound, stated at the layer's own
local prime-counting scale. -/
def HasUniformMainLayerUpperBound
    (h : Prime) (v B : Nat) (coefficient : Real) : Prop :=
  ∀ ε : Real, 0 < ε →
    ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h (stageOldPrimeCutoff v X),
        ∀ e ∈ hardMainExponentRange h X (B * X),
          ((hardLayerUnits h (stageOldPrimeCutoff v X) e a
              (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Real) /
              primeCountingScale (X / h.1 ^ e) ≤
            coefficient + ε

/-- Summing a uniform local layer estimate gives the required uniform
main-stage estimate.  The harmless factor four comes solely from the
shifted scale comparison above. -/
theorem HasUniformMainLayerUpperBound.toMainHardStageUpperBound
    {h : Prime} {v B : Nat} {coefficient : Real}
    (hLayer : HasUniformMainLayerUpperBound h v B coefficient)
    (hcoefficient : 0 ≤ coefficient) :
    HasUniformMainHardStageUpperBound h v B
      (4 * coefficient * controllerDensity h) := by
  intro ε hε
  have hδ : 0 < controllerDensity h := controllerDensity_pos h
  let η : Real := ε / (4 * controllerDensity h)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hLayerEventually := hLayer η hη
  filter_upwards [hLayerEventually, eventually_ge_atTop 4] with X hLX hX
  intro a
  have hTerm :
      ∀ e ∈ hardMainExponentRange h X (B * X),
        ((hardLayerUnits h (stageOldPrimeCutoff v X) e a
            (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Real) ≤
          (coefficient + η) *
            (4 * (((h.1 ^ e : Nat) : Real)⁻¹) *
              primeCountingScale X) := by
    intro e he
    have hLocal :=
      (div_le_iff₀
        (primeCountingScale_pos (X / h.1 ^ e))).1
        (hLX a e he)
    have hScaleRatio :=
      primeCountingScale_div_le_four_inv_prime_power
        hX he
    have hScale :
        primeCountingScale (X / h.1 ^ e) ≤
          4 * (((h.1 ^ e : Nat) : Real)⁻¹) *
            primeCountingScale X := by
      exact
        (div_le_iff₀ (primeCountingScale_pos X)).1
          hScaleRatio
    exact hLocal.trans
      (mul_le_mul_of_nonneg_left hScale
        (add_nonneg hcoefficient hη.le))
  have hSum :=
    Finset.sum_le_sum hTerm
  have hGeom :
      (∑ e ∈ hardMainExponentRange h X (B * X),
          (((h.1 ^ e : Nat) : Real)⁻¹)) ≤
        controllerDensity h :=
    sum_inv_prime_powers_le_controllerDensity
      h _ (fun e he =>
        one_le_of_mem_hardMainExponentRange he)
  have hScalePos : 0 < primeCountingScale X :=
    primeCountingScale_pos X
  unfold uniformMainHardStageCount
  push_cast
  rw [div_le_iff₀ hScalePos]
  calc
    ∑ e ∈ hardMainExponentRange h X (B * X),
        ((hardLayerUnits h (stageOldPrimeCutoff v X) e a
          (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Real) ≤
      ∑ e ∈ hardMainExponentRange h X (B * X),
        (coefficient + η) *
          (4 * (((h.1 ^ e : Nat) : Real)⁻¹) *
            primeCountingScale X) := hSum
    _ =
      (4 * (coefficient + η) * primeCountingScale X) *
        (∑ e ∈ hardMainExponentRange h X (B * X),
          (((h.1 ^ e : Nat) : Real)⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ ≤
      (4 * (coefficient + η) * primeCountingScale X) *
        controllerDensity h := by
      gcongr
    _ =
      (4 * coefficient * controllerDensity h + ε) *
        primeCountingScale X := by
      dsimp [η]
      field_simp [hδ.ne']

end Erdos279
