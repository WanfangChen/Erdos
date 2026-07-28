import Mathlib.Analysis.PSeries

/-!
# Divergence of the logarithmic harmonic series

The fixed-progression PNT will be converted to reciprocal divergence by
comparing the reciprocal of the `n`th prime with
`1 / ((n+2) log (n+2))`.  This file supplies the required elementary
divergence theorem using mathlib's Cauchy condensation test.
-/

namespace Erdos279

/-- A harmlessly regularized version of `1 / (n log n)`. -/
noncomputable def logHarmonicTerm (n : Nat) : Real :=
  if n < 2 then
    1 / ((2 : Real) * Real.log 2)
  else
    1 / ((n : Real) * Real.log (n : Real))

theorem logHarmonicTerm_nonneg (n : Nat) :
    0 ≤ logHarmonicTerm n := by
  unfold logHarmonicTerm
  split_ifs
  · positivity
  · positivity

theorem logHarmonicTerm_antitone :
    ∀ ⦃m n : Nat⦄,
      0 < m → m ≤ n →
        logHarmonicTerm n ≤ logHarmonicTerm m := by
  intro m n hm hmn
  by_cases hn : n < 2
  · have hm' : m < 2 := lt_of_le_of_lt hmn hn
    simp [logHarmonicTerm, hn, hm']
  · have hn2 : 2 ≤ n := by omega
    by_cases hm2 : m < 2
    · have hm1 : m = 1 := by omega
      subst m
      simp only [logHarmonicTerm, Nat.one_lt_ofNat,
        ↓reduceIte, hn, one_div]
      have hdenN :
          0 < (n : Real) * Real.log (n : Real) := by
        have hnR : (1 : Real) < (n : Real) := by
          exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn2)
        exact mul_pos (by positivity) (Real.log_pos hnR)
      exact (inv_le_inv₀ hdenN (by positivity)).2 (by
        have hlog :
            Real.log (2 : Real) ≤
              Real.log (n : Real) := by
          exact Real.log_le_log (by positivity) (by
            exact_mod_cast hn2)
        have hlog2 : 0 ≤ Real.log (2 : Real) :=
          (Real.log_pos (by norm_num)).le
        have hnR : (2 : Real) ≤ (n : Real) := by
          exact_mod_cast hn2
        nlinarith [mul_le_mul hnR hlog hlog2
          (by positivity : 0 ≤ (n : Real))])
    · have hm2' : 2 ≤ m := by omega
      simp only [logHarmonicTerm, hn, hm2, ↓reduceIte,
        one_div]
      have hmR : (1 : Real) < (m : Real) := by
          exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hm2')
      have hnR : (1 : Real) < (n : Real) := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hn2)
      exact
        (inv_le_inv₀
          (mul_pos (by positivity) (Real.log_pos hnR))
          (mul_pos (by positivity) (Real.log_pos hmR))).2 (by
        have hcast : (m : Real) ≤ (n : Real) := by
          exact_mod_cast hmn
        have hlog :
            Real.log (m : Real) ≤
              Real.log (n : Real) :=
          Real.log_le_log (by
            exact_mod_cast hm) hcast
        have hlogm : 0 ≤ Real.log (m : Real) :=
          (Real.log_pos (by
            exact_mod_cast (lt_of_lt_of_le
              (by omega : 1 < 2) hm2'))).le
        exact mul_le_mul hcast hlog hlogm (by positivity))

/-- Exact value of the positive-index condensed terms. -/
theorem log_mul_condensedLogHarmonic_succ
    (k : Nat) :
    Real.log (2 : Real) *
        ((2 : Real) ^ (k + 1) *
          logHarmonicTerm (2 ^ (k + 1))) =
      1 / ((k + 1 : Nat) : Real) := by
  have hpow2 :
      ¬ 2 ^ (k + 1) < (2 : Nat) := by
    have : 2 ≤ 2 ^ (k + 1) := by
      simpa [pow_succ] using
        Nat.pow_le_pow_right (by omega : 1 ≤ 2)
          (by omega : 1 ≤ k + 1)
    omega
  have hlog2 : Real.log (2 : Real) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  unfold logHarmonicTerm
  rw [if_neg hpow2]
  push_cast
  rw [Real.log_pow]
  field_simp [hlog2]
  simp [Nat.cast_add]

/-- The ordinary harmonic series remains divergent after deleting its
zeroth term. -/
theorem not_summable_one_div_natCast_succ :
    ¬ Summable
      (fun k : Nat =>
        1 / ((k + 1 : Nat) : Real)) := by
  exact
    mt
      (summable_nat_add_iff
        (f := fun n : Nat => 1 / (n : Real)) 1).1
      Real.not_summable_one_div_natCast

set_option maxHeartbeats 500000 in
/-- The Cauchy-condensed logarithmic harmonic series diverges. -/
theorem not_summable_condensedLogHarmonic :
    ¬ Summable
      (fun k : Nat =>
        (2 : Real) ^ k *
          logHarmonicTerm (2 ^ k)) := by
  intro hsum
  have htail :
      Summable
        (fun k : Nat =>
          (2 : Real) ^ (k + 1) *
            logHarmonicTerm (2 ^ (k + 1))) :=
    (summable_nat_add_iff
      (f := fun k : Nat =>
        (2 : Real) ^ k *
          logHarmonicTerm (2 ^ k)) 1).2 hsum
  have hscaled :=
    htail.mul_left (Real.log (2 : Real))
  have heq :
      (fun k : Nat =>
        Real.log (2 : Real) *
          ((2 : Real) ^ (k + 1) *
            logHarmonicTerm (2 ^ (k + 1)))) =
        (fun k : Nat =>
          1 / ((k + 1 : Nat) : Real)) :=
    funext log_mul_condensedLogHarmonic_succ
  have hharmonic :
      Summable
        (fun k : Nat =>
          1 / ((k + 1 : Nat) : Real)) := by
    rw [← heq]
    exact hscaled
  exact not_summable_one_div_natCast_succ hharmonic

/-- The regularized logarithmic harmonic series diverges. -/
theorem not_summable_logHarmonicTerm :
    ¬ Summable logHarmonicTerm := by
  intro hregularized
  exact not_summable_condensedLogHarmonic
    ((summable_condensed_iff_of_nonneg
      logHarmonicTerm_nonneg
      logHarmonicTerm_antitone).2
      hregularized)

/-- Removing the first two terms does not restore convergence. -/
theorem not_summable_logHarmonicTerm_add_two :
    ¬ Summable
      (fun n : Nat => logHarmonicTerm (n + 2)) := by
  intro h
  exact not_summable_logHarmonicTerm
    ((summable_nat_add_iff
      (f := logHarmonicTerm) 2).1 h)

end Erdos279
