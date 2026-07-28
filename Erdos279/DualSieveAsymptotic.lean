import Erdos279.DualResidueSieve
import Erdos279.UniformMainLayerAggregation
import Erdos279.DynamicScaleGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform asymptotics for the two-shift sieve

We use the fixed sieve exponent `64`.  This generous exponent makes the
explicit Selberg rounding error elementary: its normalized contribution is
bounded by `32 / floor(X^(1/16))`.
-/

namespace Erdos279

open Filter

/-- A fixed positive integral root tends to infinity. -/
theorem nat_nthRoot_tendsto_atTop
    (v : Nat) (hv : 0 < v) :
    Tendsto (Nat.nthRoot v) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  refine ⟨K ^ v, ?_⟩
  intro X hX
  exact (Nat.le_nthRoot_iff hv.ne').2 hX

/-- The real cast of a fixed positive integral root also tends to
infinity. -/
theorem natCast_nthRoot_tendsto_atTop
    (v : Nat) (hv : 0 < v) :
    Tendsto (fun X : Nat => (Nat.nthRoot v X : Real))
      atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (nat_nthRoot_tendsto_atTop v hv)

/-- The explicit two-sieve remainder at the fixed exponent `64`. -/
noncomputable def dualSieveError (X : Nat) : Real :=
  let z := Nat.nthRoot 64 X
  2 * (z : Real) * (1 + Real.log (z : Real)) ^ 3

theorem nthRoot64_pow_four_le_nthRoot16 (X : Nat) :
    Nat.nthRoot 64 X ^ 4 ≤ Nat.nthRoot 16 X := by
  rw [Nat.le_nthRoot_iff (by norm_num : (16 : Nat) ≠ 0)]
  rw [← pow_mul]
  norm_num

theorem nthRoot16_pow_two_le_nthRoot8 (X : Nat) :
    Nat.nthRoot 16 X ^ 2 ≤ Nat.nthRoot 8 X := by
  rw [Nat.le_nthRoot_iff (by norm_num : (8 : Nat) ≠ 0)]
  rw [← pow_mul]
  norm_num

theorem nthRoot8_pow_two_le_nthRoot4 (X : Nat) :
    Nat.nthRoot 8 X ^ 2 ≤ Nat.nthRoot 4 X := by
  rw [Nat.le_nthRoot_iff (by norm_num : (4 : Nat) ≠ 0)]
  rw [← pow_mul]
  norm_num

theorem nthRoot16_pow_four_le_sqrt (X : Nat) :
    Nat.nthRoot 16 X ^ 4 ≤ Nat.sqrt X := by
  calc
    Nat.nthRoot 16 X ^ 4 =
        (Nat.nthRoot 16 X ^ 2) ^ 2 := by ring
    _ ≤ Nat.nthRoot 8 X ^ 2 :=
      pow_le_pow_left₀ (Nat.zero_le _)
        (nthRoot16_pow_two_le_nthRoot8 X) 2
    _ ≤ Nat.nthRoot 4 X :=
      nthRoot8_pow_two_le_nthRoot4 X
    _ ≤ Nat.sqrt X :=
      nthRoot_le_sqrt (by norm_num : 2 ≤ (4 : Nat))

/-- On every main layer, the explicit Selberg error is bounded by a
quantity depending only on the ambient scale and tending to zero. -/
theorem dualSieveError_div_primeCountingScale_le
    {X Y : Nat}
    (hX : 1 ≤ X)
    (hmain : Nat.sqrt X ≤ Y) :
    dualSieveError X / primeCountingScale Y ≤
      32 / (Nat.nthRoot 16 X : Real) := by
  let z := Nat.nthRoot 64 X
  let r := Nat.nthRoot 16 X
  have hzOne : 1 ≤ z := by
    dsimp [z]
    rw [Nat.le_nthRoot_iff (by norm_num : (64 : Nat) ≠ 0)]
    simpa using hX
  have hrOne : 1 ≤ r := by
    dsimp [r]
    rw [Nat.le_nthRoot_iff (by norm_num : (16 : Nat) ≠ 0)]
    simpa using hX
  have hzNonneg : (0 : Real) ≤ (z : Real) := by positivity
  have hlogzNonneg : 0 ≤ Real.log (z : Real) := by
    exact Real.log_nonneg (by exact_mod_cast hzOne)
  have hlogzLe : Real.log (z : Real) ≤ (z : Real) :=
    Real.log_le_self hzNonneg
  have honeLogLe :
      1 + Real.log (z : Real) ≤ 2 * (z : Real) := by
    have hzOneReal : (1 : Real) ≤ (z : Real) := by
      exact_mod_cast hzOne
    linarith
  have herror :
      dualSieveError X ≤ 16 * (r : Real) := by
    have hpow :
        (1 + Real.log (z : Real)) ^ 3 ≤
          (2 * (z : Real)) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) honeLogLe 3
    have hz4r :
        ((z : Real) ^ 4) ≤ (r : Real) := by
      exact_mod_cast nthRoot64_pow_four_le_nthRoot16 X
    dsimp [dualSieveError, z]
    calc
      2 * (z : Real) *
            (1 + Real.log (z : Real)) ^ 3 ≤
          2 * (z : Real) * (2 * (z : Real)) ^ 3 := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 16 * (z : Real) ^ 4 := by ring
      _ ≤ 16 * (r : Real) :=
        mul_le_mul_of_nonneg_left hz4r (by norm_num)
  have hr4Y : r ^ 4 ≤ Y := by
    exact (nthRoot16_pow_four_le_sqrt X).trans hmain
  have hrSqSqrt :
      ((r : Real) ^ 2) ≤
        Real.sqrt ((Y + 2 : Nat) : Real) := by
    apply (Real.le_sqrt' (by positivity)).2
    have hcast : ((r ^ 4 : Nat) : Real) ≤ (Y : Real) := by
      exact_mod_cast hr4Y
    calc
      ((r : Real) ^ 2) ^ 2 =
          ((r ^ 4 : Nat) : Real) := by
        push_cast
        ring
      _ ≤ (Y : Real) := hcast
      _ ≤ ((Y + 2 : Nat) : Real) := by
        exact_mod_cast (Nat.le_add_right Y 2)
  have hlogUpper :
      Real.log ((Y + 2 : Nat) : Real) ≤
        2 * Real.sqrt ((Y + 2 : Nat) : Real) := by
    have h :=
      Real.log_le_rpow_div
        (show (0 : Real) ≤ ((Y + 2 : Nat) : Real) by positivity)
        (show (0 : Real) < (1 / 2 : Real) by norm_num)
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using h
  have hlogPos :
      0 < Real.log ((Y + 2 : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < Y + 2)
  have hsqrtSq :
      Real.sqrt ((Y + 2 : Nat) : Real) ^ 2 =
        ((Y + 2 : Nat) : Real) :=
    Real.sq_sqrt (by positivity)
  have hscale :
      (r : Real) ^ 2 / 2 ≤ primeCountingScale Y := by
    unfold primeCountingScale
    apply (le_div_iff₀ hlogPos).2
    calc
      (r : Real) ^ 2 / 2 *
            Real.log ((Y + 2 : Nat) : Real) ≤
          (r : Real) ^ 2 / 2 *
            (2 * Real.sqrt ((Y + 2 : Nat) : Real)) := by
        exact mul_le_mul_of_nonneg_left hlogUpper (by positivity)
      _ = (r : Real) ^ 2 *
            Real.sqrt ((Y + 2 : Nat) : Real) := by ring
      _ ≤ Real.sqrt ((Y + 2 : Nat) : Real) *
            Real.sqrt ((Y + 2 : Nat) : Real) := by
        exact mul_le_mul_of_nonneg_right hrSqSqrt (Real.sqrt_nonneg _)
      _ = ((Y + 2 : Nat) : Real) := by
        nlinarith
  have hrPos : (0 : Real) < (r : Real) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hrOne)
  calc
    dualSieveError X / primeCountingScale Y ≤
        (16 * (r : Real)) / ((r : Real) ^ 2 / 2) := by
      exact div_le_div₀ (by positivity) herror
        (by positivity) hscale
    _ = 32 / (r : Real) := by
      field_simp [hrPos.ne']
      ring

/-- Uniform `o(1)` form of the rounding error over all main-layer local
scales. -/
theorem dualSieveError_normalized_eventually_lt
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ X : Nat in atTop,
      ∀ Y : Nat, Nat.sqrt X ≤ Y →
        dualSieveError X / primeCountingScale Y < ε := by
  have hmajor :
      Tendsto
        (fun X : Nat => 32 / (Nat.nthRoot 16 X : Real))
        atTop (nhds 0) :=
    (natCast_nthRoot_tendsto_atTop 16 (by norm_num)).const_div_atTop 32
  have hmajorEventually := hmajor.eventually_lt_const hε
  filter_upwards [eventually_ge_atTop (1 : Nat),
    hmajorEventually] with X hX hmajorX
  intro Y hmain
  exact (dualSieveError_div_primeCountingScale_le hX hmain).trans_lt
    hmajorX

/-- A convenient upper bound for multiplying before natural division. -/
theorem mul_div_le_mul_div_add_one
    (B X d : Nat) (hd : 0 < d) :
    (B * X) / d ≤ B * (X / d + 1) := by
  by_cases hB : B = 0
  · simp [hB]
  · apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hd).2
    have hXlt : X < d * (X / d + 1) :=
      Nat.lt_mul_div_succ X hd
    calc
      B * X < B * (d * (X / d + 1)) :=
        Nat.mul_lt_mul_of_pos_left hXlt (Nat.pos_of_ne_zero hB)
      _ = (B * (X / d + 1)) * d := by ring
      _ < (B * (X / d + 1) + 1) * d := by
        exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hd

set_option maxHeartbeats 1000000 in
/-- The logarithm of the local main-layer scale is uniformly controlled by
the logarithm of the `64`-th-root sieve cutoff. -/
theorem mainLayer_log_le_cutoff_log
    {X Y : Nat}
    (hz : 2 ≤ Nat.nthRoot 64 X)
    (hYX : Y ≤ X) :
    Real.log ((Y + 2 : Nat) : Real) ≤
      129 * Real.log (Nat.nthRoot 64 X : Real) := by
  let z := Nat.nthRoot 64 X
  have hroot :
      X < (z + 1) ^ 64 := by
    exact Nat.lt_pow_nthRoot_add_one (by norm_num) X
  have hzOne : 1 ≤ z := hz.trans' (by norm_num)
  have hzplus : z + 1 ≤ 2 * z := by omega
  have hpowMono :
      (z + 1) ^ 64 ≤ (2 * z) ^ 64 :=
    pow_le_pow_left₀ (Nat.zero_le _) hzplus 64
  have hpowTwo : 1 ≤ (z + 1) ^ 64 := by
    have : 0 < (z + 1) ^ 64 := Nat.pow_pos (by omega)
    omega
  have hNat :
      Y + 2 ≤ 2 * (2 * z) ^ 64 := by
    calc
      Y + 2 ≤ X + 2 := Nat.add_le_add_right hYX 2
      _ ≤ (z + 1) ^ 64 + 1 := by omega
      _ ≤ 2 * ((z + 1) ^ 64) := by omega
      _ ≤ 2 * ((2 * z) ^ 64) :=
        Nat.mul_le_mul_left 2 hpowMono
  have hcast :
      ((Y + 2 : Nat) : Real) ≤
        2 * ((2 * z : Nat) : Real) ^ 64 := by
    have hcastRaw :
        ((Y + 2 : Nat) : Real) ≤
          ((2 * (2 * z) ^ 64 : Nat) : Real) :=
      Nat.cast_le.2 hNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hcastRaw
  have hlogLe :
      Real.log ((Y + 2 : Nat) : Real) ≤
        Real.log (2 * ((2 * z : Nat) : Real) ^ 64) :=
    Real.log_le_log
      (by
        exact_mod_cast (show 0 < Y + 2 by omega))
      hcast
  have hzPos : (0 : Real) < (z : Real) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hzOne)
  have htwozPos : (0 : Real) < (2 * z : Nat) := by positivity
  have hlogExpand :
      Real.log (2 * ((2 * z : Nat) : Real) ^ 64) =
        65 * Real.log 2 + 64 * Real.log (z : Real) := by
    push_cast
    rw [Real.log_mul
        (by norm_num : (2 : Real) ≠ 0)
        (pow_ne_zero 64 (by positivity : (2 * (z : Real)) ≠ 0)),
      Real.log_pow,
      Real.log_mul (by norm_num : (2 : Real) ≠ 0) hzPos.ne']
    ring
  have hlogTwoLe :
      Real.log 2 ≤ Real.log (z : Real) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hz
  rw [hlogExpand] at hlogLe
  linarith

/-- Ratio form of the preceding logarithmic estimate. -/
theorem mainLayer_log_ratio_le
    {X Y : Nat}
    (hz : 2 ≤ Nat.nthRoot 64 X)
    (hYX : Y ≤ X) :
    Real.log ((Y + 2 : Nat) : Real) /
        Real.log (Nat.nthRoot 64 X : Real) ≤
      129 := by
  have hlogPos :
      0 < Real.log (Nat.nthRoot 64 X : Real) := by
    apply Real.log_pos
    exact_mod_cast hz
  exact (div_le_iff₀ hlogPos).2
    (by
      simpa [mul_comm] using mainLayer_log_le_cutoff_log hz hYX)

/-- Explicit coefficient supplied by the two-shift sieve on one local
main layer. -/
noncomputable def dualSieveLayerCoefficient
    (h : Prime) (B : Nat) : Real :=
  516 * ((2 * B + 1 : Nat) : Real) / (h.1 : Real)

theorem dualSieveLayerCoefficient_nonneg
    (h : Prime) (B : Nat) :
    0 ≤ dualSieveLayerCoefficient h B := by
  unfold dualSieveLayerCoefficient
  positivity

/-- The unconditional, class-uniform one-layer estimate furnished by the
ordinary two-shift Selberg sieve. -/
theorem hasUniformMainLayerUpperBound_dualSieve
    (h : Prime) (B : Nat) :
    HasUniformMainLayerUpperBound h 64 B
      (dualSieveLayerCoefficient h B) := by
  intro ε hε
  have hzEventually :
      ∀ᶠ X : Nat in atTop, 2 ≤ Nat.nthRoot 64 X :=
    (nat_nthRoot_tendsto_atTop 64 (by norm_num)).eventually_ge_atTop 2
  have hhubEventually :
      ∀ᶠ X : Nat in atTop, h.1 ^ 2 ≤ X :=
    eventually_ge_atTop (h.1 ^ 2)
  have herrorEventually :=
    dualSieveError_normalized_eventually_lt hε
  filter_upwards [hzEventually, hhubEventually,
    herrorEventually] with X hzX hhubX herrorX
  intro a e he
  let d := h.1 ^ e
  let Y := X / d
  let Z := (B * X) / d
  let z := Nat.nthRoot 64 X
  have hdPos : 0 < d := by
    dsimp [d]
    exact Nat.pow_pos h.pos
  have hmain : Nat.sqrt X ≤ Y := by
    simpa [Y, d] using (Finset.mem_filter.mp he).2
  have hYX : Y ≤ X := by
    dsimp [Y]
    exact Nat.div_le_self X d
  have hhubSqrt : h.1 ≤ Nat.sqrt X := by
    exact Nat.le_sqrt'.2 hhubX
  have hhubY : h.1 ≤ Y := hhubSqrt.trans hmain
  have hYOne : 1 ≤ Y := h.one_lt.le.trans hhubY
  have hZ :
      Z ≤ B * (Y + 1) := by
    simpa [Z, Y, d] using
      mul_div_le_mul_div_add_one B X d hdPos
  have hYplus : Y + 1 ≤ 2 * Y := by omega
  have hNmul :
      (Z / h.1 + 1) * h.1 ≤
        (2 * B + 1) * Y := by
    calc
      (Z / h.1 + 1) * h.1 =
          (Z / h.1) * h.1 + h.1 := by ring
      _ ≤ Z + h.1 :=
        Nat.add_le_add (Nat.div_mul_le_self Z h.1) le_rfl
      _ ≤ B * (Y + 1) + Y :=
        Nat.add_le_add hZ hhubY
      _ ≤ B * (2 * Y) + Y :=
        Nat.add_le_add_right (Nat.mul_le_mul_left B hYplus) Y
      _ = (2 * B + 1) * Y := by ring
  have hhPos : (0 : Real) < (h.1 : Real) := by
    exact_mod_cast h.pos
  have hN :
      ((Z / h.1 + 1 : Nat) : Real) ≤
        ((2 * B + 1 : Nat) : Real) * (Y : Real) /
          (h.1 : Real) := by
    apply (le_div_iff₀ hhPos).2
    have hcast :
        (((Z / h.1 + 1) * h.1 : Nat) : Real) ≤
          (((2 * B + 1) * Y : Nat) : Real) :=
      Nat.cast_le.2 hNmul
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hcast
  have hzTwo : 2 ≤ z := by simpa [z] using hzX
  have hlogzPos : 0 < Real.log (z : Real) := by
    apply Real.log_pos
    exact_mod_cast hzTwo
  have hlogYPos :
      0 < Real.log ((Y + 2 : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < Y + 2)
  have hvalueRatio :
      (Y : Real) / ((Y + 2 : Nat) : Real) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    exact_mod_cast (Nat.le_add_right Y 2)
  have hlocalMain :
      (4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log z) /
          primeCountingScale Y ≤
        dualSieveLayerCoefficient h B := by
    have hA :
        4 * ((Z / h.1 + 1 : Nat) : Real) /
            ((Y + 2 : Nat) : Real) ≤
          4 * ((2 * B + 1 : Nat) : Real) /
            (h.1 : Real) := by
      calc
        4 * ((Z / h.1 + 1 : Nat) : Real) /
              ((Y + 2 : Nat) : Real) ≤
            4 *
                (((2 * B + 1 : Nat) : Real) * (Y : Real) /
                  (h.1 : Real)) /
              ((Y + 2 : Nat) : Real) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hN (by norm_num))
            (by positivity)
        _ =
            (4 * ((2 * B + 1 : Nat) : Real) / (h.1 : Real)) *
              ((Y : Real) / ((Y + 2 : Nat) : Real)) := by ring
        _ ≤
            4 * ((2 * B + 1 : Nat) : Real) /
              (h.1 : Real) := by
          exact mul_le_of_le_one_right
            (by positivity) hvalueRatio
    have hL :
        Real.log ((Y + 2 : Nat) : Real) /
            Real.log z ≤ 129 := by
      simpa [z] using mainLayer_log_ratio_le hzX hYX
    have hLNonneg :
        0 ≤ Real.log ((Y + 2 : Nat) : Real) /
            Real.log z :=
      (div_pos hlogYPos hlogzPos).le
    unfold primeCountingScale dualSieveLayerCoefficient
    have hYtwoNe : ((Y + 2 : Nat) : Real) ≠ 0 := by positivity
    have hlogYNe : Real.log ((Y + 2 : Nat) : Real) ≠ 0 :=
      hlogYPos.ne'
    have hlogzNe : Real.log (z : Real) ≠ 0 :=
      hlogzPos.ne'
    calc
      (4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log (z : Real)) /
            (((Y + 2 : Nat) : Real) /
              Real.log ((Y + 2 : Nat) : Real)) =
          (4 * ((Z / h.1 + 1 : Nat) : Real) /
            ((Y + 2 : Nat) : Real)) *
            (Real.log ((Y + 2 : Nat) : Real) /
              Real.log (z : Real)) := by
        field_simp [hYtwoNe, hlogYNe, hlogzNe]
      _ ≤
          (4 * ((2 * B + 1 : Nat) : Real) / (h.1 : Real)) *
            129 :=
        mul_le_mul hA hL hLNonneg (by positivity)
      _ =
          516 * ((2 * B + 1 : Nat) : Real) / (h.1 : Real) := by
        ring
  have herror :
      dualSieveError X / primeCountingScale Y < ε :=
    herrorX Y hmain
  have hlayer :=
    hardLayerUnits_card_real_le_simpler
      h z e a Y Z hzTwo
  have hlayer' :
      ((hardLayerUnits h z e a Y Z).card : Real) ≤
        4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log z +
          dualSieveError X := by
    simpa [dualSieveError, z] using hlayer
  have hscaleNonneg : 0 ≤ primeCountingScale Y :=
    (primeCountingScale_pos Y).le
  calc
    ((hardLayerUnits h (stageOldPrimeCutoff 64 X) e a
          (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Real) /
          primeCountingScale (X / h.1 ^ e) =
        ((hardLayerUnits h z e a Y Z).card : Real) /
          primeCountingScale Y := by
      simp [stageOldPrimeCutoff, z, Y, Z, d]
    _ ≤
        (4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log z +
          dualSieveError X) / primeCountingScale Y :=
      div_le_div_of_nonneg_right hlayer' hscaleNonneg
    _ =
        (4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log z) /
            primeCountingScale Y +
          dualSieveError X / primeCountingScale Y := by
      rw [add_div]
    _ ≤ dualSieveLayerCoefficient h B + ε :=
      (add_lt_add_of_le_of_lt hlocalMain herror).le

end Erdos279
