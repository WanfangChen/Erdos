import Erdos279.HardLayerTruncation
import Erdos279.PrimeCountingAsymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Negligibility of the high-exponent hard tail

This file completes the limiting part of equation (2.24).  The exact bound
proved in `HardLayerTruncation` is `O(sqrt X log X)`; here we prove directly
that this is `o(X / log X)` for the shifted positive normalization used
throughout the project.
-/

namespace Erdos279

open Filter

/-- A natural logarithm to a fixed base is bounded by the corresponding
quotient of real logarithms. -/
theorem natLog_cast_le_realLog_div
    {b n : Nat} (hb : 1 < b) (hn : n ≠ 0) :
    (Nat.log b n : Real) ≤
      Real.log (n : Real) / Real.log (b : Real) := by
  have hpowNat :
      b ^ Nat.log b n ≤ n :=
    Nat.pow_log_le_self b hn
  have hpowReal :
      (b : Real) ^ Nat.log b n ≤ (n : Real) := by
    exact_mod_cast hpowNat
  have hbasePos : (0 : Real) < (b : Real) := by
    exact_mod_cast (Nat.zero_lt_one.trans hb)
  have hlog :=
    Real.log_le_log (by positivity : 0 < (b : Real) ^ Nat.log b n)
      hpowReal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hb))).2
    (by simpa using hlog)

/-- The real comparison function used for the tail tends to zero. -/
theorem log_sq_div_sqrt_shift_tendsto_zero :
    Tendsto
      (fun X : Nat =>
        Real.log (((X + 2 : Nat) : Real)) ^ 2 /
          Real.sqrt (((X + 2 : Nat) : Real)))
      atTop (nhds 0) := by
  have hReal :
      Tendsto
        (fun x : Real =>
          Real.log x ^ 2 / Real.sqrt x)
        atTop (nhds 0) := by
    have h :=
      ((isLittleO_log_rpow_rpow_atTop
        (s := (1 / 2 : Real)) (2 : Real)
        (by norm_num)).tendsto_div_nhds_zero)
    apply h.congr'
    exact Eventually.of_forall fun x => by
      change
        Real.log x ^ (2 : Real) / x ^ (1 / 2 : Real) =
          Real.log x ^ (2 : Nat) / Real.sqrt x
      rw [Real.sqrt_eq_rpow, Real.rpow_two]
  have hShift :
      Tendsto
        (fun X : Nat => (((X + 2 : Nat) : Real)))
        atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 2)
  exact hReal.comp hShift

/-- The explicit upper bound for the complementary hard layers. -/
noncomputable def hardTailRealBound
    (h : Prime) (B X : Nat) : Real :=
  (((Nat.log h.1 (B * X) + 1) *
    (B * Nat.sqrt X) : Nat) : Real)

/-- Equation (2.24), with a slightly weaker but still negligible
`O(sqrt X log X)` upper bound. -/
theorem hardTailRealBound_normalized_tendsto_zero
    (h : Prime) (B : Nat) (hB : 0 < B) :
    Tendsto
      (fun X : Nat =>
        hardTailRealBound h B X /
          primeCountingScale X)
      atTop (nhds 0) := by
  let c : Real := Real.log (h.1 : Real)
  let C : Real :=
    (1 / c) + Real.log (B : Real) / c + 1
  have hcPos : 0 < c := by
    dsimp [c]
    exact Real.log_pos (by exact_mod_cast h.one_lt)
  have hlogBNonneg :
      0 ≤ Real.log (B : Real) := by
    exact Real.log_nonneg (by exact_mod_cast hB)
  have hCNonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hShiftTop :
      Tendsto
        (fun X : Nat => (((X + 2 : Nat) : Real)))
        atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 2)
  have hLogShiftTop :
      Tendsto
        (fun X : Nat =>
          Real.log (((X + 2 : Nat) : Real)))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hShiftTop
  have hLogShiftOne :
      ∀ᶠ X : Nat in atTop,
        1 ≤ Real.log (((X + 2 : Nat) : Real)) :=
    hLogShiftTop.eventually_ge_atTop 1
  have hMajorant :
      Tendsto
        (fun X : Nat =>
          (C * (B : Real)) *
            (Real.log (((X + 2 : Nat) : Real)) ^ 2 /
              Real.sqrt (((X + 2 : Nat) : Real))))
        atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds :
          Tendsto (fun _ : Nat => C * (B : Real))
            atTop (nhds (C * (B : Real)))).mul
        log_sq_div_sqrt_shift_tendsto_zero)
  refine squeeze_zero'
    (g := fun X : Nat =>
      (C * (B : Real)) *
        (Real.log (((X + 2 : Nat) : Real)) ^ 2 /
          Real.sqrt (((X + 2 : Nat) : Real))))
    ?_ ?_ hMajorant
  · exact Eventually.of_forall fun X =>
      div_nonneg
        (by
          unfold hardTailRealBound
          positivity)
        (primeCountingScale_pos X).le
  · filter_upwards
      [eventually_gt_atTop (0 : Nat), hLogShiftOne] with X hX hLogOne
    have hBX : B * X ≠ 0 :=
      Nat.mul_ne_zero hB.ne' hX.ne'
    have hNatLog :
        (Nat.log h.1 (B * X) : Real) ≤
          Real.log ((B * X : Nat) : Real) / c := by
      simpa [c] using
        natLog_cast_le_realLog_div h.one_lt hBX
    have hlogMul :
        Real.log ((B * X : Nat) : Real) =
          Real.log (B : Real) + Real.log (X : Real) := by
      push_cast
      rw [Real.log_mul (by positivity) (by positivity)]
    have hXShift :
        (X : Real) ≤ ((X + 2 : Nat) : Real) := by
      exact_mod_cast (Nat.le_add_right X 2)
    have hlogXLe :
        Real.log (X : Real) ≤
          Real.log (((X + 2 : Nat) : Real)) :=
      Real.log_le_log (by exact_mod_cast hX) hXShift
    have hlogBScaled :
        Real.log (B : Real) / c ≤
          (Real.log (B : Real) / c) *
            Real.log (((X + 2 : Nat) : Real)) := by
      calc
        Real.log (B : Real) / c =
            (Real.log (B : Real) / c) * 1 := by ring
        _ ≤
            (Real.log (B : Real) / c) *
              Real.log (((X + 2 : Nat) : Real)) :=
          mul_le_mul_of_nonneg_left hLogOne
            (div_nonneg hlogBNonneg hcPos.le)
    have hNatLogAdd :
        (Nat.log h.1 (B * X) : Real) + 1 ≤
          C * Real.log (((X + 2 : Nat) : Real)) := by
      rw [hlogMul] at hNatLog
      dsimp [C]
      have hcNe : c ≠ 0 := hcPos.ne'
      calc
        (Nat.log h.1 (B * X) : Real) + 1 ≤
            (Real.log (B : Real) +
                Real.log (X : Real)) / c + 1 := by
          linarith
        _ ≤
            (Real.log (B : Real) +
                Real.log (((X + 2 : Nat) : Real))) / c +
              Real.log (((X + 2 : Nat) : Real)) := by
          have hdiv :
              (Real.log (B : Real) + Real.log (X : Real)) / c ≤
                (Real.log (B : Real) +
                  Real.log (((X + 2 : Nat) : Real))) / c :=
            div_le_div_of_nonneg_right
              (by
                simpa [add_comm] using
                  add_le_add_left hlogXLe (Real.log (B : Real)))
              hcPos.le
          linarith
        _ ≤
            (1 / c + Real.log (B : Real) / c + 1) *
              Real.log (((X + 2 : Nat) : Real)) := by
          have hLNonneg :
              0 ≤ Real.log (((X + 2 : Nat) : Real)) :=
            hLogOne.trans' zero_le_one
          calc
            (Real.log (B : Real) +
                Real.log (((X + 2 : Nat) : Real))) / c +
                Real.log (((X + 2 : Nat) : Real)) =
              Real.log (B : Real) / c +
                (1 / c) *
                  Real.log (((X + 2 : Nat) : Real)) +
                Real.log (((X + 2 : Nat) : Real)) := by
              field_simp [hcNe]
            _ ≤
                (Real.log (B : Real) / c) *
                    Real.log (((X + 2 : Nat) : Real)) +
                  (1 / c) *
                    Real.log (((X + 2 : Nat) : Real)) +
                  Real.log (((X + 2 : Nat) : Real)) := by
              linarith
            _ =
                (1 / c + Real.log (B : Real) / c + 1) *
                  Real.log (((X + 2 : Nat) : Real)) := by
              ring
    have hsqrtLe :
        (Nat.sqrt X : Real) ≤
          Real.sqrt (((X + 2 : Nat) : Real)) := by
      exact (Real.nat_sqrt_le_real_sqrt).trans
        (Real.sqrt_le_sqrt hXShift)
    have hTailNumerator :
        hardTailRealBound h B X ≤
          (C * Real.log (((X + 2 : Nat) : Real))) *
            ((B : Real) *
              Real.sqrt (((X + 2 : Nat) : Real))) := by
      unfold hardTailRealBound
      push_cast
      have hNatLogAdd' :
          (Nat.log h.1 (B * X) : Real) + 1 ≤
            C * Real.log ((X : Real) + 2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hNatLogAdd
      have hsqrtLe' :
          (Nat.sqrt X : Real) ≤
            Real.sqrt ((X : Real) + 2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hsqrtLe
      have hLogOne' :
          1 ≤ Real.log ((X : Real) + 2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hLogOne
      exact mul_le_mul hNatLogAdd'
        (mul_le_mul_of_nonneg_left hsqrtLe' (by positivity))
        (by positivity)
        (mul_nonneg hCNonneg
          (hLogOne'.trans' zero_le_one))
    have hDivide :
        hardTailRealBound h B X / primeCountingScale X ≤
          ((C * Real.log (((X + 2 : Nat) : Real))) *
            ((B : Real) *
              Real.sqrt (((X + 2 : Nat) : Real)))) /
            primeCountingScale X :=
      div_le_div_of_nonneg_right hTailNumerator
        (primeCountingScale_pos X).le
    refine hDivide.trans_eq ?_
    unfold primeCountingScale
    push_cast
    have hshiftPos :
        0 < (X : Real) + 2 := by positivity
    have hsqrtPos :
        0 < Real.sqrt ((X : Real) + 2) :=
      Real.sqrt_pos.2 hshiftPos
    have hlogPos :
        0 < Real.log ((X : Real) + 2) :=
      Real.log_pos (by
        have hXR : 0 ≤ (X : Real) := by positivity
        linarith)
    have hsquare :
        Real.sqrt ((X : Real) + 2) ^ 2 =
          (X : Real) + 2 :=
      Real.sq_sqrt hshiftPos.le
    field_simp [hlogPos.ne', hsqrtPos.ne']
    nlinarith

/-- The actual sum of all complementary layers is negligible after
normalization. -/
theorem hardTailLayers_normalized_tendsto_zero
    (h : Prime) (z B : Nat)
    (a : OldPrimeClasses h z)
    (hB : 0 < B) :
    Tendsto
      (fun X : Nat =>
        ((∑ e ∈ hardTailExponentRange h X (B * X),
          (hardLayerUnits h z e a
            (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Nat) : Real) /
          primeCountingScale X)
      atTop (nhds 0) := by
  refine squeeze_zero'
    (g := fun X : Nat =>
      hardTailRealBound h B X /
        primeCountingScale X)
    ?_ ?_ (hardTailRealBound_normalized_tendsto_zero h B hB)
  · exact Eventually.of_forall fun X =>
      div_nonneg (by positivity) (primeCountingScale_pos X).le
  · exact Eventually.of_forall fun X =>
      div_le_div_of_nonneg_right
        (by
          unfold hardTailRealBound
          exact_mod_cast
            sum_hardTailLayers_card_le h z B X a hB)
        (primeCountingScale_pos X).le

end Erdos279
