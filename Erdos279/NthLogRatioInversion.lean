import Erdos279.CountingToImplicitNth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The logarithm-ratio inversion lemma

This file proves the remaining elementary inverse-function fact:
a positive implicit `x / log x` nth relation forces

`log (p_n + 2) / log (n + 2) → 1`.
-/

namespace Erdos279

open Filter

noncomputable def nthShiftValue
    (P : Nat → Prop) (n : Nat) : Real :=
  (Nat.nth P n : Real) + 2

noncomputable def indexShiftValue
    (n : Nat) : Real :=
  (n : Real) + 2

theorem nthShiftValue_pos
    (P : Nat → Prop) (n : Nat) :
    0 < nthShiftValue P n := by
  unfold nthShiftValue
  positivity

theorem indexShiftValue_pos
    (n : Nat) :
    0 < indexShiftValue n := by
  unfold indexShiftValue
  positivity

theorem nthShiftValue_tendsto_atTop
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P)) :
    Tendsto (nthShiftValue P) atTop atTop := by
  unfold nthShiftValue
  exact
    tendsto_atTop_add_const_right
      atTop 2
      (tendsto_natCast_atTop_atTop.comp
        (nth_tendsto_atTop P hInf))

theorem indexShiftValue_tendsto_atTop :
    Tendsto indexShiftValue atTop atTop := by
  unfold indexShiftValue
  exact
    tendsto_atTop_add_const_right
      atTop 2 tendsto_natCast_atTop_atTop

/-- A positive implicit inverse relation already gives a polynomial upper
bound on the nth values. -/
theorem implicitNth_eventually_polynomialBound
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    {density : Real}
    (hdensity : 0 < density)
    (hImplicit :
      HasImplicitNthAsymptotic
        P hInf density) :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n in atTop,
        nthShiftValue P n <
          C * (indexShiftValue n) ^ 2 := by
  let C : Real := 16 / density ^ 2
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  have hLower :
      ∀ᶠ n : Nat in atTop,
        density / 2 <
          (n : Real) /
            primeCountingScale
              (Nat.nth P n) :=
    hImplicit.eventually_const_lt
      (by linarith)
  filter_upwards [hLower] with n hn
  let x := nthShiftValue P n
  have hx : 0 < x :=
    nthShiftValue_pos P n
  have hxOne : 1 < x := by
    unfold x nthShiftValue
    have hnthNonneg :
        (0 : Real) ≤
          (Nat.nth P n : Real) := by
      positivity
    linarith
  have hlogPos :
      0 < Real.log x :=
    Real.log_pos hxOne
  have hlogBound :
      Real.log x ≤ 2 * Real.sqrt x := by
    have h :=
      Real.log_le_rpow_div hx.le
        (by norm_num :
          (0 : Real) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    norm_num at h ⊢
    linarith
  have hnRewritten :
      density / 2 <
        (n : Real) * Real.log x / x := by
    unfold primeCountingScale at hn
    unfold x nthShiftValue
    push_cast at hn
    have hlogNe :
        Real.log
            ((Nat.nth P n : Real) + 2) ≠
          0 := by
      simpa [x, nthShiftValue] using
        hlogPos.ne'
    field_simp [hlogNe] at hn ⊢
    nlinarith
  have hmul :
      density / 2 * x <
        (n : Real) * Real.log x :=
    (lt_div_iff₀ hx).mp hnRewritten
  have hmulBound :
      (n : Real) * Real.log x ≤
        (n : Real) *
          (2 * Real.sqrt x) :=
    mul_le_mul_of_nonneg_left
      hlogBound (by positivity)
  have hsqrtPos :
      0 < Real.sqrt x :=
    Real.sqrt_pos.2 hx
  have hsqrtSq :
      (Real.sqrt x) ^ 2 = x := by
    exact Real.sq_sqrt hx.le
  have hlinear :
      density * Real.sqrt x <
        4 * (n : Real) := by
    nlinarith
  have hsquare :
      (density * Real.sqrt x) ^ 2 <
        (4 * (n : Real)) ^ 2 :=
    by
      simpa only [pow_two] using
        mul_self_lt_mul_self
          (mul_nonneg hdensity.le
            (Real.sqrt_nonneg x))
          hlinear
  have hpoly :
      density ^ 2 * x <
        16 * (n : Real) ^ 2 := by
    nlinarith
  have hdensitySq :
      0 < density ^ 2 := sq_pos_of_pos hdensity
  have hxBound :
      x < C * (n : Real) ^ 2 := by
    dsimp [C]
    rw [show
      16 / density ^ 2 *
          (n : Real) ^ 2 =
        (16 * (n : Real) ^ 2) /
          density ^ 2 by
            ring]
    apply (lt_div_iff₀ hdensitySq).2
    nlinarith
  have hnSquare :
      (n : Real) ^ 2 ≤
        (indexShiftValue n) ^ 2 := by
    unfold indexShiftValue
    nlinarith [sq_nonneg ((n : Real) + 2)]
  exact
    hxBound.trans_le
      (mul_le_mul_of_nonneg_left
        hnSquare hC.le)

/-- The polynomial bound makes the logarithm ratio uniformly bounded. -/
theorem implicitNth_eventually_logRatio_bounded
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    {density : Real}
    (hdensity : 0 < density)
    (hImplicit :
      HasImplicitNthAsymptotic
        P hInf density) :
    ∃ D : Real, 0 < D ∧
      ∀ᶠ n in atTop,
        |Real.log (nthShiftValue P n) /
            Real.log (indexShiftValue n)| ≤ D := by
  obtain ⟨C, hC, hPoly⟩ :=
    implicitNth_eventually_polynomialBound
      P hInf hdensity hImplicit
  let D : Real := |Real.log C| + 3
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, hD, ?_⟩
  have hIndexLogTop :
      Tendsto
        (fun n : Nat =>
          Real.log (indexShiftValue n))
        atTop atTop :=
    Real.tendsto_log_atTop.comp
      indexShiftValue_tendsto_atTop
  have hIndexLogOne :
      ∀ᶠ n : Nat in atTop,
        1 ≤ Real.log (indexShiftValue n) :=
    hIndexLogTop.eventually_ge_atTop 1
  filter_upwards [hPoly, hIndexLogOne] with
      n hnPoly hnLogOne
  let x := nthShiftValue P n
  let y := indexShiftValue n
  have hx : 0 < x :=
    nthShiftValue_pos P n
  have hxOne : 1 < x := by
    unfold x nthShiftValue
    have hnthNonneg :
        (0 : Real) ≤
          (Nat.nth P n : Real) := by
      positivity
    linarith
  have hy : 0 < y :=
    indexShiftValue_pos n
  have hyLogPos :
      0 < Real.log y := by
    dsimp [y]
    linarith
  have hyLogOne :
      1 ≤ Real.log y := by
    simpa [y] using hnLogOne
  have hCySq :
      0 < C * y ^ 2 :=
    mul_pos hC (sq_pos_of_pos hy)
  have hlogUpper :
      Real.log x ≤
        Real.log (C * y ^ 2) :=
    Real.log_le_log hx hnPoly.le
  rw [Real.log_mul hC.ne'
      (pow_ne_zero 2 hy.ne'),
    Real.log_pow] at hlogUpper
  have hratioNonneg :
      0 ≤
        Real.log x / Real.log y :=
    div_nonneg
      (Real.log_nonneg hxOne.le)
      hyLogPos.le
  have hratioUpper :
      Real.log x / Real.log y ≤ D := by
    apply (div_le_iff₀ hyLogPos).2
    dsimp [D]
    have hlogC :
        Real.log C ≤ |Real.log C| :=
      le_abs_self _
    calc
      Real.log x ≤
          Real.log C +
            (2 : Real) * Real.log y :=
        hlogUpper
      _ ≤
          |Real.log C| +
            (2 : Real) * Real.log y :=
        by
          simpa [add_comm] using
            add_le_add_right hlogC
              ((2 : Real) * Real.log y)
      _ ≤
          (|Real.log C| + 3) *
            Real.log y := by
        have hmulNonneg :
            0 ≤
              |Real.log C| *
                (Real.log y - 1) :=
          mul_nonneg (abs_nonneg _)
            (sub_nonneg.mpr hyLogOne)
        nlinarith
  rw [abs_of_nonneg hratioNonneg]
  exact hratioUpper

/-- The iterated logarithm is negligible compared with the index
logarithm. -/
theorem implicitNth_loglog_div_logIndex_tendsto_zero
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    {density : Real}
    (hdensity : 0 < density)
    (hImplicit :
      HasImplicitNthAsymptotic
        P hInf density) :
    Tendsto
      (fun n : Nat =>
        Real.log
            (Real.log (nthShiftValue P n)) /
          Real.log (indexShiftValue n))
      atTop (nhds 0) := by
  obtain ⟨D, hD, hBound⟩ :=
    implicitNth_eventually_logRatio_bounded
      P hInf hdensity hImplicit
  have hLogNthTop :
      Tendsto
        (fun n : Nat =>
          Real.log (nthShiftValue P n))
        atTop atTop :=
    Real.tendsto_log_atTop.comp
      (nthShiftValue_tendsto_atTop
        P hInf)
  have hLittleReal :
      Tendsto
        (fun t : Real =>
          Real.log t / t)
        atTop (nhds 0) := by
    simpa only [id_eq] using
      Real.isLittleO_log_id_atTop
        |>.tendsto_div_nhds_zero
  have hSmall :
      Tendsto
        (fun n : Nat =>
          Real.log
              (Real.log
                (nthShiftValue P n)) /
            Real.log (nthShiftValue P n))
        atTop (nhds 0) :=
    hLittleReal.comp hLogNthTop
  let u : Nat → Real :=
    fun n =>
      Real.log
          (Real.log (nthShiftValue P n)) /
        Real.log (nthShiftValue P n)
  let v : Nat → Real :=
    fun n =>
      Real.log (nthShiftValue P n) /
        Real.log (indexShiftValue n)
  have hu :
      Tendsto u atTop (nhds 0) := by
    simpa [u] using hSmall
  have hDom :
      Tendsto
        (fun n => D * |u n|)
        atTop (nhds 0) := by
    have huAbs :
        Tendsto (fun n => |u n|)
          atTop (nhds 0) := by
      simpa using hu.abs
    simpa using
      (tendsto_const_nhds.mul huAbs :
        Tendsto
          (fun n => D * |u n|)
          atTop (nhds (D * 0)))
  have hAbsProduct :
      Tendsto
        (fun n => |u n * v n|)
        atTop (nhds 0) := by
    refine
      squeeze_zero'
        (g := fun n => D * |u n|)
        ?_ ?_ hDom
    · exact
        Eventually.of_forall
          (fun n => abs_nonneg (u n * v n))
    · filter_upwards [hBound] with n hn
      rw [abs_mul]
      simpa [v, mul_comm] using
        mul_le_mul_of_nonneg_left
          hn (abs_nonneg (u n))
  have hProduct :
      Tendsto
        (fun n => u n * v n)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact hAbsProduct
  have hLogNthOne :
      ∀ᶠ n : Nat in atTop,
        1 ≤ Real.log
          (nthShiftValue P n) :=
    hLogNthTop.eventually_ge_atTop 1
  have hEq :
      ∀ᶠ n : Nat in atTop,
        u n * v n =
          Real.log
              (Real.log
                (nthShiftValue P n)) /
            Real.log (indexShiftValue n) :=
    hLogNthOne.mono
      (by
        intro n hn
        have hnNe :
            Real.log
                (nthShiftValue P n) ≠
              0 := by
          linarith
        exact
          div_mul_div_cancel₀
            (a :=
              Real.log
                (Real.log
                  (nthShiftValue P n)))
            (b :=
              Real.log
                (nthShiftValue P n))
            (c :=
              Real.log
                (indexShiftValue n))
            hnNe)
  exact hProduct.congr' hEq

/-- Shifting the index by two does not change its logarithm to first
order. -/
theorem index_log_div_shift_tendsto_one :
    Tendsto
      (fun n : Nat =>
        Real.log (n : Real) /
          Real.log (indexShiftValue n))
      atTop (nhds 1) := by
  have hDifference :
      Tendsto
        (fun n : Nat =>
          Real.log (indexShiftValue n) -
            Real.log (n : Real))
        atTop (nhds 0) := by
    simpa [indexShiftValue] using
      (Real.tendsto_log_comp_add_sub_log 2).comp
        tendsto_natCast_atTop_atTop
  have hIndexLogTop :
      Tendsto
        (fun n : Nat =>
          Real.log (indexShiftValue n))
        atTop atTop :=
    Real.tendsto_log_atTop.comp
      indexShiftValue_tendsto_atTop
  have hDifferenceRatio :
      Tendsto
        (fun n : Nat =>
          (Real.log (indexShiftValue n) -
              Real.log (n : Real)) /
            Real.log (indexShiftValue n))
        atTop (nhds 0) :=
    hDifference.div_atTop hIndexLogTop
  have hOneSub :
      Tendsto
        (fun n : Nat =>
          1 -
            (Real.log (indexShiftValue n) -
                Real.log (n : Real)) /
              Real.log (indexShiftValue n))
        atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hDifferenceRatio
  have hLogOne :
      ∀ᶠ n : Nat in atTop,
        1 ≤ Real.log (indexShiftValue n) :=
    hIndexLogTop.eventually_ge_atTop 1
  have hEventually :
      (fun n : Nat =>
        1 -
          (Real.log (indexShiftValue n) -
              Real.log (n : Real)) /
            Real.log (indexShiftValue n)) =ᶠ[atTop]
      (fun n : Nat =>
        Real.log (n : Real) /
          Real.log (indexShiftValue n)) := by
    filter_upwards [hLogOne] with n hn
    have hne :
        Real.log (indexShiftValue n) ≠ 0 := by
      linarith
    field_simp [hne]
    ring
  simpa using hOneSub.congr' hEventually

/-- A positive implicit `x / log x` inverse relation forces the
logarithm of the nth value to be asymptotic to the logarithm of its
index.  This is the elementary inversion step that was previously an
extra hypothesis of the project. -/
theorem implicitNth_to_logRatio
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    {density : Real}
    (hdensity : 0 < density)
    (hImplicit :
      HasImplicitNthAsymptotic
        P hInf density) :
    HasNthLogRatio P hInf := by
  have hIndexLogTop :
      Tendsto
        (fun n : Nat =>
          Real.log (indexShiftValue n))
        atTop atTop :=
    Real.tendsto_log_atTop.comp
      indexShiftValue_tendsto_atTop
  have hImplicitLog :
      Tendsto
        (fun n : Nat =>
          Real.log
            ((n : Real) /
              primeCountingScale
                (Nat.nth P n)))
        atTop (nhds (Real.log density)) :=
    hImplicit.log hdensity.ne'
  have hImplicitLogSmall :
      Tendsto
        (fun n : Nat =>
          Real.log
              ((n : Real) /
                primeCountingScale
                  (Nat.nth P n)) /
            Real.log (indexShiftValue n))
        atTop (nhds 0) :=
    hImplicitLog.div_atTop hIndexLogTop
  have hLogLogSmall :=
    implicitNth_loglog_div_logIndex_tendsto_zero
      P hInf hdensity hImplicit
  have hCombined :
      Tendsto
        (fun n : Nat =>
          Real.log (n : Real) /
                Real.log (indexShiftValue n) +
              Real.log
                  (Real.log
                    (nthShiftValue P n)) /
                Real.log (indexShiftValue n) -
            Real.log
                ((n : Real) /
                  primeCountingScale
                    (Nat.nth P n)) /
              Real.log (indexShiftValue n))
        atTop (nhds (1 + 0 - 0)) :=
    (index_log_div_shift_tendsto_one.add
      hLogLogSmall).sub hImplicitLogSmall
  have hIndexLogOne :
      ∀ᶠ n : Nat in atTop,
        1 ≤ Real.log (indexShiftValue n) :=
    hIndexLogTop.eventually_ge_atTop 1
  have hEventually :
      (fun n : Nat =>
        Real.log (nthShiftValue P n) /
          Real.log (indexShiftValue n)) =ᶠ[atTop]
      (fun n : Nat =>
        Real.log (n : Real) /
              Real.log (indexShiftValue n) +
            Real.log
                (Real.log
                  (nthShiftValue P n)) /
              Real.log (indexShiftValue n) -
          Real.log
              ((n : Real) /
                primeCountingScale
                  (Nat.nth P n)) /
            Real.log (indexShiftValue n)) := by
    filter_upwards
      [eventually_ge_atTop 1,
        hIndexLogOne] with n hn hnIndexLog
    let x := nthShiftValue P n
    have hx : 0 < x :=
      nthShiftValue_pos P n
    have hxOne : 1 < x := by
      unfold x nthShiftValue
      have hnthNonneg :
          (0 : Real) ≤
            (Nat.nth P n : Real) := by
        positivity
      linarith
    have hlogx :
        0 < Real.log x :=
      Real.log_pos hxOne
    have hnPos :
        (0 : Real) < (n : Real) := by
      exact_mod_cast
        (Nat.zero_lt_of_lt hn)
    have hScaleNe :
        primeCountingScale
            (Nat.nth P n) ≠ 0 := by
      unfold primeCountingScale
      apply div_ne_zero
      · positivity
      · simpa [x, nthShiftValue] using
          hlogx.ne'
    have hLogIdentity :
        Real.log
            ((n : Real) /
              primeCountingScale
                (Nat.nth P n)) =
          Real.log (n : Real) -
            (Real.log x -
              Real.log (Real.log x)) := by
      rw [Real.log_div hnPos.ne'
          hScaleNe]
      unfold primeCountingScale
      push_cast
      change
        Real.log (n : Real) -
              Real.log
                (x / Real.log x) =
          Real.log (n : Real) -
            (Real.log x -
              Real.log (Real.log x))
      rw [Real.log_div hx.ne'
          hlogx.ne']
    have hIndexLogNe :
        Real.log (indexShiftValue n) ≠ 0 := by
      linarith
    rw [hLogIdentity]
    field_simp [hIndexLogNe]
    ring
  unfold HasNthLogRatio
  have hShiftRatio :
      Tendsto
        (fun n : Nat =>
          Real.log (nthShiftValue P n) /
            Real.log (indexShiftValue n))
        atTop (nhds 1) := by
    simpa using hCombined.congr' hEventually.symm
  simpa [nthShiftValue, indexShiftValue,
    Nat.cast_add] using hShiftRatio

/-- Count-form PNT with positive density now implies the full explicit
nth-value asymptotic, with no separate inversion hypothesis. -/
theorem nthAsymptotic_of_counting
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    {density : Real}
    (hdensity : 0 < density)
    (hCount :
      HasPrimeCountingAsymptotic
        P density) :
    Tendsto
      (fun n : Nat =>
        ((Nat.nth P n : Nat) : Real) /
          nthPrimeScale n)
      atTop (nhds (1 / density)) := by
  have hImplicit :=
    hCount.toImplicitNth hInf
  exact
    nthAsymptotic_of_implicit_and_logRatio
      P hInf hdensity hImplicit
      (implicitNth_to_logRatio
        P hInf hdensity hImplicit)

/-- Project-level count-form PNT implies the quantitative nth-prime
asymptotic used by the mesh construction. -/
theorem projectNthAsymptotic_of_counting
    (P : Prime → Prop)
    (hInf :
      Set.Infinite
        (setOf (primeNatPredicate P)))
    {density : Real}
    (hdensity : 0 < density)
    (hCount :
      HasProjectPrimeCountingAsymptotic
        P density) :
    HasNthPrimeAsymptotic
      P hInf density := by
  unfold HasNthPrimeAsymptotic
  simpa only [enumeratePrimePredicate_val] using
    nthAsymptotic_of_counting
      (primeNatPredicate P) hInf
      hdensity hCount

end Erdos279
