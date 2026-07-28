import Erdos279.ComplementaryResidueCardinality

/-!
# From count-form PNT to nth-prime asymptotics

Composing a counting asymptotic with `Nat.nth` immediately gives the
implicit inverse relation

`n / ((p_n + 2) / log (p_n + 2)) → density`.

This file proves that composition and isolates the one remaining standard
inverse-function fact as convergence of the logarithm ratio.
-/

namespace Erdos279

open Filter

/-- The implicit inverse relation obtained by evaluating the counting
function at its canonical `n`th value. -/
def HasImplicitNthAsymptotic
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    (density : Real) : Prop :=
  Tendsto
    (fun n : Nat =>
      (n : Real) /
        primeCountingScale (Nat.nth P n))
    atTop (nhds density)

/-- The logarithm-ratio statement needed to turn the implicit inverse
relation into the usual explicit nth-prime asymptotic. -/
def HasNthLogRatio
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P)) : Prop :=
  Tendsto
    (fun n : Nat =>
      Real.log
          ((Nat.nth P n : Nat) + 2 : Nat) /
        Real.log (n + 2 : Nat))
    atTop (nhds 1)

theorem predicateCount_nth_of_infinite
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    (n : Nat) :
    predicateCount P (Nat.nth P n) = n := by
  classical
  unfold predicateCount
  exact Nat.count_nth_of_infinite hInf n

/-- A count-form asymptotic implies the exact implicit nth relation. -/
theorem HasPrimeCountingAsymptotic.toImplicitNth
    {P : Nat → Prop} {density : Real}
    (hInf : Set.Infinite (setOf P))
    (hCount :
      HasPrimeCountingAsymptotic P density) :
    HasImplicitNthAsymptotic
      P hInf density := by
  unfold HasPrimeCountingAsymptotic at hCount
  unfold HasImplicitNthAsymptotic
  have hnthTop :
      Tendsto (Nat.nth P) atTop atTop :=
    (Nat.nth_strictMono hInf).tendsto_atTop
  have hcomp := hCount.comp hnthTop
  apply hcomp.congr'
  apply Eventually.of_forall
  intro n
  simp only [Function.comp_apply,
    predicateCount_nth_of_infinite
      P hInf]

/-- Nth values of an infinite predicate tend to infinity. -/
theorem nth_tendsto_atTop
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P)) :
    Tendsto (Nat.nth P) atTop atTop :=
  (Nat.nth_strictMono hInf).tendsto_atTop

/-- Along an infinite predicate, `p_n / (p_n + 2) → 1`. -/
theorem nth_div_add_two_tendsto_one
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P)) :
    Tendsto
      (fun n : Nat =>
        ((Nat.nth P n : Nat) : Real) /
          (((Nat.nth P n : Nat) : Real) + 2))
      atTop (nhds 1) := by
  exact
    (tendsto_natCast_div_add_atTop
      (2 : Real)).comp
      (nth_tendsto_atTop P hInf)

/-- The explicit nth-prime asymptotic follows from the implicit relation
once the standard logarithm-ratio inversion lemma is known. -/
theorem nthAsymptotic_of_implicit_and_logRatio
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    {density : Real}
    (hdensity : 0 < density)
    (hImplicit :
      HasImplicitNthAsymptotic
        P hInf density)
    (hLog : HasNthLogRatio P hInf) :
    Tendsto
      (fun n : Nat =>
        ((Nat.nth P n : Nat) : Real) /
          nthPrimeScale n)
      atTop (nhds (1 / density)) := by
  have hInv :
      Tendsto
        (fun n : Nat =>
          ((n : Real) /
            primeCountingScale
              (Nat.nth P n))⁻¹)
        atTop (nhds density⁻¹) :=
    hImplicit.inv₀ hdensity.ne'
  have hPrimeShift :=
    nth_div_add_two_tendsto_one
      P hInf
  have hIndexShift :
      Tendsto
        (fun n : Nat =>
          (n : Real) /
            ((n : Real) + 2))
        atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop
      (2 : Real)
  have hProduct :
      Tendsto
        (fun n : Nat =>
          ((n : Real) /
              primeCountingScale
                (Nat.nth P n))⁻¹ *
            (Real.log
                ((Nat.nth P n : Nat) + 2 : Nat) /
              Real.log (n + 2 : Nat)) *
            (((Nat.nth P n : Nat) : Real) /
              (((Nat.nth P n : Nat) : Real) + 2)) *
            ((n : Real) /
              ((n : Real) + 2)))
        atTop
        (nhds
          (density⁻¹ * 1 * 1 * 1)) :=
    ((hInv.mul hLog).mul hPrimeShift).mul
      hIndexShift
  have hEventually :
      (fun n : Nat =>
        ((n : Real) /
              primeCountingScale
                (Nat.nth P n))⁻¹ *
            (Real.log
                ((Nat.nth P n : Nat) + 2 : Nat) /
              Real.log (n + 2 : Nat)) *
            (((Nat.nth P n : Nat) : Real) /
              (((Nat.nth P n : Nat) : Real) + 2)) *
            ((n : Real) /
              ((n : Real) + 2))) =ᶠ[atTop]
      (fun n : Nat =>
        ((Nat.nth P n : Nat) : Real) /
          nthPrimeScale n) := by
    filter_upwards
      [eventually_ge_atTop 1] with n hn
    have hnPos : (0 : Real) < (n : Real) := by
      exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hnLog :
        Real.log ((n + 2 : Nat) : Real) ≠ 0 := by
      exact
        (Real.log_pos
          (by
            exact_mod_cast
              (by omega :
                1 < n + 2))).ne'
    have hpPos :
        (0 : Real) <
          ((Nat.nth P n : Nat) : Real) := by
      have hpNatPos :
          0 < Nat.nth P n := by
        have hstrict :
            Nat.nth P 0 <
              Nat.nth P n :=
          (Nat.nth_lt_nth hInf).2
            (by omega)
        exact
          (Nat.zero_le
            (Nat.nth P 0)).trans_lt
            hstrict
      exact_mod_cast hpNatPos
    have hpLog :
        Real.log
            (((Nat.nth P n : Nat) + 2 : Nat) : Real) ≠
          0 := by
      exact
        (Real.log_pos
          (by
            exact_mod_cast
              (by omega :
                1 <
                  (Nat.nth P n : Nat) + 2))).ne'
    have hnLogCast :
        Real.log ((n : Real) + 2) ≠ 0 := by
      simpa [Nat.cast_add] using hnLog
    have hpLogCast :
        Real.log
            (((Nat.nth P n : Nat) : Real) + 2) ≠
          0 := by
      simpa [Nat.cast_add] using hpLog
    unfold primeCountingScale nthPrimeScale
    push_cast
    field_simp [hnPos.ne', hpPos.ne',
      hnLogCast, hpLogCast]
  have hFinal :=
    hProduct.congr' hEventually
  simpa [div_eq_mul_inv] using hFinal

/-- Count-form PNT plus the logarithm-ratio inversion fact gives the
project's `HasNthPrimeAsymptotic` interface. -/
theorem projectNthAsymptotic_of_counting_and_logRatio
    (P : Prime → Prop)
    (hInf :
      Set.Infinite
        (setOf (primeNatPredicate P)))
    {density : Real}
    (hdensity : 0 < density)
    (hCount :
      HasProjectPrimeCountingAsymptotic
        P density)
    (hLog :
      HasNthLogRatio
        (primeNatPredicate P) hInf) :
    HasNthPrimeAsymptotic
      P hInf density := by
  unfold HasNthPrimeAsymptotic
  simpa only [enumeratePrimePredicate_val] using
    nthAsymptotic_of_implicit_and_logRatio
      (primeNatPredicate P) hInf
      hdensity
      (hCount.toImplicitNth hInf)
      hLog

end Erdos279
