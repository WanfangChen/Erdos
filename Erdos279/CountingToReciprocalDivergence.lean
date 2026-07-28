import Erdos279.LogHarmonicDivergence
import Erdos279.NthLogRatioInversion

/-!
# Positive prime-counting density forces reciprocal divergence

This is an elementary consequence of the already formalized inversion of
the count-form PNT.  If the `n`th value of a positive predicate is
`O((n+2) log (n+2))`, then its reciprocal dominates a positive constant
multiple of the divergent logarithmic harmonic series.
-/

namespace Erdos279

open Filter

/-- The logarithmic harmonic term is exactly the reciprocal of the
normalization used for `n`th prime values. -/
theorem logHarmonicTerm_add_two_eq_inv_nthPrimeScale
    (n : Nat) :
    logHarmonicTerm (n + 2) =
      1 / nthPrimeScale n := by
  unfold logHarmonicTerm nthPrimeScale
  rw [if_neg (by omega)]

/--
A positive count-form PNT for a predicate containing only positive
integers forces divergence of the reciprocal series along its canonical
increasing enumeration.
-/
theorem not_summable_reciprocal_nth_of_counting
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    (hPpos : ∀ n, P n → 0 < n)
    {density : Real}
    (hdensity : 0 < density)
    (hCount :
      HasPrimeCountingAsymptotic P density) :
    ¬ Summable
      (fun n : Nat =>
        1 / ((Nat.nth P n : Nat) : Real)) := by
  let C : Real := 1 / density + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hlimit :
      1 / density < C := by
    dsimp [C]
    linarith
  have hNth :=
    nthAsymptotic_of_counting
      P hInf hdensity hCount
  have hevent :
      ∀ᶠ n : Nat in atTop,
        ((Nat.nth P n : Nat) : Real) /
            nthPrimeScale n <
          C :=
    hNth.eventually_lt_const hlimit
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  intro hsum
  have htail :
      Summable
        (fun n : Nat =>
          1 /
            ((Nat.nth P (n + N) : Nat) : Real)) :=
    (summable_nat_add_iff
      (f := fun n : Nat =>
        1 / ((Nat.nth P n : Nat) : Real)) N).2
      hsum
  have hupper :
      Summable
        (fun n : Nat =>
          C *
            (1 /
              ((Nat.nth P (n + N) : Nat) : Real))) :=
    htail.mul_left C
  have hlower :
      Summable
        (fun n : Nat =>
          logHarmonicTerm ((n + N) + 2)) := by
    apply hupper.of_nonneg_of_le
    · intro n
      exact logHarmonicTerm_nonneg _
    · intro n
      let m := n + N
      let p := Nat.nth P m
      have hPm : P p :=
        Nat.nth_mem_of_infinite hInf m
      have hpNat : 0 < p := hPpos p hPm
      have hpR : 0 < (p : Real) := by
        exact_mod_cast hpNat
      have hscale : 0 < nthPrimeScale m :=
        nthPrimeScale_pos m
      have hratio :
          (p : Real) / nthPrimeScale m < C := by
        exact hN m (by
          dsimp [m]
          omega)
      have hpScale :
          (p : Real) ≤ C * nthPrimeScale m := by
        exact
          ((div_lt_iff₀ hscale).mp hratio).le
      have hinv :
          1 / nthPrimeScale m ≤
            C * (1 / (p : Real)) := by
        have hcross :
            (1 : Real) * (p : Real) ≤
              C * nthPrimeScale m := by
          simpa using hpScale
        have hdiv :
            (1 : Real) / nthPrimeScale m ≤
              C / (p : Real) :=
          (div_le_div_iff₀ hscale hpR).2 hcross
        simpa [div_eq_mul_inv] using hdiv
      simpa [m, p,
        logHarmonicTerm_add_two_eq_inv_nthPrimeScale]
        using hinv
  have hshifted :
      Summable
        (fun n : Nat =>
          logHarmonicTerm (n + (N + 2))) := by
    simpa [add_assoc] using hlower
  exact not_summable_logHarmonicTerm
    ((summable_nat_add_iff
      (f := logHarmonicTerm) (N + 2)).1
      hshifted)

/-- Reciprocal indicator of a natural-number predicate. -/
noncomputable def predicateReciprocalTerm
    (P : Nat → Prop) (n : Nat) : Real := by
  classical
  exact if P n then 1 / (n : Real) else 0

theorem predicateReciprocalTerm_nonneg
    (P : Nat → Prop) (n : Nat) :
    0 ≤ predicateReciprocalTerm P n := by
  classical
  unfold predicateReciprocalTerm
  split_ifs
  · positivity
  · exact le_rfl

/-- The same divergence expressed as a series indexed by all natural
numbers, with zero outside the predicate. -/
theorem not_summable_predicateReciprocal_of_counting
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    (hPpos : ∀ n, P n → 0 < n)
    {density : Real}
    (hdensity : 0 < density)
    (hCount :
      HasPrimeCountingAsymptotic P density) :
    ¬ Summable (predicateReciprocalTerm P) := by
  classical
  have hnth :=
    not_summable_reciprocal_nth_of_counting
      P hInf hPpos hdensity hCount
  intro hsum
  have hsub :=
    hsum.comp_injective (Nat.nth_injective hInf)
  apply hnth
  apply hsub.congr
  intro n
  have hmem : P (Nat.nth P n) :=
    Nat.nth_mem_of_infinite hInf n
  simp [predicateReciprocalTerm, hmem]

/-- Hence the finite reciprocal partial sums tend to infinity. -/
theorem predicateReciprocalSum_tendsto_atTop_of_counting
    (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    (hPpos : ∀ n, P n → 0 < n)
    {density : Real}
    (hdensity : 0 < density)
    (hCount :
      HasPrimeCountingAsymptotic P density) :
    Tendsto
      (fun z : Nat =>
        ∑ n ∈ Finset.range z,
          predicateReciprocalTerm P n)
      atTop atTop := by
  rw [←
    not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact
      not_summable_predicateReciprocal_of_counting
        P hInf hPpos hdensity hCount
  · exact predicateReciprocalTerm_nonneg P

end Erdos279
