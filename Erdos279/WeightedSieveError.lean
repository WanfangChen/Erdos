import Erdos279.BetaSieveApplication

/-!
# Weighted main-term and discrepancy decomposition

This file proves the exact real-valued algebra behind equation (2.17).
No distribution theorem is assumed: the progression discrepancies are
left as an explicit finite sum for the later Bombieri--Vinogradov estimate.
-/

namespace Erdos279

open Finset

/--
A signed weighted sum is bounded by its weighted main term plus the
absolute-weighted discrepancies.
-/
theorem weighted_sum_le_main_add_discrepancy
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (weight value main : ι → Real) :
    (∑ i ∈ s, weight i * value i) ≤
      (∑ i ∈ s, weight i * main i) +
        ∑ i ∈ s, |weight i| * |value i - main i| := by
  calc
    (∑ i ∈ s, weight i * value i) =
        ∑ i ∈ s,
          (weight i * main i +
            weight i * (value i - main i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ ≤
        ∑ i ∈ s,
          (weight i * main i +
            |weight i| * |value i - main i|) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hdiff :
          weight i * (value i - main i) ≤
            |weight i| * |value i - main i| :=
        (le_abs_self (weight i * (value i - main i))).trans_eq
          (abs_mul (weight i) (value i - main i))
      linarith
    _ =
        (∑ i ∈ s, weight i * main i) +
          ∑ i ∈ s, |weight i| * |value i - main i| := by
      rw [Finset.sum_add_distrib]

/-- With `|weight| ≤ 1`, absolute-weighted discrepancies are no larger
than their unweighted sum. -/
theorem weighted_discrepancy_le_unweighted
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι)
    (weight value main : ι → Real)
    (hweight : ∀ i ∈ s, |weight i| ≤ 1) :
    (∑ i ∈ s, |weight i| * |value i - main i|) ≤
      ∑ i ∈ s, |value i - main i| := by
  apply Finset.sum_le_sum
  intro i hi
  calc
    |weight i| * |value i - main i| ≤
        1 * |value i - main i| :=
      mul_le_mul_of_nonneg_right (hweight i hi) (abs_nonneg _)
    _ = |value i - main i| := one_mul _

/--
The beta-sieve weighted progression sum is bounded by the reciprocal
divisor main term plus the exact absolute-weighted progression discrepancy.
-/
theorem beta_progression_sum_le_main_add_discrepancy
    (h : Prime) (z e Y Z level : Nat)
    (a : OldPrimeClasses h z)
    (W :
      BetaUpperSieveWeights
        (primeSubsetModulus (oldControllerPrimes h z)) level)
    (base : Real) :
    (∑ d ∈ (oldControllerPrimes h z).powerset,
        (W.weight (primeSubsetModulus d) : Real) *
          (controllerProgressionMass h
            (primeSubsetModulus d)
            (translatedSubsetClass e a d) Y Z : Real)) ≤
      base *
          (∑ n ∈
              (primeSubsetModulus
                (oldControllerPrimes h z)).divisors,
            (W.weight n : Real) / (n : Real)) +
        ∑ d ∈ (oldControllerPrimes h z).powerset,
          |(W.weight (primeSubsetModulus d) : Real)| *
            |(controllerProgressionMass h
                (primeSubsetModulus d)
                (translatedSubsetClass e a d) Y Z : Real) -
              base / (primeSubsetModulus d : Real)| := by
  let P := oldControllerPrimes h z
  have hdecomp :=
    weighted_sum_le_main_add_discrepancy
      P.powerset
      (fun d =>
        (W.weight (primeSubsetModulus d) : Real))
      (fun d =>
        (controllerProgressionMass h
          (primeSubsetModulus d)
          (translatedSubsetClass e a d) Y Z : Real))
      (fun d => base / (primeSubsetModulus d : Real))
  calc
    (∑ d ∈ P.powerset,
        (W.weight (primeSubsetModulus d) : Real) *
          (controllerProgressionMass h
            (primeSubsetModulus d)
            (translatedSubsetClass e a d) Y Z : Real)) ≤
        (∑ d ∈ P.powerset,
          (W.weight (primeSubsetModulus d) : Real) *
            (base / (primeSubsetModulus d : Real))) +
          ∑ d ∈ P.powerset,
            |(W.weight (primeSubsetModulus d) : Real)| *
              |(controllerProgressionMass h
                  (primeSubsetModulus d)
                  (translatedSubsetClass e a d) Y Z : Real) -
                base / (primeSubsetModulus d : Real)| :=
      hdecomp
    _ =
        base *
            (∑ n ∈ (primeSubsetModulus P).divisors,
              (W.weight n : Real) / (n : Real)) +
          ∑ d ∈ P.powerset,
            |(W.weight (primeSubsetModulus d) : Real)| *
              |(controllerProgressionMass h
                  (primeSubsetModulus d)
                  (translatedSubsetClass e a d) Y Z : Real) -
                base / (primeSubsetModulus d : Real)| := by
      congr 1
      calc
        (∑ d ∈ P.powerset,
            (W.weight (primeSubsetModulus d) : Real) *
              (base / (primeSubsetModulus d : Real))) =
            base *
              ∑ d ∈ P.powerset,
                (W.weight (primeSubsetModulus d) : Real) /
                  (primeSubsetModulus d : Real) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _hd
          ring
        _ =
            base *
              ∑ n ∈ (primeSubsetModulus P).divisors,
                (W.weight n : Real) / (n : Real) := by
          rw [subset_weighted_reciprocal_sum_eq_divisor_sum]

/--
Real form of (2.16), followed by the exact main-term/discrepancy
decomposition used in (2.17).
-/
theorem translatedLayer_card_le_beta_main_add_discrepancy
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z level : Nat)
    (W :
      BetaUpperSieveWeights
        (primeSubsetModulus (oldControllerPrimes h z)) level)
    (base : Real) :
    ((translatedLayerSurvivors h z e a Y Z).card : Real) ≤
      base *
          (∑ n ∈
              (primeSubsetModulus
                (oldControllerPrimes h z)).divisors,
            (W.weight n : Real) / (n : Real)) +
        ∑ d ∈ (oldControllerPrimes h z).powerset,
          |(W.weight (primeSubsetModulus d) : Real)| *
            |(controllerProgressionMass h
                (primeSubsetModulus d)
                (translatedSubsetClass e a d) Y Z : Real) -
              base / (primeSubsetModulus d : Real)| := by
  have hsieveInt :=
    translatedLayer_upperSieve_bound_crt_beta
      h z e a Y Z level W
  have hsieveReal :
      ((translatedLayerSurvivors h z e a Y Z).card : Real) ≤
        ∑ d ∈ (oldControllerPrimes h z).powerset,
          (W.weight (primeSubsetModulus d) : Real) *
            (controllerProgressionMass h
              (primeSubsetModulus d)
              (translatedSubsetClass e a d) Y Z : Real) := by
    exact_mod_cast hsieveInt
  exact hsieveReal.trans
    (beta_progression_sum_le_main_add_discrepancy
      h z e Y Z level a W base)

/--
Abstract final form of (2.17): once the fundamental-lemma main sum and the
Bombieri--Vinogradov discrepancy sum are bounded, the layer survivor count
obeys their stated combination.
-/
theorem translatedLayer_card_le_of_beta_and_distribution
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z level : Nat)
    (W :
      BetaUpperSieveWeights
        (primeSubsetModulus (oldControllerPrimes h z)) level)
    (base mainBound distributionError : Real)
    (hbase : 0 ≤ base)
    (hfundamental :
      (∑ n ∈
          (primeSubsetModulus
            (oldControllerPrimes h z)).divisors,
        (W.weight n : Real) / (n : Real)) ≤ mainBound)
    (hdistribution :
      (∑ d ∈ (oldControllerPrimes h z).powerset,
          |(W.weight (primeSubsetModulus d) : Real)| *
            |(controllerProgressionMass h
                (primeSubsetModulus d)
                (translatedSubsetClass e a d) Y Z : Real) -
              base / (primeSubsetModulus d : Real)|) ≤
        distributionError) :
    ((translatedLayerSurvivors h z e a Y Z).card : Real) ≤
      base * mainBound + distributionError := by
  refine
    (translatedLayer_card_le_beta_main_add_discrepancy
      h z e a Y Z level W base).trans ?_
  gcongr

end Erdos279
