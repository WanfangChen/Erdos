import Erdos279.BetaSieveBridge
import Erdos279.GlobalOldPrimeSieve

/-!
# Applying natural beta-sieve weights to the old-prime sieve

These are equation (2.16) and its all-layer version, now stated with the
paper's natural divisor-indexed weights `λ⁺ d`.
-/

namespace Erdos279

open Finset

/-- Equation (2.16) with natural divisor-indexed upper-sieve weights. -/
theorem translatedLayer_upperSieve_bound_crt_natural
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat)
    (W :
      NaturalUpperSieveWeights
        (primeSubsetModulus (oldControllerPrimes h z))) :
    ((translatedLayerSurvivors h z e a Y Z).card : Int) ≤
      ∑ d ∈ (oldControllerPrimes h z).powerset,
        W.weight (primeSubsetModulus d) *
          controllerProgressionMass h
            (primeSubsetModulus d)
            (translatedSubsetClass e a d) Y Z := by
  simpa using
    translatedLayer_upperSieve_bound_crt
      h z e a Y Z (W.toSubset (oldControllerPrimes h z))

/-- Equation (2.16) specialized to a full beta-sieve weight package. -/
theorem translatedLayer_upperSieve_bound_crt_beta
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z level : Nat)
    (W :
      BetaUpperSieveWeights
        (primeSubsetModulus (oldControllerPrimes h z)) level) :
    ((translatedLayerSurvivors h z e a Y Z).card : Int) ≤
      ∑ d ∈ (oldControllerPrimes h z).powerset,
        W.weight (primeSubsetModulus d) *
          controllerProgressionMass h
            (primeSubsetModulus d)
            (translatedSubsetClass e a d) Y Z := by
  exact translatedLayer_upperSieve_bound_crt_natural
    h z e a Y Z W.toNatural

/--
All-layer old-prime sieve bound, with a natural beta-sieve package allowed
to depend on the hard exponent.
-/
theorem hardSurvivors_upperSieve_bound_crt_natural
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat)
    (W :
      (e : Nat) →
        NaturalUpperSieveWeights
          (primeSubsetModulus (oldControllerPrimes h z))) :
    ((hardSurvivors h z a X Z).card : Int) ≤
      ∑ e ∈ hardExponentRange Z,
        ∑ d ∈ (oldControllerPrimes h z).powerset,
          (W e).weight (primeSubsetModulus d) *
            controllerProgressionMass h
              (primeSubsetModulus d)
              (translatedSubsetClass e a d)
              (X / h.1 ^ e) (Z / h.1 ^ e) := by
  simpa using
    hardSurvivors_upperSieve_bound_crt
      h z a X Z
      (fun e => (W e).toSubset (oldControllerPrimes h z))

/-- All-layer specialization to full beta-sieve packages. -/
theorem hardSurvivors_upperSieve_bound_crt_beta
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat)
    (level : Nat → Nat)
    (W :
      (e : Nat) →
        BetaUpperSieveWeights
          (primeSubsetModulus (oldControllerPrimes h z)) (level e)) :
    ((hardSurvivors h z a X Z).card : Int) ≤
      ∑ e ∈ hardExponentRange Z,
        ∑ d ∈ (oldControllerPrimes h z).powerset,
          (W e).weight (primeSubsetModulus d) *
            controllerProgressionMass h
              (primeSubsetModulus d)
              (translatedSubsetClass e a d)
              (X / h.1 ^ e) (Z / h.1 ^ e) := by
  exact hardSurvivors_upperSieve_bound_crt_natural
    h z a X Z (fun e => (W e).toNatural)

end Erdos279
