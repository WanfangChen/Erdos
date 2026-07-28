import Erdos279.HardLayerCounting
import Erdos279.SieveCRT

/-!
# The old-prime sieve summed over every hard layer

This module assembles the exact ingredients proved earlier:

* canonical, disjoint `h`-adic layers;
* translation of old residue classes in each layer;
* CRT compression of every upper-sieve fibre.

The resulting theorem is the complete finite-combinatorial reduction behind
Proposition 2.1.  No asymptotic theorem is used here: all remaining work for
that proposition is an estimate of the displayed progression masses.
-/

namespace Erdos279

open Finset

/--
The hard survivor count is exactly the sum of the translated survivor counts
over all possible canonical hub exponents.
-/
theorem hardSurvivors_card_eq_sum_translatedLayers
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card =
      ∑ e ∈ hardExponentRange Z,
        (translatedLayerSurvivors h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card := by
  rw [hardSurvivors_card_eq_sum_layerUnits]
  apply Finset.sum_congr rfl
  intro e _he
  rw [hardLayerUnits_eq_translated]

/--
Global finite old-prime sieve inequality.  The weights may depend on the
layer.  Every term on the right is the exact arithmetic-progression mass
`A_d(I,b)` occurring in equation (2.16).
-/
theorem hardSurvivors_upperSieve_bound_crt
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat)
    (W :
      (e : Nat) →
        UpperSubsetSieveWeights (oldControllerPrimes h z)) :
    ((hardSurvivors h z a X Z).card : Int) ≤
      ∑ e ∈ hardExponentRange Z,
        ∑ d ∈ (oldControllerPrimes h z).powerset,
          (W e).weight d *
            controllerProgressionMass h
              (primeSubsetModulus d)
              (translatedSubsetClass e a d)
              (X / h.1 ^ e) (Z / h.1 ^ e) := by
  calc
    ((hardSurvivors h z a X Z).card : Int) =
        ∑ e ∈ hardExponentRange Z,
          ((translatedLayerSurvivors h z e a
            (X / h.1 ^ e) (Z / h.1 ^ e)).card : Int) := by
      exact_mod_cast
        hardSurvivors_card_eq_sum_translatedLayers h z a X Z
    _ ≤
        ∑ e ∈ hardExponentRange Z,
          ∑ d ∈ (oldControllerPrimes h z).powerset,
            (W e).weight d *
              controllerProgressionMass h
                (primeSubsetModulus d)
                (translatedSubsetClass e a d)
                (X / h.1 ^ e) (Z / h.1 ^ e) := by
      apply Finset.sum_le_sum
      intro e _he
      exact translatedLayer_upperSieve_bound_crt
        h z e a (X / h.1 ^ e) (Z / h.1 ^ e) (W e)

end Erdos279
