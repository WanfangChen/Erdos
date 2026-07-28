import Erdos279.SquarefreeDivisorIndexing
import Erdos279.UpperSieveCombinatorics

/-!
# Natural beta-sieve weights and subset weights

The paper writes upper-bound beta-sieve weights as integers
`λ⁺ d`, indexed by divisors of the squarefree sieving modulus.  The finite
combinatorial sieve in this project is indexed by subsets of its prime
conditions.  This file proves that the two formulations are exactly
equivalent for the direction used in the proof.
-/

namespace Erdos279

open Finset

/--
Natural-number form of the upper-sieve majorization property

`1_{L = 1} ≤ ∑_{d ∣ L} λ⁺ d`

for every divisor `L` of the fixed sieving modulus.
-/
structure NaturalUpperSieveWeights (P : Nat) where
  weight : Nat → Int
  majorizes :
    ∀ L : Nat, L ∣ P →
      (if L = 1 then 1 else 0) ≤
        ∑ d ∈ L.divisors, weight d

/--
The full finite package of beta-sieve properties used in (2.12)--(2.13).
The `level` parameter is the cutoff denoted by `D_Y` in the paper.
-/
structure BetaUpperSieveWeights (P level : Nat) where
  weight : Nat → Int
  abs_weight_le_one : ∀ d : Nat, |weight d| ≤ 1
  supported :
    ∀ d : Nat, weight d ≠ 0 →
      d ∣ P ∧ Squarefree d ∧ d ≤ level
  majorizes :
    ∀ L : Nat, L ∣ P →
      (if L = 1 then 1 else 0) ≤
        ∑ d ∈ L.divisors, weight d

/-- Forget the size and support information, retaining upper majorization. -/
def BetaUpperSieveWeights.toNatural
    {P level : Nat} (W : BetaUpperSieveWeights P level) :
    NaturalUpperSieveWeights P where
  weight := W.weight
  majorizes := W.majorizes

@[simp]
theorem BetaUpperSieveWeights.toNatural_weight
    {P level : Nat} (W : BetaUpperSieveWeights P level)
    (d : Nat) :
    W.toNatural.weight d = W.weight d := rfl

/-- A prime-subset modulus is `1` precisely for the empty subset. -/
theorem primeSubsetModulus_eq_one_iff
    (d : Finset Prime) :
    primeSubsetModulus d = 1 ↔ d = ∅ := by
  classical
  constructor
  · intro hprod
    by_contra hne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hpdiv :
        p.1 ∣ primeSubsetModulus d := by
      rw [primeSubsetModulus]
      exact Finset.dvd_prod_of_mem (fun q : Prime => q.1) hp
    rw [hprod] at hpdiv
    have hple : p.1 ≤ 1 :=
      Nat.le_of_dvd (by omega) hpdiv
    have hptwo : 2 ≤ p.1 := p.natPrime.two_le
    omega
  · rintro rfl
    simp [primeSubsetModulus]

/-- Products respect inclusion of finite prime subsets. -/
theorem primeSubsetModulus_dvd_of_subset
    {d P : Finset Prime} (hd : d ⊆ P) :
    primeSubsetModulus d ∣ primeSubsetModulus P := by
  simpa [primeSubsetModulus] using
    (Finset.prod_dvd_prod_of_subset
      d P (fun p : Prime => p.1) hd)

/--
Every natural divisor-indexed upper-sieve weight induces a subset-indexed
weight by evaluating it on the product of the subset.
-/
noncomputable def NaturalUpperSieveWeights.toSubset
    (P : Finset Prime)
    (W : NaturalUpperSieveWeights (primeSubsetModulus P)) :
    UpperSubsetSieveWeights P where
  weight d := W.weight (primeSubsetModulus d)
  majorizes L hL := by
    have hmajor :=
      W.majorizes (primeSubsetModulus L)
        (primeSubsetModulus_dvd_of_subset hL)
    rw [sum_primeSubsetModulus_divisors_eq_primePowerset] at hmajor
    simpa [primeSubsetModulus_eq_one_iff] using hmajor

@[simp]
theorem NaturalUpperSieveWeights.toSubset_weight
    (P : Finset Prime)
    (W : NaturalUpperSieveWeights (primeSubsetModulus P))
    (d : Finset Prime) :
    (W.toSubset P).weight d =
      W.weight (primeSubsetModulus d) := rfl

/-- The subset-indexed weight obtained from a full beta-sieve package. -/
noncomputable def BetaUpperSieveWeights.toSubset
    (P : Finset Prime) {level : Nat}
    (W : BetaUpperSieveWeights (primeSubsetModulus P) level) :
    UpperSubsetSieveWeights P :=
  W.toNatural.toSubset P

@[simp]
theorem BetaUpperSieveWeights.toSubset_weight
    (P : Finset Prime) {level : Nat}
    (W : BetaUpperSieveWeights (primeSubsetModulus P) level)
    (d : Finset Prime) :
    (W.toSubset P).weight d =
      W.weight (primeSubsetModulus d) := rfl

theorem BetaUpperSieveWeights.subset_abs_weight_le_one
    (P : Finset Prime) {level : Nat}
    (W : BetaUpperSieveWeights (primeSubsetModulus P) level)
    (d : Finset Prime) :
    |(W.toSubset P).weight d| ≤ 1 := by
  simpa using W.abs_weight_le_one (primeSubsetModulus d)

theorem BetaUpperSieveWeights.subset_weight_eq_zero_of_level_lt
    (P : Finset Prime) {level : Nat}
    (W : BetaUpperSieveWeights (primeSubsetModulus P) level)
    (d : Finset Prime)
    (hd : level < primeSubsetModulus d) :
    (W.toSubset P).weight d = 0 := by
  by_contra hne
  have hsupp :=
    W.supported (primeSubsetModulus d) (by simpa using hne)
  omega

/--
The subset-indexed reciprocal sum is literally the conventional
divisor-indexed beta-sieve sum.
-/
theorem subset_weighted_reciprocal_sum_eq_divisor_sum
    (P : Finset Prime) (weight : Nat → Int) :
    (∑ d ∈ P.powerset,
        (weight (primeSubsetModulus d) : Real) /
          (primeSubsetModulus d : Real)) =
      ∑ n ∈ (primeSubsetModulus P).divisors,
        (weight n : Real) / (n : Real) := by
  simpa using
    (sum_primeSubsetModulus_divisors_eq_primePowerset
      (α := Real) P
      (fun n => (weight n : Real) / (n : Real))).symm

/-- The same exact reindexing for the absolute-weight error sum. -/
theorem subset_abs_weighted_reciprocal_sum_eq_divisor_sum
    (P : Finset Prime) (weight : Nat → Int) :
    (∑ d ∈ P.powerset,
        (|weight (primeSubsetModulus d)| : Real) /
          (primeSubsetModulus d : Real)) =
      ∑ n ∈ (primeSubsetModulus P).divisors,
        (|weight n| : Real) / (n : Real) := by
  simpa using
    (sum_primeSubsetModulus_divisors_eq_primePowerset
      (α := Real) P
      (fun n => (|weight n| : Real) / (n : Real))).symm

end Erdos279
