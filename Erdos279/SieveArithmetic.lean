import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Erdos279.SieveModulus

/-!
# Elementary arithmetic of squarefree sieve moduli

The analytic local-density statement uses only squarefree products of
distinct controller primes.  This file records their exact squarefreeness,
totient, and Euler-factor identities.
-/

namespace Erdos279

open Finset

theorem primeSubsetModulus_ne_zero (d : Finset Prime) :
    primeSubsetModulus d ≠ 0 := by
  classical
  rw [primeSubsetModulus]
  exact Finset.prod_ne_zero_iff.mpr fun p _hp =>
    Nat.ne_of_gt p.pos

theorem primeSubsetModulus_pos (d : Finset Prime) :
    0 < primeSubsetModulus d :=
  Nat.pos_of_ne_zero (primeSubsetModulus_ne_zero d)

/-- A product indexed by a finite set of distinct primes is squarefree. -/
theorem primeSubsetModulus_squarefree (d : Finset Prime) :
    Squarefree (primeSubsetModulus d) := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      simp [primeSubsetModulus]
  | @insert p d hpd ih =>
      have hcop :
          p.1.Coprime (∏ q ∈ d, q.1) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hqd
        exact
          (Nat.coprime_primes p.natPrime q.natPrime).mpr fun hpqval =>
            hpd (by
              have hpq : p = q := Subtype.ext hpqval
              simpa [hpq] using hqd)
      rw [primeSubsetModulus, Finset.prod_insert hpd]
      exact (Nat.squarefree_mul hcop).mpr
        ⟨p.natPrime.squarefree, by
          simpa [primeSubsetModulus] using ih⟩

/-- Exact totient formula for a squarefree prime-subset modulus. -/
theorem totient_primeSubsetModulus (d : Finset Prime) :
    Nat.totient (primeSubsetModulus d) =
      ∏ p ∈ d, (p.1 - 1) := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      simp [primeSubsetModulus]
  | @insert p d hpd ih =>
      have hcop :
          p.1.Coprime (∏ q ∈ d, q.1) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hqd
        exact
          (Nat.coprime_primes p.natPrime q.natPrime).mpr fun hpqval =>
            hpd (by
              have hpq : p = q := Subtype.ext hpqval
              simpa [hpq] using hqd)
      rw [primeSubsetModulus, Finset.prod_insert hpd,
        Nat.totient_mul hcop, Nat.totient_prime p.natPrime,
        Finset.prod_insert hpd]
      simpa [primeSubsetModulus] using congrArg (fun n => (p.1 - 1) * n) ih

/--
The rational local-density factor is the product of the expected Euler
factors `(1 - 1/p)`.
-/
theorem totientRatio_primeSubsetModulus (d : Finset Prime) :
    (Nat.totient (primeSubsetModulus d) : ℚ) /
        (primeSubsetModulus d : ℚ) =
      ∏ p ∈ d, (1 - ((p.1 : ℚ)⁻¹)) := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      norm_num [primeSubsetModulus]
  | @insert p d hpd ih =>
      have hcop :
          p.1.Coprime (∏ q ∈ d, q.1) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hqd
        exact
          (Nat.coprime_primes p.natPrime q.natPrime).mpr fun hpqval =>
            hpd (by
              have hpq : p = q := Subtype.ext hpqval
              simpa [hpq] using hqd)
      have hp0q : (p.1 : ℚ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt p.pos
      have hd0q : (primeSubsetModulus d : ℚ) ≠ 0 := by
        exact_mod_cast primeSubsetModulus_ne_zero d
      have hcop' :
          p.1.Coprime (primeSubsetModulus d) := by
        simpa [primeSubsetModulus] using hcop
      have hmodinsert :
          primeSubsetModulus (insert p d) =
            p.1 * primeSubsetModulus d := by
        simp [primeSubsetModulus, hpd]
      rw [Finset.prod_insert hpd]
      calc
        (Nat.totient (primeSubsetModulus (insert p d)) : ℚ) /
              (primeSubsetModulus (insert p d) : ℚ) =
            ((p.1 - 1 : Nat) : ℚ) / (p.1 : ℚ) *
              ((Nat.totient (primeSubsetModulus d) : ℚ) /
                (primeSubsetModulus d : ℚ)) := by
          rw [hmodinsert, Nat.totient_mul hcop',
            Nat.totient_prime p.natPrime]
          push_cast
          field_simp
        _ = ((p.1 - 1 : Nat) : ℚ) / (p.1 : ℚ) *
              ∏ q ∈ d, (1 - ((q.1 : ℚ)⁻¹)) := by rw [ih]
        _ = (1 - ((p.1 : ℚ)⁻¹)) *
              ∏ q ∈ d, (1 - ((q.1 : ℚ)⁻¹)) := by
          congr 1
          rw [Nat.cast_sub p.one_lt.le]
          push_cast
          field_simp

/-- The squarefree subset form of the Möbius weight `μ(r)/r`. -/
def subsetMobiusDensity (d : Finset Prime) : ℚ :=
  (-1 : ℚ) ^ d.card / (primeSubsetModulus d : ℚ)

theorem subsetMobiusDensity_eq_prod (d : Finset Prime) :
    subsetMobiusDensity d =
      ∏ p ∈ d, (-((p.1 : ℚ)⁻¹)) := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      norm_num [subsetMobiusDensity, primeSubsetModulus]
  | @insert p d hpd ih =>
      have hp0q : (p.1 : ℚ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt p.pos
      have hd0q : (primeSubsetModulus d : ℚ) ≠ 0 := by
        exact_mod_cast primeSubsetModulus_ne_zero d
      have hmodinsert :
          primeSubsetModulus (insert p d) =
            p.1 * primeSubsetModulus d := by
        simp [primeSubsetModulus, hpd]
      rw [subsetMobiusDensity, Finset.card_insert_of_not_mem hpd,
        hmodinsert, pow_succ, Finset.prod_insert hpd]
      rw [← ih]
      rw [subsetMobiusDensity]
      push_cast
      field_simp

/--
Exact finite inclusion-exclusion identity:
`∑_{r∣d} μ(r)/r = ∏_{p∣d}(1-1/p)`, with divisors indexed by subsets.
-/
theorem sum_subsetMobiusDensity (d : Finset Prime) :
    ∑ s ∈ d.powerset, subsetMobiusDensity s =
      ∏ p ∈ d, (1 - ((p.1 : ℚ)⁻¹)) := by
  classical
  calc
    ∑ s ∈ d.powerset, subsetMobiusDensity s =
        ∑ s ∈ d.powerset,
          ∏ p ∈ s, (-((p.1 : ℚ)⁻¹)) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [subsetMobiusDensity_eq_prod]
    _ = ∏ p ∈ d, (1 + (-((p.1 : ℚ)⁻¹))) := by
      symm
      exact Finset.prod_one_add d
    _ = ∏ p ∈ d, (1 - ((p.1 : ℚ)⁻¹)) := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [sub_eq_add_neg]

theorem sum_subsetMobiusDensity_eq_totientRatio (d : Finset Prime) :
    ∑ s ∈ d.powerset, subsetMobiusDensity s =
      (Nat.totient (primeSubsetModulus d) : ℚ) /
        (primeSubsetModulus d : ℚ) := by
  rw [sum_subsetMobiusDensity, totientRatio_primeSubsetModulus]

end Erdos279
