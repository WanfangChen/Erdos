import Erdos279.SquarefreeDivisorIndexing
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Euler-product identities for squarefree divisor sums

These are the exact finite identities used in the proof of Lemma 2.2.
-/

namespace Erdos279

open Finset

/-- The reciprocal divisor sum of a project-prime product is its finite
Euler product. -/
theorem reciprocal_divisor_sum_primeSubsetModulus
    (d : Finset Prime) :
    (∑ r ∈ (primeSubsetModulus d).divisors,
        (r : Real)⁻¹) =
      ∏ p ∈ d, (1 + (p.1 : Real)⁻¹) := by
  rw [sum_primeSubsetModulus_divisors_eq_primePowerset]
  calc
    (∑ s ∈ d.powerset,
        ((primeSubsetModulus s : Nat) : Real)⁻¹) =
        ∑ s ∈ d.powerset,
          ∏ p ∈ s, (p.1 : Real)⁻¹ := by
      apply Finset.sum_congr rfl
      intro s _hs
      simp [primeSubsetModulus]
    _ = ∏ p ∈ d, (1 + (p.1 : Real)⁻¹) := by
      simpa [add_comm] using
        (Finset.prod_add
          (fun p : Prime => (p.1 : Real)⁻¹)
          (fun _p : Prime => (1 : Real)) d).symm

/--
Generic logarithmic-derivative identity for a finite Euler product, stated
without logarithms so it can be reused for other additive weights.
-/
theorem powerset_prod_mul_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → Real)
    (hnonzero : ∀ i ∈ s, 1 + a i ≠ 0) :
    (∑ t ∈ s.powerset,
        (∏ i ∈ t, a i) * ∑ i ∈ t, b i) =
      (∏ i ∈ s, (1 + a i)) *
        ∑ i ∈ s, (a i * b i) / (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert x s hxs ih =>
      have hxnonzero : 1 + a x ≠ 0 :=
        hnonzero x (Finset.mem_insert_self x s)
      have hsnonzero : ∀ i ∈ s, 1 + a i ≠ 0 := by
        intro i hi
        exact hnonzero i (Finset.mem_insert_of_mem hi)
      have hih := ih hsnonzero
      rw [Finset.sum_powerset_insert hxs]
      have hsecond :
          (∑ t ∈ s.powerset,
              (∏ i ∈ insert x t, a i) *
                ∑ i ∈ insert x t, b i) =
            a x * b x * (∏ i ∈ s, (1 + a i)) +
              a x *
                (∑ t ∈ s.powerset,
                  (∏ i ∈ t, a i) * ∑ i ∈ t, b i) := by
        calc
          (∑ t ∈ s.powerset,
              (∏ i ∈ insert x t, a i) *
                ∑ i ∈ insert x t, b i) =
              ∑ t ∈ s.powerset,
                (a x * ∏ i ∈ t, a i) *
                  (b x + ∑ i ∈ t, b i) := by
            apply Finset.sum_congr rfl
            intro t ht
            have hxt : x ∉ t :=
              fun hmem =>
                hxs (Finset.mem_powerset.mp ht hmem)
            rw [Finset.prod_insert hxt, Finset.sum_insert hxt]
          _ =
              a x * b x *
                  (∑ t ∈ s.powerset, ∏ i ∈ t, a i) +
                a x *
                  (∑ t ∈ s.powerset,
                    (∏ i ∈ t, a i) * ∑ i ∈ t, b i) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, Finset.mul_sum,
              Finset.mul_sum]
            congr 1
            · apply Finset.sum_congr rfl
              intro t _ht
              ring
            · apply Finset.sum_congr rfl
              intro t _ht
              ring
          _ =
              a x * b x * (∏ i ∈ s, (1 + a i)) +
                a x *
                  (∑ t ∈ s.powerset,
                    (∏ i ∈ t, a i) * ∑ i ∈ t, b i) := by
            congr 2
            simpa [add_comm] using
              (Finset.prod_add a (fun _i : ι => (1 : Real)) s).symm
      rw [hsecond, hih, Finset.prod_insert hxs,
        Finset.sum_insert hxs]
      field_simp [hxnonzero]
      ring

/--
The logarithm of a project-prime subset modulus is the sum of the
logarithms of its prime factors.
-/
theorem log_primeSubsetModulus
    (d : Finset Prime) :
    Real.log (primeSubsetModulus d : Real) =
      ∑ p ∈ d, Real.log (p.1 : Real) := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      simp [primeSubsetModulus]
  | @insert p d hpd ih =>
      have hpne : (p.1 : Real) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt p.pos
      have hdne : (primeSubsetModulus d : Real) ≠ 0 := by
        exact_mod_cast primeSubsetModulus_ne_zero d
      rw [primeSubsetModulus, Finset.prod_insert hpd, Nat.cast_mul]
      change
        Real.log
            ((p.1 : Real) * (primeSubsetModulus d : Real)) =
          ∑ q ∈ insert p d, Real.log (q.1 : Real)
      rw [Real.log_mul hpne hdne, Finset.sum_insert hpd, ih]

/--
The logarithmically weighted reciprocal divisor sum used after (2.9).
-/
theorem log_reciprocal_divisor_sum_primeSubsetModulus
    (d : Finset Prime) :
    (∑ r ∈ (primeSubsetModulus d).divisors,
        Real.log (r : Real) / (r : Real)) =
      (∏ p ∈ d, (1 + (p.1 : Real)⁻¹)) *
        ∑ p ∈ d,
          Real.log (p.1 : Real) / (p.1 + 1 : Real) := by
  rw [sum_primeSubsetModulus_divisors_eq_primePowerset]
  calc
    (∑ s ∈ d.powerset,
        Real.log (primeSubsetModulus s : Real) /
          (primeSubsetModulus s : Real)) =
        ∑ s ∈ d.powerset,
          (∏ p ∈ s, (p.1 : Real)⁻¹) *
            ∑ p ∈ s, Real.log (p.1 : Real) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [log_primeSubsetModulus]
      have hinv :
          (primeSubsetModulus s : Real)⁻¹ =
            ∏ p ∈ s, (p.1 : Real)⁻¹ := by
        simp [primeSubsetModulus]
      rw [div_eq_mul_inv, hinv]
      ring
    _ =
        (∏ p ∈ d, (1 + (p.1 : Real)⁻¹)) *
          ∑ p ∈ d,
            ((p.1 : Real)⁻¹ * Real.log (p.1 : Real)) /
              (1 + (p.1 : Real)⁻¹) := by
      apply powerset_prod_mul_sum
      intro p _hp
      have hpPos : 0 < (p.1 : Real) := by
        exact_mod_cast p.pos
      positivity
    _ =
        (∏ p ∈ d, (1 + (p.1 : Real)⁻¹)) *
          ∑ p ∈ d,
            Real.log (p.1 : Real) / (p.1 + 1 : Real) := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _hp
      have hpne : (p.1 : Real) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt p.pos
      field_simp

end Erdos279
