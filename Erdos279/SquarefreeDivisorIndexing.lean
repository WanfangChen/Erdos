import Erdos279.SieveArithmetic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Divisors of a squarefree product as subsets of its primes

Beta-sieve weights are conventionally indexed by natural divisors, while the
deterministic sieve in this project is indexed by finite subsets of project
primes.  This file establishes the exact finite bridge.
-/

namespace Erdos279

open Finset

/-- The natural prime factors of a project-prime product are exactly its values. -/
theorem primeFactors_primeSubsetModulus
    (d : Finset Prime) :
    (primeSubsetModulus d).primeFactors =
      d.image (fun p : Prime => p.1) := by
  classical
  have hprime :
      ∀ n ∈ d.image (fun p : Prime => p.1), n.Prime := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨p, _hp, rfl⟩
    exact p.natPrime
  have hfactor :=
    Nat.primeFactors_prod hprime
  simpa [primeSubsetModulus] using hfactor

/--
For a nonzero squarefree number, summing over divisors is exactly summing
over all subsets of its natural prime factors.
-/
theorem sum_divisors_eq_sum_primeFactors_powerset
    {α : Type*} [AddCommMonoid α]
    {n : Nat} (hn : n ≠ 0) (hsq : Squarefree n)
    (f : Nat → α) :
    (∑ r ∈ n.divisors, f r) =
      ∑ s ∈ n.primeFactors.powerset,
        f (∏ p ∈ s, p) := by
  classical
  calc
    (∑ r ∈ n.divisors, f r) =
        ∑ r ∈ n.divisors with Squarefree r, f r := by
      rw [Nat.divisors_filter_squarefree_of_squarefree hsq]
    _ = ∑ s ∈ n.primeFactors.powerset,
          f (∏ p ∈ s, p) := by
      simpa [Nat.factors_eq] using
        (Nat.sum_divisors_filter_squarefree
          (α := α) (f := f) hn)

/-- Specialization to a finite product of project primes. -/
theorem sum_primeSubsetModulus_divisors_eq_natPowerset
    {α : Type*} [AddCommMonoid α]
    (d : Finset Prime) (f : Nat → α) :
    (∑ r ∈ (primeSubsetModulus d).divisors, f r) =
      ∑ s ∈ (d.image (fun p : Prime => p.1)).powerset,
        f (∏ p ∈ s, p) := by
  rw [sum_divisors_eq_sum_primeFactors_powerset
    (primeSubsetModulus_ne_zero d)
    (primeSubsetModulus_squarefree d),
    primeFactors_primeSubsetModulus]

/--
Mapping a subset of project primes to its underlying natural values gives a
bijection between the two powersets, and it preserves the attached product.
-/
theorem sum_natPowerset_eq_sum_primePowerset
    {α : Type*} [AddCommMonoid α]
    (d : Finset Prime) (f : Nat → α) :
    (∑ s ∈ (d.image (fun p : Prime => p.1)).powerset,
        f (∏ p ∈ s, p)) =
      ∑ t ∈ d.powerset, f (primeSubsetModulus t) := by
  classical
  symm
  refine Finset.sum_bij
    (fun t _ht => t.image (fun p : Prime => p.1)) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_powerset] at ht ⊢
    exact Finset.image_subset_image ht
  · intro t₁ ht₁ t₂ ht₂ heq
    change
      t₁.image (fun p : Prime => p.1) =
        t₂.image (fun p : Prime => p.1) at heq
    exact Finset.image_injective Subtype.val_injective heq
  · intro s hs
    have hsSub :
        s ⊆ d.image (fun p : Prime => p.1) :=
      Finset.mem_powerset.mp hs
    let t : Finset Prime :=
      d.filter fun p => p.1 ∈ s
    have ht : t ∈ d.powerset := by
      exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    refine ⟨t, ht, ?_⟩
    ext n
    constructor
    · intro hn
      rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
      exact (Finset.mem_filter.mp hp).2
    · intro hn
      rcases Finset.mem_image.mp (hsSub hn) with ⟨p, hp, hpval⟩
      apply Finset.mem_image.mpr
      refine ⟨p, ?_, hpval⟩
      exact Finset.mem_filter.mpr ⟨hp, hpval ▸ hn⟩
  · intro t ht
    rw [primeSubsetModulus]
    exact congrArg f
      (Finset.prod_image
        (s := t)
        (f := fun n : Nat => n)
        Subtype.val_injective.injOn).symm

/--
For a product of project primes, the natural divisor sum is exactly the sum
over project-prime subsets.  This is the index conversion used by the
beta-sieve upper weights.
-/
theorem sum_primeSubsetModulus_divisors_eq_primePowerset
    {α : Type*} [AddCommMonoid α]
    (d : Finset Prime) (f : Nat → α) :
    (∑ r ∈ (primeSubsetModulus d).divisors, f r) =
      ∑ s ∈ d.powerset, f (primeSubsetModulus s) := by
  rw [sum_primeSubsetModulus_divisors_eq_natPowerset,
    sum_natPowerset_eq_sum_primePowerset]

end Erdos279
