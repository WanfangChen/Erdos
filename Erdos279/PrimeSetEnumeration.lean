import Erdos279.MeshScheduledConstruction
import Mathlib.Data.Nat.Nth

/-!
# Canonical enumeration of infinite prime predicates

This file removes arbitrary sequence choices from the analytic interface.
An infinite predicate on project primes is enumerated canonically by
`Nat.nth` on the underlying natural values.  The resulting sequence is
injective, lies in the predicate, and is surjective onto it.
-/

namespace Erdos279

open Filter

/-- The natural-number predicate underlying a predicate on project primes. -/
def primeNatPredicate (P : Prime → Prop) (n : Nat) : Prop :=
  ∃ hn : IsPrime n, P ⟨n, hn⟩

/-- Canonical increasing enumeration of an infinite prime predicate. -/
noncomputable def enumeratePrimePredicate
    (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P)))
    (i : Nat) : Prime := by
  have hmem :
      primeNatPredicate P
        (Nat.nth (primeNatPredicate P) i) :=
    Nat.nth_mem_of_infinite hInf i
  exact
    ⟨Nat.nth (primeNatPredicate P) i,
      Classical.choose hmem⟩

@[simp]
theorem enumeratePrimePredicate_val
    (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P)))
    (i : Nat) :
    (enumeratePrimePredicate P hInf i).1 =
      Nat.nth (primeNatPredicate P) i :=
  rfl

theorem enumeratePrimePredicate_mem
    (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P)))
    (i : Nat) :
    P (enumeratePrimePredicate P hInf i) := by
  have hmem :
      primeNatPredicate P
        (Nat.nth (primeNatPredicate P) i) :=
    Nat.nth_mem_of_infinite hInf i
  exact (Classical.choose_spec hmem)

theorem enumeratePrimePredicate_injective
    (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P))) :
    Function.Injective (enumeratePrimePredicate P hInf) := by
  intro i j hij
  apply (Nat.nth_injective hInf)
  exact congrArg Subtype.val hij

theorem enumeratePrimePredicate_surjective
    (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P))) :
    ∀ p, P p →
      ∃ i, enumeratePrimePredicate P hInf i = p := by
  intro p hp
  have hpNat : primeNatPredicate P p.1 :=
    ⟨p.2, hp⟩
  have hpRange :
      p.1 ∈ Set.range (Nat.nth (primeNatPredicate P)) := by
    rw [Nat.range_nth_of_infinite hInf]
    exact hpNat
  obtain ⟨i, hi⟩ := hpRange
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact hi

/-- Canonical nth enumerations for the periodic reservoir and complementary
prime targets, with the sole analytic input being their ratio limit. -/
noncomputable def periodicComplementaryEnumerationsOfNth
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hPeriodic :
      Set.Infinite
        (setOf
          (primeNatPredicate
            (InPeriodicReservoir h L R H))))
    (hComplementary :
      Set.Infinite
        (setOf
          (primeNatPredicate
            (IsComplementaryPrimeTarget h H))))
    (ratio : Real)
    (hratio :
      Tendsto
        (fun i =>
          ((enumeratePrimePredicate
            (InPeriodicReservoir h L R H)
            hPeriodic i).1 : Real) /
          ((enumeratePrimePredicate
            (IsComplementaryPrimeTarget h H)
            hComplementary i).1 : Real))
        atTop (nhds ratio)) :
    PeriodicComplementaryEnumerations h L R H where
  periodic :=
    enumeratePrimePredicate
      (InPeriodicReservoir h L R H) hPeriodic
  complementary :=
    enumeratePrimePredicate
      (IsComplementaryPrimeTarget h H) hComplementary
  periodic_injective :=
    enumeratePrimePredicate_injective _ hPeriodic
  complementary_injective :=
    enumeratePrimePredicate_injective _ hComplementary
  periodic_mem :=
    enumeratePrimePredicate_mem _ hPeriodic
  complementary_mem :=
    enumeratePrimePredicate_mem _ hComplementary
  complementary_surjective :=
    enumeratePrimePredicate_surjective _ hComplementary
  ratio := ratio
  ratio_tendsto := hratio

end Erdos279
