import Erdos279.CountingToReciprocalDivergence
import Erdos279.ControllerReciprocalDensity
import Erdos279.ControllerPrimeExistence
import Erdos279.FixedProgressionPNT

/-!
# Controller reciprocal divergence from fixed-progression PNT

The density-mesh construction previously received reciprocal divergence
as a separate analytic input.  It is in fact an elementary consequence of
the fixed-modulus PNT already needed later.  This file proves the
conversion, including the exact equality between the project's
prime-subtype sum and the natural-number indicator partial sum.
-/

namespace Erdos279

open Filter

/-- Natural predicate for prime values in the controller progression. -/
def controllerPrimeNatPredicate
    (h : Prime) (n : Nat) : Prop :=
  primeNatPredicate (InControllerProgression h) n

/-- Dirichlet's theorem already supplies infinitude of the controller
predicate, independently of the quantitative PNT. -/
theorem controllerPrimeNatPredicate_infinite
    (h : Prime) :
    Set.Infinite
      (setOf (controllerPrimeNatPredicate h)) := by
  have hrange :
      Set.Infinite
        (Set.range
          (fun n : Nat =>
            (controllerPrimeSequence h n).1)) :=
    Set.infinite_range_of_injective
      (controllerPrimeSequence_strictMono h).injective
  apply hrange.mono
  rintro n ⟨i, rfl⟩
  exact
    ⟨(controllerPrimeSequence h i).2,
      controllerPrimeSequence_mem h i⟩

theorem controllerPrimeNatPredicate_pos
    (h : Prime) {n : Nat}
    (hn : controllerPrimeNatPredicate h n) :
    0 < n := by
  have hn2 : 2 ≤ n := (Classical.choose hn).1
  omega

/-- The project's controller predicate is exactly the reduced residue
class `1 mod h`. -/
theorem primeInModEq_one_iff_controller
    (h : Prime) (n : Nat) :
    PrimeInModEq h.1 1 n ↔
      controllerPrimeNatPredicate h n := by
  constructor
  · rintro ⟨hnPrime, hnMod⟩
    refine ⟨hnPrime, ?_⟩
    unfold InControllerProgression
    change n % h.1 = 1
    change n % h.1 = 1 % h.1 at hnMod
    simpa [Nat.mod_eq_of_lt h.one_lt] using hnMod
  · rintro ⟨hnPrime, hnController⟩
    refine ⟨hnPrime, ?_⟩
    unfold InControllerProgression at hnController
    change n % h.1 = 1 % h.1
    simpa [Nat.mod_eq_of_lt h.one_lt] using hnController

/-- Fixed-progression PNT gives the positive count density of controller
primes. -/
theorem controllerPrime_countingAsymptotic
    (h : Prime)
    (hPNT :
      FixedProgressionPrimeNumberTheorem h.1) :
    HasPrimeCountingAsymptotic
      (controllerPrimeNatPredicate h)
      (1 / (Nat.totient h.1 : Real)) := by
  have hclass :=
    hPNT 1 (Nat.coprime_one_left h.1)
  have heq :
      PrimeInModEq h.1 1 =
        controllerPrimeNatPredicate h := by
    funext n
    exact propext (primeInModEq_one_iff_controller h n)
  rwa [heq] at hclass

/-- Exact reindexing of the reciprocal sum from project primes to natural
values. -/
theorem controllerPrimeReciprocalSum_eq_indicator
    (h : Prime) (z : Nat) :
    controllerPrimeReciprocalSum h z =
      ∑ n ∈ Finset.range (z + 1),
        predicateReciprocalTerm
          (controllerPrimeNatPredicate h) n := by
  classical
  have hfiltered :
      (∑ n ∈
          (Finset.range (z + 1)).filter
            (controllerPrimeNatPredicate h),
          1 / (n : Real)) =
        ∑ p ∈ oldControllerPrimes h z,
          1 / (p.1 : Real) := by
    refine Finset.sum_bij
      (fun n hn =>
        (⟨n,
          Classical.choose
            ((Finset.mem_filter.mp hn).2)⟩ : Prime))
      ?_ ?_ ?_ ?_
    · intro n hn
      have hnData :=
        Finset.mem_filter.mp hn
      have hnController :
          InControllerProgression h
            (⟨n,
              Classical.choose hnData.2⟩ : Prime) :=
        Classical.choose_spec hnData.2
      apply mem_oldControllerPrimes.mpr
      constructor
      · exact hnController
      · change n ≤ z
        have hnRange :
            n < z + 1 :=
          Finset.mem_range.mp hnData.1
        omega
    · intro n₁ hn₁ n₂ hn₂ heq
      exact congrArg Subtype.val heq
    · intro p hp
      have hpData :=
        mem_oldControllerPrimes.mp hp
      have hpPred :
          controllerPrimeNatPredicate h p.1 :=
        ⟨p.2, hpData.1⟩
      refine ⟨p.1, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hpPred⟩, ?_⟩
      apply Subtype.ext
      rfl
    · intro n hn
      rfl
  unfold controllerPrimeReciprocalSum
  rw [← hfiltered]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  unfold predicateReciprocalTerm
  split_ifs <;> rfl

/--
The fixed-progression PNT implies exactly the reciprocal-divergence
property consumed by the density-mesh theorem.
-/
theorem controllerPrimeReciprocalDiverges_of_fixedProgressionPNT
    (h : Prime)
    (hPNT :
      FixedProgressionPrimeNumberTheorem h.1) :
    ControllerPrimeReciprocalDiverges h := by
  have htotient :
      0 < (Nat.totient h.1 : Real) := by
    exact_mod_cast
      (Nat.totient_pos.mpr h.pos)
  have hpartial :=
    predicateReciprocalSum_tendsto_atTop_of_counting
      (controllerPrimeNatPredicate h)
      (controllerPrimeNatPredicate_infinite h)
      (fun n hn =>
        controllerPrimeNatPredicate_pos h hn)
      (one_div_pos.mpr htotient)
      (controllerPrime_countingAsymptotic h hPNT)
  have hshifted :
      Tendsto
        (fun z : Nat =>
          ∑ n ∈ Finset.range (z + 1),
            predicateReciprocalTerm
              (controllerPrimeNatPredicate h) n)
        atTop atTop :=
    hpartial.comp (tendsto_add_atTop_nat 1)
  unfold ControllerPrimeReciprocalDiverges
  apply hshifted.congr'
  exact Filter.Eventually.of_forall
    (fun z =>
      (controllerPrimeReciprocalSum_eq_indicator
        h z).symm)

end Erdos279
