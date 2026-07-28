import Erdos279.PrimeSetEnumeration

/-!
# Nth-prime asymptotics imply the matching ratio

For a prime predicate of density `d`, inversion of its counting asymptotic
has the standard form

`pₙ / (n log n) → 1/d`.

This file proves the elementary quotient step: nth-prime asymptotics for
the periodic and complementary sets imply the ratio limit required in
(3.6).
-/

namespace Erdos279

open Filter

/-- A common positive normalization for zero-indexed prime enumerations. -/
noncomputable def nthPrimeScale (n : Nat) : Real :=
  ((n + 2 : Nat) : Real) *
    Real.log ((n + 2 : Nat) : Real)

theorem nthPrimeScale_pos (n : Nat) :
    0 < nthPrimeScale n := by
  unfold nthPrimeScale
  have hn : (1 : Real) < ((n + 2 : Nat) : Real) := by
    exact_mod_cast (by omega : 1 < n + 2)
  exact mul_pos (by positivity) (Real.log_pos hn)

theorem nthPrimeScale_ne_zero (n : Nat) :
    nthPrimeScale n ≠ 0 :=
  (nthPrimeScale_pos n).ne'

/-- The inverted prime-counting asymptotic for one prime predicate. -/
def HasNthPrimeAsymptotic
    (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P)))
    (density : Real) : Prop :=
  Tendsto
    (fun n =>
      ((enumeratePrimePredicate P hInf n).1 : Real) /
        nthPrimeScale n)
    atTop (nhds (1 / density))

/-- Quotienting two nth-prime asymptotics cancels the common `n log n`
normalization. -/
theorem ratio_tendsto_of_nthPrimeAsymptotics
    (P Q : Prime → Prop)
    (hP : Set.Infinite (setOf (primeNatPredicate P)))
    (hQ : Set.Infinite (setOf (primeNatPredicate Q)))
    {densityP densityQ : Real}
    (hdP : 0 < densityP) (hdQ : 0 < densityQ)
    (hAsymP : HasNthPrimeAsymptotic P hP densityP)
    (hAsymQ : HasNthPrimeAsymptotic Q hQ densityQ) :
    Tendsto
      (fun n =>
        ((enumeratePrimePredicate P hP n).1 : Real) /
          ((enumeratePrimePredicate Q hQ n).1 : Real))
      atTop (nhds (densityQ / densityP)) := by
  have hlimit :
      Tendsto
        (fun n =>
          (((enumeratePrimePredicate P hP n).1 : Real) /
              nthPrimeScale n) /
            (((enumeratePrimePredicate Q hQ n).1 : Real) /
              nthPrimeScale n))
        atTop
        (nhds ((1 / densityP) / (1 / densityQ))) :=
    hAsymP.div hAsymQ (by
      exact one_div_ne_zero hdQ.ne')
  have hsource :
      (fun n =>
        ((enumeratePrimePredicate P hP n).1 : Real) /
          ((enumeratePrimePredicate Q hQ n).1 : Real)) =ᶠ[atTop]
      (fun n =>
        (((enumeratePrimePredicate P hP n).1 : Real) /
            nthPrimeScale n) /
          (((enumeratePrimePredicate Q hQ n).1 : Real) /
            nthPrimeScale n)) := by
    apply Eventually.of_forall
    intro n
    have hscale := nthPrimeScale_ne_zero n
    have hq :
        ((enumeratePrimePredicate Q hQ n).1 : Real) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt
          (enumeratePrimePredicate Q hQ n).pos)
    field_simp
  have hratio :
      Tendsto
        (fun n =>
          ((enumeratePrimePredicate P hP n).1 : Real) /
            ((enumeratePrimePredicate Q hQ n).1 : Real))
        atTop
        (nhds ((1 / densityP) / (1 / densityQ))) :=
    Tendsto.congr' hsource.symm hlimit
  simpa [div_eq_mul_inv, mul_comm] using hratio

/-- Nth-prime PNT inputs for the two predicates selected by a density
mesh. -/
structure MeshNthPrimeInputs
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) where
  periodic_infinite :
    Set.Infinite
      (setOf
        (primeNatPredicate
          (InPeriodicReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff))))
  complementary_infinite :
    Set.Infinite
      (setOf
        (primeNatPredicate
          (IsComplementaryPrimeTarget h
            (oldControllerPrimes h M.cutoff))))
  periodic_asymptotic :
    HasNthPrimeAsymptotic
      (InPeriodicReservoir
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff))
      periodic_infinite M.periodicDensity
  complementary_asymptotic :
    HasNthPrimeAsymptotic
      (IsComplementaryPrimeTarget h
        (oldControllerPrimes h M.cutoff))
      complementary_infinite
      (controllerComplementDensity h
        (oldControllerPrimes h M.cutoff))

namespace MeshNthPrimeInputs

/-- The two nth-prime asymptotics construct the exact enumeration object
consumed by the prime-target matching. -/
noncomputable def toMeshPrimeEnumerations
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (A : MeshNthPrimeInputs M)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    MeshPrimeEnumerations M := by
  have hPeriodic : 0 < M.periodicDensity :=
    M.periodicDensity_pos hh hk
  have hH :
      ∀ p ∈ oldControllerPrimes h M.cutoff,
        InControllerProgression h p := by
    intro p hp
    exact (mem_oldControllerPrimes.mp hp).1
  have hComplementary :
      0 <
        controllerComplementDensity h
          (oldControllerPrimes h M.cutoff) :=
    controllerComplementDensity_pos
      h hh (oldControllerPrimes h M.cutoff) hH
  let ratio :=
    controllerComplementDensity h
        (oldControllerPrimes h M.cutoff) /
      M.periodicDensity
  have hratio :
      Tendsto
        (fun n =>
          ((enumeratePrimePredicate
            (InPeriodicReservoir
              h M.modulus M.classes
              (oldControllerPrimes h M.cutoff))
            A.periodic_infinite n).1 : Real) /
          ((enumeratePrimePredicate
            (IsComplementaryPrimeTarget h
              (oldControllerPrimes h M.cutoff))
            A.complementary_infinite n).1 : Real))
        atTop (nhds ratio) := by
    exact
      ratio_tendsto_of_nthPrimeAsymptotics
        _ _ A.periodic_infinite A.complementary_infinite
        hPeriodic hComplementary
        A.periodic_asymptotic
        A.complementary_asymptotic
  exact
    { enumerations :=
        periodicComplementaryEnumerationsOfNth
          h M.modulus M.classes
          (oldControllerPrimes h M.cutoff)
          A.periodic_infinite
          A.complementary_infinite
          ratio hratio
      ratio_eq := rfl }

end MeshNthPrimeInputs

end Erdos279
