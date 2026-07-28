import Erdos279.ControllerDivergenceFromPNT
import Erdos279.IntegralHardReduction

/-!
# Final reduction to fixed-progression PNT and the hard sieve bound

Reciprocal divergence is no longer an independent input.  One universal
fixed-modulus PNT supplies:

* the controller reciprocal divergence used to build the density mesh;
* the periodic-reservoir PNT for that mesh;
* the complementary-prime PNT for that mesh.

Thus only the fixed-progression PNT and the uniform hard-survivor estimate
remain in the levelwise analytic package.
-/

namespace Erdos279

/-- Prime number theorem in every fixed reduced arithmetic progression. -/
def AllFixedProgressionPrimeNumberTheorems : Prop :=
  ∀ q : Nat, FixedProgressionPrimeNumberTheorem q

/-- Minimal levelwise analytic package after reciprocal divergence and all
elementary parameter choices have been discharged. -/
structure FixedPNTHardInputs (k : Nat) where
  Csv : Real
  Csv_nonneg : 0 ≤ Csv
  v : Nat
  one_le_v : 1 ≤ v
  fixedPNT : AllFixedProgressionPrimeNumberTheorems
  hardUpperBound :
    ∀ {h : Prime}
      (hh : 3 ≤ h.1)
      (hkpos : 0 < k)
      (hlarge : 256 * k ≤ h.1)
      (M : OldControllerPrimeDensityMesh h k)
      (A : MeshFixedProgressionPNTInputs M)
      (T : TailPrimeTargetMatching
        (A.toMeshPrimeEnumerations
          (hh := hh)
          (hk := hkpos)).enumerations.periodic
        (A.toMeshPrimeEnumerations
          (hh := hh)
          (hk := hkpos)).enumerations.complementary k),
      HasMeshHardStageUpperBound
        (A.toMeshPrimeEnumerations
          (hh := hh)
          (hk := hkpos))
        T
        (integralStageRatio k h.1)
        (hardSurvivorCoefficient
          Csv v (integralStageRatio k h.1) h)

namespace FixedPNTHardInputs

/-- The universal fixed-PNT hypothesis constructs all of the older
`IntegralHardInputs` fields. -/
noncomputable def toIntegralHardInputs
    {k : Nat} (I : FixedPNTHardInputs k) :
    IntegralHardInputs k where
  Csv := I.Csv
  Csv_nonneg := I.Csv_nonneg
  v := I.v
  one_le_v := I.one_le_v
  controllerDiverges := fun h =>
    controllerPrimeReciprocalDiverges_of_fixedProgressionPNT
      h (I.fixedPNT h.1)
  fixedProgressionPNT := fun {h} M =>
    { periodicPNT :=
        I.fixedPNT (h.1 * M.modulus.1)
      complementaryPNT :=
        I.fixedPNT
          (h.1 *
            primeSubsetModulus
              (oldControllerPrimes h M.cutoff)) }
  hardUpperBound := by
    intro h hh hkpos hlarge M A T
    exact I.hardUpperBound hh hkpos hlarge M A T

end FixedPNTHardInputs

/-- Fixed-progression PNT plus the paper's hard-survivor estimate prove
the fixed-level statement. -/
theorem P_of_fixedPNTHardInputs
    {k : Nat} (hk : 3 ≤ k)
    (I : FixedPNTHardInputs k) :
    P k :=
  P_of_integralHardInputs hk I.toIntegralHardInputs

/-- Levelwise reduced analytic packages prove Erdős 279 globally. -/
theorem globalAffirmative_of_fixedPNTHardInputs
    (I : ∀ k : Nat, 3 ≤ k → FixedPNTHardInputs k) :
    GlobalAffirmative := by
  intro k hk
  exact P_of_fixedPNTHardInputs hk (I k hk)

end Erdos279
