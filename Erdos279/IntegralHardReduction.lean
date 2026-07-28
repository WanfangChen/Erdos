import Erdos279.IntegralStageRatio

/-!
# Reduction with the integral scale chosen automatically

This file closes the elementary parameter-selection loop.  For a fixed
level `k`, a sufficiently large hub prime has enough normalized capacity.
The integral ratio from `IntegralStageRatio` then supplies all scale
inequalities, and every density mesh for that hub has a strict surplus of
controller primes.

Consequently the only hypotheses left in `P_of_integralHardInputs` are
the three genuinely analytic statements used by the paper:

* reciprocal divergence in the controller progression;
* the two fixed-progression prime number theorems;
* the uniform upper bound for hard survivors.
-/

namespace Erdos279

/-- The analytic statements still required after all elementary parameter
choices at level `k` have been made explicit. -/
structure IntegralHardInputs (k : Nat) where
  Csv : Real
  Csv_nonneg : 0 ≤ Csv
  v : Nat
  one_le_v : 1 ≤ v
  controllerDiverges :
    ∀ h : Prime, ControllerPrimeReciprocalDiverges h
  fixedProgressionPNT :
    ∀ {h : Prime} (M : OldControllerPrimeDensityMesh h k),
      MeshFixedProgressionPNTInputs M
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

/--
All arithmetic choices in the paper are automatic: an
`IntegralHardInputs k` package proves `P k`.
-/
theorem P_of_integralHardInputs
    {k : Nat} (hk : 3 ≤ k)
    (I : IntegralHardInputs k) :
    P k := by
  have hscaled : 0 ≤ 4 * I.Csv := by
    exact mul_nonneg (by norm_num) I.Csv_nonneg
  obtain ⟨h, hlarge, hkh, hcap⟩ :=
    exists_hub_prime_capacity_above
      (4 * I.Csv) hscaled I.v k I.one_le_v hk
      (256 * k)
  have hh : 3 ≤ h.1 := by omega
  have hratioSpec :=
    integralStageRatio_spec
      (k := k) (h := h.1)
      (by omega) hlarge.le
  let B := integralStageRatio k h.1
  have hB : 2 ≤ B := by
    simpa [B] using hratioSpec.1
  have hBk : k * B < h.1 := by
    simpa [B] using hratioSpec.2.1
  have hseparated : h.1 ≤ k * B ^ 2 := by
    simpa [B] using hratioSpec.2.2.1
  have hwidth :
      0 <
        1 / (k : Real) -
          (B : Real) / (h.1 : Real) := by
    simpa [B] using hratioSpec.2.2.2.1
  have hgeometric :
      ((B : Real) - 1) /
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) ≤
        4 * Real.sqrt ((k * h.1 : Nat) : Real) := by
    simpa [B] using hratioSpec.2.2.2.2
  let M : OldControllerPrimeDensityMesh h k :=
    Classical.choice
      (exists_oldControllerPrime_reducedClass_mesh
        h hh k hkh (I.controllerDiverges h))
  let A : MeshFixedProgressionPNTInputs M :=
    I.fixedProgressionPNT M
  have hdimensionless :
      2 * I.Csv *
          (I.v : Real) ^ (controllerDensity h) *
          paperA (controllerDensity h) *
          ((B : Real) - 1) /
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) <
        1 := by
    apply hardCapacity_ratio_of_sqrt_bound
        I.Csv 4 I.Csv_nonneg (by norm_num)
        hwidth hgeometric
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcap
  have hgap :
      hardSurvivorCoefficient I.Csv I.v B h <
        M.controllerReservoirDensity *
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) := by
    exact
      hardSurvivorCoefficient_lt_controller
        M I.Csv I.Csv_nonneg (by omega)
        (by omega) hwidth hdimensionless
  apply P_of_mesh_hardUpperBound
      hh hk hkh hB hBk hseparated A
      (hardSurvivorCoefficient I.Csv I.v B h)
  · intro T
    simpa [A, B] using
      I.hardUpperBound hh (by omega) hlarge.le M A T
  · exact hgap

/-- A levelwise supply of the reduced analytic inputs proves the global
affirmative statement. -/
theorem globalAffirmative_of_integralHardInputs
    (I : ∀ k : Nat, 3 ≤ k → IntegralHardInputs k) :
    GlobalAffirmative := by
  intro k hk
  exact P_of_integralHardInputs hk (I k hk)

end Erdos279
