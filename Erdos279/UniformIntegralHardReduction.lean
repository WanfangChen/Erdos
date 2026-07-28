import Erdos279.DynamicScheduledPaperConstruction
import Erdos279.FixedPNTHardReduction

/-!
# Corrected integral reduction using the uniform hard sieve

Unlike the earlier fixed-cutoff interface, this reduction states the hard
sieve input uniformly over every nonzero residue vector up to
`floor(X^(1/v))`.  This is the exact quantifier structure of Proposition
2.1 and is strong enough to construct the recursive global assignment.
-/

namespace Erdos279

/-- The genuine analytic inputs remaining at a fixed level after all
elementary parameter choices. -/
structure UniformIntegralHardInputs (k : Nat) where
  Csv : Real
  Csv_nonneg : 0 ≤ Csv
  v : Nat
  two_le_v : 2 ≤ v
  controllerDiverges :
    ∀ h : Prime, ControllerPrimeReciprocalDiverges h
  fixedProgressionPNT :
    ∀ {h : Prime} (M : OldControllerPrimeDensityMesh h k),
      MeshFixedProgressionPNTInputs M
  hardUpperBound :
    ∀ {h : Prime}
      (hh : 3 ≤ h.1)
      (hkpos : 0 < k)
      (hlarge : 256 * k ≤ h.1),
      HasUniformHardStageUpperBound
        h v (integralStageRatio k h.1)
        (hardSurvivorCoefficient
          Csv v (integralStageRatio k h.1) h)

/-- All structural choices, recursive updates, and completion arguments
are discharged from the corrected analytic package. -/
theorem P_of_uniformIntegralHardInputs
    {k : Nat} (hk : 3 ≤ k)
    (I : UniformIntegralHardInputs k) :
    P k := by
  have hscaled : 0 ≤ 4 * I.Csv :=
    mul_nonneg (by norm_num) I.Csv_nonneg
  obtain ⟨h, hlarge, hkh, hcap⟩ :=
    exists_hub_prime_capacity_above
      (4 * I.Csv) hscaled I.v k
      ((by omega : 1 ≤ 2).trans I.two_le_v)
      hk (256 * k)
  have hh : 3 ≤ h.1 := by omega
  have hkpos : 0 < k := by omega
  have hratioSpec :=
    integralStageRatio_spec
      (k := k) (h := h.1)
      hkpos hlarge.le
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
  let E : MeshPrimeEnumerations M :=
    A.toMeshPrimeEnumerations
      (hh := hh) (hk := hkpos)
  obtain ⟨T⟩ := E.exists_tailMatching hh hkpos
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
            (B : Real) / (h.1 : Real)) :=
    hardSurvivorCoefficient_lt_controller
      M I.Csv I.Csv_nonneg hkpos
      (by omega) hwidth hdimensionless
  have hHard :
      HasUniformHardStageUpperBound
        h I.v B
        (hardSurvivorCoefficient I.Csv I.v B h) := by
    simpa [B] using
      I.hardUpperBound hh hkpos hlarge.le
  have hController :
      HasMeshControllerStageAsymptotic
        M B
        (M.controllerReservoirDensity *
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real))) :=
    mesh_controllerStage_asymptotic
      M hkpos (by omega) hBk A.periodicPNT
  let HD :
      DynamicHardScheduleAnalyticData
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff)
        I.v k :=
    dynamicHardScheduleAnalyticData_of_upperBound
      M hkpos I.two_le_v hB hseparated
      hHard hController hgap
  let D : DynamicScheduledPaperConstruction k :=
    { hub := h
      hub_gt_level := hkh
      modulus := M.modulus
      cutoff := M.cutoff
      classes := M.classes
      enumerations := E.enumerations
      primeTail := T
      sieveExponent := I.v
      hardData := HD }
  exact
    DynamicScheduledPaperConstruction.P_of_dynamicScheduledPaperConstruction
      hk D

/-- A levelwise supply of the corrected analytic inputs proves the global
affirmative statement. -/
theorem globalAffirmative_of_uniformIntegralHardInputs
    (I : ∀ k : Nat, 3 ≤ k →
      UniformIntegralHardInputs k) :
    GlobalAffirmative := by
  intro k hk
  exact P_of_uniformIntegralHardInputs hk (I k hk)

/-- Minimal corrected package after deriving reciprocal divergence and all
mesh PNT statements from PNT in every fixed reduced progression. -/
structure UniformFixedPNTHardInputs (k : Nat) where
  Csv : Real
  Csv_nonneg : 0 ≤ Csv
  v : Nat
  two_le_v : 2 ≤ v
  fixedPNT : AllFixedProgressionPrimeNumberTheorems
  hardUpperBound :
    ∀ {h : Prime}
      (hh : 3 ≤ h.1)
      (hkpos : 0 < k)
      (hlarge : 256 * k ≤ h.1),
      HasUniformHardStageUpperBound
        h v (integralStageRatio k h.1)
        (hardSurvivorCoefficient
          Csv v (integralStageRatio k h.1) h)

namespace UniformFixedPNTHardInputs

noncomputable def toUniformIntegralHardInputs
    {k : Nat} (I : UniformFixedPNTHardInputs k) :
    UniformIntegralHardInputs k where
  Csv := I.Csv
  Csv_nonneg := I.Csv_nonneg
  v := I.v
  two_le_v := I.two_le_v
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
    intro h hh hkpos hlarge
    exact I.hardUpperBound hh hkpos hlarge

end UniformFixedPNTHardInputs

theorem P_of_uniformFixedPNTHardInputs
    {k : Nat} (hk : 3 ≤ k)
    (I : UniformFixedPNTHardInputs k) :
    P k :=
  P_of_uniformIntegralHardInputs hk
    I.toUniformIntegralHardInputs

theorem globalAffirmative_of_uniformFixedPNTHardInputs
    (I : ∀ k : Nat, 3 ≤ k →
      UniformFixedPNTHardInputs k) :
    GlobalAffirmative := by
  intro k hk
  exact P_of_uniformFixedPNTHardInputs hk (I k hk)

end Erdos279
