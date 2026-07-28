import Erdos279.DualSieveAsymptotic
import Erdos279.AllFixedProgressionPNT
import Erdos279.UniformIntegralHardReduction

/-!
# Unconditional direct hard-stage reduction

The two-shift Selberg sieve gives a simpler coefficient than the
Selberg--Delange coefficient used in the paper.  This file compares that
coefficient directly with the controller reservoir and feeds it into the
already verified dynamic construction.
-/

namespace Erdos279

/-- Complete hard-stage coefficient obtained by summing the local
two-shift bounds over all positive `h`-adic exponents. -/
noncomputable def directHardCoefficient
    (h : Prime) (B : Nat) : Real :=
  4 * dualSieveLayerCoefficient h B * controllerDensity h

theorem directHardCoefficient_nonneg
    (h : Prime) (B : Nat) :
    0 ≤ directHardCoefficient h B := by
  unfold directHardCoefficient
  exact mul_nonneg
    (mul_nonneg (by norm_num) (dualSieveLayerCoefficient_nonneg h B))
    (controllerDensity_pos h).le

/-- The two-shift sieve supplies the complete uniform hard-stage bound. -/
theorem hasUniformHardStageUpperBound_direct
    (h : Prime) (B : Nat) (hB : 0 < B) :
    HasUniformHardStageUpperBound h 64 B
      (directHardCoefficient h B) := by
  apply HasUniformMainHardStageUpperBound.toHardUpperBound
  · exact
      HasUniformMainLayerUpperBound.toMainHardStageUpperBound
        (hasUniformMainLayerUpperBound_dualSieve h B)
        (dualSieveLayerCoefficient_nonneg h B)
  · exact hB

/-- The fixed constant used to choose a hub large enough for the direct
two-shift coefficient. -/
noncomputable def directHubConstant (k : Nat) : Real :=
  82560 * Real.sqrt (k : Real)

theorem directHubConstant_nonneg (k : Nat) :
    0 ≤ directHubConstant k := by
  unfold directHubConstant
  positivity

/-- The geometric ratio bound makes eight local coefficients fit inside
the controller-annulus width. -/
theorem eight_dualSieveLayerCoefficient_lt_width
    {h : Prime} {k B : Nat}
    (hk : 0 < k)
    (hB : 2 ≤ B)
    (hwidth :
      0 < 1 / (k : Real) - (B : Real) / (h.1 : Real))
    (hgeometric :
      ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h.1 : Real)) ≤
        4 * Real.sqrt ((k * h.1 : Nat) : Real))
    (hhub :
      directHubConstant k * Real.sqrt (h.1 : Real) /
          ((h.1 : Real) - 1) < 1) :
    8 * dualSieveLayerCoefficient h B <
      1 / (k : Real) - (B : Real) / (h.1 : Real) := by
  let width : Real :=
    1 / (k : Real) - (B : Real) / (h.1 : Real)
  have hhPos : (0 : Real) < (h.1 : Real) := by
    exact_mod_cast h.pos
  have hhSubPos : 0 < (h.1 : Real) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast h.one_lt)
  have hBrel :
      ((2 * B + 1 : Nat) : Real) ≤
        5 * ((B : Real) - 1) := by
    push_cast
    have hBR : (2 : Real) ≤ (B : Real) := by exact_mod_cast hB
    linarith
  have hratio :
      ((2 * B + 1 : Nat) : Real) / width ≤
        20 * Real.sqrt ((k * h.1 : Nat) : Real) := by
    calc
      ((2 * B + 1 : Nat) : Real) / width ≤
          (5 * ((B : Real) - 1)) / width := by
        exact div_le_div_of_nonneg_right hBrel hwidth.le
      _ =
          5 * (((B : Real) - 1) / width) := by ring
      _ ≤ 5 * (4 * Real.sqrt ((k * h.1 : Nat) : Real)) :=
        mul_le_mul_of_nonneg_left
          (by simpa [width] using hgeometric) (by norm_num)
      _ = 20 * Real.sqrt ((k * h.1 : Nat) : Real) := by ring
  have hkPosR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hsqrtMul :
      Real.sqrt ((k * h.1 : Nat) : Real) =
        Real.sqrt (k : Real) * Real.sqrt (h.1 : Real) := by
    push_cast
    rw [Real.sqrt_mul (by positivity)]
  have hratioOne :
      (8 * dualSieveLayerCoefficient h B) / width < 1 := by
    have hnonneg :
        0 ≤ 4128 / (h.1 : Real) := by positivity
    have hupper :
        (8 * dualSieveLayerCoefficient h B) / width ≤
          directHubConstant k * Real.sqrt (h.1 : Real) /
            (h.1 : Real) := by
      unfold dualSieveLayerCoefficient directHubConstant
      calc
        (8 * (516 * ((2 * B + 1 : Nat) : Real) /
              (h.1 : Real))) / width =
            (4128 / (h.1 : Real)) *
              (((2 * B + 1 : Nat) : Real) / width) := by
          field_simp [hhPos.ne', hwidth.ne']
          ring
        _ ≤
            (4128 / (h.1 : Real)) *
              (20 * Real.sqrt ((k * h.1 : Nat) : Real)) :=
          mul_le_mul_of_nonneg_left hratio hnonneg
        _ =
            (82560 * Real.sqrt (k : Real)) *
                Real.sqrt (h.1 : Real) /
              (h.1 : Real) := by
          rw [hsqrtMul]
          ring
    have hdenom :
        directHubConstant k * Real.sqrt (h.1 : Real) /
              (h.1 : Real) ≤
            directHubConstant k * Real.sqrt (h.1 : Real) /
              ((h.1 : Real) - 1) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (directHubConstant_nonneg k)
          (Real.sqrt_nonneg _)
      · exact hhSubPos
      · linarith
    exact hupper.trans_lt (hdenom.trans_lt hhub)
  exact (div_lt_one hwidth).mp (by simpa [width] using hratioOne)

/-- Direct strict capacity gap against every old-prime density mesh. -/
theorem directHardCoefficient_lt_controller
    {h : Prime} {k B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hk : 0 < k)
    (hB : 2 ≤ B)
    (hwidth :
      0 < 1 / (k : Real) - (B : Real) / (h.1 : Real))
    (hgeometric :
      ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h.1 : Real)) ≤
        4 * Real.sqrt ((k * h.1 : Nat) : Real))
    (hhub :
      directHubConstant k * Real.sqrt (h.1 : Real) /
          ((h.1 : Real) - 1) < 1) :
    directHardCoefficient h B <
      M.controllerReservoirDensity *
        (1 / (k : Real) - (B : Real) / (h.1 : Real)) := by
  let width : Real :=
    1 / (k : Real) - (B : Real) / (h.1 : Real)
  have hsmall :
      8 * dualSieveLayerCoefficient h B < width := by
    simpa [width] using
      eight_dualSieveLayerCoefficient_lt_width
        hk hB hwidth hgeometric hhub
  have hδ : 0 < controllerDensity h := controllerDensity_pos h
  have hhalf :
      controllerDensity h / 2 <
        M.controllerReservoirDensity :=
    M.controllerReservoirDensity_gt_half
  have hfirst :
      directHardCoefficient h B <
        (controllerDensity h / 2) * width := by
    unfold directHardCoefficient
    nlinarith
  exact hfirst.trans
    (mul_lt_mul_of_pos_right hhalf (by simpa [width] using hwidth))

/-- The unconditional fixed-progression PNT and the direct two-shift sieve
construct the full residue assignment at every level `k ≥ 3`. -/
theorem P_of_allFixedProgressionPNT_direct
    {k : Nat} (hk : 3 ≤ k)
    (fixedPNT : AllFixedProgressionPrimeNumberTheorems) :
    P k := by
  have hkpos : 0 < k := by omega
  obtain ⟨h, hmax, hhub⟩ :=
    exists_prime_sqrt_div_sub_one_lt
      (directHubConstant k) (directHubConstant_nonneg k)
      (max (256 * k) k)
  have hlarge : 256 * k < h.1 :=
    (le_max_left (256 * k) k).trans_lt hmax
  have hkh : k < h.1 :=
    (le_max_right (256 * k) k).trans_lt hmax
  have hh : 3 ≤ h.1 := by omega
  have hratioSpec :=
    integralStageRatio_spec
      (k := k) (h := h.1) hkpos hlarge.le
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
  have hdiv : ControllerPrimeReciprocalDiverges h :=
    controllerPrimeReciprocalDiverges_of_fixedProgressionPNT
      h (fixedPNT h.1)
  let M : OldControllerPrimeDensityMesh h k :=
    Classical.choice
      (exists_oldControllerPrime_reducedClass_mesh
        h hh k hkh hdiv)
  let A : MeshFixedProgressionPNTInputs M :=
    { periodicPNT :=
        fixedPNT (h.1 * M.modulus.1)
      complementaryPNT :=
        fixedPNT
          (h.1 *
            primeSubsetModulus
              (oldControllerPrimes h M.cutoff)) }
  let E : MeshPrimeEnumerations M :=
    A.toMeshPrimeEnumerations
      (hh := hh) (hk := hkpos)
  obtain ⟨T⟩ := E.exists_tailMatching hh hkpos
  have hHard :
      HasUniformHardStageUpperBound
        h 64 B (directHardCoefficient h B) :=
    hasUniformHardStageUpperBound_direct h B (by omega)
  have hController :
      HasMeshControllerStageAsymptotic
        M B
        (M.controllerReservoirDensity *
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real))) :=
    mesh_controllerStage_asymptotic
      M hkpos (by omega) hBk A.periodicPNT
  have hgap :
      directHardCoefficient h B <
        M.controllerReservoirDensity *
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) :=
    directHardCoefficient_lt_controller
      M hkpos hB hwidth hgeometric hhub
  let HD :
      DynamicHardScheduleAnalyticData
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff)
        64 k :=
    dynamicHardScheduleAnalyticData_of_upperBound
      M hkpos (by norm_num) hB hseparated
      hHard hController hgap
  let D : DynamicScheduledPaperConstruction k :=
    { hub := h
      hub_gt_level := hkh
      modulus := M.modulus
      cutoff := M.cutoff
      classes := M.classes
      enumerations := E.enumerations
      primeTail := T
      sieveExponent := 64
      hardData := HD }
  exact
    DynamicScheduledPaperConstruction.P_of_dynamicScheduledPaperConstruction
      hk D

/-- Erdős Problem 279, with every analytic input discharged inside Lean. -/
theorem globalAffirmative_direct : GlobalAffirmative := by
  intro k hk
  exact
    P_of_allFixedProgressionPNT_direct
      hk allFixedProgressionPrimeNumberTheorems

/-- Canonical exported name for the unconditional solution of Erdős 279. -/
theorem globalAffirmative : GlobalAffirmative :=
  globalAffirmative_direct

end Erdos279
