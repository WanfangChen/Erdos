import Erdos279.PrimeCountingIntervals

/-!
# Final mesh reduction to the deterministic hard-survivor bound

For one density mesh, fixed-progression PNT now constructs both prime
enumerations and the controller-annulus asymptotic.  The only remaining
stage input is the uniform one-sided hard-survivor estimate with a strict
coefficient gap.
-/

namespace Erdos279

/-- Fixed-progression PNT together with the paper's uniform hard-survivor
upper bound constructs all analytic inputs for one mesh. -/
noncomputable def meshAnalyticInputs_of_hardUpperBound
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (hh : 3 ≤ h.1)
    (hk : 0 < k)
    (hB : 2 ≤ B)
    (hBk : k * B < h.1)
    (hseparated : h.1 ≤ k * B ^ 2)
    (A : MeshFixedProgressionPNTInputs M)
    (hardCoefficient : Real)
    (hHard :
      ∀ T : TailPrimeTargetMatching
        (A.toMeshPrimeEnumerations
          (hh := hh) (hk := hk)).enumerations.periodic
        (A.toMeshPrimeEnumerations
          (hh := hh) (hk := hk)).enumerations.complementary k,
        HasMeshHardStageUpperBound
          (A.toMeshPrimeEnumerations
            (hh := hh) (hk := hk))
          T B hardCoefficient)
    (hGap :
      hardCoefficient <
        M.controllerReservoirDensity *
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real))) :
    MeshAnalyticInputs M := by
  let E : MeshPrimeEnumerations M :=
    A.toMeshPrimeEnumerations
      (hh := hh) (hk := hk)
  exact
    { primeEnumerations := E
      hardSchedule := by
        intro T
        refine ⟨?_⟩
        show HardScheduleAnalyticData E T
        apply
          hardScheduleAnalyticData_of_upperBound
            hk hB hseparated
            (hardCoefficient := hardCoefficient)
            (controllerCoefficient :=
              M.controllerReservoirDensity *
                (1 / (k : Real) -
                  (B : Real) / (h.1 : Real)))
        · simpa [E] using hHard T
        · exact
            mesh_controllerStage_asymptotic
              M hk (by omega) hBk
              A.periodicPNT
        · exact hGap }

/-- The same reduced data already prove the fixed-level statement `P(k)`. -/
theorem P_of_mesh_hardUpperBound
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (hh : 3 ≤ h.1)
    (hk : 3 ≤ k)
    (hkh : k < h.1)
    (hB : 2 ≤ B)
    (hBk : k * B < h.1)
    (hseparated : h.1 ≤ k * B ^ 2)
    (A : MeshFixedProgressionPNTInputs M)
    (hardCoefficient : Real)
    (hHard :
      ∀ T : TailPrimeTargetMatching
        (A.toMeshPrimeEnumerations
          (hh := hh) (hk := by omega)).enumerations.periodic
        (A.toMeshPrimeEnumerations
          (hh := hh) (hk := by omega)).enumerations.complementary k,
        HasMeshHardStageUpperBound
          (A.toMeshPrimeEnumerations
            (hh := hh) (hk := by omega))
          T B hardCoefficient)
    (hGap :
      hardCoefficient <
        M.controllerReservoirDensity *
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real))) :
    P k := by
  apply P_of_meshAnalyticInputs
      (meshAnalyticInputs_of_hardUpperBound
        hh (by omega) hB hBk hseparated
        A hardCoefficient hHard hGap)
      hh hk hkh

end Erdos279
