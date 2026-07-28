import Erdos279.DynamicHardScheduleData
import Erdos279.GeometricHardSchedule

/-!
# Sampling the uniform sieve estimate on a geometric scale

The strict asymptotic coefficient gap first gives a capacity inequality
uniformly over every scale-dependent old residue vector.  We then sample
that eventual statement on a sufficiently large integral geometric scale
and verify all recursive cutoff invariants.
-/

namespace Erdos279

open Filter

/-- A strict coefficient gap turns the paper's uniform one-sided sieve
bound into the finite capacity inequality, uniformly over all old-class
vectors. -/
theorem eventually_uniformStage_capacity_of_upperBound
    {h : Prime} {k v B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    {hardCoefficient controllerCoefficient : Real}
    (hHard :
      HasUniformHardStageUpperBound
        h v B hardCoefficient)
    (hController :
      HasMeshControllerStageAsymptotic
        M B controllerCoefficient)
    (hGap :
      hardCoefficient < controllerCoefficient) :
    ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h
        (stageOldPrimeCutoff v X),
        uniformHardStageCount h v B X a ≤
          meshControllerStageCount M B X := by
  let midpoint :=
    (hardCoefficient + controllerCoefficient) / 2
  have hHardEps :
      0 < midpoint - hardCoefficient := by
    dsimp [midpoint]
    linarith
  have hMidController :
      midpoint < controllerCoefficient := by
    dsimp [midpoint]
    linarith
  have hHardEventually :=
    hHard (midpoint - hardCoefficient) hHardEps
  have hControllerEventually :
      ∀ᶠ X : Nat in atTop,
        midpoint <
          (meshControllerStageCount M B X : Real) /
            primeCountingScale X :=
    hController.eventually_const_lt hMidController
  filter_upwards
    [hHardEventually, hControllerEventually] with
      X hHardX hControllerX
  intro a
  have hHardMid :
      (uniformHardStageCount h v B X a : Real) /
          primeCountingScale X ≤ midpoint := by
    have hEq :
        hardCoefficient +
            (midpoint - hardCoefficient) =
          midpoint := by ring
    simpa [hEq] using hHardX a
  have hNormalized :
      (uniformHardStageCount h v B X a : Real) /
          primeCountingScale X <
        (meshControllerStageCount M B X : Real) /
          primeCountingScale X :=
    hHardMid.trans_lt hControllerX
  have hCardReal :
      (uniformHardStageCount h v B X a : Real) <
        (meshControllerStageCount M B X : Real) :=
    (div_lt_div_iff_of_pos_right
      (primeCountingScale_pos X)).mp hNormalized
  exact_mod_cast hCardReal.le

/-- Any eventual uniform stage-capacity inequality can be sampled on a
geometric sequence that is simultaneously separated, cutoff-ready, and
cutoff-mature. -/
noncomputable def dynamicHardScheduleAnalyticData_of_eventually_geometric
    {h : Prime} {k v B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hk : 0 < k)
    (hv : 2 ≤ v)
    (hB : 2 ≤ B)
    (hseparated : h.1 ≤ k * B ^ 2)
    (hcapacity :
      ∀ᶠ X : Nat in atTop,
        ∀ a : OldPrimeClasses h
          (stageOldPrimeCutoff v X),
          uniformHardStageCount h v B X a ≤
            meshControllerStageCount M B X) :
    DynamicHardScheduleAnalyticData
      h M.modulus M.classes
      (oldControllerPrimes h M.cutoff) v k := by
  let hThreshold :
      ∃ N, ∀ X ≥ N,
        ∀ a : OldPrimeClasses h
          (stageOldPrimeCutoff v X),
          uniformHardStageCount h v B X a ≤
            meshControllerStageCount M B X :=
    eventually_atTop.1 hcapacity
  let N : Nat := Classical.choose hThreshold
  have hN :
      ∀ X ≥ N,
        ∀ a : OldPrimeClasses h
          (stageOldPrimeCutoff v X),
          uniformHardStageCount h v B X a ≤
            meshControllerStageCount M B X :=
    Classical.choose_spec hThreshold
  let D : Nat := h.1 + k + N + 2
  let base : Nat := D ^ 2
  let scale : Nat → Nat :=
    fun j => base * B ^ j
  have hDpos : 0 < D := by
    dsimp [D]
    omega
  have hNbase : N ≤ base := by
    have hND : N ≤ D := by
      dsimp [D]
      omega
    have hDbase : D ≤ base := by
      dsimp [base]
      simpa [pow_two] using
        Nat.le_mul_of_pos_right D hDpos
    exact hND.trans hDbase
  have hkbase : k ^ 2 ≤ base := by
    have hkD : k ≤ D := by
      dsimp [D]
      omega
    dsimp [base]
    exact Nat.pow_le_pow_left hkD 2
  have hCbase : (h.1 + 1) ^ 2 ≤ base := by
    have hCD : h.1 + 1 ≤ D := by
      dsimp [D]
      omega
    dsimp [base]
    exact Nat.pow_le_pow_left hCD 2
  have hbasePos : 0 < base := by
    exact pow_pos hDpos 2
  have hBC :
      2 * h.1 ≤ B * (h.1 + 1) := by
    calc
      2 * h.1 ≤ B * h.1 :=
        Nat.mul_le_mul_right h.1 hB
      _ ≤ B * (h.1 + 1) :=
        Nat.mul_le_mul_left B (by omega)
  have hscaleNext :
      ∀ j, scale (j + 1) = B * scale j := by
    intro j
    dsimp [scale]
    rw [pow_succ]
    ring
  have hscaleTwo :
      ∀ j, scale (j + 2) = B ^ 2 * scale j := by
    intro j
    rw [show j + 2 = (j + 1) + 1 by omega,
      hscaleNext, hscaleNext]
    ring
  have hscaleBase :
      ∀ j, base ≤ scale j := by
    intro j
    dsimp [scale]
    exact Nat.le_mul_of_pos_right base
      (pow_pos (by omega : 0 < B) j)
  have hscaleMono : Monotone scale := by
    intro i j hij
    dsimp [scale]
    exact Nat.mul_le_mul_left base
      (pow_right_monotone (by omega : 1 ≤ B) hij)
  exact
    { scale := scale
      scale_monotone := hscaleMono
      scale_unbounded := by
        have hPow :
            Tendsto (fun j : Nat => B ^ j)
              atTop atTop :=
          tendsto_pow_atTop_atTop_of_one_lt
            (by omega : 1 < B)
        apply tendsto_atTop_mono' atTop
          (Eventually.of_forall
            (fun j =>
              Nat.le_mul_of_pos_left
                (B ^ j) hbasePos))
        exact hPow
      stage_capacity := by
        intro j a
        have hscaleN :
            N ≤ scale j :=
          hNbase.trans (hscaleBase j)
        have hstage := hN (scale j) hscaleN a
        unfold uniformHardStageCount
          meshControllerStageCount at hstage
        simpa [dynamicHardAnnulus, hscaleNext j] using
          hstage
      scale_separated := by
        intro i
        apply (Nat.le_div_iff_mul_le h.pos).2
        calc
          (scale i / k) * h.1 ≤
              (scale i / k) * (k * B ^ 2) :=
            Nat.mul_le_mul_left (scale i / k)
              hseparated
          _ = ((scale i / k) * k) * B ^ 2 := by
            ring
          _ ≤ scale i * B ^ 2 :=
            Nat.mul_le_mul_right (B ^ 2)
              (Nat.div_mul_le_self (scale i) k)
          _ = scale (i + 2) := by
            rw [hscaleTwo]
            ring
      cutoff_below_future := by
        intro j i hji
        have hCscale :
            (h.1 + 1) ^ 2 ≤ scale j :=
          hCbase.trans (hscaleBase j)
        have hcurrent :
            stageOldPrimeCutoff v (scale j) <
              scale (j + 1) / h.1 := by
          rw [hscaleNext]
          exact stageOldPrimeCutoff_lt_mul_div
            hv h.pos hCscale hBC
        exact hcurrent.trans_le
          (Nat.div_le_div_right
            (hscaleMono (by omega : j + 1 ≤ i + 1)))
      cutoff_mature := by
        intro j
        exact mul_nthRoot_le_of_sq_le hv
          (hkbase.trans (hscaleBase j)) }

/-- The paper's uniform hard bound and the controller-prime asymptotic
therefore construct all corrected dynamic hard-schedule data. -/
noncomputable def dynamicHardScheduleAnalyticData_of_upperBound
    {h : Prime} {k v B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hk : 0 < k)
    (hv : 2 ≤ v)
    (hB : 2 ≤ B)
    (hseparated : h.1 ≤ k * B ^ 2)
    {hardCoefficient controllerCoefficient : Real}
    (hHard :
      HasUniformHardStageUpperBound
        h v B hardCoefficient)
    (hController :
      HasMeshControllerStageAsymptotic
        M B controllerCoefficient)
    (hGap :
      hardCoefficient < controllerCoefficient) :
    DynamicHardScheduleAnalyticData
      h M.modulus M.classes
      (oldControllerPrimes h M.cutoff) v k :=
  dynamicHardScheduleAnalyticData_of_eventually_geometric
    M hk hv hB hseparated
    (eventually_uniformStage_capacity_of_upperBound
      M hHard hController hGap)

end Erdos279
