import Erdos279.MeshFixedProgressionPNT

/-!
# From stage-count asymptotics to a geometric hard schedule

This file isolates the purely limiting part of the hard-stage argument.
If the normalized hard-survivor count and controller-annulus count have
limits with a strict coefficient gap, then the cardinal capacity inequality
holds at every sufficiently large scale.  An integral geometric scale
sequence, chosen divisible by both `k` and the hub, turns that eventual
inequality into all of `HardScheduleAnalyticData`.
-/

namespace Erdos279

open Filter

/-- The hard-survivor count for one multiplicative stage `(X,BX]`. -/
noncomputable def meshHardStageCount
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    (B X : Nat) : Nat :=
  (hardSurvivors h M.cutoff
    (E.enumerations.primeTargetOldClasses T)
    X (B * X)).card

/-- The available controller count in the corresponding annulus. -/
noncomputable def meshControllerStageCount
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (B X : Nat) : Nat :=
  (hardStageControllerAnnulus
    h M.modulus M.classes
    (oldControllerPrimes h M.cutoff)
    k X (B * X)).card

/-- A normalized asymptotic for hard survivors at a fixed integral scale
ratio. -/
def HasMeshHardStageAsymptotic
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    (B : Nat) (coefficient : Real) : Prop :=
  Tendsto
    (fun X : Nat =>
      (meshHardStageCount E T B X : Real) /
        primeCountingScale X)
    atTop (nhds coefficient)

/-- The one-sided asymptotic upper bound actually supplied by the
deterministic sieve proposition. -/
def HasMeshHardStageUpperBound
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    (B : Nat) (coefficient : Real) : Prop :=
  ∀ ε : Real, 0 < ε →
    ∀ᶠ X : Nat in atTop,
      (meshHardStageCount E T B X : Real) /
          primeCountingScale X ≤
        coefficient + ε

/-- A genuine asymptotic implies its corresponding one-sided upper
bound. -/
theorem HasMeshHardStageAsymptotic.toUpperBound
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {E : MeshPrimeEnumerations M}
    {T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k}
    {coefficient : Real}
    (hAsymptotic :
      HasMeshHardStageAsymptotic
        E T B coefficient) :
    HasMeshHardStageUpperBound
      E T B coefficient := by
  intro ε hε
  exact
    (hAsymptotic.eventually_lt_const
      (by linarith)).mono
      (fun _ h => h.le)

/-- A normalized asymptotic for the controller annulus at a fixed integral
scale ratio. -/
def HasMeshControllerStageAsymptotic
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (B : Nat) (coefficient : Real) : Prop :=
  Tendsto
    (fun X : Nat =>
      (meshControllerStageCount M B X : Real) /
        primeCountingScale X)
    atTop (nhds coefficient)

/-- A strict gap between the two limiting coefficients gives the eventual
finite cardinal inequality needed for stagewise pairing. -/
theorem eventually_meshStage_capacity_of_asymptotics
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    {hardCoefficient controllerCoefficient : Real}
    (hHard :
      HasMeshHardStageAsymptotic
        E T B hardCoefficient)
    (hController :
      HasMeshControllerStageAsymptotic
        M B controllerCoefficient)
    (hGap :
      hardCoefficient < controllerCoefficient) :
    ∀ᶠ X : Nat in atTop,
      meshHardStageCount E T B X ≤
        meshControllerStageCount M B X := by
  let midpoint :=
    (hardCoefficient + controllerCoefficient) / 2
  have hHardMid :
      hardCoefficient < midpoint := by
    dsimp [midpoint]
    linarith
  have hMidController :
      midpoint < controllerCoefficient := by
    dsimp [midpoint]
    linarith
  have hHardEventually :
      ∀ᶠ X : Nat in atTop,
        (meshHardStageCount E T B X : Real) /
            primeCountingScale X <
          midpoint :=
    hHard.eventually_lt_const hHardMid
  have hControllerEventually :
      ∀ᶠ X : Nat in atTop,
        midpoint <
          (meshControllerStageCount M B X : Real) /
            primeCountingScale X :=
    hController.eventually_const_lt
      hMidController
  filter_upwards
    [hHardEventually,
      hControllerEventually] with X hHX hXC
  have hNormalized :
      (meshHardStageCount E T B X : Real) /
          primeCountingScale X <
        (meshControllerStageCount M B X : Real) /
          primeCountingScale X :=
    hHX.trans hXC
  have hCardReal :
      (meshHardStageCount E T B X : Real) <
        (meshControllerStageCount M B X : Real) :=
    (div_lt_div_iff_of_pos_right
      (primeCountingScale_pos X)).mp
      hNormalized
  exact_mod_cast hCardReal.le

/-- The one-sided sieve upper bound is enough: a strict coefficient gap
against the controller-annulus asymptotic gives eventual finite capacity. -/
theorem eventually_meshStage_capacity_of_upperBound
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    {hardCoefficient controllerCoefficient : Real}
    (hHard :
      HasMeshHardStageUpperBound
        E T B hardCoefficient)
    (hController :
      HasMeshControllerStageAsymptotic
        M B controllerCoefficient)
    (hGap :
      hardCoefficient < controllerCoefficient) :
    ∀ᶠ X : Nat in atTop,
      meshHardStageCount E T B X ≤
        meshControllerStageCount M B X := by
  let midpoint :=
    (hardCoefficient + controllerCoefficient) / 2
  have hHardMid :
      0 < midpoint - hardCoefficient := by
    dsimp [midpoint]
    linarith
  have hMidController :
      midpoint < controllerCoefficient := by
    dsimp [midpoint]
    linarith
  have hHardEventually :=
    hHard (midpoint - hardCoefficient)
      hHardMid
  have hControllerEventually :
      ∀ᶠ X : Nat in atTop,
        midpoint <
          (meshControllerStageCount M B X : Real) /
            primeCountingScale X :=
    hController.eventually_const_lt
      hMidController
  filter_upwards
    [hHardEventually,
      hControllerEventually] with X hHX hXC
  have hHardMidLe :
      (meshHardStageCount E T B X : Real) /
          primeCountingScale X ≤
        midpoint := by
    have hmid :
        hardCoefficient +
            (midpoint - hardCoefficient) =
          midpoint := by ring
    simpa [hmid] using hHX
  have hNormalized :
      (meshHardStageCount E T B X : Real) /
          primeCountingScale X <
        (meshControllerStageCount M B X : Real) /
          primeCountingScale X :=
    hHardMidLe.trans_lt hXC
  have hCardReal :
      (meshHardStageCount E T B X : Real) <
        (meshControllerStageCount M B X : Real) :=
    (div_lt_div_iff_of_pos_right
      (primeCountingScale_pos X)).mp
      hNormalized
  exact_mod_cast hCardReal.le

/-- Any eventual capacity inequality can be sampled on a sufficiently
large integral geometric sequence.  Divisibility of the starting scale
removes all floor-error issues in the separation condition. -/
noncomputable def hardScheduleAnalyticData_of_eventually_geometric
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {E : MeshPrimeEnumerations M}
    {T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k}
    (hk : 0 < k)
    (hB : 2 ≤ B)
    (hseparated : h.1 ≤ k * B ^ 2)
    (hcapacity :
      ∀ᶠ X : Nat in atTop,
        meshHardStageCount E T B X ≤
          meshControllerStageCount M B X) :
    HardScheduleAnalyticData E T := by
  let hThreshold :
      ∃ N, ∀ X ≥ N,
        meshHardStageCount E T B X ≤
          meshControllerStageCount M B X :=
    eventually_atTop.1 hcapacity
  let N : Nat := Classical.choose hThreshold
  have hN :
      ∀ X ≥ N,
        meshHardStageCount E T B X ≤
          meshControllerStageCount M B X :=
    Classical.choose_spec hThreshold
  let base : Nat :=
    k * h.1 * (N + 1)
  let scale : Nat → Nat :=
    fun j => base * B ^ j
  have hbasePos : 0 < base := by
    dsimp [base]
    exact
      Nat.mul_pos
        (Nat.mul_pos hk h.pos)
        (Nat.succ_pos N)
  have hbaseN : N ≤ base := by
    have hfactor :
        1 ≤ k * h.1 := by
      exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hk.ne' h.pos.ne')
    dsimp [base]
    have hNsucc : N ≤ N + 1 := by omega
    have hmul :
        N + 1 ≤
          (k * h.1) * (N + 1) :=
      le_mul_of_one_le_left
        (by omega) hfactor
    exact hNsucc.trans hmul
  have hscaleNext :
      ∀ j,
        scale (j + 1) = B * scale j := by
    intro j
    dsimp [scale]
    rw [pow_succ]
    ring
  exact
    { scale := scale
      scale_monotone := by
        intro i j hij
        dsimp [scale]
        exact Nat.mul_le_mul_left base
          (pow_right_monotone
            (by omega : 1 ≤ B) hij)
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
        intro j
        have hscaleN :
            N ≤ scale j := by
          have hpowPos :
              0 < B ^ j :=
            pow_pos (by omega : 0 < B) j
          exact hbaseN.trans
            (Nat.le_mul_of_pos_right
              base hpowPos)
        have hstage :=
          hN (scale j) hscaleN
        unfold meshHardStageCount
          meshControllerStageCount at hstage
        simpa [hscaleNext j] using hstage
      scale_separated := by
        intro i
        have hLeft :
            scale i / k =
              h.1 * (N + 1) * B ^ i := by
          dsimp [scale, base]
          rw [show
            k * h.1 * (N + 1) * B ^ i =
              k * (h.1 * (N + 1) * B ^ i) by
                ring]
          simpa [Nat.mul_comm] using
            (Nat.mul_div_left
              (h.1 * (N + 1) * B ^ i) hk)
        have hRight :
            scale (i + 2) / h.1 =
              k * (N + 1) * B ^ (i + 2) := by
          dsimp [scale, base]
          rw [show
            k * h.1 * (N + 1) * B ^ (i + 2) =
              h.1 *
                (k * (N + 1) * B ^ (i + 2)) by
                  ring]
          simpa [Nat.mul_comm] using
            (Nat.mul_div_left
              (k * (N + 1) * B ^ (i + 2))
              h.pos)
        rw [hLeft, hRight]
        have hmul :=
          Nat.mul_le_mul_right
            ((N + 1) * B ^ i)
            hseparated
        rw [pow_add, pow_two]
        simpa only [pow_two, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using
          hmul }

/-- The strict asymptotic coefficient gap therefore constructs the complete
hard-schedule data on an integral geometric scale. -/
noncomputable def hardScheduleAnalyticData_of_asymptotics
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {E : MeshPrimeEnumerations M}
    {T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k}
    (hk : 0 < k)
    (hB : 2 ≤ B)
    (hseparated : h.1 ≤ k * B ^ 2)
    {hardCoefficient controllerCoefficient : Real}
    (hHard :
      HasMeshHardStageAsymptotic
        E T B hardCoefficient)
    (hController :
      HasMeshControllerStageAsymptotic
        M B controllerCoefficient)
    (hGap :
      hardCoefficient < controllerCoefficient) :
    HardScheduleAnalyticData E T :=
  hardScheduleAnalyticData_of_eventually_geometric
    hk hB hseparated
    (eventually_meshStage_capacity_of_asymptotics
      E T hHard hController hGap)

/-- One-sided hard-survivor bounds, as in the paper, likewise construct the
complete hard-schedule data. -/
noncomputable def hardScheduleAnalyticData_of_upperBound
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {E : MeshPrimeEnumerations M}
    {T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k}
    (hk : 0 < k)
    (hB : 2 ≤ B)
    (hseparated : h.1 ≤ k * B ^ 2)
    {hardCoefficient controllerCoefficient : Real}
    (hHard :
      HasMeshHardStageUpperBound
        E T B hardCoefficient)
    (hController :
      HasMeshControllerStageAsymptotic
        M B controllerCoefficient)
    (hGap :
      hardCoefficient < controllerCoefficient) :
    HardScheduleAnalyticData E T :=
  hardScheduleAnalyticData_of_eventually_geometric
    hk hB hseparated
    (eventually_meshStage_capacity_of_upperBound
      E T hHard hController hGap)

end Erdos279
