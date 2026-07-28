import Erdos279.MeshHardAsymptoticReduction

/-!
# Hard-survivor and controller capacity coefficients

This file records the exact coefficient comparison used after the
deterministic sieve.  The mesh leaves strictly more than half of the
controller density for cleanup, so the paper's normalized ratio inequality
implies a strict gap between hard survivors and controller primes.
-/

namespace Erdos279

/-- Leading hard-survivor coefficient for an integral stage ratio `B`. -/
noncomputable def hardSurvivorCoefficient
    (Csv : Real) (v B : Nat) (h : Prime) : Real :=
  Csv *
    controllerDensity h *
    paperA (controllerDensity h) *
    (v : Real) ^ (controllerDensity h) *
    ((B : Real) - 1)

theorem hardSurvivorCoefficient_nonneg
    (Csv : Real) (hCsv : 0 ≤ Csv)
    (v B : Nat) (hB : 1 ≤ B)
    (h : Prime) :
    0 ≤ hardSurvivorCoefficient Csv v B h := by
  unfold hardSurvivorCoefficient
  have hBsub :
      0 ≤ (B : Real) - 1 := by
    exact sub_nonneg.mpr
      (by exact_mod_cast hB)
  have hδ :
      0 ≤ controllerDensity h :=
    (controllerDensity_pos h).le
  have hA :
      0 ≤ paperA (controllerDensity h) :=
    (paperA_controllerDensity_pos h).le
  have hv :
      0 ≤
        (v : Real) ^
          (controllerDensity h) :=
    Real.rpow_nonneg (by positivity) _
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hCsv hδ) hA)
        hv)
      hBsub

/-- The dimensionless coefficient inequality from the paper implies the
strict capacity gap for every density mesh attached to the hub. -/
theorem hardSurvivorCoefficient_lt_controller
    {h : Prime} {k B v : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (Csv : Real) (hCsv : 0 ≤ Csv)
    (hk : 0 < k)
    (hB : 1 < B)
    (hwidth :
      0 <
        1 / (k : Real) -
          (B : Real) / (h.1 : Real))
    (hratio :
      2 * Csv *
          (v : Real) ^ (controllerDensity h) *
          paperA (controllerDensity h) *
          ((B : Real) - 1) /
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) <
        1) :
    hardSurvivorCoefficient Csv v B h <
      M.controllerReservoirDensity *
        (1 / (k : Real) -
          (B : Real) / (h.1 : Real)) := by
  let width : Real :=
    1 / (k : Real) -
      (B : Real) / (h.1 : Real)
  have hδ :
      0 < controllerDensity h :=
    controllerDensity_pos h
  have hA :
      0 < paperA (controllerDensity h) :=
    paperA_controllerDensity_pos h
  have hvpow :
      0 ≤
        (v : Real) ^
          (controllerDensity h) := by
    positivity
  have hBsub :
      0 < (B : Real) - 1 := by
    exact sub_pos.mpr
      (by exact_mod_cast hB)
  have hMain :
      2 * Csv *
          (v : Real) ^ (controllerDensity h) *
          paperA (controllerDensity h) *
          ((B : Real) - 1) <
        width := by
    apply (div_lt_one hwidth).mp
    simpa [width] using hratio
  have hHalf :
      controllerDensity h / 2 <
        M.controllerReservoirDensity :=
    M.controllerReservoirDensity_gt_half
  have hHardHalf :
      hardSurvivorCoefficient Csv v B h <
        (controllerDensity h / 2) * width := by
    unfold hardSurvivorCoefficient
    dsimp [width] at hMain ⊢
    nlinarith
  exact hHardHalf.trans
    (mul_lt_mul_of_pos_right
      hHalf hwidth)

/-- A bound for the geometric ratio by a multiple of `√(kh)` reduces the
dimensionless condition to the hub-capacity coefficient. -/
theorem hardCapacity_ratio_of_sqrt_bound
    {h : Prime} {k B v : Nat}
    (Csv C : Real)
    (hCsv : 0 ≤ Csv) (hC : 0 ≤ C)
    (hwidth :
      0 <
        1 / (k : Real) -
          (B : Real) / (h.1 : Real))
    (hgeometric :
      ((B : Real) - 1) /
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) ≤
        C *
          Real.sqrt ((k * h.1 : Nat) : Real))
    (hhub :
      hubCapacityCoefficient
        (C * Csv) v k h < 1) :
    2 * Csv *
          (v : Real) ^ (controllerDensity h) *
          paperA (controllerDensity h) *
          ((B : Real) - 1) /
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) <
        1 := by
  have hnonneg :
      0 ≤
        2 * Csv *
          (v : Real) ^ (controllerDensity h) *
          paperA (controllerDensity h) := by
    have hA :
        0 ≤ paperA (controllerDensity h) :=
      (paperA_controllerDensity_pos h).le
    positivity
  have hmul :=
    mul_le_mul_of_nonneg_left
      hgeometric hnonneg
  unfold hubCapacityCoefficient at hhub
  have hEq :
      2 * Csv *
            (v : Real) ^ (controllerDensity h) *
            paperA (controllerDensity h) *
            (((B : Real) - 1) /
              (1 / (k : Real) -
                (B : Real) / (h.1 : Real))) =
        2 * Csv *
            (v : Real) ^ (controllerDensity h) *
            paperA (controllerDensity h) *
            ((B : Real) - 1) /
              (1 / (k : Real) -
                (B : Real) / (h.1 : Real)) := by
    field_simp [hwidth.ne']
  rw [hEq] at hmul
  have hUpper :
      2 * Csv *
            (v : Real) ^ (controllerDensity h) *
            paperA (controllerDensity h) *
            ((B : Real) - 1) /
              (1 / (k : Real) -
                (B : Real) / (h.1 : Real)) ≤
        2 * (C * Csv) *
          (v : Real) ^ (controllerDensity h) *
          Real.sqrt ((k * h.1 : Nat) : Real) *
          paperA (controllerDensity h) := by
    calc
      _ ≤
          (2 * Csv *
            (v : Real) ^ (controllerDensity h) *
            paperA (controllerDensity h)) *
              (C *
                Real.sqrt
                  ((k * h.1 : Nat) : Real)) :=
        hmul
      _ =
          2 * (C * Csv) *
            (v : Real) ^ (controllerDensity h) *
            Real.sqrt ((k * h.1 : Nat) : Real) *
            paperA (controllerDensity h) := by
        ring
  exact hUpper.trans_lt hhub

end Erdos279
