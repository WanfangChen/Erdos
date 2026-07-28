import Erdos279.DynamicScaleGeometry
import Erdos279.ScaleTail

/-!
# Analytic data for the dynamic hard schedule

This is the corrected structural interface for §3.2.  Its cutoff varies
with the scale exactly as in Proposition 2.1, and its finite pairings are
therefore compatible with the uniform sieve statement.
-/

namespace Erdos279

open Filter

/-- Normalize only controller-progression coordinates, replacing the
zero residue by the canonical nonzero residue `1`.  Coordinates already
carrying a nonzero residue are unchanged. -/
noncomputable def controllerNonzeroBase
    (h : Prime) (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p =>
    if InControllerProgression h p then
      forceNonzeroResidue p (base p)
    else
      base p

theorem controllerNonzeroBase_ne_zero
    (h : Prime) (base : ShiftedAssignment)
    (p : Prime)
    (hpG : InControllerProgression h p) :
    (controllerNonzeroBase h base p : Nat) ≠ 0 := by
  rw [controllerNonzeroBase, if_pos hpG]
  exact forceNonzeroResidue_ne_zero p (base p)

theorem controllerNonzeroBase_eq_of_not_progression
    (h : Prime) (base : ShiftedAssignment)
    (p : Prime)
    (hpG : ¬ InControllerProgression h p) :
    controllerNonzeroBase h base p = base p := by
  simp [controllerNonzeroBase, hpG]

theorem controllerNonzeroBase_eq_of_ne_zero
    (h : Prime) (base : ShiftedAssignment)
    (p : Prime)
    (hp : (base p : Nat) ≠ 0) :
    controllerNonzeroBase h base p = base p := by
  classical
  by_cases hpG : InControllerProgression h p
  · rw [controllerNonzeroBase, if_pos hpG]
    exact forceNonzeroResidue_eq_self p (base p) hp
  · exact controllerNonzeroBase_eq_of_not_progression
      h base p hpG

/-- All scale and capacity facts needed to construct the recursive
variable-cutoff hard schedule. -/
structure DynamicHardScheduleAnalyticData
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (v k : Nat) where
  scale : Nat → Nat
  scale_monotone : Monotone scale
  scale_unbounded : Tendsto scale atTop atTop
  stage_capacity :
    ∀ (j : Nat)
      (a : OldPrimeClasses h
        (stageOldPrimeCutoff v (scale j))),
      (hardSurvivors h
        (stageOldPrimeCutoff v (scale j)) a
        (scale j) (scale (j + 1))).card ≤
      (dynamicHardAnnulus h L R H k scale j).card
  scale_separated :
    ∀ i, scale i / k ≤ scale (i + 2) / h.1
  cutoff_below_future :
    ∀ j i, j ≤ i →
      stageOldPrimeCutoff v (scale j) <
        scale (i + 1) / h.1
  cutoff_mature :
    ∀ j,
      k * stageOldPrimeCutoff v (scale j) ≤
        scale j

namespace DynamicHardScheduleAnalyticData

/-- The scale intervals supplied by the analytic data cover a tail. -/
theorem scale_covers
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k) :
    ∀ m, A.scale 0 + 1 ≤ m →
      ∃ j, A.scale j < m ∧ m ≤ A.scale (j + 1) :=
  adjacent_scale_intervals_cover_tail
    A.scale A.scale_monotone A.scale_unbounded

/-- The analytic package constructs one globally compatible recursive
schedule while preserving every coordinate outside the controller
reservoir. -/
noncomputable def toVariableHardPairingSchedule
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k)
    (base : ShiftedAssignment)
    (hbase :
      ∀ p : Prime,
        InControllerProgression h p →
        ¬ InControllerReservoir h L R H p →
        (base p : Nat) ≠ 0) :
    VariableHardPairingSchedule
      h L R H
      (fun j => stageOldPrimeCutoff v (A.scale j))
      A.scale k := by
  let prepared :=
    prepareDynamicBase h L R H A.scale k base
  exact
    variableHardPairingScheduleOfCapacity
      h L R H
      (fun j => stageOldPrimeCutoff v (A.scale j))
      A.scale k A.stage_capacity prepared
      (hardStageControllerAnnuli_pairwise_disjoint
        h L R H k A.scale A.scale_monotone
        A.scale_separated)
      (dynamicCutoffReady_of_below_future_annuli
        h L R H
        (fun j => stageOldPrimeCutoff v (A.scale j))
        A.scale k base hbase A.cutoff_below_future)
      A.cutoff_mature

/-- Outside the controller reservoir, the schedule obtained from `A`
agrees with the original, unprepared base assignment. -/
theorem toVariableHardPairingSchedule_of_not_in_reservoir
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k)
    (base : ShiftedAssignment)
    (hbase :
      ∀ p : Prime,
        InControllerProgression h p →
        ¬ InControllerReservoir h L R H p →
        (base p : Nat) ≠ 0)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    (A.toVariableHardPairingSchedule base hbase).assignment p =
      base p := by
  rw [(A.toVariableHardPairingSchedule base hbase).assignment_of_not_in_reservoir
    p hp]
  exact prepareDynamicBase_of_not_in_reservoir
    h L R H A.scale k base p hp

/-- A canonical constructor needing no external nonvanishing hypothesis:
normalize zero controller classes first, then run the recursive schedule. -/
noncomputable def toVariableHardPairingScheduleWithNonzeroBase
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k)
    (base : ShiftedAssignment) :
    VariableHardPairingSchedule
      h L R H
      (fun j => stageOldPrimeCutoff v (A.scale j))
      A.scale k :=
  A.toVariableHardPairingSchedule
    (controllerNonzeroBase h base)
    (fun p hpG _hpS =>
      controllerNonzeroBase_ne_zero h base p hpG)

/-- Outside the controller reservoir, the canonical dynamic schedule
agrees with the normalized base. -/
theorem toVariableHardPairingScheduleWithNonzeroBase_of_not_in_reservoir
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    (A.toVariableHardPairingScheduleWithNonzeroBase base).assignment p =
      controllerNonzeroBase h base p :=
  A.toVariableHardPairingSchedule_of_not_in_reservoir
    (controllerNonzeroBase h base)
    (fun q hqG _hqS =>
      controllerNonzeroBase_ne_zero h base q hqG)
    p hp

end DynamicHardScheduleAnalyticData

end Erdos279
