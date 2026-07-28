import Erdos279.DensityRatioWindow

/-!
# From density-mesh analytic data to the scheduled construction

This file is the final structural bridge before the genuinely analytic
inputs.  Given:

* the reciprocal-density mesh;
* the fixed-progression prime enumeration asymptotic; and
* the stagewise hard-survivor capacity inequalities,

it constructs `ScheduledPaperConstruction` and therefore the theorem at the
fixed level `k`.
-/

namespace Erdos279

open Filter

/-- The remaining hard-layer analytic data after a prime-target tail
matching has been fixed. -/
structure HardScheduleAnalyticData
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k) where
  scale : Nat → Nat
  scale_monotone : Monotone scale
  scale_unbounded : Tendsto scale atTop atTop
  stage_capacity :
    ∀ j,
      (hardSurvivors h M.cutoff
        (E.enumerations.primeTargetOldClasses T)
        (scale j) (scale (j + 1))).card ≤
      (hardStageControllerAnnulus
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff)
        k (scale j) (scale (j + 1))).card
  scale_separated :
    ∀ i,
      scale i / k ≤ scale (i + 2) / h.1

namespace HardScheduleAnalyticData

/-- All finite pairings and the common assignment are constructed from the
analytic stage-capacity data. -/
noncomputable def toScheduledPaperConstruction
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {E : MeshPrimeEnumerations M}
    {T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k}
    (A : HardScheduleAnalyticData E T)
    (hkh : k < h.1) :
    ScheduledPaperConstruction k where
  hub := h
  hub_gt_level := hkh
  modulus := M.modulus
  cutoff := M.cutoff
  classes := M.classes
  enumerations := E.enumerations
  primeTail := T
  scale := A.scale
  hardSchedule :=
    HardPairingSchedule.ofCardLe
      h M.modulus M.classes
      (oldControllerPrimes h M.cutoff)
      M.cutoff k
      (E.enumerations.primeTargetOldClasses T)
      A.scale A.stage_capacity
      (hardStageControllerAnnuli_pairwise_disjoint
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff)
        k A.scale A.scale_monotone
        A.scale_separated)
  scaleThreshold := A.scale 0 + 1
  scale_covers :=
    adjacent_scale_intervals_cover_tail
      A.scale A.scale_monotone A.scale_unbounded

end HardScheduleAnalyticData

/-- For one fixed density mesh, these are precisely the two analytic
existence statements still needed to obtain the scheduled construction. -/
structure MeshAnalyticInputs
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) where
  primeEnumerations : MeshPrimeEnumerations M
  hardSchedule :
    ∀ T : TailPrimeTargetMatching
      primeEnumerations.enumerations.periodic
      primeEnumerations.enumerations.complementary k,
      Nonempty
        (HardScheduleAnalyticData
          primeEnumerations T)

/-- Density-mesh analytic inputs imply the complete scheduled construction
at level `k`. -/
theorem exists_scheduledPaperConstruction_of_meshInputs
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (A : MeshAnalyticInputs M)
    (hh : 3 ≤ h.1) (hk : 0 < k)
    (hkh : k < h.1) :
    Nonempty (ScheduledPaperConstruction k) := by
  obtain ⟨T⟩ :=
    A.primeEnumerations.exists_tailMatching hh hk
  obtain ⟨H⟩ := A.hardSchedule T
  exact ⟨H.toScheduledPaperConstruction hkh⟩

/-- The same inputs already imply `P(k)` through the fully verified
construction and completion layers. -/
theorem P_of_meshAnalyticInputs
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (A : MeshAnalyticInputs M)
    (hh : 3 ≤ h.1) (hk : 3 ≤ k)
    (hkh : k < h.1) :
    P k := by
  obtain ⟨D⟩ :=
    exists_scheduledPaperConstruction_of_meshInputs
      A hh (by omega) hkh
  exact
    ScheduledPaperConstruction.P_of_scheduledPaperConstruction
      hk D

/-- The exact remaining global analytic obligation in density-mesh form.
Unlike an axiom, this is an ordinary proposition that must be supplied by
kernel-checked PNT/Mertens/Selberg--Delange/sieve proofs. -/
def RemainingMeshAnalyticConstruction : Prop :=
  ∀ k : Nat, 3 ≤ k →
    ∃ h : Prime,
      3 ≤ h.1 ∧
      k < h.1 ∧
      ∃ M : OldControllerPrimeDensityMesh h k,
        Nonempty (MeshAnalyticInputs M)

/-- Once the remaining analytic obligation is proved, the final theorem is
an immediate kernel-checked consequence. -/
theorem globalAffirmative_of_meshAnalyticConstruction
    (build : RemainingMeshAnalyticConstruction) :
    GlobalAffirmative := by
  intro k hk
  obtain ⟨h, hh, hkh, M, ⟨A⟩⟩ := build k hk
  exact P_of_meshAnalyticInputs A hh hk hkh

end Erdos279
