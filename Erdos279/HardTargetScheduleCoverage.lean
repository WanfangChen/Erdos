import Erdos279.OldPrimeCoverage

/-!
# Covering the complete hard-target tail

This file combines:

* a scale sequence covering a tail of the natural numbers;
* the old-prime complement argument; and
* the collision-free all-stage pairing schedule.

It proves hard-target coverage for the one final assignment.  The remaining
analytic obligation is now exactly the stagewise capacity inequality used
to build the schedule.
-/

namespace Erdos279

/-- The structural output of the hard-target construction. -/
structure ScheduledHardTargetConstruction
    (k : Nat) (h : Prime) where
  shifted : ShiftedAssignment
  threshold : Nat
  hardForm :
    ∀ m : Nat, threshold ≤ m →
      HasHardForm h m →
      ShiftedMatureCovers k m shifted

namespace HardPairingSchedule

/-- A schedule whose scales cover a tail covers every large hard target:
old-prime hits use their frozen class, and genuine survivors use the
stage pairing. -/
theorem covers_hardForm_tail
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (hk : 0 < k)
    (base : ShiftedAssignment)
    (hbaseOld :
      ∀ p : Prime, InControllerProgression h p →
        p.1 ≤ z →
        (base p : Nat) = (a.residue p : Nat))
    (holdOutsideS :
      ∀ p : Prime, InControllerProgression h p →
        p.1 ≤ z →
        ¬ InControllerReservoir h L R H p)
    (scaleThreshold : Nat)
    (hscale :
      ∀ m, scaleThreshold ≤ m →
        ∃ j, scale j < m ∧ m ≤ scale (j + 1)) :
    ∀ m,
      max scaleThreshold (k * z) ≤ m →
      HasHardForm h m →
      ShiftedMatureCovers k m (S.assignment base) := by
  intro m hmLarge hmHard
  have hmScale : scaleThreshold ≤ m :=
    (le_max_left _ _).trans hmLarge
  have hmOldMature : k * z ≤ m :=
    (le_max_right _ _).trans hmLarge
  by_cases hmAvoids : AvoidsOldClasses a m
  · obtain ⟨j, hmLower, hmUpper⟩ :=
      hscale m hmScale
    have hmSurvivor :
        m ∈ hardSurvivors h z a
          (scale j) (scale (j + 1)) :=
      mem_hardSurvivors.mpr
        ⟨hmLower, hmUpper, hmHard, hmAvoids⟩
    obtain ⟨i, hi⟩ :=
      (S.stage j).target_surjective m hmSurvivor
    have hcover :=
      S.assignment_covers hk base
        (⟨j, i⟩ : HardScheduleIndex h z a scale)
    simpa [HardPairingSchedule.target, hi] using hcover
  · exact
      covered_of_not_avoidsOldClasses
        a (S.assignment base)
        (fun p hpG hpz => by
          rw [S.assignment_of_not_in_reservoir
            base p (holdOutsideS p hpG hpz)]
          exact hbaseOld p hpG hpz)
        hmOldMature hmAvoids

/-- Specialization when the old classes are literally the restriction of
the base assignment and `H` is the canonical set of old controller primes. -/
noncomputable def toScheduledHardTargetConstruction
    {h L : Prime} {R : Finset Nat}
    {z k : Nat}
    (base : ShiftedAssignment)
    (hnonzero :
      ∀ p : Prime, InControllerProgression h p →
        p.1 ≤ z → (base p : Nat) ≠ 0)
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R
      (oldControllerPrimes h z) z k
      (oldPrimeClassesOfAssignment
        h z base hnonzero) scale)
    (hk : 0 < k)
    (scaleThreshold : Nat)
    (hscale :
      ∀ m, scaleThreshold ≤ m →
        ∃ j, scale j < m ∧ m ≤ scale (j + 1)) :
    ScheduledHardTargetConstruction k h where
  shifted := S.assignment base
  threshold := max scaleThreshold (k * z)
  hardForm := by
    exact
      S.covers_hardForm_tail
        hk base
        (fun _p _hpG _hpz => rfl)
        (fun p hpG hpz hpS =>
          hpS.not_mem_old
            (mem_oldControllerPrimes.mpr
              ⟨hpG, hpz⟩))
        scaleThreshold hscale

end HardPairingSchedule

end Erdos279
