import Erdos279.OldPrimeCoverage

/-!
# Hard pairing schedules with a scale-dependent old-prime cutoff

The deterministic sieve at stage `j` uses all controller primes up to
`z j`, not one fixed finite cutoff.  This module generalizes the structural
coverage argument to exactly that setting.
-/

namespace Erdos279

/-- A globally compatible family of finite hard-stage pairings with
scale-dependent old-class vectors. -/
structure VariableHardPairingSchedule
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat) where
  oldClasses :
    ∀ j, OldPrimeClasses h (z j)
  stage :
    ∀ j,
      HardStagePairing h L R H (z j) k
        (scale j) (scale (j + 1)) (oldClasses j)
  base : ShiftedAssignment
  assignment : ShiftedAssignment
  assignment_at_controller :
    ∀ (j : Nat)
      (i : Fin
        (hardSurvivors h (z j) (oldClasses j)
          (scale j) (scale (j + 1))).card),
      (assignment ((stage j).controller i) : Nat) =
        (controllerResidue
          ((stage j).controller i)
          ((stage j).target i) : Nat)
  assignment_matches_old :
    ∀ (j : Nat) (p : Prime),
      InControllerProgression h p →
      p.1 ≤ z j →
      (assignment p : Nat) =
        ((oldClasses j).residue p : Nat)
  assignment_of_not_in_reservoir :
    ∀ p : Prime,
      ¬ InControllerReservoir h L R H p →
      assignment p =
        base p
  cutoff_mature :
    ∀ j, k * z j ≤ scale j

namespace VariableHardPairingSchedule

/-- Every target recorded in one variable-cutoff stage is covered by the
single global assignment. -/
theorem assignment_covers_stage
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z scale : Nat → Nat} {k : Nat}
    (S : VariableHardPairingSchedule h L R H z scale k)
    (hk : 0 < k)
    (j : Nat)
    (i : Fin
      (hardSurvivors h (z j) (S.oldClasses j)
        (scale j) (scale (j + 1))).card) :
    ShiftedMatureCovers k ((S.stage j).target i)
      S.assignment := by
  exact
    (S.stage j).assignment_covers
      hk S.assignment
      (S.assignment_at_controller j)
      i

/-- A variable-cutoff schedule whose scale intervals cover a tail covers
every sufficiently large hard target. -/
theorem covers_hardForm_tail
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z scale : Nat → Nat} {k : Nat}
    (S : VariableHardPairingSchedule h L R H z scale k)
    (hk : 0 < k)
    (scaleThreshold : Nat)
    (hscale :
      ∀ m, scaleThreshold ≤ m →
        ∃ j, scale j < m ∧ m ≤ scale (j + 1)) :
    ∀ m,
      scaleThreshold ≤ m →
      HasHardForm h m →
      ShiftedMatureCovers k m S.assignment := by
  intro m hmLarge hmHard
  obtain ⟨j, hmLower, hmUpper⟩ :=
    hscale m hmLarge
  by_cases hmAvoids :
      AvoidsOldClasses (S.oldClasses j) m
  · have hmSurvivor :
        m ∈ hardSurvivors h (z j) (S.oldClasses j)
          (scale j) (scale (j + 1)) :=
      mem_hardSurvivors.mpr
        ⟨hmLower, hmUpper, hmHard, hmAvoids⟩
    obtain ⟨i, hi⟩ :=
      (S.stage j).target_surjective m hmSurvivor
    have hcover :=
      S.assignment_covers_stage hk j i
    simpa [hi] using hcover
  · have hmOldMature :
        k * z j ≤ m :=
      (S.cutoff_mature j).trans
        (Nat.le_of_lt hmLower)
    exact
      covered_of_not_avoidsOldClasses
        (S.oldClasses j)
        S.assignment
        (S.assignment_matches_old j)
        hmOldMature hmAvoids

end VariableHardPairingSchedule

end Erdos279
