import Erdos279.DynamicHardScheduleCore

/-!
# Globalization of the recursive hard schedule

Pairwise disjoint annuli make every reservoir coordinate a one-time
coordinate.  This file constructs the one final assignment, proves that it
agrees with the recursively read old classes, and packages the result as a
`VariableHardPairingSchedule`.
-/

namespace Erdos279

/-- The controller annulus used at recursive stage `j`. -/
noncomputable def dynamicHardAnnulus
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (k : Nat)
    (scale : Nat → Nat) (j : Nat) : Finset Prime :=
  hardStageControllerAnnulus h L R H k
    (scale j) (scale (j + 1))

/-- The final assignment obtained by installing the unique value attached
to every annulus coordinate, and retaining the base value elsewhere. -/
noncomputable def dynamicFinalAssignment
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p =>
    if hex :
        ∃ j : Nat,
          p ∈ dynamicHardAnnulus h L R H k scale j then
      installedHardStageValue
        (dynamicHardStage h L R H z scale k
          hcapacity base (Classical.choose hex))
        p
    else
      base p

/-- A cutoff is ready at stage `j` when every controller prime below it is
either a permanently nonzero coordinate belonging to no annulus, or
belongs to an already activated annulus.  The first alternative includes
the harmless gaps created by integral scale rounding. -/
def DynamicCutoffReady
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment) : Prop :=
  ∀ (j : Nat) (p : Prime),
    InControllerProgression h p →
    p.1 ≤ z j →
    ((∀ i : Nat,
        p ∉ dynamicHardAnnulus h L R H k scale i) ∧
        (base p : Nat) ≠ 0) ∨
      ∃ i : Nat, i < j ∧
        p ∈ dynamicHardAnnulus h L R H k scale i

/-- A prime belonging to no processing annulus is never changed by the
recursive finite-stage assignments. -/
theorem dynamicAssignmentBefore_eq_base_of_never_mem
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp :
      ∀ i : Nat,
        p ∉ dynamicHardAnnulus h L R H k scale i) :
    ∀ j,
      dynamicAssignmentBefore h L R H z scale k
        hcapacity base j p = base p := by
  intro j
  induction j with
  | zero =>
      rfl
  | succ j ih =>
      rw [dynamicAssignmentBefore_succ]
      rw [installHardStage_of_not_mem]
      · exact ih
      · exact hp j

/-- In particular, a prime outside the reservoir belongs to no processing
annulus and is never changed. -/
theorem dynamicAssignmentBefore_eq_base_of_not_reservoir
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    ∀ j,
      dynamicAssignmentBefore h L R H z scale k
        hcapacity base j p = base p := by
  apply dynamicAssignmentBefore_eq_base_of_never_mem
  intro i hpMem
  exact hp (mem_hardStageControllerAnnulus.mp hpMem).2.2

/-- After a prime's annulus has been activated, all subsequent recursive
assignments retain its installed value. -/
theorem dynamicAssignmentBefore_eq_installed_of_mem
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint :
      ∀ i j, i ≠ j →
        Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (p : Prime) (i j : Nat)
    (hp :
      p ∈ dynamicHardAnnulus h L R H k scale i)
    (hij : i < j) :
    dynamicAssignmentBefore h L R H z scale k
        hcapacity base j p =
      installedHardStageValue
        (dynamicHardStage h L R H z scale k
          hcapacity base i) p := by
  induction j with
  | zero =>
      omega
  | succ j ih =>
      rw [dynamicAssignmentBefore_succ]
      by_cases hEq : i = j
      · subst j
        have hp' :
            p ∈ hardStageControllerAnnulus h L R H k
              (scale i) (scale (i + 1)) := by
          simpa [dynamicHardAnnulus] using hp
        simp [installHardStage, hp']
      · have hiJ : i < j := by omega
        rw [installHardStage_of_not_mem]
        · exact ih hiJ
        · intro hpJ
          exact
            (Finset.disjoint_left.mp
              (hdisjoint i j hEq)) hp hpJ

/-- On a prime belonging to stage `i`, the final assignment is exactly the
value installed by stage `i`. -/
theorem dynamicFinalAssignment_eq_installed_of_mem
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint :
      ∀ i j, i ≠ j →
        Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (p : Prime) (i : Nat)
    (hp :
      p ∈ dynamicHardAnnulus h L R H k scale i) :
    dynamicFinalAssignment h L R H z scale k
        hcapacity base p =
      installedHardStageValue
        (dynamicHardStage h L R H z scale k
          hcapacity base i) p := by
  classical
  let hex :
      ∃ j : Nat,
        p ∈ dynamicHardAnnulus h L R H k scale j :=
    ⟨i, hp⟩
  rw [dynamicFinalAssignment]
  simp only [dif_pos hex]
  have hpChosen :
      p ∈ dynamicHardAnnulus h L R H k scale
        (Classical.choose hex) :=
    Classical.choose_spec hex
  have hChosen : Classical.choose hex = i := by
    by_contra hne
    exact
      (Finset.disjoint_left.mp
        (hdisjoint (Classical.choose hex) i hne))
        hpChosen hp
  exact congrArg
    (fun t =>
      installedHardStageValue
        (dynamicHardStage h L R H z scale k
          hcapacity base t) p)
    hChosen

/-- The final assignment records every prescribed paired residue. -/
theorem dynamicFinalAssignment_at_controller
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint :
      ∀ i j, i ≠ j →
        Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (j : Nat)
    (i : Fin
      (hardSurvivors h (z j)
        (dynamicOldClasses h L R H z scale k
          hcapacity base j)
        (scale j) (scale (j + 1))).card) :
    (dynamicFinalAssignment h L R H z scale k
        hcapacity base
        ((dynamicHardStage h L R H z scale k
          hcapacity base j).controller i) : Nat) =
      (controllerResidue
        ((dynamicHardStage h L R H z scale k
          hcapacity base j).controller i)
        ((dynamicHardStage h L R H z scale k
          hcapacity base j).target i) : Nat) := by
  let B :=
    dynamicHardStage h L R H z scale k
      hcapacity base j
  rw [dynamicFinalAssignment_eq_installed_of_mem
    h L R H z scale k hcapacity base hdisjoint
    (B.controller i) j]
  · exact installedHardStageValue_at_controller B i
  · exact B.controller_mem i

/-- A coordinate belonging to no processing annulus retains its base value
in the final assignment. -/
theorem dynamicFinalAssignment_of_never_mem
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp :
      ∀ i : Nat,
        p ∉ dynamicHardAnnulus h L R H k scale i) :
    dynamicFinalAssignment h L R H z scale k
      hcapacity base p = base p := by
  classical
  rw [dynamicFinalAssignment]
  apply dif_neg
  intro hex
  obtain ⟨j, hpj⟩ := hex
  exact hp j hpj

/-- Coordinates outside the controller reservoir retain their base value in
the final assignment. -/
theorem dynamicFinalAssignment_of_not_in_reservoir
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    dynamicFinalAssignment h L R H z scale k
      hcapacity base p = base p := by
  apply dynamicFinalAssignment_of_never_mem
  intro i hpMem
  exact hp (mem_hardStageControllerAnnulus.mp hpMem).2.2

/-- Under the readiness condition, the final assignment agrees with every
scale-dependent old-class vector read by the recursion. -/
theorem dynamicFinalAssignment_matches_old
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint :
      ∀ i j, i ≠ j →
        Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (hready :
      DynamicCutoffReady h L R H z scale k base)
    (j : Nat) (p : Prime)
    (hpG : InControllerProgression h p)
    (hpz : p.1 ≤ z j) :
    (dynamicFinalAssignment h L R H z scale k
        hcapacity base p : Nat) =
      ((dynamicOldClasses h L R H z scale k
        hcapacity base j).residue p : Nat) := by
  rcases hready j p hpG hpz with
    ⟨hpNever, hpBaseNonzero⟩ | ⟨i, hiJ, hpI⟩
  · have hBefore :=
      dynamicAssignmentBefore_eq_base_of_never_mem
        h L R H z scale k hcapacity base p hpNever j
    have hFinal :=
      dynamicFinalAssignment_of_never_mem
        h L R H z scale k hcapacity base p hpNever
    change
      (dynamicFinalAssignment h L R H z scale k
          hcapacity base p : Nat) =
        (forceNonzeroResidue p
          (dynamicAssignmentBefore h L R H z scale k
            hcapacity base j p) : Nat)
    rw [hFinal, hBefore,
      forceNonzeroResidue_eq_self p (base p) hpBaseNonzero]
  · have hBefore :=
      dynamicAssignmentBefore_eq_installed_of_mem
        h L R H z scale k hcapacity base hdisjoint
        p i j hpI hiJ
    have hFinal :=
      dynamicFinalAssignment_eq_installed_of_mem
        h L R H z scale k hcapacity base hdisjoint
        p i hpI
    have hInstalledNonzero :
        (installedHardStageValue
          (dynamicHardStage h L R H z scale k
            hcapacity base i) p : Nat) ≠ 0 :=
      installedHardStageValue_ne_zero
        (dynamicHardStage h L R H z scale k
          hcapacity base i) p
    change
      (dynamicFinalAssignment h L R H z scale k
          hcapacity base p : Nat) =
        (forceNonzeroResidue p
          (dynamicAssignmentBefore h L R H z scale k
            hcapacity base j p) : Nat)
    rw [hFinal, hBefore,
      forceNonzeroResidue_eq_self _ _ hInstalledNonzero]

/-- The recursive construction produces a globally compatible
variable-cutoff pairing schedule. -/
noncomputable def variableHardPairingScheduleOfCapacity
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint :
      ∀ i j, i ≠ j →
        Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (hready :
      DynamicCutoffReady h L R H z scale k base)
    (hmature : ∀ j, k * z j ≤ scale j) :
    VariableHardPairingSchedule h L R H z scale k where
  oldClasses j :=
    dynamicOldClasses h L R H z scale k
      hcapacity base j
  stage j :=
    dynamicHardStage h L R H z scale k
      hcapacity base j
  base := base
  assignment :=
    dynamicFinalAssignment h L R H z scale k
      hcapacity base
  assignment_at_controller :=
    dynamicFinalAssignment_at_controller
      h L R H z scale k hcapacity base hdisjoint
  assignment_matches_old :=
    dynamicFinalAssignment_matches_old
      h L R H z scale k hcapacity base
      hdisjoint hready
  assignment_of_not_in_reservoir :=
    dynamicFinalAssignment_of_not_in_reservoir
      h L R H z scale k hcapacity base
  cutoff_mature := hmature

end Erdos279
