import Erdos279.HardTargetScheduleCoverage
import Erdos279.ConstructionCore

/-!
# Combining the prime-target and hard-target schedules

This file joins §3.1 and §3.2 on one final assignment.  It verifies that
the hard-stage schedule changes only `S`-coordinates, while the isolated
prime construction uses only the hub, `H`, and `T`.  Thus both infinite
coverage conclusions coexist and produce `PaperConstructionCore`.
-/

namespace Erdos279

namespace PeriodicComplementaryEnumerations

/-- The old-prime classes obtained from the §3.1 assignment when
`H = oldControllerPrimes h z`. -/
noncomputable def primeTargetOldClasses
    {h L : Prime} {R : Finset Nat}
    {z k : Nat}
    (E : PeriodicComplementaryEnumerations h L R
      (oldControllerPrimes h z))
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k) :
    OldPrimeClasses h z where
  residue := E.primeTargetAssignment T
  nonzero := by
    intro p hpG hpz
    have hpOld :
        p ∈ oldControllerPrimes h z :=
      mem_oldControllerPrimes.mpr ⟨hpG, hpz⟩
    rw [E.primeTargetAssignment_old T hpOld]
    omega

end PeriodicComplementaryEnumerations

/-- The remaining explicit schedule data for one level `k`, after all
finite CRT, matching, and compatibility arguments have been discharged. -/
structure ScheduledPaperConstruction (k : Nat) where
  hub : Prime
  hub_gt_level : k < hub.1
  modulus : Prime
  cutoff : Nat
  classes : Finset Nat
  enumerations :
    PeriodicComplementaryEnumerations
      hub modulus classes
        (oldControllerPrimes hub cutoff)
  primeTail :
    TailPrimeTargetMatching
      enumerations.periodic
      enumerations.complementary k
  scale : Nat → Nat
  hardSchedule :
    HardPairingSchedule
      hub modulus classes
      (oldControllerPrimes hub cutoff)
      cutoff k
      (enumerations.primeTargetOldClasses primeTail)
      scale
  scaleThreshold : Nat
  scale_covers :
    ∀ m, scaleThreshold ≤ m →
      ∃ j, scale j < m ∧ m ≤ scale (j + 1)

namespace ScheduledPaperConstruction

noncomputable def primeBase
    {k : Nat} (D : ScheduledPaperConstruction k) :
    ShiftedAssignment :=
  D.enumerations.primeTargetAssignment D.primeTail

noncomputable def finalAssignment
    {k : Nat} (D : ScheduledPaperConstruction k) :
    ShiftedAssignment :=
  D.hardSchedule.assignment D.primeBase

noncomputable def primeThreshold
    {k : Nat} (D : ScheduledPaperConstruction k) : Nat :=
  max
    (PeriodicComplementaryEnumerations.primePrefixBound
      D.enumerations.complementary
      D.primeTail.offset)
    (max (k * D.hub.1)
      (oldPrimeMaturityBound k
        (oldControllerPrimes D.hub D.cutoff)))

def hardThreshold
    {k : Nat} (D : ScheduledPaperConstruction k) : Nat :=
  max D.scaleThreshold (k * D.cutoff)

noncomputable def threshold
    {k : Nat} (D : ScheduledPaperConstruction k) : Nat :=
  max D.primeThreshold D.hardThreshold

private theorem hub_not_in_controllerReservoir
    {k : Nat} (D : ScheduledPaperConstruction k) :
    ¬ InControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff)
      D.hub := by
  intro hh
  exact inControllerProgression_ne_hub
    hh.inControllerProgression rfl

private theorem periodic_not_in_controllerReservoir
    {k : Nat} (D : ScheduledPaperConstruction k)
    {p : Prime}
    (hp : InPeriodicReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p) :
    ¬ InControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p := by
  intro hpS
  exact
    not_inPeriodic_and_inControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p
      ⟨hp, hpS⟩

private theorem old_not_in_controllerReservoir
    {k : Nat} (D : ScheduledPaperConstruction k)
    {p : Prime}
    (hp : p ∈ oldControllerPrimes D.hub D.cutoff) :
    ¬ InControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p := by
  intro hpS
  exact hpS.not_mem_old hp

theorem finalAssignment_hub
    {k : Nat} (D : ScheduledPaperConstruction k) :
    (D.finalAssignment D.hub : Nat) = 1 := by
  rw [finalAssignment,
    D.hardSchedule.assignment_of_not_in_reservoir
      D.primeBase D.hub D.hub_not_in_controllerReservoir]
  exact D.enumerations.primeTargetAssignment_hub D.primeTail

theorem finalAssignment_outside_zero
    {k : Nat} (D : ScheduledPaperConstruction k)
    (q : Prime) (hqh : q ≠ D.hub)
    (hqG : ¬ InControllerProgression D.hub q) :
    (D.finalAssignment q : Nat) = 0 := by
  have hqNotS :
      ¬ InControllerReservoir
        D.hub D.modulus D.classes
        (oldControllerPrimes D.hub D.cutoff) q := by
    intro hqS
    exact hqG hqS.inControllerProgression
  rw [finalAssignment,
    D.hardSchedule.assignment_of_not_in_reservoir
      D.primeBase q hqNotS]
  exact
    D.enumerations.primeTargetAssignment_outside_zero
      (fun ℓ hℓ =>
        (mem_oldControllerPrimes.mp hℓ).1)
      D.primeTail q hqh hqG

theorem finalAssignment_old
    {k : Nat} (D : ScheduledPaperConstruction k)
    {p : Prime}
    (hp : p ∈ oldControllerPrimes D.hub D.cutoff) :
    (D.finalAssignment p : Nat) = 1 := by
  rw [finalAssignment,
    D.hardSchedule.assignment_of_not_in_reservoir
      D.primeBase p (D.old_not_in_controllerReservoir hp)]
  exact
    D.enumerations.primeTargetAssignment_old
      D.primeTail hp

theorem finalAssignment_periodic
    {k : Nat} (D : ScheduledPaperConstruction k)
    {p : Prime}
    (hp : InPeriodicReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p) :
    D.finalAssignment p = D.primeBase p := by
  exact
    D.hardSchedule.assignment_of_not_in_reservoir
      D.primeBase p
      (D.periodic_not_in_controllerReservoir hp)

theorem final_covers_large_complementary
    {k : Nat} (D : ScheduledPaperConstruction k)
    (q : Prime)
    (hq : IsComplementaryPrimeTarget D.hub
      (oldControllerPrimes D.hub D.cutoff) q)
    (hqLarge :
      PeriodicComplementaryEnumerations.primePrefixBound
        D.enumerations.complementary
        D.primeTail.offset ≤ q.1) :
    ShiftedMatureCovers k q.1 D.finalAssignment := by
  obtain ⟨i, hiq⟩ :=
    D.enumerations.complementary_surjective q hq
  have hvalue :
      PeriodicComplementaryEnumerations.primePrefixBound
          D.enumerations.complementary
          D.primeTail.offset ≤
        (D.enumerations.complementary i).1 := by
    simpa [hiq] using hqLarge
  have hoffset : D.primeTail.offset ≤ i :=
    PeriodicComplementaryEnumerations.index_ge_of_primePrefixBound_le
      D.enumerations.complementary
      D.primeTail.offset i hvalue
  let j := i - D.primeTail.offset
  have hindex : D.primeTail.offset + j = i := by
    dsimp [j]
    exact Nat.add_sub_of_le hoffset
  let pair := D.primeTail.matching.pair j
  have hpair :
      pair =
        { controller :=
            D.enumerations.periodic
              (D.primeTail.offset + j)
          target :=
            D.enumerations.complementary
              (D.primeTail.offset + j) } := by
    exact D.primeTail.pair_eq j
  have hpT :
      InPeriodicReservoir
        D.hub D.modulus D.classes
        (oldControllerPrimes D.hub D.cutoff)
        pair.controller := by
    rw [hpair]
    exact
      D.enumerations.periodic_mem
        (D.primeTail.offset + j)
  have hfinalResidue :
      (D.finalAssignment pair.controller : Nat) =
        (pair.residue : Nat) := by
    rw [D.finalAssignment_periodic hpT]
    exact congrArg Fin.val
      (D.primeTail.matching.assignment_at_controller
        (hubOldPrimeAssignment D.hub
          (oldControllerPrimes D.hub D.cutoff)) j)
  have hcover :
      ShiftedMatureCovers k pair.target.1
        D.finalAssignment :=
    pair.covers_of_assignment
      (D.primeTail.matching.admissible j)
      hfinalResidue
  have htarget : pair.target = q := by
    rw [hpair]
    simpa [hindex, hiq]
  simpa [htarget] using hcover

theorem final_covers_prime_tail
    {k : Nat} (D : ScheduledPaperConstruction k) :
    ∀ m, D.primeThreshold ≤ m →
      IsPrime m →
      ShiftedMatureCovers k m D.finalAssignment := by
  intro m hm hmPrime
  let q : Prime := ⟨m, hmPrime⟩
  have hprefix :
      PeriodicComplementaryEnumerations.primePrefixBound
          D.enumerations.complementary
          D.primeTail.offset ≤ q.1 :=
    (le_max_left _ _).trans hm
  have hhub : k * D.hub.1 ≤ q.1 :=
    (le_max_left (k * D.hub.1)
      (oldPrimeMaturityBound k
        (oldControllerPrimes D.hub D.cutoff))).trans
      ((le_max_right _ _).trans hm)
  have hold :
      oldPrimeMaturityBound k
          (oldControllerPrimes D.hub D.cutoff) ≤ q.1 :=
    (le_max_right (k * D.hub.1)
      (oldPrimeMaturityBound k
        (oldControllerPrimes D.hub D.cutoff))).trans
      ((le_max_right _ _).trans hm)
  by_cases hcomp :
      IsComplementaryPrimeTarget D.hub
        (oldControllerPrimes D.hub D.cutoff) q
  · exact D.final_covers_large_complementary q hcomp hprefix
  · by_cases hqG : InControllerProgression D.hub q
    · refine
        ⟨D.hub,
          hhub.trans (Nat.le_add_right q.1 1), ?_⟩
      rw [D.finalAssignment_hub]
      exact hqG
    · have hnotAll :
        ¬ ∀ ℓ ∈ oldControllerPrimes D.hub D.cutoff,
          q.1 % ℓ.1 ≠ 1 := by
        intro hall
        exact hcomp ⟨hqG, hall⟩
      push_neg at hnotAll
      obtain ⟨ℓ, hℓ, hqℓ⟩ := hnotAll
      refine ⟨ℓ, ?_, ?_⟩
      · exact
          (oldPrimeMaturity_le k
            (oldControllerPrimes D.hub D.cutoff) hℓ).trans
            hold |>.trans (Nat.le_add_right q.1 1)
      · rw [D.finalAssignment_old hℓ]
        exact hqℓ

theorem final_covers_hard_tail
    {k : Nat} (D : ScheduledPaperConstruction k)
    (hk : 0 < k) :
    ∀ m, D.hardThreshold ≤ m →
      HasHardForm D.hub m →
      ShiftedMatureCovers k m D.finalAssignment := by
  exact
    D.hardSchedule.covers_hardForm_tail
      hk D.primeBase
      (fun _p _hpG _hpz => rfl)
      (fun p hpG hpz hpS =>
        hpS.not_mem_old
          (mem_oldControllerPrimes.mpr
            ⟨hpG, hpz⟩))
      D.scaleThreshold D.scale_covers

/-- The combined schedule produces the exact construction core consumed by
the already verified four-case completion theorem. -/
noncomputable def toPaperConstructionCore
    {k : Nat} (D : ScheduledPaperConstruction k)
    (hk : 0 < k) :
    PaperConstructionCore k where
  hub := D.hub
  hub_gt_level := D.hub_gt_level
  shifted := D.finalAssignment
  threshold := D.threshold
  hub_residue := D.finalAssignment_hub
  outside_zero := D.finalAssignment_outside_zero
  hardForm := by
    intro m hm hhard
    exact D.final_covers_hard_tail hk m
      ((le_max_right _ _).trans hm) hhard
  primeTarget := by
    intro m hm hprime
    exact D.final_covers_prime_tail m
      ((le_max_left _ _).trans hm) hprime

theorem P_of_scheduledPaperConstruction
    {k : Nat} (hk : 3 ≤ k)
    (D : ScheduledPaperConstruction k) :
    P k :=
  P_of_paperConstructionCore hk
    (D.toPaperConstructionCore (by omega))

def RemainingScheduledPaperConstruction : Prop :=
  ∀ k : Nat, 3 ≤ k →
    Nonempty (ScheduledPaperConstruction k)

theorem globalAffirmative_of_scheduledPaperConstruction
    (build : RemainingScheduledPaperConstruction) :
    GlobalAffirmative := by
  intro k hk
  obtain ⟨D⟩ := build k hk
  exact P_of_scheduledPaperConstruction hk D

end ScheduledPaperConstruction

end Erdos279
