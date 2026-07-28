import Erdos279.UniformGeometricHardSchedule
import Erdos279.ConstructionCore

/-!
# Combining the prime schedule with the dynamic hard schedule

This is the variable-cutoff replacement for `ScheduledPaperConstruction`.
The finite prefix of unused controller coordinates is normalized to the
class `1`; every coordinate used by the prime-target matching already has
a nonzero value and is therefore unchanged.
-/

namespace Erdos279

/-- Complete structural data at one level `k`, using the correct
scale-dependent old-prime cutoff. -/
structure DynamicScheduledPaperConstruction (k : Nat) where
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
  sieveExponent : Nat
  hardData :
    DynamicHardScheduleAnalyticData
      hub modulus classes
      (oldControllerPrimes hub cutoff)
      sieveExponent k

namespace DynamicScheduledPaperConstruction

noncomputable def primeBase
    {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    ShiftedAssignment :=
  D.enumerations.primeTargetAssignment D.primeTail

noncomputable def hardSchedule
    {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    VariableHardPairingSchedule
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff)
      (fun j =>
        stageOldPrimeCutoff D.sieveExponent
          (D.hardData.scale j))
      D.hardData.scale k :=
  D.hardData.toVariableHardPairingScheduleWithNonzeroBase
    D.primeBase

noncomputable def finalAssignment
    {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    ShiftedAssignment :=
  D.hardSchedule.assignment

noncomputable def primeThreshold
    {k : Nat} (D : DynamicScheduledPaperConstruction k) : Nat :=
  max
    (PeriodicComplementaryEnumerations.primePrefixBound
      D.enumerations.complementary
      D.primeTail.offset)
    (max (k * D.hub.1)
      (oldPrimeMaturityBound k
        (oldControllerPrimes D.hub D.cutoff)))

def hardThreshold
    {k : Nat} (D : DynamicScheduledPaperConstruction k) : Nat :=
  D.hardData.scale 0 + 1

noncomputable def threshold
    {k : Nat} (D : DynamicScheduledPaperConstruction k) : Nat :=
  max D.primeThreshold D.hardThreshold

private theorem hub_not_in_controllerReservoir
    {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    ¬ InControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff)
      D.hub := by
  intro hh
  exact inControllerProgression_ne_hub
    hh.inControllerProgression rfl

private theorem periodic_not_in_controllerReservoir
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
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
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    {p : Prime}
    (hp : p ∈ oldControllerPrimes D.hub D.cutoff) :
    ¬ InControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p := by
  intro hpS
  exact hpS.not_mem_old hp

/-- The dynamic schedule agrees with the normalized prime base away from
the controller reservoir. -/
theorem finalAssignment_of_not_in_reservoir
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (p : Prime)
    (hp :
      ¬ InControllerReservoir
        D.hub D.modulus D.classes
        (oldControllerPrimes D.hub D.cutoff) p) :
    D.finalAssignment p =
      controllerNonzeroBase D.hub D.primeBase p :=
  D.hardData.toVariableHardPairingScheduleWithNonzeroBase_of_not_in_reservoir
    D.primeBase p hp

theorem finalAssignment_hub
    {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    (D.finalAssignment D.hub : Nat) = 1 := by
  rw [D.finalAssignment_of_not_in_reservoir
    D.hub D.hub_not_in_controllerReservoir]
  rw [controllerNonzeroBase_eq_of_not_progression
    D.hub D.primeBase D.hub
    (fun hpG =>
      inControllerProgression_ne_hub hpG rfl)]
  exact D.enumerations.primeTargetAssignment_hub D.primeTail

theorem finalAssignment_outside_zero
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (q : Prime) (hqh : q ≠ D.hub)
    (hqG : ¬ InControllerProgression D.hub q) :
    (D.finalAssignment q : Nat) = 0 := by
  have hqNotS :
      ¬ InControllerReservoir
        D.hub D.modulus D.classes
        (oldControllerPrimes D.hub D.cutoff) q := by
    intro hqS
    exact hqG hqS.inControllerProgression
  rw [D.finalAssignment_of_not_in_reservoir q hqNotS]
  rw [controllerNonzeroBase_eq_of_not_progression
    D.hub D.primeBase q hqG]
  exact
    D.enumerations.primeTargetAssignment_outside_zero
      (fun ℓ hℓ =>
        (mem_oldControllerPrimes.mp hℓ).1)
      D.primeTail q hqh hqG

theorem finalAssignment_old
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    {p : Prime}
    (hp : p ∈ oldControllerPrimes D.hub D.cutoff) :
    (D.finalAssignment p : Nat) = 1 := by
  have hbase :
      (D.primeBase p : Nat) = 1 :=
    D.enumerations.primeTargetAssignment_old
      D.primeTail hp
  rw [D.finalAssignment_of_not_in_reservoir
    p (D.old_not_in_controllerReservoir hp)]
  rw [controllerNonzeroBase_eq_of_ne_zero
    D.hub D.primeBase p (by omega)]
  exact hbase

/-- Every nonzero periodic base coordinate is preserved.  In particular,
this applies to every controller occurring in the prime-tail matching. -/
theorem finalAssignment_periodic_of_ne_zero
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    {p : Prime}
    (hp : InPeriodicReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p)
    (hbase : (D.primeBase p : Nat) ≠ 0) :
    D.finalAssignment p = D.primeBase p := by
  rw [D.finalAssignment_of_not_in_reservoir
    p (D.periodic_not_in_controllerReservoir hp)]
  exact controllerNonzeroBase_eq_of_ne_zero
    D.hub D.primeBase p hbase

theorem final_covers_large_complementary
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (hk : 0 < k)
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
  have hbaseNonzero :
      (D.primeBase pair.controller : Nat) ≠ 0 := by
    exact
      D.primeTail.matching.assignment_at_controller_ne_zero
        (hubOldPrimeAssignment D.hub
          (oldControllerPrimes D.hub D.cutoff))
        hk j
  have hfinalResidue :
      (D.finalAssignment pair.controller : Nat) =
        (pair.residue : Nat) := by
    rw [D.finalAssignment_periodic_of_ne_zero
      hpT hbaseNonzero]
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
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (hk : 0 < k) :
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
  · exact D.final_covers_large_complementary
      hk q hcomp hprefix
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
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (hk : 0 < k) :
    ∀ m, D.hardThreshold ≤ m →
      HasHardForm D.hub m →
      ShiftedMatureCovers k m D.finalAssignment := by
  exact
    D.hardSchedule.covers_hardForm_tail
      hk D.hardThreshold D.hardData.scale_covers

/-- The corrected dynamic construction feeds the already verified
four-case completion theorem. -/
noncomputable def toPaperConstructionCore
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
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
    exact D.final_covers_prime_tail hk m
      ((le_max_left _ _).trans hm) hprime

theorem P_of_dynamicScheduledPaperConstruction
    {k : Nat} (hk : 3 ≤ k)
    (D : DynamicScheduledPaperConstruction k) :
    P k :=
  P_of_paperConstructionCore hk
    (D.toPaperConstructionCore (by omega))

def RemainingDynamicScheduledPaperConstruction : Prop :=
  ∀ k : Nat, 3 ≤ k →
    Nonempty (DynamicScheduledPaperConstruction k)

theorem globalAffirmative_of_dynamicScheduledPaperConstruction
    (build : RemainingDynamicScheduledPaperConstruction) :
    GlobalAffirmative := by
  intro k hk
  obtain ⟨D⟩ := build k hk
  exact P_of_dynamicScheduledPaperConstruction hk D

end DynamicScheduledPaperConstruction

end Erdos279
