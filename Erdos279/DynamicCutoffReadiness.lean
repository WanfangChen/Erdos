import Erdos279.DynamicHardSchedule

/-!
# Preparing the base assignment and proving cutoff readiness

Integral geometric annuli may leave harmless gaps.  Reservoir primes in
those gaps are never selected as controllers, so we assign them the
permanent nonzero default class `1` from the start.  Primes that do belong
to an annulus retain their provisional base value until that annulus is
processed.
-/

namespace Erdos279

/-- Set every reservoir coordinate belonging to no processing annulus to
the permanent class `1`; preserve all other coordinates. -/
noncomputable def prepareDynamicBase
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p =>
    if hpS : InControllerReservoir h L R H p then
      if hex :
          ∃ i : Nat,
            p ∈ dynamicHardAnnulus h L R H k scale i then
        base p
      else
        ⟨1, p.one_lt⟩
    else
      base p

theorem prepareDynamicBase_of_not_in_reservoir
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    prepareDynamicBase h L R H scale k base p =
      base p := by
  simp [prepareDynamicBase, hp]

theorem prepareDynamicBase_nonzero_of_never_mem
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment)
    (hbase :
      ∀ p : Prime,
        InControllerProgression h p →
        ¬ InControllerReservoir h L R H p →
        (base p : Nat) ≠ 0)
    (p : Prime)
    (hpG : InControllerProgression h p)
    (hpNever :
      ∀ i : Nat,
        p ∉ dynamicHardAnnulus h L R H k scale i) :
    (prepareDynamicBase h L R H scale k base p : Nat) ≠ 0 := by
  classical
  by_cases hpS : InControllerReservoir h L R H p
  · have hnone :
        ¬ ∃ i : Nat,
          p ∈ dynamicHardAnnulus h L R H k scale i := by
      intro hex
      obtain ⟨i, hi⟩ := hex
      exact hpNever i hi
    simp [prepareDynamicBase, hpS, hnone]
  · rw [prepareDynamicBase_of_not_in_reservoir
      h L R H scale k base p hpS]
    exact hbase p hpG hpS

/-- If every future annulus starts above the current old-prime cutoff, the
prepared base satisfies the recursive readiness invariant. -/
theorem dynamicCutoffReady_of_below_future_annuli
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment)
    (hbase :
      ∀ p : Prime,
        InControllerProgression h p →
        ¬ InControllerReservoir h L R H p →
        (base p : Nat) ≠ 0)
    (hbelow :
      ∀ j i : Nat, j ≤ i →
        z j < scale (i + 1) / h.1) :
    DynamicCutoffReady h L R H z scale k
      (prepareDynamicBase h L R H scale k base) := by
  intro j p hpG hpz
  by_cases hex :
      ∃ i : Nat,
        p ∈ dynamicHardAnnulus h L R H k scale i
  · obtain ⟨i, hpI⟩ := hex
    have hiJ : i < j := by
      by_contra hnot
      have hjI : j ≤ i := Nat.le_of_not_gt hnot
      have hcut := hbelow j i hjI
      have hlower :
          scale (i + 1) / h.1 < p.1 :=
        (mem_hardStageControllerAnnulus.mp hpI).1
      omega
    exact Or.inr ⟨i, hiJ, hpI⟩
  · have hpNever :
        ∀ i : Nat,
          p ∉ dynamicHardAnnulus h L R H k scale i := by
      intro i hpI
      exact hex ⟨i, hpI⟩
    exact Or.inl
      ⟨hpNever,
        prepareDynamicBase_nonzero_of_never_mem
          h L R H scale k base hbase p hpG hpNever⟩

end Erdos279
