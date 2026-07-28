import Erdos279.PrimeTargetConstruction
import Erdos279.ConstructionPartition

/-!
# The concrete `H/T/S/outside` partition

This file instantiates the abstract priority layout with the actual finite
old-prime set, periodic reservoir, and complementary controller reservoir
from (3.5).
-/

namespace Erdos279

/-- Boolean priority data for the paper's concrete prime partition. -/
noncomputable def periodicHTSPriority
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    HTSPriority := by
  classical
  exact
    { inG := fun p => decide (InControllerProgression h p)
      inH := fun p => decide (p ∈ H)
      inT := fun p =>
        decide (InPeriodicReservoir h L R H p)
      H_sub_G := by
        intro p hp
        rw [decide_eq_true_eq] at hp ⊢
        exact hH p hp
      T_sub_G := by
        intro p hp
        rw [decide_eq_true_eq] at hp ⊢
        exact hp.inControllerProgression
      H_disjoint_T := by
        intro p hpH hpT
        rw [decide_eq_true_eq] at hpH hpT
        exact hpT.not_mem_old hpH }

@[simp]
theorem periodicHTSPriority_inG
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p)
    (p : Prime) :
    (periodicHTSPriority h L R H hH).inG p = true ↔
      InControllerProgression h p := by
  classical
  simp [periodicHTSPriority]

@[simp]
theorem periodicHTSPriority_inH
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p)
    (p : Prime) :
    (periodicHTSPriority h L R H hH).inH p = true ↔
      p ∈ H := by
  classical
  simp [periodicHTSPriority]

@[simp]
theorem periodicHTSPriority_inT
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p)
    (p : Prime) :
    (periodicHTSPriority h L R H hH).inT p = true ↔
      InPeriodicReservoir h L R H p := by
  classical
  simp [periodicHTSPriority]

/-- The abstract priority role `H` is exactly membership in the finite old
set. -/
theorem periodicHTSPriority_role_H_iff
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p)
    (p : Prime) :
    (periodicHTSPriority h L R H hH).role p = .H ↔
      p ∈ H := by
  classical
  rw [(periodicHTSPriority h L R H hH).role_eq_H_iff]
  exact periodicHTSPriority_inH h L R H hH p

/-- The abstract priority role `T` is exactly the periodic reservoir. -/
theorem periodicHTSPriority_role_T_iff
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p)
    (p : Prime) :
    (periodicHTSPriority h L R H hH).role p = .T ↔
      InPeriodicReservoir h L R H p := by
  classical
  rw [(periodicHTSPriority h L R H hH).role_eq_T_iff]
  exact periodicHTSPriority_inT h L R H hH p

/-- The abstract priority role `S` is exactly the complementary controller
reservoir. -/
theorem periodicHTSPriority_role_S_iff
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p)
    (p : Prime) :
    (periodicHTSPriority h L R H hH).role p = .S ↔
      InControllerReservoir h L R H p := by
  classical
  rw [(periodicHTSPriority h L R H hH).role_eq_S_iff]
  simp only [periodicHTSPriority, decide_eq_true_eq,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨hpG, hpH, hpNotT⟩
    apply (inControllerReservoir_iff h L R H p).2
    refine ⟨hpG, hpH, ?_⟩
    intro hpR
    apply hpNotT
    exact (inPeriodicReservoir_iff h L R H p).2
      ⟨hpG, hpH, hpR⟩
  · intro hpS
    have hp :=
      (inControllerReservoir_iff h L R H p).1 hpS
    refine ⟨hp.1, hp.2.1, ?_⟩
    intro hpT
    exact hp.2.2
      ((inPeriodicReservoir_iff h L R H p).1 hpT).2.2

/-- The outside role is exactly the complement of the controller
progression. -/
theorem periodicHTSPriority_role_outside_iff
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p)
    (p : Prime) :
    (periodicHTSPriority h L R H hH).role p = .outside ↔
      ¬ InControllerProgression h p := by
  classical
  rw [(periodicHTSPriority h L R H hH).role_eq_outside_iff]
  simp [periodicHTSPriority]

/-- The corresponding hub-first layout. -/
noncomputable def periodicHubHTSLayout
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    HubHTSLayout := by
  classical
  exact
    { hub := h
      inner := periodicHTSPriority h L R H hH
      hub_not_G := by
        simp only [periodicHTSPriority]
        have hnot : ¬ InControllerProgression h h := by
          intro hh
          exact inControllerProgression_ne_hub hh rfl
        simp [hnot] }

end Erdos279
