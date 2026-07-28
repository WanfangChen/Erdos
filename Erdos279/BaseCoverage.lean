import Erdos279.ControllerValidity

/-!
# Permanent base-class witnesses

These lemmas formalize the easy coverage supplied by the shifted zero classes
outside the hub/controller set.
-/

namespace Erdos279

theorem zero_class_covers_factor
    {k m : Nat} {q : Prime} {a : ShiftedAssignment}
    (hqdiv : q.1 ∣ m)
    (hqMature : k * q.1 ≤ m)
    (haq : (a q : Nat) = 0) :
    ShiftedMatureCovers k m a := by
  refine ⟨q, Nat.le_trans hqMature (Nat.le_add_right m 1), ?_⟩
  rw [haq]
  exact Nat.mod_eq_zero_of_dvd hqdiv

theorem smallOutside_covered_by_zero_classes
    {k m : Nat} {h : Prime} {a : ShiftedAssignment}
    (hzero :
      ∀ q : Prime, q ≠ h →
        ¬ InControllerProgression h q →
        (a q : Nat) = 0)
    (houtside : HasSmallOutsideFactor k h m) :
    ShiftedMatureCovers k m a := by
  rcases houtside with ⟨q, hqdiv, hqne, hqG, hqMature⟩
  exact zero_class_covers_factor hqdiv hqMature (hzero q hqne hqG)

end Erdos279
