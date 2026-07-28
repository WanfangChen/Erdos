import Erdos279.HardPairingSchedule

/-!
# Coverage by the frozen old-prime classes

The sieve survivor predicate is a negated finite collection of congruence
classes.  Consequently, every target that is not a survivor is already
covered by one of those old classes.  This file makes that elementary
complement argument explicit and records the finite maturity threshold.
-/

namespace Erdos279

/-- Package the restriction of a shifted assignment as old controller-prime
classes once their nonvanishing has been proved. -/
def oldPrimeClassesOfAssignment
    (h : Prime) (z : Nat)
    (assignment : ShiftedAssignment)
    (hnonzero :
      ∀ p : Prime, InControllerProgression h p →
        p.1 ≤ z → (assignment p : Nat) ≠ 0) :
    OldPrimeClasses h z where
  residue := assignment
  nonzero := hnonzero

/-- Negating `AvoidsOldClasses` produces an actual old-prime congruence
witness. -/
theorem exists_oldPrimeClass_of_not_avoids
    {h : Prime} {z m : Nat}
    (a : OldPrimeClasses h z)
    (hm : ¬ AvoidsOldClasses a m) :
    ∃ p : Prime,
      InControllerProgression h p ∧
        p.1 ≤ z ∧
        m % p.1 = (a.residue p : Nat) := by
  classical
  unfold AvoidsOldClasses at hm
  push_neg at hm
  obtain ⟨p, hpG, hpz, hpClass⟩ := hm
  exact ⟨p, hpG, hpz, hpClass⟩

/-- Above `kz`, every target failing the survivor condition is maturely
covered by one of the frozen old classes. -/
theorem covered_of_not_avoidsOldClasses
    {h : Prime} {z k m : Nat}
    (a : OldPrimeClasses h z)
    (assignment : ShiftedAssignment)
    (hmatch :
      ∀ p : Prime, InControllerProgression h p →
        p.1 ≤ z →
        (assignment p : Nat) = (a.residue p : Nat))
    (hmLarge : k * z ≤ m)
    (hm : ¬ AvoidsOldClasses a m) :
    ShiftedMatureCovers k m assignment := by
  obtain ⟨p, hpG, hpz, hpClass⟩ :=
    exists_oldPrimeClass_of_not_avoids a hm
  refine ⟨p, ?_, ?_⟩
  · exact
      (Nat.mul_le_mul_left k hpz).trans hmLarge
        |>.trans (Nat.le_add_right m 1)
  · exact hpClass.trans (hmatch p hpG hpz).symm

/-- For classes obtained from an assignment, the matching premise in the
previous theorem is definitional. -/
theorem covered_of_not_avoids_assignmentClasses
    {h : Prime} {z k m : Nat}
    (assignment : ShiftedAssignment)
    (hnonzero :
      ∀ p : Prime, InControllerProgression h p →
        p.1 ≤ z → (assignment p : Nat) ≠ 0)
    (hmLarge : k * z ≤ m)
    (hm :
      ¬ AvoidsOldClasses
        (oldPrimeClassesOfAssignment
          h z assignment hnonzero) m) :
    ShiftedMatureCovers k m assignment := by
  apply covered_of_not_avoidsOldClasses
    (oldPrimeClassesOfAssignment h z assignment hnonzero)
    assignment
  · intro p _hpG _hpz
    rfl
  · exact hmLarge
  · exact hm

end Erdos279
