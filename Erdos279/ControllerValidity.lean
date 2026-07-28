import Erdos279.CausalBackup

/-!
# Controller validity

This file isolates the arithmetic behind the controller annuli.  The
semigroup-specific fact "if the controller divides a hard target, then the
cofactor is at least the hub" is an explicit hypothesis.
-/

namespace Erdos279

/-- The canonical residue selected when controller `p` is paired with `m`. -/
def controllerResidue (p : Prime) (m : Nat) : Fin p.1 :=
  ⟨m % p.1, Nat.mod_lt m p.pos⟩

theorem controllerResidue_ne_zero
    {h p : Prime} {m : Nat}
    (hpLower : m / h.1 < p.1)
    (hcofactor : p.1 ∣ m → h.1 ≤ m / p.1) :
    (controllerResidue p m : Nat) ≠ 0 := by
  intro hzero
  change m % p.1 = 0 at hzero
  have hpdiv : p.1 ∣ m :=
    Nat.dvd_of_mod_eq_zero hzero
  have hq : h.1 ≤ m / p.1 :=
    hcofactor hpdiv
  have heq : p.1 * (m / p.1) = m := by
    have := Nat.mod_add_div m p.1
    simpa [hzero] using this
  have hle : p.1 * h.1 ≤ m := by
    rw [← heq]
    exact Nat.mul_le_mul_left p.1 hq
  have hlt : m < p.1 * h.1 :=
    (Nat.div_lt_iff_lt_mul h.pos).mp hpLower
  exact Nat.not_lt_of_ge hle hlt

theorem controller_mature_from_annulus
    {k X m : Nat} {p : Prime}
    (hk : 0 < k)
    (hpUpper : p.1 ≤ X / k)
    (hXm : X < m) :
    k * p.1 ≤ m + 1 := by
  have hpkX : p.1 * k ≤ X :=
    (Nat.le_div_iff_mul_le hk).mp hpUpper
  have hkpX : k * p.1 ≤ X := by
    simpa [Nat.mul_comm] using hpkX
  exact Nat.le_trans hkpX
    (Nat.le_trans (Nat.le_of_lt hXm) (Nat.le_add_right m 1))

theorem controller_pair_covers
    {k m : Nat} {p : Prime} {a : ShiftedAssignment}
    (hmature : k * p.1 ≤ m + 1)
    (ha : (a p : Nat) = (controllerResidue p m : Nat)) :
    ShiftedMatureCovers k m a := by
  refine ⟨p, hmature, ?_⟩
  exact ha.symm

end Erdos279
