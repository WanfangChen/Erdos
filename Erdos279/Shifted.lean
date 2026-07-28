import Erdos279.BasicLemmas

/-!
# The shifted formulation

The paper works with `m = n - 1` and shifted residues
`a_p ≡ r_p - 1 (mod p)`.  This file checks the translation, including the
canonical reduction back into `Fin p`.
-/

namespace Erdos279

abbrev ShiftedAssignment := ResidueAssignment

/-- Convert shifted classes `a_p` into canonical original classes `a_p+1`. -/
def unshiftAssignment (a : ShiftedAssignment) : ResidueAssignment :=
  fun p =>
    ⟨((a p : Nat) + 1) % p.1, Nat.mod_lt _ p.pos⟩

/-- Coverage of shifted target `m`; maturity is measured at `n=m+1`. -/
def ShiftedMatureCovers
    (k m : Nat) (a : ShiftedAssignment) : Prop :=
  ∃ p : Prime, k * p.1 ≤ m + 1 ∧ m % p.1 = (a p : Nat)

theorem shiftedMatureCovers_implies_original
    {k m : Nat} {a : ShiftedAssignment}
    (hcover : ShiftedMatureCovers k m a) :
    MatureCovers k (m + 1) (unshiftAssignment a) := by
  rcases hcover with ⟨p, hkp, hmod⟩
  refine ⟨p, hkp, ?_⟩
  change (m + 1) % p.1 = ((a p : Nat) + 1) % p.1
  calc
    (m + 1) % p.1 = (m % p.1 + 1) % p.1 :=
      (Nat.mod_add_mod m p.1 1).symm
    _ = ((a p : Nat) + 1) % p.1 := by rw [hmod]

/-- A shifted assignment covers all sufficiently large shifted targets. -/
def ShiftedCoversTail (k : Nat) (a : ShiftedAssignment) : Prop :=
  ∃ M₀ : Nat, ∀ m : Nat, M₀ ≤ m → ShiftedMatureCovers k m a

/-- The completion step of the paper, formalized independently of the sieve. -/
theorem P_of_shiftedCoversTail {k : Nat} {a : ShiftedAssignment}
    (hshifted : ShiftedCoversTail k a) :
    P k := by
  rcases hshifted with ⟨M₀, htail⟩
  refine ⟨unshiftAssignment a, M₀ + 1, ?_, ?_⟩
  · exact Nat.succ_le_succ (Nat.zero_le M₀)
  · intro n hn
    have hn1 : 1 ≤ n :=
      Nat.le_trans (Nat.succ_le_succ (Nat.zero_le M₀)) hn
    have hm : M₀ ≤ n - 1 :=
      Nat.le_sub_of_add_le hn
    have hm1 : n - 1 + 1 = n :=
      Nat.sub_add_cancel hn1
    apply (covers_iff_matureCovers k n (unshiftAssignment a)).mpr
    rw [← hm1]
    exact shiftedMatureCovers_implies_original (htail (n - 1) hm)

end Erdos279
