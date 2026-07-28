import Erdos279.Semigroup

/-!
# Causal backup arithmetic

This file kernel-checks the local permanence mechanism.  The only
factorization input is exposed as `hfactor`: every coefficient `c>1` under
consideration has a prime divisor.
-/

namespace Erdos279

/--
If a controller `p` formerly covered the zero-class point `c*p`, then under
the paper's frontier inequalities the point has a permanent backup:

* `c=1`: the hub class;
* `c>1`: a small prime divisor of `c` carrying the zero class.
-/
theorem causal_backup_witness
    {k c : Nat} {h p : Prime} {a : ShiftedAssignment}
    (hcpos : 1 ≤ c)
    (hclt : c < h.1)
    (hpG : InControllerProgression h p)
    (hpLarge : k * h.1 < p.1)
    (hah : (a h : Nat) = 1)
    (hsmallZero :
      ∀ d : Prime, d.1 < h.1 → (a d : Nat) = 0)
    (hfactor :
      1 < c → ∃ d : Prime, d.1 ∣ c) :
    ShiftedMatureCovers k (c * p.1) a := by
  rcases Nat.eq_or_lt_of_le hcpos with rfl | hcgt
  · refine ⟨h, ?_, ?_⟩
    · simpa using Nat.le_trans (Nat.le_of_lt hpLarge)
        (Nat.le_add_right p.1 1)
    · simpa [hah] using hpG
  · rcases hfactor hcgt with ⟨d, hdc⟩
    have hcle : d.1 ≤ c :=
      Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one hcpos) hdc
    have hdlt : d.1 < h.1 :=
      Nat.lt_of_le_of_lt hcle hclt
    refine ⟨d, ?_, ?_⟩
    · have hdkh : k * d.1 ≤ k * h.1 :=
        Nat.mul_le_mul_left k (Nat.le_of_lt hdlt)
      have hkp : k * d.1 ≤ p.1 :=
        Nat.le_trans hdkh (Nat.le_of_lt hpLarge)
      exact Nat.le_trans hkp
        (Nat.le_trans
          (Nat.le_mul_of_pos_left p.1 hcpos)
          (Nat.le_add_right (c * p.1) 1))
    · rw [hsmallZero d hdlt]
      exact Nat.mod_eq_zero_of_dvd
        (Nat.dvd_mul_right_of_dvd hdc p.1)

end Erdos279
