import Erdos279.Factorization

namespace Erdos279

/--
Changing only the controller coordinate cannot destroy an already covered
target strictly below the causal frontier `h * p`.  If the old witness is
not `p`, it survives unchanged.  If it is `p`, its old zero residue writes
the target as `c * p` with `1 ≤ c < h`, and the permanent small classes
supply a backup witness.
-/
theorem causal_change_preserves_below_frontier
    {k m : Nat} {h p : Prime} {old new : ShiftedAssignment}
    (hk : 0 < k)
    (hmfront : m < h.1 * p.1)
    (hold : ShiftedMatureCovers k m old)
    (hpG : InControllerProgression h p)
    (hpLarge : k * h.1 < p.1)
    (holdp : (old p : Nat) = 0)
    (hagree : ∀ q : Prime, q ≠ p → new q = old q)
    (hnewh : (new h : Nat) = 1)
    (hnewSmallZero :
      ∀ d : Prime, d.1 < h.1 → (new d : Nat) = 0) :
    ShiftedMatureCovers k m new := by
  rcases hold with ⟨q, hqmature, hqmod⟩
  by_cases hqp : q = p
  · subst q
    have hmodzero : m % p.1 = 0 := by
      simpa [holdp] using hqmod
    have hpdiv : p.1 ∣ m :=
      Nat.dvd_of_mod_eq_zero hmodzero
    have hkone : 1 ≤ k := hk
    have hp_le_kp : p.1 ≤ k * p.1 := by
      simpa using Nat.mul_le_mul_right p.1 hkone
    have hp_le_m1 : p.1 ≤ m + 1 :=
      Nat.le_trans hp_le_kp hqmature
    have hmpos : 0 < m := by
      exact Nat.lt_of_succ_lt_succ
        (Nat.lt_of_lt_of_le p.one_lt hp_le_m1)
    have hp_le_m : p.1 ≤ m :=
      Nat.le_of_dvd hmpos hpdiv
    have hcpos : 1 ≤ m / p.1 :=
      (Nat.le_div_iff_mul_le p.pos).mpr (by simpa using hp_le_m)
    have hm_eq : (m / p.1) * p.1 = m :=
      Nat.div_mul_cancel hpdiv
    have hclt : m / p.1 < h.1 := by
      apply (Nat.mul_lt_mul_right p.pos).mp
      calc
        (m / p.1) * p.1 = m := hm_eq
        _ < h.1 * p.1 := hmfront
    have hbackup :=
      causal_backup_witness_unconditional
        (a := new) hcpos hclt hpG hpLarge hnewh hnewSmallZero
    rw [hm_eq] at hbackup
    exact hbackup
  · refine ⟨q, hqmature, ?_⟩
    rw [hagree q hqp]
    exact hqmod

/-- Replace exactly one dependent coordinate of a shifted assignment. -/
def updateController
    (old : ShiftedAssignment) (p : Prime) (u : Fin p.1) :
    ShiftedAssignment :=
  fun q =>
    if hqp : q = p then
      hqp.symm ▸ u
    else
      old q

@[simp] theorem updateController_self
    (old : ShiftedAssignment) (p : Prime) (u : Fin p.1) :
    updateController old p u p = u := by
  simp [updateController]

theorem updateController_of_ne
    (old : ShiftedAssignment) (p q : Prime) (u : Fin p.1)
    (hqp : q ≠ p) :
    updateController old p u q = old q := by
  simp [updateController, hqp]

/--
Concrete one-coordinate update corollary.  The assumptions `holdp` and
`hunonzero` record that this is genuinely a zero-to-nonzero update.
-/
theorem causal_update_preserves_below_frontier
    {k m : Nat} {h p : Prime} {old : ShiftedAssignment}
    (u : Fin p.1)
    (hk : 0 < k)
    (hmfront : m < h.1 * p.1)
    (hold : ShiftedMatureCovers k m old)
    (hpG : InControllerProgression h p)
    (hpLarge : k * h.1 < p.1)
    (holdp : (old p : Nat) = 0)
    (_hunonzero : (u : Nat) ≠ 0)
    (holdh : (old h : Nat) = 1)
    (holdSmallZero :
      ∀ d : Prime, d.1 < h.1 → (old d : Nat) = 0) :
    ShiftedMatureCovers k m (updateController old p u) := by
  have hkone : 1 ≤ k := hk
  have hh_le_kh : h.1 ≤ k * h.1 := by
    simpa using Nat.mul_le_mul_right h.1 hkone
  have hh_lt_p : h.1 < p.1 :=
    Nat.lt_of_le_of_lt hh_le_kh hpLarge
  apply causal_change_preserves_below_frontier
    hk hmfront hold hpG hpLarge holdp
  · intro q hqp
    simp [updateController, hqp]
  · have hhp : h ≠ p := by
      intro heq
      subst p
      exact Nat.lt_irrefl h.1 hh_lt_p
    simpa [updateController, hhp] using holdh
  · intro d hdlt
    have hdp : d ≠ p := by
      intro heq
      subst d
      exact Nat.not_lt_of_ge (Nat.le_of_lt hh_lt_p) hdlt
    simpa [updateController, hdp] using holdSmallZero d hdlt

/--
Set-level form: every target in the previously covered prefix below `h*p`
remains covered after the single zero-to-nonzero controller update.
-/
theorem causal_update_preserves_covered_prefix
    {k : Nat} {h p : Prime} {old : ShiftedAssignment}
    (u : Fin p.1)
    (hk : 0 < k)
    (hpG : InControllerProgression h p)
    (hpLarge : k * h.1 < p.1)
    (holdp : (old p : Nat) = 0)
    (hunonzero : (u : Nat) ≠ 0)
    (holdh : (old h : Nat) = 1)
    (holdSmallZero :
      ∀ d : Prime, d.1 < h.1 → (old d : Nat) = 0) :
    ∀ m : Nat, m < h.1 * p.1 →
      ShiftedMatureCovers k m old →
      ShiftedMatureCovers k m (updateController old p u) := by
  intro m hmfront hold
  exact causal_update_preserves_below_frontier
    u hk hmfront hold hpG hpLarge holdp hunonzero
    holdh holdSmallZero

end Erdos279
