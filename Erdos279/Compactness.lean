import Erdos279.FiniteCSP

/-!
# A pure-`Std` compactness proof

This is a specialized diagonal proof of compactness for the product
`∏ p, Fin p`.  It avoids any appeal to an unproved compactness axiom and does
not require `mathlib`.
-/

namespace Erdos279Compactness

def Cofinal (S : Nat → Prop) : Prop :=
  ∀ b : Nat, ∃ i : Nat, b ≤ i ∧ S i

theorem cofinal_mono {S T : Nat → Prop}
    (hS : Cofinal S) (hST : ∀ i, S i → T i) :
    Cofinal T := by
  intro b
  rcases hS b with ⟨i, hbi, hSi⟩
  exact ⟨i, hbi, hST i hSi⟩

theorem cofinal_inter_tail {S : Nat → Prop}
    (hS : Cofinal S) (b : Nat) :
    Cofinal (fun i => S i ∧ b ≤ i) := by
  intro c
  rcases hS (b + c) with ⟨i, hi, hSi⟩
  refine ⟨i, Nat.le_trans (Nat.le_add_left c b) hi, hSi, ?_⟩
  exact Nat.le_trans (Nat.le_add_right b c) hi

theorem not_cofinal_eventually {S : Nat → Prop}
    (hS : ¬ Cofinal S) :
    ∃ b : Nat, ∀ i : Nat, b ≤ i → ¬ S i := by
  have hb : ∃ b : Nat, ¬ ∃ i : Nat, b ≤ i ∧ S i := by
    apply Classical.byContradiction
    intro h
    apply hS
    intro b
    apply Classical.byContradiction
    intro hb'
    exact h ⟨b, hb'⟩
  rcases hb with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro i hbi hSi
  exact hb ⟨i, hbi, hSi⟩

/--
An unbounded sequence taking values in `{0,...,q-1}` has a cofinal fiber.
-/
theorem cofinal_bounded_fiber :
    ∀ q : Nat, 0 < q →
      ∀ (S : Nat → Prop), Cofinal S →
      ∀ f : Nat → Nat, (∀ i, f i < q) →
      ∃ a : Nat, a < q ∧ Cofinal (fun i => S i ∧ f i = a) := by
  intro q
  induction q with
  | zero =>
      intro hq
      exact False.elim (Nat.lt_irrefl 0 hq)
  | succ q ih =>
      intro hq S hS f hf
      by_cases htop : Cofinal (fun i => S i ∧ f i = q)
      · exact ⟨q, Nat.lt_succ_self q, htop⟩
      · rcases not_cofinal_eventually htop with ⟨b, hb⟩
        cases q with
        | zero =>
            apply False.elim
            apply htop
            intro c
            rcases hS c with ⟨i, hci, hSi⟩
            have hfi : f i = 0 :=
              Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (hf i))
            exact ⟨i, hci, hSi, hfi⟩
        | succ q =>
            have htail := cofinal_inter_tail hS b
            let g : Nat → Nat :=
              fun c => Classical.choose (htail c)
            have hg_ge (c : Nat) : c ≤ g c :=
              (Classical.choose_spec (htail c)).1
            have hg_S (c : Nat) : S (g c) :=
              (Classical.choose_spec (htail c)).2.1
            have hg_b (c : Nat) : b ≤ g c :=
              (Classical.choose_spec (htail c)).2.2
            have hfg (c : Nat) : f (g c) < q.succ := by
              have hle : f (g c) ≤ q.succ :=
                Nat.le_of_lt_succ (hf (g c))
              apply Nat.lt_of_le_of_ne hle
              intro heq
              exact hb (g c) (hg_b c) ⟨hg_S c, heq⟩
            have htrue : Cofinal (fun _ : Nat => True) := by
              intro c
              exact ⟨c, Nat.le_refl c, True.intro⟩
            rcases ih (Nat.zero_lt_succ q)
                (fun _ : Nat => True) htrue
                (fun c => f (g c)) hfg with
              ⟨a, ha, haCofinal⟩
            refine ⟨a, Nat.lt_succ_of_lt ha, ?_⟩
            intro c
            rcases haCofinal c with ⟨d, hcd, _, hgd⟩
            exact ⟨g d, Nat.le_trans hcd (hg_ge d), hg_S d, hgd⟩

end Erdos279Compactness

namespace Erdos279

open Erdos279Compactness

/-- A cofinal set of finite-window indices. -/
structure CofinalSet where
  pred : Nat → Prop
  cofinal : Cofinal pred

def CofinalSet.all : CofinalSet where
  pred := fun _ => True
  cofinal := by
    intro b
    exact ⟨b, Nat.le_refl b, True.intro⟩

/--
Refine a cofinal family so that the coordinate with natural value `m`
is constant, when `m` is prime.
-/
noncomputable def refineAt
    (w : Nat → ResidueAssignment) (m : Nat) (s : CofinalSet) :
    CofinalSet := by
  classical
  by_cases hp : ∃ p : Prime, p.1 = m
  · let p : Prime := Classical.choose hp
    have hpPos : 0 < p.1 := p.pos
    have hfiber :
        ∃ a : Nat, a < p.1 ∧
          Cofinal (fun i => s.pred i ∧ (w i p : Nat) = a) :=
      cofinal_bounded_fiber p.1 hpPos s.pred s.cofinal
        (fun i => (w i p : Nat)) (fun i => (w i p).isLt)
    let a : Nat := Classical.choose hfiber
    exact
      { pred := fun i => s.pred i ∧ (w i p : Nat) = a
        cofinal := (Classical.choose_spec hfiber).2 }
  · exact s

theorem refineAt_subset
    (w : Nat → ResidueAssignment) (m : Nat) (s : CofinalSet)
    {i : Nat} (hi : (refineAt w m s).pred i) :
    s.pred i := by
  classical
  by_cases hp : ∃ p : Prime, p.1 = m
  · simp only [refineAt, dif_pos hp] at hi
    exact hi.1
  · simpa only [refineAt, dif_neg hp] using hi

theorem refineAt_constant
    (w : Nat → ResidueAssignment) (m : Nat) (s : CofinalSet)
    (p : Prime) (hp : p.1 = m)
    {i j : Nat}
    (hi : (refineAt w m s).pred i)
    (hj : (refineAt w m s).pred j) :
    w i p = w j p := by
  classical
  have hex : ∃ q : Prime, q.1 = m := ⟨p, hp⟩
  have hchosen : Classical.choose hex = p := by
    apply Subtype.ext
    exact (Classical.choose_spec hex).trans hp.symm
  have hi' := hi
  have hj' := hj
  simp only [refineAt, dif_pos hex] at hi' hj'
  have hq :
      w i (Classical.choose hex) =
        w j (Classical.choose hex) := by
    apply Fin.ext
    exact hi'.2.trans hj'.2.symm
  exact hchosen ▸ hq

noncomputable def diagonalStages
    (w : Nat → ResidueAssignment) : Nat → CofinalSet
  | 0 => CofinalSet.all
  | m + 1 => refineAt w m (diagonalStages w m)

theorem diagonalStages_step_subset
    (w : Nat → ResidueAssignment) (m i : Nat)
    (hi : (diagonalStages w (m + 1)).pred i) :
    (diagonalStages w m).pred i := by
  exact refineAt_subset w m (diagonalStages w m) hi

theorem diagonalStages_anti
    (w : Nat → ResidueAssignment) :
    ∀ {a b i : Nat}, a ≤ b →
      (diagonalStages w b).pred i →
      (diagonalStages w a).pred i := by
  intro a b
  induction b with
  | zero =>
      intro i hab hi
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      exact hi
  | succ b ih =>
      intro i hab hi
      rcases Nat.lt_or_eq_of_le hab with hlt | heq
      · apply ih (Nat.le_of_lt_succ hlt)
        exact diagonalStages_step_subset w b i hi
      · subst a
        exact hi

noncomputable def diagonalRepIndex
    (w : Nat → ResidueAssignment) (p : Prime) : Nat :=
  Classical.choose ((diagonalStages w (p.1 + 1)).cofinal 0)

theorem diagonalRepIndex_mem
    (w : Nat → ResidueAssignment) (p : Prime) :
    (diagonalStages w (p.1 + 1)).pred (diagonalRepIndex w p) :=
  (Classical.choose_spec
    ((diagonalStages w (p.1 + 1)).cofinal 0)).2

noncomputable def diagonalAssignment
    (w : Nat → ResidueAssignment) : ResidueAssignment :=
  fun p => w (diagonalRepIndex w p) p

theorem diagonalStages_eq_assignment
    (w : Nat → ResidueAssignment)
    {m i : Nat} (hi : (diagonalStages w m).pred i)
    (p : Prime) (hp : p.1 < m) :
    w i p = diagonalAssignment w p := by
  have hpm : p.1 + 1 ≤ m := Nat.succ_le_iff.mpr hp
  have hi' :
      (diagonalStages w (p.1 + 1)).pred i :=
    diagonalStages_anti w hpm hi
  have hj' :
      (diagonalStages w (p.1 + 1)).pred
        (diagonalRepIndex w p) :=
    diagonalRepIndex_mem w p
  exact refineAt_constant w p.1 (diagonalStages w p.1) p rfl hi' hj'

/--
The compactness principle used in `FiniteCSP.lean`, now proved without
additional axioms.
-/
theorem assignmentCompactness_pureStd : AssignmentCompactness := by
  intro k N hk hwindows
  let w : Nat → ResidueAssignment :=
    fun i =>
      Classical.choose
        (hwindows (N + i) (Nat.le_add_right N i))
  have hw (i : Nat) :
      WindowSatisfied k N (N + i) (w i) := by
    dsimp only [w]
    exact Classical.choose_spec
      (hwindows (N + i) (Nat.le_add_right N i))
  let r : ResidueAssignment := diagonalAssignment w
  refine ⟨r, ?_⟩
  intro n hn
  rcases (diagonalStages w (n + 1)).cofinal n with
    ⟨i, hni, hiStage⟩
  have hnEndpoint : n ≤ N + i :=
    Nat.le_trans hni (Nat.le_add_left i N)
  rcases hw i n hn hnEndpoint with ⟨p, hkp, hmod⟩
  have hp_le_kp : p.1 ≤ k * p.1 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right p.1 hk
  have hp_lt : p.1 < n + 1 :=
    Nat.lt_succ_of_le (Nat.le_trans hp_le_kp hkp)
  have hpStable : w i p = diagonalAssignment w p :=
    diagonalStages_eq_assignment w hiStage p hp_lt
  refine ⟨p, hkp, ?_⟩
  change n % p.1 = (diagonalAssignment w p : Nat)
  exact hmod.trans (congrArg Fin.val hpStable)

/-- The unconditional compactness equivalence requested in the problem. -/
theorem P_iff_all_finiteCSP (k : Nat) (hk : 1 ≤ k) :
    P k ↔ ∃ N : Nat, 1 ≤ N ∧
      ∀ M : Nat, N ≤ M → FiniteCSP k N M :=
  P_iff_all_finiteCSP_of_compactness assignmentCompactness_pureStd k hk

/-- The unconditional finite-unsatisfiability formulation of `¬P(k)`. -/
theorem not_P_iff_arbitrarilyUnsat (k : Nat) (hk : 1 ≤ k) :
    (¬ P k) ↔ ArbitrarilyUnsat k :=
  not_P_iff_arbitrarilyUnsat_of_compactness
    assignmentCompactness_pureStd k hk

end Erdos279
