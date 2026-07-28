import Erdos279.CausalUpdate

/-!
# Coordinatewise stabilization of dependent residue assignments

Each prime coordinate may stabilize at its own finite stage.  The final
assignment reads coordinate `p` at its declared freeze stage.  This checks
the globalization step without assuming that finite-stage assignments
converge automatically.
-/

namespace Erdos279

structure StabilizingAssignments where
  stage : Nat → ShiftedAssignment
  freezeStage : Prime → Nat
  stable :
    ∀ (p : Prime) (s : Nat), freezeStage p ≤ s →
      stage s p = stage (freezeStage p) p

namespace StabilizingAssignments

/-- The one global assignment obtained from coordinatewise stabilization. -/
def final (S : StabilizingAssignments) : ShiftedAssignment :=
  fun p => S.stage (S.freezeStage p) p

theorem final_agrees_of_frozen
    (S : StabilizingAssignments) (p : Prime) (s : Nat)
    (hps : S.freezeStage p ≤ s) :
    S.final p = S.stage s p := by
  symm
  exact S.stable p s hps

theorem stage_agrees_with_final_of_frozen
    (S : StabilizingAssignments) (p : Prime) (s : Nat)
    (hps : S.freezeStage p ≤ s) :
    S.stage s p = S.final p :=
  S.stable p s hps

/--
For any numerical bound, all prime coordinates below that bound have
stabilized by one common finite stage.
-/
theorem exists_freeze_bound
    (S : StabilizingAssignments) :
    ∀ B : Nat, ∃ s : Nat, ∀ p : Prime, p.1 ≤ B →
      S.freezeStage p ≤ s := by
  intro B
  induction B with
  | zero =>
      refine ⟨0, ?_⟩
      intro p hp
      have hpzero : p.1 = 0 := Nat.eq_zero_of_le_zero hp
      have hpge : 2 ≤ p.1 := p.property.1
      omega
  | succ B ih =>
      rcases ih with ⟨s, hs⟩
      by_cases hprime : IsPrime (B + 1)
      · let q : Prime := ⟨B + 1, hprime⟩
        refine ⟨max s (S.freezeStage q), ?_⟩
        intro p hp
        rcases Nat.lt_or_eq_of_le hp with hplt | hpeq
        · have hpB : p.1 ≤ B := by omega
          exact Nat.le_trans (hs p hpB) (Nat.le_max_left _ _)
        · have hpq : p = q := by
            apply Subtype.ext
            exact hpeq
          subst p
          exact Nat.le_max_right _ _
      · refine ⟨s, ?_⟩
        intro p hp
        rcases Nat.lt_or_eq_of_le hp with hplt | hpeq
        · exact hs p (by omega)
        · exfalso
          apply hprime
          rw [← hpeq]
          exact p.property

/-- Coverage of `m` occurs at every sufficiently late stage. -/
def EventuallyCovers
    (S : StabilizingAssignments) (k m : Nat) : Prop :=
  ∃ s₀ : Nat, ∀ s : Nat, s₀ ≤ s →
    ShiftedMatureCovers k m (S.stage s)

/-- Coverage of `m` occurs at arbitrarily late stages. -/
def CofinallyCovers
    (S : StabilizingAssignments) (k m : Nat) : Prop :=
  ∀ s₀ : Nat, ∃ s : Nat, s₀ ≤ s ∧
    ShiftedMatureCovers k m (S.stage s)

/--
A stage witness transfers to the final assignment once all coordinates that
could be mature witnesses have frozen.
-/
theorem stage_cover_transfers_to_final
    (S : StabilizingAssignments) {k m s : Nat}
    (hfrozen :
      ∀ p : Prime, k * p.1 ≤ m + 1 →
        S.freezeStage p ≤ s)
    (hcover : ShiftedMatureCovers k m (S.stage s)) :
    ShiftedMatureCovers k m S.final := by
  rcases hcover with ⟨p, hpmature, hpmod⟩
  refine ⟨p, hpmature, ?_⟩
  rw [S.final_agrees_of_frozen p s (hfrozen p hpmature)]
  exact hpmod

theorem cofinallyCovers_final
    (S : StabilizingAssignments) {k m : Nat}
    (hk : 0 < k)
    (hcover : S.CofinallyCovers k m) :
    ShiftedMatureCovers k m S.final := by
  rcases S.exists_freeze_bound (m + 1) with ⟨s₀, hs₀⟩
  rcases hcover s₀ with ⟨s, hs₀s, p, hpmature, hpmod⟩
  have hkone : 1 ≤ k := hk
  have hp_le_kp : p.1 ≤ k * p.1 := by
    simpa using Nat.mul_le_mul_right p.1 hkone
  have hpbound : p.1 ≤ m + 1 :=
    Nat.le_trans hp_le_kp hpmature
  have hpfrozen : S.freezeStage p ≤ s :=
    Nat.le_trans (hs₀ p hpbound) hs₀s
  exact S.stage_cover_transfers_to_final
    (fun q hqmature => by
      have hqbound : q.1 ≤ m + 1 :=
        Nat.le_trans
          (by simpa using Nat.mul_le_mul_right q.1 hkone)
          hqmature
      exact Nat.le_trans (hs₀ q hqbound) hs₀s)
    ⟨p, hpmature, hpmod⟩

theorem eventuallyCovers_cofinallyCovers
    (S : StabilizingAssignments) {k m : Nat}
    (hcover : S.EventuallyCovers k m) :
    S.CofinallyCovers k m := by
  rcases hcover with ⟨s₁, hs₁⟩
  intro s₀
  refine ⟨max s₀ s₁, Nat.le_max_left _ _, ?_⟩
  exact hs₁ _ (Nat.le_max_right _ _)

theorem eventuallyCovers_final
    (S : StabilizingAssignments) {k m : Nat}
    (hk : 0 < k)
    (hcover : S.EventuallyCovers k m) :
    ShiftedMatureCovers k m S.final :=
  S.cofinallyCovers_final hk
    (S.eventuallyCovers_cofinallyCovers hcover)

/--
Pointwise eventual coverage of a shifted tail transfers to the one final
assignment.  The stabilization stage may depend on the target; the final
assignment does not.
-/
theorem shiftedCoversTail_final_of_eventual
    (S : StabilizingAssignments) {k M₀ : Nat}
    (hk : 0 < k)
    (hcover :
      ∀ m : Nat, M₀ ≤ m → S.EventuallyCovers k m) :
    ShiftedCoversTail k S.final := by
  refine ⟨M₀, ?_⟩
  intro m hm
  exact S.eventuallyCovers_final hk (hcover m hm)

theorem P_of_eventual_staged_tail
    (S : StabilizingAssignments) {k M₀ : Nat}
    (hk : 0 < k)
    (hcover :
      ∀ m : Nat, M₀ ≤ m → S.EventuallyCovers k m) :
    P k :=
  P_of_shiftedCoversTail
    (S.shiftedCoversTail_final_of_eventual hk hcover)

end StabilizingAssignments

/-- An explicit schedule in which each coordinate is updated at most once. -/
structure OneShotSchedule where
  initial : ShiftedAssignment
  updateStage : Prime → Nat
  updatedValue : (p : Prime) → Fin p.1

namespace OneShotSchedule

def assignmentAt
    (S : OneShotSchedule) (s : Nat) : ShiftedAssignment :=
  fun p =>
    if S.updateStage p ≤ s then S.updatedValue p else S.initial p

theorem assignmentAt_before
    (S : OneShotSchedule) (p : Prime) (s : Nat)
    (hs : s < S.updateStage p) :
    S.assignmentAt s p = S.initial p := by
  simp [assignmentAt, Nat.not_le.mpr hs]

theorem assignmentAt_after
    (S : OneShotSchedule) (p : Prime) (s : Nat)
    (hs : S.updateStage p ≤ s) :
    S.assignmentAt s p = S.updatedValue p := by
  simp [assignmentAt, hs]

/-- Every explicit one-shot schedule is coordinatewise stabilizing. -/
def toStabilizingAssignments
    (S : OneShotSchedule) : StabilizingAssignments where
  stage := S.assignmentAt
  freezeStage := S.updateStage
  stable := by
    intro p s hps
    rw [S.assignmentAt_after p s hps]
    rw [S.assignmentAt_after p (S.updateStage p) (Nat.le_refl _)]

@[simp] theorem final_toStabilizingAssignments
    (S : OneShotSchedule) (p : Prime) :
    S.toStabilizingAssignments.final p = S.updatedValue p := by
  simp [StabilizingAssignments.final, toStabilizingAssignments,
    assignmentAt]

end OneShotSchedule

end Erdos279
