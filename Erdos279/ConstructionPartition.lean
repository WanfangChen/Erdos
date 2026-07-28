import Erdos279.ConstructionCore
import Erdos279.Stabilization

/-!
# Prime-pool partition and immutable reservoir plans

This module formalizes the hub-first `H/T/S/outside` partition, the
one-time activation of reservoir primes, the finite capacity injection, and
compatibility of all local pairings with one global assignment.
-/

namespace Erdos279

inductive HTSRole where
  | H
  | T
  | S
  | outside
deriving DecidableEq, Repr

/-- Boolean membership data, including `H,T ⊆ G` and `H ∩ T = ∅`. -/
structure HTSPriority where
  inG : Prime → Bool
  inH : Prime → Bool
  inT : Prime → Bool
  H_sub_G : ∀ p, inH p = true → inG p = true
  T_sub_G : ∀ p, inT p = true → inG p = true
  H_disjoint_T : ∀ p, inH p = true → inT p = true → False

/-- Total priority classification; `S` is the remainder of `G`. -/
def HTSPriority.role (P : HTSPriority) (p : Prime) : HTSRole :=
  if P.inH p then
    .H
  else if P.inT p then
    .T
  else if P.inG p then
    .S
  else
    .outside

theorem HTSPriority.role_eq_H_iff
    (P : HTSPriority) (p : Prime) :
    P.role p = .H ↔ P.inH p = true := by
  cases hH : P.inH p <;>
    cases hT : P.inT p <;>
      cases hG : P.inG p <;>
        simp [HTSPriority.role, hH, hT, hG]

private theorem HTSPriority.role_eq_T_raw
    (P : HTSPriority) (p : Prime) :
    P.role p = .T ↔ P.inH p = false ∧ P.inT p = true := by
  cases hH : P.inH p <;>
    cases hT : P.inT p <;>
      cases hG : P.inG p <;>
        simp [HTSPriority.role, hH, hT, hG]

theorem HTSPriority.role_eq_T_iff
    (P : HTSPriority) (p : Prime) :
    P.role p = .T ↔ P.inT p = true := by
  rw [P.role_eq_T_raw]
  constructor
  · exact And.right
  · intro hT
    refine ⟨?_, hT⟩
    cases hH : P.inH p with
    | false => rfl
    | true => exact False.elim (P.H_disjoint_T p hH hT)

theorem HTSPriority.role_eq_S_iff
    (P : HTSPriority) (p : Prime) :
    P.role p = .S ↔
      P.inG p = true ∧ P.inH p = false ∧ P.inT p = false := by
  cases hH : P.inH p <;>
    cases hT : P.inT p <;>
      cases hG : P.inG p <;>
        simp [HTSPriority.role, hH, hT, hG, and_comm]

private theorem HTSPriority.role_eq_outside_raw
    (P : HTSPriority) (p : Prime) :
    P.role p = .outside ↔
      P.inH p = false ∧ P.inT p = false ∧ P.inG p = false := by
  cases hH : P.inH p <;>
    cases hT : P.inT p <;>
      cases hG : P.inG p <;>
        simp [HTSPriority.role, hH, hT, hG]

theorem HTSPriority.role_eq_outside_iff
    (P : HTSPriority) (p : Prime) :
    P.role p = .outside ↔ P.inG p = false := by
  rw [P.role_eq_outside_raw]
  constructor
  · exact fun hr => hr.2.2
  · intro hG
    have hH : P.inH p = false := by
      cases hp : P.inH p with
      | false => rfl
      | true =>
          have htrue : P.inG p = true := P.H_sub_G p hp
          rw [hG] at htrue
          cases htrue
    have hT : P.inT p = false := by
      cases hp : P.inT p with
      | false => rfl
      | true =>
          have htrue : P.inG p = true := P.T_sub_G p hp
          rw [hG] at htrue
          cases htrue
    exact ⟨hH, hT, hG⟩

/--
The arithmetic hub is outside `G`, so it is handled before the inner
partition and cannot accidentally receive the outside-zero class.
-/
structure HubHTSLayout where
  hub : Prime
  inner : HTSPriority
  hub_not_G : inner.inG hub = false

inductive PaperPrimeRole where
  | hub
  | H
  | T
  | S
  | outside
deriving DecidableEq, Repr

def HubHTSLayout.role (L : HubHTSLayout) (p : Prime) : PaperPrimeRole :=
  if p = L.hub then
    .hub
  else
    match L.inner.role p with
    | .H => .H
    | .T => .T
    | .S => .S
    | .outside => .outside

theorem HubHTSLayout.role_hub (L : HubHTSLayout) :
    L.role L.hub = .hub := by
  simp [HubHTSLayout.role]

theorem HubHTSLayout.role_of_ne_hub
    (L : HubHTSLayout) {p : Prime}
    (hne : p ≠ L.hub) :
    L.role p =
      match L.inner.role p with
      | .H => .H
      | .T => .T
      | .S => .S
      | .outside => .outside := by
  simp [HubHTSLayout.role, hne]

theorem HubHTSLayout.inner_role_hub_is_outside
    (L : HubHTSLayout) :
    L.inner.role L.hub = .outside :=
  (L.inner.role_eq_outside_iff L.hub).2 L.hub_not_G

def shiftedZeroResidue (p : Prime) : Fin p.1 :=
  ⟨0, p.pos⟩

def shiftedOneResidue (p : Prime) : Fin p.1 :=
  ⟨1, p.one_lt⟩

/-- Hub and `H` start at one; every other role starts at zero. -/
def HubHTSLayout.initialAssignment (L : HubHTSLayout) :
    ShiftedAssignment :=
  fun p =>
    match L.role p with
    | .hub => shiftedOneResidue p
    | .H => shiftedOneResidue p
    | .T => shiftedZeroResidue p
    | .S => shiftedZeroResidue p
    | .outside => shiftedZeroResidue p

theorem HubHTSLayout.initialAssignment_hub
    (L : HubHTSLayout) :
    (L.initialAssignment L.hub : Nat) = 1 := by
  simp [HubHTSLayout.initialAssignment, L.role_hub, shiftedOneResidue]

theorem HubHTSLayout.initialAssignment_H
    (L : HubHTSLayout) {p : Prime}
    (hH : L.role p = .H) :
    (L.initialAssignment p : Nat) = 1 := by
  simp [HubHTSLayout.initialAssignment, hH, shiftedOneResidue]

theorem HubHTSLayout.initialAssignment_zero_of_role
    (L : HubHTSLayout) {p : Prime}
    (hrole : L.role p = .T ∨ L.role p = .S ∨ L.role p = .outside) :
    (L.initialAssignment p : Nat) = 0 := by
  rcases hrole with hT | hrest
  · simp [HubHTSLayout.initialAssignment, hT, shiftedZeroResidue]
  · rcases hrest with hS | hout
    · simp [HubHTSLayout.initialAssignment, hS, shiftedZeroResidue]
    · simp [HubHTSLayout.initialAssignment, hout, shiftedZeroResidue]

def shiftedTargetResidue (p : Prime) (m : Nat) : Fin p.1 :=
  ⟨m % p.1, Nat.mod_lt _ p.pos⟩

/--
An immutable plan: every `S` coordinate has one activation stage and one
final target/default residue.
-/
structure ImmutableReservoirPlan (P : HTSPriority) where
  activation : Prime → Option Nat
  activation_none_iff :
    ∀ p, activation p = none ↔ P.role p ≠ .S
  pairedTarget : Prime → Option Nat
  paired_only_in_S :
    ∀ p m, pairedTarget p = some m → P.role p = .S
  defaultClass : ShiftedAssignment

def ImmutableReservoirPlan.finalAssignment
    {P : HTSPriority} (D : ImmutableReservoirPlan P) :
    ShiftedAssignment :=
  fun p =>
    match D.pairedTarget p with
    | some m => shiftedTargetResidue p m
    | none => D.defaultClass p

def ImmutableReservoirPlan.atStage
    {P : HTSPriority} (D : ImmutableReservoirPlan P) (j : Nat) :
    ShiftedAssignment :=
  fun p =>
    match D.activation p with
    | none => D.finalAssignment p
    | some i =>
        if i ≤ j then D.finalAssignment p else ⟨0, p.pos⟩

theorem ImmutableReservoirPlan.finalAssignment_of_paired
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime} {m : Nat}
    (hpair : D.pairedTarget p = some m) :
    D.finalAssignment p = shiftedTargetResidue p m := by
  simp [ImmutableReservoirPlan.finalAssignment, hpair]

theorem ImmutableReservoirPlan.finalAssignment_of_unpaired
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime}
    (hpair : D.pairedTarget p = none) :
    D.finalAssignment p = D.defaultClass p := by
  simp [ImmutableReservoirPlan.finalAssignment, hpair]

theorem ImmutableReservoirPlan.atStage_of_inactive
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime} {j : Nat}
    (hinactive : D.activation p = none) :
    D.atStage j p = D.finalAssignment p := by
  simp [ImmutableReservoirPlan.atStage, hinactive]

theorem ImmutableReservoirPlan.atStage_before_activation
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime} {i j : Nat}
    (hactive : D.activation p = some i)
    (hbefore : j < i) :
    (D.atStage j p : Nat) = 0 := by
  simp [ImmutableReservoirPlan.atStage, hactive, Nat.not_le.mpr hbefore]

theorem ImmutableReservoirPlan.atStage_after_activation
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime} {i j : Nat}
    (hactive : D.activation p = some i)
    (hafter : i ≤ j) :
    D.atStage j p = D.finalAssignment p := by
  simp [ImmutableReservoirPlan.atStage, hactive, hafter]

theorem ImmutableReservoirPlan.activation_unique
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime} {i j : Nat}
    (hi : D.activation p = some i)
    (hj : D.activation p = some j) :
    i = j := by
  rw [hi] at hj
  exact Option.some.inj hj

theorem ImmutableReservoirPlan.reservoir_has_unique_activation
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime}
    (hS : P.role p = .S) :
    ∃ i, D.activation p = some i ∧
      ∀ j, D.activation p = some j → j = i := by
  cases hactive : D.activation p with
  | none =>
      have hnS : P.role p ≠ .S :=
        (D.activation_none_iff p).1 hactive
      exact False.elim (hnS hS)
  | some i =>
      refine ⟨i, rfl, ?_⟩
      intro j hj
      exact Option.some.inj hj.symm

theorem ImmutableReservoirPlan.nonreservoir_is_permanent
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime}
    (hnS : P.role p ≠ .S) :
    ∀ j, D.atStage j p = D.finalAssignment p := by
  intro j
  exact D.atStage_of_inactive ((D.activation_none_iff p).2 hnS)

theorem ImmutableReservoirPlan.no_reselection
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    {p : Prime} {i j₁ j₂ : Nat}
    (hactive : D.activation p = some i)
    (hj₁ : i ≤ j₁)
    (hj₂ : i ≤ j₂) :
    D.atStage j₁ p = D.atStage j₂ p := by
  rw [D.atStage_after_activation hactive hj₁]
  rw [D.atStage_after_activation hactive hj₂]

theorem ImmutableReservoirPlan.coordinate_eventually_final
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    (p : Prime) :
    ∃ i, ∀ j, i ≤ j → D.atStage j p = D.finalAssignment p := by
  cases hactive : D.activation p with
  | none =>
      exact ⟨0, fun _ _ => D.atStage_of_inactive hactive⟩
  | some i =>
      exact ⟨i, fun _ hij => D.atStage_after_activation hactive hij⟩

/-- The declared freeze stage associated with the immutable activation map. -/
def ImmutableReservoirPlan.freezeStage
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    (p : Prime) : Nat :=
  match D.activation p with
  | none => 0
  | some i => i

/--
Every immutable reservoir plan is a coordinatewise stabilizing construction.
-/
def ImmutableReservoirPlan.toStabilizingAssignments
    {P : HTSPriority} (D : ImmutableReservoirPlan P) :
    StabilizingAssignments where
  stage := D.atStage
  freezeStage := D.freezeStage
  stable := by
    intro p s hfreeze
    cases hactive : D.activation p with
    | none =>
        simp [ImmutableReservoirPlan.atStage, hactive]
    | some i =>
        have his : i ≤ s := by
          simpa [ImmutableReservoirPlan.freezeStage, hactive] using hfreeze
        simp [ImmutableReservoirPlan.atStage,
          ImmutableReservoirPlan.freezeStage, hactive, his]

/-- The stabilization limit is definitionally the plan's final assignment. -/
@[simp] theorem ImmutableReservoirPlan.final_toStabilizingAssignments
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    (p : Prime) :
    D.toStabilizingAssignments.final p = D.finalAssignment p := by
  cases hactive : D.activation p with
  | none =>
      simp [StabilizingAssignments.final,
        ImmutableReservoirPlan.toStabilizingAssignments,
        ImmutableReservoirPlan.freezeStage,
        ImmutableReservoirPlan.atStage, hactive]
  | some i =>
      simp [StabilizingAssignments.final,
        ImmutableReservoirPlan.toStabilizingAssignments,
        ImmutableReservoirPlan.freezeStage,
        ImmutableReservoirPlan.atStage, hactive]

/-- Finite survivor and reservoir enumerations at one stage. -/
structure FiniteReservoirStage
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    (j survivorCount reservoirCount : Nat) where
  target : Fin survivorCount → Nat
  target_injective : Function.Injective target
  reservoir : Fin reservoirCount → Prime
  reservoir_injective : Function.Injective reservoir
  reservoir_at_stage :
    ∀ i, D.activation (reservoir i) = some j
  capacity : survivorCount ≤ reservoirCount

def finiteCapacityInjection
    {survivorCount reservoirCount : Nat}
    (h : survivorCount ≤ reservoirCount) :
    Fin survivorCount → Fin reservoirCount :=
  Fin.castLE h

theorem finiteCapacityInjection_injective
    {survivorCount reservoirCount : Nat}
    (h : survivorCount ≤ reservoirCount) :
    Function.Injective (finiteCapacityInjection h) := by
  intro i₁ i₂ heq
  apply Fin.ext
  simpa [finiteCapacityInjection] using
    congrArg (fun x : Fin reservoirCount => x.val) heq

def FiniteReservoirStage.pairedController
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j survivorCount reservoirCount : Nat}
    (B : FiniteReservoirStage D j survivorCount reservoirCount)
    (i : Fin survivorCount) : Prime :=
  B.reservoir (finiteCapacityInjection B.capacity i)

theorem FiniteReservoirStage.pairedController_injective
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j survivorCount reservoirCount : Nat}
    (B : FiniteReservoirStage D j survivorCount reservoirCount) :
    Function.Injective B.pairedController := by
  intro i₁ i₂ heq
  apply finiteCapacityInjection_injective B.capacity
  apply B.reservoir_injective
  exact heq

theorem FiniteReservoirStage.pairedController_at_stage
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j survivorCount reservoirCount : Nat}
    (B : FiniteReservoirStage D j survivorCount reservoirCount)
    (i : Fin survivorCount) :
    D.activation (B.pairedController i) = some j :=
  B.reservoir_at_stage (finiteCapacityInjection B.capacity i)

theorem FiniteReservoirStage.controllers_disjoint
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j₁ j₂ s₁ r₁ s₂ r₂ : Nat}
    (B₁ : FiniteReservoirStage D j₁ s₁ r₁)
    (B₂ : FiniteReservoirStage D j₂ s₂ r₂)
    (hne : j₁ ≠ j₂)
    (i₁ : Fin s₁) (i₂ : Fin s₂) :
    B₁.pairedController i₁ ≠ B₂.pairedController i₂ := by
  intro heq
  have h₁ := B₁.pairedController_at_stage i₁
  have h₂ := B₂.pairedController_at_stage i₂
  rw [heq] at h₁
  exact hne (D.activation_unique h₁ h₂)

/-- A local finite matching recorded in the one global immutable plan. -/
structure RecordedFiniteReservoirStage
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    (j survivorCount reservoirCount : Nat) where
  base : FiniteReservoirStage D j survivorCount reservoirCount
  pairing_recorded :
    ∀ i, D.pairedTarget (base.pairedController i) =
      some (base.target i)

theorem RecordedFiniteReservoirStage.finalAssignment_paired
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j survivorCount reservoirCount : Nat}
    (R : RecordedFiniteReservoirStage D j survivorCount reservoirCount)
    (i : Fin survivorCount) :
    D.finalAssignment (R.base.pairedController i) =
      shiftedTargetResidue (R.base.pairedController i) (R.base.target i) :=
  D.finalAssignment_of_paired (R.pairing_recorded i)

theorem RecordedFiniteReservoirStage.assignment_paired_from_stage
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j survivorCount reservoirCount : Nat}
    (R : RecordedFiniteReservoirStage D j survivorCount reservoirCount)
    (i : Fin survivorCount)
    {later : Nat} (hlater : j ≤ later) :
    D.atStage later (R.base.pairedController i) =
      shiftedTargetResidue
        (R.base.pairedController i) (R.base.target i) := by
  calc
    D.atStage later (R.base.pairedController i) =
        D.finalAssignment (R.base.pairedController i) :=
      D.atStage_after_activation
        (R.base.pairedController_at_stage i) hlater
    _ = shiftedTargetResidue
          (R.base.pairedController i) (R.base.target i) :=
      R.finalAssignment_paired i

theorem RecordedFiniteReservoirStage.assignment_paired_mod_from_stage
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j survivorCount reservoirCount : Nat}
    (R : RecordedFiniteReservoirStage D j survivorCount reservoirCount)
    (i : Fin survivorCount)
    {later : Nat} (hlater : j ≤ later) :
    (D.atStage later (R.base.pairedController i) : Nat) =
      R.base.target i % (R.base.pairedController i).1 := by
  rw [R.assignment_paired_from_stage i hlater]
  rfl

/-- A mature recorded pairing covers its target at every later stage. -/
theorem RecordedFiniteReservoirStage.covers_paired_from_stage
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j survivorCount reservoirCount k : Nat}
    (R : RecordedFiniteReservoirStage D j survivorCount reservoirCount)
    (i : Fin survivorCount)
    (hmature :
      k * (R.base.pairedController i).1 ≤ R.base.target i + 1)
    {later : Nat} (hlater : j ≤ later) :
    ShiftedMatureCovers k (R.base.target i) (D.atStage later) := by
  refine ⟨R.base.pairedController i, hmature, ?_⟩
  exact (R.assignment_paired_mod_from_stage i hlater).symm

/-- The same recorded pairing covers its target in the global final assignment. -/
theorem RecordedFiniteReservoirStage.finalAssignment_covers_paired
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {j survivorCount reservoirCount k : Nat}
    (R : RecordedFiniteReservoirStage D j survivorCount reservoirCount)
    (i : Fin survivorCount)
    (hmature :
      k * (R.base.pairedController i).1 ≤ R.base.target i + 1) :
    ShiftedMatureCovers k (R.base.target i) D.finalAssignment := by
  refine ⟨R.base.pairedController i, hmature, ?_⟩
  have hassign := R.finalAssignment_paired i
  exact congrArg Fin.val hassign |>.symm

end Erdos279
