import Erdos279.Factorization

/-!
# Collision-free prime-target matchings

A matching pairs distinct controller primes with distinct prime targets.
The strict gap `k*p < q` makes the residue nonzero and makes the controller
mature.  Controller injectivity produces one global dependent assignment.
-/

namespace Erdos279

structure PrimeTargetPair where
  controller : Prime
  target : Prime

namespace PrimeTargetPair

def residue (s : PrimeTargetPair) : Fin s.controller.1 :=
  controllerResidue s.controller s.target.1

def Admissible (k : Nat) (s : PrimeTargetPair) : Prop :=
  k * s.controller.1 < s.target.1

theorem controller_lt_target
    {k : Nat} {s : PrimeTargetPair}
    (hk : 0 < k) (hs : s.Admissible k) :
    s.controller.1 < s.target.1 := by
  have hp_le_kp : s.controller.1 ≤ k * s.controller.1 := by
    have hkone : 1 ≤ k := hk
    simpa using Nat.mul_le_mul_right s.controller.1 hkone
  exact Nat.lt_of_le_of_lt hp_le_kp hs

theorem residue_ne_zero
    {k : Nat} {s : PrimeTargetPair}
    (hk : 0 < k) (hs : s.Admissible k) :
    (s.residue : Nat) ≠ 0 :=
  prime_mod_prime_ne_zero_of_lt (s.controller_lt_target hk hs)

theorem mature
    {k : Nat} {s : PrimeTargetPair}
    (hs : s.Admissible k) :
    k * s.controller.1 ≤ s.target.1 + 1 :=
  Nat.le_trans (Nat.le_of_lt hs) (Nat.le_add_right _ _)

theorem covers_of_assignment
    {k : Nat} {s : PrimeTargetPair} {a : ShiftedAssignment}
    (hs : s.Admissible k)
    (ha : (a s.controller : Nat) = (s.residue : Nat)) :
    ShiftedMatureCovers k s.target.1 a :=
  controller_pair_covers (s.mature hs) ha

end PrimeTargetPair

/-- An injective matching of controller primes to distinct prime targets. -/
structure PrimeTargetMatching (ι : Type) (k : Nat) where
  pair : ι → PrimeTargetPair
  controller_injective :
    Function.Injective (fun i => (pair i).controller)
  target_injective :
    Function.Injective (fun i => (pair i).target)
  admissible :
    ∀ i : ι, (pair i).Admissible k

namespace PrimeTargetMatching

abbrev FiniteBatch (batchSize k : Nat) :=
  PrimeTargetMatching (Fin batchSize) k

abbrev Sequence (k : Nat) :=
  PrimeTargetMatching Nat k

def ControllersIn
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (h : Prime) : Prop :=
  ∀ i : ι, InControllerProgression h (M.pair i).controller

/--
The one assignment induced by the matching.  At a matched controller,
injectivity makes the chosen matching index unique; unmatched coordinates
retain the base value.
-/
noncomputable def assignment
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p =>
    if h : ∃ i : ι, (M.pair i).controller = p then
      controllerResidue p (M.pair (Classical.choose h)).target.1
    else
      base p

theorem assignment_at_controller
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (i : ι) :
    M.assignment base (M.pair i).controller =
      (M.pair i).residue := by
  let hex :
      ∃ j : ι, (M.pair j).controller = (M.pair i).controller :=
    ⟨i, rfl⟩
  rw [assignment]
  simp only [dif_pos hex]
  have hchosen :
      (M.pair (Classical.choose hex)).controller =
        (M.pair i).controller :=
    Classical.choose_spec hex
  have hindex : Classical.choose hex = i :=
    M.controller_injective hchosen
  rw [hindex]
  rfl

theorem assignment_of_unmatched
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (p : Prime)
    (hp : ∀ i : ι, (M.pair i).controller ≠ p) :
    M.assignment base p = base p := by
  have hnone : ¬ ∃ i : ι, (M.pair i).controller = p := by
    intro hex
    rcases hex with ⟨i, hi⟩
    exact hp i hi
  rw [assignment]
  simp only [dif_neg hnone]

theorem assignment_at_hub
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (h : Prime) (hcontrollers : M.ControllersIn h) :
    M.assignment base h = base h := by
  apply M.assignment_of_unmatched
  intro i hi
  have hne :
      (M.pair i).controller ≠ h :=
    inControllerProgression_ne_hub (hcontrollers i)
  exact hne hi

theorem assignment_of_not_in_progression
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    {h q : Prime}
    (hcontrollers : M.ControllersIn h)
    (hqout : ¬ InControllerProgression h q) :
    M.assignment base q = base q := by
  apply M.assignment_of_unmatched
  intro i hi
  apply hqout
  rw [← hi]
  exact hcontrollers i

theorem assignment_below_hub
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    {h q : Prime}
    (hcontrollers : M.ControllersIn h)
    (hqsmall : q.1 < h.1) :
    M.assignment base q = base q := by
  apply M.assignment_of_unmatched
  intro i hi
  have hhlt :
      h.1 < (M.pair i).controller.1 :=
    hub_lt_of_inControllerProgression (hcontrollers i)
  have hvals :
      (M.pair i).controller.1 = q.1 :=
    congrArg Subtype.val hi
  rw [hvals] at hhlt
  exact (Nat.not_lt_of_ge (Nat.le_of_lt hqsmall)) hhlt

theorem assignment_at_controller_ne_zero
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (hk : 0 < k) (i : ι) :
    (M.assignment base (M.pair i).controller : Nat) ≠ 0 := by
  rw [M.assignment_at_controller base i]
  exact (M.pair i).residue_ne_zero hk (M.admissible i)

/-- One fixed assignment covers every target in the matching. -/
theorem assignment_covers_target
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (i : ι) :
    ShiftedMatureCovers k (M.pair i).target.1
      (M.assignment base) := by
  apply (M.pair i).covers_of_assignment (M.admissible i)
  exact congrArg Fin.val (M.assignment_at_controller base i)

theorem exists_single_assignment
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment) :
    ∃ a : ShiftedAssignment,
      (∀ i : ι,
        a (M.pair i).controller = (M.pair i).residue) ∧
      (∀ i : ι,
        ShiftedMatureCovers k (M.pair i).target.1 a) := by
  refine ⟨M.assignment base, ?_, ?_⟩
  · exact M.assignment_at_controller base
  · exact M.assignment_covers_target base

theorem exists_single_nonzero_assignment
    {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (hk : 0 < k) :
    ∃ a : ShiftedAssignment,
      (∀ i : ι,
        (a (M.pair i).controller : Nat) ≠ 0) ∧
      (∀ i : ι,
        ShiftedMatureCovers k (M.pair i).target.1 a) := by
  refine ⟨M.assignment base, ?_, ?_⟩
  · exact M.assignment_at_controller_ne_zero base hk
  · exact M.assignment_covers_target base

end PrimeTargetMatching

end Erdos279
