import Erdos279.CausalUpdate

/-!
# Finite batches of causal controller updates

This module lifts the one-coordinate theorem to a finite, pairwise-distinct
list.  Its hypotheses are arithmetic and assignment invariants, rather than
a restatement of the desired coverage conclusion.
-/

namespace Erdos279

/-- A controller coordinate together with its new canonical residue. -/
structure ControllerUpdate where
  prime : Prime
  residue : Fin prime.1

/-- Apply a finite batch in list order. -/
def applyControllerUpdates :
    ShiftedAssignment → List ControllerUpdate → ShiftedAssignment
  | a, [] => a
  | a, s :: ss =>
      applyControllerUpdates
        (updateController a s.prime s.residue) ss

@[simp] theorem applyControllerUpdates_nil
    (a : ShiftedAssignment) :
    applyControllerUpdates a [] = a := rfl

@[simp] theorem applyControllerUpdates_cons
    (a : ShiftedAssignment) (s : ControllerUpdate)
    (ss : List ControllerUpdate) :
    applyControllerUpdates a (s :: ss) =
      applyControllerUpdates
        (updateController a s.prime s.residue) ss := rfl

/-- A coordinate absent from the batch is unchanged. -/
theorem applyControllerUpdates_of_prime_not_mem
    (a : ShiftedAssignment) (ss : List ControllerUpdate) (q : Prime)
    (hq : ∀ s : ControllerUpdate, s ∈ ss → q ≠ s.prime) :
    applyControllerUpdates a ss q = a q := by
  induction ss generalizing a with
  | nil =>
      rfl
  | cons s ss ih =>
      rw [applyControllerUpdates_cons]
      rw [ih]
      · exact updateController_of_ne a s.prime q s.residue
          (hq s (by simp))
      · intro t ht
        exact hq t (by simp [ht])

/--
The update prime lies in the controller progression, is beyond the mature
hub frontier, and receives a genuinely nonzero residue.
-/
def ControllerUpdate.Admissible
    (k : Nat) (h : Prime) (s : ControllerUpdate) : Prop :=
  InControllerProgression h s.prime ∧
    k * h.1 < s.prime.1 ∧
    (s.residue : Nat) ≠ 0

/--
Static hypotheses for a finite batch: distinct coordinates, admissible
updates, zero original values at all updated coordinates, and a common
causal prefix bound.
-/
def ControllerBatch.Admissible
    (k B : Nat) (h : Prime) (old : ShiftedAssignment)
    (ss : List ControllerUpdate) : Prop :=
  ss.Pairwise (fun s t => s.prime ≠ t.prime) ∧
  (∀ s : ControllerUpdate, s ∈ ss →
    s.Admissible k h) ∧
  (∀ s : ControllerUpdate, s ∈ ss →
    (old s.prime : Nat) = 0) ∧
  (∀ s : ControllerUpdate, s ∈ ss →
    B ≤ h.1 * s.prime.1)

/--
Batch causal permanence.  A pairwise-distinct admissible batch preserves
every previously covered target in the common prefix `[0,B)`.
-/
theorem applyControllerUpdates_preserves_covered_prefix
    {k B : Nat} {h : Prime} {old : ShiftedAssignment}
    {ss : List ControllerUpdate}
    (hk : 0 < k)
    (hbatch : ControllerBatch.Admissible k B h old ss)
    (holdh : (old h : Nat) = 1)
    (holdSmallZero :
      ∀ d : Prime, d.1 < h.1 → (old d : Nat) = 0) :
    ∀ m : Nat, m < B →
      ShiftedMatureCovers k m old →
      ShiftedMatureCovers k m (applyControllerUpdates old ss) := by
  induction ss generalizing old with
  | nil =>
      intro m _ hold
      simpa using hold
  | cons s ss ih =>
      rcases hbatch with
        ⟨hpair, hadmissible, hzero, hfront⟩
      have hsAdmissible : s.Admissible k h :=
        hadmissible s (by simp)
      rcases hsAdmissible with ⟨hsG, hsLarge, hsNonzero⟩
      have hsZero : (old s.prime : Nat) = 0 :=
        hzero s (by simp)
      have hsFront : B ≤ h.1 * s.prime.1 :=
        hfront s (by simp)
      have hpairParts :
          (∀ t ∈ ss, s.prime ≠ t.prime) ∧
            ss.Pairwise (fun x y => x.prime ≠ y.prime) := by
        simpa only [List.pairwise_cons] using hpair
      rcases hpairParts with ⟨hsNeTail, hpairTail⟩
      let next : ShiftedAssignment :=
        updateController old s.prime s.residue
      have hkone : 1 ≤ k := hk
      have hh_le_kh : h.1 ≤ k * h.1 := by
        simpa using Nat.mul_le_mul_right h.1 hkone
      have hh_lt_sp : h.1 < s.prime.1 :=
        Nat.lt_of_le_of_lt hh_le_kh hsLarge
      have hnextH : (next h : Nat) = 1 := by
        have hhne : h ≠ s.prime := by
          intro heq
          have hvals : h.1 = s.prime.1 :=
            congrArg Subtype.val heq
          exact (Nat.ne_of_lt hh_lt_sp) hvals
        change
          (updateController old s.prime s.residue h : Nat) = 1
        rw [updateController_of_ne old s.prime h s.residue hhne]
        exact holdh
      have hnextSmallZero :
          ∀ d : Prime, d.1 < h.1 → (next d : Nat) = 0 := by
        intro d hd
        have hdne : d ≠ s.prime := by
          intro heq
          have hvals : d.1 = s.prime.1 :=
            congrArg Subtype.val heq
          have : s.prime.1 < s.prime.1 := by
            calc
              s.prime.1 = d.1 := hvals.symm
              _ < h.1 := hd
              _ < s.prime.1 := hh_lt_sp
          exact Nat.lt_irrefl _ this
        change
          (updateController old s.prime s.residue d : Nat) = 0
        rw [updateController_of_ne old s.prime d s.residue hdne]
        exact holdSmallZero d hd
      have hnextTailZero :
          ∀ t : ControllerUpdate, t ∈ ss →
            (next t.prime : Nat) = 0 := by
        intro t ht
        have htne : t.prime ≠ s.prime := Ne.symm (hsNeTail t ht)
        rw [show next t.prime = old t.prime by
          exact updateController_of_ne old s.prime t.prime s.residue htne]
        exact hzero t (by simp [ht])
      have htailBatch :
          ControllerBatch.Admissible k B h next ss := by
        refine ⟨hpairTail, ?_, hnextTailZero, ?_⟩
        · intro t ht
          exact hadmissible t (by simp [ht])
        · intro t ht
          exact hfront t (by simp [ht])
      intro m hmB hold
      have hmFront : m < h.1 * s.prime.1 :=
        Nat.lt_of_lt_of_le hmB hsFront
      have hnextCover : ShiftedMatureCovers k m next := by
        exact causal_update_preserves_below_frontier
          s.residue hk hmFront hold hsG hsLarge hsZero hsNonzero
          holdh holdSmallZero
      simpa [next] using
        ih htailBatch hnextH hnextSmallZero m hmB hnextCover

end Erdos279
