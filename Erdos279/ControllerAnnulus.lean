import Erdos279.PeriodicHTSLayout
import Erdos279.HardReservoirStage
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite controller annuli

This file defines the concrete finite sets

`S ∩ (Y,Z]`

and, in particular, the stage annulus

`S ∩ (Xnext / h, X / k]`

from (3.8).  It also supplies canonical collision-free enumerations and the
exact integer bounds used by the controller-validity lemma.
-/

namespace Erdos279

/-- Prime elements of the complementary controller reservoir in `(Y,Z]`. -/
noncomputable def controllerReservoirAnnulus
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (Y Z : Nat) :
    Finset Prime := by
  classical
  exact
    ((Finset.Ioc Y Z).subtype IsPrime).filter
      (InControllerReservoir h L R H)

@[simp]
theorem mem_controllerReservoirAnnulus
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {Y Z : Nat}
    {p : Prime} :
    p ∈ controllerReservoirAnnulus h L R H Y Z ↔
      Y < p.1 ∧ p.1 ≤ Z ∧
        InControllerReservoir h L R H p := by
  classical
  simp [controllerReservoirAnnulus, and_assoc]

/-- The exact number of available controller primes in an annulus. -/
noncomputable def controllerReservoirAnnulusCount
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (Y Z : Nat) : Nat :=
  (controllerReservoirAnnulus h L R H Y Z).card

/-- Canonical enumeration of a finite set by `Fin card`. -/
noncomputable def enumeratePrimeFinset
    (s : Finset Prime) : Fin s.card → Prime :=
  fun i => (s.equivFin.symm i).1

theorem enumeratePrimeFinset_injective
    (s : Finset Prime) :
    Function.Injective (enumeratePrimeFinset s) := by
  intro i j hij
  apply s.equivFin.symm.injective
  apply Subtype.ext
  exact hij

theorem enumeratePrimeFinset_mem
    (s : Finset Prime) (i : Fin s.card) :
    enumeratePrimeFinset s i ∈ s :=
  (s.equivFin.symm i).2

/-- Canonical enumeration of the controller reservoir annulus. -/
noncomputable def enumerateControllerReservoirAnnulus
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (Y Z : Nat) :
    Fin (controllerReservoirAnnulusCount h L R H Y Z) →
      Prime :=
  enumeratePrimeFinset
    (controllerReservoirAnnulus h L R H Y Z)

theorem enumerateControllerReservoirAnnulus_injective
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (Y Z : Nat) :
    Function.Injective
      (enumerateControllerReservoirAnnulus
        h L R H Y Z) :=
  enumeratePrimeFinset_injective _

theorem enumerateControllerReservoirAnnulus_mem
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (Y Z : Nat)
    (i : Fin
      (controllerReservoirAnnulusCount h L R H Y Z)) :
    enumerateControllerReservoirAnnulus h L R H Y Z i ∈
      controllerReservoirAnnulus h L R H Y Z :=
  enumeratePrimeFinset_mem _ i

/-- Separated half-open annuli are disjoint. -/
theorem controllerReservoirAnnulus_disjoint
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    {Y₁ Z₁ Y₂ Z₂ : Nat}
    (hsep : Z₁ ≤ Y₂) :
    Disjoint
      (controllerReservoirAnnulus h L R H Y₁ Z₁)
      (controllerReservoirAnnulus h L R H Y₂ Z₂) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hp₁' :=
    (mem_controllerReservoirAnnulus.mp hp₁).2.1
  have hp₂' :=
    (mem_controllerReservoirAnnulus.mp hp₂).1
  omega

/-- The stage-`j` annulus in the exact integer form used by the existing
hard-target certification layer. -/
noncomputable def hardStageControllerAnnulus
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (k X Xnext : Nat) : Finset Prime :=
  controllerReservoirAnnulus h L R H
    (Xnext / h.1) (X / k)

@[simp]
theorem mem_hardStageControllerAnnulus
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {k X Xnext : Nat} {p : Prime} :
    p ∈ hardStageControllerAnnulus
        h L R H k X Xnext ↔
      Xnext / h.1 < p.1 ∧
        p.1 ≤ X / k ∧
        InControllerReservoir h L R H p := by
  simp [hardStageControllerAnnulus]

/-- Every prime in a hard-stage annulus lies in the controller
progression. -/
theorem hardStageControllerAnnulus_in_progression
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {k X Xnext : Nat} {p : Prime}
    (hp : p ∈ hardStageControllerAnnulus
      h L R H k X Xnext) :
    InControllerProgression h p :=
  (mem_hardStageControllerAnnulus.mp hp).2.2
    |>.inControllerProgression

/-- The annulus supplies the mature upper bound. -/
theorem hardStageControllerAnnulus_upper
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {k X Xnext : Nat} {p : Prime}
    (hp : p ∈ hardStageControllerAnnulus
      h L R H k X Xnext) :
    p.1 ≤ X / k :=
  (mem_hardStageControllerAnnulus.mp hp).2.1

/-- If a target belongs to `(X,Xnext]`, every prime in the corresponding
annulus is strictly above `m/h`. -/
theorem hardStageControllerAnnulus_above_target_div_hub
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {k X Xnext m : Nat} {p : Prime}
    (hp : p ∈ hardStageControllerAnnulus
      h L R H k X Xnext)
    (hm : m ≤ Xnext) :
    m / h.1 < p.1 := by
  exact
    (Nat.div_le_div_right hm).trans_lt
      (mem_hardStageControllerAnnulus.mp hp).1

/-- A stage annulus contains exactly the number recorded by the generic
annulus-count definition. -/
theorem hardStageControllerAnnulus_card
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (k X Xnext : Nat) :
    (hardStageControllerAnnulus
      h L R H k X Xnext).card =
      controllerReservoirAnnulusCount h L R H
        (Xnext / h.1) (X / k) :=
  rfl

/-- A one-step separation condition on a monotone scale makes all of the
hard-stage controller annuli pairwise disjoint.  The condition compares the
upper endpoint of stage `i` with the lower endpoint two scale indices later;
monotonicity then handles every later stage. -/
theorem hardStageControllerAnnuli_pairwise_disjoint
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (k : Nat)
    (scale : Nat → Nat)
    (hmono : Monotone scale)
    (hsep :
      ∀ i,
        scale i / k ≤ scale (i + 2) / h.1) :
    ∀ i j, i ≠ j →
      Disjoint
        (hardStageControllerAnnulus
          h L R H k (scale i) (scale (i + 1)))
        (hardStageControllerAnnulus
          h L R H k (scale j) (scale (j + 1))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hijScale : scale (i + 2) ≤ scale (j + 1) := by
      apply hmono
      omega
    have hbound :
        scale i / k ≤ scale (j + 1) / h.1 :=
      (hsep i).trans (Nat.div_le_div_right hijScale)
    exact
      controllerReservoirAnnulus_disjoint
        h L R H hbound
  · have hjiScale : scale (j + 2) ≤ scale (i + 1) := by
      apply hmono
      omega
    have hbound :
        scale j / k ≤ scale (i + 1) / h.1 :=
      (hsep j).trans (Nat.div_le_div_right hjiScale)
    exact
      (controllerReservoirAnnulus_disjoint
        h L R H hbound).symm

end Erdos279
