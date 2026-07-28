import Erdos279.ConstructionPartition
import Erdos279.Factorization

/-!
# Certified hard-target reservoir stages

This module joins the finite capacity matching with the annular arithmetic.
A certified stage records that every matched target has hard form and that
its controller lies between the strict lower and mature upper bounds.
-/

namespace Erdos279

structure CertifiedHardReservoirStage
    {P : HTSPriority} (D : ImmutableReservoirPlan P)
    (h : Prime)
    (k X j survivorCount reservoirCount : Nat) where
  recorded :
    RecordedFiniteReservoirStage D j survivorCount reservoirCount
  target_hard :
    ∀ i, HasHardForm h (recorded.base.target i)
  controller_in_progression :
    ∀ i, InControllerProgression h
      (recorded.base.pairedController i)
  controller_lower :
    ∀ i, recorded.base.target i / h.1 <
      (recorded.base.pairedController i).1
  controller_upper :
    ∀ i, (recorded.base.pairedController i).1 ≤ X / k
  target_above_scale :
    ∀ i, X < recorded.base.target i

namespace CertifiedHardReservoirStage

private theorem final_residue_eq_controllerResidue
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {h : Prime} {k X j survivorCount reservoirCount : Nat}
    (C : CertifiedHardReservoirStage
      D h k X j survivorCount reservoirCount)
    (i : Fin survivorCount) :
    (D.finalAssignment (C.recorded.base.pairedController i) : Nat) =
      (controllerResidue
        (C.recorded.base.pairedController i)
        (C.recorded.base.target i) : Nat) := by
  simpa [shiftedTargetResidue, controllerResidue] using
    congrArg Fin.val (C.recorded.finalAssignment_paired i)

private theorem stage_residue_eq_controllerResidue
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {h : Prime} {k X j survivorCount reservoirCount later : Nat}
    (C : CertifiedHardReservoirStage
      D h k X j survivorCount reservoirCount)
    (i : Fin survivorCount)
    (hlater : j ≤ later) :
    (D.atStage later (C.recorded.base.pairedController i) : Nat) =
      (controllerResidue
        (C.recorded.base.pairedController i)
        (C.recorded.base.target i) : Nat) := by
  simpa [shiftedTargetResidue, controllerResidue] using
    congrArg Fin.val
      (C.recorded.assignment_paired_from_stage i hlater)

/--
Every paired controller has a nonzero installed class and covers its hard
target in the one final assignment.
-/
theorem final_pair_valid
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {h : Prime} {k X j survivorCount reservoirCount : Nat}
    (C : CertifiedHardReservoirStage
      D h k X j survivorCount reservoirCount)
    (hk : 0 < k)
    (i : Fin survivorCount) :
    (controllerResidue
      (C.recorded.base.pairedController i)
      (C.recorded.base.target i) : Nat) ≠ 0 ∧
    ShiftedMatureCovers k (C.recorded.base.target i)
      D.finalAssignment := by
  exact hardForm_controller_pair_valid
    hk
    (C.target_hard i)
    (C.controller_in_progression i)
    (C.controller_lower i)
    (C.controller_upper i)
    (C.target_above_scale i)
    (C.final_residue_eq_controllerResidue i)

/--
The same validity holds at the processing stage and at every later stage.
-/
theorem stage_pair_valid
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {h : Prime} {k X j survivorCount reservoirCount later : Nat}
    (C : CertifiedHardReservoirStage
      D h k X j survivorCount reservoirCount)
    (hk : 0 < k)
    (i : Fin survivorCount)
    (hlater : j ≤ later) :
    (controllerResidue
      (C.recorded.base.pairedController i)
      (C.recorded.base.target i) : Nat) ≠ 0 ∧
    ShiftedMatureCovers k (C.recorded.base.target i)
      (D.atStage later) := by
  exact hardForm_controller_pair_valid
    hk
    (C.target_hard i)
    (C.controller_in_progression i)
    (C.controller_lower i)
    (C.controller_upper i)
    (C.target_above_scale i)
    (C.stage_residue_eq_controllerResidue i hlater)

/--
A recorded survivor is covered at every sufficiently late stage of the
stabilizing construction induced by the immutable plan.
-/
theorem paired_eventuallyCovers
    {P : HTSPriority} {D : ImmutableReservoirPlan P}
    {h : Prime} {k X j survivorCount reservoirCount : Nat}
    (C : CertifiedHardReservoirStage
      D h k X j survivorCount reservoirCount)
    (hk : 0 < k)
    (i : Fin survivorCount) :
    D.toStabilizingAssignments.EventuallyCovers k
      (C.recorded.base.target i) := by
  refine ⟨j, ?_⟩
  intro later hlater
  exact (C.stage_pair_valid hk i hlater).2

end CertifiedHardReservoirStage

end Erdos279
