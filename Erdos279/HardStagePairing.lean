import Erdos279.ControllerAnnulus

/-!
# Concrete finite hard-stage pairings

Given the cardinal inequality comparing surviving hard targets with the
available `S`-primes in the corresponding annulus, this file constructs the
actual injective pairing used in (3.14).  No asymptotic estimate is assumed:
the finite cardinal inequality is an explicit argument.
-/

namespace Erdos279

/-- Canonical enumeration of a finite natural-number set. -/
noncomputable def enumerateNatFinset
    (s : Finset Nat) : Fin s.card → Nat :=
  fun i => (s.equivFin.symm i).1

theorem enumerateNatFinset_injective
    (s : Finset Nat) :
    Function.Injective (enumerateNatFinset s) := by
  intro i j hij
  apply s.equivFin.symm.injective
  apply Subtype.ext
  exact hij

theorem enumerateNatFinset_mem
    (s : Finset Nat) (i : Fin s.card) :
    enumerateNatFinset s i ∈ s :=
  (s.equivFin.symm i).2

/-- The exact finite pairing at one hard-target stage. -/
structure HardStagePairing
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z k X Xnext : Nat)
    (a : OldPrimeClasses h z) where
  target :
    Fin (hardSurvivors h z a X Xnext).card → Nat
  controller :
    Fin (hardSurvivors h z a X Xnext).card → Prime
  target_injective : Function.Injective target
  controller_injective : Function.Injective controller
  target_mem :
    ∀ i, target i ∈ hardSurvivors h z a X Xnext
  target_surjective :
    ∀ m ∈ hardSurvivors h z a X Xnext,
      ∃ i, target i = m
  controller_mem :
    ∀ i, controller i ∈
      hardStageControllerAnnulus h L R H k X Xnext

/-- The finite cardinal capacity inequality canonically produces a
collision-free hard-stage pairing. -/
noncomputable def hardStagePairingOfCardLe
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z k X Xnext : Nat)
    (a : OldPrimeClasses h z)
    (hcapacity :
      (hardSurvivors h z a X Xnext).card ≤
        (hardStageControllerAnnulus
          h L R H k X Xnext).card) :
    HardStagePairing h L R H z k X Xnext a := by
  let survivors := hardSurvivors h z a X Xnext
  let annulus :=
    hardStageControllerAnnulus h L R H k X Xnext
  exact
    { target := enumerateNatFinset survivors
      controller := fun i =>
        enumeratePrimeFinset annulus
          (finiteCapacityInjection hcapacity i)
      target_injective :=
        enumerateNatFinset_injective survivors
      controller_injective := by
        apply Function.Injective.comp
          (enumeratePrimeFinset_injective annulus)
        exact finiteCapacityInjection_injective hcapacity
      target_mem := enumerateNatFinset_mem survivors
      target_surjective := by
        intro m hm
        let x : survivors := ⟨m, hm⟩
        refine ⟨survivors.equivFin x, ?_⟩
        change
          (survivors.equivFin.symm
            (survivors.equivFin x)).1 = m
        rw [Equiv.symm_apply_apply]
      controller_mem := by
        intro i
        exact enumeratePrimeFinset_mem annulus
          (finiteCapacityInjection hcapacity i) }

namespace HardStagePairing

theorem target_above_scale
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    X < B.target i :=
  (mem_hardSurvivors.mp (B.target_mem i)).1

theorem target_at_most_next
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    B.target i ≤ Xnext :=
  (mem_hardSurvivors.mp (B.target_mem i)).2.1

theorem target_hard
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    HasHardForm h (B.target i) :=
  (mem_hardSurvivors.mp (B.target_mem i)).2.2.1

theorem target_avoids_old
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    AvoidsOldClasses a (B.target i) :=
  (mem_hardSurvivors.mp (B.target_mem i)).2.2.2

theorem controller_in_progression
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    InControllerProgression h (B.controller i) :=
  hardStageControllerAnnulus_in_progression
    (B.controller_mem i)

theorem controller_lower
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    B.target i / h.1 < (B.controller i).1 :=
  hardStageControllerAnnulus_above_target_div_hub
    (B.controller_mem i) (B.target_at_most_next i)

theorem controller_upper
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    (B.controller i).1 ≤ X / k :=
  hardStageControllerAnnulus_upper (B.controller_mem i)

/-- The residue prescribed by (3.14) is nonzero. -/
theorem residue_ne_zero
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    (controllerResidue (B.controller i) (B.target i) : Nat) ≠ 0 :=
  hardForm_controllerResidue_ne_zero
    (B.target_hard i)
    (B.controller_in_progression i)
    (B.controller_lower i)

/-- Every paired controller is mature at its target. -/
theorem controller_mature
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (hk : 0 < k)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    k * (B.controller i).1 ≤ B.target i + 1 :=
  controller_mature_from_annulus
    hk (B.controller_upper i) (B.target_above_scale i)

/-- Any assignment recording all prescribed residues covers every target in
the finite pairing. -/
theorem assignment_covers
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (hk : 0 < k)
    (assignment : ShiftedAssignment)
    (hrecorded :
      ∀ i,
        (assignment (B.controller i) : Nat) =
          (controllerResidue
            (B.controller i) (B.target i) : Nat))
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    ShiftedMatureCovers k (B.target i) assignment :=
  controller_pair_covers
    (B.controller_mature hk i) (hrecorded i)

end HardStagePairing

end Erdos279
