import Erdos279.VariableHardPairingSchedule

/-!
# Recursive core for the scale-dependent hard schedule

At stage `j`, the old residue vector is read from the assignment produced
by the preceding stages.  A finite pairing is then chosen and the whole
current controller annulus is activated: paired controllers receive their
target residue, while unused controllers receive the nonzero default
class `1`.
-/

namespace Erdos279

/-- Replace a zero residue by the canonical class `1`, leaving every
nonzero residue unchanged. -/
def forceNonzeroResidue (p : Prime) (u : Fin p.1) : Fin p.1 :=
  if hu : (u : Nat) = 0 then
    ⟨1, p.one_lt⟩
  else
    u

theorem forceNonzeroResidue_ne_zero
    (p : Prime) (u : Fin p.1) :
    (forceNonzeroResidue p u : Nat) ≠ 0 := by
  by_cases hu : (u : Nat) = 0
  · simp [forceNonzeroResidue, hu]
  · simpa [forceNonzeroResidue, hu] using hu

theorem forceNonzeroResidue_eq_self
    (p : Prime) (u : Fin p.1)
    (hu : (u : Nat) ≠ 0) :
    forceNonzeroResidue p u = u := by
  simp [forceNonzeroResidue, hu]

/-- Turn any assignment into a legal arbitrary nonzero old-class vector
at a finite cutoff. -/
def nonzeroOldPrimeClasses
    (h : Prime) (z : Nat)
    (assignment : ShiftedAssignment) :
    OldPrimeClasses h z where
  residue p := forceNonzeroResidue p (assignment p)
  nonzero := by
    intro p _hpG _hpz
    exact forceNonzeroResidue_ne_zero p (assignment p)

/-- The value installed at a prime when one finite hard stage is
activated.  Unpaired primes receive class `1`. -/
noncomputable def installedHardStageValue
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (p : Prime) : Fin p.1 := by
  classical
  exact
    if hex :
        ∃ i : Fin (hardSurvivors h z a X Xnext).card,
          B.controller i = p then
      ⟨B.target (Classical.choose hex) % p.1,
        Nat.mod_lt _ p.pos⟩
    else
      ⟨1, p.one_lt⟩

theorem installedHardStageValue_at_controller
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    (installedHardStageValue B (B.controller i) : Nat) =
      (controllerResidue (B.controller i) (B.target i) : Nat) := by
  let hex :
      ∃ t : Fin (hardSurvivors h z a X Xnext).card,
        B.controller t = B.controller i :=
    ⟨i, rfl⟩
  rw [installedHardStageValue]
  simp only [dif_pos hex]
  have hcontroller :
      B.controller (Classical.choose hex) =
        B.controller i :=
    Classical.choose_spec hex
  have hindex :
      Classical.choose hex = i :=
    B.controller_injective hcontroller
  rw [hindex]
  rfl

theorem installedHardStageValue_ne_zero
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (p : Prime) :
    (installedHardStageValue B p : Nat) ≠ 0 := by
  classical
  by_cases hex :
      ∃ i : Fin (hardSurvivors h z a X Xnext).card,
        B.controller i = p
  · obtain ⟨i, hi⟩ := hex
    subst p
    rw [installedHardStageValue_at_controller B i]
    exact B.residue_ne_zero i
  · simp [installedHardStageValue, hex]

/-- Activate one full annulus over the preceding assignment. -/
noncomputable def installHardStage
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (old : ShiftedAssignment)
    (B : HardStagePairing h L R H z k X Xnext a) :
    ShiftedAssignment := by
  classical
  exact fun p =>
    if p ∈ hardStageControllerAnnulus h L R H k X Xnext then
      installedHardStageValue B p
    else
      old p

theorem installHardStage_at_controller
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (old : ShiftedAssignment)
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    (installHardStage old B (B.controller i) : Nat) =
      (controllerResidue (B.controller i) (B.target i) : Nat) := by
  rw [installHardStage]
  simp only [B.controller_mem i, ↓reduceIte]
  exact installedHardStageValue_at_controller B i

theorem installHardStage_of_not_mem
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (old : ShiftedAssignment)
    (B : HardStagePairing h L R H z k X Xnext a)
    (p : Prime)
    (hp :
      p ∉ hardStageControllerAnnulus h L R H k X Xnext) :
    installHardStage old B p = old p := by
  simp [installHardStage, hp]

theorem installHardStage_nonzero_of_mem
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (old : ShiftedAssignment)
    (B : HardStagePairing h L R H z k X Xnext a)
    (p : Prime)
    (hp :
      p ∈ hardStageControllerAnnulus h L R H k X Xnext) :
    (installHardStage old B p : Nat) ≠ 0 := by
  rw [installHardStage]
  simp only [hp, ↓reduceIte]
  exact installedHardStageValue_ne_zero B p

/-- The assignment immediately before each recursive stage. -/
noncomputable def dynamicAssignmentBefore
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (base : ShiftedAssignment) :
    Nat → ShiftedAssignment
  | 0 => base
  | j + 1 =>
      let old :=
        dynamicAssignmentBefore h L R H z scale k
          hcapacity base j
      let a := nonzeroOldPrimeClasses h (z j) old
      let B :=
        hardStagePairingOfCardLe
          h L R H (z j) k
          (scale j) (scale (j + 1)) a
          (hcapacity j a)
      installHardStage old B

/-- The old classes actually used by recursive stage `j`. -/
noncomputable def dynamicOldClasses
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (base : ShiftedAssignment)
    (j : Nat) :
    OldPrimeClasses h (z j) :=
  nonzeroOldPrimeClasses h (z j)
    (dynamicAssignmentBefore h L R H z scale k
      hcapacity base j)

/-- The canonical finite pairing chosen at recursive stage `j`. -/
noncomputable def dynamicHardStage
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (base : ShiftedAssignment)
    (j : Nat) :
    HardStagePairing h L R H (z j) k
      (scale j) (scale (j + 1))
      (dynamicOldClasses h L R H z scale k
        hcapacity base j) :=
  hardStagePairingOfCardLe
    h L R H (z j) k
    (scale j) (scale (j + 1))
    (dynamicOldClasses h L R H z scale k
      hcapacity base j)
    (hcapacity j
      (dynamicOldClasses h L R H z scale k
        hcapacity base j))

/-- Recursive equation: stage `j` is installed to produce the assignment
before stage `j+1`. -/
theorem dynamicAssignmentBefore_succ
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity :
      ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (base : ShiftedAssignment)
    (j : Nat) :
    dynamicAssignmentBefore h L R H z scale k
        hcapacity base (j + 1) =
      installHardStage
        (dynamicAssignmentBefore h L R H z scale k
          hcapacity base j)
        (dynamicHardStage h L R H z scale k
          hcapacity base j) := by
  rfl

end Erdos279
