import Erdos279.HardStagePairing

/-!
# A single assignment for all hard-target stages

The stage annuli are disjoint, so all finite pairings can be combined into
one injective dependent family.  This file constructs the resulting global
assignment and proves that it records every prescribed residue without
changing any coordinate outside the complementary reservoir `S`.
-/

namespace Erdos279

/-- The dependent type of all survivor indices across every stage. -/
def HardScheduleIndex
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (scale : Nat → Nat) :=
  Σ j : Nat,
    Fin (hardSurvivors h z a
      (scale j) (scale (j + 1))).card

/-- Collision-free hard-stage pairings at all scales. -/
structure HardPairingSchedule
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z k : Nat) (a : OldPrimeClasses h z)
    (scale : Nat → Nat) where
  stage :
    ∀ j,
      HardStagePairing h L R H z k
        (scale j) (scale (j + 1)) a
  controller_injective :
    Function.Injective fun
      s : HardScheduleIndex h z a scale =>
        (stage s.1).controller s.2

namespace HardPairingSchedule

/-- Build a schedule from the finite capacity inequality at every stage and
pairwise disjointness of the corresponding annuli. -/
noncomputable def ofCardLe
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z k : Nat) (a : OldPrimeClasses h z)
    (scale : Nat → Nat)
    (hcapacity :
      ∀ j,
        (hardSurvivors h z a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (hdisjoint :
      ∀ i j, i ≠ j →
        Disjoint
          (hardStageControllerAnnulus h L R H k
            (scale i) (scale (i + 1)))
          (hardStageControllerAnnulus h L R H k
            (scale j) (scale (j + 1)))) :
    HardPairingSchedule h L R H z k a scale := by
  let stage :
      ∀ j,
        HardStagePairing h L R H z k
          (scale j) (scale (j + 1)) a :=
    fun j =>
      hardStagePairingOfCardLe
        h L R H z k (scale j) (scale (j + 1)) a
        (hcapacity j)
  exact
    { stage := stage
      controller_injective := by
        rintro ⟨i, ii⟩ ⟨j, jj⟩ hij
        by_cases heq : i = j
        · subst j
          have hijIndex :
              ii = jj :=
            (stage i).controller_injective hij
          subst jj
          rfl
        · have hiMem := (stage i).controller_mem ii
          have hjMem := (stage j).controller_mem jj
          change
            (stage i).controller ii =
              (stage j).controller jj at hij
          have hjMem' :
              (stage i).controller ii ∈
                hardStageControllerAnnulus h L R H k
                  (scale j) (scale (j + 1)) := by
            rw [hij]
            exact hjMem
          have hd := Finset.disjoint_left.mp
            (hdisjoint i j heq)
          exact False.elim
            (hd hiMem hjMem') }

/-- The controller used by one dependent schedule index. -/
def controller
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (s : HardScheduleIndex h z a scale) : Prime :=
  (S.stage s.1).controller s.2

/-- The hard target paired with one dependent schedule index. -/
def target
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (s : HardScheduleIndex h z a scale) : Nat :=
  (S.stage s.1).target s.2

/-- The one global assignment obtained by installing every hard-stage
pairing over a base assignment. -/
noncomputable def assignment
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p =>
    if hex :
        ∃ s : HardScheduleIndex h z a scale,
          S.controller s = p then
      ⟨S.target (Classical.choose hex) % p.1,
        Nat.mod_lt _ p.pos⟩
    else
      base p

/-- The global assignment records exactly the residue prescribed at every
stage controller. -/
theorem assignment_at_controller
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (base : ShiftedAssignment)
    (s : HardScheduleIndex h z a scale) :
    (S.assignment base (S.controller s) : Nat) =
      (controllerResidue (S.controller s) (S.target s) : Nat) := by
  let hex :
      ∃ t : HardScheduleIndex h z a scale,
        S.controller t = S.controller s :=
    ⟨s, rfl⟩
  rw [assignment]
  simp only [dif_pos hex]
  have hchosen :
      S.controller (Classical.choose hex) =
        S.controller s :=
    Classical.choose_spec hex
  have hindex :
      Classical.choose hex = s :=
    S.controller_injective hchosen
  rw [hindex]
  rfl

/-- Coordinates not used by the schedule retain their base value. -/
theorem assignment_of_unmatched
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp :
      ∀ s : HardScheduleIndex h z a scale,
        S.controller s ≠ p) :
    S.assignment base p = base p := by
  have hnone :
      ¬ ∃ s : HardScheduleIndex h z a scale,
        S.controller s = p := by
    intro hex
    obtain ⟨s, hs⟩ := hex
    exact hp s hs
  rw [assignment]
  simp only [dif_neg hnone]

/-- Every schedule controller lies in the concrete complementary reservoir
`S`. -/
theorem controller_in_reservoir
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (s : HardScheduleIndex h z a scale) :
    InControllerReservoir h L R H (S.controller s) := by
  exact
    (mem_hardStageControllerAnnulus.mp
      ((S.stage s.1).controller_mem s.2)).2.2

/-- Hence every coordinate outside `S` is permanently unchanged. -/
theorem assignment_of_not_in_reservoir
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    S.assignment base p = base p := by
  apply S.assignment_of_unmatched
  intro s hs
  apply hp
  rw [← hs]
  exact S.controller_in_reservoir s

/-- The global schedule assignment covers every paired hard survivor. -/
theorem assignment_covers
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {z k : Nat} {a : OldPrimeClasses h z}
    {scale : Nat → Nat}
    (S : HardPairingSchedule h L R H z k a scale)
    (hk : 0 < k)
    (base : ShiftedAssignment)
    (s : HardScheduleIndex h z a scale) :
    ShiftedMatureCovers k (S.target s)
      (S.assignment base) := by
  exact
    (S.stage s.1).assignment_covers
      hk (S.assignment base)
      (fun i =>
        S.assignment_at_controller base ⟨s.1, i⟩)
      s.2

end HardPairingSchedule

end Erdos279
