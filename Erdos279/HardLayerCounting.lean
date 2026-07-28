import Erdos279.HardLayerDecomposition
import Erdos279.DeterministicOldPrimeSieve

/-!
# Exact finite counting by hard layers

This file turns the paper's decomposition `m = h^e u` into an exact
partition of every finite survivor set.  It also identifies each fibre with
the `u`-coordinate set to which the deterministic old-prime sieve applies.

All endpoints use natural-number division, so the statements have no
rounding convention hidden in prose.
-/

namespace Erdos279

open Finset

/-- The fibre of hard survivors whose canonical hub exponent equals `e`. -/
noncomputable def hardSurvivorLayer
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) : Finset Nat := by
  classical
  exact (hardSurvivors h z a X Z).filter fun m =>
    hardExponent h m = e

@[simp]
theorem mem_hardSurvivorLayer
    {h : Prime} {z e X Z m : Nat}
    {a : OldPrimeClasses h z} :
    m ∈ hardSurvivorLayer h z e a X Z ↔
      m ∈ hardSurvivors h z a X Z ∧ hardExponent h m = e := by
  classical
  simp [hardSurvivorLayer]

@[simp]
theorem mem_hardLayerUnits
    {h : Prime} {z e Y Z u : Nat}
    {a : OldPrimeClasses h z} :
    u ∈ hardLayerUnits h z e a Y Z ↔
      Y < u ∧ u ≤ Z ∧
      ControllerSemigroup h u ∧
      AvoidsOldClasses a (h.1 ^ e * u) := by
  classical
  simp [hardLayerUnits, and_assoc]

/-- Exponents needed for hard targets at most `Z`. -/
def hardExponentRange (Z : Nat) : Finset Nat :=
  Finset.Icc 1 Z

/-- Every hard survivor's canonical exponent lies in the finite range. -/
theorem hardExponent_mem_range_of_mem
    {h : Prime} {z X Z m : Nat}
    {a : OldPrimeClasses h z}
    (hm : m ∈ hardSurvivors h z a X Z) :
    hardExponent h m ∈ hardExponentRange Z := by
  have hmData := mem_hardSurvivors.mp hm
  have hmForm : HasHardForm h m := hmData.2.2.1
  have heLower : 1 ≤ hardExponent h m :=
    hmForm.one_le_hardExponent
  have heLt : hardExponent h m < m := by
    simpa [hardExponent] using
      Nat.factorization_lt h.1 hmForm.pos.ne'
  exact Finset.mem_Icc.mpr
    ⟨heLower, (Nat.le_of_lt heLt).trans hmData.2.1⟩

/--
The cardinality of the complete hard survivor set is exactly the sum of the
cardinalities of its canonical exponent fibres.
-/
theorem hardSurvivors_card_eq_sum_layers
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card =
      ∑ e ∈ hardExponentRange Z,
        (hardSurvivorLayer h z e a X Z).card := by
  classical
  have hsum :=
    Finset.sum_card_fiberwise_eq_card_filter
      (hardSurvivors h z a X Z)
      (hardExponentRange Z)
      (hardExponent h)
  have hfilter :
      (hardSurvivors h z a X Z).filter
          (fun m => hardExponent h m ∈ hardExponentRange Z) =
        hardSurvivors h z a X Z := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    exact hardExponent_mem_range_of_mem hm
  rw [hfilter] at hsum
  simpa [hardSurvivorLayer] using hsum.symm

/--
For `e ≥ 1`, multiplication by `h^e` is a bijection from the exact
`u`-interval to the canonical `e`-th hard layer.
-/
theorem hardLayerUnits_card_eq_survivorLayer
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat)
    (he : 1 ≤ e) :
    (hardLayerUnits h z e a
        (X / h.1 ^ e) (Z / h.1 ^ e)).card =
      (hardSurvivorLayer h z e a X Z).card := by
  classical
  have hpowpos : 0 < h.1 ^ e := Nat.pow_pos h.pos
  refine Finset.card_bij'
    (fun u _hu => h.1 ^ e * u)
    (fun m _hm => hardCofactor h m)
    ?_ ?_ ?_ ?_
  · intro u hu
    rcases mem_hardLayerUnits.mp hu with
      ⟨huLower, huUpper, huG, huAvoids⟩
    apply mem_hardSurvivorLayer.mpr
    refine ⟨mem_hardSurvivors.mpr ⟨?_, ?_, ?_, huAvoids⟩, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hpowpos).mp at huLower
      simpa [Nat.mul_comm] using huLower
    · apply (Nat.le_div_iff_mul_le hpowpos).mp at huUpper
      simpa [Nat.mul_comm] using huUpper
    · exact ⟨e, u, he, huG, rfl⟩
    · exact hardExponent_eq_of_decomposition rfl huG
  · intro m hm
    rcases mem_hardSurvivorLayer.mp hm with ⟨hmSurvivor, hmExponent⟩
    rcases mem_hardSurvivors.mp hmSurvivor with
      ⟨hmLower, hmUpper, hmForm, hmAvoids⟩
    have hmDecomp :
        m = h.1 ^ e * hardCofactor h m := by
      simpa [hmExponent] using hmForm.canonical_decomposition
    apply mem_hardLayerUnits.mpr
    refine ⟨?_, ?_, hmForm.hardCofactor_mem, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hpowpos).mpr
      have hproduct :
          X < h.1 ^ e * hardCofactor h m := by
        rw [← hmDecomp]
        exact hmLower
      simpa only [Nat.mul_comm] using hproduct
    · apply (Nat.le_div_iff_mul_le hpowpos).mpr
      have hproduct :
          h.1 ^ e * hardCofactor h m ≤ Z := by
        rw [← hmDecomp]
        exact hmUpper
      simpa only [Nat.mul_comm] using hproduct
    · rw [← hmDecomp]
      exact hmAvoids
  · intro u hu
    have huG := (mem_hardLayerUnits.mp hu).2.2.1
    exact hardCofactor_eq_of_decomposition rfl huG
  · intro m hm
    have hmExponent := (mem_hardSurvivorLayer.mp hm).2
    change h.1 ^ e * hardCofactor h m = m
    calc
      h.1 ^ e * hardCofactor h m =
          h.1 ^ hardExponent h m * hardCofactor h m := by
            rw [hmExponent]
      _ = m := hard_pow_mul_cofactor h m

/--
Exact finite counterpart of the layer summation in (2.23): the total hard
survivor count is the sum of the translated-sieve coordinate counts, with
the natural-number quotient endpoints made explicit.
-/
theorem hardSurvivors_card_eq_sum_layerUnits
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card =
      ∑ e ∈ hardExponentRange Z,
        (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card := by
  rw [hardSurvivors_card_eq_sum_layers]
  apply Finset.sum_congr rfl
  intro e he
  exact (hardLayerUnits_card_eq_survivorLayer
    h z e a X Z (Finset.mem_Icc.mp he).1).symm

end Erdos279
