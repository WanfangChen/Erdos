import Erdos279.HardLayerTail
import Mathlib.Data.Nat.Log

/-!
# Logarithmic truncation of the hard layers

The paper separates the layers `m = h^e u` according to whether
`X / h^e` is at least `sqrt X`.  This file makes that separation exact.
It also gives a completely elementary bound for the complementary layers.

The logarithmic exponent range is important: the older coarse range
`1 ≤ e ≤ Z` is finite but much too large for the normalized tail estimate.
-/

namespace Erdos279

open Finset

/-- Every hard exponent occurring below `Z` lies in this logarithmic range. -/
def hardLogExponentRange (h : Prime) (Z : Nat) : Finset Nat :=
  Finset.Icc 1 (Nat.log h.1 Z)

/-- An exponent in a hard decomposition below `Z` is at most `log_h Z`. -/
theorem hardExponent_le_log_of_mem
    {h : Prime} {z X Z m : Nat}
    {a : OldPrimeClasses h z}
    (hm : m ∈ hardSurvivors h z a X Z) :
    hardExponent h m ≤ Nat.log h.1 Z := by
  have hmData := mem_hardSurvivors.mp hm
  have hmForm : HasHardForm h m := hmData.2.2.1
  have hpowDvd :
      h.1 ^ hardExponent h m ∣ m := by
    refine ⟨hardCofactor h m, ?_⟩
    exact hmForm.canonical_decomposition
  have hpowLeM :
      h.1 ^ hardExponent h m ≤ m :=
    Nat.le_of_dvd hmForm.pos hpowDvd
  exact Nat.le_log_of_pow_le h.one_lt
    (hpowLeM.trans hmData.2.1)

/-- Logarithmic strengthening of `hardExponent_mem_range_of_mem`. -/
theorem hardExponent_mem_logRange_of_mem
    {h : Prime} {z X Z m : Nat}
    {a : OldPrimeClasses h z}
    (hm : m ∈ hardSurvivors h z a X Z) :
    hardExponent h m ∈ hardLogExponentRange h Z := by
  exact Finset.mem_Icc.mpr
    ⟨(mem_hardSurvivors.mp hm).2.2.1.one_le_hardExponent,
      hardExponent_le_log_of_mem hm⟩

/-- Exact layer decomposition over the sharp logarithmic exponent range. -/
theorem hardSurvivors_card_eq_sum_logLayers
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card =
      ∑ e ∈ hardLogExponentRange h Z,
        (hardSurvivorLayer h z e a X Z).card := by
  classical
  have hsum :=
    Finset.sum_card_fiberwise_eq_card_filter
      (hardSurvivors h z a X Z)
      (hardLogExponentRange h Z)
      (hardExponent h)
  have hfilter :
      (hardSurvivors h z a X Z).filter
          (fun m => hardExponent h m ∈ hardLogExponentRange h Z) =
        hardSurvivors h z a X Z := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    exact hardExponent_mem_logRange_of_mem hm
  rw [hfilter] at hsum
  simpa [hardSurvivorLayer] using hsum.symm

/-- Coordinate form of the logarithmically truncated layer decomposition. -/
theorem hardSurvivors_card_eq_sum_logLayerUnits
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card =
      ∑ e ∈ hardLogExponentRange h Z,
        (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card := by
  rw [hardSurvivors_card_eq_sum_logLayers]
  apply Finset.sum_congr rfl
  intro e he
  exact (hardLayerUnits_card_eq_survivorLayer
    h z e a X Z (Finset.mem_Icc.mp he).1).symm

/-- Main layers, whose semigroup-coordinate lower endpoint is at least
`sqrt X`. -/
def hardMainExponentRange
    (h : Prime) (X Z : Nat) : Finset Nat :=
  (hardLogExponentRange h Z).filter fun e =>
    Nat.sqrt X ≤ X / h.1 ^ e

/-- Complementary layers, whose lower endpoint is below `sqrt X`. -/
def hardTailExponentRange
    (h : Prime) (X Z : Nat) : Finset Nat :=
  (hardLogExponentRange h Z).filter fun e =>
    X / h.1 ^ e < Nat.sqrt X

/-- The main and tail exponent ranges partition all possible hard layers. -/
theorem hardSurvivors_card_eq_main_add_tail
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card =
      (∑ e ∈ hardMainExponentRange h X Z,
        (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card) +
      ∑ e ∈ hardTailExponentRange h X Z,
        (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card := by
  classical
  rw [hardSurvivors_card_eq_sum_logLayerUnits]
  simpa only [hardMainExponentRange, hardTailExponentRange, not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (hardLogExponentRange h Z)
      (fun e => Nat.sqrt X ≤ X / h.1 ^ e)
      (fun e =>
        (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card)).symm

/-- A hard layer contains no more elements than its upper interval
endpoint. -/
theorem hardLayerUnits_card_le_upper
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat) :
    (hardLayerUnits h z e a Y Z).card ≤ Z := by
  classical
  have hsubset :
      hardLayerUnits h z e a Y Z ⊆ natIoc Y Z := by
    intro u hu
    exact Finset.mem_Ioc.mpr
      ⟨(mem_hardLayerUnits.mp hu).1,
        (mem_hardLayerUnits.mp hu).2.1⟩
  calc
    (hardLayerUnits h z e a Y Z).card ≤
        (natIoc Y Z).card :=
      Finset.card_le_card hsubset
    _ = Z - Y := by simp [natIoc]
    _ ≤ Z := Nat.sub_le _ _

/-- Each tail layer in `(X,BX]` has at most `B sqrt X` elements. -/
theorem hardTailLayer_card_le
    (h : Prime) (z e B X : Nat)
    (a : OldPrimeClasses h z)
    (hB : 0 < B)
    (heTail : X / h.1 ^ e < Nat.sqrt X) :
    (hardLayerUnits h z e a
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card ≤
        B * Nat.sqrt X := by
  have hpowPos : 0 < h.1 ^ e := Nat.pow_pos h.pos
  have hXlt :
      X < Nat.sqrt X * h.1 ^ e :=
    (Nat.div_lt_iff_lt_mul hpowPos).mp heTail
  have hBXlt :
      B * X < (B * Nat.sqrt X) * h.1 ^ e := by
    calc
      B * X < B * (Nat.sqrt X * h.1 ^ e) :=
        Nat.mul_lt_mul_of_pos_left hXlt hB
      _ = (B * Nat.sqrt X) * h.1 ^ e := by
        ac_rfl
  have hquotient :
      (B * X) / h.1 ^ e < B * Nat.sqrt X :=
    (Nat.div_lt_iff_lt_mul hpowPos).mpr hBXlt
  exact
    (hardLayerUnits_card_le_upper h z e a
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).trans
      hquotient.le

/-- Exact elementary version of the complementary-layer estimate.  The
extra logarithmic factor is harmless for the final `X / log X`
normalization. -/
theorem sum_hardTailLayers_card_le
    (h : Prime) (z B X : Nat)
    (a : OldPrimeClasses h z)
    (hB : 0 < B) :
    (∑ e ∈ hardTailExponentRange h X (B * X),
      (hardLayerUnits h z e a
        (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card) ≤
      (Nat.log h.1 (B * X) + 1) * (B * Nat.sqrt X) := by
  classical
  calc
    (∑ e ∈ hardTailExponentRange h X (B * X),
      (hardLayerUnits h z e a
        (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card) ≤
        ∑ _e ∈ hardTailExponentRange h X (B * X),
          B * Nat.sqrt X := by
      apply Finset.sum_le_sum
      intro e he
      exact hardTailLayer_card_le h z e B X a hB
        (Finset.mem_filter.mp he).2
    _ =
        (hardTailExponentRange h X (B * X)).card *
          (B * Nat.sqrt X) := by
      simp
    _ ≤
        (Nat.log h.1 (B * X) + 1) *
          (B * Nat.sqrt X) := by
      apply Nat.mul_le_mul_right
      have hsubset :
          hardTailExponentRange h X (B * X) ⊆
            hardLogExponentRange h (B * X) := by
        intro e he
        exact (Finset.mem_filter.mp he).1
      calc
        (hardTailExponentRange h X (B * X)).card ≤
            (hardLogExponentRange h (B * X)).card :=
          Finset.card_le_card hsubset
        _ ≤ Nat.log h.1 (B * X) + 1 := by
          simp [hardLogExponentRange]

end Erdos279
