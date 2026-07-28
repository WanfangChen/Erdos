import Erdos279.HardLayerCounting

/-!
# Elementary bound for the high-exponent hard tail

Equation (2.24) is elementary: once the canonical hub exponent is at least
`E`, every target is divisible by `h^E`.  Division by that fixed power
injects all such targets at most `Z` into `[1, Z / h^E]`.

The resulting bound is exact and stronger than estimating every short layer
separately.
-/

namespace Erdos279

open Finset

/-- Hard survivors whose canonical hub exponent is at least `E`. -/
noncomputable def hardSurvivorsFromExponent
    (h : Prime) (z E : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) : Finset Nat := by
  classical
  exact (hardSurvivors h z a X Z).filter fun m =>
    E ≤ hardExponent h m

@[simp]
theorem mem_hardSurvivorsFromExponent
    {h : Prime} {z E X Z m : Nat}
    {a : OldPrimeClasses h z} :
    m ∈ hardSurvivorsFromExponent h z E a X Z ↔
      m ∈ hardSurvivors h z a X Z ∧ E ≤ hardExponent h m := by
  classical
  simp [hardSurvivorsFromExponent]

/-- A lower bound on the canonical exponent gives divisibility by that power. -/
theorem hubPow_dvd_of_le_hardExponent
    {h : Prime} {m E : Nat}
    (hm : 0 < m)
    (hE : E ≤ hardExponent h m) :
    h.1 ^ E ∣ m := by
  apply (h.natPrime.pow_dvd_iff_le_factorization hm.ne').mpr
  simpa [hardExponent] using hE

/--
Exact elementary tail bound: there are at most `Z / h^E` hard survivors up
to `Z` whose hub exponent is at least `E`.
-/
theorem hardSurvivorsFromExponent_card_le
    (h : Prime) (z E : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivorsFromExponent h z E a X Z).card ≤
      Z / h.1 ^ E := by
  classical
  let S := hardSurvivorsFromExponent h z E a X Z
  let T := Finset.Icc 1 (Z / h.1 ^ E)
  have hpowpos : 0 < h.1 ^ E := Nat.pow_pos h.pos
  have hmaps :
      Set.MapsTo (fun m : Nat => m / h.1 ^ E) (S : Set Nat) (T : Set Nat) := by
    intro m hm
    have hm' : m ∈ hardSurvivorsFromExponent h z E a X Z := hm
    rcases mem_hardSurvivorsFromExponent.mp hm' with
      ⟨hmSurvivor, hmExponent⟩
    have hmData := mem_hardSurvivors.mp hmSurvivor
    have hmForm : HasHardForm h m := hmData.2.2.1
    have hdiv : h.1 ^ E ∣ m :=
      hubPow_dvd_of_le_hardExponent hmForm.pos hmExponent
    change m / h.1 ^ E ∈ Finset.Icc 1 (Z / h.1 ^ E)
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.div_pos
        (Nat.le_of_dvd hmForm.pos hdiv) hpowpos
    · exact Nat.div_le_div_right hmData.2.1
  have hinj :
      Set.InjOn (fun m : Nat => m / h.1 ^ E) (S : Set Nat) := by
    intro m₁ hm₁ m₂ hm₂ heq
    have hm₁' : m₁ ∈ hardSurvivorsFromExponent h z E a X Z := hm₁
    have hm₂' : m₂ ∈ hardSurvivorsFromExponent h z E a X Z := hm₂
    have hm₁Data := mem_hardSurvivorsFromExponent.mp hm₁'
    have hm₂Data := mem_hardSurvivorsFromExponent.mp hm₂'
    have hm₁Form : HasHardForm h m₁ :=
      (mem_hardSurvivors.mp hm₁Data.1).2.2.1
    have hm₂Form : HasHardForm h m₂ :=
      (mem_hardSurvivors.mp hm₂Data.1).2.2.1
    have hdiv₁ : h.1 ^ E ∣ m₁ :=
      hubPow_dvd_of_le_hardExponent hm₁Form.pos hm₁Data.2
    have hdiv₂ : h.1 ^ E ∣ m₂ :=
      hubPow_dvd_of_le_hardExponent hm₂Form.pos hm₂Data.2
    change m₁ / h.1 ^ E = m₂ / h.1 ^ E at heq
    calc
      m₁ = (m₁ / h.1 ^ E) * h.1 ^ E :=
        (Nat.div_mul_cancel hdiv₁).symm
      _ = (m₂ / h.1 ^ E) * h.1 ^ E := by rw [heq]
      _ = m₂ := Nat.div_mul_cancel hdiv₂
  have hcard : S.card ≤ T.card :=
    Finset.card_le_card_of_injOn
      (fun m : Nat => m / h.1 ^ E) hmaps hinj
  simpa [S, T] using hcard

/--
The fibres with exponents in `[E,Z]` are exactly the survivor tail starting
at `E`, provided `E ≥ 1`.
-/
theorem hardSurvivorsFromExponent_card_eq_sum_layers
    (h : Prime) (z E : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivorsFromExponent h z E a X Z).card =
      ∑ e ∈ Finset.Icc E Z,
        (hardSurvivorLayer h z e a X Z).card := by
  classical
  have hsum :=
    Finset.sum_card_fiberwise_eq_card_filter
      (hardSurvivors h z a X Z)
      (Finset.Icc E Z)
      (hardExponent h)
  have hfilter :
      (hardSurvivors h z a X Z).filter
          (fun m => hardExponent h m ∈ Finset.Icc E Z) =
        hardSurvivorsFromExponent h z E a X Z := by
    ext m
    constructor
    · intro hm
      rcases Finset.mem_filter.mp hm with ⟨hmSurvivor, hmRange⟩
      exact mem_hardSurvivorsFromExponent.mpr
        ⟨hmSurvivor, (Finset.mem_Icc.mp hmRange).1⟩
    · intro hm
      rcases mem_hardSurvivorsFromExponent.mp hm with
        ⟨hmSurvivor, hmLower⟩
      have hmUpper :=
        (Finset.mem_Icc.mp
          (hardExponent_mem_range_of_mem hmSurvivor)).2
      exact Finset.mem_filter.mpr
        ⟨hmSurvivor, Finset.mem_Icc.mpr ⟨hmLower, hmUpper⟩⟩
  rw [hfilter] at hsum
  simpa [hardSurvivorLayer] using hsum.symm

/--
Summed coordinate form of the high-exponent tail bound.  This is the exact
finite estimate used to discard the complementary layers in (2.24).
-/
theorem sum_hardLayerUnits_card_le_tail
    (h : Prime) (z E : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat)
    (hE : 1 ≤ E) :
    (∑ e ∈ Finset.Icc E Z,
      (hardLayerUnits h z e a
        (X / h.1 ^ e) (Z / h.1 ^ e)).card) ≤
      Z / h.1 ^ E := by
  calc
    (∑ e ∈ Finset.Icc E Z,
      (hardLayerUnits h z e a
        (X / h.1 ^ e) (Z / h.1 ^ e)).card) =
        (hardSurvivorsFromExponent h z E a X Z).card := by
      rw [hardSurvivorsFromExponent_card_eq_sum_layers
        h z E a X Z]
      apply Finset.sum_congr rfl
      intro e he
      exact hardLayerUnits_card_eq_survivorLayer
        h z e a X Z (hE.trans (Finset.mem_Icc.mp he).1)
    _ ≤ Z / h.1 ^ E :=
      hardSurvivorsFromExponent_card_le h z E a X Z

end Erdos279
