import Mathlib.Data.Nat.Factorization.Basic
import Erdos279.AnalyticDefinitions

/-!
# Canonical decomposition of hard targets

For a fixed hub prime `h`, every positive hard target has a unique
decomposition

`m = h ^ e * u`

where `e ≥ 1` and `u` belongs to the controller semigroup.  The exponent is
the `h`-adic valuation supplied by `Nat.factorization`, and the cofactor is
mathlib's `Nat.ordCompl`.

This removes an otherwise implicit uniqueness assertion from the layer
decomposition used in equations (2.23)--(2.24) of the paper.
-/

namespace Erdos279

/-- The canonical exponent of the hub prime in `m`. -/
def hardExponent (h : Prime) (m : Nat) : Nat :=
  m.factorization h.1

/-- The canonical factor of `m` left after removing every copy of the hub. -/
def hardCofactor (h : Prime) (m : Nat) : Nat :=
  ordCompl[h.1] m

/-- The canonical exponent and cofactor always multiply back to `m`. -/
theorem hard_pow_mul_cofactor (h : Prime) (m : Nat) :
    h.1 ^ hardExponent h m * hardCofactor h m = m := by
  simpa [hardExponent, hardCofactor] using
    Nat.ordProj_mul_ordCompl_eq_self m h.1

/-- The canonical cofactor divides the original number. -/
theorem hardCofactor_dvd (h : Prime) (m : Nat) :
    hardCofactor h m ∣ m := by
  simpa [hardCofactor] using Nat.ordCompl_dvd m h.1

/-- A nonzero number's canonical cofactor is not divisible by the hub. -/
theorem hub_not_dvd_hardCofactor
    (h : Prime) {m : Nat} (hm : m ≠ 0) :
    ¬h.1 ∣ hardCofactor h m := by
  simpa [hardCofactor] using Nat.not_dvd_ordCompl h.natPrime hm

/-- A nonzero number's canonical cofactor is positive. -/
theorem hardCofactor_pos
    (h : Prime) {m : Nat} (hm : m ≠ 0) :
    0 < hardCofactor h m := by
  simpa [hardCofactor] using Nat.ordCompl_pos h.1 hm

/--
In any decomposition with a controller-semigroup cofactor, the displayed
exponent is the canonical exponent.
-/
theorem hardExponent_eq_of_decomposition
    {h : Prime} {m e u : Nat}
    (hm : m = h.1 ^ e * u)
    (hu : ControllerSemigroup h u) :
    hardExponent h m = e := by
  have hhne : h.1 ^ e ≠ 0 :=
    (Nat.pow_pos h.pos).ne'
  have hune : u ≠ 0 := hu.pos.ne'
  have hnot : ¬h.1 ∣ u := by
    rw [← h.natPrime.coprime_iff_not_dvd]
    exact hu.coprime_hub.symm
  rw [hardExponent, hm, Nat.factorization_mul hhne hune]
  change (h.1 ^ e).factorization h.1 + u.factorization h.1 = e
  rw [Nat.factorization_pow_self h.natPrime,
    Nat.factorization_eq_zero_of_not_dvd hnot]
  omega

/--
In any decomposition with a controller-semigroup cofactor, the displayed
cofactor is the canonical cofactor.
-/
theorem hardCofactor_eq_of_decomposition
    {h : Prime} {m e u : Nat}
    (hm : m = h.1 ^ e * u)
    (hu : ControllerSemigroup h u) :
    hardCofactor h m = u := by
  have he : hardExponent h m = e :=
    hardExponent_eq_of_decomposition hm hu
  have hcanonical :
      h.1 ^ e * hardCofactor h m = h.1 ^ e * u := by
    calc
      h.1 ^ e * hardCofactor h m =
          h.1 ^ hardExponent h m * hardCofactor h m := by rw [he]
      _ = m := hard_pow_mul_cofactor h m
      _ = h.1 ^ e * u := hm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos h.pos) hcanonical

/-- A hard form has positive canonical exponent. -/
theorem HasHardForm.one_le_hardExponent
    {h : Prime} {m : Nat}
    (hm : HasHardForm h m) :
    1 ≤ hardExponent h m := by
  rcases hm with ⟨e, u, he, hu, hdecomp⟩
  simpa [hardExponent_eq_of_decomposition hdecomp hu] using he

/-- The canonical cofactor of a hard form lies in the controller semigroup. -/
theorem HasHardForm.hardCofactor_mem
    {h : Prime} {m : Nat}
    (hm : HasHardForm h m) :
    ControllerSemigroup h (hardCofactor h m) := by
  rcases hm with ⟨e, u, _he, hu, hdecomp⟩
  simpa [hardCofactor_eq_of_decomposition hdecomp hu] using hu

/-- Every hard form is equal to its canonical hard decomposition. -/
theorem HasHardForm.canonical_decomposition
    {h : Prime} {m : Nat}
    (_hm : HasHardForm h m) :
    m = h.1 ^ hardExponent h m * hardCofactor h m :=
  (hard_pow_mul_cofactor h m).symm

/--
The canonical exponent and cofactor provide a hard form exactly when the
exponent is positive and the cofactor belongs to the controller semigroup.
-/
theorem hasHardForm_iff_canonical
    {h : Prime} {m : Nat} :
    HasHardForm h m ↔
      1 ≤ hardExponent h m ∧
      ControllerSemigroup h (hardCofactor h m) := by
  constructor
  · intro hm
    exact ⟨hm.one_le_hardExponent, hm.hardCofactor_mem⟩
  · rintro ⟨he, hu⟩
    exact ⟨hardExponent h m, hardCofactor h m, he, hu,
      (hard_pow_mul_cofactor h m).symm⟩

/--
Uniqueness of the hard-layer coordinates.  This is the injectivity needed to
sum disjoint layer counts without overcounting.
-/
theorem hard_decomposition_unique
    {h : Prime} {e₁ e₂ u₁ u₂ : Nat}
    (hu₁ : ControllerSemigroup h u₁)
    (hu₂ : ControllerSemigroup h u₂)
    (heq : h.1 ^ e₁ * u₁ = h.1 ^ e₂ * u₂) :
    e₁ = e₂ ∧ u₁ = u₂ := by
  let m := h.1 ^ e₁ * u₁
  have hm₁ : m = h.1 ^ e₁ * u₁ := rfl
  have hm₂ : m = h.1 ^ e₂ * u₂ := by
    exact heq
  have he₁ : hardExponent h m = e₁ :=
    hardExponent_eq_of_decomposition hm₁ hu₁
  have he₂ : hardExponent h m = e₂ :=
    hardExponent_eq_of_decomposition hm₂ hu₂
  have hu₁' : hardCofactor h m = u₁ :=
    hardCofactor_eq_of_decomposition hm₁ hu₁
  have hu₂' : hardCofactor h m = u₂ :=
    hardCofactor_eq_of_decomposition hm₂ hu₂
  exact ⟨he₁.symm.trans he₂, hu₁'.symm.trans hu₂'⟩

end Erdos279
