import Erdos279.ControllerReciprocalDensity
import Erdos279.SieveArithmetic
import Mathlib.Data.Nat.Totient

/-!
# The density window and its auxiliary-prime mesh

This file formalizes the finite discretization in §3.1.  Once reciprocal
divergence has made the old-controller-prime complement density `Δ` small,
there is a real window

`k Δ < τ < h Δ`,  `τ < δ / 2`.

An auxiliary prime `L`, chosen sufficiently large and coprime to the old
modulus, makes the mesh `δ / (L - 1)` fine enough to put a grid point in
that window.  Since `(ZMod L)ˣ` has exactly `L - 1` elements, that grid
point is realized by an actual finite set of reduced residue classes.
-/

namespace Erdos279

open Finset

/-- Every controller-prime exclusion factor is strictly positive. -/
theorem controllerExclusionFactor_pos
    {h p : Prime} (hh : 3 ≤ h.1)
    (hp : InControllerProgression h p) :
    0 < (1 : Real) - 1 / ((p.1 : Real) - 1) := by
  have hhp : h.1 < p.1 :=
    hub_lt_of_inControllerProgression hp
  have hpLower : 4 ≤ p.1 := by omega
  have hpLowerR : (4 : Real) ≤ (p.1 : Real) := by
    exact_mod_cast hpLower
  have hpdenPos : (0 : Real) < (p.1 : Real) - 1 := by
    linarith
  have hpdenOne : (1 : Real) < (p.1 : Real) - 1 := by
    linarith
  exact sub_pos.mpr ((div_lt_one hpdenPos).mpr hpdenOne)

/-- The hub exclusion factor is strictly positive in the paper's range. -/
theorem hubComplementFactor_pos
    (h : Prime) (hh : 3 ≤ h.1) :
    0 < (1 : Real) - 1 / ((h.1 : Real) - 1) := by
  have hhR : (3 : Real) ≤ (h.1 : Real) := by
    exact_mod_cast hh
  have hdenPos : (0 : Real) < (h.1 : Real) - 1 := by
    linarith
  have hdenOne : (1 : Real) < (h.1 : Real) - 1 := by
    linarith
  exact sub_pos.mpr ((div_lt_one hdenPos).mpr hdenOne)

/-- The complementary density `Δ_H` never vanishes for a finite set of
controller primes. -/
theorem controllerComplementDensity_pos
    (h : Prime) (hh : 3 ≤ h.1)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    0 < controllerComplementDensity h H := by
  unfold controllerComplementDensity controllerExclusionProduct
  apply mul_pos (hubComplementFactor_pos h hh)
  exact Finset.prod_pos fun p hp =>
    controllerExclusionFactor_pos hh (hH p hp)

/-- A positive sufficiently small density admits the strict window used in
(3.4).  The midpoint between `k Δ` and `h Δ` is a convenient witness. -/
theorem exists_density_window
    {δ Δ : Real} {k h : Nat}
    (hΔ : 0 < Δ) (hkh : k < h)
    (hsmall : Δ < δ / ((k + h : Nat) : Real)) :
    ∃ τ : Real,
      0 < τ ∧
      (k : Real) * Δ < τ ∧
      τ < (h : Real) * Δ ∧
      τ < δ / 2 := by
  have hkR : (k : Real) < (h : Real) := by
    exact_mod_cast hkh
  have hhpos : 0 < h := lt_of_le_of_lt (Nat.zero_le k) hkh
  have hsumPos : (0 : Real) < (k : Real) + (h : Real) := by
    positivity
  have hsmall' :
      Δ < δ / ((k : Real) + (h : Real)) := by
    simpa [Nat.cast_add] using hsmall
  have hmul :
      Δ * ((k : Real) + (h : Real)) < δ :=
    (lt_div_iff₀ hsumPos).mp hsmall'
  refine ⟨((k : Real) + (h : Real)) * Δ / 2, ?_⟩
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- A mesh finer than an open interval has a positive natural-number grid
point inside the interval. -/
theorem exists_nat_mul_mem_Ioo_of_step_lt
    {a b step : Real}
    (ha : 0 ≤ a) (hstep : 0 < step)
    (hmesh : step < b - a) :
    ∃ m : Nat,
      a < (m : Real) * step ∧
      (m : Real) * step < b := by
  let q : Real := a / step
  let m : Nat := ⌊q⌋₊ + 1
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt : q < (m : Nat) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hfloor_le : ((⌊q⌋₊ : Nat) : Real) ≤ q :=
    Nat.floor_le hq
  have hm_le : (m : Real) ≤ q + 1 := by
    dsimp [m]
    push_cast
    linarith
  have hq_mul : q * step = a := by
    dsimp [q]
    field_simp
  have hlower :
      a < (m : Real) * step := by
    have :=
      mul_lt_mul_of_pos_right hq_lt hstep
    rwa [hq_mul] at this
  have hupperWeak :
      (m : Real) * step ≤ a + step := by
    have :=
      mul_le_mul_of_nonneg_right hm_le hstep.le
    rw [add_mul, hq_mul, one_mul] at this
    exact this
  exact ⟨m, hlower, hupperWeak.trans_lt (by linarith)⟩

/-- A prime larger than a positive modulus is coprime to that modulus. -/
theorem auxiliaryPrime_coprime_of_gt
    (L : Prime) {M : Nat} (hM : 0 < M) (hML : M < L.1) :
    L.1.Coprime M := by
  rw [L.natPrime.coprime_iff_not_dvd]
  intro hdiv
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd hM hdiv)) hML

/-- There is an arbitrarily large auxiliary prime whose density mesh is
finer than a prescribed positive interval. -/
theorem exists_auxiliary_prime_with_fine_mesh
    {δ gap : Real} (_hδ : 0 < δ) (hgap : 0 < gap)
    (avoid : Nat) (havoid : 0 < avoid) :
    ∃ L : Prime,
      max avoid 2 < L.1 ∧
      L.1.Coprime avoid ∧
      δ / ((L.1 : Real) - 1) < gap := by
  obtain ⟨N : Nat, hN⟩ :=
    exists_nat_gt
      (max (max avoid 2 : Real) (δ / gap + 1))
  obtain ⟨p, hpPrime, hNp, _hpmod⟩ :=
    Nat.exists_prime_gt_modEq_one
      (k := 1) N one_ne_zero
  let L : Prime :=
    ⟨p, (isPrime_iff_natPrime p).2 hpPrime⟩
  have hboundN :
      (max avoid 2 : Real) < (N : Real) :=
    (le_max_left _ _).trans_lt hN
  have hratioN :
      δ / gap + 1 < (N : Real) :=
    (le_max_right _ _).trans_lt hN
  have hNpR : (N : Real) < (p : Real) := by
    exact_mod_cast hNp
  have hlarge : max avoid 2 < p := by
    exact_mod_cast hboundN.trans hNpR
  have hratio :
      δ / gap < (p : Real) - 1 := by
    linarith
  have hmul :
      δ < ((p : Real) - 1) * gap := by
    have := (div_lt_iff₀ hgap).mp hratio
    simpa [mul_comm] using this
  have hpden : (0 : Real) < (p : Real) - 1 := by
    have : (2 : Real) < (p : Real) := by
      exact_mod_cast (lt_of_le_of_lt (le_max_right avoid 2) hlarge)
    linarith
  have havoidp : avoid < p :=
    (le_max_left avoid 2).trans_lt hlarge
  have hcoprime : L.1.Coprime avoid :=
    @auxiliaryPrime_coprime_of_gt
      L avoid havoid havoidp
  refine ⟨L, hlarge, hcoprime, ?_⟩
  exact
    (div_lt_iff₀ hpden).mpr
      (by simpa [mul_comm] using hmul)

/-- Reciprocal divergence supplies an old-prime cutoff and a point in the
strict density window. -/
theorem exists_oldControllerPrimes_density_window
    (h : Prime) (hh : 3 ≤ h.1)
    (k : Nat) (hkh : k < h.1)
    (hdiv : ControllerPrimeReciprocalDiverges h) :
    ∃ z : Nat, ∃ τ : Real,
      0 <
        controllerComplementDensity h
          (oldControllerPrimes h z) ∧
      0 < τ ∧
      (k : Real) *
          controllerComplementDensity h
            (oldControllerPrimes h z) < τ ∧
      τ <
          (h.1 : Real) *
            controllerComplementDensity h
              (oldControllerPrimes h z) ∧
      τ < controllerDensity h / 2 := by
  have hsumPosNat : 0 < k + h.1 := by
    omega
  have hsumPosReal :
      (0 : Real) < ((k + h.1 : Nat) : Real) := by
    exact_mod_cast hsumPosNat
  have heps :
      0 <
        controllerDensity h /
          ((k + h.1 : Nat) : Real) :=
    div_pos (controllerDensity_pos h) hsumPosReal
  obtain ⟨z, hzsmall⟩ :=
    exists_oldControllerPrimes_complementDensity_lt
      h hh hdiv heps
  have hH :
      ∀ p ∈ oldControllerPrimes h z,
        InControllerProgression h p := by
    intro p hp
    exact (mem_oldControllerPrimes.mp hp).1
  have hΔ :
      0 <
        controllerComplementDensity h
          (oldControllerPrimes h z) :=
    controllerComplementDensity_pos
      h hh (oldControllerPrimes h z) hH
  obtain ⟨τ, hτpos, hkτ, hτh, hτδ⟩ :=
    exists_density_window hΔ hkh hzsmall
  exact ⟨z, τ, hΔ, hτpos, hkτ, hτh, hτδ⟩

/-- Canonical natural-number representatives of the reduced residue classes
modulo an auxiliary prime. -/
def reducedResidues (L : Prime) : Finset Nat :=
  (Finset.range L.1).filter fun a => L.1.Coprime a

@[simp]
theorem mem_reducedResidues
    {L : Prime} {a : Nat} :
    a ∈ reducedResidues L ↔
      a < L.1 ∧ L.1.Coprime a := by
  simp [reducedResidues]

/-- A prime modulus has exactly `L - 1` reduced residue classes. -/
theorem card_reducedResidues (L : Prime) :
    (reducedResidues L).card = L.1 - 1 := by
  rw [reducedResidues, ← Nat.totient_eq_card_coprime]
  exact Nat.totient_prime L.natPrime

private theorem reducedResidueSubset_exists
    (L : Prime) (m : Nat) (hm : m ≤ L.1 - 1) :
    ∃ R : Finset Nat,
      R ⊆ reducedResidues L ∧ R.card = m := by
  have hm' : m ≤ (reducedResidues L).card := by
    simpa [card_reducedResidues] using hm
  exact Finset.exists_subset_card_eq hm'

/-- A fixed choice of `m` canonical reduced residues. -/
noncomputable def selectedReducedResidues
    (L : Prime) (m : Nat) (hm : m ≤ L.1 - 1) :
    Finset Nat :=
  Classical.choose (reducedResidueSubset_exists L m hm)

theorem selectedReducedResidues_subset
    (L : Prime) (m : Nat) (hm : m ≤ L.1 - 1) :
    selectedReducedResidues L m hm ⊆
      reducedResidues L :=
  (Classical.choose_spec
    (reducedResidueSubset_exists L m hm)).1

theorem selectedReducedResidues_card
    (L : Prime) (m : Nat) (hm : m ≤ L.1 - 1) :
    (selectedReducedResidues L m hm).card = m :=
  (Classical.choose_spec
    (reducedResidueSubset_exists L m hm)).2

/-- Density contributed by a finite set of reduced residue classes modulo
the auxiliary prime. -/
noncomputable def reducedClassDensity
    (δ : Real) (L : Prime)
    (R : Finset Nat) : Real :=
  (R.card : Real) *
    (δ / ((L.1 : Real) - 1))

/-- The density mesh point indexed by `m`. -/
noncomputable def densityMeshPoint
    (δ : Real) (L : Prime) (m : Nat) : Real :=
  (m : Real) * (δ / ((L.1 : Real) - 1))

/-- A set of exactly `m` reduced classes has the `m`-th mesh density. -/
theorem reducedClassDensity_eq_densityMeshPoint
    (δ : Real) (L : Prime) (m : Nat)
    (R : Finset Nat) (hcard : R.card = m) :
    reducedClassDensity δ L R =
      densityMeshPoint δ L m := by
  simp [reducedClassDensity, densityMeshPoint, hcard]

/-- The purely numerical output of the auxiliary-prime mesh argument. -/
structure NumericalDensityMesh
    (δ Δ : Real) (k h avoid : Nat) where
  modulus : Prime
  index : Nat
  large : max avoid 2 < modulus.1
  coprime : modulus.1.Coprime avoid
  index_le : index ≤ modulus.1 - 1
  lower :
    (k : Real) * Δ <
      (index : Real) *
        (δ / ((modulus.1 : Real) - 1))
  upper_hub :
    (index : Real) *
        (δ / ((modulus.1 : Real) - 1)) <
      (h : Real) * Δ
  upper_half :
    (index : Real) *
        (δ / ((modulus.1 : Real) - 1)) <
      δ / 2

theorem numericalDensityMesh_nonempty
    {δ Δ : Real} {k h avoid : Nat}
    (L : Prime) (m : Nat)
    (hlarge : max avoid 2 < L.1)
    (hcoprime : L.1.Coprime avoid)
    (hm : m ≤ L.1 - 1)
    (hlower :
      (k : Real) * Δ <
        (m : Real) *
          (δ / ((L.1 : Real) - 1)))
    (hupper :
      (m : Real) *
          (δ / ((L.1 : Real) - 1)) <
        (h : Real) * Δ)
    (hhalf :
      (m : Real) *
          (δ / ((L.1 : Real) - 1)) <
        δ / 2) :
    Nonempty (NumericalDensityMesh δ Δ k h avoid) :=
  ⟨{
    modulus := L
    index := m
    large := hlarge
    coprime := hcoprime
    index_le := hm
    lower := hlower
    upper_hub := hupper
    upper_half := hhalf
  }⟩

/-- A concrete auxiliary-prime mesh and a set of reduced residue classes
realizing its index. -/
structure ReducedClassDensityMesh
    (δ Δ : Real) (k h avoid : Nat) where
  modulus : Prime
  index : Nat
  classes : Finset Nat
  large : max avoid 2 < modulus.1
  coprime : modulus.1.Coprime avoid
  classes_reduced : classes ⊆ reducedResidues modulus
  card_classes : classes.card = index
  lower :
    (k : Real) * Δ <
      (index : Real) *
        (δ / ((modulus.1 : Real) - 1))
  upper_hub :
    (index : Real) *
        (δ / ((modulus.1 : Real) - 1)) <
      (h : Real) * Δ
  upper_half :
    (index : Real) *
        (δ / ((modulus.1 : Real) - 1)) <
      δ / 2

/--
Every strict density window has a sufficiently fine numerical
auxiliary-prime mesh.
-/
theorem exists_numerical_density_mesh
    {δ Δ τ : Real} {k h : Nat}
    (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hkτ : (k : Real) * Δ < τ)
    (hτh : τ < (h : Real) * Δ)
    (hτδ : τ < δ / 2)
    (avoid : Nat) (havoid : 0 < avoid) :
    Nonempty (NumericalDensityMesh δ Δ k h avoid) := by
  classical
  let a : Real := (k : Real) * Δ
  let b : Real := min ((h : Real) * Δ) (δ / 2)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hτb : τ < b := by
    dsimp [b]
    exact lt_min hτh hτδ
  have hab : a < b := by
    exact hkτ.trans hτb
  have hgap : 0 < b - a := sub_pos.mpr hab
  obtain ⟨L, hLlarge, hLcoprime, hmesh⟩ :=
    exists_auxiliary_prime_with_fine_mesh
      hδ hgap avoid havoid
  have hLtwo : 2 < L.1 :=
    (le_max_right avoid 2).trans_lt hLlarge
  have hden :
      (0 : Real) < (L.1 : Real) - 1 := by
    have hLtwoR : (2 : Real) < (L.1 : Real) := by
      exact_mod_cast hLtwo
    linarith
  let step : Real :=
    δ / ((L.1 : Real) - 1)
  have hstep : 0 < step := by
    dsimp [step]
    exact div_pos hδ hden
  obtain ⟨m, hma, hmb⟩ :=
    exists_nat_mul_mem_Ioo_of_step_lt
      ha hstep hmesh
  dsimp [step, a, b] at hma hmb
  have hbδ : b < δ := by
    calc
      b ≤ δ / 2 := min_le_right _ _
      _ < δ := by linarith
  have hmδ :
      (m : Real) *
          (δ / ((L.1 : Real) - 1)) < δ :=
    hmb.trans hbδ
  have hmdiv :
      (m : Real) * δ /
          ((L.1 : Real) - 1) < δ := by
    simpa [div_eq_mul_inv, mul_assoc] using hmδ
  have hmmul :
      (m : Real) * δ <
        δ * ((L.1 : Real) - 1) := by
    have :=
      (div_lt_iff₀ hden).mp hmdiv
    simpa [mul_comm] using this
  have hmR :
      (m : Real) < (L.1 : Real) - 1 := by
    nlinarith
  have hmSuccR :
      (m : Real) + 1 < (L.1 : Real) := by
    linarith
  have hmSucc : m + 1 < L.1 := by
    exact_mod_cast hmSuccR
  have hmle : m ≤ L.1 - 1 := by
    omega
  have hmbSplit :=
    (lt_min_iff.mp hmb)
  rcases hmbSplit with ⟨hupper, hhalf⟩
  refine
    @numericalDensityMesh_nonempty
      δ Δ k h avoid
      L m hLlarge hLcoprime hmle
      ?_ ?_ ?_
  · exact hma
  · exact hupper
  · assumption

/--
Every strict density window can be realized by an actual set of reduced
residue classes modulo a sufficiently large auxiliary prime.
-/
theorem exists_reducedClasses_in_density_window
    {δ Δ τ : Real} {k h : Nat}
    (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hkτ : (k : Real) * Δ < τ)
    (hτh : τ < (h : Real) * Δ)
    (hτδ : τ < δ / 2)
    (avoid : Nat) (havoid : 0 < avoid) :
    Nonempty (ReducedClassDensityMesh δ Δ k h avoid) := by
  obtain ⟨M⟩ :=
    exists_numerical_density_mesh
      hδ hΔ hkτ hτh hτδ avoid havoid
  exact
    ⟨{
      modulus := M.modulus
      index := M.index
      classes :=
        selectedReducedResidues
          M.modulus M.index M.index_le
      large := M.large
      coprime := M.coprime
      classes_reduced :=
        selectedReducedResidues_subset
          M.modulus M.index M.index_le
      card_classes :=
        selectedReducedResidues_card
          M.modulus M.index M.index_le
      lower := M.lower
      upper_hub := M.upper_hub
      upper_half := M.upper_half
    }⟩

/-- The complete density mesh after selecting the old controller primes. -/
structure OldControllerPrimeDensityMesh
    (h : Prime) (k : Nat) where
  cutoff : Nat
  modulus : Prime
  index : Nat
  classes : Finset Nat
  large :
    max
        (h.1 *
          primeSubsetModulus
            (oldControllerPrimes h cutoff)) 2 <
      modulus.1
  coprime :
    modulus.1.Coprime
      (h.1 *
        primeSubsetModulus
          (oldControllerPrimes h cutoff))
  classes_reduced :
    classes ⊆ reducedResidues modulus
  card_classes : classes.card = index
  lower :
    (k : Real) *
        controllerComplementDensity h
          (oldControllerPrimes h cutoff) <
      (index : Real) *
        (controllerDensity h /
          ((modulus.1 : Real) - 1))
  upper_hub :
    (index : Real) *
        (controllerDensity h /
          ((modulus.1 : Real) - 1)) <
      (h.1 : Real) *
        controllerComplementDensity h
          (oldControllerPrimes h cutoff)
  upper_half :
    (index : Real) *
        (controllerDensity h /
          ((modulus.1 : Real) - 1)) <
      controllerDensity h / 2

/--
The complete density-mesh output used in §3.1.  The auxiliary prime is
automatically coprime to the hub and every old controller prime.
-/
theorem exists_oldControllerPrime_reducedClass_mesh
    (h : Prime) (hh : 3 ≤ h.1)
    (k : Nat) (hkh : k < h.1)
    (hdiv : ControllerPrimeReciprocalDiverges h) :
    Nonempty (OldControllerPrimeDensityMesh h k) := by
  obtain ⟨z, τ, hΔ, _hτpos, hkτ, hτh, hτδ⟩ :=
    exists_oldControllerPrimes_density_window
      h hh k hkh hdiv
  let avoid : Nat :=
    h.1 *
      primeSubsetModulus
        (oldControllerPrimes h z)
  have havoid : 0 < avoid := by
    dsimp [avoid]
    exact
      Nat.mul_pos h.natPrime.pos
        (primeSubsetModulus_pos
          (oldControllerPrimes h z))
  obtain ⟨M⟩ :=
    exists_reducedClasses_in_density_window
      (controllerDensity_pos h) hΔ
      hkτ hτh hτδ avoid havoid
  exact
    ⟨{
      cutoff := z
      modulus := M.modulus
      index := M.index
      classes := M.classes
      large := M.large
      coprime := M.coprime
      classes_reduced := M.classes_reduced
      card_classes := M.card_classes
      lower := M.lower
      upper_hub := M.upper_hub
      upper_half := M.upper_half
    }⟩

end Erdos279
