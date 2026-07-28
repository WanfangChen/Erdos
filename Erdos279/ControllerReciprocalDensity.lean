import Erdos279.HubCapacity
import Erdos279.MertensProducts
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Reciprocal divergence and the finite exceptional-prime density

This file isolates the exact consequence of reciprocal divergence used in
§3.1: a finite set of controller primes can make the complementary Euler
product, and hence `Δ_H`, arbitrarily small.
-/

namespace Erdos279

open Finset Filter

/-- Partial reciprocal sum over controller primes at most `z`. -/
noncomputable def controllerPrimeReciprocalSum
    (h : Prime) (z : Nat) : Real :=
  ∑ p ∈ oldControllerPrimes h z, 1 / (p.1 : Real)

/-- The precise reciprocal-divergence statement needed in §3.1. -/
def ControllerPrimeReciprocalDiverges
    (h : Prime) : Prop :=
  Tendsto (controllerPrimeReciprocalSum h) atTop atTop

/-- The Euler product contributed by a finite set of controller primes. -/
noncomputable def controllerExclusionProduct
    (H : Finset Prime) : Real :=
  ∏ p ∈ H, (1 - 1 / ((p.1 : Real) - 1))

/-- The complementary prime density `Δ_H` in (3.3). -/
noncomputable def controllerComplementDensity
    (h : Prime) (H : Finset Prime) : Real :=
  (1 - 1 / ((h.1 : Real) - 1)) *
    controllerExclusionProduct H

/-- Generic finite comparison
`∏(1-x_i) ≤ exp(-∑x_i)` for `0 ≤ x_i ≤ 1`. -/
theorem prod_one_sub_le_exp_neg_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → Real)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) :
    (∏ i ∈ s, (1 - x i)) ≤
      Real.exp (-(∑ i ∈ s, x i)) := by
  calc
    (∏ i ∈ s, (1 - x i)) ≤
        ∏ i ∈ s, Real.exp (-x i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact sub_nonneg.mpr (hx1 i hi)
      · intro i _hi
        exact Real.one_sub_le_exp_neg (x i)
    _ = Real.exp (∑ i ∈ s, -x i) := by
      exact (Real.exp_sum s (fun i => -x i)).symm
    _ = Real.exp (-(∑ i ∈ s, x i)) := by
      rw [Finset.sum_neg_distrib]

/-- Controller-prime exclusion factors are in `[0,1]`. -/
theorem controllerExclusionFactor_mem_unitInterval
    {h p : Prime} (hh : 3 ≤ h.1)
    (hp : InControllerProgression h p) :
    (0 : Real) ≤ 1 - 1 / ((p.1 : Real) - 1) ∧
      1 - 1 / ((p.1 : Real) - 1) ≤ 1 := by
  have hhp : h.1 < p.1 :=
    hub_lt_of_inControllerProgression hp
  have hpLowerR : (4 : Real) ≤ (p.1 : Real) := by
    exact_mod_cast (by omega : 4 ≤ p.1)
  have hpden : (1 : Real) ≤ (p.1 : Real) - 1 := by
    linarith
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_one (by linarith)).mpr hpden
  · have hinv : 0 ≤ 1 / ((p.1 : Real) - 1) := by
      positivity
    linarith

/-- The exclusion product is bounded by the exponential of the reciprocal
sum with denominators `p-1`. -/
theorem controllerExclusionProduct_le_exp
    (h : Prime) (hh : 3 ≤ h.1)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    controllerExclusionProduct H ≤
      Real.exp
        (-(∑ p ∈ H, 1 / ((p.1 : Real) - 1))) := by
  unfold controllerExclusionProduct
  apply prod_one_sub_le_exp_neg_sum
  · intro p hp
    have hhp :=
      hub_lt_of_inControllerProgression (hH p hp)
    have hpLowerR : (4 : Real) ≤ (p.1 : Real) := by
      exact_mod_cast (by omega : 4 ≤ p.1)
    exact (one_div_pos.mpr (by linarith)).le
  · intro p hp
    have hmem :=
      controllerExclusionFactor_mem_unitInterval
        hh (hH p hp)
    linarith [hmem.1]

/-- Replacing `p-1` by `p` only enlarges the exponential upper bound. -/
theorem controllerExclusionProduct_le_exp_reciprocal
    (h : Prime) (hh : 3 ≤ h.1)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    controllerExclusionProduct H ≤
      Real.exp (-(∑ p ∈ H, 1 / (p.1 : Real))) := by
  refine
    (controllerExclusionProduct_le_exp h hh H hH).trans ?_
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro p hp
  have hpPos : (0 : Real) < (p.1 : Real) - 1 := by
    have hhp := hub_lt_of_inControllerProgression (hH p hp)
    have hpLowerR : (4 : Real) ≤ (p.1 : Real) := by
      exact_mod_cast (by omega : 4 ≤ p.1)
    linarith
  apply one_div_le_one_div_of_le hpPos
  norm_num

/-- The hub factor in `Δ_H` lies in `[0,1]`. -/
theorem hubComplementFactor_mem_unitInterval
    (h : Prime) (hh : 3 ≤ h.1) :
    (0 : Real) ≤ 1 - 1 / ((h.1 : Real) - 1) ∧
      1 - 1 / ((h.1 : Real) - 1) ≤ 1 := by
  have hden : (1 : Real) ≤ (h.1 : Real) - 1 := by
    have hhR : (3 : Real) ≤ (h.1 : Real) := by
      exact_mod_cast hh
    linarith
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_one (by linarith)).mpr hden
  · have : 0 ≤ 1 / ((h.1 : Real) - 1) := by positivity
    linarith

/-- `Δ_H` is nonnegative. -/
theorem controllerComplementDensity_nonneg
    (h : Prime) (hh : 3 ≤ h.1)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    0 ≤ controllerComplementDensity h H := by
  unfold controllerComplementDensity
  apply mul_nonneg
  · exact (hubComplementFactor_mem_unitInterval h hh).1
  · unfold controllerExclusionProduct
    apply Finset.prod_nonneg
    intro p hp
    exact
      (controllerExclusionFactor_mem_unitInterval
        hh (hH p hp)).1

/--
Reciprocal divergence produces a finite initial set `H` with arbitrarily
small complementary density.
-/
theorem exists_oldControllerPrimes_complementDensity_lt
    (h : Prime) (hh : 3 ≤ h.1)
    (hdiv : ControllerPrimeReciprocalDiverges h)
    {ε : Real} (hε : 0 < ε) :
    ∃ z : Nat,
      controllerComplementDensity h
        (oldControllerPrimes h z) < ε := by
  let B : Real := -Real.log ε + 1
  have hevent :
      ∀ᶠ z in atTop,
        B ≤ controllerPrimeReciprocalSum h z :=
    tendsto_atTop.1 hdiv B
  obtain ⟨z, hz⟩ := hevent.exists
  have hH :
      ∀ p ∈ oldControllerPrimes h z,
        InControllerProgression h p := by
    intro p hp
    exact (mem_oldControllerPrimes.mp hp).1
  have hprod :
      controllerExclusionProduct
          (oldControllerPrimes h z) <
        ε := by
    have hupper :=
      controllerExclusionProduct_le_exp_reciprocal
        h hh (oldControllerPrimes h z) hH
    have hsum :
        B ≤
          ∑ p ∈ oldControllerPrimes h z,
            1 / (p.1 : Real) := by
      simpa [controllerPrimeReciprocalSum] using hz
    have hexp :
        Real.exp
            (-(∑ p ∈ oldControllerPrimes h z,
              1 / (p.1 : Real))) < ε := by
      have harg :
          -(∑ p ∈ oldControllerPrimes h z,
              1 / (p.1 : Real)) <
            Real.log ε := by
        dsimp [B] at hsum
        linarith
      have :=
        Real.exp_lt_exp.mpr harg
      simpa [Real.exp_log hε] using this
    exact hupper.trans_lt hexp
  refine ⟨z, ?_⟩
  unfold controllerComplementDensity
  have hhub :=
    hubComplementFactor_mem_unitInterval h hh
  have hprodNonneg :
      0 ≤ controllerExclusionProduct
        (oldControllerPrimes h z) := by
    unfold controllerExclusionProduct
    apply Finset.prod_nonneg
    intro p hp
    exact
      (controllerExclusionFactor_mem_unitInterval
        hh (hH p hp)).1
  exact
    (mul_le_of_le_one_left hprodNonneg hhub.2).trans_lt hprod

end Erdos279
