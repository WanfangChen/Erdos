import Erdos279.ControllerIndicatorProperties
import Erdos279.DeterministicOldPrimeSieve

/-!
# Finite Mertens products and exact cancellation of `K_h`

The asymptotic Mertens theorem is not used in this file.  We define the
finite products from (2.8) and prove the exact identity

`K_h(z) V_h(z) = (∏_{p≤z} (1-1/p))^δ`.

Consequently the `h`-dependent Euler-product constant cancels algebraically
before any limiting argument, exactly as asserted in (2.19)--(2.20).
-/

namespace Erdos279

open Finset

/-- All project primes at most `z`. -/
noncomputable def allPrimesUpTo (z : Nat) : Finset Prime := by
  classical
  exact (Finset.range (z + 1)).subtype IsPrime

@[simp]
theorem mem_allPrimesUpTo
    {p : Prime} {z : Nat} :
    p ∈ allPrimesUpTo z ↔ p.1 ≤ z := by
  classical
  simp [allPrimesUpTo, Nat.lt_succ_iff]

/-- Ordinary finite Mertens product over all primes at most `z`. -/
noncomputable def ordinaryMertensProduct (z : Nat) : Real :=
  ∏ p ∈ allPrimesUpTo z, (1 - ((p.1 : Real)⁻¹))

/-- The finite controller-prime sieve product `V_h(z)`. -/
noncomputable def controllerMertensProduct
    (h : Prime) (z : Nat) : Real :=
  ∏ p ∈ oldControllerPrimes h z, (1 - ((p.1 : Real)⁻¹))

/--
The partial Euler-product constant from (2.8), written as the equivalent
quotient `M(z)^δ / V_h(z)`.
-/
noncomputable def partialControllerEulerConstant
    (h : Prime) (z : Nat) : Real :=
  ordinaryMertensProduct z ^ controllerDensity h /
    controllerMertensProduct h z

/-- Every individual prime Mertens factor is positive. -/
theorem primeMertensFactor_pos (p : Prime) :
    (0 : Real) < 1 - ((p.1 : Real)⁻¹) := by
  rw [sub_pos]
  apply inv_lt_one_of_one_lt₀
  exact_mod_cast p.one_lt

/-- The ordinary finite Mertens product is positive. -/
theorem ordinaryMertensProduct_pos (z : Nat) :
    0 < ordinaryMertensProduct z := by
  rw [ordinaryMertensProduct]
  exact Finset.prod_pos fun p _hp => primeMertensFactor_pos p

/-- The controller finite Mertens product is positive. -/
theorem controllerMertensProduct_pos
    (h : Prime) (z : Nat) :
    0 < controllerMertensProduct h z := by
  rw [controllerMertensProduct]
  exact Finset.prod_pos fun p _hp => primeMertensFactor_pos p

/-- The partial Euler constant is positive. -/
theorem partialControllerEulerConstant_pos
    (h : Prime) (z : Nat) :
    0 < partialControllerEulerConstant h z := by
  rw [partialControllerEulerConstant]
  exact div_pos
    (Real.rpow_pos_of_pos (ordinaryMertensProduct_pos z) _)
    (controllerMertensProduct_pos h z)

/-- Exact finite form of equation (2.8). -/
theorem partialEulerConstant_mul_controllerProduct
    (h : Prime) (z : Nat) :
    partialControllerEulerConstant h z *
        controllerMertensProduct h z =
      ordinaryMertensProduct z ^ controllerDensity h := by
  rw [partialControllerEulerConstant]
  exact div_mul_cancel₀ _
    (controllerMertensProduct_pos h z).ne'

/--
Exact finite cancellation of the `h`-dependent Euler constant in the
Selberg--Delange coefficient times the sieve product.
-/
theorem partialEulerConstant_gamma_cancellation
    (h : Prime) (z : Nat) :
    (partialControllerEulerConstant h z /
        Real.Gamma (controllerDensity h)) *
        controllerMertensProduct h z =
      ordinaryMertensProduct z ^ controllerDensity h /
        Real.Gamma (controllerDensity h) := by
  calc
    (partialControllerEulerConstant h z /
        Real.Gamma (controllerDensity h)) *
        controllerMertensProduct h z =
      (partialControllerEulerConstant h z *
        controllerMertensProduct h z) /
          Real.Gamma (controllerDensity h) := by ring
    _ = ordinaryMertensProduct z ^ controllerDensity h /
          Real.Gamma (controllerDensity h) := by
      rw [partialEulerConstant_mul_controllerProduct]

/-- Controller primes up to `z` form a subset of all primes up to `z`. -/
theorem oldControllerPrimes_subset_allPrimesUpTo
    (h : Prime) (z : Nat) :
    oldControllerPrimes h z ⊆ allPrimesUpTo z := by
  intro p hp
  exact mem_allPrimesUpTo.mpr
    (mem_oldControllerPrimes.mp hp).2

end Erdos279
