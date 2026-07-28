import Erdos279.MathlibPrelude
import Erdos279.SmoothHard

/-!
# Arithmetic objects for the deterministic old-prime sieve

This file introduces the exact arithmetic function and finite sums used in
Section 2 of the paper.  It contains only algebraic and finite-combinatorial
facts; no asymptotic estimate is assumed.
-/

namespace Erdos279

open Finset

namespace ControllerSemigroup

/-- The product of two controller-semigroup elements is again in the semigroup. -/
theorem mul_closed
    {h : Prime} {u v : Nat}
    (hu : ControllerSemigroup h u)
    (hv : ControllerSemigroup h v) :
    ControllerSemigroup h (u * v) := by
  induction hu with
  | one =>
      simpa using hv
  | mul p hp hu ih =>
      rw [Nat.mul_assoc]
      exact ControllerSemigroup.mul p hp ih

/--
Every positive divisor of a controller-semigroup element belongs to the
controller semigroup.  This is the divisor-closed form of the fact that all
prime factors lie in the progression `1 mod h`.
-/
theorem of_dvd
    {h : Prime} {u v : Nat}
    (hv : ControllerSemigroup h v)
    (huv : u ∣ v) :
    ControllerSemigroup h u := by
  have hupos : 0 < u := by
    by_contra h
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos h
    subst u
    have hv0 : v = 0 := zero_dvd_iff.mp huv
    subst v
    exact (Nat.not_lt_zero 0) hv.pos
  have husmooth : SmoothFor h u := by
    intro q hqu
    right
    exact hv.primeDivisor_mem (Nat.dvd_trans hqu huv)
  have hnotHub : ¬ h.1 ∣ u := by
    intro hhu
    have hhv : h.1 ∣ v := Nat.dvd_trans hhu huv
    have hvmod : v % h.1 = 0 := Nat.mod_eq_zero_of_dvd hhv
    have hvone : v % h.1 = 1 := hv.mod_h_eq_one
    omega
  exact smoothFor_controllerSemigroup_of_not_dvd husmooth hnotHub

/-- Membership in the controller semigroup is exactly multiplicative. -/
theorem mul_iff
    {h : Prime} {u v : Nat} :
    ControllerSemigroup h (u * v) ↔
      ControllerSemigroup h u ∧ ControllerSemigroup h v := by
  constructor
  · intro huv
    constructor
    · exact huv.of_dvd ⟨v, rfl⟩
    · exact huv.of_dvd ⟨u, Nat.mul_comm u v⟩
  · rintro ⟨hu, hv⟩
    exact hu.mul_closed hv

/--
Every controller-semigroup element is coprime to the hub prime.  Indeed its
residue modulo the hub is `1`, whereas a multiple of the hub has residue `0`.
-/
theorem coprime_hub
    {h : Prime} {u : Nat}
    (hu : ControllerSemigroup h u) :
    u.Coprime h.1 := by
  rw [Nat.coprime_comm, h.natPrime.coprime_iff_not_dvd]
  intro hdiv
  have hzero : u % h.1 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hone : u % h.1 = 1 := hu.mod_h_eq_one
  omega

end ControllerSemigroup

/--
The `{0,1}`-valued arithmetic function
`f(u) = 1_{u ∈ ⟨G⟩}` from Section 2.
-/
noncomputable def controllerIndicator (h : Prime) : ArithmeticFunction Nat :=
  by
    classical
    refine ⟨fun u => if ControllerSemigroup h u then 1 else 0, ?_⟩
    change (if ControllerSemigroup h 0 then 1 else 0) = 0
    rw [if_neg]
    intro hu
    exact (Nat.not_lt_zero 0) hu.pos

@[simp]
theorem controllerIndicator_apply_of_mem
    {h : Prime} {u : Nat}
    (hu : ControllerSemigroup h u) :
    controllerIndicator h u = 1 := by
  classical
  simp [controllerIndicator, hu]

@[simp]
theorem controllerIndicator_apply_of_not_mem
    {h : Prime} {u : Nat}
    (hu : ¬ ControllerSemigroup h u) :
    controllerIndicator h u = 0 := by
  classical
  simp [controllerIndicator, hu]

@[simp]
theorem controllerIndicator_eq_one_iff
    {h : Prime} {u : Nat} :
    controllerIndicator h u = 1 ↔ ControllerSemigroup h u := by
  classical
  simp [controllerIndicator]

@[simp]
theorem controllerIndicator_eq_zero_iff
    {h : Prime} {u : Nat} :
    controllerIndicator h u = 0 ↔ ¬ ControllerSemigroup h u := by
  classical
  simp [controllerIndicator]

/-- The paper's indicator is completely multiplicative, not merely multiplicative. -/
theorem controllerIndicator_mul
    (h : Prime) (u v : Nat) :
    controllerIndicator h (u * v) =
      controllerIndicator h u * controllerIndicator h v := by
  classical
  by_cases hu : ControllerSemigroup h u <;>
    by_cases hv : ControllerSemigroup h v <;>
      simp [controllerIndicator, hu, hv, ControllerSemigroup.mul_iff]

/-- The indicator, packaged as a mathlib multiplicative arithmetic function. -/
theorem controllerIndicator_isMultiplicative
    (h : Prime) :
    ArithmeticFunction.IsMultiplicative (controllerIndicator h) := by
  constructor
  · simp [controllerIndicator, ControllerSemigroup.one]
  · intro u v _huv
    exact controllerIndicator_mul h u v

/-- Multiplication by an element of `⟨G⟩` leaves the indicator unchanged. -/
theorem controllerIndicator_mul_left_of_mem
    {h : Prime} {r u : Nat}
    (hr : ControllerSemigroup h r) :
    controllerIndicator h (r * u) = controllerIndicator h u := by
  rw [controllerIndicator_mul]
  simp [controllerIndicator_eq_one_iff.mpr hr]

/-- The natural-number interval corresponding to `(Y,Z]`. -/
def natIoc (Y Z : Nat) : Finset Nat :=
  Finset.Ioc Y Z

/-- `F((Y,Z])`, the total controller-semigroup mass in `(Y,Z]`. -/
noncomputable def controllerMass (h : Prime) (Y Z : Nat) : Nat :=
  ∑ u ∈ natIoc Y Z, controllerIndicator h u

/-- `F_d((Y,Z])`, with the additional coprimality restriction `(u,d)=1`. -/
noncomputable def controllerCoprimeMass (h : Prime) (d Y Z : Nat) : Nat :=
  ∑ u ∈ natIoc Y Z with u.Coprime d, controllerIndicator h u

/-- `A_d((Y,Z],b)`, restricted to one residue class modulo `d`. -/
noncomputable def controllerProgressionMass
    (h : Prime) (d b Y Z : Nat) : Nat :=
  ∑ u ∈ natIoc Y Z with u % d = b % d, controllerIndicator h u

/--
An arbitrary correlated vector of old residue classes.  Values outside the
old controller-prime range are present only to avoid a partial function; the
nonzero condition is imposed exactly where Proposition 2.1 needs it.
-/
structure OldPrimeClasses (h : Prime) (z : Nat) where
  residue : (p : Prime) → Fin p.1
  nonzero :
    ∀ p : Prime, InControllerProgression h p → p.1 ≤ z →
      (residue p : Nat) ≠ 0

/-- A number avoids every assigned nonzero class on controller primes up to `z`. -/
def AvoidsOldClasses
    {h : Prime} {z : Nat}
    (a : OldPrimeClasses h z) (m : Nat) : Prop :=
  ∀ p : Prime,
    InControllerProgression h p →
    p.1 ≤ z →
    m % p.1 ≠ (a.residue p : Nat)

/-- The finite survivor set in one natural-number scale interval. -/
noncomputable def hardSurvivors
    (h : Prime) (z : Nat)
    (a : OldPrimeClasses h z)
    (X Z : Nat) : Finset Nat := by
  classical
  exact (natIoc X Z).filter fun m =>
    HasHardForm h m ∧ AvoidsOldClasses a m

@[simp]
theorem mem_hardSurvivors
    {h : Prime} {z : Nat}
    {a : OldPrimeClasses h z}
    {X Z m : Nat} :
    m ∈ hardSurvivors h z a X Z ↔
      X < m ∧ m ≤ Z ∧
      HasHardForm h m ∧ AvoidsOldClasses a m := by
  classical
  simp [hardSurvivors, natIoc, and_assoc]

end Erdos279
