import Erdos279.SieveCRT

/-!
# Arithmetic properties of sieve moduli

This file proves the reduced-residue properties in equations (2.2)--(2.3).
For every subset of old controller primes, its product belongs to the
controller semigroup, the combined translated class is coprime to that
product, and its CRT lift with the hub is coprime to the full modulus `d*h`.
-/

namespace Erdos279

open Finset

/-- A product of old controller primes belongs to the controller semigroup. -/
theorem primeSubsetModulus_mem_controllerSemigroup
    {h : Prime} {z : Nat} {d : Finset Prime}
    (hd : d ⊆ oldControllerPrimes h z) :
    ControllerSemigroup h (primeSubsetModulus d) := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      simpa [primeSubsetModulus] using
        (ControllerSemigroup.one : ControllerSemigroup h 1)
  | @insert p d hpd ih =>
      have hpold : p ∈ oldControllerPrimes h z :=
        hd (Finset.mem_insert_self p d)
      have hdold : d ⊆ oldControllerPrimes h z := by
        intro q hq
        exact hd (Finset.mem_insert_of_mem hq)
      have hpG : InControllerProgression h p :=
        (mem_oldControllerPrimes.mp hpold).1
      have hpsem : ControllerSemigroup h p.1 := by
        simpa using
          (ControllerSemigroup.mul p hpG
            (ControllerSemigroup.one : ControllerSemigroup h 1))
      have hdsem := ih hdold
      simpa [primeSubsetModulus, Finset.prod_insert hpd] using
        hpsem.mul_closed hdsem

/-- The combined translated class is reduced modulo the prime product. -/
theorem translatedSubsetClass_coprime_modulus
    {h : Prime} {z e : Nat}
    (a : OldPrimeClasses h z)
    {d : Finset Prime}
    (hd : d ⊆ oldControllerPrimes h z) :
    (translatedSubsetClass e a d).Coprime
      (primeSubsetModulus d) := by
  classical
  rw [primeSubsetModulus, Nat.coprime_prod_right_iff]
  intro p hp
  rw [Nat.coprime_comm, p.natPrime.coprime_iff_not_dvd]
  intro hpdiv
  have hpold : p ∈ oldControllerPrimes h z := hd hp
  have hpG : InControllerProgression h p :=
    (mem_oldControllerPrimes.mp hpold).1
  have hpz : p.1 ≤ z :=
    (mem_oldControllerPrimes.mp hpold).2
  have htranslated :
      (translatedPrimeClass h p e (a.residue p) : Nat) ≠ 0 :=
    translatedPrimeClass_ne_zero e (a.residue p) hpG
      (a.nonzero p hpG hpz)
  have hmod := translatedSubsetClass_modEq (e := e) a hp
  change
    translatedSubsetClass e a d % p.1 =
      (translatedPrimeClass h p e (a.residue p) : Nat) % p.1 at hmod
  have hleft : translatedSubsetClass e a d % p.1 = 0 :=
    Nat.mod_eq_zero_of_dvd hpdiv
  have hright :
      (translatedPrimeClass h p e (a.residue p) : Nat) % p.1 =
        (translatedPrimeClass h p e (a.residue p) : Nat) :=
    Nat.mod_eq_of_lt
      (translatedPrimeClass h p e (a.residue p)).isLt
  apply htranslated
  omega

/--
The lifted class in equation (2.3): it keeps the translated class modulo the
prime product and is `1` modulo the hub.
-/
noncomputable def translatedLiftedClass
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z)
    (d : Finset Prime)
    (hd : d ⊆ oldControllerPrimes h z) : Nat :=
  translatedCrtLift h
    (primeSubsetModulus d)
    (translatedSubsetClass e a d)
    (primeSubsetModulus_mem_controllerSemigroup hd)

theorem translatedLiftedClass_modEq_modulus
    {h : Prime} {z e : Nat}
    (a : OldPrimeClasses h z)
    {d : Finset Prime}
    (hd : d ⊆ oldControllerPrimes h z) :
    translatedLiftedClass e a d hd ≡
      translatedSubsetClass e a d
        [MOD primeSubsetModulus d] := by
  exact translatedCrtLift_modEq_d h
    (primeSubsetModulus d)
    (translatedSubsetClass e a d)
    (primeSubsetModulus_mem_controllerSemigroup hd)

theorem translatedLiftedClass_modEq_hub
    {h : Prime} {z e : Nat}
    (a : OldPrimeClasses h z)
    {d : Finset Prime}
    (hd : d ⊆ oldControllerPrimes h z) :
    translatedLiftedClass e a d hd ≡ 1 [MOD h.1] := by
  exact translatedCrtLift_modEq_h h
    (primeSubsetModulus d)
    (translatedSubsetClass e a d)
    (primeSubsetModulus_mem_controllerSemigroup hd)

theorem translatedLiftedClass_coprime_fullModulus
    {h : Prime} {z e : Nat}
    (a : OldPrimeClasses h z)
    {d : Finset Prime}
    (hd : d ⊆ oldControllerPrimes h z) :
    (translatedLiftedClass e a d hd).Coprime
      (primeSubsetModulus d * h.1) := by
  exact translatedCrtLift_coprime_mul h
    (primeSubsetModulus d)
    (translatedSubsetClass e a d)
    (primeSubsetModulus_mem_controllerSemigroup hd)
    (translatedSubsetClass_coprime_modulus a hd)

theorem translatedLiftedClass_lt_fullModulus
    {h : Prime} {z e : Nat}
    (a : OldPrimeClasses h z)
    {d : Finset Prime}
    (hd : d ⊆ oldControllerPrimes h z) :
    translatedLiftedClass e a d hd <
      primeSubsetModulus d * h.1 := by
  exact translatedCrtLift_lt h
    (primeSubsetModulus d)
    (translatedSubsetClass e a d)
    (primeSubsetModulus_mem_controllerSemigroup hd)

/-- Replacing the translated class by its hub lift does not change `A_d`. -/
theorem controllerProgressionMass_lifted
    {h : Prime} {z e : Nat}
    (a : OldPrimeClasses h z)
    {d : Finset Prime}
    (hd : d ⊆ oldControllerPrimes h z)
    (Y Z : Nat) :
    controllerProgressionMass h
        (primeSubsetModulus d)
        (translatedLiftedClass e a d hd) Y Z =
      controllerProgressionMass h
        (primeSubsetModulus d)
        (translatedSubsetClass e a d) Y Z := by
  have hmod :=
    translatedLiftedClass_modEq_modulus (e := e) a hd
  change
    translatedLiftedClass e a d hd % primeSubsetModulus d =
      translatedSubsetClass e a d % primeSubsetModulus d at hmod
  simp [controllerProgressionMass, hmod]

end Erdos279
