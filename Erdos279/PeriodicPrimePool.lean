import Erdos279.DensityMesh
import Mathlib.Data.Nat.ChineseRemainder

/-!
# The periodic prime pool

This file formalizes the CRT algebra behind (3.5).  A reduced class `c`
modulo the auxiliary prime `L`, together with the controller condition
`p ≡ 1 (mod h)`, is a single reduced class modulo `hL`.
-/

namespace Erdos279

/-- The canonical representative of the simultaneous classes
`1 mod h` and `c mod L`. -/
noncomputable def periodicCrtClass
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (c : Nat) : Nat :=
  (Nat.chineseRemainder hcop 1 c).1

theorem periodicCrtClass_modEq_h
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (c : Nat) :
    periodicCrtClass h L hcop c ≡ 1 [MOD h.1] := by
  simpa [periodicCrtClass] using
    (Nat.chineseRemainder hcop 1 c).2.1

theorem periodicCrtClass_modEq_aux
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (c : Nat) :
    periodicCrtClass h L hcop c ≡ c [MOD L.1] := by
  simpa [periodicCrtClass] using
    (Nat.chineseRemainder hcop 1 c).2.2

theorem periodicCrtClass_lt
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (c : Nat) :
    periodicCrtClass h L hcop c < h.1 * L.1 := by
  exact
    Nat.chineseRemainder_lt_mul hcop 1 c
      h.natPrime.ne_zero L.natPrime.ne_zero

/-- The CRT class is reduced modulo the hub. -/
theorem periodicCrtClass_coprime_h
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (c : Nat) :
    (periodicCrtClass h L hcop c).Coprime h.1 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd (periodicCrtClass h L hcop c) h.1 =
        Nat.gcd h.1 (periodicCrtClass h L hcop c) :=
      Nat.gcd_comm _ _
    _ =
        Nat.gcd
          ((periodicCrtClass h L hcop c) % h.1)
          h.1 :=
      Nat.gcd_rec h.1
        (periodicCrtClass h L hcop c)
    _ = Nat.gcd (1 % h.1) h.1 := by
      rw [periodicCrtClass_modEq_h]
    _ = Nat.gcd 1 h.1 := by
      rw [Nat.mod_eq_of_lt h.one_lt]
    _ = 1 := Nat.gcd_one_left h.1

/-- A selected reduced auxiliary class remains reduced after CRT lifting. -/
theorem periodicCrtClass_coprime_aux
    (h L : Prime) (hcop : h.1.Coprime L.1)
    {c : Nat} (hc : c ∈ reducedResidues L) :
    (periodicCrtClass h L hcop c).Coprime L.1 := by
  have hcCoprime : c.Coprime L.1 :=
    (mem_reducedResidues.mp hc).2.symm
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd (periodicCrtClass h L hcop c) L.1 =
        Nat.gcd L.1 (periodicCrtClass h L hcop c) :=
      Nat.gcd_comm _ _
    _ =
        Nat.gcd
          ((periodicCrtClass h L hcop c) % L.1)
          L.1 :=
      Nat.gcd_rec L.1
        (periodicCrtClass h L hcop c)
    _ = Nat.gcd (c % L.1) L.1 := by
      rw [periodicCrtClass_modEq_aux]
    _ = Nat.gcd L.1 c := (Nat.gcd_rec L.1 c).symm
    _ = Nat.gcd c L.1 := Nat.gcd_comm _ _
    _ = 1 := hcCoprime.gcd_eq_one

/-- Hence every selected CRT class is reduced modulo `hL`, as required by
the fixed-progression prime number theorem. -/
theorem periodicCrtClass_coprime_modulus
    (h L : Prime) (hcop : h.1.Coprime L.1)
    {c : Nat} (hc : c ∈ reducedResidues L) :
    (periodicCrtClass h L hcop c).Coprime
      (h.1 * L.1) := by
  exact Nat.coprime_mul_iff_right.mpr
    ⟨periodicCrtClass_coprime_h h L hcop c,
      periodicCrtClass_coprime_aux h L hcop hc⟩

/-- Membership in one paired progression is exactly membership in its
single CRT class. -/
theorem modEq_periodicCrtClass_iff
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (c n : Nat) :
    n ≡ periodicCrtClass h L hcop c
        [MOD h.1 * L.1] ↔
      n ≡ 1 [MOD h.1] ∧ n ≡ c [MOD L.1] := by
  constructor
  · intro hn
    constructor
    · exact
        (hn.of_mul_right L.1).trans
          (periodicCrtClass_modEq_h h L hcop c)
    · exact
        (hn.of_mul_left h.1).trans
          (periodicCrtClass_modEq_aux h L hcop c)
  · rintro ⟨hnh, hnL⟩
    exact
      Nat.chineseRemainder_modEq_unique
        hcop hnh hnL

/-- The periodic set `T₀`: controller primes whose auxiliary residue lies
in the selected reduced-class set. -/
def InPeriodicPrimePool
    (h L : Prime) (R : Finset Nat)
    (p : Prime) : Prop :=
  InControllerProgression h p ∧
    p.1 % L.1 ∈ R

/-- The eventual reservoir `T = T₀ \ H`. -/
def InPeriodicReservoir
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (p : Prime) : Prop :=
  InPeriodicPrimePool h L R p ∧ p ∉ H

/-- The complementary controller-prime pool
`S = G \ (H ∪ T)`. -/
def InControllerReservoir
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (p : Prime) : Prop :=
  InControllerProgression h p ∧
    p ∉ H ∧
    ¬ InPeriodicPrimePool h L R p

/-- A periodic-pool prime lies in one of the single reduced CRT classes,
and conversely.  This is the exact finite-union formulation of (3.5). -/
theorem inPeriodicPrimePool_iff_exists_modEq
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L)
    (p : Prime) :
    InPeriodicPrimePool h L R p ↔
      ∃ c ∈ R,
        p.1 ≡ periodicCrtClass h L hcop c
          [MOD h.1 * L.1] := by
  constructor
  · rintro ⟨hph, hpR⟩
    refine ⟨p.1 % L.1, hpR, ?_⟩
    apply (modEq_periodicCrtClass_iff h L hcop _ _).2
    constructor
    · simpa [InControllerProgression, Nat.ModEq,
        Nat.mod_eq_of_lt h.one_lt] using hph
    · simp [Nat.ModEq]
  · rintro ⟨c, hcR, hpc⟩
    have hcRed : c ∈ reducedResidues L := hR hcR
    have hcLt : c < L.1 := (mem_reducedResidues.mp hcRed).1
    have hpair :=
      (modEq_periodicCrtClass_iff h L hcop c p.1).1 hpc
    constructor
    · simpa [InControllerProgression, Nat.ModEq,
        Nat.mod_eq_of_lt h.one_lt] using hpair.1
    · have hmod : p.1 % L.1 = c := by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hcLt] using hpair.2
      simpa [hmod] using hcR

/-- Removing the finite old-prime set does not change the controller
condition or the selected auxiliary residue condition. -/
theorem inPeriodicReservoir_iff
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (p : Prime) :
    InPeriodicReservoir h L R H p ↔
      InControllerProgression h p ∧
        p ∉ H ∧ p.1 % L.1 ∈ R := by
  constructor
  · rintro ⟨⟨hpG, hpR⟩, hpH⟩
    exact ⟨hpG, hpH, hpR⟩
  · rintro ⟨hpG, hpH, hpR⟩
    exact ⟨⟨hpG, hpR⟩, hpH⟩

/-- The complementary reservoir is the part of the controller progression
outside both the old-prime set and the selected periodic pool. -/
theorem inControllerReservoir_iff
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (p : Prime) :
    InControllerReservoir h L R H p ↔
      InControllerProgression h p ∧
        p ∉ H ∧ p.1 % L.1 ∉ R := by
  constructor
  · rintro ⟨hpG, hpH, hpNotT⟩
    refine ⟨hpG, hpH, ?_⟩
    intro hpR
    exact hpNotT ⟨hpG, hpR⟩
  · rintro ⟨hpG, hpH, hpR⟩
    refine ⟨hpG, hpH, ?_⟩
    rintro ⟨_hpG, hpInR⟩
    exact hpR hpInR

/-- The two reservoirs partition exactly the controller primes outside
the finite old-prime set. -/
theorem inPeriodic_or_inControllerReservoir_iff
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (p : Prime) :
    InPeriodicReservoir h L R H p ∨
        InControllerReservoir h L R H p ↔
      InControllerProgression h p ∧ p ∉ H := by
  constructor
  · rintro (hpT | hpS)
    · have hp :=
        (inPeriodicReservoir_iff h L R H p).1 hpT
      exact ⟨hp.1, hp.2.1⟩
    · have hp :=
        (inControllerReservoir_iff h L R H p).1 hpS
      exact ⟨hp.1, hp.2.1⟩
  · rintro ⟨hpG, hpH⟩
    by_cases hpR : p.1 % L.1 ∈ R
    · left
      exact (inPeriodicReservoir_iff h L R H p).2
        ⟨hpG, hpH, hpR⟩
    · right
      exact (inControllerReservoir_iff h L R H p).2
        ⟨hpG, hpH, hpR⟩

/-- The periodic and complementary reservoirs are disjoint. -/
theorem not_inPeriodic_and_inControllerReservoir
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (p : Prime) :
    ¬ (InPeriodicReservoir h L R H p ∧
        InControllerReservoir h L R H p) := by
  rintro ⟨hpT, hpS⟩
  have hpR :=
    ((inPeriodicReservoir_iff h L R H p).1 hpT).2.2
  have hpNotR :=
    ((inControllerReservoir_iff h L R H p).1 hpS).2.2
  exact hpNotR hpR

/-- Every periodic-reservoir prime is a controller prime. -/
theorem InPeriodicReservoir.inControllerProgression
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {p : Prime}
    (hp : InPeriodicReservoir h L R H p) :
    InControllerProgression h p :=
  (inPeriodicReservoir_iff h L R H p).1 hp |>.1

/-- Every complementary-reservoir prime is a controller prime. -/
theorem InControllerReservoir.inControllerProgression
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {p : Prime}
    (hp : InControllerReservoir h L R H p) :
    InControllerProgression h p :=
  (inControllerReservoir_iff h L R H p).1 hp |>.1

/-- The periodic reservoir has had all old primes removed. -/
theorem InPeriodicReservoir.not_mem_old
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {p : Prime}
    (hp : InPeriodicReservoir h L R H p) :
    p ∉ H :=
  (inPeriodicReservoir_iff h L R H p).1 hp |>.2.1

/-- The complementary reservoir has had all old primes removed. -/
theorem InControllerReservoir.not_mem_old
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {p : Prime}
    (hp : InControllerReservoir h L R H p) :
    p ∉ H :=
  (inControllerReservoir_iff h L R H p).1 hp |>.2.1

/-- The auxiliary modulus supplied by the density mesh is coprime to the
hub modulus. -/
theorem OldControllerPrimeDensityMesh.hub_coprime_modulus
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    h.1.Coprime M.modulus.1 := by
  have hLh : M.modulus.1.Coprime h.1 :=
    (Nat.coprime_mul_iff_right.mp M.coprime).1
  exact hLh.symm

/-- The auxiliary modulus is coprime to each old controller prime, not
merely to their product. -/
theorem OldControllerPrimeDensityMesh.modulus_coprime_oldPrime
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    {p : Prime}
    (hp : p ∈ oldControllerPrimes h M.cutoff) :
    M.modulus.1.Coprime p.1 := by
  have hprod :
      M.modulus.1.Coprime
        (primeSubsetModulus
          (oldControllerPrimes h M.cutoff)) :=
    (Nat.coprime_mul_iff_right.mp M.coprime).2
  apply Nat.Coprime.of_dvd_right _ hprod
  simpa [primeSubsetModulus] using
    Finset.dvd_prod_of_mem
      (fun q : Prime => q.1) hp

end Erdos279
