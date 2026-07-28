import Erdos279.GeometricHardSchedule

/-!
# Count-form PNT for the controller reservoir

The cleanup reservoir is the union of the reduced auxiliary residue classes
not selected for the periodic prime-target pool, apart from one possible
exceptional prime equal to the auxiliary modulus.  This file makes that
finite perturbation exact and derives its density from the same fixed
progression PNT used for the periodic pool.
-/

namespace Erdos279

/-- Reduced auxiliary classes not selected by the density mesh. -/
def OldControllerPrimeDensityMesh.remainingClasses
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    Finset Nat :=
  reducedResidues M.modulus \ M.classes

theorem OldControllerPrimeDensityMesh.remainingClasses_subset
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    M.remainingClasses ⊆
      reducedResidues M.modulus :=
  Finset.sdiff_subset

theorem OldControllerPrimeDensityMesh.card_remainingClasses
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    M.remainingClasses.card =
      (M.modulus.1 - 1) - M.index := by
  unfold OldControllerPrimeDensityMesh.remainingClasses
  rw [Finset.card_sdiff_of_subset M.classes_reduced,
    card_reducedResidues, M.card_classes]

/-- Beyond the auxiliary modulus, the complementary reduced-class
reservoir is exactly the controller cleanup reservoir. -/
theorem controllerReservoir_iff_remainingPeriodic_beyond_modulus
    {h L : Prime} {R : Finset Nat}
    (hR : R ⊆ reducedResidues L)
    (H : Finset Prime)
    {n : Nat} (hnLarge : L.1 + 1 ≤ n) :
    primeNatPredicate
        (InControllerReservoir h L R H) n ↔
      primeNatPredicate
        (InPeriodicReservoir h L
          (reducedResidues L \ R) H) n := by
  have hReduced
      (hnPrime : Nat.Prime n) :
      n % L.1 ∈ reducedResidues L := by
    apply mem_reducedResidues.mpr
    have hcop :
        L.1.Coprime n :=
      (Nat.coprime_primes
        L.natPrime hnPrime).2 (by omega)
    have hmodcop :
        L.1.Coprime (n % L.1) := by
      unfold Nat.Coprime at hcop ⊢
      rw [Nat.gcd_comm]
      rw [← Nat.gcd_rec L.1 n]
      exact hcop
    exact
      ⟨Nat.mod_lt n L.pos, hmodcop⟩
  constructor
  · rintro
      ⟨hnPrime, hpG, hpH, hpNotPeriodic⟩
    refine ⟨hnPrime, ⟨?_, hpH⟩⟩
    refine ⟨hpG, Finset.mem_sdiff.mpr
      ⟨hReduced
        ((isPrime_iff_natPrime n).mp hnPrime),
        ?_⟩⟩
    intro hpR
    exact hpNotPeriodic ⟨hpG, hpR⟩
  · rintro
      ⟨hnPrime, ⟨⟨hpG, hpRemaining⟩, hpH⟩⟩
    have hpNotR :
        n % L.1 ∉ R :=
      (Finset.mem_sdiff.mp hpRemaining).2
    refine
      ⟨hnPrime, hpG, hpH, ?_⟩
    rintro ⟨_hpG, hpR⟩
    exact hpNotR hpR

/-- The exact density of the controller cleanup reservoir. -/
noncomputable def OldControllerPrimeDensityMesh.controllerReservoirDensity
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) : Real :=
  controllerDensity h - M.periodicDensity

/-- The finite-class quotient for the remaining classes is the density
`δ - τ` appearing in the paper. -/
theorem OldControllerPrimeDensityMesh.remainingClasses_density
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    (M.remainingClasses.card : Real) /
        (Nat.totient
          (h.1 * M.modulus.1) : Real) =
      M.controllerReservoirDensity := by
  have hindex :
      M.index ≤ M.modulus.1 - 1 := by
    rw [← M.card_classes,
      ← card_reducedResidues M.modulus]
    exact Finset.card_le_card
      M.classes_reduced
  rw [M.card_remainingClasses,
    totient_hub_mul_aux
      h M.modulus M.hub_coprime_modulus]
  rw [Nat.cast_sub hindex]
  unfold
    OldControllerPrimeDensityMesh.controllerReservoirDensity
    OldControllerPrimeDensityMesh.periodicDensity
    controllerDensity
  have hhNe :
      (h.1 : Real) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr
      (by exact_mod_cast
        (Nat.ne_of_gt h.one_lt))
  have hLNe :
      (M.modulus.1 : Real) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr
      (by exact_mod_cast
        (Nat.ne_of_gt M.modulus.one_lt))
  have hhOne : 1 ≤ h.1 := by
    exact h.one_lt.le
  have hLOne : 1 ≤ M.modulus.1 := by
    exact M.modulus.one_lt.le
  rw [Nat.cast_mul,
    Nat.cast_sub hhOne,
    Nat.cast_sub hLOne]
  field_simp [hhNe, hLNe]
  ring

/-- Fixed-progression PNT for the mesh modulus gives the count-form PNT
for the controller cleanup reservoir. -/
theorem mesh_controllerReservoir_countingAsymptotic
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hPNT :
      FixedProgressionPrimeNumberTheorem
        (h.1 * M.modulus.1)) :
    HasProjectPrimeCountingAsymptotic
      (InControllerReservoir
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff))
      M.controllerReservoirDensity := by
  have hRemaining :=
    periodicReservoir_countingAsymptotic
      h M.modulus M.hub_coprime_modulus
      M.remainingClasses
      M.remainingClasses_subset
      (oldControllerPrimes h M.cutoff)
      (M.cutoff + 1)
      (by
        intro p hp
        exact Nat.lt_succ_of_le
          (mem_oldControllerPrimes.mp hp).2)
      hPNT
  unfold HasProjectPrimeCountingAsymptotic
    at hRemaining ⊢
  have hController :
      HasPrimeCountingAsymptotic
        (primeNatPredicate
          (InControllerReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff)))
        ((M.remainingClasses.card : Real) /
          (Nat.totient
            (h.1 * M.modulus.1) : Real)) :=
    HasPrimeCountingAsymptotic.congr_of_eventually_iff
      (P :=
        primeNatPredicate
          (InControllerReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff)))
      (Q :=
        primeNatPredicate
          (InPeriodicReservoir
            h M.modulus M.remainingClasses
            (oldControllerPrimes h M.cutoff)))
      (M.modulus.1 + 1)
      (by
        intro n hn
        exact
          (controllerReservoir_iff_remainingPeriodic_beyond_modulus
            M.classes_reduced
            (oldControllerPrimes h M.cutoff)
            hn))
      hRemaining
  rw [M.remainingClasses_density] at hController
  exact hController

/-- The mesh leaves more than half of the controller-prime density for
cleanup. -/
theorem OldControllerPrimeDensityMesh.controllerReservoirDensity_gt_half
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    controllerDensity h / 2 <
      M.controllerReservoirDensity := by
  have hUpper :
      M.periodicDensity <
        controllerDensity h / 2 := by
    simpa
      [OldControllerPrimeDensityMesh.periodicDensity]
      using M.upper_half
  unfold
    OldControllerPrimeDensityMesh.controllerReservoirDensity
  linarith

end Erdos279
