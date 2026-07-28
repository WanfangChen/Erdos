import Erdos279.NthPrimeAsymptotic
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Infinitude of the two prime pools

Dirichlet's theorem, already available in mathlib, is enough to prove that
the periodic reservoir and complementary prime-target set are infinite.
No prime-counting asymptotic is used here.
-/

namespace Erdos279

/-- Natural values of a finite project-prime set. -/
noncomputable def primeValueFinset
    (H : Finset Prime) : Finset Nat := by
  classical
  exact H.image Subtype.val

@[simp]
theorem mem_primeValueFinset
    {H : Finset Prime} {n : Nat} :
    n ∈ primeValueFinset H ↔
      ∃ p ∈ H, p.1 = n := by
  classical
  simp [primeValueFinset]

private theorem oldControllerPrime_odd
    {h p : Prime} {z : Nat}
    (hh : 3 ≤ h.1)
    (hp : p ∈ oldControllerPrimes h z) :
    Odd p.1 := by
  have hhp : h.1 < p.1 :=
    hub_lt_of_inControllerProgression
      (mem_oldControllerPrimes.mp hp).1
  exact p.natPrime.odd_of_ne_two (by omega)

private theorem primeSubsetModulus_old_odd
    (h : Prime) (hh : 3 ≤ h.1)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    Odd (primeSubsetModulus H) := by
  classical
  induction H using Finset.induction_on with
  | empty =>
      simp [primeSubsetModulus]
  | @insert p H hpH ih =>
      have hpGt : h.1 < p.1 :=
        hub_lt_of_inControllerProgression
          (hH p (Finset.mem_insert_self p H))
      have hpOdd : Odd p.1 :=
        p.natPrime.odd_of_ne_two (by omega)
      have hHtail :
          ∀ q ∈ H, InControllerProgression h q := by
        intro q hq
        exact hH q (Finset.mem_insert_of_mem hq)
      rw [primeSubsetModulus,
        Finset.prod_insert hpH]
      exact hpOdd.mul (ih hHtail)

/-- Every mesh selects at least one auxiliary residue class. -/
theorem OldControllerPrimeDensityMesh.classes_nonempty
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    M.classes.Nonempty := by
  have hTau : 0 < M.periodicDensity :=
    M.periodicDensity_pos hh hk
  have hIndex : 0 < M.index := by
    by_contra hnot
    have hzero : M.index = 0 :=
      Nat.eq_zero_of_not_pos hnot
    simp [OldControllerPrimeDensityMesh.periodicDensity,
      hzero] at hTau
  exact Finset.card_pos.mp
    (by simpa [M.card_classes] using hIndex)

/-- The selected periodic reservoir is infinite. -/
theorem infinite_periodicReservoir
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    Set.Infinite
      (setOf
        (primeNatPredicate
          (InPeriodicReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff)))) := by
  classical
  obtain ⟨c, hc⟩ := M.classes_nonempty hh hk
  have hcRed : c ∈ reducedResidues M.modulus :=
    M.classes_reduced hc
  have hcop : h.1.Coprime M.modulus.1 :=
    M.hub_coprime_modulus
  let a := periodicCrtClass h M.modulus hcop c
  let Q := h.1 * M.modulus.1
  have hQ : Q ≠ 0 := by
    dsimp [Q]
    exact Nat.mul_ne_zero
      h.natPrime.ne_zero M.modulus.natPrime.ne_zero
  have haCoprime : a.Coprime Q := by
    dsimp [a, Q]
    exact periodicCrtClass_coprime_modulus
      h M.modulus hcop hcRed
  have hDir :
      Set.Infinite
        {n : Nat | n.Prime ∧ n ≡ a [MOD Q]} :=
    Nat.infinite_setOf_prime_and_modEq hQ haCoprime
  have hDiff :
      Set.Infinite
        ({n : Nat | n.Prime ∧ n ≡ a [MOD Q]} \
          (primeValueFinset
            (oldControllerPrimes h M.cutoff) : Set Nat)) :=
    hDir.diff
      (primeValueFinset
        (oldControllerPrimes h M.cutoff)).finite_toSet
  apply hDiff.mono
  intro n hn
  rcases hn with ⟨⟨hnPrime, hnMod⟩, hnOld⟩
  have hnIsPrime : IsPrime n :=
    (isPrime_iff_natPrime n).2 hnPrime
  let p : Prime := ⟨n, hnIsPrime⟩
  have hpPool :
      InPeriodicPrimePool
        h M.modulus M.classes p := by
    apply
      (inPeriodicPrimePool_iff_exists_modEq
        h M.modulus hcop M.classes
        M.classes_reduced p).2
    exact ⟨c, hc, hnMod⟩
  have hpNotOld :
      p ∉ oldControllerPrimes h M.cutoff := by
    intro hpOld
    apply hnOld
    exact mem_primeValueFinset.mpr
      ⟨p, hpOld, rfl⟩
  exact ⟨hnIsPrime, ⟨hpPool, hpNotOld⟩⟩

/-- The complementary prime-target set is infinite.  The uniform residue
`2` modulo `h ∏H` avoids every residue-one class because all moduli are
odd. -/
theorem infinite_complementaryPrimeTargets
    (h : Prime) (hh : 3 ≤ h.1)
    (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    Set.Infinite
      (setOf
        (primeNatPredicate
          (IsComplementaryPrimeTarget h H))) := by
  let Q := h.1 * primeSubsetModulus H
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Nat.mul_pos h.pos
      (primeSubsetModulus_pos H)
  have hhOdd : Odd h.1 :=
    h.natPrime.odd_of_ne_two (by omega)
  have hprodOdd : Odd (primeSubsetModulus H) :=
    primeSubsetModulus_old_odd h hh H hH
  have hQOdd : Odd Q := by
    dsimp [Q]
    exact hhOdd.mul hprodOdd
  have htwoCoprime : Nat.Coprime 2 Q :=
    hQOdd.coprime_two_left
  have hDir :
      Set.Infinite
        {n : Nat | n.Prime ∧ n ≡ 2 [MOD Q]} :=
    Nat.infinite_setOf_prime_and_modEq
      hQpos.ne' htwoCoprime
  apply hDir.mono
  intro n hn
  rcases hn with ⟨hnPrime, hnMod⟩
  have hnIsPrime : IsPrime n :=
    (isPrime_iff_natPrime n).2 hnPrime
  let p : Prime := ⟨n, hnIsPrime⟩
  have hmodHub : n ≡ 2 [MOD h.1] := by
    dsimp [Q] at hnMod
    exact hnMod.of_mul_right
      (primeSubsetModulus H)
  have hpNotG : ¬ InControllerProgression h p := by
    intro hpG
    have htwoLt : 2 < h.1 := by omega
    have hmodTwo : n % h.1 = 2 := by
      simpa [Nat.ModEq,
        Nat.mod_eq_of_lt htwoLt] using hmodHub
    unfold InControllerProgression at hpG
    change n % h.1 = 1 at hpG
    omega
  have hmodOld :
      n ≡ 2 [MOD primeSubsetModulus H] := by
    dsimp [Q] at hnMod
    exact hnMod.of_mul_left h.1
  have hpNotOld :
      ∀ ℓ ∈ H, n % ℓ.1 ≠ 1 := by
    intro ℓ hℓ
    have hℓG := hH ℓ hℓ
    have hℓGt : h.1 < ℓ.1 :=
      hub_lt_of_inControllerProgression hℓG
    have hmodℓ :
        n ≡ 2 [MOD ℓ.1] :=
      (modEq_primeSubsetModulus_iff
        n 2 H).1 hmodOld ℓ hℓ
    have hmodTwo : n % ℓ.1 = 2 := by
      simpa [Nat.ModEq,
        Nat.mod_eq_of_lt (by omega : 2 < ℓ.1)] using hmodℓ
    omega
  exact ⟨hnIsPrime, ⟨hpNotG, hpNotOld⟩⟩

/-- In particular, both infinite-set fields in `MeshNthPrimeInputs` follow
from the already formalized mesh and mathlib's Dirichlet theorem. -/
theorem mesh_primePools_infinite
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    Set.Infinite
        (setOf
          (primeNatPredicate
            (InPeriodicReservoir
              h M.modulus M.classes
              (oldControllerPrimes h M.cutoff)))) ∧
      Set.Infinite
        (setOf
          (primeNatPredicate
            (IsComplementaryPrimeTarget h
              (oldControllerPrimes h M.cutoff)))) := by
  constructor
  · exact infinite_periodicReservoir M hh hk
  · exact
      infinite_complementaryPrimeTargets h hh
        (oldControllerPrimes h M.cutoff)
        (fun p hp =>
          (mem_oldControllerPrimes.mp hp).1)

/-- After Dirichlet infinitude has been discharged, the only prime-pool
inputs still needed are the two quantitative nth-prime asymptotics. -/
structure MeshNthPrimeAsymptoticInputs
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hh : 3 ≤ h.1) (hk : 0 < k) where
  periodic_asymptotic :
    HasNthPrimeAsymptotic
      (InPeriodicReservoir
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff))
      (infinite_periodicReservoir M hh hk)
      M.periodicDensity
  complementary_asymptotic :
    HasNthPrimeAsymptotic
      (IsComplementaryPrimeTarget h
        (oldControllerPrimes h M.cutoff))
      (infinite_complementaryPrimeTargets h hh
        (oldControllerPrimes h M.cutoff)
        (fun p hp =>
          (mem_oldControllerPrimes.mp hp).1))
      (controllerComplementDensity h
        (oldControllerPrimes h M.cutoff))

namespace MeshNthPrimeAsymptoticInputs

/-- Quantitative asymptotics plus the formalized Dirichlet theorem give the
full nth-prime input object used by the matching layer. -/
noncomputable def toMeshNthPrimeInputs
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {hh : 3 ≤ h.1} {hk : 0 < k}
    (A : MeshNthPrimeAsymptoticInputs M hh hk) :
    MeshNthPrimeInputs M where
  periodic_infinite :=
    infinite_periodicReservoir M hh hk
  complementary_infinite :=
    infinite_complementaryPrimeTargets h hh
      (oldControllerPrimes h M.cutoff)
      (fun p hp =>
        (mem_oldControllerPrimes.mp hp).1)
  periodic_asymptotic :=
    A.periodic_asymptotic
  complementary_asymptotic :=
    A.complementary_asymptotic

end MeshNthPrimeAsymptoticInputs

end Erdos279
