import Erdos279.FixedProgressionPNT

/-!
# Fixed-progression PNT for complementary prime targets

Complementary prime targets are, apart from finitely many primes dividing
the squarefree modulus, a finite union of reduced residue classes modulo
`h * ∏ H`.  This file proves that reduction and assembles the corresponding
counting asymptotic from fixed-progression PNT.
-/

namespace Erdos279

/-- Canonical reduced residues for an arbitrary positive modulus. -/
def reducedResiduesModulus (q : Nat) : Finset Nat :=
  (Finset.range q).filter fun a => q.Coprime a

@[simp]
theorem mem_reducedResiduesModulus
    {q a : Nat} :
    a ∈ reducedResiduesModulus q ↔
      a < q ∧ q.Coprime a := by
  simp [reducedResiduesModulus]

/-- Reduced classes modulo `h * ∏ H` avoiding residue one modulo every
prime appearing in the target exclusions. -/
def complementaryAllowedResidues
    (h : Prime) (H : Finset Prime) :
    Finset Nat :=
  (reducedResiduesModulus
      (h.1 * primeSubsetModulus H)).filter
    fun a =>
      a % h.1 ≠ 1 ∧
        ∀ p ∈ H, a % p.1 ≠ 1

@[simp]
theorem mem_complementaryAllowedResidues
    {h : Prime} {H : Finset Prime}
    {a : Nat} :
    a ∈ complementaryAllowedResidues h H ↔
      a < h.1 * primeSubsetModulus H ∧
      (h.1 * primeSubsetModulus H).Coprime a ∧
      a % h.1 ≠ 1 ∧
      ∀ p ∈ H, a % p.1 ≠ 1 := by
  simp [complementaryAllowedResidues,
    and_assoc]

/-- Every sufficiently large complementary target belongs to one of the
allowed reduced classes, and conversely every prime in an allowed class is
a complementary target. -/
theorem complementaryTarget_iff_allowedClass
    (h : Prime) (H : Finset Prime)
    (N n : Nat)
    (hhN : h.1 < N)
    (hHN : ∀ p ∈ H, p.1 < N)
    (hnN : N ≤ n) :
    primeNatPredicate
        (IsComplementaryPrimeTarget h H) n ↔
      ∃ a ∈ complementaryAllowedResidues h H,
        PrimeInModEq
          (h.1 * primeSubsetModulus H) a n := by
  classical
  let Q := h.1 * primeSubsetModulus H
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Nat.mul_pos h.pos
      (primeSubsetModulus_pos H)
  constructor
  · rintro ⟨hnPrime, hnNotHub, hnOld⟩
    let a := n % Q
    have hnNatPrime : n.Prime :=
      (isPrime_iff_natPrime n).1 hnPrime
    have hHubCoprime : h.1.Coprime n := by
      exact
        (Nat.coprime_primes
          h.natPrime hnNatPrime).2
          (by omega)
    have hOldCoprime :
        (primeSubsetModulus H).Coprime n := by
      rw [primeSubsetModulus,
        Nat.coprime_prod_left_iff]
      intro p hp
      exact
        (Nat.coprime_primes
          p.natPrime hnNatPrime).2
          (by
            have hpLt := hHN p hp
            omega)
    have hQCoprimeN : Q.Coprime n := by
      dsimp [Q]
      exact
        Nat.coprime_mul_iff_left.mpr
          ⟨hHubCoprime, hOldCoprime⟩
    have hQCoprimeA : Q.Coprime a := by
      rw [Nat.coprime_iff_gcd_eq_one]
      calc
        Nat.gcd Q a =
            Nat.gcd a Q :=
          Nat.gcd_comm _ _
        _ = Nat.gcd Q n := by
          dsimp [a]
          exact (Nat.gcd_rec Q n).symm
        _ = 1 :=
          hQCoprimeN.gcd_eq_one
    have hnaQ : n ≡ a [MOD Q] := by
      dsimp [a]
      exact (Nat.mod_mod n Q).symm
    have hnaHub : n ≡ a [MOD h.1] := by
      dsimp [Q] at hnaQ
      exact hnaQ.of_mul_right
        (primeSubsetModulus H)
    have haNotHub : a % h.1 ≠ 1 := by
      intro ha
      apply hnNotHub
      unfold InControllerProgression
      change n % h.1 = 1
      rw [hnaHub]
      exact ha
    have hnaOld :
        n ≡ a [MOD primeSubsetModulus H] := by
      dsimp [Q] at hnaQ
      exact hnaQ.of_mul_left h.1
    have haNotOld :
        ∀ p ∈ H, a % p.1 ≠ 1 := by
      intro p hp ha
      have hnap :
          n ≡ a [MOD p.1] :=
        (modEq_primeSubsetModulus_iff
          n a H).1 hnaOld p hp
      exact hnOld p hp
        (by
          rw [hnap]
          exact ha)
    refine ⟨a, ?_, hnPrime, hnaQ⟩
    exact
      mem_complementaryAllowedResidues.mpr
        ⟨Nat.mod_lt n hQpos,
          hQCoprimeA, haNotHub, haNotOld⟩
  · rintro ⟨a, haAllowed, hnPrime, hnaQ⟩
    have ha :=
      mem_complementaryAllowedResidues.mp
        haAllowed
    have hnaHub :
        n ≡ a [MOD h.1] := by
      exact hnaQ.of_mul_right
        (primeSubsetModulus H)
    have hnaOld :
        n ≡ a [MOD primeSubsetModulus H] := by
      exact hnaQ.of_mul_left h.1
    refine ⟨hnPrime, ?_, ?_⟩
    · intro hnHub
      exact ha.2.2.1
        (by
          unfold InControllerProgression at hnHub
          rw [← hnaHub]
          exact hnHub)
    · intro p hp
      have hnap :
          n ≡ a [MOD p.1] :=
        (modEq_primeSubsetModulus_iff
          n a H).1 hnaOld p hp
      intro hnp
      exact ha.2.2.2 p hp
        (by
          rw [← hnap]
          exact hnp)

/-- Fixed-progression PNT determines the complementary target density as
the number of allowed reduced classes divided by the modulus totient. -/
theorem complementaryTargets_countingAsymptotic_card
    (h : Prime) (H : Finset Prime)
    (N : Nat)
    (hhN : h.1 < N)
    (hHN : ∀ p ∈ H, p.1 < N)
    (hPNT :
      FixedProgressionPrimeNumberTheorem
        (h.1 * primeSubsetModulus H)) :
    HasProjectPrimeCountingAsymptotic
      (IsComplementaryPrimeTarget h H)
      (((complementaryAllowedResidues h H).card : Real) /
        (Nat.totient
          (h.1 * primeSubsetModulus H) : Real)) := by
  let R := complementaryAllowedResidues h H
  have hUnion :=
    fixedProgressionPNT_finiteUnion
      R
      (by
        intro a ha
        exact
          (mem_complementaryAllowedResidues.mp ha).1)
      (by
        intro a ha
        exact
          (mem_complementaryAllowedResidues.mp ha).2.1.symm)
      hPNT
  unfold HasProjectPrimeCountingAsymptotic
  exact
    hUnion.congr_of_eventually_iff N
      (fun n hn =>
        complementaryTarget_iff_allowedClass
          h H N n hhN hHN hn)

/-- Once the elementary CRT cardinality is identified with the Euler
product, fixed-progression PNT gives the exact complementary density used by
the mesh. -/
theorem complementaryTargets_countingAsymptotic
    (h : Prime) (H : Finset Prime)
    (N : Nat)
    (hhN : h.1 < N)
    (hHN : ∀ p ∈ H, p.1 < N)
    (hPNT :
      FixedProgressionPrimeNumberTheorem
        (h.1 * primeSubsetModulus H))
    (hDensity :
      ((complementaryAllowedResidues h H).card : Real) /
          (Nat.totient
            (h.1 * primeSubsetModulus H) : Real) =
        controllerComplementDensity h H) :
    HasProjectPrimeCountingAsymptotic
      (IsComplementaryPrimeTarget h H)
      (controllerComplementDensity h H) := by
  rw [← hDensity]
  exact
    complementaryTargets_countingAsymptotic_card
      h H N hhN hHN hPNT

end Erdos279
