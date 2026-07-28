import Erdos279.BasicLemmas

/-!
# The finite constraint problem

This file gives an exact dependent-type encoding of `F(k,N,M)`.  A local
assignment has one value in `Fin p` for every prime satisfying `k*p ≤ M`;
therefore the one-residue-per-prime and canonical-representative conditions
are enforced by the type.
-/

namespace Erdos279

/-- Primes whose residue variables can occur in the window ending at `M`. -/
abbrev LocalPrime (k M : Nat) :=
  {p : Prime // k * p.1 ≤ M}

theorem relevantPrime_iff_le_div {k M : Nat} (hk : 0 < k) (p : Prime) :
    k * p.1 ≤ M ↔ p.1 ≤ M / k := by
  constructor
  · intro h
    apply (Nat.le_div_iff_mul_le hk).mpr
    simpa [Nat.mul_comm] using h
  · intro h
    have := (Nat.le_div_iff_mul_le hk).mp h
    simpa [Nat.mul_comm] using this

/-- Exactly one canonical residue for every relevant prime. -/
abbrev LocalAssignment (k M : Nat) :=
  (p : LocalPrime k M) → Fin p.1.1

/-- Coverage of one target by a local assignment. -/
def LocalMatureCovers (k M n : Nat) (a : LocalAssignment k M) : Prop :=
  ∃ p : LocalPrime k M,
    k * p.1.1 ≤ n ∧ n % p.1.1 = (a p : Nat)

/-- The exact finite CSP `F(k,N,M)`. -/
def FiniteCSP (k N M : Nat) : Prop :=
  ∃ a : LocalAssignment k M, ∀ n : Nat,
    N ≤ n → n ≤ M → LocalMatureCovers k M n a

/-- A global assignment satisfies every constraint in `[N,M]`. -/
def WindowSatisfied (k N M : Nat) (r : ResidueAssignment) : Prop :=
  ∀ n : Nat, N ≤ n → n ≤ M → MatureCovers k n r

/-- Restrict a global assignment to the variables relevant at endpoint `M`. -/
def restrictAssignment (k M : Nat) (r : ResidueAssignment) :
    LocalAssignment k M :=
  fun p => r p.1

/-- The canonical zero residue, available because every prime is positive. -/
def zeroResidue (p : Prime) : Fin p.1 :=
  ⟨0, p.pos⟩

/-- Extend a local assignment arbitrarily by the zero residue. -/
def extendAssignment (k M : Nat) (a : LocalAssignment k M) :
    ResidueAssignment :=
  fun p =>
    if hp : k * p.1 ≤ M then
      a ⟨p, hp⟩
    else
      zeroResidue p

theorem extendAssignment_eq {k M : Nat} (a : LocalAssignment k M)
    (p : Prime) (hp : k * p.1 ≤ M) :
    extendAssignment k M a p = a ⟨p, hp⟩ := by
  simp [extendAssignment, hp]

theorem localMatureCovers_restrict_iff
    {k M n : Nat} (hnM : n ≤ M) (r : ResidueAssignment) :
    LocalMatureCovers k M n (restrictAssignment k M r) ↔
      MatureCovers k n r := by
  constructor
  · rintro ⟨p, hpn, hEq⟩
    exact ⟨p.1, hpn, hEq⟩
  · rintro ⟨p, hpn, hEq⟩
    have hpM : k * p.1 ≤ M := Nat.le_trans hpn hnM
    exact ⟨⟨p, hpM⟩, hpn, hEq⟩

theorem localMatureCovers_extend_iff
    {k M n : Nat} (hnM : n ≤ M) (a : LocalAssignment k M) :
    LocalMatureCovers k M n a ↔
      MatureCovers k n (extendAssignment k M a) := by
  constructor
  · rintro ⟨p, hpn, hEq⟩
    refine ⟨p.1, hpn, ?_⟩
    rw [extendAssignment_eq a p.1 p.2]
    exact hEq
  · rintro ⟨p, hpn, hEq⟩
    have hpM : k * p.1 ≤ M := Nat.le_trans hpn hnM
    refine ⟨⟨p, hpM⟩, hpn, ?_⟩
    rw [extendAssignment_eq a p hpM] at hEq
    exact hEq

theorem finiteCSP_iff_globalWindow (k N M : Nat) :
    FiniteCSP k N M ↔
      ∃ r : ResidueAssignment, WindowSatisfied k N M r := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨extendAssignment k M a, ?_⟩
    intro n hnN hnM
    exact (localMatureCovers_extend_iff hnM a).mp (ha n hnN hnM)
  · rintro ⟨r, hr⟩
    refine ⟨restrictAssignment k M r, ?_⟩
    intro n hnN hnM
    exact (localMatureCovers_restrict_iff hnM r).mpr (hr n hnN hnM)

/-- A tail cover supplies a satisfying assignment for every finite endpoint. -/
theorem P_implies_all_finiteCSP {k : Nat} :
    P k → ∃ N : Nat, 1 ≤ N ∧ ∀ M : Nat, N ≤ M → FiniteCSP k N M := by
  rintro ⟨r, N, hN, htail⟩
  refine ⟨N, hN, ?_⟩
  intro M hNM
  apply (finiteCSP_iff_globalWindow k N M).mpr
  refine ⟨r, ?_⟩
  intro n hnN hnM
  exact (covers_iff_matureCovers k n r).mp (htail n hnN)

/--
The precise compactness principle needed for the reverse implication.

This is a named hypothesis, not an axiom.  A future `mathlib` layer will prove
it from compactness of the product of the finite discrete spaces `Fin p`.
-/
def AssignmentCompactness : Prop :=
  ∀ k N : Nat, 1 ≤ k →
    (∀ M : Nat, N ≤ M →
      ∃ r : ResidueAssignment, WindowSatisfied k N M r) →
    ∃ r : ResidueAssignment, ∀ n : Nat, N ≤ n → MatureCovers k n r

/-- The exact finite-unsatisfiability formulation of failure at level `k`. -/
def ArbitrarilyUnsat (k : Nat) : Prop :=
  ∀ N : Nat, 1 ≤ N → ∃ M : Nat, N ≤ M ∧ ¬ FiniteCSP k N M

theorem not_all_finiteCSP_iff_arbitrarilyUnsat (k : Nat) :
    (¬ ∃ N : Nat, 1 ≤ N ∧
      ∀ M : Nat, N ≤ M → FiniteCSP k N M) ↔
      ArbitrarilyUnsat k := by
  constructor
  · intro hnot N hN
    apply Classical.byContradiction
    intro hnoM
    apply hnot
    refine ⟨N, hN, ?_⟩
    intro M hNM
    apply Classical.byContradiction
    intro hnotF
    apply hnoM
    exact ⟨M, hNM, hnotF⟩
  · intro hunsat
    rintro ⟨N, hN, hall⟩
    rcases hunsat N hN with ⟨M, hNM, hnotF⟩
    exact hnotF (hall M hNM)

theorem P_iff_all_finiteCSP_of_compactness
    (hcompact : AssignmentCompactness) (k : Nat) (hk : 1 ≤ k) :
    P k ↔ ∃ N : Nat, 1 ≤ N ∧ ∀ M : Nat, N ≤ M → FiniteCSP k N M := by
  constructor
  · exact P_implies_all_finiteCSP
  · rintro ⟨N, hN, hfinite⟩
    have hwindows : ∀ M : Nat, N ≤ M →
        ∃ r : ResidueAssignment, WindowSatisfied k N M r := by
      intro M hNM
      exact (finiteCSP_iff_globalWindow k N M).mp (hfinite M hNM)
    rcases hcompact k N hk hwindows with ⟨r, hr⟩
    refine ⟨r, N, hN, ?_⟩
    intro n hn
    exact (covers_iff_matureCovers k n r).mpr (hr n hn)

theorem not_P_iff_arbitrarilyUnsat_of_compactness
    (hcompact : AssignmentCompactness) (k : Nat) (hk : 1 ≤ k) :
    (¬ P k) ↔ ArbitrarilyUnsat k := by
  constructor
  · intro hnotP
    apply (not_all_finiteCSP_iff_arbitrarilyUnsat k).mp
    intro hfinite
    exact hnotP ((P_iff_all_finiteCSP_of_compactness hcompact k hk).mpr hfinite)
  · intro hunsat hP
    have hfinite :=
      (P_iff_all_finiteCSP_of_compactness hcompact k hk).mp hP
    exact (not_all_finiteCSP_iff_arbitrarilyUnsat k).mpr hunsat hfinite

end Erdos279
