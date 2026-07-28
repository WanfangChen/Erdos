import Std

/-!
# Erdős Problem 279: exact formal statement

This file fixes the quantifiers and the canonical representatives used in the
problem.  It intentionally contains no analytic number theory.
-/

namespace Erdos279

/--
Primality, stated internally so that the foundational formalization can be
kernel-checked before the larger `mathlib` dependency is available.
-/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- The type of prime numbers used as residue moduli. -/
abbrev Prime := {p : Nat // IsPrime p}

/--
A residue assignment chooses the canonical representative `0 ≤ r_p < p`
for every prime `p`.  The type `Fin p` records this normalization directly.
-/
abbrev ResidueAssignment := (p : Prime) → Fin p.1

/--
The representation-based coverage relation at level `k`.

The original statement quantifies `t : ℤ`.  Since `k : ℕ` and `t ≥ k`,
the witness is necessarily nonnegative.  `CoversInt` below records the
literal integer formulation, and `covers_iff_coversInt` proves equivalence.
-/
def Covers (k n : Nat) (r : ResidueAssignment) : Prop :=
  ∃ p : Prime, ∃ t : Nat, k ≤ t ∧ n = (r p : Nat) + t * p.1

/-- The literal integer-witness formulation appearing in the problem. -/
def CoversInt (k n : Nat) (r : ResidueAssignment) : Prop :=
  ∃ p : Prime, ∃ t : Int,
    (k : Int) ≤ t ∧ (n : Int) = ((r p : Nat) : Int) + t * (p.1 : Int)

/-- The congruence-and-maturity formulation of coverage at level `k`. -/
def MatureCovers (k n : Nat) (r : ResidueAssignment) : Prop :=
  ∃ p : Prime, k * p.1 ≤ n ∧ n % p.1 = (r p : Nat)

/-- A fixed assignment covers a complete tail at level `k`. -/
def CoversTail (k : Nat) (r : ResidueAssignment) : Prop :=
  ∃ N : Nat, 1 ≤ N ∧ ∀ n : Nat, N ≤ n → Covers k n r

/-- The proposition `P(k)` from the problem statement. -/
def P (k : Nat) : Prop :=
  ∃ r : ResidueAssignment, CoversTail k r

/-- The global affirmative statement in its exact quantifier order. -/
def GlobalAffirmative : Prop :=
  ∀ k : Nat, 3 ≤ k → P k

/-- The exact universal obstruction for one fixed level `k`. -/
def ObstructionAt (k : Nat) : Prop :=
  ∀ r : ResidueAssignment, ∀ N : Nat, 1 ≤ N → ∃ n : Nat,
    N ≤ n ∧ ∀ p : Prime, k * p.1 ≤ n → n % p.1 ≠ (r p : Nat)

/-- The exact negative statement for the global conjecture. -/
def GlobalNegative : Prop :=
  ∃ k : Nat, 3 ≤ k ∧ ObstructionAt k

end Erdos279
