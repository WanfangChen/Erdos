import Erdos279.DirectUniformHardReduction

/-!
# Bridge to the Formal Conjectures statement of Erdős Problem 279

The `FormalConjectures/ErdosProblems/279.lean` file in
`google-deepmind/formal-conjectures` represents primes by `Nat.Prime`, chooses
residues with a function `Nat → Nat`, and does not require its tail threshold
to be positive.  The present project represents primes by the subtype `Prime`,
stores canonical residues as `Fin p`, and normalizes the threshold by `1 ≤ N`.

The theorem below proves that these two encodings are logically equivalent.
-/

namespace Erdos279

/-- The affirmative right-hand side of `FormalConjectures` theorem
`Erdos279.erdos_279`, copied verbatim apart from its surrounding
`answer(True) ↔ ...` wrapper. -/
def DeepMindErdos279Affirmative : Prop :=
  ∀ k : Nat, k ≥ 3 →
    ∃ a : Nat → Nat, ∃ N : Nat, (∀ p : Nat, p.Prime → a p < p) ∧
      ∀ n ≥ N, ∃ p : Nat, ∃ t ≥ k,
        p.Prime ∧ n = a p + t * p

/-- The project's exact statement and the affirmative `FormalConjectures`
statement are logically equivalent. -/
theorem globalAffirmative_iff_deepMindErdos279Affirmative :
    GlobalAffirmative ↔ DeepMindErdos279Affirmative := by
  constructor
  · intro hglobal k hk
    rcases hglobal k hk with ⟨r, N, _hN, htail⟩
    let a : Nat → Nat := fun p =>
      if hp : p.Prime then
        (r ⟨p, (isPrime_iff_natPrime p).mpr hp⟩ : Nat)
      else 0
    refine ⟨a, N, ?_, ?_⟩
    · intro p hp
      have hp' : IsPrime p := (isPrime_iff_natPrime p).mpr hp
      simpa [a, hp] using (r ⟨p, hp'⟩).isLt
    · intro n hn
      rcases htail n hn with ⟨p, t, hkt, hnEq⟩
      refine ⟨p.1, t, hkt, p.natPrime, ?_⟩
      simpa [a, p.natPrime] using hnEq
  · intro hdeep k hk
    rcases hdeep k hk with ⟨a, N, ha, htail⟩
    let r : ResidueAssignment := fun p =>
      ⟨a p.1, ha p.1 p.natPrime⟩
    refine ⟨r, max 1 N, by omega, ?_⟩
    intro n hn
    have hnN : N ≤ n :=
      Nat.le_trans (Nat.le_max_right 1 N) hn
    rcases htail n hnN with ⟨p, t, hkt, hp, hnEq⟩
    have hp' : IsPrime p := (isPrime_iff_natPrime p).mpr hp
    let q : Prime := ⟨p, hp'⟩
    refine ⟨q, t, hkt, ?_⟩
    simpa [r, q] using hnEq

/-- The exact affirmative proposition used by `FormalConjectures`, discharged
by the unconditional theorem in this project. -/
theorem deepMindErdos279Affirmative : DeepMindErdos279Affirmative :=
  globalAffirmative_iff_deepMindErdos279Affirmative.mp globalAffirmative

end Erdos279
