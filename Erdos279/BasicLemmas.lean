import Erdos279.Definitions

/-!
# Elementary logic and arithmetic for Erdős Problem 279

Everything in this file is checked by Lean's kernel and uses no analytic
number theory.
-/

namespace Erdos279

/-- `a ≡ b (mod m)`, expressed using canonical natural remainders. -/
def CongruentMod (m a b : Nat) : Prop :=
  a % m = b % m

theorem Prime.two_le (p : Prime) : 2 ≤ p.1 :=
  p.2.1

theorem Prime.pos (p : Prime) : 0 < p.1 :=
  Nat.lt_of_lt_of_le Nat.zero_lt_two p.two_le

theorem congruentMod_canonical_iff
    (p : Prime) (a : Nat) (u : Fin p.1) :
    CongruentMod p.1 a (u : Nat) ↔ a % p.1 = (u : Nat) := by
  unfold CongruentMod
  rw [Nat.mod_eq_of_lt u.isLt]

theorem covers_iff_coversInt (k n : Nat) (r : ResidueAssignment) :
    Covers k n r ↔ CoversInt k n r := by
  constructor
  · rintro ⟨p, t, hkt, hn⟩
    refine ⟨p, (t : Int), Int.ofNat_le.mpr hkt, ?_⟩
    exact congrArg Int.ofNat hn
  · rintro ⟨p, t, hkt, hn⟩
    have ht0 : 0 ≤ t :=
      Int.le_trans (Int.natCast_nonneg k) hkt
    obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le ht0
    refine ⟨p, q, ?_, ?_⟩
    · apply Int.ofNat_le.mp
      simpa [hq] using hkt
    · apply Int.ofNat.inj
      simpa [hq] using hn

theorem coversInt_iff_covers (k n : Nat) (r : ResidueAssignment) :
    CoversInt k n r ↔ Covers k n r :=
  (covers_iff_coversInt k n r).symm

/--
The normalization `r_p < p` is the exact ingredient that turns the maturity
inequality `k p ≤ n` into the lower bound on the quotient.
-/
theorem covers_iff_matureCovers (k n : Nat) (r : ResidueAssignment) :
    Covers k n r ↔ MatureCovers k n r := by
  constructor
  · rintro ⟨p, t, hkt, rfl⟩
    refine ⟨p, ?_, ?_⟩
    · exact Nat.le_trans (Nat.mul_le_mul_right p.1 hkt)
        (Nat.le_add_left (t * p.1) (r p : Nat))
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (r p).isLt]
  · rintro ⟨p, hkn, hmod⟩
    have ht : k ≤ n / p.1 :=
      (Nat.le_div_iff_mul_le p.pos).mpr hkn
    refine ⟨p, n / p.1, ht, ?_⟩
    calc
      n = n % p.1 + p.1 * (n / p.1) := (Nat.mod_add_div n p.1).symm
      _ = (r p : Nat) + (n / p.1) * p.1 := by
        rw [hmod, Nat.mul_comm]

theorem coversInt_iff_matureCovers (k n : Nat) (r : ResidueAssignment) :
    CoversInt k n r ↔ MatureCovers k n r :=
  (coversInt_iff_covers k n r).trans
    (covers_iff_matureCovers k n r)

theorem matureCovers_iff_congruence (k n : Nat) (r : ResidueAssignment) :
    MatureCovers k n r ↔
      ∃ p : Prime, k * p.1 ≤ n ∧ CongruentMod p.1 n (r p : Nat) := by
  constructor
  · rintro ⟨p, hkp, hmod⟩
    exact ⟨p, hkp, (congruentMod_canonical_iff p n (r p)).mpr hmod⟩
  · rintro ⟨p, hkp, hcong⟩
    exact ⟨p, hkp, (congruentMod_canonical_iff p n (r p)).mp hcong⟩

theorem covers_mono_level {k₁ k₂ n : Nat} {r : ResidueAssignment}
    (hlevel : k₁ ≤ k₂) (hcover : Covers k₂ n r) :
    Covers k₁ n r := by
  rcases hcover with ⟨p, t, hkt, hn⟩
  exact ⟨p, t, Nat.le_trans hlevel hkt, hn⟩

theorem matureCovers_mono_level {k₁ k₂ n : Nat} {r : ResidueAssignment}
    (hlevel : k₁ ≤ k₂) (hcover : MatureCovers k₂ n r) :
    MatureCovers k₁ n r := by
  rcases hcover with ⟨p, hkn, hmod⟩
  refine ⟨p, Nat.le_trans (Nat.mul_le_mul_right p.1 hlevel) hkn, hmod⟩

theorem coversInt_mono_level {k₁ k₂ n : Nat} {r : ResidueAssignment}
    (hlevel : k₁ ≤ k₂) (hcover : CoversInt k₂ n r) :
    CoversInt k₁ n r := by
  rcases hcover with ⟨p, t, hkt, hn⟩
  exact ⟨p, t, Int.le_trans (Int.ofNat_le.mpr hlevel) hkt, hn⟩

theorem coversTail_mono_level {k₁ k₂ : Nat} {r : ResidueAssignment}
    (hlevel : k₁ ≤ k₂) (hcover : CoversTail k₂ r) :
    CoversTail k₁ r := by
  rcases hcover with ⟨N, hN, htail⟩
  exact ⟨N, hN, fun n hn => covers_mono_level hlevel (htail n hn)⟩

/-- The correct direction of monotonicity: `P(k₂) → P(k₁)` for `k₁ ≤ k₂`. -/
theorem P_mono_level {k₁ k₂ : Nat} (hlevel : k₁ ≤ k₂) :
    P k₂ → P k₁ := by
  rintro ⟨r, hr⟩
  exact ⟨r, coversTail_mono_level hlevel hr⟩

/-- Failure is monotone in the opposite direction. -/
theorem not_P_mono_level {k₁ k₂ : Nat} (hlevel : k₁ ≤ k₂) :
    (¬ P k₁) → ¬ P k₂ := by
  intro hnot hPk₂
  exact hnot (P_mono_level hlevel hPk₂)

theorem not_P_iff_obstructionAt (k : Nat) :
    (¬ P k) ↔ ObstructionAt k := by
  constructor
  · intro hnotP r N hN
    apply Classical.byContradiction
    intro hnoWitness
    apply hnotP
    refine ⟨r, N, hN, ?_⟩
    intro n hn
    apply (covers_iff_matureCovers k n r).mpr
    apply Classical.byContradiction
    intro hnotCovered
    apply hnoWitness
    refine ⟨n, hn, ?_⟩
    intro p hp hEq
    exact hnotCovered ⟨p, hp, hEq⟩
  · intro hobstruction hP
    rcases hP with ⟨r, N, hN, htail⟩
    rcases hobstruction r N hN with ⟨n, hn, havoid⟩
    rcases (covers_iff_matureCovers k n r).mp (htail n hn) with
      ⟨p, hp, hEq⟩
    exact havoid p hp hEq

/-- The universal obstruction becomes only easier when the level increases. -/
theorem obstructionAt_mono_level {k₁ k₂ : Nat} (hlevel : k₁ ≤ k₂) :
    ObstructionAt k₁ → ObstructionAt k₂ := by
  intro hobs r N hN
  rcases hobs r N hN with ⟨n, hn, havoid⟩
  refine ⟨n, hn, ?_⟩
  intro p hk₂p
  apply havoid p
  exact Nat.le_trans (Nat.mul_le_mul_right p.1 hlevel) hk₂p

/-- `P(k)` with the original integer witness and every quantifier exposed. -/
theorem P_iff_integer_quantifiers (k : Nat) :
    P k ↔
      ∃ r : ResidueAssignment, ∃ N : Nat, 1 ≤ N ∧
        ∀ n : Nat, N ≤ n →
          ∃ p : Prime, ∃ t : Int,
            (k : Int) ≤ t ∧
            (n : Int) = ((r p : Nat) : Int) + t * (p.1 : Int) := by
  constructor
  · rintro ⟨r, N, hN, htail⟩
    refine ⟨r, N, hN, ?_⟩
    intro n hn
    exact (coversInt_iff_covers k n r).mpr (htail n hn)
  · rintro ⟨r, N, hN, htail⟩
    refine ⟨r, N, hN, ?_⟩
    intro n hn
    exact (coversInt_iff_covers k n r).mp (htail n hn)

/-- `P(k)` with the congruence-and-maturity quantifiers exposed. -/
theorem P_iff_mature_quantifiers (k : Nat) :
    P k ↔
      ∃ r : ResidueAssignment, ∃ N : Nat, 1 ≤ N ∧
        ∀ n : Nat, N ≤ n →
          ∃ p : Prime, k * p.1 ≤ n ∧ n % p.1 = (r p : Nat) := by
  constructor
  · rintro ⟨r, N, hN, htail⟩
    refine ⟨r, N, hN, ?_⟩
    intro n hn
    exact (covers_iff_matureCovers k n r).mp (htail n hn)
  · rintro ⟨r, N, hN, htail⟩
    refine ⟨r, N, hN, ?_⟩
    intro n hn
    exact (covers_iff_matureCovers k n r).mpr (htail n hn)

theorem not_globalAffirmative_iff_globalNegative :
    (¬ GlobalAffirmative) ↔ GlobalNegative := by
  constructor
  · intro hnotGlobal
    apply Classical.byContradiction
    intro hnotNegative
    apply hnotGlobal
    intro k hk
    apply Classical.byContradiction
    intro hnotPk
    apply hnotNegative
    exact ⟨k, hk, (not_P_iff_obstructionAt k).mp hnotPk⟩
  · rintro ⟨k, hk, hobstruction⟩ hglobal
    exact (not_P_iff_obstructionAt k).mpr hobstruction (hglobal k hk)

end Erdos279
