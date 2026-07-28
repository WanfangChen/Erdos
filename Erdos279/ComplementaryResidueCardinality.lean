import Erdos279.ComplementaryProgressionPNT

/-!
# Cardinality of complementary reduced residue classes

This file proves the finite CRT count

`# {a mod ∏ p : a is a unit and a ≠ 1 mod p for every p} =
  ∏ p, (p - 2)`.

It removes the last purely finite condition from the complementary
fixed-progression PNT bridge.
-/

namespace Erdos279

/-- Reduced residues modulo a squarefree prime product that avoid one in
every prime coordinate. -/
def primeAvoidingResidues
    (H : Finset Prime) : Finset Nat :=
  (reducedResiduesModulus
      (primeSubsetModulus H)).filter
    fun a => ∀ p ∈ H, a % p.1 ≠ 1

@[simp]
theorem mem_primeAvoidingResidues
    {H : Finset Prime} {a : Nat} :
    a ∈ primeAvoidingResidues H ↔
      a < primeSubsetModulus H ∧
      (primeSubsetModulus H).Coprime a ∧
      ∀ p ∈ H, a % p.1 ≠ 1 := by
  simp [primeAvoidingResidues, and_assoc]

/-- Coprimality is unchanged when the right argument is reduced modulo the
left argument. -/
theorem coprime_mod_right_iff
    (m n : Nat) :
    m.Coprime (n % m) ↔ m.Coprime n := by
  rw [Nat.coprime_iff_gcd_eq_one,
    Nat.coprime_iff_gcd_eq_one]
  rw [show
    Nat.gcd m (n % m) =
      Nat.gcd m n by
        calc
          Nat.gcd m (n % m) =
              Nat.gcd (n % m) m :=
            Nat.gcd_comm _ _
          _ = Nat.gcd m n :=
            (Nat.gcd_rec m n).symm]

/-- One-coordinate allowed residues for a prime modulus. -/
def primeLocalAvoidingResidues
    (p : Prime) : Finset Nat :=
  (reducedResiduesModulus p.1).filter
    fun a => a % p.1 ≠ 1

@[simp]
theorem mem_primeLocalAvoidingResidues
    {p : Prime} {a : Nat} :
    a ∈ primeLocalAvoidingResidues p ↔
      a < p.1 ∧ p.1.Coprime a ∧
      a % p.1 ≠ 1 := by
  simp [primeLocalAvoidingResidues,
    and_assoc]

/-- A prime coordinate has exactly `p - 2` allowed unit residues. -/
theorem card_primeLocalAvoidingResidues
    (p : Prime) :
    (primeLocalAvoidingResidues p).card =
      p.1 - 2 := by
  have hset :
      primeLocalAvoidingResidues p =
        Finset.Ico 2 p.1 := by
    ext a
    constructor
    · intro ha
      have h :=
        mem_primeLocalAvoidingResidues.mp ha
      have haNeZero : a ≠ 0 := by
        intro ha0
        subst a
        have hpOne : p.1 = 1 := by
          simpa using h.2.1
        exact
          (Nat.ne_of_gt p.one_lt) hpOne
      have haNeOne : a ≠ 1 := by
        intro ha1
        subst a
        exact h.2.2
          (Nat.mod_eq_of_lt p.one_lt)
      simp only [Finset.mem_Ico]
      omega
    · intro ha
      have haBounds :
          2 ≤ a ∧ a < p.1 := by
        simpa only [Finset.mem_Ico] using ha
      have haCoprime :
          p.1.Coprime a :=
        Nat.coprime_of_lt_prime
          (Nat.ne_of_gt
            ((by omega :
              0 < a)))
          haBounds.2
          p.natPrime
      apply
        mem_primeLocalAvoidingResidues.mpr
      refine
        ⟨haBounds.2, haCoprime, ?_⟩
      rw [Nat.mod_eq_of_lt haBounds.2]
      omega
  rw [hset, Nat.card_Ico]

/-- A prime is coprime to the product of the values of any finite set of
distinct different primes. -/
theorem prime_coprime_primeSubsetModulus
    (p : Prime) (H : Finset Prime)
    (hpH : p ∉ H) :
    p.1.Coprime (primeSubsetModulus H) := by
  rw [primeSubsetModulus,
    Nat.coprime_prod_right_iff]
  intro q hq
  exact
    (Nat.coprime_primes
      p.natPrime q.natPrime).2
      (by
        intro hpq
        apply hpH
        have hpqPrime : p = q :=
          Subtype.ext hpq
        simpa [hpqPrime] using hq)

/-- CRT gives a bijection between allowed residues for `insert p H` and
the product of the allowed `p` coordinate with the allowed residues for
`H`. -/
noncomputable def primeAvoidingResiduesInsertEquiv
    (p : Prime) (H : Finset Prime)
    (hpH : p ∉ H) :
    {a // a ∈ primeAvoidingResidues (insert p H)} ≃
      {uv //
        uv ∈
          (primeLocalAvoidingResidues p).product
            (primeAvoidingResidues H)} := by
  classical
  let Q := primeSubsetModulus H
  have hcop : p.1.Coprime Q :=
    prime_coprime_primeSubsetModulus
      p H hpH
  have hQpos : 0 < Q :=
    primeSubsetModulus_pos H
  let forward :
      {a // a ∈ primeAvoidingResidues (insert p H)} →
        {uv //
          uv ∈
            (primeLocalAvoidingResidues p).product
              (primeAvoidingResidues H)} :=
    fun a => by
      refine
        ⟨(a.1 % p.1, a.1 % Q), ?_⟩
      have ha :=
        mem_primeAvoidingResidues.mp a.2
      rw [primeSubsetModulus,
        Finset.prod_insert hpH] at ha
      have haCop :
          p.1.Coprime a.1 ∧
            Q.Coprime a.1 :=
        Nat.coprime_mul_iff_left.mp
          ha.2.1
      have hlocal :
          a.1 % p.1 ∈
            primeLocalAvoidingResidues p := by
        apply
          mem_primeLocalAvoidingResidues.mpr
        refine
          ⟨Nat.mod_lt _ p.pos,
            (coprime_mod_right_iff
              p.1 a.1).2 haCop.1,
            ?_⟩
        simpa [Nat.mod_mod] using
          ha.2.2 p
            (Finset.mem_insert_self p H)
      have htail :
          a.1 % Q ∈
            primeAvoidingResidues H := by
        apply mem_primeAvoidingResidues.mpr
        refine
          ⟨Nat.mod_lt _ hQpos,
            (coprime_mod_right_iff
              Q a.1).2 haCop.2,
            ?_⟩
        intro q hq
        have haMod :
            a.1 ≡ a.1 % Q [MOD Q] :=
          (Nat.mod_mod a.1 Q).symm
        have haq :
            a.1 ≡ a.1 % Q [MOD q.1] :=
          (modEq_primeSubsetModulus_iff
            a.1 (a.1 % Q) H).1
            haMod q hq
        intro hbad
        exact
          ha.2.2 q
            (Finset.mem_insert_of_mem hq)
            (by
              rw [haq]
              exact hbad)
      exact
        Finset.mem_product.mpr
          ⟨hlocal, htail⟩
  let backward :
      {uv //
        uv ∈
          (primeLocalAvoidingResidues p).product
            (primeAvoidingResidues H)} →
        {a // a ∈ primeAvoidingResidues (insert p H)} :=
    fun uv => by
      let a :=
        (Nat.chineseRemainder
          hcop uv.1.1 uv.1.2).1
      have huv :=
        Finset.mem_product.mp uv.2
      have hu :=
        mem_primeLocalAvoidingResidues.mp
          huv.1
      have hv :=
        mem_primeAvoidingResidues.mp
          huv.2
      have haP :
          a ≡ uv.1.1 [MOD p.1] :=
        (Nat.chineseRemainder
          hcop uv.1.1 uv.1.2).2.1
      have haQ :
          a ≡ uv.1.2 [MOD Q] :=
        (Nat.chineseRemainder
          hcop uv.1.1 uv.1.2).2.2
      have haModP :
          a % p.1 = uv.1.1 := by
        simpa [Nat.ModEq,
          Nat.mod_eq_of_lt hu.1] using haP
      have haModQ :
          a % Q = uv.1.2 := by
        change
          a % Q = uv.1.2 % Q at haQ
        exact
          haQ.trans
            (Nat.mod_eq_of_lt hv.1)
      have haCopP : p.1.Coprime a := by
        apply
          (coprime_mod_right_iff
            p.1 a).1
        rw [haModP]
        exact hu.2.1
      have haCopQ : Q.Coprime a := by
        apply
          (coprime_mod_right_iff
            Q a).1
        rw [haModQ]
        exact hv.2.1
      refine ⟨a, ?_⟩
      apply mem_primeAvoidingResidues.mpr
      rw [primeSubsetModulus,
        Finset.prod_insert hpH]
      refine
        ⟨Nat.chineseRemainder_lt_mul
            hcop uv.1.1 uv.1.2
            p.natPrime.ne_zero hQpos.ne',
          Nat.coprime_mul_iff_left.mpr
            ⟨haCopP, haCopQ⟩,
          ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with
        rfl | hqH
      · rw [haModP]
        simpa [Nat.mod_eq_of_lt hu.1] using
          hu.2.2
      · have haq :
            a ≡ uv.1.2 [MOD q.1] :=
          (modEq_primeSubsetModulus_iff
            a uv.1.2 H).1
            haQ q hqH
        intro hbad
        exact hv.2.2 q hqH
          (by
            rw [← haq]
            exact hbad)
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    apply Subtype.ext
    dsimp [forward, backward]
    let c :=
      (Nat.chineseRemainder
        hcop (a.1 % p.1)
          (a.1 % Q)).1
    have hcP :
        c ≡ a.1 % p.1 [MOD p.1] :=
      (Nat.chineseRemainder
        hcop (a.1 % p.1)
          (a.1 % Q)).2.1
    have hcQ :
        c ≡ a.1 % Q [MOD Q] :=
      (Nat.chineseRemainder
        hcop (a.1 % p.1)
          (a.1 % Q)).2.2
    have hca :
        c ≡ a.1 [MOD p.1 * Q] := by
      apply
        (Nat.modEq_and_modEq_iff_modEq_mul
          hcop).1
      exact
        ⟨hcP.trans (Nat.mod_mod _ _),
          hcQ.trans (Nat.mod_mod _ _)⟩
    have haLt :
        a.1 < p.1 * Q := by
      have ha :=
        mem_primeAvoidingResidues.mp a.2
      simpa [primeSubsetModulus,
        Finset.prod_insert hpH] using ha.1
    have hcLt :
        c < p.1 * Q :=
      Nat.chineseRemainder_lt_mul
        hcop (a.1 % p.1) (a.1 % Q)
        p.natPrime.ne_zero hQpos.ne'
    simpa [Nat.ModEq,
      Nat.mod_eq_of_lt hcLt,
      Nat.mod_eq_of_lt haLt] using hca
  · intro uv
    apply Subtype.ext
    apply Prod.ext
    · dsimp [forward, backward]
      have hu :=
        mem_primeLocalAvoidingResidues.mp
          (Finset.mem_product.mp uv.2).1
      simpa [Nat.ModEq,
        Nat.mod_eq_of_lt hu.1] using
        (Nat.chineseRemainder
          hcop uv.1.1 uv.1.2).2.1
    · dsimp [forward, backward]
      have hv :=
        mem_primeAvoidingResidues.mp
          (Finset.mem_product.mp uv.2).2
      have hcrt :=
        (Nat.chineseRemainder
          hcop uv.1.1 uv.1.2).2.2
      change
        (Nat.chineseRemainder
            hcop uv.1.1 uv.1.2).1 % Q =
          uv.1.2 % Q at hcrt
      exact hcrt.trans
        (Nat.mod_eq_of_lt hv.1)

/-- Multiplicative cardinality formula for the allowed residue system. -/
theorem card_primeAvoidingResidues
    (H : Finset Prime) :
    (primeAvoidingResidues H).card =
      ∏ p ∈ H, (p.1 - 2) := by
  classical
  induction H using Finset.induction_on with
  | empty =>
      simp [primeAvoidingResidues,
        reducedResiduesModulus,
        primeSubsetModulus]
  | @insert p H hpH ih =>
      have hCardEquiv :
          (primeAvoidingResidues
              (insert p H)).card =
            (primeLocalAvoidingResidues p).card *
              (primeAvoidingResidues H).card := by
        have h :=
          Fintype.card_congr
            (primeAvoidingResiduesInsertEquiv
              p H hpH)
        simpa using h
      rw [hCardEquiv,
        card_primeLocalAvoidingResidues,
        ih]
      simp [hpH]

/-- The complementary residue set is exactly the avoiding residue system
for the inserted hub prime. -/
theorem complementaryAllowedResidues_eq_insert
    (h : Prime) (H : Finset Prime)
    (hhH : h ∉ H) :
    complementaryAllowedResidues h H =
      primeAvoidingResidues (insert h H) := by
  ext a
  simp only [mem_complementaryAllowedResidues,
    mem_primeAvoidingResidues,
    primeSubsetModulus,
    Finset.prod_insert hhH,
    Finset.mem_insert]
  constructor
  · rintro ⟨haLt, haCop, hah, haH⟩
    refine ⟨haLt, haCop, ?_⟩
    intro p hp
    rcases hp with rfl | hpH
    · exact hah
    · exact haH p hpH
  · rintro ⟨haLt, haCop, haAll⟩
    exact
      ⟨haLt, haCop,
        haAll h (Or.inl rfl),
        fun p hp =>
          haAll p (Or.inr hp)⟩

/-- Exact finite cardinality of the complementary allowed classes. -/
theorem card_complementaryAllowedResidues
    (h : Prime) (H : Finset Prime)
    (hhH : h ∉ H) :
    (complementaryAllowedResidues h H).card =
      (h.1 - 2) *
        ∏ p ∈ H, (p.1 - 2) := by
  rw [complementaryAllowedResidues_eq_insert
    h H hhH,
    card_primeAvoidingResidues]
  simp [hhH]

/-- The elementary one-prime density factor in quotient form. -/
theorem one_sub_reciprocal_prime_pred
    (p : Prime) :
    1 - 1 / ((p.1 : Real) - 1) =
      ((p.1 - 2 : Nat) : Real) /
        ((p.1 - 1 : Nat) : Real) := by
  have hpOneReal :
      (p.1 : Real) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast
      (Nat.ne_of_gt p.one_lt)
  rw [Nat.cast_sub p.natPrime.two_le,
    Nat.cast_sub p.one_lt.le]
  field_simp [hpOneReal]
  ring

/-- The finite Euler product is the quotient of the products of the local
allowed and reduced class counts. -/
theorem controllerExclusionProduct_eq_primeRatio
    (H : Finset Prime) :
    controllerExclusionProduct H =
      (∏ p ∈ H,
          ((p.1 - 2 : Nat) : Real)) /
        (∏ p ∈ H,
          ((p.1 - 1 : Nat) : Real)) := by
  unfold controllerExclusionProduct
  simp_rw [one_sub_reciprocal_prime_pred]
  rw [Finset.prod_div_distrib]

/-- The allowed-class proportion is exactly the complementary density
Euler product. -/
theorem complementaryAllowedResidues_density
    (h : Prime) (H : Finset Prime)
    (hhH : h ∉ H) :
    ((complementaryAllowedResidues h H).card : Real) /
        (Nat.totient
          (h.1 * primeSubsetModulus H) : Real) =
      controllerComplementDensity h H := by
  have hcop :
      h.1.Coprime (primeSubsetModulus H) :=
    prime_coprime_primeSubsetModulus
      h H hhH
  rw [card_complementaryAllowedResidues
      h H hhH,
    Nat.totient_mul hcop,
    Nat.totient_prime h.natPrime,
    totient_primeSubsetModulus,
    controllerComplementDensity,
    one_sub_reciprocal_prime_pred,
    controllerExclusionProduct_eq_primeRatio]
  push_cast
  ring

/-- The hub itself is never one of its old controller primes. -/
theorem hub_not_mem_oldControllerPrimes
    (h : Prime) (z : Nat) :
    h ∉ oldControllerPrimes h z := by
  intro hhOld
  have hhG :
      InControllerProgression h h :=
    (mem_oldControllerPrimes.mp hhOld).1
  exact
    (Nat.lt_irrefl h.1)
      (hub_lt_of_inControllerProgression hhG)

/-- For a density mesh, the complementary prime-target count-form
asymptotic now follows solely from fixed-progression PNT for its one fixed
squarefree modulus. -/
theorem mesh_complementaryTargets_countingAsymptotic
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hPNT :
      FixedProgressionPrimeNumberTheorem
        (h.1 *
          primeSubsetModulus
            (oldControllerPrimes h M.cutoff))) :
    HasProjectPrimeCountingAsymptotic
      (IsComplementaryPrimeTarget h
        (oldControllerPrimes h M.cutoff))
      (controllerComplementDensity h
        (oldControllerPrimes h M.cutoff)) := by
  let N := max h.1 M.cutoff + 1
  apply
    complementaryTargets_countingAsymptotic
      h (oldControllerPrimes h M.cutoff)
      N
  · dsimp [N]
    omega
  · intro p hp
    have hpLe :
        p.1 ≤ M.cutoff :=
      (mem_oldControllerPrimes.mp hp).2
    dsimp [N]
    omega
  · exact hPNT
  · exact
      complementaryAllowedResidues_density
        h (oldControllerPrimes h M.cutoff)
        (hub_not_mem_oldControllerPrimes
          h M.cutoff)

end Erdos279
