import Erdos279.PrimeCountingAsymptotic

/-!
# Fixed-progression PNT and the periodic pool

The analytic input is stated one reduced residue class at a time.  The
finite-union theorem from `PrimeCountingAsymptotic` then gives the exact
counting density of the selected periodic CRT classes.
-/

namespace Erdos279

/-- Prime natural numbers in one residue class. -/
def PrimeInModEq (q a n : Nat) : Prop :=
  IsPrime n ∧ n ≡ a [MOD q]

/-- PNT for every reduced residue class of one fixed modulus. -/
def FixedProgressionPrimeNumberTheorem
    (q : Nat) : Prop :=
  ∀ a : Nat, a.Coprime q →
    HasPrimeCountingAsymptotic
      (PrimeInModEq q a)
      (1 / (Nat.totient q : Real))

/-- Distinct canonical residues modulo `q` define disjoint classes. -/
theorem primeInModEq_disjoint
    {q a b : Nat}
    (ha : a < q) (hb : b < q)
    (hab : a ≠ b) :
    ∀ n, ¬
      (PrimeInModEq q a n ∧
        PrimeInModEq q b n) := by
  intro n hn
  have hna : n % q = a := by
    simpa [PrimeInModEq, Nat.ModEq,
      Nat.mod_eq_of_lt ha] using hn.1.2
  have hnb : n % q = b := by
    simpa [PrimeInModEq, Nat.ModEq,
      Nat.mod_eq_of_lt hb] using hn.2.2
  exact hab (hna.symm.trans hnb)

/-- Finite unions of distinct reduced classes have density
`card R / φ(q)`. -/
theorem fixedProgressionPNT_finiteUnion
    {q : Nat} (R : Finset Nat)
    (hRlt : ∀ a ∈ R, a < q)
    (hRcoprime : ∀ a ∈ R, a.Coprime q)
    (hPNT : FixedProgressionPrimeNumberTheorem q) :
    HasPrimeCountingAsymptotic
      (fun n => ∃ a ∈ R, PrimeInModEq q a n)
      ((R.card : Real) /
        (Nat.totient q : Real)) := by
  have hUnion :=
    hasPrimeCountingAsymptotic_exists_mem_finset
      R (fun a => PrimeInModEq q a)
      (fun _ => 1 / (Nat.totient q : Real))
      (by
        intro a ha b hb hab n
        exact
          primeInModEq_disjoint
            (hRlt a ha) (hRlt b hb)
            hab n)
      (by
        intro a ha
        exact hPNT a (hRcoprime a ha))
  simpa [Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv] using hUnion

/-- The natural predicate underlying the periodic prime pool is exactly the
finite union of its CRT residue classes. -/
theorem primeNatPredicate_periodicPool_iff
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L)
    (n : Nat) :
    primeNatPredicate (InPeriodicPrimePool h L R) n ↔
      ∃ c ∈ R,
        PrimeInModEq (h.1 * L.1)
          (periodicCrtClass h L hcop c) n := by
  constructor
  · rintro ⟨hnPrime, hnPool⟩
    let p : Prime := ⟨n, hnPrime⟩
    obtain ⟨c, hcR, hnc⟩ :=
      (inPeriodicPrimePool_iff_exists_modEq
        h L hcop R hR p).1 hnPool
    exact ⟨c, hcR, hnPrime, hnc⟩
  · rintro ⟨c, hcR, hnPrime, hnc⟩
    let p : Prime := ⟨n, hnPrime⟩
    refine ⟨hnPrime, ?_⟩
    exact
      (inPeriodicPrimePool_iff_exists_modEq
        h L hcop R hR p).2
        ⟨c, hcR, hnc⟩

/-- CRT classes indexed by distinct reduced auxiliary residues are
pairwise disjoint. -/
theorem periodicCrtClasses_disjoint
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L) :
    ∀ a ∈ R, ∀ b ∈ R, a ≠ b →
      ∀ n, ¬
        (PrimeInModEq (h.1 * L.1)
            (periodicCrtClass h L hcop a) n ∧
          PrimeInModEq (h.1 * L.1)
            (periodicCrtClass h L hcop b) n) := by
  intro a ha b hb hab n hn
  have hnaMod :
      n ≡ a [MOD L.1] :=
    (hn.1.2.of_mul_left h.1).trans
      (periodicCrtClass_modEq_aux
        h L hcop a)
  have hnbMod :
      n ≡ b [MOD L.1] :=
    (hn.2.2.of_mul_left h.1).trans
      (periodicCrtClass_modEq_aux
        h L hcop b)
  have haLt : a < L.1 :=
    (mem_reducedResidues.mp (hR ha)).1
  have hbLt : b < L.1 :=
    (mem_reducedResidues.mp (hR hb)).1
  have hna : n % L.1 = a := by
    simpa [Nat.ModEq,
      Nat.mod_eq_of_lt haLt] using hnaMod
  have hnb : n % L.1 = b := by
    simpa [Nat.ModEq,
      Nat.mod_eq_of_lt hbLt] using hnbMod
  exact hab (hna.symm.trans hnb)

/-- Fixed-progression PNT for modulus `hL` gives the exact count-form
asymptotic for the full periodic pool `T₀`. -/
theorem periodicPrimePool_countingAsymptotic
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L)
    (hPNT :
      FixedProgressionPrimeNumberTheorem
        (h.1 * L.1)) :
    HasProjectPrimeCountingAsymptotic
      (InPeriodicPrimePool h L R)
      ((R.card : Real) /
        (Nat.totient (h.1 * L.1) : Real)) := by
  have hUnion :=
    hasPrimeCountingAsymptotic_exists_mem_finset
      R
      (fun c =>
        PrimeInModEq (h.1 * L.1)
          (periodicCrtClass h L hcop c))
      (fun _ =>
        1 /
          (Nat.totient (h.1 * L.1) : Real))
      (periodicCrtClasses_disjoint
        h L hcop R hR)
      (by
        intro c hc
        exact
          hPNT
            (periodicCrtClass h L hcop c)
            (periodicCrtClass_coprime_modulus
              h L hcop (hR hc)))
  have hPred :
      primeNatPredicate
          (InPeriodicPrimePool h L R) =
        (fun n =>
          ∃ c ∈ R,
            PrimeInModEq (h.1 * L.1)
              (periodicCrtClass h L hcop c) n) := by
    funext n
    apply propext
    exact
      primeNatPredicate_periodicPool_iff
        h L hcop R hR n
  unfold HasProjectPrimeCountingAsymptotic
  rw [hPred]
  simpa [Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv] using hUnion

/-- For prime coprime moduli, the analytic density denominator is exactly
`(h-1)(L-1)`. -/
theorem totient_hub_mul_aux
    (h L : Prime) (hcop : h.1.Coprime L.1) :
    Nat.totient (h.1 * L.1) =
      (h.1 - 1) * (L.1 - 1) := by
  rw [Nat.totient_mul hcop,
    Nat.totient_prime h.natPrime,
    Nat.totient_prime L.natPrime]

/-- Removing a finite set of primes below a fixed threshold does not change
the periodic pool's count-form asymptotic. -/
theorem periodicReservoir_countingAsymptotic
    (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L)
    (H : Finset Prime) (N : Nat)
    (hH : ∀ p ∈ H, p.1 < N)
    (hPNT :
      FixedProgressionPrimeNumberTheorem
        (h.1 * L.1)) :
    HasProjectPrimeCountingAsymptotic
      (InPeriodicReservoir h L R H)
      ((R.card : Real) /
        (Nat.totient (h.1 * L.1) : Real)) := by
  have hPool :=
    periodicPrimePool_countingAsymptotic
      h L hcop R hR hPNT
  unfold HasProjectPrimeCountingAsymptotic at hPool ⊢
  exact
    hPool.congr_of_eventually_iff N
      (by
        intro n hn
        constructor
        · rintro ⟨hnPrime, hnPool, hnH⟩
          exact ⟨hnPrime, hnPool⟩
        · rintro ⟨hnPrime, hnPool⟩
          refine ⟨hnPrime, hnPool, ?_⟩
          intro hpH
          let p : Prime := ⟨n, hnPrime⟩
          have hpLt : p.1 < N :=
            hH p hpH
          exact (Nat.not_lt_of_ge hn) hpLt)

/-- Hence, for a density mesh, fixed-progression PNT supplies the periodic
reservoir count with exactly the density stored in the mesh. -/
theorem mesh_periodicReservoir_countingAsymptotic
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hPNT :
      FixedProgressionPrimeNumberTheorem
        (h.1 * M.modulus.1)) :
    HasProjectPrimeCountingAsymptotic
      (InPeriodicReservoir
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff))
      M.periodicDensity := by
  have hcop :
      h.1.Coprime M.modulus.1 :=
    M.hub_coprime_modulus
  have hReservoir :=
    periodicReservoir_countingAsymptotic
      h M.modulus hcop
      M.classes M.classes_reduced
      (oldControllerPrimes h M.cutoff)
      (M.cutoff + 1)
      (by
        intro p hp
        have hpLe :
            p.1 ≤ M.cutoff :=
          (mem_oldControllerPrimes.mp hp).2
        omega)
      hPNT
  have hhReal :
      (h.1 : Real) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (Nat.ne_of_gt h.one_lt)
  have hLReal :
      (M.modulus.1 : Real) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast
      (Nat.ne_of_gt M.modulus.one_lt)
  have hDensity :
      ((M.classes.card : Real) /
          (Nat.totient
            (h.1 * M.modulus.1) : Real)) =
        M.periodicDensity := by
    rw [totient_hub_mul_aux
      h M.modulus hcop,
      M.card_classes]
    unfold
      OldControllerPrimeDensityMesh.periodicDensity
      controllerDensity
    rw [Nat.cast_mul,
      Nat.cast_sub h.one_lt.le,
      Nat.cast_sub M.modulus.one_lt.le]
    field_simp [hhReal, hLReal]
    ring
  rw [← hDensity]
  exact hReservoir

end Erdos279
