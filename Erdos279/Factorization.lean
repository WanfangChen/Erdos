import Erdos279.ControllerValidity

/-!
Elementary factorization lemmas needed by the controller construction.
Everything here is proved from the internal pure-`Std` primality predicate.
-/

namespace Erdos279

/-- A prime not dividing `n` is coprime to `n`. -/
theorem isPrime_coprime_of_not_dvd
    {p n : Nat} (hp : IsPrime p) (hpn : ¬ p ∣ n) :
    Nat.Coprime p n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases hp.2 (Nat.gcd p n) (Nat.gcd_dvd_left p n) with hgcd | hgcd
  · exact hgcd
  · exfalso
    apply hpn
    rw [← hgcd]
    exact Nat.gcd_dvd_right p n

/-- Euclid's lemma for the internal pure-`Std` primality predicate. -/
theorem isPrime_dvd_mul
    {p a b : Nat} (hp : IsPrime p) (hab : p ∣ a * b) :
    p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · exact Or.inr ((isPrime_coprime_of_not_dvd hp hpa).dvd_of_dvd_mul_left hab)

/-- A prime dividing a power divides its base. -/
theorem isPrime_dvd_pow
    {p a e : Nat} (hp : IsPrime p) (hpow : p ∣ a ^ e) :
    p ∣ a := by
  induction e with
  | zero =>
      have hpone : p = 1 := Nat.dvd_one.mp (by simpa using hpow)
      have hp2 : 2 ≤ p := hp.1
      omega
  | succ e ih =>
      rw [Nat.pow_succ] at hpow
      rcases isPrime_dvd_mul hp hpow with hrest | hbase
      · exact ih hrest
      · exact hbase

/-- Every natural number greater than one has an internal prime divisor. -/
theorem exists_isPrime_dvd
    {n : Nat} (hn : 1 < n) :
    ∃ p : Prime, p.1 ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hp : IsPrime n
      · exact ⟨⟨n, hp⟩, Nat.dvd_refl n⟩
      · have hn2 : 2 ≤ n := hn
        have hproper :
            ∃ d : Nat, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
          apply Classical.byContradiction
          intro hnone
          apply hp
          refine ⟨hn2, ?_⟩
          intro d hd
          by_cases hd1 : d = 1
          · exact Or.inl hd1
          · by_cases hdn : d = n
            · exact Or.inr hdn
            · exfalso
              apply hnone
              exact ⟨d, hd, hd1, hdn⟩
        rcases hproper with ⟨d, hdn, hd1, hdne⟩
        have hnpos : 0 < n := by omega
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hnpos
        have hdlt : d < n :=
          Nat.lt_of_le_of_ne (Nat.le_of_dvd hnpos hdn) hdne
        have hdgt : 1 < d := by omega
        rcases ih d hdlt hdgt with ⟨q, hqd⟩
        exact ⟨q, Nat.dvd_trans hqd hdn⟩

/-- A controller-progression prime cannot be the hub itself. -/
theorem inControllerProgression_ne_hub
    {h p : Prime} (hp : InControllerProgression h p) :
    p ≠ h := by
  intro hph
  subst p
  simp [InControllerProgression] at hp

/-- In fact every prime in the controller progression is strictly above the hub. -/
theorem hub_lt_of_inControllerProgression
    {h p : Prime} (hp : InControllerProgression h p) :
    h.1 < p.1 := by
  have hpne : p ≠ h := inControllerProgression_ne_hub hp
  have hnotlt : ¬ p.1 < h.1 := by
    intro hplt
    have hpone : p.1 = 1 := by
      have := hp
      rw [InControllerProgression, Nat.mod_eq_of_lt hplt] at this
      exact this
    have hp2 := p.two_le
    omega
  have hle : h.1 ≤ p.1 := Nat.le_of_not_gt hnotlt
  have hvalne : p.1 ≠ h.1 := by
    intro heq
    apply hpne
    exact Subtype.ext heq
  exact Nat.lt_of_le_of_ne hle (Ne.symm hvalne)

/-- Every certified controller-semigroup element is positive. -/
theorem ControllerSemigroup.pos
    {h : Prime} {u : Nat} (hu : ControllerSemigroup h u) :
    0 < u := by
  induction hu with
  | one => omega
  | mul p hp hu ih =>
      exact Nat.mul_pos p.pos ih

/-- A prime divisor of a prime is that prime. -/
theorem prime_dvd_prime_eq
    {p q : Prime} (hpq : p.1 ∣ q.1) :
    p = q := by
  rcases q.2.2 p.1 hpq with hpone | hpqeq
  · have hp2 := p.two_le
    omega
  · exact Subtype.ext hpqeq

/-- A smaller prime has nonzero residue modulo a larger prime target. -/
theorem prime_mod_prime_ne_zero_of_lt
    {p q : Prime} (hpq : p.1 < q.1) :
    q.1 % p.1 ≠ 0 := by
  intro hzero
  have hpdivq : p.1 ∣ q.1 :=
    Nat.dvd_of_mod_eq_zero hzero
  have hpEq : p = q :=
    prime_dvd_prime_eq hpdivq
  subst q
  exact Nat.lt_irrefl p.1 hpq

/--
If a controller prime divides a hard-form target, its complementary factor
is at least the hub.  This discharges the hypothesis previously exposed in
`controllerResidue_ne_zero`.
-/
theorem hasHardForm_controller_cofactor_ge_hub
    {h p : Prime} {m : Nat}
    (hm : HasHardForm h m)
    (hpG : InControllerProgression h p)
    (hpm : p.1 ∣ m) :
    h.1 ≤ m / p.1 := by
  rcases hm with ⟨e, u, he, hu, rfl⟩
  have hpne : p ≠ h := inControllerProgression_ne_hub hpG
  have hpnotdivh : ¬ p.1 ∣ h.1 := by
    intro hph
    exact hpne (prime_dvd_prime_eq hph)
  have hpnotpow : ¬ p.1 ∣ h.1 ^ e := by
    intro hppow
    exact hpnotdivh (isPrime_dvd_pow p.2 hppow)
  have hpu : p.1 ∣ u := by
    rcases isPrime_dvd_mul p.2 hpm with hppow | hpu
    · exact False.elim (hpnotpow hppow)
    · exact hpu
  have hupos : 0 < u := hu.pos
  have hp_le_u : p.1 ≤ u := Nat.le_of_dvd hupos hpu
  have hquotpos : 0 < u / p.1 := Nat.div_pos hp_le_u p.pos
  have hhubpow : h.1 ≤ h.1 ^ e := Nat.le_pow (by omega)
  calc
    h.1 ≤ h.1 ^ e := hhubpow
    _ ≤ h.1 ^ e * (u / p.1) :=
      Nat.le_mul_of_pos_right (h.1 ^ e) hquotpos
    _ = (h.1 ^ e * u) / p.1 :=
      (Nat.mul_div_assoc (h.1 ^ e) hpu).symm

/--
The elementary fourth-case classification: above `k²`, if a target is not
`{h} ∪ G`-smooth but has no mature outside prime divisor, then the target
itself is prime.
-/
theorem outsideLarge_isPrime
    {k m : Nat} {h : Prime}
    (hk : 3 ≤ k)
    (hkh : k < h.1)
    (hlarge : k * k < m)
    (hnonsmooth : ¬ SmoothFor h m)
    (hnosmall : ¬ HasSmallOutsideFactor k h m) :
    IsPrime m := by
  have houtside :
      ∃ q : Prime,
        q.1 ∣ m ∧ q ≠ h ∧ ¬ InControllerProgression h q := by
    apply Classical.byContradiction
    intro hnone
    apply hnonsmooth
    intro q hqm
    by_cases hqh : q = h
    · exact Or.inl hqh
    · right
      apply Classical.byContradiction
      intro hqG
      apply hnone
      exact ⟨q, hqm, hqh, hqG⟩
  rcases houtside with ⟨q, hqm, hqne, hqout⟩
  have hmpos : 0 < m := by omega
  have hqle : q.1 ≤ m := Nat.le_of_dvd hmpos hqm
  let c : Nat := m / q.1
  have hcpos : 0 < c := Nat.div_pos hqle q.pos
  have hmc : m = q.1 * c := by
    exact (Nat.mul_div_cancel' hqm).symm
  have hnotmature : ¬ k * q.1 ≤ m := by
    intro hkq
    apply hnosmall
    exact ⟨q, hqm, hqne, hqout, hkq⟩
  have hmlt : m < k * q.1 := Nat.lt_of_not_ge hnotmature
  have hclt : c < k := by
    apply (Nat.mul_lt_mul_left q.pos).mp
    simpa [hmc, Nat.mul_comm] using hmlt
  have hkltq : k < q.1 := by
    apply Classical.byContradiction
    intro hnlt
    have hqk : q.1 ≤ k := Nat.le_of_not_gt hnlt
    have hmkk : m < k * k := by
      rw [hmc]
      exact Nat.mul_lt_mul_of_le_of_lt hqk hclt (by omega)
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hlarge)) hmkk
  have hc1 : c = 1 := by
    apply Classical.byContradiction
    intro hcne
    have hcgt : 1 < c := by omega
    rcases exists_isPrime_dvd hcgt with ⟨r, hrc⟩
    have hrle : r.1 ≤ c := Nat.le_of_dvd hcpos hrc
    have hrltk : r.1 < k := Nat.lt_of_le_of_lt hrle hclt
    have hrneh : r ≠ h := by
      intro hrh
      have : h.1 < h.1 := by
        simpa [hrh] using Nat.lt_trans hrltk hkh
      exact Nat.lt_irrefl _ this
    have hrout : ¬ InControllerProgression h r := by
      intro hrG
      have hhlt := hub_lt_of_inControllerProgression hrG
      exact (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hrltk hkh))) hhlt
    have hcm : c ∣ m := by
      rw [hmc]
      exact Nat.dvd_mul_left c q.1
    have hrm : r.1 ∣ m := Nat.dvd_trans hrc hcm
    have hkrm : k * r.1 ≤ m := by
      rw [hmc]
      exact Nat.mul_le_mul (Nat.le_of_lt hkltq) hrle
    apply hnosmall
    exact ⟨r, hrm, hrneh, hrout, hkrm⟩
  have hmq : m = q.1 := by
    simpa [hc1] using hmc
  rw [hmq]
  exact q.2

/-- The causal-backup theorem with its prime-factor premise discharged. -/
theorem causal_backup_witness_unconditional
    {k c : Nat} {h p : Prime} {a : ShiftedAssignment}
    (hcpos : 1 ≤ c)
    (hclt : c < h.1)
    (hpG : InControllerProgression h p)
    (hpLarge : k * h.1 < p.1)
    (hah : (a h : Nat) = 1)
    (hsmallZero :
      ∀ d : Prime, d.1 < h.1 → (a d : Nat) = 0) :
    ShiftedMatureCovers k (c * p.1) a :=
  causal_backup_witness hcpos hclt hpG hpLarge hah hsmallZero
    (fun hc => exists_isPrime_dvd hc)

/--
For a hard-form target, the abstract cofactor premise of
`controllerResidue_ne_zero` follows from factorization.
-/
theorem hardForm_controllerResidue_ne_zero
    {h p : Prime} {m : Nat}
    (hm : HasHardForm h m)
    (hpG : InControllerProgression h p)
    (hpLower : m / h.1 < p.1) :
    (controllerResidue p m : Nat) ≠ 0 :=
  controllerResidue_ne_zero hpLower
    (fun hpm => hasHardForm_controller_cofactor_ge_hub hm hpG hpm)

/--
Combined controller-validity lemma in the exact annular form used by the
construction: the installed residue is nonzero and covers its hard target.
-/
theorem hardForm_controller_pair_valid
    {k X m : Nat} {h p : Prime} {a : ShiftedAssignment}
    (hk : 0 < k)
    (hm : HasHardForm h m)
    (hpG : InControllerProgression h p)
    (hpLower : m / h.1 < p.1)
    (hpUpper : p.1 ≤ X / k)
    (hXm : X < m)
    (ha : (a p : Nat) = (controllerResidue p m : Nat)) :
    (controllerResidue p m : Nat) ≠ 0 ∧
      ShiftedMatureCovers k m a := by
  refine ⟨hardForm_controllerResidue_ne_zero hm hpG hpLower, ?_⟩
  exact controller_pair_covers
    (controller_mature_from_annulus hk hpUpper hXm) ha

end Erdos279
