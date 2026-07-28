import Erdos279.MertensProducts
import Erdos279.SieveCRT
import Erdos279.ShiftedIntervalSelberg

/-!
# A two-shift ordinary sieve for controller-semigroup layers

After writing a controller-semigroup element as `u = h * n + 1`, every
prime up to the sieve cutoff excludes one residue class of `n`.  At the hub
prime we use either residue `0` or residue `1`; the two resulting ordinary
Selberg sieves cover every possible `n`.
-/

namespace Erdos279

/-- The forbidden class of the semigroup coordinate `u`, extended from old
controller primes to every prime: a non-controller prime forbids zero. -/
noncomputable def extendedUnitBadClassZMod
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (q : Prime) :
    ZMod q.1 := by
  classical
  exact
    if InControllerProgression h q then
      ((translatedPrimeClass h q e (a.residue q) : Nat) : ZMod q.1)
    else
      0

/-- The forbidden class of `n` in `u = h*n+1`.  Away from the hub it is
obtained by inverting `h`; at the hub it is the freely chosen class `j`. -/
noncomputable def unitQuotientBadClassZMod
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j : Nat) (q : Prime) :
    ZMod q.1 :=
  if q = h then
    (j : ZMod q.1)
  else
    (extendedUnitBadClassZMod e a q - 1) *
      ((h.1 : Nat) : ZMod q.1)⁻¹

/-- A natural representative of the forbidden quotient class. -/
noncomputable def unitQuotientBadClass
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j : Nat) (q : Prime) :
    Nat :=
  (unitQuotientBadClassZMod e a j q).val

/-- The CRT residue imposed on the translated interval.  Its negative makes
divisibility of `C+n` equivalent to `n` lying in the forbidden class. -/
noncomputable def unitSieveShiftResidue
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j : Nat) (q : Prime) :
    Nat :=
  (-unitQuotientBadClassZMod e a j q).val

/-- The simultaneous CRT shift for all primes at most `z`. -/
noncomputable def unitSieveShift
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j : Nat) :
    Nat :=
  (Nat.chineseRemainderOfFinset
    (unitSieveShiftResidue e a j)
    (fun q : Prime => q.1)
    (allPrimesUpTo z)
    (primeValues_ne_zero (allPrimesUpTo z))
    (primeValues_pairwise_coprime (allPrimesUpTo z))).1

theorem unitSieveShift_modEq
    {h : Prime} {z e j : Nat}
    (a : OldPrimeClasses h z) {q : Prime}
    (hqz : q.1 ≤ z) :
    unitSieveShift e a j ≡
      unitSieveShiftResidue e a j q [MOD q.1] := by
  exact
    (Nat.chineseRemainderOfFinset
      (unitSieveShiftResidue e a j)
      (fun r : Prime => r.1)
      (allPrimesUpTo z)
      (primeValues_ne_zero (allPrimesUpTo z))
      (primeValues_pairwise_coprime (allPrimesUpTo z))).2
        q (mem_allPrimesUpTo.mpr hqz)

@[simp]
theorem unitQuotientBadClass_cast
    {h : Prime} {z e j : Nat}
    (a : OldPrimeClasses h z) (q : Prime) :
    ((unitQuotientBadClass e a j q : Nat) : ZMod q.1) =
      unitQuotientBadClassZMod e a j q := by
  letI : NeZero q.1 := ⟨Nat.ne_of_gt q.pos⟩
  exact ZMod.natCast_zmod_val _

@[simp]
theorem unitSieveShiftResidue_cast
    {h : Prime} {z e j : Nat}
    (a : OldPrimeClasses h z) (q : Prime) :
    ((unitSieveShiftResidue e a j q : Nat) : ZMod q.1) =
      -unitQuotientBadClassZMod e a j q := by
  letI : NeZero q.1 := ⟨Nat.ne_of_gt q.pos⟩
  exact ZMod.natCast_zmod_val _

/-- Divisibility in the shifted interval is exactly membership in the
chosen forbidden quotient class. -/
theorem prime_dvd_unitSieveShift_add_iff
    {h : Prime} {z e j n : Nat}
    (a : OldPrimeClasses h z) {q : Prime}
    (hqz : q.1 ≤ z) :
    q.1 ∣ unitSieveShift e a j + n ↔
      ((n : Nat) : ZMod q.1) =
        unitQuotientBadClassZMod e a j q := by
  have hshift :
      ((unitSieveShift e a j : Nat) : ZMod q.1) =
        -unitQuotientBadClassZMod e a j q := by
    have hmod := unitSieveShift_modEq a (e := e) (j := j) hqz
    rw [← ZMod.natCast_eq_natCast_iff] at hmod
    simpa using hmod.trans (unitSieveShiftResidue_cast a q)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [hshift]
  constructor <;> intro hn
  · apply sub_eq_zero.mp
    simpa [sub_eq_add_neg, add_comm] using hn
  · rw [hn, neg_add_cancel]

/-- Distinct prime moduli make the hub invertible modulo `q`. -/
theorem hub_coprime_prime_of_ne
    {h q : Prime} (hqh : q ≠ h) :
    h.1.Coprime q.1 := by
  exact
    (Nat.coprime_primes h.natPrime q.natPrime).mpr
      (fun hv => hqh (Subtype.ext hv.symm))

/-- Away from the hub, substituting the forbidden quotient class in
`h*n+1` gives the extended forbidden class of `u`. -/
theorem hub_mul_unitQuotientBadClass_add_one
    {h : Prime} {z e j : Nat}
    (a : OldPrimeClasses h z) {q : Prime}
    (hqh : q ≠ h) :
    ((h.1 : Nat) : ZMod q.1) *
          unitQuotientBadClassZMod e a j q + 1 =
        extendedUnitBadClassZMod e a q := by
  have hinv :
      ((h.1 : Nat) : ZMod q.1) *
          ((h.1 : Nat) : ZMod q.1)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one h.1
      (hub_coprime_prime_of_ne hqh)
  rw [unitQuotientBadClassZMod, if_neg hqh]
  calc
    ((h.1 : Nat) : ZMod q.1) *
          ((extendedUnitBadClassZMod e a q - 1) *
            ((h.1 : Nat) : ZMod q.1)⁻¹) + 1 =
        (extendedUnitBadClassZMod e a q - 1) *
            (((h.1 : Nat) : ZMod q.1) *
              ((h.1 : Nat) : ZMod q.1)⁻¹) + 1 := by ring
    _ = extendedUnitBadClassZMod e a q := by
      rw [hinv]
      ring

/-- A semigroup element avoiding the old translated controller classes
produces a sifted quotient point, provided the freely chosen hub class is
also avoided. -/
theorem unitSieveShift_add_coprime
    {h : Prime} {z e j u n : Nat}
    (a : OldPrimeClasses h z)
    (hu : ControllerSemigroup h u)
    (hun : u = h.1 * n + 1)
    (hav : AvoidsOldClasses (translatedOldPrimeClasses e a) u)
    (hhub :
      ((n : Nat) : ZMod h.1) ≠ (j : ZMod h.1)) :
    (unitSieveShift e a j + n).Coprime (primorial z) := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpShift hpPrimorial
  let q : Prime := ⟨p, (isPrime_iff_natPrime p).mpr hp⟩
  have hqz : q.1 ≤ z :=
    (Sieve.prime_dvd_primorial_iff z p hp).mp hpPrimorial
  have hnotBad :
      ((n : Nat) : ZMod q.1) ≠
        unitQuotientBadClassZMod e a j q := by
    by_cases hqh : q = h
    · subst h
      simpa [unitQuotientBadClassZMod] using hhub
    · intro hnBad
      have huBad :
          ((u : Nat) : ZMod q.1) =
            extendedUnitBadClassZMod e a q := by
        calc
          ((u : Nat) : ZMod q.1) =
              ((h.1 : Nat) : ZMod q.1) *
                  ((n : Nat) : ZMod q.1) + 1 := by
            rw [hun]
            push_cast
            rfl
          _ = ((h.1 : Nat) : ZMod q.1) *
                  unitQuotientBadClassZMod e a j q + 1 := by
            rw [hnBad]
          _ = extendedUnitBadClassZMod e a q :=
            hub_mul_unitQuotientBadClass_add_one a hqh
      by_cases hqG : InControllerProgression h q
      · apply hav q hqG hqz
        change
          u % q.1 =
            (translatedPrimeClass h q e (a.residue q) : Nat)
        have heqmod :=
          (ZMod.natCast_eq_natCast_iff' u
            (translatedPrimeClass h q e (a.residue q) : Nat)
            q.1).mp
            (by
              simpa [extendedUnitBadClassZMod, hqG] using huBad)
        simpa [Nat.mod_eq_of_lt
          (translatedPrimeClass h q e (a.residue q)).isLt] using heqmod
      · apply hqG
        apply hu.primeDivisor_mem
        apply (ZMod.natCast_eq_zero_iff u q.1).mp
        simpa [extendedUnitBadClassZMod, hqG] using huBad
  exact hnotBad
    ((prime_dvd_unitSieveShift_add_iff a hqz).mp hpShift)

/-- The canonical quotient in `u = h * (u/h) + 1`. -/
theorem ControllerSemigroup.eq_hub_mul_div_add_one
    {h : Prime} {u : Nat}
    (hu : ControllerSemigroup h u) :
    u = h.1 * (u / h.1) + 1 := by
  have hdivmod := Nat.div_add_mod u h.1
  rw [hu.mod_h_eq_one] at hdivmod
  omega

/-- Division by the hub is injective on controller-semigroup elements. -/
theorem controllerSemigroup_div_hub_injective
    {h : Prime} :
    Set.InjOn (fun u : Nat => u / h.1)
      {u | ControllerSemigroup h u} := by
  intro u hu v hv huv
  change u / h.1 = v / h.1 at huv
  rw [hu.eq_hub_mul_div_add_one,
    hv.eq_hub_mul_div_add_one, huv]

@[simp]
theorem unitQuotientBadClassZMod_hub
    {h : Prime} {z e j : Nat}
    (a : OldPrimeClasses h z) :
    unitQuotientBadClassZMod e a j h =
      (j : ZMod h.1) := by
  simp [unitQuotientBadClassZMod]

/-- One of the two ordinary sifted quotient sets. -/
noncomputable def unitQuotientSiftedSet
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j Z : Nat) :
    Finset Nat := by
  classical
  exact
    (Finset.range (Z / h.1 + 1)).filter fun n =>
      (unitSieveShift e a j + n).Coprime (primorial z)

/-- Every translated hard-layer unit maps into the union of the two
ordinary quotient sieves. -/
theorem hardLayerUnit_div_mem_dualSieve
    {h : Prime} {z e Y Z u : Nat}
    {a : OldPrimeClasses h z}
    (huMem : u ∈ hardLayerUnits h z e a Y Z) :
    u / h.1 ∈
      unitQuotientSiftedSet e a 0 Z ∪
        unitQuotientSiftedSet e a 1 Z := by
  classical
  have huData :
      Y < u ∧ u ≤ Z ∧ ControllerSemigroup h u ∧
        AvoidsOldClasses a (h.1 ^ e * u) := by
    simpa [hardLayerUnits, mem_controllerElements, and_assoc] using huMem
  rcases huData with ⟨_hYu, huZ, huG, huAvoid⟩
  have huAvoidTranslated :
      AvoidsOldClasses (translatedOldPrimeClasses e a) u :=
    (avoidsOldClasses_hubPower_mul_iff a).mp huAvoid
  have hnRange : u / h.1 < Z / h.1 + 1 := by
    exact Nat.lt_succ_of_le (Nat.div_le_div_right huZ)
  have huEq : u = h.1 * (u / h.1) + 1 :=
    huG.eq_hub_mul_div_add_one
  letI : NeZero h.1 := ⟨Nat.ne_of_gt h.pos⟩
  by_cases hnZero :
      (((u / h.1 : Nat) : ZMod h.1) = 0)
  · rw [Finset.mem_union]
    right
    rw [unitQuotientSiftedSet, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hnRange, ?_⟩
    apply unitSieveShift_add_coprime a huG huEq huAvoidTranslated
    intro hnOne
    have hnZeroMod :
        (u / h.1) % h.1 = 0 % h.1 := by
      apply (ZMod.natCast_eq_natCast_iff'
        (u / h.1) 0 h.1).mp
      simpa using hnZero
    have hnOneMod :
        (u / h.1) % h.1 = 1 % h.1 := by
      apply (ZMod.natCast_eq_natCast_iff'
        (u / h.1) 1 h.1).mp
      simpa using hnOne
    simp only [Nat.zero_mod] at hnZeroMod
    rw [Nat.mod_eq_of_lt h.one_lt] at hnOneMod
    omega
  · rw [Finset.mem_union]
    left
    rw [unitQuotientSiftedSet, Finset.mem_filter]
    refine
      ⟨Finset.mem_range.mpr hnRange,
        unitSieveShift_add_coprime a huG huEq huAvoidTranslated ?_⟩
    simpa only [Nat.cast_zero] using hnZero

/-- Cardinality comparison before applying the analytic Selberg bound. -/
theorem hardLayerUnits_card_le_dualSieve
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat) :
    (hardLayerUnits h z e a Y Z).card ≤
      (unitQuotientSiftedSet e a 0 Z).card +
        (unitQuotientSiftedSet e a 1 Z).card := by
  classical
  calc
    (hardLayerUnits h z e a Y Z).card ≤
        (unitQuotientSiftedSet e a 0 Z ∪
          unitQuotientSiftedSet e a 1 Z).card := by
      apply Finset.card_le_card_of_injOn (fun u : Nat => u / h.1)
      · intro u hu
        exact hardLayerUnit_div_mem_dualSieve hu
      · intro u hu v hv huv
        have huData :
            (Y < u ∧ u ≤ Z ∧ ControllerSemigroup h u) ∧
              AvoidsOldClasses a (h.1 ^ e * u) := by
          simpa [hardLayerUnits, mem_controllerElements] using hu
        have hvData :
            (Y < v ∧ v ≤ Z ∧ ControllerSemigroup h v) ∧
              AvoidsOldClasses a (h.1 ^ e * v) := by
          simpa [hardLayerUnits, mem_controllerElements] using hv
        exact
          controllerSemigroup_div_hub_injective
            (h := h) huData.1.2.2 hvData.1.2.2 huv
    _ ≤ (unitQuotientSiftedSet e a 0 Z).card +
          (unitQuotientSiftedSet e a 1 Z).card :=
      Finset.card_union_le _ _

/-- Explicit real-valued bound for every hard layer, uniform in the
correlated old residue classes and in the exponent. -/
theorem hardLayerUnits_card_real_le
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat) (hz : 2 ≤ z) :
    ((hardLayerUnits h z e a Y Z).card : Real) ≤
      4 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
        2 * ((z : Real) * (1 + Real.log z) ^ 3) := by
  have hcard :
      ((hardLayerUnits h z e a Y Z).card : Real) ≤
        ((unitQuotientSiftedSet e a 0 Z).card : Real) +
          ((unitQuotientSiftedSet e a 1 Z).card : Real) := by
    exact_mod_cast hardLayerUnits_card_le_dualSieve h z e a Y Z
  have hzero :=
    shiftedInterval_sifted_card_le
      (unitSieveShift e a 0) (Z / h.1) z hz
  have hone :=
    shiftedInterval_sifted_card_le
      (unitSieveShift e a 1) (Z / h.1) z hz
  change
    ((unitQuotientSiftedSet e a 0 Z).card : Real) ≤
      2 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
        (z : Real) * (1 + Real.log z) ^ 3 at hzero
  change
    ((unitQuotientSiftedSet e a 1 Z).card : Real) ≤
      2 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
        (z : Real) * (1 + Real.log z) ^ 3 at hone
  calc
    ((hardLayerUnits h z e a Y Z).card : Real) ≤
        ((unitQuotientSiftedSet e a 0 Z).card : Real) +
          ((unitQuotientSiftedSet e a 1 Z).card : Real) := hcard
    _ ≤
        (2 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
          (z : Real) * (1 + Real.log z) ^ 3) +
        (2 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
          (z : Real) * (1 + Real.log z) ^ 3) :=
      add_le_add hzero hone
    _ =
        4 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
          2 * ((z : Real) * (1 + Real.log z) ^ 3) := by ring

theorem hardLayerUnits_card_real_le_simpler
    (h : Prime) (z e : Nat)
    (a : OldPrimeClasses h z)
    (Y Z : Nat) (hz : 2 ≤ z) :
    ((hardLayerUnits h z e a Y Z).card : Real) ≤
      4 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
        2 * (z : Real) * (1 + Real.log z) ^ 3 := by
  simpa [mul_assoc] using
    hardLayerUnits_card_real_le h z e a Y Z hz

end Erdos279
