import Erdos279.TranslatedProgressions

/-!
# Translation of old prime residue classes

This file proves the exact congruence translation in equation (2.2) of the
paper.  No analytic estimate is used.
-/

namespace Erdos279

/-- A power of the hub is coprime to every prime in the controller progression. -/
theorem hubPower_coprime_controllerPrime
    {h p : Prime} (e : Nat)
    (hp : InControllerProgression h p) :
    (h.1 ^ e).Coprime p.1 := by
  have hnotdvd : ¬p.1 ∣ h.1 :=
    Nat.not_dvd_of_pos_of_lt h.pos
      (hub_lt_of_inControllerProgression hp)
  have hcop : h.1.Coprime p.1 := by
    rw [Nat.coprime_comm, p.natPrime.coprime_iff_not_dvd]
    exact hnotdvd
  exact hcop.pow_left e

/--
The translated class as an element of `ZMod p`.  The explicit inverse is
available for every modulus; coprimality below proves that it is a genuine
multiplicative inverse in the case used by the paper.
-/
noncomputable def translatedPrimeClassZMod
    (h p : Prime) (e : Nat) (a : Fin p.1) : ZMod p.1 :=
  ((a : Nat) : ZMod p.1) * (((h.1 ^ e : Nat) : ZMod p.1)⁻¹)

theorem hubPower_mul_translatedPrimeClassZMod
    {h p : Prime} (e : Nat) (a : Fin p.1)
    (hp : InControllerProgression h p) :
    (((h.1 ^ e : Nat) : ZMod p.1) *
        translatedPrimeClassZMod h p e a) =
      ((a : Nat) : ZMod p.1) := by
  have hinv :
      (((h.1 ^ e : Nat) : ZMod p.1) *
          (((h.1 ^ e : Nat) : ZMod p.1)⁻¹)) = 1 :=
    ZMod.coe_mul_inv_eq_one (h.1 ^ e)
      (hubPower_coprime_controllerPrime e hp)
  calc
    ((h.1 ^ e : Nat) : ZMod p.1) *
          translatedPrimeClassZMod h p e a =
        ((a : Nat) : ZMod p.1) *
          (((h.1 ^ e : Nat) : ZMod p.1) *
            (((h.1 ^ e : Nat) : ZMod p.1)⁻¹)) := by
      simp only [translatedPrimeClassZMod]
      ac_rfl
    _ = ((a : Nat) : ZMod p.1) * 1 := by rw [hinv]
    _ = ((a : Nat) : ZMod p.1) := mul_one _

/-- The canonical natural representative of the translated class. -/
noncomputable def translatedPrimeClass
    (h p : Prime) (e : Nat) (a : Fin p.1) : Fin p.1 := by
  letI : NeZero p.1 := ⟨Nat.ne_of_gt p.pos⟩
  exact
    ⟨(translatedPrimeClassZMod h p e a).val,
      ZMod.val_lt (translatedPrimeClassZMod h p e a)⟩

/-- Multiplying the translated class by `h^e` gives the old class modulo `p`. -/
theorem hubPower_mul_translatedPrimeClass_modEq
    {h p : Prime} (e : Nat) (a : Fin p.1)
    (hp : InControllerProgression h p) :
    h.1 ^ e * (translatedPrimeClass h p e a : Nat) ≡
      (a : Nat) [MOD p.1] := by
  letI : NeZero p.1 := ⟨Nat.ne_of_gt p.pos⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [Nat.cast_mul]
  simp only [translatedPrimeClass]
  rw [ZMod.natCast_zmod_val]
  exact hubPower_mul_translatedPrimeClassZMod e a hp

/-- A nonzero old class translates to a nonzero class. -/
theorem translatedPrimeClass_ne_zero
    {h p : Prime} (e : Nat) (a : Fin p.1)
    (hp : InControllerProgression h p)
    (ha : (a : Nat) ≠ 0) :
    (translatedPrimeClass h p e a : Nat) ≠ 0 := by
  letI : NeZero p.1 := ⟨Nat.ne_of_gt p.pos⟩
  intro hz
  have hzval : (translatedPrimeClassZMod h p e a).val = 0 := by
    simpa [translatedPrimeClass] using hz
  have hzmod : translatedPrimeClassZMod h p e a = 0 :=
    (ZMod.val_eq_zero (translatedPrimeClassZMod h p e a)).mp hzval
  have hacast : ((a : Nat) : ZMod p.1) = 0 := by
    rw [← hubPower_mul_translatedPrimeClassZMod e a hp, hzmod, mul_zero]
  have hadiv : p.1 ∣ (a : Nat) :=
    (ZMod.natCast_eq_zero_iff (a : Nat) p.1).mp hacast
  have ha0 : (a : Nat) = 0 :=
    Nat.eq_zero_of_dvd_of_lt hadiv a.isLt
  exact ha ha0

/--
The exact translated-congruence equivalence.  This is the formal content of
`h^e u ≡ a_p (mod p) ⇔ u ≡ b_{e,p} (mod p)`.
-/
theorem hubPower_mul_modEq_old_iff
    {h p : Prime} (e u : Nat) (a : Fin p.1)
    (hp : InControllerProgression h p) :
    h.1 ^ e * u ≡ (a : Nat) [MOD p.1] ↔
      u ≡ (translatedPrimeClass h p e a : Nat) [MOD p.1] := by
  have htranslated :=
    hubPower_mul_translatedPrimeClass_modEq e a hp
  have hgcd : Nat.gcd p.1 (h.1 ^ e) = 1 := by
    rw [Nat.gcd_comm]
    exact (hubPower_coprime_controllerPrime e hp).gcd_eq_one
  constructor
  · intro hu
    exact Nat.ModEq.cancel_left_of_coprime hgcd
      (hu.trans htranslated.symm)
  · intro hu
    exact (hu.mul_left (h.1 ^ e)).trans htranslated

/-- Translate a whole correlated vector of old prime classes at exponent `e`. -/
noncomputable def translatedOldPrimeClasses
    {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) :
    OldPrimeClasses h z where
  residue p := translatedPrimeClass h p e (a.residue p)
  nonzero p hp hpz :=
    translatedPrimeClass_ne_zero e (a.residue p) hp
      (a.nonzero p hp hpz)

/-- Avoiding the old classes after multiplication is exactly avoiding their translation. -/
theorem avoidsOldClasses_hubPower_mul_iff
    {h : Prime} {z e u : Nat}
    (a : OldPrimeClasses h z) :
    AvoidsOldClasses a (h.1 ^ e * u) ↔
      AvoidsOldClasses (translatedOldPrimeClasses e a) u := by
  constructor
  · intro hav p hp hpz
    intro heq
    apply hav p hp hpz
    have heq' :
        u ≡ (translatedPrimeClass h p e (a.residue p) : Nat)
          [MOD p.1] := by
      change u % p.1 =
        (translatedPrimeClass h p e (a.residue p) : Nat) % p.1
      simpa [translatedOldPrimeClasses,
        Nat.mod_eq_of_lt
          (translatedPrimeClass h p e (a.residue p)).isLt] using heq
    have hout :=
      (hubPower_mul_modEq_old_iff e u (a.residue p) hp).mpr heq'
    change (h.1 ^ e * u) % p.1 = (a.residue p : Nat) % p.1 at hout
    simpa [Nat.mod_eq_of_lt (a.residue p).isLt] using hout
  · intro hav p hp hpz
    intro heq
    apply hav p hp hpz
    have heq' :
        h.1 ^ e * u ≡ (a.residue p : Nat) [MOD p.1] := by
      change (h.1 ^ e * u) % p.1 = (a.residue p : Nat) % p.1
      simpa [Nat.mod_eq_of_lt (a.residue p).isLt] using heq
    have hout :=
      (hubPower_mul_modEq_old_iff e u (a.residue p) hp).mp heq'
    change u % p.1 =
      (translatedPrimeClass h p e (a.residue p) : Nat) % p.1 at hout
    simpa [translatedOldPrimeClasses,
      Nat.mod_eq_of_lt
        (translatedPrimeClass h p e (a.residue p)).isLt] using hout

end Erdos279
