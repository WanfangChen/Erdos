import Mathlib.Data.Nat.ChineseRemainder
import Erdos279.LocalDensity

/-!
# Translated progression classes

For a hard-form integer `n = h^e u`, the old congruence conditions on `n`
become congruence conditions on the semigroup variable `u`.  This file
formalizes the elementary CRT step used in Section 2.1 of the paper.
-/

namespace Erdos279

/--
The canonical CRT lift of a class `b mod d` to the simultaneous classes
`b mod d` and `1 mod h`.  The semigroup hypothesis supplies `(d,h)=1`.
-/
noncomputable def translatedCrtLift
    (h : Prime) (d b : Nat)
    (hd : ControllerSemigroup h d) : Nat :=
  (Nat.chineseRemainder hd.coprime_hub b 1).1

theorem translatedCrtLift_modEq_d
    (h : Prime) (d b : Nat)
    (hd : ControllerSemigroup h d) :
    translatedCrtLift h d b hd ≡ b [MOD d] := by
  simpa [translatedCrtLift] using
    (Nat.chineseRemainder hd.coprime_hub b 1).2.1

theorem translatedCrtLift_modEq_h
    (h : Prime) (d b : Nat)
    (hd : ControllerSemigroup h d) :
    translatedCrtLift h d b hd ≡ 1 [MOD h.1] := by
  simpa [translatedCrtLift] using
    (Nat.chineseRemainder hd.coprime_hub b 1).2.2

theorem translatedCrtLift_lt
    (h : Prime) (d b : Nat)
    (hd : ControllerSemigroup h d) :
    translatedCrtLift h d b hd < d * h.1 := by
  exact Nat.chineseRemainder_lt_mul hd.coprime_hub b 1
    (Nat.ne_of_gt hd.pos) (Nat.ne_of_gt h.pos)

/--
A residue class modulo `d` that is coprime to `d` remains coprime after the
CRT lift.
-/
theorem translatedCrtLift_coprime_d
    (h : Prime) (d b : Nat)
    (hd : ControllerSemigroup h d)
    (hb : b.Coprime d) :
    (translatedCrtLift h d b hd).Coprime d := by
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd (translatedCrtLift h d b hd) d =
        Nat.gcd d (translatedCrtLift h d b hd) :=
      Nat.gcd_comm _ _
    _ = Nat.gcd ((translatedCrtLift h d b hd) % d) d :=
      Nat.gcd_rec d (translatedCrtLift h d b hd)
    _ = Nat.gcd (b % d) d := by
      rw [translatedCrtLift_modEq_d h d b hd]
    _ = Nat.gcd d b := (Nat.gcd_rec d b).symm
    _ = Nat.gcd b d := Nat.gcd_comm _ _
    _ = 1 := hb.gcd_eq_one

/-- The CRT lift is also coprime to the hub prime. -/
theorem translatedCrtLift_coprime_h
    (h : Prime) (d b : Nat)
    (hd : ControllerSemigroup h d) :
    (translatedCrtLift h d b hd).Coprime h.1 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd (translatedCrtLift h d b hd) h.1 =
        Nat.gcd h.1 (translatedCrtLift h d b hd) :=
      Nat.gcd_comm _ _
    _ = Nat.gcd ((translatedCrtLift h d b hd) % h.1) h.1 :=
      Nat.gcd_rec h.1 (translatedCrtLift h d b hd)
    _ = Nat.gcd (1 % h.1) h.1 := by
      rw [translatedCrtLift_modEq_h h d b hd]
    _ = Nat.gcd 1 h.1 := by rw [Nat.mod_eq_of_lt h.one_lt]
    _ = 1 := Nat.gcd_one_left h.1

/--
The lifted class is reduced modulo the combined modulus `d*h`, which is the
coprimality condition required for the fixed-progression estimate.
-/
theorem translatedCrtLift_coprime_mul
    (h : Prime) (d b : Nat)
    (hd : ControllerSemigroup h d)
    (hb : b.Coprime d) :
    (translatedCrtLift h d b hd).Coprime (d * h.1) := by
  exact Nat.coprime_mul_iff_right.mpr
    ⟨translatedCrtLift_coprime_d h d b hd hb,
      translatedCrtLift_coprime_h h d b hd⟩

end Erdos279
