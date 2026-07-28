import Erdos279.External.SieveSelbergBounds
import Mathlib.Data.Int.CardIntervalMod

/-!
# A Selberg bound for a translated natural interval

This module specializes the general Selberg sieve to
`{C, C + 1, ..., C + N}` with unit weights and local density `1 / d`.
The divisibility count in every modulus differs from its expected value by
at most one.
-/

namespace Erdos279

open Finset Real Nat
open scoped BigOperators ArithmeticFunction
open BoundingSieve

/-- The unit-weight Selberg sieve on a translated interval. -/
noncomputable def shiftedIntervalSelbergSieve
    (C N z : Nat) (hz : 1 ≤ z) : SelbergSieve where
  support :=
    (Finset.range (N + 1)).image fun n => C + n
  prodPrimes := primorial z
  prodPrimes_squarefree := Sieve.primorial_squarefree z
  weights := fun _ => 1
  weights_nonneg := by
    intro n
    norm_num
  totalMass := (N + 1 : Nat)
  nu :=
    (ArithmeticFunction.zeta : ArithmeticFunction Real).pdiv
      ArithmeticFunction.id
  nu_mult := by
    exact
      Sieve.CompletelyMultiplicative.zeta.pdiv
        Sieve.CompletelyMultiplicative.id
        |>.isMultiplicative
  nu_pos_of_prime := by
    intro p hp _hpP
    rw [ArithmeticFunction.pdiv_apply]
    apply _root_.div_pos
    · exact Sieve.zeta_pos_of_prime p hp
    · rw [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.id_apply]
      exact_mod_cast hp.pos
  nu_lt_one_of_prime := by
    intro p hp _hpP
    rw [ArithmeticFunction.pdiv_apply]
    apply (div_lt_one (by
      rw [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.id_apply]
      exact_mod_cast hp.pos)).2
    simpa [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.id_apply] using
        Sieve.zeta_lt_self_of_prime p hp
  level := z
  one_le_level := by
    exact_mod_cast hz

@[simp]
theorem shiftedIntervalSelbergSieve_support
    (C N z : Nat) (hz : 1 ≤ z) :
    (shiftedIntervalSelbergSieve C N z hz).support =
      (Finset.range (N + 1)).image (fun n => C + n) :=
  rfl

@[simp]
theorem shiftedIntervalSelbergSieve_nu
    (C N z : Nat) (hz : 1 ≤ z) (d : Nat) :
    (shiftedIntervalSelbergSieve C N z hz).nu d =
      if d = 0 then 0 else 1 / (d : Real) := by
  by_cases hd : d = 0
  · simp [shiftedIntervalSelbergSieve, hd,
      ArithmeticFunction.pdiv_apply,
      ArithmeticFunction.zeta_apply]
  · simp [shiftedIntervalSelbergSieve, hd,
      ArithmeticFunction.pdiv_apply,
      ArithmeticFunction.zeta_apply, one_div]

/-- Unit weights turn the sifted sum into the cardinality of the translated
interval elements coprime to the primorial. -/
theorem shiftedIntervalSelbergSieve_siftedSum_eq
    (C N z : Nat) (hz : 1 ≤ z) :
    (shiftedIntervalSelbergSieve C N z hz).siftedSum =
      (((Finset.range (N + 1)).filter fun n =>
        (C + n).Coprime (primorial z)).card : Real) := by
  classical
  unfold BoundingSieve.siftedSum
  simp only [shiftedIntervalSelbergSieve]
  rw [Finset.sum_image]
  · simp [Nat.coprime_comm]
  · intro a _ha b _hb hab
    exact Nat.add_left_cancel hab

/-- The divisibility mass is the cardinality of one residue class in the
unshifted interval. -/
theorem shiftedIntervalSelbergSieve_multSum_eq
    (C N z : Nat) (hz : 1 ≤ z) (d : Nat) :
    (shiftedIntervalSelbergSieve C N z hz).multSum d =
      (((Finset.range (N + 1)).filter fun n =>
        d ∣ C + n).card : Real) := by
  classical
  unfold BoundingSieve.multSum
  simp only [shiftedIntervalSelbergSieve]
  rw [Finset.sum_image]
  · rw [← Finset.sum_filter]
    simp
  · intro a _ha b _hb hab
    exact Nat.add_left_cancel hab

/-- The local divisibility remainder on a translated interval is bounded by
one. -/
theorem shiftedIntervalSelbergSieve_rem_abs_le_one
    (C N z : Nat) (hz : 1 ≤ z)
    (d : Nat) (hd : 0 < d) :
    |(shiftedIntervalSelbergSieve C N z hz).rem d| ≤ 1 := by
  classical
  letI : NeZero d := ⟨hd.ne'⟩
  let v : Nat := (-(C : ZMod d)).val
  have hv :
      ∀ n : Nat, d ∣ C + n ↔ n ≡ v [MOD d] := by
    intro n
    constructor
    · intro h
      have hzero :
          ((C + n : Nat) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (C + n) d).2 h
      apply (ZMod.natCast_eq_natCast_iff n v d).1
      rw [show (v : ZMod d) = -(C : ZMod d) by
        simp [v]]
      calc
        (n : ZMod d) =
            -(C : ZMod d) + ((C + n : Nat) : ZMod d) := by
          push_cast
          ring
        _ = -(C : ZMod d) := by rw [hzero, add_zero]
    · intro h
      apply (ZMod.natCast_eq_zero_iff (C + n) d).1
      have heq :
          (n : ZMod d) = (v : ZMod d) :=
        (ZMod.natCast_eq_natCast_iff n v d).2 h
      rw [show (v : ZMod d) = -(C : ZMod d) by
        simp [v]] at heq
      calc
        ((C + n : Nat) : ZMod d) =
            (C : ZMod d) + (n : ZMod d) := by simp
        _ = (C : ZMod d) + (-(C : ZMod d)) := by rw [heq]
        _ = 0 := add_neg_cancel _
  have hcount :
      ((Finset.range (N + 1)).filter fun n => d ∣ C + n).card =
        (N + 1) / d +
          if v % d < (N + 1) % d then 1 else 0 := by
    rw [← Nat.count_eq_card_filter_range]
    simpa only [hv] using
      Nat.count_modEq_card (N + 1) hd v
  have hfloor :
      ((N + 1) / d : Nat) ≤ (N + 1 : Real) / d := by
    simpa using
      Nat.cast_div_le (α := Real)
        (m := N + 1) (n := d)
  have hdecomp :
      (((N + 1) / d : Nat) : Real) * (d : Real) +
          (((N + 1) % d : Nat) : Real) =
        (N + 1 : Real) := by
    exact_mod_cast
      (by
        simpa [Nat.mul_comm] using
          Nat.div_add_mod (N + 1) d)
  have hmod :
      (((N + 1) % d : Nat) : Real) < (d : Real) := by
    exact_mod_cast Nat.mod_lt (N + 1) hd
  have hdReal : (0 : Real) < (d : Real) := by
    exact_mod_cast hd
  have hceil :
      (N + 1 : Real) / d <
        ((N + 1) / d : Nat) + 1 := by
    rw [div_lt_iff₀ hdReal]
    push_cast
    nlinarith
  rw [BoundingSieve.rem,
    shiftedIntervalSelbergSieve_multSum_eq,
    shiftedIntervalSelbergSieve_nu]
  simp only [hd.ne', ↓reduceIte,
    shiftedIntervalSelbergSieve]
  rw [hcount]
  push_cast
  have hmain :
      1 / (d : Real) * ((N : Real) + 1) =
        ((N : Real) + 1) / d := by
    ring
  rw [hmain]
  split_ifs <;> rw [abs_le] <;>
    constructor <;> linarith

/-- Explicit one-dimensional Selberg upper bound for a translated interval.
The first term is the optimized main term and the second is the completely
explicit rounding-error sum. -/
theorem shiftedIntervalSelbergSieve_siftedSum_le
    (C N z : Nat) (hz : 2 ≤ z) :
    (shiftedIntervalSelbergSieve C N z (by omega)).siftedSum ≤
      2 * ((N + 1 : Nat) : Real) / Real.log z +
        (z : Real) * (1 + Real.log z) ^ 3 := by
  have hz1 : 1 ≤ z := by omega
  let s : SelbergSieve :=
    shiftedIntervalSelbergSieve C N z hz1
  have hnu :
      s.nu =
        (ArithmeticFunction.zeta : ArithmeticFunction Real).pdiv
          ArithmeticFunction.id := rfl
  have hP :
      ∀ p : Nat, p.Prime →
        (p : Real) ≤ s.level →
        p ∣ s.prodPrimes := by
    intro p hp hpz
    rw [show s.prodPrimes = primorial z by rfl,
      Sieve.prime_dvd_primorial_iff z p hp]
    change (p : Real) ≤ (z : Real) at hpz
    exact_mod_cast hpz
  have hbounding :
      Real.log z / 2 ≤ s.selbergBoundingSum :=
    Sieve.boundingSum_ge_log s hnu hP
  have hlogPos : 0 < Real.log (z : Real) := by
    exact Real.log_pos (by exact_mod_cast hz)
  have hmain :
      s.totalMass / s.selbergBoundingSum ≤
        2 * ((N + 1 : Nat) : Real) / Real.log z := by
    calc
      s.totalMass / s.selbergBoundingSum ≤
          s.totalMass / (Real.log z / 2) := by
        apply div_le_div_of_nonneg_left
        · change (0 : Real) ≤ ((N + 1 : Nat) : Real)
          positivity
        · exact _root_.div_pos hlogPos (by norm_num)
        · exact hbounding
      _ = 2 * ((N + 1 : Nat) : Real) / Real.log z := by
        dsimp [s, shiftedIntervalSelbergSieve]
        field_simp [hlogPos.ne']
  have herror :
      (∑ d ∈ s.prodPrimes.divisors,
          if (d : Real) ≤ s.level then
            (3 : Real) ^ ArithmeticFunction.cardDistinctFactors d *
              |s.rem d|
          else 0) ≤
        (z : Real) * (1 + Real.log z) ^ 3 := by
    have hraw :=
      Sieve.rem_sum_le_of_const s 1
        (fun d hd =>
          shiftedIntervalSelbergSieve_rem_abs_le_one
            C N z hz1 d hd)
    simpa [s, shiftedIntervalSelbergSieve] using hraw
  exact
    (s.selberg_bound_simple).trans
      (add_le_add hmain herror)

/-- Cardinality form of the translated-interval Selberg bound. -/
theorem shiftedInterval_sifted_card_le
    (C N z : Nat) (hz : 2 ≤ z) :
    ((((Finset.range (N + 1)).filter fun n =>
        (C + n).Coprime (primorial z)).card : Nat) : Real) ≤
      2 * ((N + 1 : Nat) : Real) / Real.log z +
        (z : Real) * (1 + Real.log z) ^ 3 := by
  have hz1 : 1 ≤ z := by omega
  rw [← shiftedIntervalSelbergSieve_siftedSum_eq
    C N z hz1]
  exact shiftedIntervalSelbergSieve_siftedSum_le C N z hz

end Erdos279
