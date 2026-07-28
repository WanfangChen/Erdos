import Erdos279.AnalyticDefinitions

/-!
# Exact finite identities behind the local-density calculation

These are the algebraic identities used before any Selberg--Delange or
Bombieri--Vinogradov estimate enters the proof.
-/

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The summatory function `M(x) = ∑_{u ≤ x} f(u)`, with values in `ℤ`. -/
noncomputable def controllerSummatory (h : Prime) (x : Nat) : Int :=
  ∑ u ∈ Finset.range (x + 1), (controllerIndicator h u : Int)

/--
Multiples of a fixed positive `r` up to `x` are in bijection with integers
up to `x / r`.
-/
theorem sum_controllerIndicator_over_multiples
    {h : Prime} {r x : Nat}
    (hrpos : 0 < r) :
    (∑ u ∈ (Finset.range (x + 1)).filter (r ∣ ·),
        (controllerIndicator h u : Int)) =
      ∑ v ∈ Finset.range (x / r + 1),
        (controllerIndicator h (r * v) : Int) := by
  classical
  refine Finset.sum_nbij'
    (fun u => u / r) (fun v => r * v) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_range]
    have hult : u < x + 1 := Finset.mem_range.mp hu.1
    have hux : u ≤ x := by omega
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hux)
  · intro v hv
    rw [Finset.mem_range] at hv
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · apply Nat.lt_succ_of_le
      have hvle : v ≤ x / r := Nat.le_of_lt_succ hv
      have hmul : v * r ≤ x :=
        (Nat.le_div_iff_mul_le hrpos).mp hvle
      simpa [Nat.mul_comm] using hmul
    · exact ⟨v, rfl⟩
  · intro u hu
    rw [Finset.mem_filter] at hu
    exact Nat.mul_div_cancel' hu.2
  · intro v hv
    exact Nat.mul_div_right v hrpos
  · intro u hu
    rw [Finset.mem_filter] at hu
    rw [Nat.mul_div_cancel' hu.2]

/--
If `r ∈ ⟨G⟩`, the exact multiples sum is the same summatory function at
`x / r`.  This is the finite identity used in equation (2.9).
-/
theorem sum_controllerIndicator_over_semigroup_multiples
    {h : Prime} {r x : Nat}
    (hr : ControllerSemigroup h r) :
    (∑ u ∈ (Finset.range (x + 1)).filter (r ∣ ·),
        (controllerIndicator h u : Int)) =
      controllerSummatory h (x / r) := by
  rw [sum_controllerIndicator_over_multiples hr.pos]
  unfold controllerSummatory
  apply Finset.sum_congr rfl
  intro v hv
  rw [controllerIndicator_mul_left_of_mem hr]

/-- The divisor sum of the Möbius function is the unit arithmetic function. -/
theorem sum_moebius_divisors (n : Nat) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  calc
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
        ((ArithmeticFunction.moebius : ArithmeticFunction Int) *
          (ArithmeticFunction.zeta : ArithmeticFunction Int)) n := by
          symm
          exact ArithmeticFunction.coe_mul_zeta_apply
    _ = (1 : ArithmeticFunction Int) n := by
          rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = if n = 1 then 1 else 0 := by
          rfl

/-- The exact Möbius weight detecting the coprimality condition `(u,d)=1`. -/
def coprimeMobiusWeight (u d : Nat) : Int :=
  ∑ r ∈ (u.gcd d).divisors, ArithmeticFunction.moebius r

@[simp]
theorem coprimeMobiusWeight_eq
    (u d : Nat) :
    coprimeMobiusWeight u d =
      if u.Coprime d then 1 else 0 := by
  rw [coprimeMobiusWeight, sum_moebius_divisors]

/-- Divisors of `gcd(u,d)` are precisely the divisors of `d` that divide `u`. -/
theorem divisors_gcd_eq_filter
    {u d : Nat} (hd : d ≠ 0) :
    (u.gcd d).divisors =
      d.divisors.filter (· ∣ u) := by
  calc
    (u.gcd d).divisors =
        d.divisors.filter (· ∣ u.gcd d) :=
      (Nat.divisors_filter_dvd_of_dvd hd
        (Nat.gcd_dvd_right u d)).symm
    _ = d.divisors.filter (· ∣ u) := by
      ext r
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      aesop

/-- The Möbius coprimality weight, expressed on the fixed divisor set of `d`. -/
theorem coprimeMobiusWeight_eq_sum_filter
    {u d : Nat} (hd : d ≠ 0) :
    coprimeMobiusWeight u d =
      ∑ r ∈ d.divisors.filter (· ∣ u),
        ArithmeticFunction.moebius r := by
  rw [coprimeMobiusWeight, divisors_gcd_eq_filter hd]

/-- `M_d(x)`, the controller-semigroup mass up to `x` coprime to `d`. -/
noncomputable def controllerCoprimeSummatory
    (h : Prime) (d x : Nat) : Int :=
  ∑ u ∈ (Finset.range (x + 1)).filter (·.Coprime d),
    (controllerIndicator h u : Int)

/--
Exact Möbius inversion for the coprime controller-semigroup mean:

`M_d(x) = ∑_{r ∣ d} μ(r) M(x/r)`.

The hypothesis `d ∈ ⟨G⟩` is exactly what permits
`f(r v) = f(v)` for every divisor `r ∣ d`.
-/
theorem controllerCoprimeSummatory_eq_moebius
    {h : Prime} {d x : Nat}
    (hd : ControllerSemigroup h d) :
    controllerCoprimeSummatory h d x =
      ∑ r ∈ d.divisors,
        ArithmeticFunction.moebius r * controllerSummatory h (x / r) := by
  classical
  have hd0 : d ≠ 0 := Nat.ne_of_gt hd.pos
  unfold controllerCoprimeSummatory
  calc
    (∑ u ∈ (Finset.range (x + 1)).filter (·.Coprime d),
        (controllerIndicator h u : Int)) =
        ∑ u ∈ Finset.range (x + 1),
          (controllerIndicator h u : Int) * coprimeMobiusWeight u d := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      rw [coprimeMobiusWeight_eq]
      by_cases hcop : u.Coprime d <;> simp [hcop]
    _ = ∑ u ∈ Finset.range (x + 1),
          ∑ r ∈ d.divisors.filter (· ∣ u),
            ArithmeticFunction.moebius r * (controllerIndicator h u : Int) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [coprimeMobiusWeight_eq_sum_filter hd0, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ u ∈ Finset.range (x + 1),
          ∑ r ∈ d.divisors,
            if r ∣ u then
              ArithmeticFunction.moebius r * (controllerIndicator h u : Int)
            else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_filter]
    _ = ∑ r ∈ d.divisors,
          ∑ u ∈ Finset.range (x + 1),
            if r ∣ u then
              ArithmeticFunction.moebius r * (controllerIndicator h u : Int)
            else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ d.divisors,
          ArithmeticFunction.moebius r *
            (∑ u ∈ (Finset.range (x + 1)).filter (r ∣ ·),
              (controllerIndicator h u : Int)) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hru : r ∣ u <;> simp [hru]
    _ = ∑ r ∈ d.divisors,
          ArithmeticFunction.moebius r * controllerSummatory h (x / r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrd : r ∣ d := (Nat.mem_divisors.mp hr).1
      rw [sum_controllerIndicator_over_semigroup_multiples
        (hd.of_dvd hrd)]

end Erdos279
