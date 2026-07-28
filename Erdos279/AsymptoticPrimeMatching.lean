import Erdos279.PeriodicPrimePool
import Erdos279.PrimeTargetMatching

/-!
# From an asymptotic prime ratio to a collision-free matching

This file formalizes the elementary inversion consequence used in (3.6)
and (3.7).  The analytic prime-counting theorem is deliberately not assumed
here: the input is an explicit convergence proof for the two enumerations.
Once their ratio has a limit in `(1 / h, 1 / k)`, a common tail gives the
strict inequalities needed for a valid prime-target matching.
-/

namespace Erdos279

open Filter

/-- A prime target not already covered by the hub residue or one of the
finitely many old controller residues set equal to one. -/
def IsComplementaryPrimeTarget
    (h : Prime) (H : Finset Prime) (q : Prime) : Prop :=
  ¬ InControllerProgression h q ∧
    ∀ ℓ ∈ H, q.1 % ℓ.1 ≠ 1

/-- Convergence of `pᵢ / qᵢ` to a point in `(1/h,1/k)` eventually gives
both strict integer gaps `k pᵢ < qᵢ < h pᵢ`. -/
theorem eventually_controller_target_gap
    {p q : Nat → Prime} {k h : Nat} {r : Real}
    (hk : 0 < k) (hh : 0 < h)
    (hratio :
      Tendsto
        (fun i => ((p i).1 : Real) / ((q i).1 : Real))
        atTop (nhds r))
    (hlower : 1 / (h : Real) < r)
    (hupper : r < 1 / (k : Real)) :
    ∀ᶠ i in atTop,
      k * (p i).1 < (q i).1 ∧
        (q i).1 < h * (p i).1 := by
  have heventLower :
      ∀ᶠ i in atTop,
        1 / (h : Real) <
          ((p i).1 : Real) / ((q i).1 : Real) :=
    hratio.eventually_const_lt hlower
  have heventUpper :
      ∀ᶠ i in atTop,
        ((p i).1 : Real) / ((q i).1 : Real) <
          1 / (k : Real) :=
    hratio.eventually_lt_const hupper
  filter_upwards [heventLower, heventUpper] with i hiLower hiUpper
  have hkR : (0 : Real) < (k : Real) := by
    exact_mod_cast hk
  have hhR : (0 : Real) < (h : Real) := by
    exact_mod_cast hh
  have hqR : (0 : Real) < ((q i).1 : Real) := by
    exact_mod_cast (q i).pos
  have hcrossUpper :
      ((p i).1 : Real) * (k : Real) <
        (1 : Real) * ((q i).1 : Real) :=
    (div_lt_div_iff₀ hqR hkR).mp hiUpper
  have hcrossLower :
      (1 : Real) * ((q i).1 : Real) <
        ((p i).1 : Real) * (h : Real) :=
    (div_lt_div_iff₀ hhR hqR).mp hiLower
  have hcrossUpper' :
      (k : Real) * ((p i).1 : Real) <
        ((q i).1 : Real) := by
    simpa [mul_comm] using hcrossUpper
  have hcrossLower' :
      ((q i).1 : Real) <
        (h : Real) * ((p i).1 : Real) := by
    simpa [mul_comm] using hcrossLower
  constructor
  · exact_mod_cast hcrossUpper'
  · exact_mod_cast hcrossLower'

/-- The explicit result of discarding the finite exceptional prefix of two
prime enumerations. -/
structure TailPrimeTargetMatching
    (p q : Nat → Prime) (k : Nat) where
  offset : Nat
  matching : PrimeTargetMatching.Sequence k
  pair_eq :
    ∀ i,
      matching.pair i =
        { controller := p (offset + i)
          target := q (offset + i) }

/-- Injective prime enumerations with an admissible limiting ratio induce
a collision-free matching after deleting a finite prefix. -/
theorem exists_tailPrimeTargetMatching_of_ratio
    {p q : Nat → Prime} {k h : Nat} {r : Real}
    (hpInjective : Function.Injective p)
    (hqInjective : Function.Injective q)
    (hk : 0 < k) (hh : 0 < h)
    (hratio :
      Tendsto
        (fun i => ((p i).1 : Real) / ((q i).1 : Real))
        atTop (nhds r))
    (hlower : 1 / (h : Real) < r)
    (hupper : r < 1 / (k : Real)) :
    Nonempty (TailPrimeTargetMatching p q k) := by
  obtain ⟨N, hN⟩ :=
    eventually_atTop.mp
      (eventually_controller_target_gap
        hk hh hratio hlower hupper)
  let M : PrimeTargetMatching.Sequence k :=
    { pair := fun i =>
        { controller := p (N + i)
          target := q (N + i) }
      controller_injective := by
        intro i j hij
        dsimp at hij
        exact Nat.add_left_cancel (hpInjective hij)
      target_injective := by
        intro i j hij
        dsimp at hij
        exact Nat.add_left_cancel (hqInjective hij)
      admissible := by
        intro i
        exact (hN (N + i) (Nat.le_add_right N i)).1 }
  exact
    ⟨
      { offset := N
        matching := M
        pair_eq := fun _ => rfl }⟩

/-- The paper-specific data behind (3.6): increasing enumerations of the
periodic reservoir and the complementary prime targets, together with the
proved limiting ratio. -/
structure PeriodicComplementaryEnumerations
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) where
  periodic : Nat → Prime
  complementary : Nat → Prime
  periodic_injective : Function.Injective periodic
  complementary_injective : Function.Injective complementary
  periodic_mem :
    ∀ i, InPeriodicReservoir h L R H (periodic i)
  complementary_mem :
    ∀ i, IsComplementaryPrimeTarget h H (complementary i)
  complementary_surjective :
    ∀ q, IsComplementaryPrimeTarget h H q →
      ∃ i, complementary i = q
  ratio : Real
  ratio_tendsto :
    Tendsto
      (fun i =>
        ((periodic i).1 : Real) /
          ((complementary i).1 : Real))
      atTop (nhds ratio)

namespace PeriodicComplementaryEnumerations

/-- A natural-number bound strictly above every target in the deleted
prefix.  It is zero when the prefix is empty. -/
def primePrefixBound
    (q : Nat → Prime) (N : Nat) : Nat :=
  (Finset.range N).sup fun i => (q i).1 + 1

theorem index_ge_of_primePrefixBound_le
    (q : Nat → Prime) (N i : Nat)
    (hi :
      primePrefixBound q N ≤ (q i).1) :
    N ≤ i := by
  by_contra hnot
  have hiN : i < N := Nat.lt_of_not_ge hnot
  have hle :
      (q i).1 + 1 ≤ primePrefixBound q N := by
    simpa [primePrefixBound] using
      (Finset.le_sup
        (s := Finset.range N)
        (f := fun j : Nat => (q j).1 + 1)
        (Finset.mem_range.mpr hiN))
  omega

/-- A ratio window converts the paper-specific enumerations into one valid
infinite prime-target matching. -/
theorem exists_tailMatching
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat} (hk : 0 < k)
    (hlower : 1 / (h.1 : Real) < E.ratio)
    (hupper : E.ratio < 1 / (k : Real)) :
    Nonempty
      (TailPrimeTargetMatching
        E.periodic E.complementary k) := by
  exact
    exists_tailPrimeTargetMatching_of_ratio
      (p := E.periodic) (q := E.complementary)
      (k := k) (h := h.1) (r := E.ratio)
      E.periodic_injective E.complementary_injective
      hk h.pos E.ratio_tendsto hlower hupper

/-- Every controller in the tail matching still lies in the hub
progression. -/
theorem tailMatching_controllersIn
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k) :
    T.matching.ControllersIn h := by
  intro i
  rw [T.pair_eq i]
  exact
    (E.periodic_mem (T.offset + i)).inControllerProgression

/-- Every target in the tail matching is one of the complementary prime
targets from (3.3). -/
theorem tailMatching_target_complementary
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k)
    (i : Nat) :
    IsComplementaryPrimeTarget h H
      (T.matching.pair i).target := by
  rw [T.pair_eq i]
  exact E.complementary_mem (T.offset + i)

/-- After deleting the finite exceptional prefix, the matching assignment
covers every complementary prime target above the explicit prefix bound. -/
theorem tailMatching_assignment_covers_large_complementary
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k)
    (base : ShiftedAssignment)
    (q : Prime)
    (hq : IsComplementaryPrimeTarget h H q)
    (hqLarge :
      primePrefixBound E.complementary T.offset ≤ q.1) :
    ShiftedMatureCovers k q.1
      (T.matching.assignment base) := by
  obtain ⟨i, hiq⟩ :=
    E.complementary_surjective q hq
  have hvalue :
      primePrefixBound E.complementary T.offset ≤
        (E.complementary i).1 := by
    simpa [hiq] using hqLarge
  have hoffset : T.offset ≤ i :=
    index_ge_of_primePrefixBound_le
      E.complementary T.offset i hvalue
  let j := i - T.offset
  have hindex : T.offset + j = i := by
    dsimp [j]
    exact Nat.add_sub_of_le hoffset
  have hcover :=
    T.matching.assignment_covers_target base j
  rw [T.pair_eq j] at hcover
  simpa [hindex, hiq] using hcover

end PeriodicComplementaryEnumerations

end Erdos279
