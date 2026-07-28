import Erdos279.PrimePoolInfinitude

/-!
# Prime-counting asymptotics

This file introduces a count-form PNT interface and proves that asymptotics
for pairwise disjoint classes add over a finite union.  This is the exact
algebraic bridge needed to assemble the periodic prime pool from its finitely
many CRT residue classes.
-/

namespace Erdos279

open Filter

/-- A positive shifted version of `x / log x`.  The shift is immaterial at
infinity and avoids exceptional values at `0` and `1`. -/
noncomputable def primeCountingScale (x : Nat) : Real :=
  ((x + 2 : Nat) : Real) /
    Real.log ((x + 2 : Nat) : Real)

theorem primeCountingScale_pos (x : Nat) :
    0 < primeCountingScale x := by
  unfold primeCountingScale
  have hx : (1 : Real) < ((x + 2 : Nat) : Real) := by
    exact_mod_cast (by omega : 1 < x + 2)
  exact div_pos (by positivity) (Real.log_pos hx)

theorem primeCountingScale_ne_zero (x : Nat) :
    primeCountingScale x ≠ 0 :=
  (primeCountingScale_pos x).ne'

/-- The shifted `x / log x` normalization tends to infinity. -/
theorem primeCountingScale_tendsto_atTop :
    Tendsto primeCountingScale atTop atTop := by
  have hy :
      Tendsto
        (fun x : Nat => (x : Real) + 2)
        atTop atTop :=
    tendsto_atTop_add_const_right
      atTop 2 tendsto_natCast_atTop_atTop
  have hsmallReal :
      Tendsto
        (fun y : Real => Real.log y / y)
        atTop (nhds 0) := by
    simpa only [id_eq] using
      Real.isLittleO_log_id_atTop
        |>.tendsto_div_nhds_zero
  have hsmall :
      Tendsto
        (fun x : Nat =>
          Real.log ((x : Real) + 2) /
            ((x : Real) + 2))
        atTop (nhds 0) :=
    hsmallReal.comp hy
  have hpositive :
      ∀ x : Nat,
        0 <
          Real.log ((x : Real) + 2) /
            ((x : Real) + 2) := by
    intro x
    have hx : (1 : Real) < (x : Real) + 2 := by
      have hx0 : 0 ≤ (x : Real) :=
        Nat.cast_nonneg x
      linarith
    exact div_pos (Real.log_pos hx) (by positivity)
  have hsmallPos :
      Tendsto
        (fun x : Nat =>
          Real.log ((x : Real) + 2) /
            ((x : Real) + 2))
        atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact
      ⟨hsmall,
        Eventually.of_forall
          (fun x => hpositive x)⟩
  have hinv := hsmallPos.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  apply Eventually.of_forall
  intro x
  unfold primeCountingScale
  push_cast
  change
    (Real.log ((x : Real) + 2) /
      ((x : Real) + 2))⁻¹ =
    ((x : Real) + 2) /
      Real.log ((x : Real) + 2)
  rw [inv_div]

/-- The number of values below `x` satisfying `P`, with classical
decidability hidden behind a noncomputable wrapper. -/
noncomputable def predicateCount
    (P : Nat → Prop) (x : Nat) : Nat := by
  classical
  exact Nat.count P x

theorem predicateCount_add
    (P : Nat → Prop) (a b : Nat) :
    predicateCount P (a + b) =
      predicateCount P a +
        predicateCount (fun k => P (a + k)) b := by
  classical
  unfold predicateCount
  exact Nat.count_add P a b

/-- Count-form prime number theorem for a natural-number predicate. -/
def HasPrimeCountingAsymptotic
    (P : Nat → Prop) (density : Real) : Prop :=
  Tendsto
    (fun x =>
      ((predicateCount P x : Nat) : Real) /
        primeCountingScale x)
    atTop (nhds density)

/-- Count-form PNT specialized to a predicate on project primes. -/
def HasProjectPrimeCountingAsymptotic
    (P : Prime → Prop) (density : Real) : Prop :=
  HasPrimeCountingAsymptotic
    (primeNatPredicate P) density

/-- Counts add for two pointwise disjoint predicates. -/
theorem count_or_of_pointwise_disjoint
    (P Q : Nat → Prop)
    (hdisjoint : ∀ n, ¬ (P n ∧ Q n))
    (x : Nat) :
    predicateCount (fun n => P n ∨ Q n) x =
      predicateCount P x + predicateCount Q x := by
  classical
  unfold predicateCount
  induction x with
  | zero =>
      simp
  | succ x ih =>
      rw [Nat.count_succ, Nat.count_succ,
        Nat.count_succ, ih]
      by_cases hp : P x <;>
        by_cases hq : Q x <;>
        simp [hp, hq, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
      exact (hdisjoint x ⟨hp, hq⟩).elim

/-- The count of a pairwise disjoint finite union is the sum of its
individual counts. -/
theorem count_exists_mem_finset
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (A : ι → Nat → Prop)
    (hdisjoint :
      ∀ a ∈ R, ∀ b ∈ R, a ≠ b →
        ∀ n, ¬ (A a n ∧ A b n))
    (x : Nat) :
    predicateCount (fun n => ∃ a ∈ R, A a n) x =
      ∑ a ∈ R, predicateCount (A a) x := by
  classical
  induction R using Finset.induction_on with
  | empty =>
      simp [predicateCount]
  | @insert a R ha ih =>
      have hhead :
          ∀ n, ¬ (A a n ∧ ∃ b ∈ R, A b n) := by
        intro n hn
        rcases hn with ⟨han, b, hbR, hbn⟩
        exact
          hdisjoint a (Finset.mem_insert_self a R)
            b (Finset.mem_insert_of_mem hbR)
            (by
              intro hab
              subst b
              exact ha hbR)
            n ⟨han, hbn⟩
      have htail :
          ∀ b ∈ R, ∀ c ∈ R, b ≠ c →
            ∀ n, ¬ (A b n ∧ A c n) := by
        intro b hb c hc hbc n
        exact
          hdisjoint b (Finset.mem_insert_of_mem hb)
            c (Finset.mem_insert_of_mem hc)
            hbc n
      have hor :
          predicateCount
              (fun n => A a n ∨ ∃ b ∈ R, A b n) x =
            predicateCount (A a) x +
              predicateCount (fun n => ∃ b ∈ R, A b n) x :=
        count_or_of_pointwise_disjoint
          (A a) (fun n => ∃ b ∈ R, A b n)
          hhead x
      calc
        predicateCount
            (fun n => ∃ b ∈ insert a R, A b n) x =
          predicateCount
            (fun n => A a n ∨ ∃ b ∈ R, A b n) x := by
              apply congrArg (fun P => predicateCount P x)
              funext n
              apply propext
              simp only [Finset.mem_insert]
              constructor
              · rintro ⟨b, hb, hbn⟩
                rcases hb with rfl | hbR
                · exact Or.inl hbn
                · exact Or.inr ⟨b, hbR, hbn⟩
              · rintro (han | ⟨b, hbR, hbn⟩)
                · exact ⟨a, Or.inl rfl, han⟩
                · exact ⟨b, Or.inr hbR, hbn⟩
        _ =
          predicateCount (A a) x +
            predicateCount (fun n => ∃ b ∈ R, A b n) x :=
              hor
        _ =
          predicateCount (A a) x +
            ∑ b ∈ R, predicateCount (A b) x := by
              rw [ih htail]
        _ =
          ∑ b ∈ insert a R, predicateCount (A b) x := by
              simp [ha]

/-- Count-form PNT asymptotics add over a pairwise disjoint finite union. -/
theorem hasPrimeCountingAsymptotic_exists_mem_finset
    {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (A : ι → Nat → Prop)
    (density : ι → Real)
    (hdisjoint :
      ∀ a ∈ R, ∀ b ∈ R, a ≠ b →
        ∀ n, ¬ (A a n ∧ A b n))
    (hAsymptotic :
      ∀ a ∈ R,
        HasPrimeCountingAsymptotic
          (A a) (density a)) :
    HasPrimeCountingAsymptotic
      (fun n => ∃ a ∈ R, A a n)
      (∑ a ∈ R, density a) := by
  classical
  unfold HasPrimeCountingAsymptotic
  have hsum :
      Tendsto
        (fun x =>
          ∑ a ∈ R,
            ((predicateCount (A a) x : Nat) : Real) /
              primeCountingScale x)
        atTop
        (nhds (∑ a ∈ R, density a)) := by
    exact
      tendsto_finset_sum R
        (fun a ha => by
          simpa [HasPrimeCountingAsymptotic] using
            hAsymptotic a ha)
  have heq :
      (fun x =>
        ((predicateCount
          (fun n => ∃ a ∈ R, A a n) x : Nat) : Real) /
            primeCountingScale x) =
      (fun x =>
        ∑ a ∈ R,
          ((predicateCount (A a) x : Nat) : Real) /
            primeCountingScale x) := by
    funext x
    rw [count_exists_mem_finset R A hdisjoint x]
    push_cast
    rw [Finset.sum_div]
  rw [heq]
  exact hsum

/-- Changing a predicate at only finitely many initial values does not alter
its count-form asymptotic. -/
theorem HasPrimeCountingAsymptotic.congr_of_eventually_iff
    {P Q : Nat → Prop} {density : Real}
    (N : Nat)
    (hPQ : ∀ n, N ≤ n → (P n ↔ Q n))
    (hQ : HasPrimeCountingAsymptotic Q density) :
    HasPrimeCountingAsymptotic P density := by
  unfold HasPrimeCountingAsymptotic at hQ ⊢
  let cP : Real := predicateCount P N
  let cQ : Real := predicateCount Q N
  have hdiffEventually :
      (fun x =>
        ((predicateCount P x : Nat) : Real) /
            primeCountingScale x -
          ((predicateCount Q x : Nat) : Real) /
            primeCountingScale x) =ᶠ[atTop]
      (fun x =>
        (cP - cQ) /
          primeCountingScale x) := by
    filter_upwards [eventually_ge_atTop N] with x hx
    obtain ⟨t, rfl⟩ :=
      Nat.exists_eq_add_of_le hx
    have htail :
        (fun k => P (N + k)) =
          (fun k => Q (N + k)) := by
      funext k
      apply propext
      exact hPQ (N + k) (Nat.le_add_right N k)
    have htailCount :
        predicateCount (fun k => P (N + k)) t =
          predicateCount (fun k => Q (N + k)) t :=
      congrArg (fun S => predicateCount S t) htail
    unfold cP cQ
    rw [predicateCount_add,
      predicateCount_add, htailCount]
    push_cast
    field_simp [primeCountingScale_ne_zero]
    ring
  have hdiffLimit :
      Tendsto
        (fun x =>
          ((predicateCount P x : Nat) : Real) /
              primeCountingScale x -
            ((predicateCount Q x : Nat) : Real) /
              primeCountingScale x)
        atTop (nhds 0) := by
    apply Tendsto.congr' hdiffEventually.symm
    exact
      primeCountingScale_tendsto_atTop
        |>.const_div_atTop (cP - cQ)
  simpa only [sub_add_cancel, zero_add] using
    hdiffLimit.add hQ

/-- Symmetric form of finite-initial-perturbation invariance. -/
theorem hasPrimeCountingAsymptotic_congr_of_eventually_iff
    {P Q : Nat → Prop} {density : Real}
    (N : Nat)
    (hPQ : ∀ n, N ≤ n → (P n ↔ Q n)) :
    HasPrimeCountingAsymptotic P density ↔
      HasPrimeCountingAsymptotic Q density := by
  constructor
  · intro hP
    exact
      hP.congr_of_eventually_iff N
        (fun n hn => (hPQ n hn).symm)
  · intro hQ
    exact
      hQ.congr_of_eventually_iff N hPQ

end Erdos279
