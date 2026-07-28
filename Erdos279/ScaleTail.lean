import Erdos279.ScheduledPaperConstruction

/-!
# Adjacent scale intervals cover a tail

The multiscale construction only needs an increasing unbounded sequence.
This file proves that every integer above the initial scale belongs to one
of its adjacent half-open intervals.
-/

namespace Erdos279

open Filter

/-- A monotone sequence tending to infinity places every value above its
initial term in some interval `(scale j, scale (j+1)]`. -/
theorem exists_adjacent_scale_interval
    (scale : Nat → Nat)
    (_hmono : Monotone scale)
    (hunbounded : Tendsto scale atTop atTop)
    {m : Nat} (hm : scale 0 < m) :
    ∃ j, scale j < m ∧ m ≤ scale (j + 1) := by
  have hevent : ∀ᶠ n in atTop, m ≤ scale n :=
    (tendsto_atTop.1 hunbounded) m
  obtain ⟨n, hn⟩ := hevent.exists
  have hex : ∃ n : Nat, m ≤ scale n := ⟨n, hn⟩
  let first : Nat := Nat.find hex
  have hfirst : m ≤ scale first :=
    Nat.find_spec hex
  have hfirstPos : 0 < first := by
    by_contra hnot
    have hzero : first = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hfirst
    omega
  let j : Nat := first - 1
  have hjSucc : j + 1 = first := by
    dsimp [j]
    omega
  have hjLt : j < first := by
    dsimp [j]
    omega
  have hnotAtJ : ¬ m ≤ scale j :=
    Nat.find_min hex hjLt
  exact ⟨j, Nat.lt_of_not_ge hnotAtJ, by simpa [hjSucc] using hfirst⟩

/-- Uniform tail form, suitable for the schedule constructor. -/
theorem adjacent_scale_intervals_cover_tail
    (scale : Nat → Nat)
    (hmono : Monotone scale)
    (hunbounded : Tendsto scale atTop atTop) :
    ∀ m, scale 0 + 1 ≤ m →
      ∃ j, scale j < m ∧ m ≤ scale (j + 1) := by
  intro m hm
  apply exists_adjacent_scale_interval
    scale hmono hunbounded
  omega

end Erdos279
