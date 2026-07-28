import Erdos279.TranslatedPrimeClasses

/-!
# Finite upper-sieve combinatorics

This is the exact finite inequality behind equation (2.16).  It is stated for
an arbitrary finite family of forbidden conditions, so the proof is purely
combinatorial and independent of any analytic estimate for the weights.
-/

namespace Erdos279

open Finset

/--
Upper-bound sieve weights indexed by subsets of a finite set of sieving
conditions.  `majorizes` is the subset form of
`1_{L = 1} ≤ ∑_{d ∣ L} λ⁺ d`.
-/
structure UpperSubsetSieveWeights {ι : Type*} [DecidableEq ι]
    (P : Finset ι) where
  weight : Finset ι → Int
  majorizes :
    ∀ L : Finset ι, L ⊆ P →
      (if L = ∅ then 1 else 0) ≤
        ∑ d ∈ L.powerset, weight d

/-- The set of sieving conditions violated by `u`. -/
noncomputable def violatedConditions
    {α ι : Type*} [DecidableEq ι]
    (P : Finset ι) (bad : α → ι → Prop) (u : α) : Finset ι := by
  classical
  exact P.filter (bad u)

/-- The elements of `U` that avoid every forbidden condition. -/
noncomputable def sieveSurvivors
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (P : Finset ι) (bad : α → ι → Prop) : Finset α := by
  classical
  exact U.filter fun u => violatedConditions P bad u = ∅

/-- The common fibre on which all conditions in `d` are violated. -/
noncomputable def violationFiber
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (d : Finset ι) (bad : α → ι → Prop) : Finset α := by
  classical
  exact U.filter fun u => ∀ p ∈ d, bad u p

@[simp]
theorem mem_sieveSurvivors
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    {U : Finset α} {P : Finset ι} {bad : α → ι → Prop} {u : α} :
    u ∈ sieveSurvivors U P bad ↔
      u ∈ U ∧ ∀ p ∈ P, ¬bad u p := by
  classical
  simp [sieveSurvivors, violatedConditions]

@[simp]
theorem mem_violationFiber
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    {U : Finset α} {d : Finset ι} {bad : α → ι → Prop} {u : α} :
    u ∈ violationFiber U d bad ↔
      u ∈ U ∧ ∀ p ∈ d, bad u p := by
  classical
  simp [violationFiber]

theorem violatedConditions_subset
    {α ι : Type*} [DecidableEq ι]
    (P : Finset ι) (bad : α → ι → Prop) (u : α) :
    violatedConditions P bad u ⊆ P := by
  classical
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem subset_violatedConditions_iff
    {α ι : Type*} [DecidableEq ι]
    {P d : Finset ι} (hd : d ⊆ P)
    (bad : α → ι → Prop) (u : α) :
    d ⊆ violatedConditions P bad u ↔
      ∀ p ∈ d, bad u p := by
  classical
  constructor
  · intro h p hp
    exact (Finset.mem_filter.mp (h hp)).2
  · intro h p hp
    exact Finset.mem_filter.mpr ⟨hd hp, h p hp⟩

/--
Finite upper-sieve inequality.  The right side is the weighted sum of all
common violation fibres.  Negative weights are allowed, exactly as for
standard beta-sieve upper weights.
-/
theorem upperSubsetSieve_bound
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (P : Finset ι)
    (bad : α → ι → Prop)
    (W : UpperSubsetSieveWeights P) :
    ((sieveSurvivors U P bad).card : Int) ≤
      ∑ d ∈ P.powerset,
        W.weight d * (violationFiber U d bad).card := by
  classical
  have hpoint (u : α) :
      (if violatedConditions P bad u = ∅ then (1 : Int) else 0) ≤
        ∑ d ∈ P.powerset,
          if d ⊆ violatedConditions P bad u then W.weight d else 0 := by
    let L := violatedConditions P bad u
    have hLP : L ⊆ P := violatedConditions_subset P bad u
    have hmajor := W.majorizes L hLP
    have hpowers :
        L.powerset =
          P.powerset.filter (fun d => d ⊆ L) := by
      ext d
      simp only [Finset.mem_powerset, Finset.mem_filter]
      constructor
      · intro hdL
        exact ⟨Subset.trans hdL hLP, hdL⟩
      · exact fun h => h.2
    change (if L = ∅ then (1 : Int) else 0) ≤ _ at hmajor ⊢
    rw [hpowers] at hmajor
    simpa [Finset.sum_filter] using hmajor
  calc
    ((sieveSurvivors U P bad).card : Int) =
        ∑ u ∈ U,
          if violatedConditions P bad u = ∅ then (1 : Int) else 0 := by
      simp [sieveSurvivors]
    _ ≤ ∑ u ∈ U, ∑ d ∈ P.powerset,
          if d ⊆ violatedConditions P bad u then W.weight d else 0 := by
      exact Finset.sum_le_sum fun u _hu => hpoint u
    _ = ∑ d ∈ P.powerset, ∑ u ∈ U,
          if d ⊆ violatedConditions P bad u then W.weight d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.powerset,
          W.weight d * (violationFiber U d bad).card := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdP : d ⊆ P := Finset.mem_powerset.mp hd
      have hcond (u : α) :
          d ⊆ violatedConditions P bad u ↔
            ∀ p ∈ d, bad u p :=
        subset_violatedConditions_iff hdP bad u
      simp only [hcond]
      calc
        (∑ u ∈ U,
            if (∀ p ∈ d, bad u p) then W.weight d else 0) =
            ∑ _u ∈ violationFiber U d bad, W.weight d := by
          rw [violationFiber, Finset.sum_filter]
        _ = W.weight d * (violationFiber U d bad).card := by
          simp [mul_comm]

end Erdos279
