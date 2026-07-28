import Erdos279.HardTailAsymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# The correctly uniform deterministic hard sieve

Proposition 2.1 does not sieve by one fixed finite set of old primes.
At scale `X` it uses every controller prime up to `X^(1/v)`, with an
arbitrary correlated vector of nonzero residue classes.  This file records
that quantifier structure exactly.

This interface supersedes any fixed-cutoff stage count for the analytic
part of the proof.
-/

namespace Erdos279

open Filter

/-- The integral old-prime cutoff `floor(X^(1/v))`. -/
def stageOldPrimeCutoff (v X : Nat) : Nat :=
  Nat.nthRoot v X

/-- Hard survivors at scale `X`, with the full scale-dependent old-prime
cutoff. -/
noncomputable def uniformHardStageCount
    (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X)) : Nat :=
  (hardSurvivors h (stageOldPrimeCutoff v X) a X (B * X)).card

/-- Main-layer portion of the uniformly sieved hard-stage count. -/
noncomputable def uniformMainHardStageCount
    (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X)) : Nat :=
  ∑ e ∈ hardMainExponentRange h X (B * X),
    (hardLayerUnits h (stageOldPrimeCutoff v X) e a
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card

/-- Complementary high-exponent portion of the uniformly sieved count. -/
noncomputable def uniformTailHardStageCount
    (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X)) : Nat :=
  ∑ e ∈ hardTailExponentRange h X (B * X),
    (hardLayerUnits h (stageOldPrimeCutoff v X) e a
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card

/-- Exact main/tail decomposition at every scale and for every old-class
vector. -/
theorem uniformHardStageCount_eq_main_add_tail
    (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X)) :
    uniformHardStageCount h v B X a =
      uniformMainHardStageCount h v B X a +
        uniformTailHardStageCount h v B X a := by
  unfold uniformHardStageCount uniformMainHardStageCount
    uniformTailHardStageCount
  exact
    hardSurvivors_card_eq_main_add_tail
      h (stageOldPrimeCutoff v X) a X (B * X)

/-- Proposition 2.1 in its actual uniform quantifier form. -/
def HasUniformHardStageUpperBound
    (h : Prime) (v B : Nat) (coefficient : Real) : Prop :=
  ∀ ε : Real, 0 < ε →
    ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h (stageOldPrimeCutoff v X),
        (uniformHardStageCount h v B X a : Real) /
            primeCountingScale X ≤
          coefficient + ε

/-- The remaining main-layer version of the uniform hard estimate. -/
def HasUniformMainHardStageUpperBound
    (h : Prime) (v B : Nat) (coefficient : Real) : Prop :=
  ∀ ε : Real, 0 < ε →
    ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h (stageOldPrimeCutoff v X),
        (uniformMainHardStageCount h v B X a : Real) /
            primeCountingScale X ≤
          coefficient + ε

/-- The exact high-exponent estimate is uniform in both the cutoff and all
chosen nonzero classes. -/
theorem uniformTailHardStageCount_le
    (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X))
    (hB : 0 < B) :
    uniformTailHardStageCount h v B X a ≤
      (Nat.log h.1 (B * X) + 1) *
        (B * Nat.sqrt X) := by
  exact
    sum_hardTailLayers_card_le
      h (stageOldPrimeCutoff v X) B X a hB

/-- Uniform `o(X/log X)` form of equation (2.24). -/
theorem uniformTailHardStageCount_normalized_eventually_lt
    (h : Prime) (v B : Nat) (hB : 0 < B)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h (stageOldPrimeCutoff v X),
        (uniformTailHardStageCount h v B X a : Real) /
            primeCountingScale X <
          ε := by
  have hBoundEventually :
      ∀ᶠ X : Nat in atTop,
        hardTailRealBound h B X /
            primeCountingScale X <
          ε :=
    (hardTailRealBound_normalized_tendsto_zero
      h B hB).eventually_lt_const hε
  filter_upwards [hBoundEventually] with X hX
  intro a
  have hTailCast :
      (uniformTailHardStageCount h v B X a : Real) ≤
        hardTailRealBound h B X := by
    unfold hardTailRealBound
    exact_mod_cast uniformTailHardStageCount_le h v B X a hB
  exact
    (div_le_div_of_nonneg_right hTailCast
      (primeCountingScale_pos X).le).trans_lt hX

/-- Once the main layers have the paper's uniform upper bound, the full
uniform deterministic sieve estimate follows automatically. -/
theorem HasUniformMainHardStageUpperBound.toHardUpperBound
    {h : Prime} {v B : Nat} {coefficient : Real}
    (hMain :
      HasUniformMainHardStageUpperBound h v B coefficient)
    (hB : 0 < B) :
    HasUniformHardStageUpperBound h v B coefficient := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hMainEventually :=
    hMain (ε / 2) hhalf
  have hTailEventually :=
    uniformTailHardStageCount_normalized_eventually_lt
      h v B hB hhalf
  filter_upwards
    [hMainEventually, hTailEventually] with X hMainX hTailX
  intro a
  have hMainAt := hMainX a
  have hTailAt := hTailX a
  rw [uniformHardStageCount_eq_main_add_tail h v B X a]
  push_cast
  rw [add_div]
  linarith

end Erdos279
