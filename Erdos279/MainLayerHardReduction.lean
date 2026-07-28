import Erdos279.HardTailAsymptotic
import Erdos279.FixedPNTHardReduction

/-!
# Reduction of the hard estimate to the main layers

The high-exponent layers have now been proved negligible.  Consequently
the deterministic sieve only has to estimate the layers satisfying
`sqrt X ≤ X / h^e`, exactly the range on which the paper invokes its
uniform Selberg--Delange and Bombieri--Vinogradov estimates.
-/

namespace Erdos279

open Filter

/-- Total hard-survivor count contributed by the main exponent range. -/
noncomputable def meshMainHardStageCount
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    (B X : Nat) : Nat :=
  ∑ e ∈ hardMainExponentRange h X (B * X),
    (hardLayerUnits h M.cutoff e
      (E.enumerations.primeTargetOldClasses T)
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card

/-- Total hard-survivor count contributed by the complementary tail. -/
noncomputable def meshTailHardStageCount
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    (B X : Nat) : Nat :=
  ∑ e ∈ hardTailExponentRange h X (B * X),
    (hardLayerUnits h M.cutoff e
      (E.enumerations.primeTargetOldClasses T)
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card

/-- Exact decomposition of a mesh hard-stage count into main and tail
layers. -/
theorem meshHardStageCount_eq_main_add_tail
    {h : Prime} {k B X : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k) :
    meshHardStageCount E T B X =
      meshMainHardStageCount E T B X +
        meshTailHardStageCount E T B X := by
  unfold meshHardStageCount meshMainHardStageCount
    meshTailHardStageCount
  exact
    hardSurvivors_card_eq_main_add_tail
      h M.cutoff
      (E.enumerations.primeTargetOldClasses T)
      X (B * X)

/-- The one-sided normalized upper bound that remains to be proved on the
main layers. -/
def HasMeshMainHardStageUpperBound
    {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    (B : Nat) (coefficient : Real) : Prop :=
  ∀ ε : Real, 0 < ε →
    ∀ᶠ X : Nat in atTop,
      (meshMainHardStageCount E T B X : Real) /
          primeCountingScale X ≤
        coefficient + ε

/-- The tail part of every mesh hard stage tends to zero after
normalization. -/
theorem meshTailHardStageCount_normalized_tendsto_zero
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k)
    (hB : 0 < B) :
    Tendsto
      (fun X : Nat =>
        (meshTailHardStageCount E T B X : Real) /
          primeCountingScale X)
      atTop (nhds 0) := by
  simpa [meshTailHardStageCount] using
    hardTailLayers_normalized_tendsto_zero
      h M.cutoff B
      (E.enumerations.primeTargetOldClasses T)
      hB

/-- A main-layer upper bound automatically extends to the complete hard
stage because the complementary layers are `o(X / log X)`. -/
theorem HasMeshMainHardStageUpperBound.toHardUpperBound
    {h : Prime} {k B : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    {E : MeshPrimeEnumerations M}
    {T : TailPrimeTargetMatching
      E.enumerations.periodic
      E.enumerations.complementary k}
    {coefficient : Real}
    (hMain :
      HasMeshMainHardStageUpperBound
        E T B coefficient)
    (hB : 0 < B) :
    HasMeshHardStageUpperBound E T B coefficient := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hMainEventually :=
    hMain (ε / 2) hhalf
  have hTailEventually :
      ∀ᶠ X : Nat in atTop,
        (meshTailHardStageCount E T B X : Real) /
            primeCountingScale X <
          ε / 2 :=
    (meshTailHardStageCount_normalized_tendsto_zero
      E T hB).eventually_lt_const hhalf
  filter_upwards
    [hMainEventually, hTailEventually] with X hMainX hTailX
  rw [meshHardStageCount_eq_main_add_tail E T]
  push_cast
  rw [add_div]
  linarith

/-- Analytic input package after the elementary high-exponent tail has
been completely removed. -/
structure FixedPNTMainLayerInputs (k : Nat) where
  Csv : Real
  Csv_nonneg : 0 ≤ Csv
  v : Nat
  one_le_v : 1 ≤ v
  fixedPNT : AllFixedProgressionPrimeNumberTheorems
  mainUpperBound :
    ∀ {h : Prime}
      (hh : 3 ≤ h.1)
      (hkpos : 0 < k)
      (hlarge : 256 * k ≤ h.1)
      (M : OldControllerPrimeDensityMesh h k)
      (A : MeshFixedProgressionPNTInputs M)
      (T : TailPrimeTargetMatching
        (A.toMeshPrimeEnumerations
          (hh := hh)
          (hk := hkpos)).enumerations.periodic
        (A.toMeshPrimeEnumerations
          (hh := hh)
          (hk := hkpos)).enumerations.complementary k),
      HasMeshMainHardStageUpperBound
        (A.toMeshPrimeEnumerations
          (hh := hh)
          (hk := hkpos))
        T
        (integralStageRatio k h.1)
        (hardSurvivorCoefficient
          Csv v (integralStageRatio k h.1) h)

namespace FixedPNTMainLayerInputs

/-- Convert the main-layer package to the previous complete-hard-stage
interface using the proved tail theorem. -/
noncomputable def toFixedPNTHardInputs
    {k : Nat} (I : FixedPNTMainLayerInputs k) :
    FixedPNTHardInputs k where
  Csv := I.Csv
  Csv_nonneg := I.Csv_nonneg
  v := I.v
  one_le_v := I.one_le_v
  fixedPNT := I.fixedPNT
  hardUpperBound := by
    intro h hh hkpos hlarge M A T
    have hB :
        0 < integralStageRatio k h.1 := by
      have hspec :=
        integralStageRatio_spec
          (k := k) (h := h.1)
          hkpos hlarge
      omega
    exact
      (I.mainUpperBound hh hkpos hlarge M A T).toHardUpperBound hB

end FixedPNTMainLayerInputs

/-- Fixed-progression PNT and the main-layer deterministic sieve estimate
prove the fixed-level statement. -/
theorem P_of_fixedPNTMainLayerInputs
    {k : Nat} (hk : 3 ≤ k)
    (I : FixedPNTMainLayerInputs k) :
    P k :=
  P_of_fixedPNTHardInputs hk I.toFixedPNTHardInputs

/-- Levelwise main-layer analytic packages prove Erdős 279 globally. -/
theorem globalAffirmative_of_fixedPNTMainLayerInputs
    (I : ∀ k : Nat, 3 ≤ k → FixedPNTMainLayerInputs k) :
    GlobalAffirmative := by
  intro k hk
  exact P_of_fixedPNTMainLayerInputs hk (I k hk)

end Erdos279
