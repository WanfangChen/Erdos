import Erdos279.PrimeCountingScaleLinear

/-!
# Fixed-ratio interval prime counts

This file converts a count-form PNT into asymptotics for half-open intervals
whose endpoints are fixed rational multiples of the main scale.  All
inclusive endpoints are handled by exact `Nat.count` identities.
-/

namespace Erdos279

open Filter

/-- Values satisfying `P` in the natural half-open interval `(Y,Z]`. -/
noncomputable def predicateIoc
    (P : Nat → Prop) (Y Z : Nat) : Finset Nat := by
  classical
  exact (Finset.Ioc Y Z).filter P

@[simp]
theorem mem_predicateIoc
    {P : Nat → Prop} {Y Z n : Nat} :
    n ∈ predicateIoc P Y Z ↔
      Y < n ∧ n ≤ Z ∧ P n := by
  classical
  simp [predicateIoc, and_assoc]

/-- Exact conversion between an interval cardinal and two prefix counts. -/
theorem predicateIoc_card_eq_count_sub
    (P : Nat → Prop) {Y Z : Nat}
    (hYZ : Y ≤ Z) :
    (predicateIoc P Y Z).card =
      predicateCount P (Z + 1) -
        predicateCount P (Y + 1) := by
  classical
  unfold predicateIoc predicateCount
  rw [Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range]
  have hsubset :
      (Finset.range (Y + 1)).filter P ⊆
        (Finset.range (Z + 1)).filter P := by
    intro n hn
    simp only [Finset.mem_filter,
      Finset.mem_range] at hn ⊢
    exact ⟨by omega, hn.2⟩
  rw [← Finset.card_sdiff_of_subset hsubset]
  congr 1
  ext n
  simp only [Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_range,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hYn, hnZ⟩, hPn⟩
    refine ⟨⟨by omega, hPn⟩, ?_⟩
    rintro ⟨hnY, _hPn⟩
    omega
  · rintro ⟨⟨hnZ, hPn⟩, hnot⟩
    refine ⟨⟨?_, by omega⟩, hPn⟩
    by_contra hYn
    apply hnot
    exact ⟨by omega, hPn⟩

/-- A count-form asymptotic evaluated at a fixed rationally rescaled
endpoint, but still normalized at the original scale. -/
theorem HasPrimeCountingAsymptotic.at_mul_div_add
    {P : Nat → Prop} {density : Real}
    (hCount :
      HasPrimeCountingAsymptotic P density)
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun X : Nat =>
        (predicateCount P
            (a * X / b + c) : Real) /
          primeCountingScale X)
      atTop
      (nhds
        (density *
          ((a : Real) / (b : Real)))) := by
  have hEndpointTop :
      Tendsto
        (fun X : Nat =>
          a * X / b + c)
        atTop atTop :=
    (tendsto_add_atTop_nat c).comp
      (nat_mul_div_tendsto_atTop
        a b ha hb)
  have hAtEndpoint :
      Tendsto
        (fun X : Nat =>
          (predicateCount P
              (a * X / b + c) : Real) /
            primeCountingScale
              (a * X / b + c))
        atTop (nhds density) :=
    hCount.comp hEndpointTop
  have hScale :=
    primeCountingScale_mul_div_add_ratio_tendsto
      a b c ha hb
  have hProduct :=
    hAtEndpoint.mul hScale
  apply hProduct.congr'
  apply Eventually.of_forall
  intro X
  have hscaleNe :
      primeCountingScale
          (a * X / b + c) ≠ 0 :=
    primeCountingScale_ne_zero _
  field_simp [hscaleNe]

/-- Strictly ordered rational endpoint coefficients give eventually ordered
natural-number quotient endpoints. -/
theorem eventually_nat_mul_div_le_of_ratio_lt
    (a b c d : Nat)
    (hb : 0 < b) (hd : 0 < d)
    (hratio :
      (a : Real) / (b : Real) <
        (c : Real) / (d : Real)) :
    ∀ᶠ X : Nat in atTop,
      a * X / b ≤ c * X / d := by
  let midpoint :=
    ((a : Real) / (b : Real) +
      (c : Real) / (d : Real)) / 2
  have hleftMid :
      (a : Real) / (b : Real) <
        midpoint := by
    dsimp [midpoint]
    linarith
  have hmidRight :
      midpoint <
        (c : Real) / (d : Real) := by
    dsimp [midpoint]
    linarith
  have hleft :=
    (natCast_mul_div_ratio_tendsto
      a b hb).eventually_lt_const hleftMid
  have hright :=
    (natCast_mul_div_ratio_tendsto
      c d hd).eventually_const_lt hmidRight
  filter_upwards
    [hleft, hright,
      eventually_gt_atTop 0] with X hXl hXr hX
  have hnormalized :
      ((a * X / b : Nat) : Real) /
          (X : Real) <
        ((c * X / d : Nat) : Real) /
          (X : Real) :=
    hXl.trans hXr
  have hXR : 0 < (X : Real) := by
    exact_mod_cast hX
  have hcast :
      ((a * X / b : Nat) : Real) <
        ((c * X / d : Nat) : Real) :=
    (div_lt_div_iff_of_pos_right hXR).mp
      hnormalized
  exact_mod_cast hcast.le

/-- The cardinality of a fixed-ratio half-open interval inherits the
difference of the two endpoint PNT coefficients. -/
theorem predicateIoc_mul_div_asymptotic
    {P : Nat → Prop} {density : Real}
    (hCount :
      HasPrimeCountingAsymptotic P density)
    (a b c d : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d)
    (hratio :
      (a : Real) / (b : Real) <
        (c : Real) / (d : Real)) :
    Tendsto
      (fun X : Nat =>
        ((predicateIoc P
          (a * X / b)
          (c * X / d)).card : Real) /
            primeCountingScale X)
      atTop
      (nhds
        (density *
            ((c : Real) / (d : Real)) -
          density *
            ((a : Real) / (b : Real)))) := by
  have hLower :=
    hCount.at_mul_div_add
      a b 1 ha hb
  have hUpper :=
    hCount.at_mul_div_add
      c d 1 hc hd
  have hDifference := hUpper.sub hLower
  have hOrder :=
    eventually_nat_mul_div_le_of_ratio_lt
      a b c d hb hd hratio
  have hEq :
      (fun X : Nat =>
        (predicateCount P
              (c * X / d + 1) : Real) /
            primeCountingScale X -
          (predicateCount P
              (a * X / b + 1) : Real) /
            primeCountingScale X) =ᶠ[atTop]
      (fun X : Nat =>
        ((predicateIoc P
          (a * X / b)
          (c * X / d)).card : Real) /
            primeCountingScale X) := by
    filter_upwards [hOrder] with X hXZ
    have hCountLe :
        predicateCount P
            (a * X / b + 1) ≤
          predicateCount P
            (c * X / d + 1) :=
      by
        classical
        unfold predicateCount
        exact
          (Nat.count_monotone P)
            (by omega)
    rw [predicateIoc_card_eq_count_sub
      P hXZ]
    rw [Nat.cast_sub hCountLe]
    ring
  exact hDifference.congr' hEq

/-- The project-prime annulus is cardinally identical to the natural
predicate interval. -/
theorem controllerReservoirAnnulus_card_eq_predicateIoc
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (Y Z : Nat) :
    (controllerReservoirAnnulus
      h L R H Y Z).card =
      (predicateIoc
        (primeNatPredicate
          (InControllerReservoir h L R H))
        Y Z).card := by
  classical
  apply Finset.card_bij
      (fun p _hp => p.1)
  · intro p hp
    apply mem_predicateIoc.mpr
    have hpData :=
      mem_controllerReservoirAnnulus.mp hp
    exact
      ⟨hpData.1, hpData.2.1,
        p.2, hpData.2.2⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro n hn
    have hnData := mem_predicateIoc.mp hn
    rcases hnData.2.2 with
      ⟨hnPrime, hnReservoir⟩
    let p : Prime :=
      ⟨n, hnPrime⟩
    refine ⟨p, ?_, rfl⟩
    exact
      mem_controllerReservoirAnnulus.mpr
        ⟨hnData.1, hnData.2.1,
          hnReservoir⟩

/-- Fixed-progression PNT supplies the exact controller-annulus asymptotic
at any fixed integral stage ratio lying below `h/k`. -/
theorem mesh_controllerStage_asymptotic
    {h : Prime} {k B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hk : 0 < k)
    (hB : 0 < B)
    (hBk : k * B < h.1)
    (hPNT :
      FixedProgressionPrimeNumberTheorem
        (h.1 * M.modulus.1)) :
    HasMeshControllerStageAsymptotic
      M B
      (M.controllerReservoirDensity *
        (1 / (k : Real) -
          (B : Real) / (h.1 : Real))) := by
  have hratio :
      (B : Real) / (h.1 : Real) <
        (1 : Real) / (k : Real) := by
    have hhR :
        (0 : Real) < h.1 := by
      exact_mod_cast h.pos
    have hkR :
        (0 : Real) < k := by
      exact_mod_cast hk
    apply (div_lt_div_iff₀
      hhR hkR).2
    norm_num
    exact_mod_cast
      (by simpa [Nat.mul_comm] using hBk)
  have hCount :=
    mesh_controllerReservoir_countingAsymptotic
      M hPNT
  have hInterval :=
    predicateIoc_mul_div_asymptotic
      hCount B h.1 1 k
      hB h.pos (by omega) hk
      (by simpa using hratio)
  unfold HasMeshControllerStageAsymptotic
    meshControllerStageCount
  have hEq :
      (fun X : Nat =>
        ((predicateIoc
          (primeNatPredicate
            (InControllerReservoir
              h M.modulus M.classes
              (oldControllerPrimes
                h M.cutoff)))
          (B * X / h.1)
          (1 * X / k)).card : Real) /
            primeCountingScale X) =ᶠ[atTop]
      (fun X : Nat =>
        ((hardStageControllerAnnulus
          h M.modulus M.classes
          (oldControllerPrimes h M.cutoff)
          k X (B * X)).card : Real) /
            primeCountingScale X) := by
    apply Eventually.of_forall
    intro X
    change
      ((predicateIoc
        (primeNatPredicate
          (InControllerReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff)))
        (B * X / h.1)
        (1 * X / k)).card : Real) /
          primeCountingScale X =
        ((controllerReservoirAnnulus
          h M.modulus M.classes
          (oldControllerPrimes h M.cutoff)
          (B * X / h.1)
          (X / k)).card : Real) /
            primeCountingScale X
    rw [controllerReservoirAnnulus_card_eq_predicateIoc]
    simp
  have hFinal := hInterval.congr' hEq
  simpa [mul_sub] using hFinal

end Erdos279
