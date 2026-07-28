import Erdos279.External.WienerCore

/-!
# The von Mangoldt prime number theorem in a fixed arithmetic progression

This file connects the proved Wiener--Ikehara theorem to Mathlib's
zero-free-line continuation of the logarithmic derivatives of Dirichlet
`L`-functions.  It is the weighted fixed-modulus PNT needed before partial
summation removes prime powers and logarithmic weights.
-/

namespace Erdos279

open ArithmeticFunction
open ArithmeticFunction.vonMangoldt
open Complex Filter LSeries Set Topology

/-- The Chebyshev bound for the von Mangoldt function restricts to every
residue class. -/
theorem residueClass_cheby
    {q : Nat} (a : ZMod q) :
    cheby (fun n => (residueClass a n : Complex)) := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨C, ?_⟩
  intro N
  have hCN := hC N
  unfold cumsum at hCN ⊢
  calc
    ∑ n ∈ Finset.range N, ‖(residueClass a n : Complex)‖ ≤
        ∑ n ∈ Finset.range N, ‖(vonMangoldt n : Complex)‖ := by
      gcongr with n hn
      have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
      rw [Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (residueClass_nonneg a n),
        abs_of_nonneg hΛ]
      exact residueClass_le a n
    _ ≤ C * (N : Real) := hCN

/-- Weighted PNT in one fixed reduced residue class:
`Σ_{n<N, n≡a (mod q)} Λ(n) / N → 1/φ(q)`. -/
theorem weightedProgressionPNT
    {q a : Nat} (hq : 0 < q) (ha : a.Coprime q) :
    Tendsto
      (fun N =>
        cumsum
          (residueClass (a : ZMod q)) N / (N : Real))
      atTop
      (nhds ((Nat.totient q : Real)⁻¹)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let az : ZMod q := a
  let f : Nat → Real := residueClass az
  let density : Real := (Nat.totient q : Real)⁻¹
  let G : Complex → Complex :=
    LFunctionResidueClassAux az
  have haUnit : IsUnit az := by
    exact (ZMod.isUnit_iff_coprime a q).2 ha
  have hnonneg : 0 ≤ f := by
    intro n
    exact residueClass_nonneg az n
  have hsummable :
      ∀ σ : Real, 1 < σ →
        Summable
          (nterm (fun n => (f n : Complex)) σ) := by
    intro σ hσ
    have habscissa :
        abscissaOfAbsConv (fun n => (f n : Complex)) <
          (σ : Complex).re := by
      simpa [f] using
        (abscissaOfAbsConv_residueClass_le_one az).trans_lt
          (by exact_mod_cast hσ)
    have hL :
        LSeriesSummable (fun n => (f n : Complex)) (σ : Complex) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re habscissa
    simpa only [← nterm_eq_norm_term] using hL.norm
  have hcheby :
      cheby (fun n => (f n : Complex)) := by
    simpa [f] using residueClass_cheby az
  have hcontinuous :
      ContinuousOn G {s | 1 ≤ s.re} := by
    simpa [G] using
      continuousOn_LFunctionResidueClassAux az
  have hcastTotientInv :
      ((Nat.totient q : Complex)⁻¹) =
        (density : Complex) := by
    dsimp [density]
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_inv _).symm
  have hWI :
      Tendsto
        (fun N => cumsum f N / (N : Real))
        atTop
        (nhds density) := by
    apply WienerIkeharaTheorem'
      (A := density)
      (G := G)
      hnonneg hsummable hcheby hcontinuous
    intro s hs
    have hsource :
        G s =
          LSeries (fun n => (f n : Complex)) s -
            (Nat.totient q : Complex)⁻¹ / (s - 1) := by
      simpa only [G, f] using
        (eqOn_LFunctionResidueClassAux haUnit hs)
    calc
      G s =
          LSeries (fun n => (f n : Complex)) s -
            (Nat.totient q : Complex)⁻¹ / (s - 1) :=
        hsource
      _ =
          LSeries (fun n => (f n : Complex)) s -
            (density : Complex) /
              (s - 1) := by
        rw [hcastTotientInv]
  simpa [az, f, density] using hWI

end Erdos279
