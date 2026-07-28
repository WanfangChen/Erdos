import Erdos279.AnalyticConstants
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Convex.Deriv

/-!
# Strict convexity of `log Γ` and the paper's Gamma constant

Mathlib supplies convexity of `log ∘ Γ`.  The Gamma recurrence makes its
derivative recurrence strict enough to upgrade this to strict convexity.
This yields Lemma 2.3 directly from the tangent at `1`.
-/

namespace Erdos279

/-- The real log-Gamma function on the positive axis. -/
noncomputable def logGammaFn : Real → Real :=
  Real.log ∘ Real.Gamma

theorem differentiableAt_logGammaFn
    {x : Real} (hx : 0 < x) :
    DifferentiableAt Real logGammaFn x := by
  unfold logGammaFn
  refine
    ((Real.differentiableAt_Gamma ?_).log
      (Real.Gamma_ne_zero ?_))
  · intro m
    have hm : (0 : Real) ≤ m := by positivity
    exact ne_of_gt (by linarith)
  · intro m
    have hm : (0 : Real) ≤ m := by positivity
    exact ne_of_gt (by linarith)

theorem logGammaFn_add_one
    {x : Real} (hx : 0 < x) :
    logGammaFn (x + 1) =
      logGammaFn x + Real.log x := by
  simp only [logGammaFn, Function.comp_apply,
    Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne',
    add_comm]

/-- Derivative form of the Gamma functional equation. -/
theorem deriv_logGammaFn_add_one
    {x : Real} (hx : 0 < x) :
    deriv logGammaFn (x + 1) =
      deriv logGammaFn x + 1 / x := by
  rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
    ← deriv_add
      (differentiableAt_logGammaFn (by positivity))
      (Real.differentiableAt_log hx.ne')]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact logGammaFn_add_one hy

/-- The derivative of log-Gamma is strictly increasing on the positive
axis. -/
theorem strictMonoOn_deriv_logGammaFn :
    StrictMonoOn (deriv logGammaFn) (Set.Ioi (0 : Real)) := by
  have hconv :
      ConvexOn Real (Set.Ioi (0 : Real)) logGammaFn := by
    simpa [logGammaFn] using Real.convexOn_log_Gamma
  have hdiff :
      ∀ x ∈ Set.Ioi (0 : Real),
        DifferentiableAt Real logGammaFn x := by
    intro x hx
    exact differentiableAt_logGammaFn hx
  intro x hx y hy hxy
  have hx0 : 0 < x := Set.mem_Ioi.mp hx
  have hy0 : 0 < y := Set.mem_Ioi.mp hy
  have hshift :
      deriv logGammaFn (x + 1) ≤
        deriv logGammaFn (y + 1) := by
    exact hconv.monotoneOn_deriv hdiff
      (by exact Set.mem_Ioi.mpr (by linarith))
      (by exact Set.mem_Ioi.mpr (by linarith))
      (by linarith)
  rw [deriv_logGammaFn_add_one hx0,
    deriv_logGammaFn_add_one hy0] at hshift
  have hinv : 1 / y < 1 / x :=
    one_div_lt_one_div_of_lt hx0 hxy
  linarith

/-- Strict log-convexity of the real Gamma function. -/
theorem strictConvexOn_logGammaFn :
    StrictConvexOn Real (Set.Ioi (0 : Real)) logGammaFn := by
  have hcontinuous :
      ContinuousOn logGammaFn (Set.Ioi (0 : Real)) := by
    intro x hx
    exact
      (differentiableAt_logGammaFn
        (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  apply StrictMonoOn.strictConvexOn_of_deriv
    (D := Set.Ioi (0 : Real))
    (convex_Ioi (0 : Real))
    hcontinuous
  simpa using strictMonoOn_deriv_logGammaFn

/-- The derivative of log-Gamma at one is `-γ`. -/
theorem hasDerivAt_logGammaFn_one :
    HasDerivAt logGammaFn
      (-Real.eulerMascheroniConstant) 1 := by
  have h :=
    Real.hasDerivAt_Gamma_one.log
      (by simp [Real.Gamma_one])
  simpa [logGammaFn, Function.comp_def, Real.Gamma_one] using h

/--
The strict tangent inequality at one:
`-γ δ < log Γ(1+δ)` for every positive `δ`.
-/
theorem neg_euler_mul_lt_log_Gamma_one_add
    {δ : Real} (hδ : 0 < δ) :
    -Real.eulerMascheroniConstant * δ <
      Real.log (Real.Gamma (δ + 1)) := by
  have hslope :=
    strictConvexOn_logGammaFn.lt_slope_of_hasDerivAt
      (show (1 : Real) ∈ Set.Ioi 0 by norm_num)
      (show (1 + δ : Real) ∈ Set.Ioi 0 by
        exact Set.mem_Ioi.mpr (by linarith))
      (by linarith)
      hasDerivAt_logGammaFn_one
  rw [slope_def_field] at hslope
  simp [logGammaFn, Real.Gamma_one] at hslope
  have hmul :=
    (lt_div_iff₀ hδ).mp hslope
  simpa [add_comm] using hmul

/-- Exponential form of the strict tangent inequality. -/
theorem exp_neg_euler_mul_lt_Gamma_one_add
    {δ : Real} (hδ : 0 < δ) :
    Real.exp
        (-Real.eulerMascheroniConstant * δ) <
      Real.Gamma (δ + 1) := by
  have hlog :=
    neg_euler_mul_lt_log_Gamma_one_add hδ
  have hgammaPos :
      0 < Real.Gamma (δ + 1) :=
    Real.Gamma_pos_of_pos (by linarith)
  exact
    (Real.exp_lt_exp.mpr hlog).trans_eq
      (Real.exp_log hgammaPos)

/--
Lemma 2.3, in the stronger range `δ > 0`:
`Aδ = exp(-γδ) / Γ(δ) < δ`.
-/
theorem paperA_lt
    {δ : Real} (hδ : 0 < δ) :
    paperA δ < δ := by
  have hratio :
      Real.exp
          (-Real.eulerMascheroniConstant * δ) /
            Real.Gamma (δ + 1) < 1 := by
    apply (div_lt_one
      (Real.Gamma_pos_of_pos (by linarith))).mpr
    exact exp_neg_euler_mul_lt_Gamma_one_add hδ
  have hpaper : paperA δ / δ < 1 := by
    rw [paperA_div_eq hδ.ne']
    exact hratio
  exact (div_lt_one hδ).mp hpaper

/-- Lemma 2.3 at the controller density. -/
theorem paperA_controllerDensity_lt_density
    (h : Prime) :
    paperA (controllerDensity h) <
      controllerDensity h :=
  paperA_lt (controllerDensity_pos h)

end Erdos279
