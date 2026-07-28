import Erdos279.ArithmeticProgressionWeightedPNT
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.NumberTheory.PrimeCounting

/-!
# Removing prime powers in a fixed arithmetic progression

The Wiener--Ikehara output counts all prime powers with von Mangoldt
weights.  This file proves that the non-prime prime powers contribute
`o(x)`, uniformly enough for each fixed residue class, and obtains the
Chebyshev-theta form of the PNT in that class.
-/

namespace Erdos279

open ArithmeticFunction Nat Finset BigOperators Filter Real
  Asymptotics
open scoped Chebyshev

/-- If `u ~ v` and `u - w = o(v)`, then `w ~ v`. -/
theorem Asymptotics.IsEquivalent.sub_isLittleO_right
    {α β : Type*} [NormedAddCommGroup β]
    {u v w : α → β} {l : Filter α}
    (huv : IsEquivalent l u v)
    (huw : (u - w) =o[l] v) :
    IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact huv.sub_isLittleO huw

/-- `sqrt x * log x = o(x)`. -/
theorem isLittleO_sqrt_mul_log_atTop :
    (fun x : Real => x.sqrt * x.log) =o[atTop]
      (fun x => x) := by
  refine (isLittleO_mul_iff_isLittleO_div ?_).2 ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact (Real.sqrt_ne_zero hx.le).2 hx.ne'
  · convert
      isLittleO_log_rpow_atTop
        (by norm_num : (0 : Real) < 1 / 2) using 2 with x
    rw [div_sqrt, Real.sqrt_eq_rpow]

/-- `(floor x + 1) / x -> 1`. -/
theorem tendsto_floor_add_one_div_self_ap :
    Tendsto
      (fun x : Real => ((⌊x⌋₊ + 1 : Nat) : Real) / x)
      atTop (nhds 1) := by
  have hfloor := Asymptotics.isEquivalent_nat_floor (R := Real)
  have hfloor' :
      IsEquivalent atTop
        (fun x : Real => (⌊x⌋₊ : Real) + 1)
        _root_.id :=
    hfloor.add_isLittleO
      (Asymptotics.isLittleO_const_id_atTop 1)
  have htendsto :=
    (isEquivalent_iff_tendsto_one
      (by
        filter_upwards [eventually_gt_atTop 0] with x hx hzero
        simp only [_root_.id] at hzero
        exact hx.ne' hzero)).1 hfloor'
  simpa only [Nat.cast_add, Nat.cast_one, id_eq] using htendsto

/-- Division by a nonzero constant preserves theta order. -/
theorem isTheta_self_div_const_ap
    {c : Real} (hc : c ≠ 0) :
    (fun x : Real => x) =Θ[atTop]
      (fun x => x / c) := by
  have heq :
      (fun x : Real => x / c) =
        fun x => c⁻¹ * x := by
    funext x
    ring
  exact heq ▸
    ((isTheta_const_mul_left (inv_ne_zero hc)).2
      (isTheta_refl ..)).symm

/-- Filtered sums over `Iic` and `Icc 1` agree for primes. -/
theorem filter_prime_Iic_eq_Icc_ap (n : Nat) :
    filter Nat.Prime (Iic n) =
      filter Nat.Prime (Icc 1 n) := by
  ext p
  simp only [mem_filter, mem_Iic, mem_Icc,
    and_congr_left_iff]
  exact fun hp =>
    ⟨fun h => ⟨hp.one_lt.le, h⟩,
      fun h => h.2⟩

/-- `Icc 0 n` is obtained by adjoining zero to `Icc 1 n`. -/
theorem Icc_zero_eq_insert_ap (n : Nat) :
    Icc 0 n = insert 0 (Icc 1 n) := by
  ext m
  simp [mem_Icc]
  omega

/-- The log-weighted prime sum in one residue class. -/
noncomputable def progressionTheta
    (q a : Nat) (x : Real) : Real :=
  ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊),
    if p % q = a % q then Real.log p else 0

/-- Chebyshev-theta PNT in every fixed reduced residue class. -/
theorem progressionTheta_isEquivalent
    {q a : Nat} (hq : 0 < q) (ha : a.Coprime q) :
    progressionTheta q a ~[atTop]
      (fun x => x / (Nat.totient q : Real)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let psiAQ : Real → Real :=
    fun x =>
      ∑ n ∈ Icc 1 ⌊x⌋₊,
        if n % q = a % q then
          vonMangoldt n
        else 0
  have htotPos : (0 : Real) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hweighted :
      Tendsto
        (fun N =>
          (∑ n ∈ Iio N,
              if n % q = a % q then
                vonMangoldt n
              else 0) / (N : Real))
        atTop
        (nhds (1 / (Nat.totient q : Real))) := by
    have hW := weightedProgressionPNT hq ha
    simpa only [one_div, cumsum, ← Nat.Iio_eq_range,
      ArithmeticFunction.vonMangoldt.residueClass,
      Set.indicator_apply, Set.mem_setOf_eq,
      ZMod.natCast_eq_natCast_iff'] using hW
  have hpsi :
      psiAQ ~[atTop]
        (fun x => x / (Nat.totient q : Real)) := by
    have hpsiEq (x : Real) :
        psiAQ x =
          ∑ n ∈ Iio (⌊x⌋₊ + 1),
            if n % q = a % q then
              vonMangoldt n
            else 0 := by
      simp only [psiAQ,
        show Icc 1 ⌊x⌋₊ =
          (Iio (⌊x⌋₊ + 1)).filter (1 ≤ ·) by
            ext n
            simp [mem_Icc, mem_filter,
              Nat.lt_add_one_iff]
            tauto,
        sum_filter]
      refine sum_congr rfl fun n _ => ?_
      by_cases hn : 1 ≤ n
      · simp only [hn, ↓reduceIte]
      · push_neg at hn
        interval_cases n
        simp
    refine
      (isEquivalent_iff_tendsto_one ?_).2 ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx
      exact div_ne_zero (by linarith) htotPos.ne'
    have hlim :
        Tendsto
          (fun x : Real =>
            (∑ n ∈ Iio (⌊x⌋₊ + 1),
                if n % q = a % q then
                  vonMangoldt n
                else 0) /
              ((⌊x⌋₊ + 1 : Nat) : Real))
          atTop
          (nhds (1 / (Nat.totient q : Real))) := by
      have heq :
          (fun x : Real =>
            (∑ n ∈ Iio (⌊x⌋₊ + 1),
                if n % q = a % q then
                  vonMangoldt n
                else 0) /
              ((⌊x⌋₊ + 1 : Nat) : Real)) =
            (fun N =>
              (∑ n ∈ Iio N,
                  if n % q = a % q then
                    vonMangoldt n
                  else 0) / (N : Real)) ∘
              (fun x : Real => ⌊x⌋₊ + 1) := by
        funext x
        rfl
      exact heq ▸
        hweighted.comp
          ((tendsto_add_atTop_nat 1).comp
            tendsto_nat_floor_atTop)
    have hratio :
        (psiAQ /
            fun x =>
              x / (Nat.totient q : Real)) =
          fun x =>
            psiAQ x / x *
              (Nat.totient q : Real) := by
      funext x
      simp only [Pi.div_apply, div_div_eq_mul_div]
      ring
    rw [hratio,
      show (1 : Real) =
          1 / (Nat.totient q : Real) * 1 *
            (Nat.totient q : Real) by
        field_simp]
    refine Tendsto.mul ?_ tendsto_const_nhds
    have hevent :
        (fun x => psiAQ x / x) =ᶠ[atTop]
          fun x =>
            ((∑ n ∈ Iio (⌊x⌋₊ + 1),
                if n % q = a % q then
                  vonMangoldt n
                else 0) /
              ((⌊x⌋₊ + 1 : Nat) : Real)) *
            (((⌊x⌋₊ + 1 : Nat) : Real) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [hpsiEq]
      field_simp
    exact Tendsto.congr' hevent.symm
      (hlim.mul tendsto_floor_add_one_div_self_ap)
  refine Asymptotics.IsEquivalent.sub_isLittleO_right hpsi
    (IsBigO.trans_isLittleO
      (g := fun x => 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']
    refine ⟨1, one_pos,
      eventually_atTop.mpr ⟨2, fun x hx => ?_⟩⟩
    simp only [Pi.sub_apply, norm_eq_abs, one_mul]
    have hdiffNonneg :
        0 ≤ psiAQ x - progressionTheta q a x := by
      simp only [psiAQ, progressionTheta, sub_nonneg]
      calc
        (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊),
            if p % q = a % q then
              Real.log p
            else 0) ≤
          ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊),
            if p % q = a % q then
              vonMangoldt p
            else 0 := by
          apply sum_le_sum
          intro p hp
          split_ifs
          · simp [vonMangoldt_apply_prime
              (mem_filter.mp hp).2]
          · rfl
        _ ≤
          ∑ n ∈ Icc 1 ⌊x⌋₊,
            if n % q = a % q then
              vonMangoldt n
            else 0 := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [mem_filter, mem_Iic,
              mem_Icc] at hp ⊢
            exact ⟨hp.2.one_lt.le, hp.1⟩
          · intro n hn hnot
            split_ifs
            · exact vonMangoldt_nonneg
            · rfl
    have hdiffLe :
        psiAQ x - progressionTheta q a x ≤
          Chebyshev.psi x - Chebyshev.theta x := by
      simp only [psiAQ, progressionTheta,
        Chebyshev.psi_eq_sum_Icc,
        Chebyshev.theta_eq_sum_Icc]
      conv_rhs =>
        rw [Icc_zero_eq_insert_ap,
          sum_insert
            (by simp :
              (0 : Nat) ∉ Icc 1 ⌊x⌋₊),
          show vonMangoldt 0 = 0 by
            simp only [ArithmeticFunction.map_zero],
          zero_add,
          show filter Nat.Prime
                (insert 0 (Icc 1 ⌊x⌋₊)) =
              filter Nat.Prime (Icc 1 ⌊x⌋₊) by
            simp [filter_insert, Nat.not_prime_zero]]
      rw [filter_prime_Iic_eq_Icc_ap,
        ← sum_filter_add_sum_filter_not
          (Icc 1 ⌊x⌋₊) Nat.Prime,
        show
          (∑ p ∈ filter Nat.Prime
              (Icc 1 ⌊x⌋₊),
            if p % q = a % q then
              Real.log p
            else 0) =
          ∑ p ∈ filter Nat.Prime
              (Icc 1 ⌊x⌋₊),
            if p % q = a % q then
              vonMangoldt p
            else 0 by
          apply sum_congr rfl
          intro p hp
          simp only [mem_filter] at hp
          split_ifs
          · simp [vonMangoldt_apply_prime hp.2]
          · rfl,
        ← sum_filter_add_sum_filter_not
          (Icc 1 ⌊x⌋₊) Nat.Prime,
        show
          (∑ p ∈ filter Nat.Prime
              (Icc 1 ⌊x⌋₊),
            vonMangoldt p) =
          ∑ p ∈ filter Nat.Prime
              (Icc 1 ⌊x⌋₊),
            Real.log p by
          exact sum_congr rfl fun p hp =>
            vonMangoldt_apply_prime
              (mem_filter.mp hp).2]
      have hnonprime :
          (∑ n ∈ (Icc 1 ⌊x⌋₊).filter
              (¬Nat.Prime ·),
            if n % q = a % q then
              vonMangoldt n
            else 0) ≤
          ∑ n ∈ (Icc 1 ⌊x⌋₊).filter
              (¬Nat.Prime ·),
            vonMangoldt n := by
        apply sum_le_sum
        intro n hn
        split_ifs
        · exact le_rfl
        · exact vonMangoldt_nonneg
      linarith
    rw [abs_of_nonneg hdiffNonneg,
      abs_of_nonneg (by bound)]
    exact hdiffLe.trans
      ((le_abs_self _).trans
        (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
          (by linarith)))
  · simpa only [mul_assoc] using
      (isLittleO_sqrt_mul_log_atTop.const_mul_left 2
        |>.trans_isTheta
          (isTheta_self_div_const_ap htotPos.ne'))

end Erdos279
