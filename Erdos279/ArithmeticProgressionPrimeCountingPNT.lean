import Erdos279.ArithmeticProgressionChebyshevPNT
import Erdos279.FixedProgressionPNT

/-!
# From Chebyshev theta to prime counting in an arithmetic progression

We use the elementary Landau squeeze.  Primes up to `x` give the lower
bound `theta(x) / log x`.  For `0 < r < 1`, primes larger than `x^r`
give the upper bound `theta(x) / (r log x)`, while there are at most
`x^r + 1` smaller integers.  Sending `r` to one proves the exact
prime-counting constant.
-/

namespace Erdos279

open ArithmeticFunction Nat Finset BigOperators Filter Real
  Asymptotics

/-- The finite set of primes in one residue class up to a real cutoff. -/
noncomputable def progressionPrimes
    (q a : Nat) (x : Real) : Finset Nat :=
  (Iic ⌊x⌋₊).filter fun p =>
    p.Prime ∧ p % q = a % q

/-- Real-valued counting function for one fixed residue class. -/
noncomputable def progressionPrimeCountReal
    (q a : Nat) (x : Real) : Real :=
  ((progressionPrimes q a x).card : Real)

theorem progressionTheta_eq_sum_progressionPrimes
    (q a : Nat) (x : Real) :
    progressionTheta q a x =
      ∑ p ∈ progressionPrimes q a x,
        Real.log p := by
  classical
  unfold progressionTheta progressionPrimes
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp [and_left_comm, and_assoc]
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simp [hp.2.2]

/-- Every log-weighted prime contributes at most `log x`. -/
theorem progressionTheta_le_count_mul_log
    {q a : Nat} {x : Real} (hx : 2 ≤ x) :
    progressionTheta q a x ≤
      progressionPrimeCountReal q a x * Real.log x := by
  rw [progressionTheta_eq_sum_progressionPrimes]
  unfold progressionPrimeCountReal
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  simp only [one_mul]
  apply Real.strictMonoOn_log.monotoneOn
  · have hpPrime :
        p.Prime :=
      (Finset.mem_filter.mp
        (show p ∈ progressionPrimes q a x from hp)).2.1
    show (0 : Real) < (p : Real)
    exact_mod_cast hpPrime.pos
  · show (0 : Real) < x
    exact lt_of_lt_of_le (by norm_num) hx
  · have hpLeFloor :
        p ≤ ⌊x⌋₊ :=
      (Finset.mem_filter.mp
        (show p ∈ progressionPrimes q a x from hp)).1
        |> Finset.mem_Iic.mp
    exact (Nat.cast_le.mpr hpLeFloor).trans
      (Nat.floor_le (by linarith))

/-- The elementary lower Landau bound. -/
theorem theta_div_log_le_progressionPrimeCount
    {q a : Nat} {x : Real} (hx : 2 ≤ x) :
    progressionTheta q a x / Real.log x ≤
      progressionPrimeCountReal q a x := by
  rw [div_le_iff₀ (Real.log_pos (by linarith))]
  simpa [mul_comm] using
    progressionTheta_le_count_mul_log
      (q := q) (a := a) hx

/-- The small-cutoff term occurring in the upper Landau bound. -/
theorem small_progression_indicator_sum_le
    (q a : Nat) (x r : Real) :
    (∑ p ∈ progressionPrimes q a x,
        if p ≤ ⌊x ^ r⌋₊ then (1 : Real) else 0) ≤
      (⌊x ^ r⌋₊ : Real) + 1 := by
  classical
  have hnat :
      (∑ p ∈ progressionPrimes q a x,
          if p ≤ ⌊x ^ r⌋₊ then 1 else 0) ≤
        ⌊x ^ r⌋₊ + 1 := by
    calc
      (∑ p ∈ progressionPrimes q a x,
          if p ≤ ⌊x ^ r⌋₊ then 1 else 0) =
          ((progressionPrimes q a x).filter
            fun p => p ≤ ⌊x ^ r⌋₊).card := by
        simp
      _ ≤ (Iic ⌊x ^ r⌋₊).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter] at hp
        exact Finset.mem_Iic.mpr hp.2
      _ = ⌊x ^ r⌋₊ + 1 := by
        simp
  exact_mod_cast hnat

/-- For a prime above `x^r`, its logarithm is at least `r log x`. -/
theorem one_le_log_div_add_small_indicator
    {q a : Nat} {x r : Real}
    (hx : 1 < x) (hr0 : 0 < r)
    {p : Nat} (hp : p ∈ progressionPrimes q a x) :
    (1 : Real) ≤
      Real.log p / (r * Real.log x) +
        if p ≤ ⌊x ^ r⌋₊ then 1 else 0 := by
  have hden : 0 < r * Real.log x :=
    mul_pos hr0 (Real.log_pos hx)
  by_cases hsmall : p ≤ ⌊x ^ r⌋₊
  · rw [if_pos hsmall]
    have hpPrime : p.Prime :=
      (Finset.mem_filter.mp hp).2.1
    have hlogp : 0 ≤ Real.log p := by
      exact Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)
    have hquot : 0 ≤
        Real.log p / (r * Real.log x) :=
      div_nonneg hlogp hden.le
    linarith
  · rw [if_neg hsmall, add_zero,
      le_div_iff₀ hden]
    have hfloorLt : ⌊x ^ r⌋₊ < p := by
      omega
    have hyNonneg : 0 ≤ x ^ r :=
      Real.rpow_nonneg (by linarith) r
    have hyLtP : x ^ r < (p : Real) := by
      exact (Nat.lt_floor_add_one (x ^ r)).trans_le
        (by exact_mod_cast hfloorLt)
    have hlog :
        Real.log (x ^ r) ≤ Real.log p := by
      exact Real.strictMonoOn_log.monotoneOn
        (Real.rpow_pos_of_pos (by linarith) r)
        (by
          have hpPrime : p.Prime :=
            (Finset.mem_filter.mp hp).2.1
          show (0 : Real) < (p : Real)
          exact_mod_cast hpPrime.pos)
        hyLtP.le
    rw [Real.log_rpow (by linarith)] at hlog
    simpa only [one_mul] using hlog

/-- The elementary upper Landau bound with a movable cutoff `x^r`. -/
theorem progressionPrimeCount_le_theta_add_power
    {q a : Nat} {x r : Real}
    (hx : 1 < x) (hr0 : 0 < r) :
    progressionPrimeCountReal q a x ≤
      progressionTheta q a x /
          (r * Real.log x) +
        (x ^ r + 1) := by
  classical
  have hsum :
      (∑ p ∈ progressionPrimes q a x, (1 : Real)) ≤
        ∑ p ∈ progressionPrimes q a x,
          (Real.log p / (r * Real.log x) +
            if p ≤ ⌊x ^ r⌋₊ then 1 else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    exact one_le_log_div_add_small_indicator
      hx hr0 hp
  have hfloor :
      (⌊x ^ r⌋₊ : Real) ≤ x ^ r :=
    Nat.floor_le
      (Real.rpow_nonneg (by linarith) r)
  rw [Finset.sum_add_distrib,
    ← Finset.sum_div] at hsum
  calc
    progressionPrimeCountReal q a x =
        ∑ p ∈ progressionPrimes q a x,
          (1 : Real) := by
      unfold progressionPrimeCountReal
      simp
    _ ≤
        (∑ p ∈ progressionPrimes q a x,
          Real.log p) / (r * Real.log x) +
          ∑ p ∈ progressionPrimes q a x,
            if p ≤ ⌊x ^ r⌋₊ then 1 else 0 :=
      hsum
    _ ≤
        progressionTheta q a x /
            (r * Real.log x) +
          ((⌊x ^ r⌋₊ : Real) + 1) := by
      rw [← progressionTheta_eq_sum_progressionPrimes]
      gcongr
      exact small_progression_indicator_sum_le q a x r
    _ ≤
        progressionTheta q a x /
            (r * Real.log x) +
          (x ^ r + 1) := by
      gcongr

/-- The normalized small-prime contribution tends to zero for `r < 1`. -/
theorem power_add_one_div_primeScale_tendsto_zero
    {r : Real} (hr : r < 1) :
    Tendsto
      (fun x : Real =>
        (x ^ r + 1) / (x / Real.log x))
      atTop (nhds 0) := by
  have h₁ :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hr))
      |>.tendsto_div_nhds_zero
  have h₂ :=
    Real.isLittleO_log_id_atTop
      |>.tendsto_div_nhds_zero
  have hadd := h₁.add h₂
  have heq :
      (fun x : Real =>
        Real.log x / x ^ (1 - r) +
          Real.log x / x) =ᶠ[atTop]
      (fun x : Real =>
        (x ^ r + 1) / (x / Real.log x)) := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have hlog : Real.log x ≠ 0 :=
      (Real.log_pos hx).ne'
    have hxne : x ≠ 0 := hx0.ne'
    have hpow :
        x ^ r * x ^ (1 - r) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    field_simp [hxne, hlog,
      (Real.rpow_pos_of_pos hx0 (1 - r)).ne']
    nlinarith
  simpa using hadd.congr' heq

/-- Theta PNT implies the exact real prime-counting PNT in the class. -/
theorem progressionPrimeCountReal_tendsto
    {q a : Nat} (hq : 0 < q) (ha : a.Coprime q) :
    Tendsto
      (fun x =>
        progressionPrimeCountReal q a x /
          (x / Real.log x))
      atTop
      (nhds (1 / (Nat.totient q : Real))) := by
  let phi : Real := Nat.totient q
  let delta : Real := 1 / phi
  have hphi : 0 < phi := by
    dsimp [phi]
    exact_mod_cast Nat.totient_pos.mpr hq
  have hthetaEq :=
    progressionTheta_isEquivalent hq ha
  have hdenomNe :
      ∀ᶠ x : Real in atTop,
        x / phi ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_ne_zero hx.ne' hphi.ne'
  have hthetaOne :
      Tendsto
        (fun x =>
          progressionTheta q a x / (x / phi))
        atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hdenomNe).1
      (by simpa [phi] using hthetaEq)
  have hthetaRatio :
      Tendsto
        (fun x =>
          progressionTheta q a x / x)
        atTop (nhds delta) := by
    have hdiv := hthetaOne.div_const phi
    apply hdiv.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp [hx.ne', hphi.ne']
  refine tendsto_order.2
    ⟨?_, ?_⟩
  · intro lower hlower
    have hthetaLower :
        ∀ᶠ x : Real in atTop,
          lower <
            progressionTheta q a x / x :=
      hthetaRatio.eventually (Ioi_mem_nhds hlower)
    filter_upwards
      [hthetaLower, eventually_ge_atTop 2] with x hθ hx
    have hscalePos :
        0 < x / Real.log x :=
      div_pos (by linarith)
        (Real.log_pos (by linarith))
    have hlowerCount :=
      theta_div_log_le_progressionPrimeCount
        (q := q) (a := a) hx
    have hx0 : x ≠ 0 := by
      exact ne_of_gt
        (lt_of_lt_of_le (by norm_num) hx)
    have hlogx : Real.log x ≠ 0 := by
      exact
        (Real.log_pos
          (lt_of_lt_of_le (by norm_num) hx)).ne'
    have heq :
        progressionTheta q a x / x *
            (x / Real.log x) =
          progressionTheta q a x /
            Real.log x := by
      field_simp [hx0, hlogx]
    rw [lt_div_iff₀ hscalePos]
    calc
      lower * (x / Real.log x) <
          progressionTheta q a x / x *
            (x / Real.log x) :=
        mul_lt_mul_of_pos_right hθ hscalePos
      _ = progressionTheta q a x / Real.log x := heq
      _ ≤ progressionPrimeCountReal q a x := hlowerCount
  · intro upper hupper
    have hupperDelta : delta < upper := by
      simpa [delta, phi] using hupper
    have hdeltaPos : 0 < delta := by
      dsimp [delta]
      exact one_div_pos.mpr hphi
    have hupperPos : 0 < upper :=
      hdeltaPos.trans hupperDelta
    let eta : Real :=
      (upper - delta) /
        (4 * (upper + 1))
    let r : Real := 1 / (1 + eta)
    have heta : 0 < eta := by
      dsimp [eta]
      exact div_pos (sub_pos.mpr hupperDelta)
        (mul_pos (by norm_num) (by linarith))
    have hr0 : 0 < r := by
      dsimp [r]
      exact one_div_pos.mpr (by linarith)
    have hr1 : r < 1 := by
      dsimp [r]
      exact (div_lt_one (by positivity)).2
        (by linarith)
    have hsmall :=
      power_add_one_div_primeScale_tendsto_zero hr1
    have hthetaUpper :
        ∀ᶠ x : Real in atTop,
          progressionTheta q a x / x <
            delta + (upper - delta) / 4 :=
      hthetaRatio.eventually
        (Iio_mem_nhds (by linarith))
    have hsmallUpper :
        ∀ᶠ x : Real in atTop,
          (x ^ r + 1) /
              (x / Real.log x) <
            (upper - delta) / 4 :=
      hsmall.eventually
        (Iio_mem_nhds (by linarith))
    filter_upwards
      [hthetaUpper, hsmallUpper,
        eventually_gt_atTop 1] with x hθ hsmallX hx
    have hscalePos :
        0 < x / Real.log x :=
      div_pos (by linarith) (Real.log_pos hx)
    have hupperCount :=
      progressionPrimeCount_le_theta_add_power
        (q := q) (a := a) hx hr0
    have hnormalized :
        progressionPrimeCountReal q a x /
              (x / Real.log x) ≤
          progressionTheta q a x / x / r +
            (x ^ r + 1) /
              (x / Real.log x) := by
      rw [div_le_iff₀ hscalePos]
      calc
        progressionPrimeCountReal q a x ≤
            progressionTheta q a x /
                (r * Real.log x) +
              (x ^ r + 1) :=
          hupperCount
        _ =
            (progressionTheta q a x / x / r +
              (x ^ r + 1) /
                (x / Real.log x)) *
              (x / Real.log x) := by
          field_simp [show x ≠ 0 by linarith,
            (Real.log_pos hx).ne', hr0.ne']
    refine hnormalized.trans_lt ?_
    have hrInv :
        1 / r = 1 + eta := by
      dsimp [r]
      field_simp
    have hthetaNonneg :
        0 ≤ progressionTheta q a x / x := by
      apply div_nonneg
      · unfold progressionTheta
        positivity
      · linarith
    have hrInv' : r⁻¹ = 1 + eta := by
      simpa [one_div] using hrInv
    rw [div_eq_mul_inv, hrInv']
    have hetaUpper :
        upper * eta < (upper - delta) / 4 := by
      calc
        upper * eta =
            (upper * (upper - delta)) /
              (4 * (upper + 1)) := by
          dsimp [eta]
          ring
        _ < (upper - delta) / 4 := by
          rw [div_lt_iff₀
            (mul_pos (by norm_num) (by linarith))]
          nlinarith
    have hthetaLtUpper :
        progressionTheta q a x / x < upper := by
      linarith
    have hthetaEta :
        progressionTheta q a x / x * eta <
          (upper - delta) / 4 := by
      exact
        (mul_lt_mul_of_pos_right hthetaLtUpper heta).trans
          hetaUpper
    nlinarith

/-- At an integral cutoff, the real-cutoff count is the strict natural
count at the next integer. -/
theorem progressionPrimeCountReal_natCast
    (q a x : Nat) :
    progressionPrimeCountReal q a (x : Real) =
      ((predicateCount (PrimeInModEq q a) (x + 1) : Nat) :
        Real) := by
  classical
  unfold progressionPrimeCountReal progressionPrimes predicateCount
  norm_cast
  rw [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext p
  simp [PrimeInModEq, Nat.ModEq, Nat.lt_succ_iff,
    isPrime_iff_natPrime, and_comm, and_left_comm]

/-- The real-cutoff PNT gives the project's fixed-modulus count-form PNT. -/
theorem fixedProgressionPrimeNumberTheorem
    (q : Nat) (hq : 0 < q) :
    FixedProgressionPrimeNumberTheorem q := by
  intro a ha
  classical
  unfold HasPrimeCountingAsymptotic
  let P : Nat → Prop := PrimeInModEq q a
  have hcutoffTop :
      Tendsto
        (fun x : Nat => ((x + 2 : Nat) : Real))
        atTop atTop := by
    exact
      tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 2)
  have hreal :=
    (progressionPrimeCountReal_tendsto hq ha).comp
      hcutoffTop
  have hshifted :
      Tendsto
        (fun x : Nat =>
          ((predicateCount P (x + 3) : Nat) : Real) /
            primeCountingScale x)
        atTop
        (nhds (1 / (Nat.totient q : Real))) := by
    apply hreal.congr'
    apply Eventually.of_forall
    intro x
    simp only [Function.comp_apply]
    rw [progressionPrimeCountReal_natCast]
    unfold primeCountingScale
    dsimp [P]
  let tail : Nat → Nat :=
    fun x =>
      predicateCount (fun k => P (x + k)) 3
  have htailBound :
      ∀ x, tail x ≤ 3 := by
    intro x
    dsimp [tail, predicateCount]
    exact Nat.count_le (p := fun k => P (x + k))
  have htailZero :
      Tendsto
        (fun x : Nat =>
          ((tail x : Nat) : Real) /
            primeCountingScale x)
        atTop (nhds 0) := by
    have hmajorant :
        Tendsto
          (fun x : Nat =>
            (3 : Real) / primeCountingScale x)
          atTop (nhds 0) :=
      primeCountingScale_tendsto_atTop
        |>.const_div_atTop (3 : Real)
    refine squeeze_zero'
      (g := fun x : Nat =>
        (3 : Real) / primeCountingScale x)
      ?_ ?_ hmajorant
    · exact Eventually.of_forall fun x =>
        div_nonneg (by positivity)
          (primeCountingScale_pos x).le
    · exact Eventually.of_forall fun x => by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast htailBound x
        · exact (primeCountingScale_pos x).le
  have hdifference := hshifted.sub htailZero
  have heq :
      (fun x : Nat =>
        ((predicateCount P (x + 3) : Nat) : Real) /
              primeCountingScale x -
            ((tail x : Nat) : Real) /
              primeCountingScale x) =ᶠ[atTop]
      (fun x : Nat =>
        ((predicateCount (PrimeInModEq q a) x : Nat) : Real) /
          primeCountingScale x) := by
    apply Eventually.of_forall
    intro x
    change
      ((predicateCount P (x + 3) : Nat) : Real) /
            primeCountingScale x -
          ((tail x : Nat) : Real) /
            primeCountingScale x =
        ((predicateCount (PrimeInModEq q a) x : Nat) : Real) /
          primeCountingScale x
    have hcount :
        predicateCount P (x + 3) =
          predicateCount P x + tail x := by
      simpa [tail] using predicateCount_add P x 3
    rw [hcount]
    dsimp [P]
    push_cast
    field_simp [primeCountingScale_ne_zero]
    ring
  simpa only [sub_zero] using hdifference.congr' heq

/-- The degenerate modulus zero case is vacuous: coprimality forces the
residue to be one, while no prime is congruent to one modulo zero. -/
theorem fixedProgressionPrimeNumberTheorem_zero :
    FixedProgressionPrimeNumberTheorem 0 := by
  intro a ha
  classical
  have ha1 : a = 1 := by
    simpa using ha
  subst a
  unfold HasPrimeCountingAsymptotic
  have hfalse :
      ∀ n, ¬ PrimeInModEq 0 1 n := by
    intro n hn
    have hn1 : n = 1 := by
      simpa [PrimeInModEq, Nat.ModEq] using hn.2
    have hnPrime : Nat.Prime n :=
      (isPrime_iff_natPrime n).mp hn.1
    subst n
    exact Nat.not_prime_one hnPrime
  have hcount :
      ∀ x, predicateCount (PrimeInModEq 0 1) x = 0 := by
    intro x
    unfold predicateCount
    exact Nat.count_of_forall_not fun n _ => hfalse n
  have heq :
      (fun x : Nat =>
        ((predicateCount (PrimeInModEq 0 1) x : Nat) : Real) /
          primeCountingScale x) =
      (fun _ : Nat => (0 : Real)) := by
    funext x
    rw [hcount]
    simp
  rw [heq]
  simpa using
    (tendsto_const_nhds :
      Tendsto (fun _ : Nat => (0 : Real))
        atTop (nhds 0))

end Erdos279
