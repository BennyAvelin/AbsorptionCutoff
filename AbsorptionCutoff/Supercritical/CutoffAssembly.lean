/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.SynchronousCutoff

/-!
# Assembly of the supercritical cutoff

This module continues the supercritical cutoff proof after the terminal
synchronous-coupling estimates in `SynchronousCutoff.lean`. Keeping the
cutoff-time specializations and final scalar/vector assembly here avoids
re-elaborating the completed coupling module for each small unit.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The real-valued supercritical cutoff center from
`eq:gaussian-cutoff-time`. -/
noncomputable def supercriticalCutoffTime
    (A qStar q₀ : ℝ) (N : ℕ) : ℝ :=
  ((1 / 2) * Real.log (N : ℝ) +
      Real.log |koenigsCoefficient A qStar q₀|) /
    |Real.log (deriv (V A) qStar)|

@[simp]
lemma supercriticalCutoffTime_eq
    (A qStar q₀ : ℝ) (N : ℕ) :
    supercriticalCutoffTime A qStar q₀ N =
      ((1 / 2) * Real.log (N : ℝ) +
          Real.log |koenigsCoefficient A qStar q₀|) /
        |Real.log (deriv (V A) qStar)| := rfl

/-- The natural-number floor of the shifted supercritical cutoff center from
`eq:gaussian-integer-cutoff-time`. -/
noncomputable def supercriticalIntegerCutoffTime
    (A qStar q₀ : ℝ) (N : ℕ) (c : ℝ) : ℕ :=
  ⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊

@[simp]
lemma supercriticalIntegerCutoffTime_eq
    (A qStar q₀ : ℝ) (N : ℕ) (c : ℝ) :
    supercriticalIntegerCutoffTime A qStar q₀ N c =
      ⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊ := rfl

/-- At the real cutoff center, the multiplier power exactly balances the
stationary `N⁻¹ᐟ²` scale and the Koenigs coefficient. -/
lemma rpow_supercriticalCutoffTime_eq_inv_sqrt_mul_abs_koenigsCoefficient
    {A qStar q₀ : ℝ} {N : ℕ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hN : 0 < N) :
    deriv (V A) qStar ^ supercriticalCutoffTime A qStar q₀ N =
      1 /
        (Real.sqrt (N : ℝ) *
          |koenigsCoefficient A qStar q₀|) := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hlogμ : Real.log (deriv (V A) qStar) < 0 :=
    Real.log_neg hμ.1 hμ.2
  have hlogμne : Real.log (deriv (V A) qStar) ≠ 0 :=
    hlogμ.ne
  have habslog :
      |Real.log (deriv (V A) qStar)| =
        -Real.log (deriv (V A) qStar) :=
    abs_of_neg hlogμ
  have hcoeffne :
      koenigsCoefficient A qStar q₀ ≠ 0 :=
    koenigsCoefficient_ne_zero hA hqStar hfix hq₀ hq₀ne
  have hcoeffpos : 0 < |koenigsCoefficient A qStar q₀| :=
    abs_pos.mpr hcoeffne
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hN
  have hsqrt :
      Real.exp ((1 / 2) * Real.log (N : ℝ)) =
        Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hNreal]
    congr 1
    ring
  rw [Real.rpow_def_of_pos hμ.1]
  dsimp only [supercriticalCutoffTime]
  rw [habslog]
  have hexponent :
      Real.log (deriv (V A) qStar) *
          (((1 / 2) * Real.log (N : ℝ) +
              Real.log |koenigsCoefficient A qStar q₀|) /
            -Real.log (deriv (V A) qStar)) =
        -((1 / 2) * Real.log (N : ℝ) +
            Real.log |koenigsCoefficient A qStar q₀|) := by
    field_simp [hlogμne]
  rw [hexponent, Real.exp_neg, Real.exp_add, hsqrt,
    Real.exp_log hcoeffpos]
  simp only [one_div]

/-- The logarithmic terminal-block length
`ℓ_N = ⌊b log log N⌋` from the synchronous coupling proof. -/
noncomputable def supercriticalTerminalBlockLength
    (b : ℝ) (N : ℕ) : ℕ :=
  ⌊b * Real.log (Real.log (N : ℝ))⌋₊

@[simp]
lemma supercriticalTerminalBlockLength_eq
    (b : ℝ) (N : ℕ) :
    supercriticalTerminalBlockLength b N =
      ⌊b * Real.log (Real.log (N : ℝ))⌋₊ := rfl

/-- The start `s_N = n_N(c) - 1 - ℓ_N` of the paper's terminal synchronous
coupling block. -/
noncomputable def supercriticalTerminalBlockStart
    (A qStar q₀ c b : ℝ) (N : ℕ) : ℕ :=
  supercriticalIntegerCutoffTime A qStar q₀ N c - 1 -
    supercriticalTerminalBlockLength b N

@[simp]
lemma supercriticalTerminalBlockStart_eq
    (A qStar q₀ c b : ℝ) (N : ℕ) :
    supercriticalTerminalBlockStart A qStar q₀ c b N =
      supercriticalIntegerCutoffTime A qStar q₀ N c - 1 -
        supercriticalTerminalBlockLength b N := rfl

/-- The shrinking localization radius `ρ_N = (log N)⁻²` used on the paper's
terminal synchronous-coupling block. -/
noncomputable def supercriticalTerminalRadius (N : ℕ) : ℝ :=
  (Real.log (N : ℝ))⁻¹ ^ 2

@[simp]
lemma supercriticalTerminalRadius_eq (N : ℕ) :
    supercriticalTerminalRadius N =
      (Real.log (N : ℝ))⁻¹ ^ 2 := rfl

/-- The shrinking terminal radius is positive for every dimension above
one. -/
lemma supercriticalTerminalRadius_pos {N : ℕ} (hN : 1 < N) :
    0 < supercriticalTerminalRadius N := by
  rw [supercriticalTerminalRadius]
  exact pow_pos
    (inv_pos.mpr (Real.log_pos (by exact_mod_cast hN))) 2

/-- The terminal localization radius shrinks to zero with the dimension. -/
lemma tendsto_supercriticalTerminalRadius_zero :
    Filter.Tendsto supercriticalTerminalRadius
      Filter.atTop (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  change
    Filter.Tendsto
      (fun N : ℕ => (Real.log (N : ℝ))⁻¹ ^ 2)
      Filter.atTop (nhds 0)
  simpa using hlog.inv_tendsto_atTop.pow 2

/-- The dimension-dependent terminal contraction factor
`a_N = μ_A + Lρ_N`. -/
noncomputable def supercriticalTerminalContraction
    (A qStar L : ℝ) (N : ℕ) : ℝ :=
  deriv (V A) qStar + L * supercriticalTerminalRadius N

@[simp]
lemma supercriticalTerminalContraction_eq
    (A qStar L : ℝ) (N : ℕ) :
    supercriticalTerminalContraction A qStar L N =
      deriv (V A) qStar + L * supercriticalTerminalRadius N := rfl

/-- A nonnegative Taylor constant gives a nonnegative terminal contraction
factor. -/
lemma supercriticalTerminalContraction_nonneg
    {A qStar L : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hL : 0 ≤ L)
    (N : ℕ) :
    0 ≤ supercriticalTerminalContraction A qStar L N := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  rw [supercriticalTerminalContraction]
  exact add_nonneg hμ.1.le
    (mul_nonneg hL (sq_nonneg _))

/-- The varying terminal contraction factor converges to the fixed-point
multiplier. -/
lemma tendsto_supercriticalTerminalContraction
    (A qStar L : ℝ) :
    Filter.Tendsto
      (supercriticalTerminalContraction A qStar L)
      Filter.atTop (nhds (deriv (V A) qStar)) := by
  change
    Filter.Tendsto
      (fun N : ℕ =>
        deriv (V A) qStar + L * supercriticalTerminalRadius N)
      Filter.atTop (nhds (deriv (V A) qStar))
  simpa only [mul_zero, add_zero] using
    tendsto_const_nhds.add
      (tendsto_supercriticalTerminalRadius_zero.const_mul L)

/-- The varying terminal contraction factor is eventually strictly below
one. -/
lemma eventually_supercriticalTerminalContraction_lt_one
    {A qStar L : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∀ᶠ N : ℕ in Filter.atTop,
      supercriticalTerminalContraction A qStar L N < 1 := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  exact
    tendsto_supercriticalTerminalContraction A qStar L
      (eventually_lt_nhds hμ.2)

/-- The shrinking-radius localization error `N⁻¹ρ_N⁻²` is negligible on
the terminal `N⁻¹ᐟ²` distance scale. -/
lemma
    tendsto_sqrt_nat_mul_inv_nat_div_supercriticalTerminalRadius_sq_zero :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.sqrt (N : ℝ) *
          ((1 / (N : ℝ)) / supercriticalTerminalRadius N ^ 2))
      Filter.atTop (nhds 0) := by
  have hsqrt :
      Filter.Tendsto
        (fun N : ℕ => Real.sqrt (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbase :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      1 0 4 one_ne_zero).comp hsqrt
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ =>
          16 *
            (Real.log (Real.sqrt (N : ℝ)) ^ 4 /
              Real.sqrt (N : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, one_mul, add_zero, mul_zero] using
      hbase.const_mul (16 : ℝ)
  apply hscaled.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hsqrtN : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 hNreal
  rw [supercriticalTerminalRadius,
    Real.log_sqrt (Nat.cast_nonneg N)]
  have hsqrt_sq :
      Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg N)
  field_simp [hlogN, hsqrtN.ne', hNreal.ne']
  nlinarith

/-- For every positive block parameter, the logarithmic terminal-block
length tends to infinity. -/
lemma tendsto_supercriticalTerminalBlockLength_atTop
    {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto
      (supercriticalTerminalBlockLength b)
      Filter.atTop Filter.atTop := by
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (Real.log (N : ℝ)))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hmul :
      Filter.Tendsto
        (fun N : ℕ => b * Real.log (Real.log (N : ℝ)))
        Filter.atTop Filter.atTop :=
    hloglog.const_mul_atTop hb
  change
    Filter.Tendsto
      (fun N : ℕ => ⌊b * Real.log (Real.log (N : ℝ))⌋₊)
      Filter.atTop Filter.atTop
  exact tendsto_nat_floor_atTop.comp hmul

/-- The logarithmic terminal block is negligible compared with the cutoff
time's `log N` scale. -/
lemma tendsto_supercriticalTerminalBlockLength_div_log_nat_zero
    {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto
      (fun N : ℕ =>
        (supercriticalTerminalBlockLength b N : ℝ) /
          Real.log (N : ℝ))
      Filter.atTop (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (Real.log (N : ℝ)))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hbase :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hlog
  have hunfloored :
      Filter.Tendsto
        (fun N : ℕ =>
          b * Real.log (Real.log (N : ℝ)) /
            Real.log (N : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, pow_one, one_mul, add_zero, mul_zero,
      mul_div_assoc] using
      hbase.const_mul b
  have hloglog_nonneg :
      ∀ᶠ N : ℕ in Filter.atTop,
        0 ≤ Real.log (Real.log (N : ℝ)) := by
    have hnear : ∀ᶠ x : ℝ in Filter.atTop, 0 ≤ x :=
      Filter.eventually_ge_atTop 0
    exact hloglog hnear
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hunfloored ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
    have hNreal : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos hNreal
    exact div_nonneg (Nat.cast_nonneg _) hlogN.le
  · filter_upwards
        [hloglog_nonneg, Filter.eventually_ge_atTop (2 : ℕ)] with
        N hloglogN hN
    have hNreal : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos hNreal
    have hfloor :
        (supercriticalTerminalBlockLength b N : ℝ) ≤
          b * Real.log (Real.log (N : ℝ)) := by
      exact Nat.floor_le (mul_nonneg hb.le hloglogN)
    exact (div_le_div_iff_of_pos_right hlogN).2 hfloor

/-- The logarithmic terminal-block length times the shrinking localization
radius tends to zero. -/
lemma tendsto_supercriticalTerminalBlockLength_mul_terminalRadius_zero
    {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto
      (fun N : ℕ =>
        (supercriticalTerminalBlockLength b N : ℝ) *
          supercriticalTerminalRadius N)
      Filter.atTop (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto
        (fun N : ℕ => (Real.log (N : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
    convert hlog.inv_tendsto_atTop using 1
    ext N
    rfl
  have hproduct :
      Filter.Tendsto
        (fun N : ℕ =>
          ((supercriticalTerminalBlockLength b N : ℝ) /
              Real.log (N : ℝ)) *
            (Real.log (N : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_supercriticalTerminalBlockLength_div_log_nat_zero hb).mul
        hinv
  apply hproduct.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  rw [supercriticalTerminalRadius]
  field_simp [hlogN]

/-- The varying contraction factor has the same terminal-block power as the
fixed-point multiplier, up to a factor tending to one. -/
lemma
    tendsto_supercriticalTerminalContraction_div_multiplier_pow_blockLength_one
    {A qStar L b : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hL : 0 ≤ L)
    (hb : 0 < b) :
    Filter.Tendsto
      (fun N : ℕ =>
        (supercriticalTerminalContraction A qStar L N /
            deriv (V A) qStar) ^
          supercriticalTerminalBlockLength b N)
      Filter.atTop (nhds 1) := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  let k : ℝ := L / deriv (V A) qStar
  have hk : 0 ≤ k := by
    dsimp only [k]
    exact div_nonneg hL hμ.1.le
  have hperturb :
      Filter.Tendsto
        (fun N : ℕ =>
          (supercriticalTerminalBlockLength b N : ℝ) *
            (k * supercriticalTerminalRadius N))
        Filter.atTop (nhds 0) := by
    have hscaled :
        Filter.Tendsto
          (fun N : ℕ =>
            k *
              ((supercriticalTerminalBlockLength b N : ℝ) *
                supercriticalTerminalRadius N))
          Filter.atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_supercriticalTerminalBlockLength_mul_terminalRadius_zero hb)
          |>.const_mul k
    apply hscaled.congr'
    filter_upwards with N
    ring
  have hexp :
      Filter.Tendsto
        (fun N : ℕ =>
          Real.exp
            ((supercriticalTerminalBlockLength b N : ℝ) *
              (k * supercriticalTerminalRadius N)))
        Filter.atTop (nhds 1) := by
    convert
      Real.continuous_exp.continuousAt.tendsto.comp hperturb using 1
    · ext N
      rfl
    · rw [Real.exp_zero]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hexp ?_ ?_
  · filter_upwards with N
    have hbase :
        supercriticalTerminalContraction A qStar L N /
            deriv (V A) qStar =
          1 + k * supercriticalTerminalRadius N := by
      dsimp only [supercriticalTerminalContraction, k]
      field_simp [hμ.1.ne']
    rw [hbase]
    exact one_le_pow₀
      (by
        have hrho : 0 ≤ supercriticalTerminalRadius N :=
          sq_nonneg _
        linarith [mul_nonneg hk hrho])
  · filter_upwards with N
    have hbase :
        supercriticalTerminalContraction A qStar L N /
            deriv (V A) qStar =
          1 + k * supercriticalTerminalRadius N := by
      dsimp only [supercriticalTerminalContraction, k]
      field_simp [hμ.1.ne']
    rw [hbase]
    let x : ℝ := k * supercriticalTerminalRadius N
    have hx : 0 ≤ x := by
      dsimp only [x]
      exact mul_nonneg hk (sq_nonneg _)
    calc
      (1 + x) ^ supercriticalTerminalBlockLength b N ≤
          Real.exp x ^ supercriticalTerminalBlockLength b N := by
        apply pow_le_pow_left₀ (by linarith)
        linarith [Real.add_one_le_exp x]
      _ =
          Real.exp
            ((supercriticalTerminalBlockLength b N : ℝ) * x) := by
        rw [Real.exp_nat_mul]
      _ =
          Real.exp
            ((supercriticalTerminalBlockLength b N : ℝ) *
              (k * supercriticalTerminalRadius N)) := by
        rfl

/-- Near the positive fixed point, the derivative is bounded by its
multiplier plus a linear Taylor error. -/
lemma exists_abs_deriv_V_le_multiplier_add_mul_abs_sub_fixed
    {A qStar : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ Set.Icc (qStar / 2) 1,
        |deriv (V A) x| ≤
          deriv (V A) qStar + L * |x - qStar| := by
  have hA0 : A ≠ 0 := by linarith
  obtain ⟨L, hL, hLip⟩ :=
    exists_deriv_V_lipschitzOn_Icc
      (A := A) (a := qStar / 2) (b := 1)
      hA0 (by linarith [hqStar.1])
  have hμ :=
    V_multiplier_mem_Ioo hA0 hqStar hfix
  refine ⟨L, hL, ?_⟩
  intro x hx
  have hqmem : qStar ∈ Set.Icc (qStar / 2) 1 := by
    constructor <;> linarith [hqStar.1, hqStar.2]
  have hdiff :=
    hLip qStar hqmem x hx
  calc
    |deriv (V A) x| =
        |(deriv (V A) x - deriv (V A) qStar) +
          deriv (V A) qStar| := by ring_nf
    _ ≤
        |deriv (V A) x - deriv (V A) qStar| +
          |deriv (V A) qStar| :=
      abs_add_le _ _
    _ ≤ L * |x - qStar| + deriv (V A) qStar := by
      exact add_le_add hdiff (le_of_eq (abs_of_pos hμ.1))
    _ = deriv (V A) qStar + L * |x - qStar| := by ring

/-- On every sufficiently small symmetric interval around the fixed point,
the mean map contracts with factor `μ + Lρ`. -/
lemma exists_abs_V_sub_le_multiplier_add_mul_radius
    {A qStar : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {ρ x y : ℝ},
        0 ≤ ρ →
        ρ ≤ min (qStar / 2) ((1 - qStar) / 2) →
        |x - qStar| ≤ ρ →
        |y - qStar| ≤ ρ →
        |V A x - V A y| ≤
          (deriv (V A) qStar + L * ρ) * |x - y| := by
  have hA0 : A ≠ 0 := by linarith
  obtain ⟨L, hL, hderiv⟩ :=
    exists_abs_deriv_V_le_multiplier_add_mul_abs_sub_fixed
      hA hqStar hfix
  refine ⟨L, hL, ?_⟩
  intro ρ x y hρ0 hρmax hx hy
  have hρq : ρ ≤ qStar / 2 :=
    hρmax.trans (min_le_left _ _)
  have hρone : ρ ≤ (1 - qStar) / 2 :=
    hρmax.trans (min_le_right _ _)
  let I : Set ℝ := Set.Icc (qStar - ρ) (qStar + ρ)
  have hxI : x ∈ I := by
    dsimp only [I]
    rw [abs_le] at hx
    constructor <;> linarith
  have hyI : y ∈ I := by
    dsimp only [I]
    rw [abs_le] at hy
    constructor <;> linarith
  have hdiff :
      ∀ z ∈ I, DifferentiableAt ℝ (V A) z := by
    intro z hz
    change z ∈ Set.Icc (qStar - ρ) (qStar + ρ) at hz
    have hzpos : 0 < z := by
      linarith [hqStar.1, hz.1]
    exact (hasDerivAt_V hA0 hzpos).differentiableAt
  have hderivBound :
      ∀ z ∈ I,
        ‖deriv (V A) z‖ ≤
          deriv (V A) qStar + L * ρ := by
    intro z hz
    change z ∈ Set.Icc (qStar - ρ) (qStar + ρ) at hz
    have hzI : z ∈ Set.Icc (qStar / 2) 1 := by
      exact ⟨by linarith [hz.1], by linarith [hqStar.2, hz.2]⟩
    have hzclose : |z - qStar| ≤ ρ := by
      rw [abs_le]
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    rw [Real.norm_eq_abs]
    calc
      |deriv (V A) z| ≤
          deriv (V A) qStar + L * |z - qStar| :=
        hderiv z hzI
      _ ≤ deriv (V A) qStar + L * ρ := by
        gcongr
  have hmv :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      hdiff hderivBound (convex_Icc (qStar - ρ) (qStar + ρ))
      hxI hyI
  simpa only [I, Real.norm_eq_abs, abs_sub_comm] using hmv

/-- One Taylor constant supplies all eventual shrinking-interval hypotheses:
positive interior radius, a genuine contraction factor, and the derivative
bound required by the synchronous recursion. -/
theorem exists_eventually_supercriticalTerminal_contraction_data
    {A qStar : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        0 < supercriticalTerminalRadius N ∧
        supercriticalTerminalRadius N ≤
          min (qStar / 2) ((1 - qStar) / 2) ∧
        0 ≤ supercriticalTerminalContraction A qStar L N ∧
        supercriticalTerminalContraction A qStar L N < 1 ∧
        ∀ x : ℝ,
          |x - qStar| ≤ supercriticalTerminalRadius N →
          |deriv (V A) x| ≤
            supercriticalTerminalContraction A qStar L N := by
  obtain ⟨L, hL, hderiv⟩ :=
    exists_abs_deriv_V_le_multiplier_add_mul_abs_sub_fixed
      hA hqStar hfix
  refine ⟨L, hL, ?_⟩
  let d : ℝ := min (qStar / 2) ((1 - qStar) / 2)
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min
      (by linarith [hqStar.1])
      (by linarith [hqStar.2])
  have hradius :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalRadius N < d :=
    tendsto_supercriticalTerminalRadius_zero
      (eventually_lt_nhds hd)
  have hcontraction :=
    eventually_supercriticalTerminalContraction_lt_one
      (L := L) hA hqStar hfix
  filter_upwards
      [hradius, hcontraction, Filter.eventually_ge_atTop (2 : ℕ)] with
      N hradiusN hcontractionN hN
  have hradiusPos : 0 < supercriticalTerminalRadius N :=
    supercriticalTerminalRadius_pos (show 1 < N by omega)
  have hradiusBound :
      supercriticalTerminalRadius N ≤
        min (qStar / 2) ((1 - qStar) / 2) := by
    dsimp only [d] at hradiusN
    exact hradiusN.le
  refine ⟨hradiusPos, hradiusBound,
    supercriticalTerminalContraction_nonneg
      hA hqStar hfix hL N,
    hcontractionN, ?_⟩
  intro x hx
  have hradiusQ :
      supercriticalTerminalRadius N ≤ qStar / 2 :=
    hradiusBound.trans (min_le_left _ _)
  have hradiusOne :
      supercriticalTerminalRadius N ≤ (1 - qStar) / 2 :=
    hradiusBound.trans (min_le_right _ _)
  have hxI : x ∈ Set.Icc (qStar / 2) 1 := by
    rw [abs_le] at hx
    constructor <;> linarith [hqStar.2]
  calc
    |deriv (V A) x| ≤
        deriv (V A) qStar + L * |x - qStar| :=
      hderiv x hxI
    _ ≤
        deriv (V A) qStar +
          L * supercriticalTerminalRadius N := by
      gcongr
    _ = supercriticalTerminalContraction A qStar L N := rfl

/-- For a supercritical positive fixed point, the paper's real cutoff center
tends to infinity with the dimension. -/
lemma tendsto_supercriticalCutoffTime_atTop
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    Filter.Tendsto
      (supercriticalCutoffTime A qStar q₀)
      Filter.atTop Filter.atTop := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hlogμ : Real.log (deriv (V A) qStar) < 0 :=
    Real.log_neg hμ.1 hμ.2
  have hden : 0 < |Real.log (deriv (V A) qStar)| :=
    abs_pos.mpr hlogμ.ne
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hhalf :
      Filter.Tendsto
        (fun N : ℕ => (1 / 2) * Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    hlog.const_mul_atTop (by norm_num)
  have hadd :
      Filter.Tendsto
        (fun N : ℕ =>
          (1 / 2) * Real.log (N : ℝ) +
            Real.log |koenigsCoefficient A qStar q₀|)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop
      (Real.log |koenigsCoefficient A qStar q₀|) hhalf
  change
    Filter.Tendsto
      (fun N : ℕ =>
        ((1 / 2) * Real.log (N : ℝ) +
            Real.log |koenigsCoefficient A qStar q₀|) /
          |Real.log (deriv (V A) qStar)|)
      Filter.atTop Filter.atTop
  exact hadd.atTop_div_const hden

/-- Every fixed shift of the paper's floored integer cutoff time tends to
infinity with the dimension. -/
lemma tendsto_supercriticalIntegerCutoffTime_atTop
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (c : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        supercriticalIntegerCutoffTime A qStar q₀ N c)
      Filter.atTop Filter.atTop := by
  have hcenter :=
    tendsto_supercriticalCutoffTime_atTop
      (q₀ := q₀) hA hqStar hfix
  have hshift :
      Filter.Tendsto
        (fun N : ℕ => supercriticalCutoffTime A qStar q₀ N + c)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c hcenter
  change
    Filter.Tendsto
      (fun N : ℕ =>
        ⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊)
      Filter.atTop Filter.atTop
  exact tendsto_nat_floor_atTop.comp hshift

/-- The real cutoff center has the paper's first-order logarithmic growth. -/
lemma tendsto_supercriticalCutoffTime_div_log_nat
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    Filter.Tendsto
      (fun N : ℕ =>
        supercriticalCutoffTime A qStar q₀ N /
          Real.log (N : ℝ))
      Filter.atTop
      (nhds ((1 / 2) / |Real.log (deriv (V A) qStar)|)) := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hlogμ : Real.log (deriv (V A) qStar) < 0 :=
    Real.log_neg hμ.1 hμ.2
  have hden : 0 < |Real.log (deriv (V A) qStar)| :=
    abs_pos.mpr hlogμ.ne
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnormalized :
      Filter.Tendsto
        (fun N : ℕ =>
          ((1 / 2) +
              Real.log |koenigsCoefficient A qStar q₀| /
                Real.log (N : ℝ)) /
            |Real.log (deriv (V A) qStar)|)
        Filter.atTop
        (nhds ((1 / 2) / |Real.log (deriv (V A) qStar)|)) := by
    simpa using
      (tendsto_const_nhds.add
        (hlog.const_div_atTop
          (Real.log |koenigsCoefficient A qStar q₀|))).div_const
            |Real.log (deriv (V A) qStar)|
  apply hnormalized.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos hNreal).ne'
  dsimp only [supercriticalCutoffTime]
  field_simp [hden.ne', hlogN]

/-- Every fixed shift of the floored integer cutoff time has the same
first-order logarithmic growth as the real cutoff center. -/
lemma tendsto_supercriticalIntegerCutoffTime_div_log_nat
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (c : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) /
          Real.log (N : ℝ))
      Filter.atTop
      (nhds ((1 / 2) / |Real.log (deriv (V A) qStar)|)) := by
  let L : ℝ := (1 / 2) / |Real.log (deriv (V A) qStar)|
  have hcenter :=
    tendsto_supercriticalCutoffTime_div_log_nat
      (q₀ := q₀) hA hqStar hfix
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htranslated (d : ℝ) :
      Filter.Tendsto
        (fun N : ℕ =>
          (supercriticalCutoffTime A qStar q₀ N + d) /
            Real.log (N : ℝ))
        Filter.atTop (nhds L) := by
    simpa only [add_div, add_zero, L] using
      hcenter.add (hlog.const_div_atTop d)
  have hshiftAtTop :
      Filter.Tendsto
        (fun N : ℕ => supercriticalCutoffTime A qStar q₀ N + c)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c
      (tendsto_supercriticalCutoffTime_atTop
        (q₀ := q₀) hA hqStar hfix)
  have hnonneg :
      ∀ᶠ N : ℕ in Filter.atTop,
        0 ≤ supercriticalCutoffTime A qStar q₀ N + c :=
    hshiftAtTop.eventually (Filter.eventually_ge_atTop 0)
  have hlower :
      Filter.Tendsto
        (fun N : ℕ =>
          (supercriticalCutoffTime A qStar q₀ N + c - 1) /
            Real.log (N : ℝ))
        Filter.atTop (nhds L) := by
    convert htranslated (c - 1) using 1
    funext N
    ring
  have hupper :
      Filter.Tendsto
        (fun N : ℕ =>
          (supercriticalCutoffTime A qStar q₀ N + c) /
            Real.log (N : ℝ))
        Filter.atTop (nhds L) :=
    htranslated c
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower hupper ?_ ?_
  · filter_upwards
        [hnonneg, Filter.eventually_ge_atTop (2 : ℕ)] with
        N hnonnegN hN
    have hNreal : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos hNreal
    have hfloor :
        supercriticalCutoffTime A qStar q₀ N + c - 1 ≤
          (⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊ : ℝ) := by
      linarith [
        Nat.lt_floor_add_one
          (supercriticalCutoffTime A qStar q₀ N + c)]
    change
      (supercriticalCutoffTime A qStar q₀ N + c - 1) /
          Real.log (N : ℝ) ≤
        (⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊ : ℝ) /
          Real.log (N : ℝ)
    exact (div_le_div_iff_of_pos_right hlogN).2 hfloor
  · filter_upwards
        [hnonneg, Filter.eventually_ge_atTop (2 : ℕ)] with
        N hnonnegN hN
    have hNreal : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos hNreal
    have hfloor :
        (⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊ : ℝ) ≤
          supercriticalCutoffTime A qStar q₀ N + c :=
      Nat.floor_le hnonnegN
    change
      (⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊ : ℝ) /
          Real.log (N : ℝ) ≤
        (supercriticalCutoffTime A qStar q₀ N + c) /
          Real.log (N : ℝ)
    exact (div_le_div_iff_of_pos_right hlogN).2 hfloor

/-- The paper's terminal block and its preceding step eventually fit inside
the shifted integer cutoff time. -/
lemma eventually_supercriticalTerminalBlockLength_add_one_le_integerCutoffTime
    {A qStar q₀ b : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hb : 0 < b)
    (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      supercriticalTerminalBlockLength b N + 1 ≤
        supercriticalIntegerCutoffTime A qStar q₀ N c := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hlogμ : Real.log (deriv (V A) qStar) < 0 :=
    Real.log_neg hμ.1 hμ.2
  have hden : 0 < |Real.log (deriv (V A) qStar)| :=
    abs_pos.mpr hlogμ.ne
  let L : ℝ := (1 / 2) / |Real.log (deriv (V A) qStar)|
  have hL : 0 < L := by
    dsimp only [L]
    exact div_pos (by norm_num) hden
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hblock :
      Filter.Tendsto
        (fun N : ℕ =>
          ((supercriticalTerminalBlockLength b N : ℝ) + 1) /
            Real.log (N : ℝ))
        Filter.atTop (nhds 0) := by
    simpa only [add_div, add_zero] using
      (tendsto_supercriticalTerminalBlockLength_div_log_nat_zero hb).add
        (hlog.const_div_atTop 1)
  have hcutoff :
      Filter.Tendsto
        (fun N : ℕ =>
          (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) /
            Real.log (N : ℝ))
        Filter.atTop (nhds L) := by
    simpa only [L] using
      tendsto_supercriticalIntegerCutoffTime_div_log_nat
        (q₀ := q₀) hA hqStar hfix c
  have hblock_lt :
      ∀ᶠ N : ℕ in Filter.atTop,
        ((supercriticalTerminalBlockLength b N : ℝ) + 1) /
            Real.log (N : ℝ) <
          L / 2 :=
    hblock (eventually_lt_nhds (by linarith))
  have hcutoff_gt :
      ∀ᶠ N : ℕ in Filter.atTop,
        L / 2 <
          (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) /
            Real.log (N : ℝ) :=
    hcutoff (eventually_gt_nhds (by linarith))
  filter_upwards
      [hblock_lt, hcutoff_gt, Filter.eventually_ge_atTop (2 : ℕ)] with
      N hblockN hcutoffN hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos hNreal
  have hblockN' :
      (supercriticalTerminalBlockLength b N : ℝ) + 1 <
        (L / 2) * Real.log (N : ℝ) :=
    (div_lt_iff₀ hlogN).1 hblockN
  have hcutoffN' :
      (L / 2) * Real.log (N : ℝ) <
        (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) :=
    (lt_div_iff₀ hlogN).1 hcutoffN
  exact_mod_cast (hblockN'.trans hcutoffN').le

/-- Eventually the terminal block ends exactly one step before the shifted
integer cutoff time; no natural-number subtraction is truncated. -/
lemma eventually_supercriticalTerminalBlockStart_add_length_eq_integerCutoffTime_sub_one
    {A qStar q₀ b : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hb : 0 < b)
    (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N =
        supercriticalIntegerCutoffTime A qStar q₀ N c - 1 := by
  filter_upwards
      [eventually_supercriticalTerminalBlockLength_add_one_le_integerCutoffTime
        (q₀ := q₀) hA hqStar hfix hb c] with N hN
  simp only [supercriticalTerminalBlockStart]
  omega

/-- The natural floor and the one-step terminal endpoint cost at most two
multiplier powers relative to the exact real cutoff center. -/
lemma eventually_pow_terminalBlockStart_le_cutoff_rpow
    {A qStar q₀ b : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hb : 0 < b)
    (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      deriv (V A) qStar ^
          supercriticalTerminalBlockStart A qStar q₀ c b N ≤
        (1 /
            (Real.sqrt (N : ℝ) *
              |koenigsCoefficient A qStar q₀|)) *
          deriv (V A) qStar ^
            (c - (supercriticalTerminalBlockLength b N : ℝ)) *
          deriv (V A) qStar ^ (-2 : ℝ) := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  filter_upwards
      [eventually_supercriticalTerminalBlockLength_add_one_le_integerCutoffTime
        (q₀ := q₀) hA hqStar hfix hb c,
       eventually_supercriticalTerminalBlockStart_add_length_eq_integerCutoffTime_sub_one
        (q₀ := q₀) hA hqStar hfix hb c,
       Filter.eventually_ge_atTop (1 : ℕ)] with N hdominates hend hN
  let μ := deriv (V A) qStar
  let t := supercriticalCutoffTime A qStar q₀ N
  let n := supercriticalIntegerCutoffTime A qStar q₀ N c
  let ℓ := supercriticalTerminalBlockLength b N
  let s := supercriticalTerminalBlockStart A qStar q₀ c b N
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hone : 1 ≤ n := by
    dsimp only [n]
    omega
  have hend' :
      (s : ℝ) + (ℓ : ℝ) = (n : ℝ) - 1 := by
    exact_mod_cast hend
  have hfloor : t + c < (n : ℝ) + 1 := by
    dsimp only [t, n]
    exact Nat.lt_floor_add_one
      (supercriticalCutoffTime A qStar q₀ N + c)
  have hexponent :
      t + c - (ℓ : ℝ) - 2 ≤ (s : ℝ) := by
    linarith
  have hpow :
      μ ^ s ≤ μ ^ (t + c - (ℓ : ℝ) - 2) := by
    rw [← Real.rpow_natCast]
    exact
      Real.rpow_le_rpow_of_exponent_ge hμ.1 hμ.2.le hexponent
  have hnormalize :
      μ ^ t =
        1 /
          (Real.sqrt (N : ℝ) *
            |koenigsCoefficient A qStar q₀|) := by
    simpa only [μ, t] using
      rpow_supercriticalCutoffTime_eq_inv_sqrt_mul_abs_koenigsCoefficient
        hA hqStar hfix hq₀ hq₀ne hNpos
  calc
    μ ^ s ≤ μ ^ (t + c - (ℓ : ℝ) - 2) := hpow
    _ = μ ^ (t + (c - (ℓ : ℝ)) + (-2 : ℝ)) := by
      congr 1
      ring
    _ = μ ^ t * μ ^ (c - (ℓ : ℝ)) * μ ^ (-2 : ℝ) := by
      rw [Real.rpow_add hμ.1, Real.rpow_add hμ.1]
    _ =
        (1 /
            (Real.sqrt (N : ℝ) *
              |koenigsCoefficient A qStar q₀|)) *
          μ ^ (c - (ℓ : ℝ)) * μ ^ (-2 : ℝ) := by
      rw [hnormalize]

/-- The terminal block start retains the cutoff time's first-order
logarithmic growth. -/
lemma tendsto_supercriticalTerminalBlockStart_div_log_nat
    {A qStar q₀ b : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hb : 0 < b)
    (c : ℝ) :
    Filter.Tendsto
      (fun N : ℕ =>
        (supercriticalTerminalBlockStart A qStar q₀ c b N : ℝ) /
          Real.log (N : ℝ))
      Filter.atTop
      (nhds ((1 / 2) / |Real.log (deriv (V A) qStar)|)) := by
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hcutoff :=
    tendsto_supercriticalIntegerCutoffTime_div_log_nat
      (q₀ := q₀) hA hqStar hfix c
  have hlength :=
    tendsto_supercriticalTerminalBlockLength_div_log_nat_zero hb
  have hnormalized :
      Filter.Tendsto
        (fun N : ℕ =>
          (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) /
              Real.log (N : ℝ) -
            1 / Real.log (N : ℝ) -
            (supercriticalTerminalBlockLength b N : ℝ) /
              Real.log (N : ℝ))
        Filter.atTop
        (nhds ((1 / 2) / |Real.log (deriv (V A) qStar)|)) := by
    simpa only [sub_zero] using
      (hcutoff.sub (hlog.const_div_atTop 1)).sub hlength
  apply hnormalized.congr'
  filter_upwards
      [eventually_supercriticalTerminalBlockLength_add_one_le_integerCutoffTime
        (q₀ := q₀) hA hqStar hfix hb c,
       eventually_supercriticalTerminalBlockStart_add_length_eq_integerCutoffTime_sub_one
        (q₀ := q₀) hA hqStar hfix hb c,
       Filter.eventually_ge_atTop (2 : ℕ)] with N hdominates hend hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos hNreal).ne'
  have hone :
      1 ≤ supercriticalIntegerCutoffTime A qStar q₀ N c := by
    omega
  have hend' :
      (supercriticalTerminalBlockStart A qStar q₀ c b N : ℝ) +
          (supercriticalTerminalBlockLength b N : ℝ) =
        (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) - 1 := by
    exact_mod_cast hend
  field_simp [hlogN]
  linarith

/-- The start of the paper's terminal synchronous-coupling block tends to
infinity with the dimension. -/
lemma tendsto_supercriticalTerminalBlockStart_atTop
    {A qStar q₀ b : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hb : 0 < b)
    (c : ℝ) :
    Filter.Tendsto
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      Filter.atTop Filter.atTop := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hlogμ : Real.log (deriv (V A) qStar) < 0 :=
    Real.log_neg hμ.1 hμ.2
  have hden : 0 < |Real.log (deriv (V A) qStar)| :=
    abs_pos.mpr hlogμ.ne
  let L : ℝ := (1 / 2) / |Real.log (deriv (V A) qStar)|
  have hL : 0 < L := by
    dsimp only [L]
    exact div_pos (by norm_num) hden
  have hratio :
      Filter.Tendsto
        (fun N : ℕ =>
          (supercriticalTerminalBlockStart A qStar q₀ c b N : ℝ) /
            Real.log (N : ℝ))
        Filter.atTop (nhds L) := by
    simpa only [L] using
      tendsto_supercriticalTerminalBlockStart_div_log_nat
        (q₀ := q₀) hA hqStar hfix hb c
  have hratio_gt :
      ∀ᶠ N : ℕ in Filter.atTop,
        L / 2 <
          (supercriticalTerminalBlockStart A qStar q₀ c b N : ℝ) /
            Real.log (N : ℝ) :=
    hratio (eventually_gt_nhds (by linarith))
  have hlog :
      Filter.Tendsto
        (fun N : ℕ => Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale :
      Filter.Tendsto
        (fun N : ℕ => (L / 2) * Real.log (N : ℝ))
        Filter.atTop Filter.atTop :=
    hlog.const_mul_atTop (by linarith)
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  refine Filter.tendsto_atTop.2 ?_
  intro M
  filter_upwards
      [hscale.eventually (Filter.eventually_ge_atTop M), hratio_gt,
       Filter.eventually_ge_atTop (2 : ℕ)] with N hscaleN hratioN hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos hNreal
  have hlower :
      (L / 2) * Real.log (N : ℝ) <
        (supercriticalTerminalBlockStart A qStar q₀ c b N : ℝ) :=
    (lt_div_iff₀ hlogN).1 hratioN
  exact hscaleN.trans hlower.le

/-- Uniformly for initial states converging to a nonstationary macroscopic
radius, the deterministic orbit at the terminal block start is bounded by a
fixed constant times the corresponding multiplier power. -/
lemma
    exists_eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_mul_pow
    {A qStar q₀ b : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b)
    (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[
            supercriticalTerminalBlockStart A qStar q₀ c b N] (q N) -
            qStar| ≤
          C * deriv (V A) qStar ^
            supercriticalTerminalBlockStart A qStar q₀ c b N := by
  obtain ⟨r, hr, hq₀K, hKD, huniform⟩ :=
    exists_tendstoUniformlyOn_normalized_V_orbit_sub_fixed
      hA hqStar hfix hq₀ hq₀ne
  let K : Set ℝ := Set.Icc (q₀ - r) (min (q₀ + r) 1)
  have hcoeffCont :
      ContinuousOn (koenigsCoefficient A qStar) K :=
    (continuousOn_koenigsCoefficient hA hqStar hfix).mono hKD
  obtain ⟨B, hB⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hcoeffCont
  have hB0 : 0 ≤ B :=
    (norm_nonneg (koenigsCoefficient A qStar q₀)).trans
      (hB q₀ hq₀K)
  let C : ℝ := B + 1
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  have hqclose :
      ∀ᶠ N : ℕ in Filter.atTop,
        dist (q N) q₀ < r :=
    hq (Metric.ball_mem_nhds q₀ hr)
  have hqK :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ K := by
    filter_upwards [hqclose, hqmem] with N hclose hqN
    rw [Real.dist_eq, abs_lt] at hclose
    change q₀ - r ≤ q N ∧ q N ≤ min (q₀ + r) 1
    exact ⟨by linarith, le_min (by linarith) hqN.2⟩
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  have huniform_one :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ x ∈ K,
          dist (koenigsCoefficient A qStar x)
            (((V A)^[n] x - qStar) *
              (deriv (V A) qStar)⁻¹ ^ n) < 1 := by
    simpa only [K] using huniform 1 zero_lt_one
  have htime :=
    tendsto_supercriticalTerminalBlockStart_atTop
      (q₀ := q₀) hA hqStar hfix hb c
  have hclose_at_time :
      ∀ᶠ N : ℕ in Filter.atTop,
        dist (koenigsCoefficient A qStar (q N))
          (((V A)^[
              supercriticalTerminalBlockStart A qStar q₀ c b N] (q N) -
                qStar) *
            (deriv (V A) qStar)⁻¹ ^
              supercriticalTerminalBlockStart A qStar q₀ c b N) < 1 := by
    filter_upwards [htime huniform_one, hqK] with N hN hqKN
    exact hN (q N) hqKN
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  filter_upwards [hclose_at_time, hqK] with N hcloseN hqKN
  let s := supercriticalTerminalBlockStart A qStar q₀ c b N
  let x := (V A)^[s] (q N) - qStar
  have hcoeff :
      |koenigsCoefficient A qStar (q N)| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB (q N) hqKN
  have hnormalized :
      |x * (deriv (V A) qStar)⁻¹ ^ s| ≤ C := by
    change
      dist (koenigsCoefficient A qStar (q N))
        (x * (deriv (V A) qStar)⁻¹ ^ s) < 1 at hcloseN
    rw [Real.dist_eq] at hcloseN
    calc
      |x * (deriv (V A) qStar)⁻¹ ^ s| =
          |(x * (deriv (V A) qStar)⁻¹ ^ s -
              koenigsCoefficient A qStar (q N)) +
            koenigsCoefficient A qStar (q N)| := by ring_nf
      _ ≤
          |x * (deriv (V A) qStar)⁻¹ ^ s -
              koenigsCoefficient A qStar (q N)| +
            |koenigsCoefficient A qStar (q N)| :=
        abs_add_le _ _
      _ ≤ 1 + B := by
        apply add_le_add _ hcoeff
        rw [abs_sub_comm]
        exact hcloseN.le
      _ = C := by simp only [C]; ring
  have hpow : 0 < deriv (V A) qStar ^ s :=
    pow_pos hμ.1 s
  have hdiv : |x| / deriv (V A) qStar ^ s ≤ C := by
    simpa only [inv_pow, abs_mul, abs_inv, abs_pow,
      abs_of_pos hμ.1, div_eq_mul_inv] using hnormalized
  simpa only [s, x] using (div_le_iff₀ hpow).1 hdiv

/-- The deterministic center at the terminal block start has the paper's
explicit `N⁻¹ᐟ² μ^(c-ℓ_N)` scale, uniformly over convergent initial
sequences. -/
lemma
    exists_eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_mul_rpow_div_sqrt
    {A qStar q₀ b : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b)
    (c : ℝ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[
            supercriticalTerminalBlockStart A qStar q₀ c b N] (q N) -
            qStar| ≤
          D *
              deriv (V A) qStar ^
                (c - (supercriticalTerminalBlockLength b N : ℝ)) /
            Real.sqrt (N : ℝ) := by
  obtain ⟨C, hC, hcenter⟩ :=
    exists_eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_mul_pow
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hcoeffne :
      koenigsCoefficient A qStar q₀ ≠ 0 :=
    koenigsCoefficient_ne_zero hA hqStar hfix hq₀ hq₀ne
  have hcoeffpos : 0 < |koenigsCoefficient A qStar q₀| :=
    abs_pos.mpr hcoeffne
  let D : ℝ :=
    C * deriv (V A) qStar ^ (-2 : ℝ) /
      |koenigsCoefficient A qStar q₀|
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos
      (mul_pos hC (Real.rpow_pos_of_pos hμ.1 (-2 : ℝ)))
      hcoeffpos
  refine ⟨D, hD, ?_⟩
  have hmultiplier :=
    eventually_pow_terminalBlockStart_le_cutoff_rpow
      hA hqStar hfix hq₀ hq₀ne hb c
  filter_upwards
      [hcenter, hmultiplier, Filter.eventually_ge_atTop (1 : ℕ)] with
      N hcenterN hmultiplierN hN
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hsqrt : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 hNreal
  calc
    |(V A)^[
          supercriticalTerminalBlockStart A qStar q₀ c b N] (q N) -
          qStar| ≤
        C * deriv (V A) qStar ^
          supercriticalTerminalBlockStart A qStar q₀ c b N :=
      hcenterN
    _ ≤
        C *
          ((1 /
              (Real.sqrt (N : ℝ) *
                |koenigsCoefficient A qStar q₀|)) *
            deriv (V A) qStar ^
              (c - (supercriticalTerminalBlockLength b N : ℝ)) *
            deriv (V A) qStar ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmultiplierN hC.le
    _ =
        D *
              deriv (V A) qStar ^
                (c - (supercriticalTerminalBlockLength b N : ℝ)) /
            Real.sqrt (N : ℝ) := by
      dsimp only [D]
      field_simp [hsqrt.ne', hcoeffne]

/-- Every fixed-shift integer cutoff time is eventually bounded by a positive
constant times `log N`, as used for the paper's dynamic horizon. -/
lemma exists_eventually_supercriticalIntegerCutoffTime_le_mul_log_nat
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) ≤
          C * Real.log (N : ℝ) := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hlogμ : Real.log (deriv (V A) qStar) < 0 :=
    Real.log_neg hμ.1 hμ.2
  have hden : 0 < |Real.log (deriv (V A) qStar)| :=
    abs_pos.mpr hlogμ.ne
  let L : ℝ := (1 / 2) / |Real.log (deriv (V A) qStar)|
  let C : ℝ := L + 1
  have hL : 0 < L := by
    dsimp only [L]
    exact div_pos (by norm_num) hden
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  have hratio :=
    tendsto_supercriticalIntegerCutoffTime_div_log_nat
      (q₀ := q₀) hA hqStar hfix c
  have hratio' :
      Filter.Tendsto
        (fun N : ℕ =>
          (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) /
            Real.log (N : ℝ))
        Filter.atTop (nhds L) := by
    simpa only [L] using hratio
  have hratio_lt :
      ∀ᶠ N : ℕ in Filter.atTop,
        (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) /
            Real.log (N : ℝ) <
          C := by
    have hnear : ∀ᶠ x : ℝ in nhds L, x < C :=
      eventually_lt_nhds (by
      dsimp only [C]
      exact lt_add_one L)
    exact hratio' hnear
  filter_upwards
      [hratio_lt, Filter.eventually_ge_atTop (2 : ℕ)] with
      N hratioN hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos hNreal
  exact ((div_lt_iff₀ hlogN).1 hratioN).le

/-- The paper's cutoff time and terminal-block choices satisfy the linear
horizon and block-containment hypotheses of the terminal coupling theorem. -/
lemma exists_eventually_supercriticalCutoff_block_horizon
    {A qStar q₀ b : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hb : 0 < b)
    (c : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) ≤
          C * (N : ℝ)) ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalBlockStart A qStar q₀ c b N +
            supercriticalTerminalBlockLength b N ≤
          supercriticalIntegerCutoffTime A qStar q₀ N c) := by
  obtain ⟨C, hC, hcutoff⟩ :=
    exists_eventually_supercriticalIntegerCutoffTime_le_mul_log_nat
      (q₀ := q₀) hA hqStar hfix c
  refine ⟨C, hC, ?_, ?_⟩
  · filter_upwards [hcutoff] with N hcutoffN
    calc
      (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) ≤
          C * Real.log (N : ℝ) := hcutoffN
      _ ≤ C * (N : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_self (Nat.cast_nonneg N)) hC.le
  · filter_upwards
        [eventually_supercriticalTerminalBlockStart_add_length_eq_integerCutoffTime_sub_one
          (q₀ := q₀) hA hqStar hfix hb c] with N hN
    omega

/-- One stationary family can be selected once and for all so that the
terminal synchronous-distance estimate only retains the evolving orbit and
block hypotheses. -/
theorem
    exists_stationary_family_eventually_terminal_distance_le_pow_mul_inv_sqrt_add_inv_nat
    {A qStar : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ R η C₂ : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C₂ ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ)) ∧
      ∀ {δ C C₀ : ℝ},
        0 < δ →
        0 ≤ C →
        δ + κ * η ≤ η →
        ∀ (q : ℕ → ℝ) (T s ℓ : ℕ → ℕ),
          (∀ᶠ N : ℕ in Filter.atTop,
            q N ∈ Set.Icc (0 : ℝ) 1) →
          (∀ᶠ N : ℕ in Filter.atTop,
            (T N : ℝ) ≤ C * (N : ℝ)) →
          (∀ᶠ N : ℕ in Filter.atTop,
            ∀ u ≤ T N,
              |(V A)^[u] (q N) - qStar| ≤ R - η) →
          (∀ᶠ N : ℕ in Filter.atTop,
            s N + ℓ N ≤ T N) →
          (∀ᶠ N : ℕ in Filter.atTop,
            |(V A)^[s N] (q N) - qStar| ≤
              C₀ / Real.sqrt (N : ℝ)) →
          ∀ᶠ N : ℕ in Filter.atTop,
            ∫ ω, |(ω (ℓ N)).1 - (ω (ℓ N)).2|
                ∂(markovPathMeasure
                  (((markovPathMeasure
                      (Measure.dirac (q N)) (Kchain A N)).map
                        (fun ω => ω (s N))).prod (ν N : Measure ℝ))
                  (synchronousKchain A N)) ≤
              κ ^ ℓ N *
                  ((Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
                      C₀ + Real.sqrt C₂) /
                    Real.sqrt (N : ℝ)) +
                ((2 * C + C₂ / R ^ 2) / (N : ℝ)) / (1 - κ) := by
  obtain ⟨κ, R, η, C₂, ν, hκ0, hκ1, hη0, hηR,
      hRinterior, hC₂, hderiv, hν⟩ :=
    exists_eventually_invariant_Kchain_family_integral_sq_sub_fixed_le_inv_nat
      hA hqStar hfix
  refine ⟨κ, R, η, C₂, ν, hκ0, hκ1, hη0, hηR,
    hRinterior, hC₂, hderiv, hν, ?_⟩
  intro δ C C₀ hδ hC hbuffer q T s ℓ hq hT horbit hblock hcenters
  have hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) := by
    filter_upwards [hν] with N hνN
    exact hνN.1
  have hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    filter_upwards [hν] with N hνN
    exact hνN.2.1
  have hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) := by
    filter_upwards [hν] with N hνN
    exact hνN.2.2.2.1
  have hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ) := by
    filter_upwards [hν] with N hνN
    exact hνN.2.2.2.2
  exact
    eventually_integral_abs_fst_sub_snd_eval_blockStart_prod_le_pow_mul_inv_sqrt_add_inv_nat
      (ne_of_gt (zero_lt_one.trans hA)) hκ0 hκ1 hη0.le hδ hC hC₂.le
      (hη0.trans hηR) hRinterior hderiv hbuffer
      q T s ℓ hq hT horbit hblock ν hνinv hνsupport hνsq hνbound hcenters

end AbsorptionCutoff
