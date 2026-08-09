/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.ScalarCutoffAssembly

/-!
# Cutoff profile assembly for the supercritical chain

This module continues the supercritical cutoff proof after the scalar and
vector fixed-shift profiles established in `ScalarCutoffAssembly.lean`. The
remaining paper-facing iterated-limit cutoff assembly belongs here.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The logarithmic cutoff-horizon constant can be selected independently of
the fixed real shift; only the eventual dimension threshold depends on the
shift. -/
lemma exists_forall_eventually_supercriticalIntegerCutoffTime_le_mul_log_nat
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ,
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
  intro c
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

/-- Every fixed-shift integer cutoff time is eventually bounded by the
dimension itself, with the bound stated uniformly over the real shift. -/
lemma forall_eventually_supercriticalIntegerCutoffTime_le_nat
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∀ c : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
      (supercriticalIntegerCutoffTime A qStar q₀ N c : ℝ) ≤
        (N : ℝ) := by
  obtain ⟨C, _hC, hcutoff⟩ :=
    exists_forall_eventually_supercriticalIntegerCutoffTime_le_mul_log_nat
      (q₀ := q₀) hA hqStar hfix
  have hlittle :
      (fun N : ℕ => C * Real.log (N : ℝ)) =o[Filter.atTop]
        (fun N : ℕ => (N : ℝ)) :=
    (Real.isLittleO_log_id_atTop.const_mul_left C).natCast_atTop
  have hlog :
      ∀ᶠ N : ℕ in Filter.atTop,
        C * Real.log (N : ℝ) ≤ (N : ℝ) := by
    have hnorm := Asymptotics.isLittleO_iff.mp hlittle zero_lt_one
    filter_upwards [hnorm] with N hnormN
    calc
      C * Real.log (N : ℝ) ≤
          ‖C * Real.log (N : ℝ)‖ :=
        by rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ 1 * ‖(N : ℝ)‖ :=
        hnormN
      _ = (N : ℝ) := by simp
  intro c
  filter_upwards [hcutoff c, hlog] with N hcutoffN hlogN
  exact hcutoffN.trans hlogN

/-- One post-entrance dynamic moment envelope controls every fixed-shift
cutoff horizon; the constants are selected before the real shift. -/
theorem
    exists_forall_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_cutoff
    {A qStar q₀ : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop, ∀ t : ℕ,
        m ≤ t →
        t ≤ supercriticalIntegerCutoffTime A qStar q₀ N c →
        ∫ ω, (ω t - (V A)^[t] (q N)) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)) ≤
          C / (N : ℝ) := by
  have hlinear :
      ∀ᶠ N : ℕ in Filter.atTop,
        (N : ℝ) ≤ (1 : ℝ) * (N : ℝ) :=
    Filter.Eventually.of_forall fun N => by simp
  obtain ⟨m, C, hC, hmoment⟩ :=
    exists_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_of_tendsto
      q (fun N : ℕ => N) hA hqStar hfix hq₀ hq hqmem
      zero_le_one hlinear
  refine ⟨m, C, hC, ?_⟩
  intro c
  have hcutoff :=
    forall_eventually_supercriticalIntegerCutoffTime_le_nat
      (q₀ := q₀) hA hqStar hfix c
  filter_upwards [hmoment, hcutoff] with N hmomentN hcutoffN
  intro t hmt ht
  have hcutoffNat :
      supercriticalIntegerCutoffTime A qStar q₀ N c ≤ N := by
    exact_mod_cast hcutoffN
  exact hmomentN t hmt (ht.trans hcutoffNat)

/-- The deterministic cutoff-scale separation uses one positive constant for
every fixed real shift; only the eventual dimension threshold depends on the
shift. -/
theorem
    exists_forall_eventually_rpow_le_sqrt_nat_mul_abs_V_iterate_integerCutoffTime_sub_fixed
    {A qStar q₀ : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ d : ℝ, 0 < d ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        d * deriv (V A) qStar ^ c ≤
          Real.sqrt (N : ℝ) *
            |(V A)^[
                supercriticalIntegerCutoffTime A qStar q₀ N c] (q N) -
              qStar| := by
  let μ := deriv (V A) qStar
  let C := koenigsCoefficient A qStar q₀
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hCne : C ≠ 0 := by
    exact koenigsCoefficient_ne_zero hA hqStar hfix hq₀ hq₀ne
  have hCpos : 0 < |C| :=
    abs_pos.mpr hCne
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro c
  let T : ℕ → ℕ :=
    fun N => supercriticalIntegerCutoffTime A qStar q₀ N c
  have hT :
      Filter.Tendsto T Filter.atTop Filter.atTop := by
    exact
      tendsto_supercriticalIntegerCutoffTime_atTop
        (q₀ := q₀) hA hqStar hfix c
  have hnormalized :=
    tendsto_normalized_V_orbit_sub_fixed_of_tendsto
      q T hA hqStar hfix hq₀ hq₀ne hq hqmem hT
  have hnormalizedLower :
      ∀ᶠ N : ℕ in Filter.atTop,
        |C| / 2 ≤
          |((V A)^[T N] (q N) - qStar) * μ⁻¹ ^ T N| := by
    have habs :
        Filter.Tendsto
          (fun N : ℕ =>
            |((V A)^[T N] (q N) - qStar) * μ⁻¹ ^ T N|)
          Filter.atTop
          (nhds |C|) := by
      simpa only [μ, C] using hnormalized.abs
    have hlower :=
      habs (eventually_gt_nhds (by linarith : |C| / 2 < |C|))
    filter_upwards [hlower] with N hN
    exact hN.le
  have hshiftAtTop :
      Filter.Tendsto
        (fun N : ℕ =>
          supercriticalCutoffTime A qStar q₀ N + c)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c
      (tendsto_supercriticalCutoffTime_atTop
        (q₀ := q₀) hA hqStar hfix)
  have hnonneg :
      ∀ᶠ N : ℕ in Filter.atTop,
        0 ≤ supercriticalCutoffTime A qStar q₀ N + c :=
    hshiftAtTop.eventually (Filter.eventually_ge_atTop 0)
  filter_upwards
      [hnormalizedLower, hnonneg,
       Filter.eventually_ge_atTop (1 : ℕ)] with
      N hnormalizedN hnonnegN hN
  let t := supercriticalCutoffTime A qStar q₀ N
  let n := T N
  let x := (V A)^[n] (q N) - qStar
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 hNreal
  have hfloor :
      (n : ℝ) ≤ t + c := by
    dsimp only [n, T, t]
    exact Nat.floor_le hnonnegN
  have hpowLower :
      μ ^ (t + c) ≤ μ ^ n := by
    rw [← Real.rpow_natCast]
    exact
      Real.rpow_le_rpow_of_exponent_ge hμ.1 hμ.2.le hfloor
  have hxLower :
      |C| / 2 * μ ^ n ≤ |x| := by
    change |C| / 2 ≤ |x * μ⁻¹ ^ n| at hnormalizedN
    have hμpowpos : 0 < μ ^ n :=
      pow_pos hμ.1 n
    calc
      |C| / 2 * μ ^ n ≤
          |x * μ⁻¹ ^ n| * μ ^ n :=
        mul_le_mul_of_nonneg_right hnormalizedN hμpowpos.le
      _ = |x| := by
        rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hμ.1),
          mul_assoc, ← mul_pow, inv_mul_cancel₀ hμ.1.ne',
          one_pow, mul_one]
  have hnormalize :
      μ ^ t =
        1 / (Real.sqrt (N : ℝ) * |C|) := by
    simpa only [μ, C, t] using
      rpow_supercriticalCutoffTime_eq_inv_sqrt_mul_abs_koenigsCoefficient
        hA hqStar hfix hq₀ hq₀ne hNpos
  have hscale :
      Real.sqrt (N : ℝ) *
          (|C| / 2 * μ ^ (t + c)) =
        1 / 2 * μ ^ c := by
    rw [Real.rpow_add hμ.1, hnormalize]
    field_simp [hsqrtpos.ne', hCne]
    ring
  change
    1 / 2 * μ ^ c ≤ Real.sqrt (N : ℝ) * |x|
  calc
    1 / 2 * μ ^ c =
        Real.sqrt (N : ℝ) *
          (|C| / 2 * μ ^ (t + c)) := hscale.symm
    _ ≤
        Real.sqrt (N : ℝ) *
          (|C| / 2 * μ ^ n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpowLower
          (div_nonneg (abs_nonneg C) (by norm_num)))
        hsqrtpos.le
    _ ≤ Real.sqrt (N : ℝ) * |x| :=
      mul_le_mul_of_nonneg_left hxLower hsqrtpos.le

/-- One centered second-moment envelope controls the evolving scalar path at
every fixed-shift cutoff time, including the integrability needed to pass to
the cutoff marginal. -/
theorem
    exists_forall_eventually_integrable_integral_sq_cutoffTime_sub_V_iterate_le_inv_nat
    {A qStar q₀ : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable
            (fun ω : ℕ → ℝ =>
              (ω (supercriticalIntegerCutoffTime
                    A qStar q₀ N c) -
                  (V A)^[
                    supercriticalIntegerCutoffTime
                      A qStar q₀ N c] (q N)) ^ 2)
            (markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)) ∧
          (∫ ω,
              (ω (supercriticalIntegerCutoffTime
                    A qStar q₀ N c) -
                  (V A)^[
                    supercriticalIntegerCutoffTime
                      A qStar q₀ N c] (q N)) ^ 2
              ∂(markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N))) ≤
            C / (N : ℝ) := by
  obtain ⟨m, C, hC, hmoment⟩ :=
    exists_forall_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_cutoff
      q hA hqStar hfix hq₀ hq hqmem
  refine ⟨C, hC, ?_⟩
  intro c
  have hmCutoff :
      ∀ᶠ N : ℕ in Filter.atTop,
        m ≤ supercriticalIntegerCutoffTime A qStar q₀ N c :=
    (tendsto_supercriticalIntegerCutoffTime_atTop
      (q₀ := q₀) hA hqStar hfix c).eventually
        (Filter.eventually_ge_atTop m)
  filter_upwards
      [hmoment c, hmCutoff, hqmem,
       Filter.eventually_ge_atTop (1 : ℕ)] with
      N hmomentN hmCutoffN hqN hN
  let T := supercriticalIntegerCutoffTime A qStar q₀ N c
  have hqIcc : q N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hqN.1.le, hqN.2⟩
  have hNpos : 0 < N :=
    Nat.zero_lt_of_lt hN
  constructor
  · apply integrable_sq_sub_of_ae_mem_Icc
      (markovPathMeasure
        (Measure.dirac (q N)) (Kchain A N))
      (fun ω : ℕ → ℝ => ω T)
      ((V A)^[T] (q N))
    · exact
        (((measurable_pi_apply T).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact
        markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
          hqIcc hNpos T
  · exact hmomentN T hmCutoffN le_rfl

/-- One selected origin-free stationary scalar family satisfies the lower
cutoff profile for every fixed real shift, with all profile constants chosen
before the shift. -/
theorem
    exists_stationary_family_forall_eventually_one_sub_mul_rpow_le_tvDist_cutoff_marginal
    {A qStar q₀ : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C D : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < D ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      ∀ c : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
        1 - D * deriv (V A) qStar ^ (-(2 * c)) ≤
          tvDist
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalIntegerCutoffTime
                    A qStar q₀ N c)))
            (ν N : Measure ℝ) := by
  let μ := deriv (V A) qStar
  obtain ⟨κ, R, η, Cν, ν, hκ0, hκ1, hη0, hηR,
      hRinterior, hCν, hderiv, hν⟩ :=
    exists_eventually_invariant_Kchain_family_integral_sq_sub_fixed_le_inv_nat
      hA hqStar hfix
  obtain ⟨Cρ, hCρ, hdynamic⟩ :=
    exists_forall_eventually_integrable_integral_sq_cutoffTime_sub_V_iterate_le_inv_nat
      q hA hqStar hfix hq₀ hq hqmem
  obtain ⟨d, hd, hseparation⟩ :=
    exists_forall_eventually_rpow_le_sqrt_nat_mul_abs_V_iterate_integerCutoffTime_sub_fixed
      q hA hqStar hfix hq₀ hq₀ne hq hqmem
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hνInt :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x : ℝ => (x - qStar) ^ 2)
          (ν N : Measure ℝ) :=
    hν.mono fun _ hνN => hνN.2.2.2.1
  have hνBound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x : ℝ, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          Cν / (N : ℝ) :=
    hν.mono fun _ hνN => hνN.2.2.2.2
  let D : ℝ := 4 * (Cρ + Cν) / d ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  refine ⟨Cν, D, ν, hCν, hD, hν, ?_⟩
  intro c
  let T : ℕ → ℕ :=
    fun N => supercriticalIntegerCutoffTime A qStar q₀ N c
  let a : ℕ → ℝ :=
    fun N => (V A)^[T N] (q N)
  let ρ : ℕ → ProbabilityMeasure ℝ :=
    fun N =>
      ⟨(markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω => ω (T N)),
        Measure.isProbabilityMeasure_map
          (measurable_pi_apply (T N)).aemeasurable⟩
  have hρInt :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x : ℝ => (x - a N) ^ 2)
          (ρ N : Measure ℝ) := by
    filter_upwards [hdynamic c] with N hdynamicN
    let f : ℝ → ℝ := fun x => (x - a N) ^ 2
    have hf :
        AEStronglyMeasurable f (ρ N : Measure ℝ) := by
      dsimp only [f]
      exact
        ((measurable_id.sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    apply
      (integrable_map_measure hf
        (measurable_pi_apply (T N)).aemeasurable).2
    change
      Integrable
        (fun ω : ℕ → ℝ => (ω (T N) - a N) ^ 2)
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N))
    simpa only [T, a] using hdynamicN.1
  have hρBound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x : ℝ, (x - a N) ^ 2 ∂(ρ N : Measure ℝ)) ≤
          Cρ / (N : ℝ) := by
    filter_upwards [hdynamic c] with N hdynamicN
    have hf :
        AEStronglyMeasurable
          (fun x : ℝ => (x - a N) ^ 2)
          (ρ N : Measure ℝ) :=
      ((measurable_id.sub measurable_const).pow_const 2)
        |>.aestronglyMeasurable
    rw [show
      (∫ x : ℝ, (x - a N) ^ 2 ∂(ρ N : Measure ℝ)) =
          ∫ ω, (ω (T N) - a N) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)) by
        dsimp only [ρ]
        exact
          integral_map
            (measurable_pi_apply (T N)).aemeasurable hf]
    simpa only [T, a] using hdynamicN.2
  have hlower :=
    eventually_one_sub_four_mul_add_div_sq_rpow_le_tvDist_of_inv_nat_moments
      ρ ν a qStar Cρ Cν d μ c hCρ hCν.le hd hμ.1
      hρInt hνInt hρBound hνBound (hseparation c)
  have hprofile :
      D * μ ^ (-(2 * c)) =
        4 * (Cρ + Cν) / (d ^ 2 * μ ^ (2 * c)) := by
    dsimp only [D, μ]
    rw [Real.rpow_neg hμ.1.le]
    field_simp [hd.ne']
  filter_upwards [hlower] with N hlowerN
  change
    1 - D * μ ^ (-(2 * c)) ≤
      tvDist (ρ N : Measure ℝ) (ν N : Measure ℝ)
  rw [hprofile]
  exact hlowerN

/-- One reconstructed origin-free invariant vector family satisfies the lower
cutoff profile for every fixed real shift, with all constants chosen before
the shift. -/
theorem
    exists_reconstructed_invariant_vector_family_forall_eventually_one_sub_mul_rpow_le_tvDist_cutoff
    {A qStar q₀ : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀))
    (hradiusMem :
      ∀ᶠ N : ℕ in Filter.atTop,
        radiusSq N (x N) ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C D : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < D ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N)
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ∧
          ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
              ({0} : Set (Fin N → ℝ)) = 0) ∧
      ∀ c : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
        1 - D * deriv (V A) qStar ^ (-(2 * c)) ≤
          tvDist
            (((Pkernel A N) ^
              supercriticalIntegerCutoffTime A qStar q₀ N c)
                (x N))
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) := by
  obtain ⟨C, D, ν, hC, hD, hν, hlower⟩ :=
    exists_stationary_family_forall_eventually_one_sub_mul_rpow_le_tvDist_cutoff_marginal
      (fun N : ℕ => radiusSq N (x N))
      hA hqStar hfix hq₀ hq₀ne hradius hradiusMem
  have hvector :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N)
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ∧
          ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
              ({0} : Set (Fin N → ℝ)) = 0 := by
    filter_upwards
        [hν, Filter.eventually_ge_atTop (1 : ℕ)] with
        N hνN hN
    refine ⟨invariant_Pkernel_of_invariant_Kchain
      A N (ν N : Measure ℝ) hνN.1, ?_⟩
    rw [← map_radiusSq_apply_singleton_zero
      (show 0 < N by omega)
      ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))]
    rw [radiusSq_map_Jkernel_comp, hνN.1.def, hνN.2.2.1]
  refine ⟨C, D, ν, hC, hD, hν, hvector, ?_⟩
  intro c
  filter_upwards [hlower c, hν] with N hlowerN hνN
  rw [markovPathMeasure_dirac_map_eval] at hlowerN
  exact hlowerN.trans
    (tvDist_Kchain_pow_le_Pkernel_pow
      A N (ν N : Measure ℝ) hνN.1 (x N)
        (supercriticalIntegerCutoffTime A qStar q₀ N c))

/-- One deterministic multiplier-envelope constant controls the convergent
initial sequence along every varying time sequence tending to infinity. -/
theorem
    exists_forall_eventually_abs_V_iterate_sub_fixed_le_mul_pow_of_tendsto
    {A qStar q₀ : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ → ℕ,
      Filter.Tendsto T Filter.atTop Filter.atTop →
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[T N] (q N) - qStar| ≤
          C * deriv (V A) qStar ^ T N := by
  let μ := deriv (V A) qStar
  let Kcoeff := koenigsCoefficient A qStar q₀
  let C : ℝ := |Kcoeff| + 1
  have hC : 0 < C := by
    dsimp only [C]
    linarith [abs_nonneg Kcoeff]
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hnormalized :=
    tendsto_normalized_V_orbit_sub_fixed_of_tendsto
      q T hA hqStar hfix hq₀ hq₀ne hq hqmem hT
  have habs :
      Filter.Tendsto
        (fun N : ℕ =>
          |((V A)^[T N] (q N) - qStar) * μ⁻¹ ^ T N|)
        Filter.atTop (nhds |Kcoeff|) := by
    simpa only [μ, Kcoeff] using hnormalized.abs
  have hbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        |((V A)^[T N] (q N) - qStar) * μ⁻¹ ^ T N| < C :=
    habs (eventually_lt_nhds (by
      dsimp only [C]
      exact lt_add_one |Kcoeff|))
  filter_upwards [hbound] with N hboundN
  let n := T N
  let x := (V A)^[n] (q N) - qStar
  have hμpow : 0 < μ ^ n :=
    pow_pos hμ.1 n
  have hid :
      |x * μ⁻¹ ^ n| * μ ^ n = |x| := by
    rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hμ.1),
      mul_assoc, ← mul_pow, inv_mul_cancel₀ hμ.1.ne',
      one_pow, mul_one]
  change |x| ≤ C * μ ^ n
  calc
    |x| = |x * μ⁻¹ ^ n| * μ ^ n := hid.symm
    _ ≤ C * μ ^ n :=
      mul_le_mul_of_nonneg_right hboundN.le hμpow.le

/-- The deterministic terminal-block center uses one cutoff-scale constant
for every fixed real shift. -/
theorem
    exists_forall_eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_mul_rpow_div_sqrt
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
    (hb : 0 < b) :
    ∃ D : ℝ, 0 < D ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[
            supercriticalTerminalBlockStart A qStar q₀ c b N] (q N) -
            qStar| ≤
          D *
              deriv (V A) qStar ^
                (c - (supercriticalTerminalBlockLength b N : ℝ)) /
            Real.sqrt (N : ℝ) := by
  obtain ⟨C, hC, hcenterAll⟩ :=
    exists_forall_eventually_abs_V_iterate_sub_fixed_le_mul_pow_of_tendsto
      q hA hqStar hfix hq₀ hq₀ne hq hqmem
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
  intro c
  have hcenter :=
    hcenterAll
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      (tendsto_supercriticalTerminalBlockStart_atTop
        (q₀ := q₀) hA hqStar hfix hb c)
  have hmultiplier :=
    eventually_pow_terminalBlockStart_le_cutoff_rpow
      hA hqStar hfix hq₀ hq₀ne hb c
  filter_upwards
      [hcenter, hmultiplier,
       Filter.eventually_ge_atTop (1 : ℕ)] with
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

/-- One centered second-moment envelope controls the evolving scalar path at
every fixed-shift terminal-block start. -/
theorem
    exists_forall_eventually_integrable_integral_sq_terminalBlockStart_sub_V_iterate_le_inv_nat
    {A qStar q₀ b : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable
            (fun ω : ℕ → ℝ =>
              (ω (supercriticalTerminalBlockStart
                    A qStar q₀ c b N) -
                  (V A)^[
                    supercriticalTerminalBlockStart
                      A qStar q₀ c b N] (q N)) ^ 2)
            (markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)) ∧
          (∫ ω,
              (ω (supercriticalTerminalBlockStart
                    A qStar q₀ c b N) -
                  (V A)^[
                    supercriticalTerminalBlockStart
                      A qStar q₀ c b N] (q N)) ^ 2
              ∂(markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N))) ≤
            C / (N : ℝ) := by
  obtain ⟨m, C, hC, hmoment⟩ :=
    exists_forall_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_cutoff
      q hA hqStar hfix hq₀ hq hqmem
  refine ⟨C, hC, ?_⟩
  intro c
  have hmStart :
      ∀ᶠ N : ℕ in Filter.atTop,
        m ≤ supercriticalTerminalBlockStart A qStar q₀ c b N :=
    (tendsto_supercriticalTerminalBlockStart_atTop
      (q₀ := q₀) hA hqStar hfix hb c).eventually
        (Filter.eventually_ge_atTop m)
  have hstartLe :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalBlockStart A qStar q₀ c b N ≤
          supercriticalIntegerCutoffTime A qStar q₀ N c := by
    filter_upwards
        [eventually_supercriticalTerminalBlockStart_add_length_eq_integerCutoffTime_sub_one
          (q₀ := q₀) hA hqStar hfix hb c] with N hN
    omega
  filter_upwards
      [hmoment c, hmStart, hstartLe, hqmem,
       Filter.eventually_ge_atTop (1 : ℕ)] with
      N hmomentN hmStartN hstartLeN hqN hN
  let T := supercriticalTerminalBlockStart A qStar q₀ c b N
  have hqIcc : q N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hqN.1.le, hqN.2⟩
  have hNpos : 0 < N :=
    Nat.zero_lt_of_lt hN
  constructor
  · apply integrable_sq_sub_of_ae_mem_Icc
      (markovPathMeasure
        (Measure.dirac (q N)) (Kchain A N))
      (fun ω : ℕ → ℝ => ω T)
      ((V A)^[T] (q N))
    · exact
        (((measurable_pi_apply T).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact
        markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
          hqIcc hNpos T
  · exact hmomentN T hmStartN hstartLeN

/-- The independent evolving/stationary product at the terminal-block start
has one inverse-square-root fluctuation envelope for every fixed shift. -/
theorem
    exists_forall_eventually_integral_abs_fst_sub_snd_terminalBlockStart_prod_le_rpow_div_sqrt
    {A qStar q₀ b C₂ : ℝ} (q : ℕ → ℝ)
    (ν : ℕ → ProbabilityMeasure ℝ)
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
    (hC₂ : 0 ≤ C₂)
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ)) :
    ∃ C₁ D : ℝ, 0 ≤ C₁ ∧ 0 < D ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        ∫ p, |p.1 - p.2|
            ∂((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockStart
                    A qStar q₀ c b N))).prod (ν N : Measure ℝ) ≤
          (Real.sqrt C₁ +
              D * deriv (V A) qStar ^
                (c - (supercriticalTerminalBlockLength b N : ℝ)) +
              Real.sqrt C₂) /
            Real.sqrt (N : ℝ) := by
  obtain ⟨C₁, hC₁, hmoment⟩ :=
    exists_forall_eventually_integrable_integral_sq_terminalBlockStart_sub_V_iterate_le_inv_nat
      q hA hqStar hfix hq₀ hq hqmem hb
  obtain ⟨D, hD, hcenter⟩ :=
    exists_forall_eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_mul_rpow_div_sqrt
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb
  refine ⟨C₁, D, hC₁, hD, ?_⟩
  intro c
  filter_upwards
      [hmoment c, hνsq, hνbound, hcenter c] with
      N hmomentN hνsqN hνboundN hcenterN
  let ρ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac (q N)) (Kchain A N)
  haveI : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    infer_instance
  simpa only [ρ] using
    integral_abs_fst_sub_snd_map_eval_prod_le_sqrt_add_const_add_sqrt_div_sqrt_nat
      ρ (ν N : Measure ℝ)
      (supercriticalTerminalBlockStart A qStar q₀ c b N)
      ((V A)^[
        supercriticalTerminalBlockStart A qStar q₀ c b N] (q N))
      qStar hC₁ hC₂ hmomentN.1 hνsqN hmomentN.2 hνboundN
      hcenterN

/-- One localization constant controls the evolving coordinate throughout
every fixed-shift restarted terminal block. -/
theorem
    exists_forall_eventually_shifted_eval_not_mem_terminalInterval_le
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
    (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u < supercriticalTerminalBlockLength b N,
          (markovPathMeasure
              ((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockStart
                    A qStar q₀ c b N)))
              (Kchain A N)).real
              {ω : ℕ → ℝ |
                ω u ∉ Set.Icc
                  (qStar - supercriticalTerminalRadius N)
                  (qStar + supercriticalTerminalRadius N)} ≤
            (4 * C / supercriticalTerminalRadius N ^ 2) /
              (N : ℝ) := by
  obtain ⟨m, C, hC, hmoment⟩ :=
    exists_forall_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_cutoff
      q hA hqStar hfix hq₀ hq hqmem
  refine ⟨C, hC, ?_⟩
  intro c
  have hblock :=
    eventually_supercriticalTerminalBlockStart_add_length_eq_integerCutoffTime_sub_one
      (q₀ := q₀) hA hqStar hfix hb c
  have hentranceBefore :
      ∀ᶠ N : ℕ in Filter.atTop,
        m ≤ supercriticalTerminalBlockStart A qStar q₀ c b N :=
    (tendsto_supercriticalTerminalBlockStart_atTop
      (q₀ := q₀) hA hqStar hfix hb c).eventually
        (Filter.eventually_ge_atTop m)
  have hmomentBlock :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u < supercriticalTerminalBlockLength b N,
          (∫ ω,
            (ω (supercriticalTerminalBlockStart
                  A qStar q₀ c b N + u) -
                (V A)^[
                  supercriticalTerminalBlockStart
                    A qStar q₀ c b N + u] (q N)) ^ 2
              ∂(markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N))) ≤
            C / (N : ℝ) := by
    filter_upwards
        [hmoment c, hentranceBefore, hblock] with
        N hmomentN hentranceBeforeN hblockN
    intro u hu
    exact
      hmomentN
        (supercriticalTerminalBlockStart A qStar q₀ c b N + u)
        (by omega) (by omega)
  have hcenter :=
    eventually_forall_abs_V_iterate_terminalBlockStart_add_sub_fixed_le_half_terminalRadius
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  have hcenterBlock :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u < supercriticalTerminalBlockLength b N,
          |(V A)^[
              supercriticalTerminalBlockStart A qStar q₀ c b N + u] (q N) -
              qStar| ≤
            supercriticalTerminalRadius N / 2 :=
    hcenter.mono fun _ hcenterN u _hu => hcenterN u
  have hqIcc :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1 :=
    hqmem.mono fun _ hqN => ⟨hqN.1.le, hqN.2⟩
  exact
    eventually_forall_shifted_eval_not_mem_terminalInterval_le_of_center
      q
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      (supercriticalTerminalBlockLength b)
      hqIcc hcenterBlock hmomentBlock

/-- The shrinking terminal recursion uses one collection of contraction,
localization, fluctuation, and center constants for every fixed shift. -/
theorem
    exists_forall_eventually_terminalBlock_distance_le_contraction_pow_mul_rpow_add
    {A qStar q₀ b C₂ : ℝ} (q : ℕ → ℝ)
    (ν : ℕ → ProbabilityMeasure ℝ)
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
    (hC₂ : 0 ≤ C₂)
    (hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ))
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ)) :
    ∃ L C₁ C₀ D : ℝ,
      0 ≤ L ∧ 0 ≤ C₁ ∧ 0 ≤ C₀ ∧ 0 < D ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        ∫ ω,
            |(ω (supercriticalTerminalBlockLength b N)).1 -
              (ω (supercriticalTerminalBlockLength b N)).2|
            ∂(markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)) ≤
          supercriticalTerminalContraction A qStar L N ^
                supercriticalTerminalBlockLength b N *
              ((Real.sqrt C₀ +
                  D * deriv (V A) qStar ^
                    (c -
                      (supercriticalTerminalBlockLength b N : ℝ)) +
                  Real.sqrt C₂) /
                Real.sqrt (N : ℝ)) +
            ((((4 * C₁ + C₂) /
                supercriticalTerminalRadius N ^ 2) /
              (N : ℝ)) /
              (1 -
                supercriticalTerminalContraction A qStar L N)) := by
  obtain ⟨L, hL, hcontractionData⟩ :=
    exists_eventually_supercriticalTerminal_contraction_data
      hA hqStar hfix
  have hcontraction :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalRadius N < qStar ∧
        0 ≤ supercriticalTerminalContraction A qStar L N ∧
        supercriticalTerminalContraction A qStar L N < 1 ∧
        ∀ z : ℝ,
          |z - qStar| ≤ supercriticalTerminalRadius N →
          |deriv (V A) z| ≤
            supercriticalTerminalContraction A qStar L N :=
    hcontractionData.mono fun N hN => by
      obtain ⟨_, hRbound, ha0, ha1, hderivN⟩ := hN
      have hRhalf :
          supercriticalTerminalRadius N ≤ qStar / 2 :=
        hRbound.trans (min_le_left _ _)
      exact ⟨by linarith [hqStar.1], ha0, ha1, hderivN⟩
  obtain ⟨C₁, hC₁, hbad₁⟩ :=
    exists_forall_eventually_shifted_eval_not_mem_terminalInterval_le
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb
  have hbad₂all :=
    eventually_forall_stationary_eval_not_mem_terminalInterval_le_inv_nat
      ν hνinv hνsq hνbound
  have hbad₂ :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u < supercriticalTerminalBlockLength b N,
          (markovPathMeasure (ν N : Measure ℝ) (Kchain A N)).real
              {ω : ℕ → ℝ |
                ω u ∉ Set.Icc
                  (qStar - supercriticalTerminalRadius N)
                  (qStar + supercriticalTerminalRadius N)} ≤
            (C₂ / supercriticalTerminalRadius N ^ 2) / (N : ℝ) :=
    hbad₂all.mono fun _ hN u _hu => hN u
  have hqIcc :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1 :=
    hqmem.mono fun _ hqN => ⟨hqN.1.le, hqN.2⟩
  obtain ⟨C₀, D, hC₀, hD, hproduct⟩ :=
    exists_forall_eventually_integral_abs_fst_sub_snd_terminalBlockStart_prod_le_rpow_div_sqrt
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb
      hC₂ hνsq hνbound
  refine ⟨L, C₁, C₀, D, hL, hC₁, hC₀, hD, ?_⟩
  intro c
  have hterminal :=
    eventually_integral_abs_fst_sub_snd_eval_blockStart_le_terminalContraction_pow_mul_add
      (ne_of_gt (zero_lt_one.trans hA))
      (mul_nonneg (by norm_num) hC₁) hC₂ q
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      (supercriticalTerminalBlockLength b) ν
      hcontraction hqIcc hνsupport (hbad₁ c) hbad₂
  filter_upwards [hterminal, hproduct c] with
      N hterminalN hproductN
  calc
    ∫ ω,
          |(ω (supercriticalTerminalBlockLength b N)).1 -
            (ω (supercriticalTerminalBlockLength b N)).2|
          ∂(markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)) ≤
        supercriticalTerminalContraction A qStar L N ^
              supercriticalTerminalBlockLength b N *
            (∫ p, |p.1 - p.2|
              ∂((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ)) +
          ((((4 * C₁ + C₂) /
              supercriticalTerminalRadius N ^ 2) /
            (N : ℝ)) /
            (1 -
              supercriticalTerminalContraction A qStar L N)) :=
      hterminalN
    _ ≤
        supercriticalTerminalContraction A qStar L N ^
              supercriticalTerminalBlockLength b N *
            ((Real.sqrt C₀ +
                D * deriv (V A) qStar ^
                  (c -
                    (supercriticalTerminalBlockLength b N : ℝ)) +
                Real.sqrt C₂) /
              Real.sqrt (N : ℝ)) +
          ((((4 * C₁ + C₂) /
              supercriticalTerminalRadius N ^ 2) /
            (N : ℝ)) /
            (1 -
              supercriticalTerminalContraction A qStar L N)) := by
      gcongr
      exact pow_nonneg
        (supercriticalTerminalContraction_nonneg
          hA hqStar hfix hL N) _

/-- Up to any fixed factor above one, the shift-uniform terminal recursion
uses the fixed-point multiplier power instead of the shrinking contraction
power. -/
theorem
    exists_forall_eventually_terminalBlock_distance_le_multiplier_pow_mul_rpow_add
    {A qStar q₀ b C₂ : ℝ} (q : ℕ → ℝ)
    (ν : ℕ → ProbabilityMeasure ℝ)
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
    (hC₂ : 0 ≤ C₂)
    (hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ))
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ)) :
    ∃ L C₁ C₀ D : ℝ,
      0 ≤ L ∧ 0 ≤ C₁ ∧ 0 ≤ C₀ ∧ 0 < D ∧
      ∀ ε : ℝ, 0 < ε → ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        ∫ ω,
            |(ω (supercriticalTerminalBlockLength b N)).1 -
              (ω (supercriticalTerminalBlockLength b N)).2|
            ∂(markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)) ≤
          (1 + ε) *
              deriv (V A) qStar ^
                supercriticalTerminalBlockLength b N *
              ((Real.sqrt C₀ +
                  D * deriv (V A) qStar ^
                    (c -
                      (supercriticalTerminalBlockLength b N : ℝ)) +
                  Real.sqrt C₂) /
                Real.sqrt (N : ℝ)) +
            ((((4 * C₁ + C₂) /
                supercriticalTerminalRadius N ^ 2) /
              (N : ℝ)) /
              (1 -
                supercriticalTerminalContraction A qStar L N)) := by
  obtain ⟨L, C₁, C₀, D, hL, hC₁, hC₀, hD, hterminal⟩ :=
    exists_forall_eventually_terminalBlock_distance_le_contraction_pow_mul_rpow_add
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb
      hC₂ hνsupport hνinv hνsq hνbound
  refine ⟨L, C₁, C₀, D, hL, hC₁, hC₀, hD, ?_⟩
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hratio :=
    tendsto_supercriticalTerminalContraction_div_multiplier_pow_blockLength_one
      hA hqStar hfix hL hb
  intro ε hε c
  have hratioUpper :
      ∀ᶠ N : ℕ in Filter.atTop,
        (supercriticalTerminalContraction A qStar L N /
            deriv (V A) qStar) ^
            supercriticalTerminalBlockLength b N <
          1 + ε :=
    hratio (eventually_lt_nhds (by linarith))
  filter_upwards [hterminal c, hratioUpper] with
      N hterminalN hratioN
  have hpow :
      supercriticalTerminalContraction A qStar L N ^
          supercriticalTerminalBlockLength b N =
        (supercriticalTerminalContraction A qStar L N /
            deriv (V A) qStar) ^
              supercriticalTerminalBlockLength b N *
          deriv (V A) qStar ^
            supercriticalTerminalBlockLength b N := by
    rw [div_pow]
    field_simp [hμ.1.ne']
  have hpowBound :
      supercriticalTerminalContraction A qStar L N ^
          supercriticalTerminalBlockLength b N ≤
        (1 + ε) *
          deriv (V A) qStar ^
            supercriticalTerminalBlockLength b N := by
    rw [hpow]
    exact mul_le_mul_of_nonneg_right hratioN.le
      (pow_nonneg hμ.1.le _)
  have hBnonneg :
      0 ≤
        (Real.sqrt C₀ +
            D * deriv (V A) qStar ^
              (c - (supercriticalTerminalBlockLength b N : ℝ)) +
            Real.sqrt C₂) /
          Real.sqrt (N : ℝ) := by
    exact div_nonneg
      (add_nonneg
        (add_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg hD.le (Real.rpow_nonneg hμ.1.le _)))
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hscaled :=
    mul_le_mul_of_nonneg_right hpowBound hBnonneg
  exact hterminalN.trans (add_le_add hscaled le_rfl)

end AbsorptionCutoff
