/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.CutoffAssembly

/-!
# Terminal contraction for the supercritical cutoff

This module continues the supercritical cutoff proof after the cutoff-time
and shrinking-interval data established in `CutoffAssembly.lean`. Keeping the
terminal contraction assembly here avoids re-elaborating the completed cutoff
parameter module for each small unit.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The arbitrary-law terminal contraction estimate specialized to the
shrinking radius and varying contraction factor at one dimension. -/
lemma
    integral_abs_fst_sub_snd_eval_blockStart_prod_le_terminalContraction_pow_mul_add_of_localization
    {A q qStar L B₁ B₂ : ℝ} {N s ℓ : ℕ}
    (hA : A ≠ 0)
    (hRq : supercriticalTerminalRadius N < qStar)
    (hκ0 : 0 ≤ supercriticalTerminalContraction A qStar L N)
    (hκ1 : supercriticalTerminalContraction A qStar L N < 1)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hderiv :
      ∀ z : ℝ,
        |z - qStar| ≤ supercriticalTerminalRadius N →
          |deriv (V A) z| ≤
            supercriticalTerminalContraction A qStar L N)
    (hN : 0 < N) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνsupport : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hbad₁ : ∀ u < ℓ,
      (markovPathMeasure
          ((markovPathMeasure
            (Measure.dirac q) (Kchain A N)).map (fun ω => ω s))
          (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc
              (qStar - supercriticalTerminalRadius N)
              (qStar + supercriticalTerminalRadius N)} ≤ B₁)
    (hbad₂ : ∀ u < ℓ,
      (markovPathMeasure ν (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc
              (qStar - supercriticalTerminalRadius N)
              (qStar + supercriticalTerminalRadius N)} ≤ B₂) :
    ∫ ω, |(ω ℓ).1 - (ω ℓ).2|
        ∂(markovPathMeasure
          (((markovPathMeasure
              (Measure.dirac q) (Kchain A N)).map (fun ω => ω s)).prod ν)
          (synchronousKchain A N)) ≤
      supercriticalTerminalContraction A qStar L N ^ ℓ *
          (∫ p, |p.1 - p.2|
            ∂((markovPathMeasure
              (Measure.dirac q) (Kchain A N)).map
                (fun ω => ω s)).prod ν) +
        (B₁ + B₂) /
          (1 - supercriticalTerminalContraction A qStar L N) := by
  exact
    integral_abs_fst_sub_snd_eval_blockStart_prod_le_pow_mul_add_of_localization
      hA hRq hκ0 hκ1 hB₁ hB₂ hderiv hN hq ν hνsupport hbad₁ hbad₂

/-- A second-moment bound around a nearby deterministic center controls
escape from the stable interval around the fixed point. -/
lemma
    measureReal_not_mem_stableInterval_le_four_mul_div_sq_div_nat_of_center
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m qStar : ℝ) {R C : ℝ} {N : ℕ}
    (hR : 0 < R)
    (hcenter : |m - qStar| ≤ R / 2)
    (hsq : Integrable (fun q => (q - m) ^ 2) μ)
    (hbound :
      (∫ q, (q - m) ^ 2 ∂μ) ≤ C / (N : ℝ)) :
    μ.real
        {q : ℝ |
          q ∉ Set.Icc (qStar - R) (qStar + R)} ≤
      (4 * C / R ^ 2) / (N : ℝ) := by
  have hcenter' :
      -(R / 2) ≤ m - qStar ∧ m - qStar ≤ R / 2 := by
    simpa only [abs_le] using hcenter
  have hsubset :
      {q : ℝ | q ∉ Set.Icc (qStar - R) (qStar + R)} ⊆
        {q : ℝ | R / 2 < |q - m|} := by
    intro q hq
    simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hq ⊢
    rw [lt_abs]
    rcases hq with hq | hq
    · right
      linarith [hcenter'.1]
    · left
      linarith [hcenter'.2]
  calc
    μ.real {q : ℝ | q ∉ Set.Icc (qStar - R) (qStar + R)} ≤
        μ.real {q : ℝ | R / 2 < |q - m|} :=
      measureReal_mono hsubset
    _ ≤ (C / (R / 2) ^ 2) / (N : ℝ) :=
      measureReal_abs_sub_gt_le_div_sq_div_nat
        μ m (by positivity) hsq hbound
    _ = (4 * C / R ^ 2) / (N : ℝ) := by ring

/-- A path-law second moment around a nearby deterministic center controls
fixed-time escape from the stable interval around the fixed point. -/
lemma
    markovPathMeasure_measureReal_eval_not_mem_stableInterval_le_four_mul_div_sq_div_nat_of_center
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (t : ℕ) (m qStar : ℝ) {R C : ℝ} {N : ℕ}
    (hR : 0 < R)
    (hcenter : |m - qStar| ≤ R / 2)
    (hsq :
      Integrable
        (fun ω : ℕ → ℝ => (ω t - m) ^ 2)
        (markovPathMeasure μ κ))
    (hbound :
      (∫ ω, (ω t - m) ^ 2 ∂(markovPathMeasure μ κ)) ≤
        C / (N : ℝ)) :
    (markovPathMeasure μ κ).real
        {ω : ℕ → ℝ |
          ω t ∉ Set.Icc (qStar - R) (qStar + R)} ≤
      (4 * C / R ^ 2) / (N : ℝ) := by
  let ν : Measure ℝ :=
    (markovPathMeasure μ κ).map (fun ω => ω t)
  have heval :
      AEMeasurable (fun ω : ℕ → ℝ => ω t)
        (markovPathMeasure μ κ) :=
    (measurable_pi_apply t).aemeasurable
  haveI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map heval
  have hνmeas :
      AEStronglyMeasurable (fun q : ℝ => (q - m) ^ 2) ν :=
    ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable
  have hνsq :
      Integrable (fun q : ℝ => (q - m) ^ 2) ν := by
    apply (integrable_map_measure hνmeas heval).2
    exact hsq
  have hνeq :
      (∫ q, (q - m) ^ 2 ∂ν) =
        ∫ ω, (ω t - m) ^ 2 ∂(markovPathMeasure μ κ) := by
    dsimp only [ν]
    exact integral_map heval hνmeas
  have hνbound :
      (∫ q, (q - m) ^ 2 ∂ν) ≤ C / (N : ℝ) := by
    rw [hνeq]
    exact hbound
  let S : Set ℝ :=
    (Set.Icc (qStar - R) (qStar + R))ᶜ
  have hS :
      S =
        {q : ℝ |
          q ∉ Set.Icc (qStar - R) (qStar + R)} := by
    ext q
    simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq]
  calc
    (markovPathMeasure μ κ).real
          {ω : ℕ → ℝ |
            ω t ∉ Set.Icc (qStar - R) (qStar + R)} =
        ν.real S := by
      change
        (markovPathMeasure μ κ).real
            ((fun ω : ℕ → ℝ => ω t) ⁻¹' S) =
          ν.real S
      exact
        (map_measureReal_apply
          (μ := markovPathMeasure μ κ)
          (measurable_pi_apply t) measurableSet_Icc.compl).symm
    _ ≤ (4 * C / R ^ 2) / (N : ℝ) := by
      rw [hS]
      exact
        measureReal_not_mem_stableInterval_le_four_mul_div_sq_div_nat_of_center
          ν m qStar hR hcenter hνsq hνbound

/-- Uniform displaced-center localization transfers to every time of a fresh
terminal-block path started from the original path's block-start marginal. -/
lemma
    eventually_forall_shifted_eval_not_mem_terminalInterval_le_of_center
    {A qStar C : ℝ}
    (q : ℕ → ℝ) (s ℓ : ℕ → ℕ)
    (hq :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1)
    (hcenter :
      ∀ᶠ N : ℕ in Filter.atTop, ∀ u < ℓ N,
        |(V A)^[s N + u] (q N) - qStar| ≤
          supercriticalTerminalRadius N / 2)
    (hmoment :
      ∀ᶠ N : ℕ in Filter.atTop, ∀ u < ℓ N,
        (∫ ω,
          (ω (s N + u) - (V A)^[s N + u] (q N)) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N))) ≤
          C / (N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ u < ℓ N,
      (markovPathMeasure
          ((markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω => ω (s N)))
          (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc
              (qStar - supercriticalTerminalRadius N)
              (qStar + supercriticalTerminalRadius N)} ≤
        (4 * C / supercriticalTerminalRadius N ^ 2) /
          (N : ℝ) := by
  filter_upwards
      [hq, hcenter, hmoment,
        Filter.eventually_ge_atTop (2 : ℕ)] with
      N hqN hcenterN hmomentN hN
  intro u hu
  have hNpos : 0 < N := by omega
  have hsq :
      Integrable
        (fun ω : ℕ → ℝ =>
          (ω (s N + u) - (V A)^[s N + u] (q N)) ^ 2)
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)) := by
    apply integrable_sq_sub_of_ae_mem_Icc
      (markovPathMeasure
        (Measure.dirac (q N)) (Kchain A N))
      (fun ω : ℕ → ℝ => ω (s N + u))
      ((V A)^[s N + u] (q N))
    · exact
        (((measurable_pi_apply (s N + u)).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact
        markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
          hqN hNpos (s N + u)
  have hlocal :=
    markovPathMeasure_measureReal_eval_not_mem_stableInterval_le_four_mul_div_sq_div_nat_of_center
      (Measure.dirac (q N)) (Kchain A N) (s N + u)
      ((V A)^[s N + u] (q N)) qStar
      (supercriticalTerminalRadius_pos (show 1 < N by omega))
      (hcenterN u hu) hsq (hmomentN u hu)
  let J : Set ℝ :=
    Set.Icc
      (qStar - supercriticalTerminalRadius N)
      (qStar + supercriticalTerminalRadius N)
  have hshift :=
    markovPathMeasure_measureReal_eval_mem_of_map_eval
      (Measure.dirac (q N)) (Kchain A N) (s N) u Jᶜ
      measurableSet_Icc.compl
  calc
    (markovPathMeasure
          ((markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω => ω (s N)))
          (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc
              (qStar - supercriticalTerminalRadius N)
              (qStar + supercriticalTerminalRadius N)} =
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω (s N + u) ∉ Set.Icc
              (qStar - supercriticalTerminalRadius N)
              (qStar + supercriticalTerminalRadius N)} := by
      simpa only [J, Set.mem_compl_iff] using hshift
    _ ≤ (4 * C / supercriticalTerminalRadius N ^ 2) /
        (N : ℝ) := hlocal

/-- The dynamic orbit moment bound is uniform over every time through a
linearly bounded varying horizon. -/
lemma eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat
    {A qStar R κ η δ C : ℝ}
    (hA : A ≠ 0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (q : ℕ → ℝ) (T : ℕ → ℕ)
    (hq :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ t ≤ T N,
          |(V A)^[t] (q N) - qStar| ≤ R - η) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ t ≤ T N,
      ∫ ω, (ω t - (V A)^[t] (q N)) ^ 2
          ∂(markovPathMeasure (Measure.dirac (q N)) (Kchain A N)) ≤
        ((1 / 4) / (1 - κ ^ 2) + 2 * C) / (N : ℝ) := by
  have hc : 0 < 2 * δ ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hδ)
  have hrem :=
    eventually_two_nat_horizon_mul_exp_neg_le_mul_inv_nat
      hC hc hT
  filter_upwards
      [hq, horbit, hrem,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hqN horbitN hremN hN
  intro t htT
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hNpos
  have hremN' :
      2 * (T N : ℝ) * Real.exp (-2 * N * δ ^ 2) ≤
        2 * C / (N : ℝ) := by
    rw [show -2 * (N : ℝ) * δ ^ 2 =
        -(2 * δ ^ 2) * (N : ℝ) by ring]
    exact hremN
  have hfull :=
    integral_sq_eval_sub_V_iterate_le_inv_add_exp
      hqN hA hNpos hκ0 hκ1 hη0 hδ hRinterior
      hderiv hbuffer horbitN htT
  calc
    ∫ ω, (ω t - (V A)^[t] (q N)) ^ 2
        ∂(markovPathMeasure (Measure.dirac (q N)) (Kchain A N)) ≤
        (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
          2 * (T N : ℝ) * Real.exp (-2 * N * δ ^ 2) :=
      hfull
    _ ≤ (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
        2 * C / (N : ℝ) :=
      add_le_add le_rfl hremN'
    _ = ((1 / 4) / (1 - κ ^ 2) + 2 * C) / (N : ℝ) := by
      have hκsq : κ ^ 2 < 1 := by
        simpa using (sq_lt_sq₀ hκ0 zero_le_one).2 hκ1
      field_simp [hNreal.ne', (sub_pos.mpr hκsq).ne']

/-- The uniform dynamic moment bound restricts to every time in a terminal
block contained in the varying horizon. -/
lemma eventually_forall_integral_sq_eval_blockStart_add_le_inv_nat
    {A qStar R κ η δ C : ℝ}
    (hA : A ≠ 0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (q : ℕ → ℝ) (T s ℓ : ℕ → ℕ)
    (hq :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ t ≤ T N,
          |(V A)^[t] (q N) - qStar| ≤ R - η)
    (hblock :
      ∀ᶠ N : ℕ in Filter.atTop,
        s N + ℓ N ≤ T N) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ u < ℓ N,
      ∫ ω,
          (ω (s N + u) - (V A)^[s N + u] (q N)) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)) ≤
        ((1 / 4) / (1 - κ ^ 2) + 2 * C) / (N : ℝ) := by
  have hdynamic :=
    eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat
      hA hκ0 hκ1 hη0 hδ hC hRinterior hderiv hbuffer
      q T hq hT horbit
  filter_upwards [hdynamic, hblock] with N hdynamicN hblockN
  intro u hu
  exact hdynamicN (s N + u) (by omega)

/-- The deterministic block-start scale is negligible compared with the
shrinking terminal radius. -/
lemma
    tendsto_mul_rpow_sub_terminalBlockLength_div_sqrt_div_terminalRadius_zero
    {μ b D c : ℝ}
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (hb : 0 < b) (hD : 0 ≤ D) :
    Filter.Tendsto
      (fun N : ℕ =>
        D *
              μ ^ (c -
                (supercriticalTerminalBlockLength b N : ℝ)) /
            Real.sqrt (N : ℝ) /
          supercriticalTerminalRadius N)
      Filter.atTop (nhds 0) := by
  have hlogμ : Real.log μ < 0 :=
    Real.log_neg hμ0 hμ1
  let a : ℝ := -Real.log μ
  have ha : 0 < a := by
    dsimp only [a]
    linarith
  have hratio :=
    tendsto_supercriticalTerminalBlockLength_div_log_nat_zero hb
  have hscaledRatio :
      Filter.Tendsto
        (fun N : ℕ =>
          a * ((supercriticalTerminalBlockLength b N : ℝ) /
            Real.log (N : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hratio.const_mul a
  have hsmall :
      ∀ᶠ N : ℕ in Filter.atTop,
        a * ((supercriticalTerminalBlockLength b N : ℝ) /
          Real.log (N : ℝ)) < 1 / 4 :=
    hscaledRatio
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hpow :
      ∀ᶠ N : ℕ in Filter.atTop,
        μ ^ (c -
            (supercriticalTerminalBlockLength b N : ℝ)) ≤
          μ ^ c * Real.sqrt (Real.sqrt (N : ℝ)) := by
    filter_upwards
        [hsmall, Filter.eventually_ge_atTop (2 : ℕ)] with
        N hsmallN hN
    have hNreal : 0 < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hblockExp :
        a * (supercriticalTerminalBlockLength b N : ℝ) ≤
          (1 / 4) * Real.log (N : ℝ) := by
      have hsmallN' :
          a * (supercriticalTerminalBlockLength b N : ℝ) /
              Real.log (N : ℝ) < 1 / 4 := by
        calc
          a * (supercriticalTerminalBlockLength b N : ℝ) /
                Real.log (N : ℝ) =
              a * ((supercriticalTerminalBlockLength b N : ℝ) /
                Real.log (N : ℝ)) := by ring
          _ < 1 / 4 := hsmallN
      exact ((div_lt_iff₀ hlogN).1 hsmallN').le
    have hquarter :
        Real.exp ((1 / 4) * Real.log (N : ℝ)) =
          Real.sqrt (Real.sqrt (N : ℝ)) := by
      rw [← Real.exp_log
        (Real.sqrt_pos.2 (Real.sqrt_pos.2 hNreal))]
      congr 1
      rw [Real.log_sqrt (Real.sqrt_nonneg _),
        Real.log_sqrt (Nat.cast_nonneg N)]
      ring
    rw [Real.rpow_def_of_pos hμ0, Real.rpow_def_of_pos hμ0,
      ← hquarter, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [a] at hblockExp
    linarith
  let K : ℝ := D * μ ^ c
  have hroot :
      Filter.Tendsto
        (fun N : ℕ => Real.sqrt (Real.sqrt (N : ℝ)))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hbase :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      1 0 2 one_ne_zero).comp hroot
  have hscaled :
      Filter.Tendsto
        (fun N : ℕ =>
          (16 * K) *
            (Real.log (Real.sqrt (Real.sqrt (N : ℝ))) ^ 2 /
              Real.sqrt (Real.sqrt (N : ℝ))))
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, one_mul, add_zero, mul_zero] using
      hbase.const_mul (16 * K)
  have hupperLimit :
      Filter.Tendsto
        (fun N : ℕ =>
          K * Real.sqrt (Real.sqrt (N : ℝ)) /
              Real.sqrt (N : ℝ) /
            supercriticalTerminalRadius N)
        Filter.atTop (nhds 0) := by
    apply hscaled.congr'
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
    have hNreal : 0 < (N : ℝ) := by
      exact_mod_cast (show 0 < N by omega)
    have hlogN : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    have hsqrtN : 0 < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos.2 hNreal
    have hrootN : 0 < Real.sqrt (Real.sqrt (N : ℝ)) :=
      Real.sqrt_pos.2 hsqrtN
    rw [supercriticalTerminalRadius,
      Real.log_sqrt (Real.sqrt_nonneg _),
      Real.log_sqrt (Nat.cast_nonneg N)]
    have hroot_sq :
        Real.sqrt (Real.sqrt (N : ℝ)) ^ 2 =
          Real.sqrt (N : ℝ) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    field_simp [hlogN, hsqrtN.ne', hrootN.ne', hNreal.ne']
    rw [hroot_sq]
    ring
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N => by
      apply div_nonneg
      · exact div_nonneg
          (mul_nonneg hD (Real.rpow_nonneg hμ0.le _))
          (Real.sqrt_nonneg (N : ℝ))
      · rw [supercriticalTerminalRadius]
        exact sq_nonneg _
  · filter_upwards [hpow] with N hpowN
    exact
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowN hD)
          (Real.sqrt_nonneg (N : ℝ)))
        (by rw [supercriticalTerminalRadius]; positivity)
  · simpa only [K, mul_assoc] using hupperLimit

end AbsorptionCutoff
