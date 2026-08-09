/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.TerminalEntranceAssembly

/-!
# Terminal cutoff assembly for the supercritical chain

This module continues the supercritical cutoff proof after the finite
stochastic entrance and post-entrance dynamic concentration established in
`TerminalEntranceAssembly.lean`. The remaining terminal-block localization
and paper-facing scalar and vector cutoff assembly belong here.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- For every positive convergent initial sequence, the evolving coordinate
is localized in the shrinking terminal interval throughout the restarted
terminal block. -/
theorem
    exists_eventually_forall_shifted_eval_not_mem_terminalInterval_le_of_tendsto
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
    (hb : 0 < b) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
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
  obtain ⟨Cₜ, hCₜ, hT, hblock⟩ :=
    exists_eventually_supercriticalCutoff_block_horizon
      (q₀ := q₀) hA hqStar hfix hb c
  obtain ⟨m, C, hC, hmoment⟩ :=
    exists_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_of_tendsto
      q (supercriticalIntegerCutoffTime A qStar q₀ · c)
      hA hqStar hfix hq₀ hq hqmem hCₜ.le hT
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
        [hmoment, hentranceBefore, hblock] with
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
  refine ⟨C, hC, ?_⟩
  exact
    eventually_forall_shifted_eval_not_mem_terminalInterval_le_of_center
      q
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      (supercriticalTerminalBlockLength b)
      hqIcc hcenterBlock hmomentBlock

/-- The independent evolving/stationary product at the terminal block start
has inverse-square-root stochastic fluctuations while retaining the paper's
varying deterministic center scale. -/
theorem
    exists_eventually_integral_abs_fst_sub_snd_terminalBlockStart_prod_le_rpow_div_sqrt_of_tendsto
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
    (hb : 0 < b) (c : ℝ)
    (hC₂ : 0 ≤ C₂)
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ)) :
    ∃ C₁ D : ℝ, 0 ≤ C₁ ∧ 0 < D ∧
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
  obtain ⟨Cₜ, hCₜ, hT, hblock⟩ :=
    exists_eventually_supercriticalCutoff_block_horizon
      (q₀ := q₀) hA hqStar hfix hb c
  obtain ⟨m, C₁, hC₁, hmoment⟩ :=
    exists_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_of_tendsto
      q (supercriticalIntegerCutoffTime A qStar q₀ · c)
      hA hqStar hfix hq₀ hq hqmem hCₜ.le hT
  have hentranceBefore :
      ∀ᶠ N : ℕ in Filter.atTop,
        m ≤ supercriticalTerminalBlockStart A qStar q₀ c b N :=
    (tendsto_supercriticalTerminalBlockStart_atTop
      (q₀ := q₀) hA hqStar hfix hb c).eventually
        (Filter.eventually_ge_atTop m)
  have hmomentStart :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ ω,
          (ω (supercriticalTerminalBlockStart A qStar q₀ c b N) -
              (V A)^[
                supercriticalTerminalBlockStart
                  A qStar q₀ c b N] (q N)) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N))) ≤
          C₁ / (N : ℝ) := by
    filter_upwards
        [hmoment, hentranceBefore, hblock] with
        N hmomentN hentranceBeforeN hblockN
    exact
      hmomentN
        (supercriticalTerminalBlockStart A qStar q₀ c b N)
        hentranceBeforeN
        ((Nat.le_add_right
          (supercriticalTerminalBlockStart A qStar q₀ c b N)
          (supercriticalTerminalBlockLength b N)).trans hblockN)
  obtain ⟨D, hD, hcenter⟩ :=
    exists_eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_mul_rpow_div_sqrt
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  have hqIcc :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1 :=
    hqmem.mono fun _ hqN => ⟨hqN.1.le, hqN.2⟩
  refine ⟨C₁, D, hC₁, hD, ?_⟩
  filter_upwards
      [hmomentStart, hνsq, hνbound, hcenter, hqIcc,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hmomentN hνsqN hνboundN hcenterN hqN hN
  have hNpos : 0 < N :=
    Nat.zero_lt_of_lt hN
  let ρ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac (q N)) (Kchain A N)
  haveI : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    infer_instance
  have hρsq :
      Integrable
        (fun ω : ℕ → ℝ =>
          (ω (supercriticalTerminalBlockStart A qStar q₀ c b N) -
            (V A)^[
              supercriticalTerminalBlockStart
                A qStar q₀ c b N] (q N)) ^ 2) ρ := by
    apply integrable_sq_sub_of_ae_mem_Icc ρ
      (fun ω : ℕ → ℝ =>
        ω (supercriticalTerminalBlockStart A qStar q₀ c b N))
      ((V A)^[
        supercriticalTerminalBlockStart A qStar q₀ c b N] (q N))
    · exact
        (((measurable_pi_apply
          (supercriticalTerminalBlockStart A qStar q₀ c b N)).sub
            measurable_const).pow_const 2).aestronglyMeasurable
    · simpa only [ρ] using
        markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
          hqN hNpos
            (supercriticalTerminalBlockStart A qStar q₀ c b N)
  simpa only [ρ] using
    integral_abs_fst_sub_snd_map_eval_prod_le_sqrt_add_const_add_sqrt_div_sqrt_nat
      ρ (ν N : Measure ℝ)
      (supercriticalTerminalBlockStart A qStar q₀ c b N)
      ((V A)^[
        supercriticalTerminalBlockStart A qStar q₀ c b N] (q N))
      qStar hC₁ hC₂ hρsq hνsqN hmomentN hνboundN hcenterN

/-- The shrinking terminal recursion for a positive convergent initial
sequence retains both the sharp deterministic block-start scale and the
inverse-square-root stochastic fluctuations. -/
theorem
    exists_eventually_terminalBlock_distance_le_contraction_pow_mul_rpow_add_of_tendsto
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
    (hb : 0 < b) (c : ℝ)
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
    exists_eventually_forall_shifted_eval_not_mem_terminalInterval_le_of_tendsto
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
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
  have hterminal :=
    eventually_integral_abs_fst_sub_snd_eval_blockStart_le_terminalContraction_pow_mul_add
      (ne_of_gt (zero_lt_one.trans hA))
      (mul_nonneg (by norm_num) hC₁) hC₂ q
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      (supercriticalTerminalBlockLength b) ν
      hcontraction hqIcc hνsupport hbad₁ hbad₂
  obtain ⟨C₀, D, hC₀, hD, hproduct⟩ :=
    exists_eventually_integral_abs_fst_sub_snd_terminalBlockStart_prod_le_rpow_div_sqrt_of_tendsto
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hC₂ hνsq hνbound
  refine ⟨L, C₁, C₀, D, hL, hC₁, hC₀, hD, ?_⟩
  filter_upwards [hterminal, hproduct] with
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

/-- Up to an arbitrary fixed factor above one, the post-entrance terminal
recursion uses the fixed-point multiplier power instead of the varying
shrinking-interval contraction power. -/
theorem
    exists_eventually_terminalBlock_distance_le_multiplier_pow_mul_rpow_add_of_tendsto
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
    (hb : 0 < b) (c : ℝ)
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
          C₂ / (N : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L C₁ C₀ D : ℝ,
      0 ≤ L ∧ 0 ≤ C₁ ∧ 0 ≤ C₀ ∧ 0 < D ∧
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
    exists_eventually_terminalBlock_distance_le_contraction_pow_mul_rpow_add_of_tendsto
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hC₂ hνsupport hνinv hνsq hνbound
  refine ⟨L, C₁, C₀, D, hL, hC₁, hC₀, hD, ?_⟩
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hratio :=
    tendsto_supercriticalTerminalContraction_div_multiplier_pow_blockLength_one
      hA hqStar hfix hL hb
  have hratioUpper :
      ∀ᶠ N : ℕ in Filter.atTop,
        (supercriticalTerminalContraction A qStar L N /
            deriv (V A) qStar) ^
            supercriticalTerminalBlockLength b N <
          1 + ε :=
    hratio (eventually_lt_nhds (by linarith))
  filter_upwards [hterminal, hratioUpper] with
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
