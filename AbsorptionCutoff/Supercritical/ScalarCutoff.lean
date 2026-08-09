/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.TerminalCutoff
import AbsorptionCutoff.Supercritical.ScoreTensorization

/-!
# Scalar cutoff assembly for the supercritical chain

This module continues the supercritical cutoff proof after the finite-entrance
terminal coupling estimate established in `TerminalCutoff.lean`. The remaining
scalar cutoff asymptotics and score-smoothing assembly belong here.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- A coupling of two input laws bounds the total variation between their
kernel mixtures by the expected pointwise kernel distance on a good set, plus
the mass of its complement. -/
lemma tvDist_kernel_comp_map_fst_snd_le_integral_add_measureReal
    {E : Type*} [MeasurableSpace E]
    (κ : Kernel ℝ E) [IsMarkovKernel κ]
    (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (G : Set (ℝ × ℝ)) (hG : MeasurableSet G)
    (C : ℝ) (hC : 0 ≤ C)
    (hdist : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) π)
    (hgood :
      ∀ p ∈ G,
        tvDist (κ p.1) (κ p.2) ≤ C * |p.1 - p.2|) :
    tvDist (κ ∘ₘ π.map Prod.fst) (κ ∘ₘ π.map Prod.snd) ≤
      C * ∫ p, |p.1 - p.2| ∂π + π.real Gᶜ := by
  letI : IsProbabilityMeasure (π.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (π.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  unfold tvDist
  refine ciSup_le fun s => ?_
  have hκmeas :
      Measurable fun x : ℝ => (κ x s.1).toReal :=
    (κ.measurable_coe s.prop).ennreal_toReal
  have hfstInt :
      Integrable (fun p : ℝ × ℝ => (κ p.1 s.1).toReal) π := by
    apply (integrable_const (1 : ℝ)).mono'
      (hκmeas.comp measurable_fst).aestronglyMeasurable
    filter_upwards with p
    change |(κ p.1 s.1).toReal| ≤ 1
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have hsndInt :
      Integrable (fun p : ℝ × ℝ => (κ p.2 s.1).toReal) π := by
    apply (integrable_const (1 : ℝ)).mono'
      (hκmeas.comp measurable_snd).aestronglyMeasurable
    filter_upwards with p
    change |(κ p.2 s.1).toReal| ≤ 1
    rw [abs_of_nonneg ENNReal.toReal_nonneg, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have hdiff :
      Integrable
        (fun p : ℝ × ℝ =>
          (κ p.1 s.1).toReal - (κ p.2 s.1).toReal) π :=
    hfstInt.sub hsndInt
  have hbadInt :
      Integrable (Gᶜ.indicator (fun _ : ℝ × ℝ => (1 : ℝ))) π :=
    (integrable_const (1 : ℝ)).indicator hG.compl
  rw [Measure.bind_apply s.prop κ.aemeasurable,
    Measure.bind_apply s.prop κ.aemeasurable,
    ← integral_toReal
      (κ.measurable_coe s.prop).aemeasurable
      (Filter.Eventually.of_forall fun x =>
        lt_of_le_of_lt (prob_le_one : κ x s.1 ≤ 1) ENNReal.one_lt_top),
    ← integral_toReal
      (κ.measurable_coe s.prop).aemeasurable
      (Filter.Eventually.of_forall fun x =>
        lt_of_le_of_lt (prob_le_one : κ x s.1 ≤ 1) ENNReal.one_lt_top),
    integral_map measurable_fst.aemeasurable
      hκmeas.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable
      hκmeas.aestronglyMeasurable,
    ← integral_sub hfstInt hsndInt]
  calc
    |∫ p, ((κ p.1 s.1).toReal - (κ p.2 s.1).toReal) ∂π| ≤
        ∫ p, |(κ p.1 s.1).toReal - (κ p.2 s.1).toReal| ∂π := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm
          (fun p : ℝ × ℝ =>
            (κ p.1 s.1).toReal - (κ p.2 s.1).toReal)
    _ ≤
        ∫ p,
          (C * |p.1 - p.2| +
            Gᶜ.indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p) ∂π := by
      apply integral_mono hdiff.abs ((hdist.const_mul C).add hbadInt)
      intro p
      have hset :
          |(κ p.1 s.1).toReal - (κ p.2 s.1).toReal| ≤
            tvDist (κ p.1) (κ p.2) :=
        abs_measure_toReal_sub_le_tvDist
          (κ p.1) (κ p.2) s.1 s.prop
      by_cases hp : p ∈ G
      · calc
          |(κ p.1 s.1).toReal - (κ p.2 s.1).toReal| ≤
              tvDist (κ p.1) (κ p.2) := hset
          _ ≤ C * |p.1 - p.2| := hgood p hp
          _ = C * |p.1 - p.2| +
              Gᶜ.indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p := by
            simp [hp]
      · calc
          |(κ p.1 s.1).toReal - (κ p.2 s.1).toReal| ≤
              tvDist (κ p.1) (κ p.2) := hset
          _ ≤ 1 := tvDist_le_one (κ p.1) (κ p.2)
          _ ≤ C * |p.1 - p.2| +
              Gᶜ.indicator (fun _ : ℝ × ℝ => (1 : ℝ)) p := by
            simp only [Set.indicator_of_mem (Set.mem_compl hp)]
            linarith [mul_nonneg hC (abs_nonneg (p.1 - p.2))]
    _ = C * ∫ p, |p.1 - p.2| ∂π + π.real Gᶜ := by
      rw [integral_add (hdist.const_mul C) hbadInt,
        integral_const_mul, integral_indicator_const (1 : ℝ) hG.compl]
      simp

/-- On a stable interval bounded away from zero, one-step score smoothing
turns a coupling's expected coordinate distance into a total-variation bound,
up to the coupling mass outside the stable square. -/
lemma tvDist_Kchain_comp_map_fst_snd_le_integral_add_stableInterval
    {A qStar R : ℝ} (hA : 0 < A) (_hR : 0 < R) (hRq : R < qStar)
    (N : ℕ) (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hdist : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) π) :
    tvDist
        (Kchain A N ∘ₘ π.map Prod.fst)
        (Kchain A N ∘ₘ π.map Prod.snd) ≤
      Real.sqrt N / (2 * Real.sqrt 2 * (qStar - R)) *
          ∫ p, |p.1 - p.2| ∂π +
        π.real
          ((Set.Icc (qStar - R) (qStar + R) ×ˢ
            Set.Icc (qStar - R) (qStar + R))ᶜ) := by
  apply
    tvDist_kernel_comp_map_fst_snd_le_integral_add_measureReal
      (κ := Kchain A N)
      (G :=
        Set.Icc (qStar - R) (qStar + R) ×ˢ
          Set.Icc (qStar - R) (qStar + R))
      (C := Real.sqrt N / (2 * Real.sqrt 2 * (qStar - R)))
      π (measurableSet_Icc.prod measurableSet_Icc) (by positivity) hdist
  intro p hp
  have hq₁ : 0 < p.1 :=
    (sub_pos.mpr hRq).trans_le hp.1.1
  have hq₂ : 0 < p.2 :=
    (sub_pos.mpr hRq).trans_le hp.2.1
  calc
    tvDist (Kchain A N p.1) (Kchain A N p.2) ≤
        Real.sqrt N / (2 * Real.sqrt 2 * min p.2 p.1) *
          |p.1 - p.2| := by
      simpa only [abs_sub_comm, min_comm] using
        tvDist_Kchain_apply_le_of_pos hA hq₂ hq₁ N
    _ ≤ Real.sqrt N / (2 * Real.sqrt 2 * (qStar - R)) *
          |p.1 - p.2| := by
      gcongr
      exact le_min hp.2.1 hp.1.1

/-- Score smoothing applied to a fixed coordinate of a synchronous path can
be written directly in terms of the pathwise coordinate-distance integral
and the corresponding bad endpoint event. -/
lemma tvDist_Kchain_comp_map_eval_fst_snd_le_integral_add_stableInterval
    {A qStar R : ℝ} (hA : 0 < A) (hR : 0 < R) (hRq : R < qStar)
    (N : ℕ) (ξ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ξ] (t : ℕ)
    (hdist :
      Integrable (fun ω : ℕ → ℝ × ℝ => |(ω t).1 - (ω t).2|)
        (markovPathMeasure ξ (synchronousKchain A N))) :
    tvDist
        (Kchain A N ∘ₘ
          ((markovPathMeasure ξ (synchronousKchain A N)).map
            (fun ω => ω t)).map Prod.fst)
        (Kchain A N ∘ₘ
          ((markovPathMeasure ξ (synchronousKchain A N)).map
            (fun ω => ω t)).map Prod.snd) ≤
      Real.sqrt N / (2 * Real.sqrt 2 * (qStar - R)) *
          ∫ ω, |(ω t).1 - (ω t).2|
            ∂(markovPathMeasure ξ (synchronousKchain A N)) +
        (markovPathMeasure ξ (synchronousKchain A N)).real
          {ω : ℕ → ℝ × ℝ |
            ω t ∉
              Set.Icc (qStar - R) (qStar + R) ×ˢ
                Set.Icc (qStar - R) (qStar + R)} := by
  let μ :=
    markovPathMeasure ξ (synchronousKchain A N)
  let π : Measure (ℝ × ℝ) := μ.map (fun ω => ω t)
  haveI : IsProbabilityMeasure π := by
    dsimp only [π]
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_apply t).aemeasurable
  have hπdist :
      Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) π := by
    apply
      (integrable_map_measure
        ((measurable_fst.sub measurable_snd).abs.aestronglyMeasurable)
        (measurable_pi_apply t).aemeasurable).2
    change
      Integrable (fun ω : ℕ → ℝ × ℝ => |(ω t).1 - (ω t).2|) μ
    simpa only [μ] using hdist
  have hscore :=
    tvDist_Kchain_comp_map_fst_snd_le_integral_add_stableInterval
      hA hR hRq N π hπdist
  have hintegral :
      (∫ p, |p.1 - p.2| ∂π) =
        ∫ ω, |(ω t).1 - (ω t).2| ∂μ := by
    dsimp only [π]
    exact integral_map
      (measurable_pi_apply t).aemeasurable
      ((measurable_fst.sub measurable_snd).abs.aestronglyMeasurable)
  have hbad :
      π.real
          ((Set.Icc (qStar - R) (qStar + R) ×ˢ
            Set.Icc (qStar - R) (qStar + R))ᶜ) =
        μ.real
          {ω : ℕ → ℝ × ℝ |
            ω t ∉
              Set.Icc (qStar - R) (qStar + R) ×ˢ
                Set.Icc (qStar - R) (qStar + R)} := by
    dsimp only [π]
    rw [map_measureReal_apply
      (μ := μ) (measurable_pi_apply t)
      (measurableSet_Icc.prod measurableSet_Icc).compl]
    rfl
  simpa only [π, μ, hintegral, hbad] using hscore

/-- The evolving coordinate is still localized in the shrinking terminal
interval at the endpoint of the terminal block. -/
theorem
    exists_eventually_shifted_eval_terminalBlockLength_not_mem_terminalInterval_le_of_tendsto
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
        (markovPathMeasure
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockStart
                    A qStar q₀ c b N)))
            (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉
                Set.Icc
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
  have hmomentEndpoint :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ ω,
          (ω (supercriticalTerminalBlockStart
                A qStar q₀ c b N +
              supercriticalTerminalBlockLength b N) -
            (V A)^[
              supercriticalTerminalBlockStart
                  A qStar q₀ c b N +
                supercriticalTerminalBlockLength b N] (q N)) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N))) ≤
          C / (N : ℝ) := by
    filter_upwards
        [hmoment, hentranceBefore, hblock] with
        N hmomentN hentranceBeforeN hblockN
    exact
      hmomentN
        (supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N)
        (by omega) hblockN
  have hcenter :=
    eventually_forall_abs_V_iterate_terminalBlockStart_add_sub_fixed_le_half_terminalRadius
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  have hqIcc :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1 :=
    hqmem.mono fun _ hqN => ⟨hqN.1.le, hqN.2⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards
      [hmomentEndpoint, hcenter, hqIcc,
        Filter.eventually_ge_atTop (2 : ℕ)] with
      N hmomentN hcenterN hqN hN
  have hNpos : 0 < N := by omega
  have hsq :
      Integrable
        (fun ω : ℕ → ℝ =>
          (ω (supercriticalTerminalBlockStart
                A qStar q₀ c b N +
              supercriticalTerminalBlockLength b N) -
            (V A)^[
              supercriticalTerminalBlockStart
                  A qStar q₀ c b N +
                supercriticalTerminalBlockLength b N] (q N)) ^ 2)
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)) := by
    apply integrable_sq_sub_of_ae_mem_Icc
      (markovPathMeasure
        (Measure.dirac (q N)) (Kchain A N))
      (fun ω : ℕ → ℝ =>
        ω (supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N))
      ((V A)^[
        supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N] (q N))
    · exact
        (((measurable_pi_apply
          (supercriticalTerminalBlockStart A qStar q₀ c b N +
            supercriticalTerminalBlockLength b N)).sub
              measurable_const).pow_const 2).aestronglyMeasurable
    · exact
        markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
          hqN hNpos
            (supercriticalTerminalBlockStart A qStar q₀ c b N +
              supercriticalTerminalBlockLength b N)
  have hlocal :=
    markovPathMeasure_measureReal_eval_not_mem_stableInterval_le_four_mul_div_sq_div_nat_of_center
      (Measure.dirac (q N)) (Kchain A N)
      (supercriticalTerminalBlockStart A qStar q₀ c b N +
        supercriticalTerminalBlockLength b N)
      ((V A)^[
        supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N] (q N))
      qStar
      (supercriticalTerminalRadius_pos (show 1 < N by omega))
      (hcenterN (supercriticalTerminalBlockLength b N))
      hsq hmomentN
  let J : Set ℝ :=
    Set.Icc
      (qStar - supercriticalTerminalRadius N)
      (qStar + supercriticalTerminalRadius N)
  have hshift :=
    markovPathMeasure_measureReal_eval_mem_of_map_eval
      (Measure.dirac (q N)) (Kchain A N)
      (supercriticalTerminalBlockStart A qStar q₀ c b N)
      (supercriticalTerminalBlockLength b N) Jᶜ
      measurableSet_Icc.compl
  calc
    (markovPathMeasure
          ((markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).map
              (fun ω =>
                ω (supercriticalTerminalBlockStart
                  A qStar q₀ c b N)))
          (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω (supercriticalTerminalBlockLength b N) ∉
              Set.Icc
                (qStar - supercriticalTerminalRadius N)
                (qStar + supercriticalTerminalRadius N)} =
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω (supercriticalTerminalBlockStart A qStar q₀ c b N +
                supercriticalTerminalBlockLength b N) ∉
              Set.Icc
                (qStar - supercriticalTerminalRadius N)
                (qStar + supercriticalTerminalRadius N)} := by
      simpa only [J, Set.mem_compl_iff] using hshift
    _ ≤ (4 * C / supercriticalTerminalRadius N ^ 2) /
        (N : ℝ) := hlocal

/-- The terminal synchronous pair is localized in the shrinking stable
square at the endpoint used by one-step score smoothing. -/
theorem
    exists_eventually_terminalBlock_endpoint_not_mem_prod_le_of_tendsto
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
    (_hC₂ : 0 ≤ C₂)
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
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)).real
            {ω : ℕ → ℝ × ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉
                Set.Icc
                    (qStar - supercriticalTerminalRadius N)
                    (qStar + supercriticalTerminalRadius N) ×ˢ
                  Set.Icc
                    (qStar - supercriticalTerminalRadius N)
                    (qStar + supercriticalTerminalRadius N)} ≤
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) := by
  obtain ⟨C, hC, hbad₁⟩ :=
    exists_eventually_shifted_eval_terminalBlockLength_not_mem_terminalInterval_le_of_tendsto
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  have hbad₂all :=
    eventually_forall_stationary_eval_not_mem_terminalInterval_le_inv_nat
      ν hνinv hνsq hνbound
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbad₁, hbad₂all] with N hbad₁N hbad₂N
  let ρ : Measure ℝ :=
    (markovPathMeasure
      (Measure.dirac (q N)) (Kchain A N)).map
        (fun ω =>
          ω (supercriticalTerminalBlockStart A qStar q₀ c b N))
  let ξ : Measure (ℝ × ℝ) := ρ.prod (ν N : Measure ℝ)
  let J : Set ℝ :=
    Set.Icc
      (qStar - supercriticalTerminalRadius N)
      (qStar + supercriticalTerminalRadius N)
  haveI : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_apply
        (supercriticalTerminalBlockStart A qStar q₀ c b N)).aemeasurable
  haveI : IsProbabilityMeasure ξ := by
    dsimp only [ξ]
    infer_instance
  have hfst : ξ.map Prod.fst = ρ := by
    dsimp only [ξ]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : ξ.map Prod.snd = (ν N : Measure ℝ) := by
    dsimp only [ξ]
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
  have hpair :=
    markovPathMeasure_measureReal_eval_not_mem_prod_le_of_measure
      A N ξ (supercriticalTerminalBlockLength b N) J measurableSet_Icc
  rw [hfst, hsnd] at hpair
  calc
    (markovPathMeasure
          (((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockStart
                    A qStar q₀ c b N))).prod (ν N : Measure ℝ))
          (synchronousKchain A N)).real
          {ω : ℕ → ℝ × ℝ |
            ω (supercriticalTerminalBlockLength b N) ∉
              Set.Icc
                  (qStar - supercriticalTerminalRadius N)
                  (qStar + supercriticalTerminalRadius N) ×ˢ
                Set.Icc
                  (qStar - supercriticalTerminalRadius N)
                  (qStar + supercriticalTerminalRadius N)} ≤
        (markovPathMeasure ρ (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉ J} +
          (markovPathMeasure (ν N : Measure ℝ) (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉ J} := by
      simpa only [ξ, ρ, J] using hpair
    _ ≤
        (4 * C / supercriticalTerminalRadius N ^ 2) / (N : ℝ) +
          (C₂ / supercriticalTerminalRadius N ^ 2) / (N : ℝ) := by
      exact add_le_add hbad₁N
        (hbad₂N (supercriticalTerminalBlockLength b N))
    _ = ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
        (N : ℝ) := by ring

/-- A natural multiplier power cancels the corresponding negative part of a
real multiplier exponent. -/
lemma pow_mul_rpow_sub_natCast
    {μ : ℝ} (hμ : 0 < μ) (ℓ : ℕ) (c : ℝ) :
    μ ^ ℓ * μ ^ (c - (ℓ : ℝ)) = μ ^ c := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hμ]
  congr 1
  ring

/-- Every strict contraction multiplier vanishes when raised to the
diverging terminal block length. -/
lemma tendsto_pow_supercriticalTerminalBlockLength_zero
    {μ b : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hb : 0 < b) :
    Filter.Tendsto
      (fun N : ℕ => μ ^ supercriticalTerminalBlockLength b N)
      Filter.atTop (nhds 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one hμ0 hμ1).comp
    (tendsto_supercriticalTerminalBlockLength_atTop hb)

/-- The shrinking-radius localization error remains negligible on the
inverse-square-root scale after division by the terminal contraction gap. -/
lemma tendsto_sqrt_nat_mul_terminalLocalizationError_zero
    {A qStar L C : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    Filter.Tendsto
      (fun N : ℕ =>
        Real.sqrt (N : ℝ) *
          ((((C / supercriticalTerminalRadius N ^ 2) / (N : ℝ)) /
            (1 - supercriticalTerminalContraction A qStar L N))))
      Filter.atTop (nhds 0) := by
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hbase :=
    tendsto_sqrt_nat_mul_inv_nat_div_supercriticalTerminalRadius_sq_zero
  have hden :
      Filter.Tendsto
        (fun N : ℕ =>
          1 - supercriticalTerminalContraction A qStar L N)
        Filter.atTop (nhds (1 - deriv (V A) qStar)) :=
    tendsto_const_nhds.sub
      (tendsto_supercriticalTerminalContraction A qStar L)
  have hquot :
      Filter.Tendsto
        ((fun N : ℕ =>
            C *
              (Real.sqrt (N : ℝ) *
                ((1 / (N : ℝ)) /
                  supercriticalTerminalRadius N ^ 2))) /
          (fun N : ℕ =>
            1 - supercriticalTerminalContraction A qStar L N))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_div] using
      (hbase.const_mul C).div hden (sub_ne_zero.mpr hμ.2.ne')
  convert hquot using 1
  funext N
  change
    Real.sqrt (N : ℝ) *
        (((C / supercriticalTerminalRadius N ^ 2) / (N : ℝ)) /
          (1 - supercriticalTerminalContraction A qStar L N)) =
      (C *
          (Real.sqrt (N : ℝ) *
            ((1 / (N : ℝ)) /
              supercriticalTerminalRadius N ^ 2))) /
        (1 - supercriticalTerminalContraction A qStar L N)
  ring

/-- The shrinking-radius endpoint escape scale vanishes without the stronger
inverse-square-root normalization. -/
lemma tendsto_inv_nat_div_supercriticalTerminalRadius_sq_zero :
    Filter.Tendsto
      (fun N : ℕ =>
        (1 / (N : ℝ)) / supercriticalTerminalRadius N ^ 2)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N =>
      div_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg N)) (sq_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with N hN
    have hbase :
        0 ≤ (1 / (N : ℝ)) / supercriticalTerminalRadius N ^ 2 :=
      div_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg N)) (sq_nonneg _)
    have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_one]
      gcongr
      exact_mod_cast hN
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hsqrt hbase
  · exact
      tendsto_sqrt_nat_mul_inv_nat_div_supercriticalTerminalRadius_sq_zero

/-- The terminal synchronous distance has the paper's cutoff profile on the
inverse-square-root scale, up to an arbitrary fixed contraction comparison
factor and vanishing slack. -/
theorem
    exists_eventually_sqrt_nat_mul_terminalBlock_distance_le_rpow_add
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
    ∃ D : ℝ, 0 < D ∧ ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ N : ℕ in Filter.atTop,
        Real.sqrt (N : ℝ) *
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
          (1 + ε) * D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨L, C₁, C₀, D, hL, hC₁, hC₀, hD, hterminal⟩ :=
    exists_eventually_terminalBlock_distance_le_multiplier_pow_mul_rpow_add_of_tendsto
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hC₂ hνsupport hνinv hνsq hνbound hε
  refine ⟨D, hD, ?_⟩
  intro ζ hζ
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hfluct :
      Filter.Tendsto
        (fun N : ℕ =>
          deriv (V A) qStar ^
              supercriticalTerminalBlockLength b N *
            (Real.sqrt C₀ + Real.sqrt C₂))
        Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_supercriticalTerminalBlockLength_zero
        hμ.1.le hμ.2 hb).mul_const (Real.sqrt C₀ + Real.sqrt C₂)
  have hlocalization :=
    tendsto_sqrt_nat_mul_terminalLocalizationError_zero
      (L := L) (C := 4 * C₁ + C₂) hA hqStar hfix
  have hupper :
      Filter.Tendsto
        (fun N : ℕ =>
          (1 + ε) *
              (deriv (V A) qStar ^
                    supercriticalTerminalBlockLength b N *
                  (Real.sqrt C₀ + Real.sqrt C₂) +
                D * deriv (V A) qStar ^ c) +
            Real.sqrt (N : ℝ) *
              ((((4 * C₁ + C₂) /
                    supercriticalTerminalRadius N ^ 2) /
                  (N : ℝ)) /
                (1 -
                  supercriticalTerminalContraction A qStar L N)))
        Filter.atTop
          (nhds ((1 + ε) *
            (D * deriv (V A) qStar ^ c))) := by
    simpa only [zero_add, add_zero] using
      ((hfluct.add_const
        (D * deriv (V A) qStar ^ c)).const_mul (1 + ε)).add
          hlocalization
  have hupperEventually :
      ∀ᶠ N : ℕ in Filter.atTop,
        (1 + ε) *
              (deriv (V A) qStar ^
                    supercriticalTerminalBlockLength b N *
                  (Real.sqrt C₀ + Real.sqrt C₂) +
                D * deriv (V A) qStar ^ c) +
            Real.sqrt (N : ℝ) *
              ((((4 * C₁ + C₂) /
                    supercriticalTerminalRadius N ^ 2) /
                  (N : ℝ)) /
                (1 -
                  supercriticalTerminalContraction A qStar L N)) <
          (1 + ε) * D * deriv (V A) qStar ^ c + ζ :=
    hupper (eventually_lt_nhds (by linarith))
  filter_upwards
      [hterminal, hupperEventually,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hterminalN hupperN hN
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hsqrt : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 hNpos
  have hscaled :=
    mul_le_mul_of_nonneg_left hterminalN hsqrt.le
  calc
    Real.sqrt (N : ℝ) *
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
        Real.sqrt (N : ℝ) *
          ((1 + ε) *
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
                supercriticalTerminalContraction A qStar L N))) :=
      hscaled
    _ =
        (1 + ε) *
              (deriv (V A) qStar ^
                    supercriticalTerminalBlockLength b N *
                  (Real.sqrt C₀ + Real.sqrt C₂) +
                D * deriv (V A) qStar ^ c) +
            Real.sqrt (N : ℝ) *
              ((((4 * C₁ + C₂) /
                    supercriticalTerminalRadius N ^ 2) /
                  (N : ℝ)) /
                (1 -
                  supercriticalTerminalContraction A qStar L N)) := by
      have hcancel :=
        pow_mul_rpow_sub_natCast hμ.1
          (supercriticalTerminalBlockLength b N) c
      have halgebra :
          deriv (V A) qStar ^
                supercriticalTerminalBlockLength b N *
              (Real.sqrt C₀ +
                D * deriv (V A) qStar ^
                  (c -
                    (supercriticalTerminalBlockLength b N : ℝ)) +
                Real.sqrt C₂) =
            deriv (V A) qStar ^
                  supercriticalTerminalBlockLength b N *
                (Real.sqrt C₀ + Real.sqrt C₂) +
              D * deriv (V A) qStar ^ c := by
        calc
          _ =
              deriv (V A) qStar ^
                    supercriticalTerminalBlockLength b N *
                  (Real.sqrt C₀ + Real.sqrt C₂) +
                D *
                  (deriv (V A) qStar ^
                      supercriticalTerminalBlockLength b N *
                    deriv (V A) qStar ^
                      (c -
                        (supercriticalTerminalBlockLength b N : ℝ))) := by
            ring
          _ = _ := by rw [hcancel]
      rw [mul_add]
      field_simp [hsqrt.ne']
      linear_combination (1 + ε) * (N : ℝ) * halgebra
    _ ≤ (1 + ε) * D * deriv (V A) qStar ^ c + ζ :=
      hupperN.le

/-- One-step score smoothing turns the terminal synchronous coupling into the
scalar upper cutoff profile for the two smoothed terminal marginals. -/
theorem
    exists_eventually_terminalBlock_smoothed_tvDist_le_rpow_add_of_tendsto
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
    ∃ D : ℝ, 0 < D ∧ ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ N : ℕ in Filter.atTop,
        tvDist
            (Kchain A N ∘ₘ
              ((markovPathMeasure
                (((markovPathMeasure
                    (Measure.dirac (q N)) (Kchain A N)).map
                      (fun ω =>
                        ω (supercriticalTerminalBlockStart
                          A qStar q₀ c b N))).prod (ν N : Measure ℝ))
                (synchronousKchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockLength b N))).map Prod.fst)
            (Kchain A N ∘ₘ
              ((markovPathMeasure
                (((markovPathMeasure
                    (Measure.dirac (q N)) (Kchain A N)).map
                      (fun ω =>
                        ω (supercriticalTerminalBlockStart
                          A qStar q₀ c b N))).prod (ν N : Measure ℝ))
                (synchronousKchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockLength b N))).map Prod.snd) ≤
          D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨D₀, hD₀, hdistance⟩ :=
    exists_eventually_sqrt_nat_mul_terminalBlock_distance_le_rpow_add
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hC₂ hνsupport hνinv hνsq hνbound
      (ε := 1) (by norm_num)
  obtain ⟨C, hC, hbad⟩ :=
    exists_eventually_terminalBlock_endpoint_not_mem_prod_le_of_tendsto
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hC₂ hνinv hνsq hνbound
  let B : ℝ := 1 / (Real.sqrt 2 * qStar)
  have hB : 0 < B := by
    dsimp only [B]
    exact one_div_pos.mpr
      (mul_pos (Real.sqrt_pos.2 (by norm_num)) hqStar.1)
  have hbadLimit :
      Filter.Tendsto
        (fun N : ℕ =>
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ))
        Filter.atTop (nhds 0) := by
    have hlimit :=
      tendsto_inv_nat_div_supercriticalTerminalRadius_sq_zero.const_mul
        (4 * C + C₂)
    convert hlimit using 1
    · funext N
      ring
    · simp
  have hradiusUpper :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalRadius N < qStar / 2 :=
    tendsto_supercriticalTerminalRadius_zero
      (eventually_lt_nhds (by linarith [hqStar.1]))
  refine ⟨2 * B * D₀, mul_pos (mul_pos (by norm_num) hB) hD₀, ?_⟩
  intro ζ hζ
  have hslack : 0 < ζ / (2 * B) := by positivity
  have hdistanceSlack :=
    hdistance (ζ / (2 * B)) hslack
  have hbadSmall :
      ∀ᶠ N : ℕ in Filter.atTop,
        ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) ≤
          ζ / 2 :=
    Filter.Eventually.mono
      (hbadLimit (eventually_lt_nhds (by linarith)))
      fun _ hN => hN.le
  filter_upwards
      [hdistanceSlack, hbad, hbadSmall, hradiusUpper,
        hqmem, hνsupport, Filter.eventually_ge_atTop (2 : ℕ)] with
      N hdistanceN hbadN hbadSmallN hradiusUpperN
        hqN hνsupportN hN
  have hNpos : 0 < N := by omega
  have hradiusPos : 0 < supercriticalTerminalRadius N :=
    supercriticalTerminalRadius_pos (show 1 < N by omega)
  have hradiusQ : supercriticalTerminalRadius N < qStar := by
    linarith [hqStar.1]
  let ρ : Measure ℝ :=
    (markovPathMeasure
      (Measure.dirac (q N)) (Kchain A N)).map
        (fun ω =>
          ω (supercriticalTerminalBlockStart A qStar q₀ c b N))
  let ξ : Measure (ℝ × ℝ) := ρ.prod (ν N : Measure ℝ)
  haveI : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_apply
        (supercriticalTerminalBlockStart A qStar q₀ c b N)).aemeasurable
  haveI : IsProbabilityMeasure ξ := by
    dsimp only [ξ]
    infer_instance
  have hρsupport :
      ρ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    dsimp only [ρ]
    exact
      markovPathMeasure_dirac_map_eval_apply_compl_Icc_eq_zero
        (A := A) ⟨hqN.1.le, hqN.2⟩ hNpos
          (supercriticalTerminalBlockStart A qStar q₀ c b N)
  have hξsupport :
      ξ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    dsimp only [ξ]
    exact Measure.prod_apply_compl_prod_Icc_eq_zero
      ρ (ν N : Measure ℝ) hρsupport hνsupportN
  have hdistInt :
      Integrable
        (fun ω : ℕ → ℝ × ℝ =>
          |(ω (supercriticalTerminalBlockLength b N)).1 -
            (ω (supercriticalTerminalBlockLength b N)).2|)
        (markovPathMeasure ξ (synchronousKchain A N)) :=
    integrable_abs_fst_sub_snd_eval_synchronousKchain_of_measure
      hNpos ξ hξsupport (supercriticalTerminalBlockLength b N)
  have hscore :=
    tvDist_Kchain_comp_map_eval_fst_snd_le_integral_add_stableInterval
      (qStar := qStar) (R := supercriticalTerminalRadius N)
      (zero_lt_one.trans hA) hradiusPos hradiusQ N ξ
      (supercriticalTerminalBlockLength b N) hdistInt
  have hgap :
      qStar / 2 ≤ qStar - supercriticalTerminalRadius N := by
    linarith
  have hden :
      Real.sqrt 2 * qStar ≤
        2 * Real.sqrt 2 *
          (qStar - supercriticalTerminalRadius N) := by
    calc
      Real.sqrt 2 * qStar =
          (2 * Real.sqrt 2) * (qStar / 2) := by ring
      _ ≤ (2 * Real.sqrt 2) *
          (qStar - supercriticalTerminalRadius N) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
  have hcoef :
      1 /
          (2 * Real.sqrt 2 *
            (qStar - supercriticalTerminalRadius N)) ≤
        B := by
    dsimp only [B]
    exact one_div_le_one_div_of_le
      (mul_pos (Real.sqrt_pos.2 (by norm_num)) hqStar.1) hden
  have hscaledNonneg :
      0 ≤
        Real.sqrt (N : ℝ) *
          ∫ ω,
            |(ω (supercriticalTerminalBlockLength b N)).1 -
              (ω (supercriticalTerminalBlockLength b N)).2|
            ∂(markovPathMeasure ξ (synchronousKchain A N)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)
  have hdistanceN' := hdistanceN
  norm_num only at hdistanceN'
  calc
    tvDist
          (Kchain A N ∘ₘ
            ((markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockLength b N))).map Prod.fst)
          (Kchain A N ∘ₘ
            ((markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockLength b N))).map Prod.snd) ≤
        Real.sqrt (N : ℝ) /
              (2 * Real.sqrt 2 *
                (qStar - supercriticalTerminalRadius N)) *
            ∫ ω,
              |(ω (supercriticalTerminalBlockLength b N)).1 -
                (ω (supercriticalTerminalBlockLength b N)).2|
              ∂(markovPathMeasure ξ (synchronousKchain A N)) +
          (markovPathMeasure ξ (synchronousKchain A N)).real
            {ω : ℕ → ℝ × ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉
                Set.Icc
                    (qStar - supercriticalTerminalRadius N)
                    (qStar + supercriticalTerminalRadius N) ×ˢ
                  Set.Icc
                    (qStar - supercriticalTerminalRadius N)
                    (qStar + supercriticalTerminalRadius N)} := by
      simpa only [ξ, ρ] using hscore
    _ ≤
        (1 /
              (2 * Real.sqrt 2 *
                (qStar - supercriticalTerminalRadius N))) *
            (Real.sqrt (N : ℝ) *
              ∫ ω,
                |(ω (supercriticalTerminalBlockLength b N)).1 -
                  (ω (supercriticalTerminalBlockLength b N)).2|
                ∂(markovPathMeasure ξ (synchronousKchain A N))) +
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) := by
      convert add_le_add_left hbadN
        (1 /
          (2 * Real.sqrt 2 *
            (qStar - supercriticalTerminalRadius N)) *
          (Real.sqrt (N : ℝ) *
            ∫ ω,
              |(ω (supercriticalTerminalBlockLength b N)).1 -
                (ω (supercriticalTerminalBlockLength b N)).2|
              ∂(markovPathMeasure ξ (synchronousKchain A N))) ) using 1 <;>
        ring
    _ ≤
        B *
            (Real.sqrt (N : ℝ) *
              ∫ ω,
                |(ω (supercriticalTerminalBlockLength b N)).1 -
                  (ω (supercriticalTerminalBlockLength b N)).2|
                ∂(markovPathMeasure ξ (synchronousKchain A N))) +
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hcoef hscaledNonneg) le_rfl
    _ ≤
        B *
            (2 * D₀ * deriv (V A) qStar ^ c + ζ / (2 * B)) +
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hB.le
        simpa only [ξ, ρ] using hdistanceN'
      · exact le_rfl
    _ ≤
        B *
            (2 * D₀ * deriv (V A) qStar ^ c + ζ / (2 * B)) +
          ζ / 2 :=
      add_le_add le_rfl hbadSmallN
    _ = (2 * B * D₀) * deriv (V A) qStar ^ c + ζ := by
      field_simp [hB.ne']
      ring

end AbsorptionCutoff
