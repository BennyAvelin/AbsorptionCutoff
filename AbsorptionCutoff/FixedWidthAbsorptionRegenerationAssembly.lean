/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthAbsorptionRegeneration

/-!
# Fixed-width finite-grid absorption regeneration assembly

This continuation module owns the remaining return-time moment,
regeneration-contraction, and final absorption-tail assembly for Chapter 3.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- The uniform rounded entrance estimate remains valid with the paper's
everywhere-positive logarithmic offset `log (max 2 K)`, including a start at
the origin. -/
theorem exists_uniform_fixedWidthRoundedGridSurvivalSetFrom_max_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar c1 c2 c3 : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ, ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            ⌊c1 * Real.log
              (max 2 (fixedWidthRoundedInitialGridRadius ρ N y0)) + r⌋₊) ≤
          c2 * Real.exp (-c3 * r) := by
  obtain ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, hbound⟩ :=
    exists_uniform_fixedWidthRoundedGridSurvivalSetFrom_bound hA hN hsub
  refine ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, ?_⟩
  intro ρ hρ y0 r
  let K := fixedWidthRoundedInitialGridRadius ρ N y0
  have hKnonneg : 0 ≤ K := by
    unfold K fixedWidthRoundedInitialGridRadius
    rw [gaussianEuclideanNorm_eq_norm]
    exact div_nonneg (norm_nonneg _) hρ.le
  rcases hKnonneg.eq_or_lt with hKzero | hKpos
  · have hempty :
        fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            ⌊c1 * Real.log (max 2 K) + r⌋₊ = ∅ := by
      ext ω
      simp only [fixedWidthRoundedGridSurvivalSetFrom, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false]
      intro h
      have hzero := h 0 (Nat.zero_le _)
      rw [fixedWidthRoundedGridRadiusFrom_zero] at hzero
      exact (not_lt_of_ge hKstar.le) (hKzero ▸ hzero)
    rw [hempty, measureReal_empty]
    positivity
  · let r' := c1 * (Real.log (max 2 K) - Real.log K) + r
    have hmaxpos : 0 < max 2 K := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hlog : Real.log K ≤ Real.log (max 2 K) :=
      Real.strictMonoOn_log.monotoneOn hKpos hmaxpos (le_max_right _ _)
    have hrr' : r ≤ r' := by
      dsimp only [r']
      nlinarith
    have hbase := hbound ρ hρ y0 hKpos r'
    have htime :
        ⌊c1 * Real.log K + r'⌋₊ =
          ⌊c1 * Real.log (max 2 K) + r⌋₊ := by
      congr 1
      dsimp only [r']
      ring
    rw [htime] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith)) hc2.le)

/-- The joint law of a deterministic-time rounded state and its shifted future
driver factors as the state marginal times a fresh canonical driver. -/
lemma map_prod_fixedWidthRoundedVectorPathFrom_shift
    (A ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (m : ℕ) :
    Measure.map
        (fun ω : fixedWidthMatrixSampleSpace N ↦
          (fixedWidthRoundedVectorPathFrom ρ N y0 m ω,
            fixedWidthMatrixShift N m ω))
        (fixedWidthMatrixGaussianMeasure A N) =
      (Measure.map (fixedWidthRoundedVectorPathFrom ρ N y0 m)
          (fixedWidthMatrixGaussianMeasure A N)).prod
        (fixedWidthMatrixGaussianMeasure A N) := by
  have hmap :=
    (indepFun_fixedWidthRoundedVectorPathFrom_shift A ρ N y0 m)
      |>.map_prod_eq_prod_map_map
        (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 m).aemeasurable
        (measurable_fixedWidthMatrixShift N m).aemeasurable
  rw [map_fixedWidthMatrixShift A N m] at hmap
  exact hmap

/-- The exact-start rounded state is jointly measurable in its deterministic
starting vector and matrix driver. -/
lemma measurable_fixedWidthRoundedVectorPathFrom_prod
    (ρ : ℝ) (N n : ℕ) :
    Measurable
      (fun p : (Fin N → ℝ) × fixedWidthMatrixSampleSpace N ↦
        fixedWidthRoundedVectorPathFrom ρ N p.1 n p.2) := by
  induction n with
  | zero =>
      simp only [fixedWidthRoundedVectorPathFrom]
      exact measurable_fst
  | succ n ih =>
      simp only [fixedWidthRoundedVectorPathFrom]
      have hmatrix : Measurable
          (fun p : (Fin N → ℝ) × fixedWidthMatrixSampleSpace N ↦ p.2 n) :=
        (measurable_pi_apply n).comp measurable_snd
      unfold roundedPstep
      apply (measurable_Qρ ρ N).comp
      apply measurable_pi_iff.mpr
      intro i
      unfold Pstep
      apply continuous_tanh.measurable.comp
      apply Finset.measurable_sum
      intro j _
      exact ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hmatrix)).mul
          ((measurable_pi_apply j).comp ih)

/-- The exact-start rounded grid radius is jointly measurable in its start and
driver. -/
lemma measurable_fixedWidthRoundedGridRadiusFrom_prod
    (ρ : ℝ) (N n : ℕ) :
    Measurable
      (fun p : (Fin N → ℝ) × fixedWidthMatrixSampleSpace N ↦
        fixedWidthRoundedGridRadiusFrom ρ N p.1 n p.2) :=
  ((measurable_gaussianEuclideanNorm N).comp
    (measurable_fixedWidthRoundedVectorPathFrom_prod ρ N n)).div_const ρ

end AbsorptionCutoff
