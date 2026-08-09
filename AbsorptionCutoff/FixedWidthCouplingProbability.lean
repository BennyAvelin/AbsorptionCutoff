/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCoupling

/-!
# Fixed-width probabilistic coupling assembly

This continuation module owns the adapted discrepancy multiplier, its Gaussian
radial law, the scalar affine domination, and the high-probability accumulated
rounding comparison on logarithmic time horizons.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Difference between the synchronously driven rounded and unrounded vector
paths. -/
noncomputable def fixedWidthVectorDiscrepancy
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → (Fin N → ℝ) :=
  fun n ω ↦ fixedWidthRoundedVectorPath ρ N x0 n ω -
    fixedWidthUnroundedVectorPath N x0 n ω

/-- Euclidean size of the synchronous path discrepancy. -/
noncomputable def fixedWidthVectorError
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → ℝ :=
  fun n ω ↦ gaussianEuclideanNorm N
    (fixedWidthVectorDiscrepancy ρ N x0 n ω)

/-- Matrix multiplier in the selected unit discrepancy direction. -/
noncomputable def fixedWidthDiscrepancyMultiplier
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → ℝ :=
  fun n ω ↦ gaussianEuclideanNorm N
    (Matrix.mulVec (ω n)
      (fixedWidthUnitDirection hN
        (fixedWidthVectorDiscrepancy ρ N x0 n ω)))

lemma measurable_fixedWidthUnitDirection
    {N : ℕ} (hN : 0 < N) :
    Measurable (fixedWidthUnitDirection hN) := by
  unfold fixedWidthUnitDirection
  exact Measurable.ite (measurableSet_singleton (0 : Fin N → ℝ))
    measurable_const
    ((measurable_gaussianEuclideanNorm N).inv.smul measurable_id)

lemma measurable_fixedWidthVectorDiscrepancy
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthVectorDiscrepancy ρ N x0 n) := by
  unfold fixedWidthVectorDiscrepancy
  exact (measurable_fixedWidthRoundedVectorPath ρ N x0 n).sub
    (measurable_fixedWidthUnroundedVectorPath N x0 n)

lemma measurable_fixedWidthVectorError
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthVectorError ρ N x0 n) :=
  (measurable_gaussianEuclideanNorm N).comp
    (measurable_fixedWidthVectorDiscrepancy ρ N x0 n)

lemma measurable_fixedWidthDiscrepancyMultiplier
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthDiscrepancyMultiplier hN ρ x0 n) := by
  have hω : Measurable
      (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n) :=
    measurable_pi_apply n
  have hθ : Measurable (fun ω : fixedWidthMatrixSampleSpace N ↦
      fixedWidthUnitDirection hN
        (fixedWidthVectorDiscrepancy ρ N x0 n ω)) :=
    (measurable_fixedWidthUnitDirection hN).comp
      (measurable_fixedWidthVectorDiscrepancy ρ N x0 n)
  have hmul : Measurable (fun ω : fixedWidthMatrixSampleSpace N ↦
      Matrix.mulVec (ω n)
        (fixedWidthUnitDirection hN
          (fixedWidthVectorDiscrepancy ρ N x0 n ω))) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp hω)).mul
        ((measurable_pi_apply j).comp hθ)
  exact (measurable_gaussianEuclideanNorm N).comp hmul

/-- The initial synchronous error is at most one coordinatewise rounding
contribution. -/
lemma fixedWidthVectorError_zero_le
    {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) (x0 : Fin N → ℝ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthVectorError ρ N x0 0 ω ≤ Real.sqrt N * (ρ / 2) := by
  simpa only [fixedWidthVectorError, fixedWidthVectorDiscrepancy,
    fixedWidthRoundedVectorPath, fixedWidthUnroundedVectorPath] using
      gaussianEuclideanNorm_Qρ_sub_le hρ N x0

/-- Scalar affine recursion dominating the synchronously accumulated rounding
error on every matrix sample. -/
lemma fixedWidthVectorError_succ_le
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthVectorError ρ N x0 (n + 1) ω ≤
      fixedWidthDiscrepancyMultiplier hN ρ x0 n ω *
          fixedWidthVectorError ρ N x0 n ω +
        Real.sqrt N * (ρ / 2) := by
  calc
    fixedWidthVectorError ρ N x0 (n + 1) ω ≤
        gaussianEuclideanNorm N
            (Matrix.mulVec (ω n)
              (fixedWidthVectorDiscrepancy ρ N x0 n ω)) +
          Real.sqrt N * (ρ / 2) := by
      simpa only [fixedWidthVectorError, fixedWidthVectorDiscrepancy] using
        fixedWidthVectorPath_error_succ_le hρ N x0 n ω
    _ = fixedWidthDiscrepancyMultiplier hN ρ x0 n ω *
          fixedWidthVectorError ρ N x0 n ω +
        Real.sqrt N * (ρ / 2) := by
      rw [gaussianEuclideanNorm_mulVec_eq_multiplier_mul hN]
      rfl

end AbsorptionCutoff
