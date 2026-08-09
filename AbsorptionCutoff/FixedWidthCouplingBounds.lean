/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingAccumulation

/-!
# Fixed-width coupling subproduct bounds

This continuation module proves logarithmic-horizon bounds for subproducts of
the iid Gaussian radial multipliers, then accumulates the scalar rounding
recursion into the synchronous comparison estimate.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- The common radial multiplier law is the law of the Euclidean norm of a
standard Gaussian vector scaled by `A / √N`. -/
lemma fixedWidthRadialMultiplierLaw_eq_map_scaledGaussianEuclideanNorm
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    fixedWidthRadialMultiplierLaw A N =
      Measure.map
        (fun g : Fin N → ℝ ↦
          (A / Real.sqrt N) * gaussianEuclideanNorm N g)
        (gaussianVec N) := by
  have hscaleLaw :
      Measure.map (fun g : Fin N → ℝ ↦
          fun i ↦ (A / Real.sqrt N) * g i) (gaussianVec N) =
        Measure.pi (fun _ : Fin N ↦
          gaussianReal 0 ((A ^ 2 / N).toNNReal)) := by
    rw [gaussianVec]
    haveI : ∀ _i : Fin N, IsProbabilityMeasure
        ((gaussianReal 0 1).map (fun g ↦ (A / Real.sqrt N) * g)) :=
      fun _ ↦ Measure.isProbabilityMeasure_map (by fun_prop)
    rw [Measure.pi_map_pi (fun _ ↦ (by fun_prop :
      AEMeasurable (fun g : ℝ ↦ (A / Real.sqrt N) * g) (gaussianReal 0 1)))]
    congr 1
    funext i
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    apply NNReal.eq
    change (A / Real.sqrt N) ^ 2 = (A ^ 2 / (N : ℝ)).toNNReal
    rw [Real.coe_toNNReal]
    · rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    · positivity
  unfold fixedWidthRadialMultiplierLaw
  rw [← hscaleLaw]
  rw [Measure.map_map]
  · congr 1
    funext g
    change gaussianEuclideanNorm N ((A / Real.sqrt N) • g) =
      (A / Real.sqrt N) * gaussianEuclideanNorm N g
    rw [gaussianEuclideanNorm_smul, abs_of_pos]
    exact div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))
  · exact measurable_gaussianEuclideanNorm N
  · fun_prop

/-- Logarithm of the time-`n` synchronous discrepancy multiplier. -/
noncomputable def fixedWidthDiscrepancyLogMultiplier
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    fixedWidthMatrixSampleSpace N → ℝ :=
  fun ω ↦ Real.log (fixedWidthDiscrepancyMultiplier hN ρ x0 n ω)

lemma measurable_fixedWidthDiscrepancyLogMultiplier
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n) :=
  Real.measurable_log.comp
    (measurable_fixedWidthDiscrepancyMultiplier hN ρ x0 n)

/-- The path-specific log multiplier is the pushforward of the standard
Gaussian vector by the negative log-radial increment. -/
lemma map_fixedWidthDiscrepancyLogMultiplier
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measure.map (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n)
        (fixedWidthMatrixGaussianMeasure A N) =
      Measure.map (fun g : Fin N → ℝ ↦ -logRadialIncrement A N g)
        (gaussianVec N) := by
  unfold fixedWidthDiscrepancyLogMultiplier
  change Measure.map
      (Real.log ∘ fixedWidthDiscrepancyMultiplier hN ρ x0 n)
        (fixedWidthMatrixGaussianMeasure A N) =
    Measure.map (fun g : Fin N → ℝ ↦ -logRadialIncrement A N g)
      (gaussianVec N)
  rw [← Measure.map_map Real.measurable_log
    (measurable_fixedWidthDiscrepancyMultiplier hN ρ x0 n)]
  rw [map_fixedWidthDiscrepancyMultiplier A hN ρ x0 n,
    fixedWidthRadialMultiplierLaw_eq_map_scaledGaussianEuclideanNorm hA hN]
  rw [Measure.map_map]
  · congr 1
    funext g
    simp only [Function.comp_apply, logRadialIncrement, neg_neg]
  · exact Real.measurable_log
  · exact (measurable_gaussianEuclideanNorm N).const_mul _

/-- The time-`n` synchronous log multiplier has the same law as the negative
Gaussian log-radial increment. -/
lemma identDistrib_fixedWidthDiscrepancyLogMultiplier
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    IdentDistrib
      (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n)
      (fun g : Fin N → ℝ ↦ -logRadialIncrement A N g)
      (fixedWidthMatrixGaussianMeasure A N) (gaussianVec N) :=
  ⟨(measurable_fixedWidthDiscrepancyLogMultiplier hN ρ x0 n).aemeasurable,
    (measurable_logRadialIncrement A N).neg.aemeasurable,
    map_fixedWidthDiscrepancyLogMultiplier hA hN ρ x0 n⟩

/-- The expected logarithmic discrepancy multiplier is the Gaussian radial
drift. -/
lemma integral_fixedWidthDiscrepancyLogMultiplier_eq_logRadialDrift
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    ∫ ω, fixedWidthDiscrepancyLogMultiplier hN ρ x0 n ω
        ∂fixedWidthMatrixGaussianMeasure A N =
      logRadialDrift A N := by
  rw [(identDistrib_fixedWidthDiscrepancyLogMultiplier
    hA hN ρ x0 n).integral_eq]
  rw [integral_neg, integral_logRadialIncrement_eq_neg_logRadialDrift]
  simp

end AbsorptionCutoff
