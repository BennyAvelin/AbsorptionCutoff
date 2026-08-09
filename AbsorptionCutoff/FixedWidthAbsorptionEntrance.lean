/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthAbsorption

/-!
# Fixed-width affine entrance and absorption

This continuation module applies negative-drift affine entrance to the rounded
grid radius and proves the return and absorption estimates required in Chapter 3.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- Logarithm of the time-`n` exact-start rounded-radius multiplier. -/
noncomputable def fixedWidthRoundedRadiusLogMultiplierFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    fixedWidthMatrixSampleSpace N → ℝ :=
  fun ω ↦ Real.log
    (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω)

lemma measurable_fixedWidthRoundedRadiusLogMultiplierFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthRoundedRadiusLogMultiplierFrom hN ρ y0 n) :=
  Real.measurable_log.comp
    (measurable_fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n)

/-- Every exact-start rounded log multiplier has the same law as the already
analyzed time-zero synchronous-discrepancy log multiplier. -/
lemma identDistrib_fixedWidthRoundedRadiusLogMultiplierFrom
    {A : ℝ} {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    IdentDistrib
      (fixedWidthRoundedRadiusLogMultiplierFrom hN ρ y0 n)
      (fixedWidthDiscrepancyLogMultiplier hN 0 (0 : Fin N → ℝ) 0)
      (fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hident : IdentDistrib
      (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n)
      (fixedWidthDiscrepancyMultiplier hN 0 (0 : Fin N → ℝ) 0)
      (fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthMatrixGaussianMeasure A N) :=
    ⟨(measurable_fixedWidthRoundedRadiusMultiplierFrom
        hN ρ y0 n).aemeasurable,
      (measurable_fixedWidthDiscrepancyMultiplier
        hN 0 (0 : Fin N → ℝ) 0).aemeasurable,
      (map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ y0 n).trans
        (map_fixedWidthDiscrepancyMultiplier
          A hN 0 (0 : Fin N → ℝ) 0).symm⟩
  exact hident.comp Real.measurable_log

/-- The expected exact-start rounded log multiplier is the Gaussian radial
drift. -/
lemma integral_fixedWidthRoundedRadiusLogMultiplierFrom_eq_logRadialDrift
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    ∫ ω, fixedWidthRoundedRadiusLogMultiplierFrom hN ρ y0 n ω
        ∂fixedWidthMatrixGaussianMeasure A N =
      logRadialDrift A N := by
  rw [(identDistrib_fixedWidthRoundedRadiusLogMultiplierFrom
    (A := A) hN ρ y0 n).integral_eq]
  exact integral_fixedWidthDiscrepancyLogMultiplier_eq_logRadialDrift
    hA hN 0 (0 : Fin N → ℝ) 0

/-- Exact-start rounded log multipliers inherit the common symmetric
exponential-integrability interval `(-N,N)`. -/
lemma Ioo_subset_integrableExpSet_fixedWidthRoundedRadiusLogMultiplierFrom
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Set.Ioo (-(N : ℝ)) (N : ℝ) ⊆
      integrableExpSet
        (fixedWidthRoundedRadiusLogMultiplierFrom hN ρ y0 n)
        (fixedWidthMatrixGaussianMeasure A N) := by
  intro t ht
  have href :=
    Ioo_subset_integrableExpSet_fixedWidthDiscrepancyLogMultiplier
      hA hN 0 (0 : Fin N → ℝ) 0 ht
  have hident :=
    (identDistrib_fixedWidthRoundedRadiusLogMultiplierFrom
      (A := A) hN ρ y0 n).comp
      (u := fun z : ℝ ↦ Real.exp (t * z)) (by fun_prop)
  exact (hident.integrable_iff).mpr href

/-- Every exact-start rounded log multiplier has exponential moments on a
neighborhood of zero. -/
lemma zero_mem_interior_integrableExpSet_fixedWidthRoundedRadiusLogMultiplierFrom
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    0 ∈ interior
      (integrableExpSet
        (fixedWidthRoundedRadiusLogMultiplierFrom hN ρ y0 n)
        (fixedWidthMatrixGaussianMeasure A N)) := by
  apply interior_maximal
    (Ioo_subset_integrableExpSet_fixedWidthRoundedRadiusLogMultiplierFrom
      hA hN ρ y0 n) isOpen_Ioo
  constructor
  · exact neg_neg_of_pos (by exact_mod_cast hN)
  · exact_mod_cast hN

/-- Exact-start rounded-radius multipliers are strictly positive almost surely. -/
lemma ae_fixedWidthRoundedRadiusMultiplierFrom_pos
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    ∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
      0 < fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω := by
  let scaleNorm : (Fin N → ℝ) → ℝ :=
    fun g ↦ (A / Real.sqrt N) * gaussianEuclideanNorm N g
  have hscale : 0 < A / Real.sqrt N :=
    div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))
  have hscaleMeas : AEMeasurable scaleNorm (gaussianVec N) :=
    ((measurable_gaussianEuclideanNorm N).const_mul _).aemeasurable
  have htarget :
      ∀ᵐ z ∂Measure.map scaleNorm (gaussianVec N), 0 < z := by
    rw [ae_map_iff hscaleMeas measurableSet_Ioi]
    filter_upwards [ae_gaussianEuclideanNorm_pos hN] with g hg
    exact mul_pos hscale hg
  have hlaw := map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ y0 n
  rw [fixedWidthRadialMultiplierLaw_eq_map_scaledGaussianEuclideanNorm
    hA hN] at hlaw
  rw [← ae_map_iff
    (measurable_fixedWidthRoundedRadiusMultiplierFrom
      hN ρ y0 n).aemeasurable measurableSet_Ioi]
  rw [hlaw]
  exact htarget

end AbsorptionCutoff
