/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingLaw

/-!
# Fixed-width coupling radial multipliers

This continuation module identifies the adapted discrepancy multiplier with
the common Gaussian radial law and owns the subsequent high-probability
accumulated rounding comparison.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Common law of a fixed-width Gaussian matrix multiplier in a unit
direction, expressed as the Euclidean norm of the isotropic product Gaussian
with coordinate variance `A² / N`. -/
noncomputable def fixedWidthRadialMultiplierLaw (A : ℝ) (N : ℕ) : Measure ℝ :=
  Measure.map (gaussianEuclideanNorm N)
    (Measure.pi (fun _ : Fin N ↦
      gaussianReal 0 ((A ^ 2 / N).toNNReal)))

/-- Gaussian matrix isotropy makes the radial multiplier law independent of
the chosen deterministic unit direction. -/
lemma map_gaussianEuclideanNorm_mulVec_gaussianMat_of_unit
    (A : ℝ) {N : ℕ} (θ : Fin N → ℝ)
    (hθ : gaussianEuclideanNorm N θ = 1) :
    Measure.map
        (fun W : Fin N → Fin N → ℝ ↦
          gaussianEuclideanNorm N (Matrix.mulVec W θ))
        (gaussianMat A N) =
      fixedWidthRadialMultiplierLaw A N := by
  have hsum : ∑ j, (θ j) ^ 2 = 1 := by
    have hsqrt : Real.sqrt (∑ j, (θ j) ^ 2) = 1 := by
      simpa [gaussianEuclideanNorm, gaussianSquaredNorm] using hθ
    have hnonneg : 0 ≤ ∑ j, (θ j) ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnonneg]
  have hradius : A ^ 2 * radiusSq N θ = A ^ 2 / N := by
    unfold radiusSq
    rw [hsum]
    simp [div_eq_mul_inv]
  let mulTheta : (Fin N → Fin N → ℝ) → (Fin N → ℝ) :=
    fun W i ↦ ∑ j, W i j * θ j
  have hmul : Measurable mulTheta := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [mulTheta]
    apply Finset.measurable_sum
    intro j _
    fun_prop
  change Measure.map (gaussianEuclideanNorm N ∘ mulTheta)
      (gaussianMat A N) = _
  rw [← Measure.map_map (measurable_gaussianEuclideanNorm N) hmul]
  unfold fixedWidthRadialMultiplierLaw
  congr 1
  simpa only [mulTheta, hradius] using
    (map_rowMap_gaussianMat A N θ)

/-- Mixing the Gaussian matrix fibre over any probability law supported on
unit directions leaves the common radial multiplier law unchanged. -/
lemma map_gaussianEuclideanNorm_mulVec_prod_eq_radialMultiplierLaw
    (A : ℝ) {N : ℕ} (ν : Measure (Fin N → ℝ))
    [IsProbabilityMeasure ν]
    (hν : ∀ᵐ θ ∂ν, gaussianEuclideanNorm N θ = 1) :
    Measure.map
        (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) ↦
          gaussianEuclideanNorm N (Matrix.mulVec p.2 p.1))
        (ν.prod (gaussianMat A N)) =
      fixedWidthRadialMultiplierLaw A N := by
  let mulNorm :
      (Fin N → ℝ) × (Fin N → Fin N → ℝ) → ℝ :=
    fun p ↦ gaussianEuclideanNorm N (Matrix.mulVec p.2 p.1)
  have hmulVec : Measurable
      (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) ↦
        Matrix.mulVec p.2 p.1) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp measurable_fst)
  have hmulNorm : Measurable mulNorm :=
    (measurable_gaussianEuclideanNorm N).comp hmulVec
  change Measure.map mulNorm (ν.prod (gaussianMat A N)) = _
  ext s hs
  rw [Measure.map_apply hmulNorm hs,
    Measure.prod_apply (hs.preimage hmulNorm)]
  have hsections : ∀ᵐ θ ∂ν,
      gaussianMat A N (Prod.mk θ ⁻¹' (mulNorm ⁻¹' s)) =
        fixedWidthRadialMultiplierLaw A N s := by
    filter_upwards [hν] with θ hθ
    have hfix : Measurable
        (fun W : Fin N → Fin N → ℝ ↦
          gaussianEuclideanNorm N (Matrix.mulVec W θ)) := by
      apply (measurable_gaussianEuclideanNorm N).comp
      apply measurable_pi_iff.mpr
      intro i
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.measurable_sum
      intro j _
      fun_prop
    rw [show Prod.mk θ ⁻¹' (mulNorm ⁻¹' s) =
        (fun W : Fin N → Fin N → ℝ ↦
          gaussianEuclideanNorm N (Matrix.mulVec W θ)) ⁻¹' s by rfl]
    rw [← Measure.map_apply hfix hs,
      map_gaussianEuclideanNorm_mulVec_gaussianMat_of_unit A θ hθ]
  calc
    ∫⁻ θ, gaussianMat A N (Prod.mk θ ⁻¹' (mulNorm ⁻¹' s)) ∂ν =
        ∫⁻ _θ, fixedWidthRadialMultiplierLaw A N s ∂ν :=
      lintegral_congr_ae hsections
    _ = fixedWidthRadialMultiplierLaw A N s := by simp

end AbsorptionCutoff
