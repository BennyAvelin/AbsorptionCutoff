/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthAbsorptionEntrance

/-!
# Fixed-width affine entrance bounds

This continuation module proves the shifted-log domination hypotheses and
applies negative-drift affine entrance to the rounded grid radius.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- Uniform deterministic envelope for the positive shifts used in dominated
convergence: when `x>0` and `0≤ε≤1`, the shifted logarithm is bounded by
`|log x|+x`. -/
lemma norm_log_add_le_norm_log_add_self {x ε : ℝ} (hx : 0 < x)
    (hε : 0 ≤ ε) (hε_one : ε ≤ 1) :
    ‖Real.log (x + ε)‖ ≤ ‖Real.log x‖ + x := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hxε : 0 < x + ε := add_pos_of_pos_of_nonneg hx hε
  by_cases hsmall : x + ε ≤ 1
  · rw [abs_of_nonpos (Real.log_nonpos hxε.le hsmall)]
    have hlog : Real.log x ≤ Real.log (x + ε) :=
      Real.log_le_log hx (le_add_of_nonneg_right hε)
    calc
      -Real.log (x + ε) ≤ -Real.log x := neg_le_neg hlog
      _ ≤ |Real.log x| := neg_le_abs _
      _ ≤ |Real.log x| + x := le_add_of_nonneg_right hx.le
  · have hone : 1 ≤ x + ε := le_of_not_ge hsmall
    rw [abs_of_nonneg (Real.log_nonneg hone)]
    calc
      Real.log (x + ε) ≤ x + ε - 1 :=
        Real.log_le_sub_one_of_pos hxε
      _ ≤ x := by linarith
      _ ≤ |Real.log x| + x := le_add_of_nonneg_left (abs_nonneg _)

/-- The Euclidean norm of a standard finite-dimensional Gaussian vector is
integrable. -/
lemma integrable_gaussianEuclideanNorm (N : ℕ) :
    Integrable (gaussianEuclideanNorm N) (gaussianVec N) := by
  have hsquareInterior :
      0 ∈ interior
        (integrableExpSet (gaussianSquaredNorm N) (gaussianVec N)) := by
    have hsub : Set.Iio (1 / 2 : ℝ) ⊆
        integrableExpSet (gaussianSquaredNorm N) (gaussianVec N) := by
      intro t ht
      exact integrable_exp_mul_gaussianSquaredNorm_of_lt N ht
    exact interior_maximal hsub isOpen_Iio (by norm_num)
  have hsquare : Integrable (gaussianSquaredNorm N) (gaussianVec N) :=
    integrable_of_mem_interior_integrableExpSet hsquareInterior
  have hmajorant : Integrable
      (fun g : Fin N → ℝ ↦ 1 + gaussianSquaredNorm N g)
      (gaussianVec N) :=
    (integrable_const 1).add hsquare
  refine hmajorant.mono'
    (measurable_gaussianEuclideanNorm N).aestronglyMeasurable ?_
  filter_upwards with g
  have hs : 0 ≤ gaussianSquaredNorm N g := by
    unfold gaussianSquaredNorm
    positivity
  have hsqrt : 0 ≤ Real.sqrt (gaussianSquaredNorm N g) :=
    Real.sqrt_nonneg _
  have hsq : (Real.sqrt (gaussianSquaredNorm N g)) ^ 2 =
      gaussianSquaredNorm N g := Real.sq_sqrt hs
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by unfold gaussianEuclideanNorm; positivity)]
  unfold gaussianEuclideanNorm
  nlinarith [sq_nonneg (Real.sqrt (gaussianSquaredNorm N g) - 1)]

/-- Every exact-start rounded-radius multiplier is integrable under the
canonical matrix law. -/
lemma integrable_fixedWidthRoundedRadiusMultiplierFrom
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Integrable (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  let scaleNorm : (Fin N → ℝ) → ℝ :=
    fun g ↦ (A / Real.sqrt N) * gaussianEuclideanNorm N g
  have hident : IdentDistrib
      (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n)
      scaleNorm
      (fixedWidthMatrixGaussianMeasure A N) (gaussianVec N) :=
    ⟨(measurable_fixedWidthRoundedRadiusMultiplierFrom
        hN ρ y0 n).aemeasurable,
      ((measurable_gaussianEuclideanNorm N).const_mul _).aemeasurable,
      (map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ y0 n).trans
        (fixedWidthRadialMultiplierLaw_eq_map_scaledGaussianEuclideanNorm
          hA hN)⟩
  apply hident.integrable_iff.mpr
  exact (integrable_gaussianEuclideanNorm N).const_mul _

/-- Integrable envelope used for all positive inverse-natural shifts of an
exact-start rounded multiplier. -/
noncomputable def fixedWidthRoundedRadiusLogEnvelopeFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    fixedWidthMatrixSampleSpace N → ℝ :=
  fun ω ↦
    ‖fixedWidthRoundedRadiusLogMultiplierFrom hN ρ y0 n ω‖ +
      fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω

lemma integrable_fixedWidthRoundedRadiusLogEnvelopeFrom
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Integrable (fixedWidthRoundedRadiusLogEnvelopeFrom hN ρ y0 n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  exact
    (integrable_of_mem_interior_integrableExpSet
      (zero_mem_interior_integrableExpSet_fixedWidthRoundedRadiusLogMultiplierFrom
        hA hN ρ y0 n)).norm.add
      (integrable_fixedWidthRoundedRadiusMultiplierFrom hA hN ρ y0 n)

/-- The common integrable envelope dominates every inverse-natural positive
shift used in `exists_affineEntrance_bound`. -/
lemma ae_norm_log_fixedWidthRoundedRadiusMultiplierFrom_add_inv_nat_le
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n k : ℕ) :
    ∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
      ‖Real.log
        (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω +
          ((k + 1 : ℕ) : ℝ)⁻¹)‖ ≤
        fixedWidthRoundedRadiusLogEnvelopeFrom hN ρ y0 n ω := by
  filter_upwards [
    ae_fixedWidthRoundedRadiusMultiplierFrom_pos hA hN ρ y0 n] with ω hω
  apply norm_log_add_le_norm_log_add_self hω
  · positivity
  · apply (inv_le_one₀
      (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ))).2
    norm_num

end AbsorptionCutoff
