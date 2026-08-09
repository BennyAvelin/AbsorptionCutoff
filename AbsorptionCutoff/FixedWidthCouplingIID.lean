/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingRadial

/-!
# Fixed-width iid coupling multipliers

This continuation module identifies the path-specific discrepancy multipliers
with independent copies of the common Gaussian radial law and owns the
subproduct and accumulated rounding estimates.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Every path-specific synchronous discrepancy multiplier has the common
fixed-width Gaussian radial law. -/
lemma map_fixedWidthDiscrepancyMultiplier
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (x0 : Fin N → ℝ) (n : ℕ) :
    Measure.map (fixedWidthDiscrepancyMultiplier hN ρ x0 n)
        (fixedWidthMatrixGaussianMeasure A N) =
      fixedWidthRadialMultiplierLaw A N := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let direction : fixedWidthMatrixSampleSpace N → (Fin N → ℝ) :=
    fun ω ↦ fixedWidthUnitDirection hN
      (fixedWidthVectorDiscrepancy ρ N x0 n ω)
  let current : fixedWidthMatrixSampleSpace N → (Fin N → Fin N → ℝ) :=
    fun ω ↦ ω n
  let ν := Measure.map direction μ
  let mulNorm :
      (Fin N → ℝ) × (Fin N → Fin N → ℝ) → ℝ :=
    fun p ↦ gaussianEuclideanNorm N (Matrix.mulVec p.2 p.1)
  have hdirection : Measurable direction :=
    (measurable_fixedWidthUnitDirection hN).comp
      (measurable_fixedWidthVectorDiscrepancy ρ N x0 n)
  have hcurrent : Measurable current := measurable_pi_apply n
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
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hdirection.aemeasurable
  have hν : ∀ᵐ θ ∂ν, gaussianEuclideanNorm N θ = 1 := by
    change ∀ᵐ θ ∂Measure.map direction μ,
      gaussianEuclideanNorm N θ = 1
    exact (ae_map_iff hdirection.aemeasurable
      ((measurableSet_singleton 1).preimage
        (measurable_gaussianEuclideanNorm N))).2
      (Eventually.of_forall fun ω ↦
        gaussianEuclideanNorm_fixedWidthUnitDirection hN
          (fixedWidthVectorDiscrepancy ρ N x0 n ω))
  have hcurrentMap : Measure.map current μ = gaussianMat A N := by
    dsimp [current, μ, fixedWidthMatrixGaussianMeasure]
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ gaussianMat A N) n).map_eq
  have hpair :
      Measure.map (fun ω ↦ (direction ω, current ω)) μ =
        ν.prod (gaussianMat A N) := by
    have hmap :=
      (indepFun_fixedWidthDiscrepancyDirection_eval
        A hN ρ x0 n).map_prod_eq_prod_map_map
          hdirection.aemeasurable hcurrent.aemeasurable
    change Measure.map (fun ω ↦ (direction ω, current ω)) μ =
      (Measure.map direction μ).prod (Measure.map current μ) at hmap
    rw [hcurrentMap] at hmap
    exact hmap
  change Measure.map
      (mulNorm ∘ fun ω ↦ (direction ω, current ω)) μ = _
  rw [← Measure.map_map hmulNorm (hdirection.prodMk hcurrent), hpair]
  exact map_gaussianEuclideanNorm_mulVec_prod_eq_radialMultiplierLaw
    A ν hν

/-- Vector of the first `n` synchronous discrepancy multipliers. -/
noncomputable def fixedWidthDiscrepancyMultiplierPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    fixedWidthMatrixSampleSpace N → (Fin n → ℝ) :=
  fun ω k ↦ fixedWidthDiscrepancyMultiplier hN ρ x0 k ω

lemma measurable_fixedWidthDiscrepancyMultiplierPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthDiscrepancyMultiplierPrefix hN ρ x0 n) :=
  measurable_pi_lambda _ fun k ↦
    measurable_fixedWidthDiscrepancyMultiplier hN ρ x0 k

/-- The first `n` multipliers as an explicit measurable function of the first
`n` matrix innovations. -/
noncomputable def fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    (Fin n → (Fin N → Fin N → ℝ)) → (Fin n → ℝ) :=
  fun u k ↦ fixedWidthDiscrepancyMultiplier hN ρ x0 k
    (fixedWidthExtendMatrixPrefix N n u)

lemma measurable_fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable
      (fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix hN ρ x0 n) :=
  measurable_pi_lambda _ fun k ↦
    (measurable_fixedWidthDiscrepancyMultiplier hN ρ x0 k).comp
      (measurable_fixedWidthExtendMatrixPrefix N n)

lemma fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix_apply
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix hN ρ x0 n
        (fixedWidthMatrixPrefix N n ω) =
      fixedWidthDiscrepancyMultiplierPrefix hN ρ x0 n ω := by
  funext k
  have hseq : ∀ j < n,
      fixedWidthExtendMatrixPrefix N n
          (fixedWidthMatrixPrefix N n ω) j = ω j := by
    intro j hj
    simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix, hj]
  unfold fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix
    fixedWidthDiscrepancyMultiplierPrefix
  unfold fixedWidthDiscrepancyMultiplier
  rw [hseq k k.isLt]
  rw [fixedWidthDiscrepancyDirection_eq_of_forall_lt hN ρ x0 k
    (fun j hj ↦ hseq j (lt_trans hj k.isLt))]

end AbsorptionCutoff
