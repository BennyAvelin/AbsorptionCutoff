/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingIID

/-!
# Fixed-width coupling multiplier subproducts

This continuation module proves the finite joint law and iid structure of the
adapted Gaussian radial multipliers, then derives the subproduct bounds and
accumulated rounding comparison used on logarithmic time horizons.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

instance (A : ℝ) (N : ℕ) :
    IsProbabilityMeasure (fixedWidthRadialMultiplierLaw A N) := by
  unfold fixedWidthRadialMultiplierLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_gaussianEuclideanNorm N).aemeasurable

/-- Retaining an arbitrary past mark while applying the fresh Gaussian radial
multiplier produces the product of the mark marginal and the common radial
law. -/
lemma map_mark_mulVec_prod_eq_prod_radialMultiplierLaw
    {E : Type*} [MeasurableSpace E]
    (A : ℝ) {N : ℕ} (ν : Measure (E × (Fin N → ℝ)))
    [IsProbabilityMeasure ν]
    (hν : ∀ᵐ p ∂ν, gaussianEuclideanNorm N p.2 = 1) :
    Measure.map
        (fun p : (E × (Fin N → ℝ)) × (Fin N → Fin N → ℝ) ↦
          (p.1.1, gaussianEuclideanNorm N (Matrix.mulVec p.2 p.1.2)))
        (ν.prod (gaussianMat A N)) =
      (Measure.map Prod.fst ν).prod
        (fixedWidthRadialMultiplierLaw A N) := by
  classical
  let markMul :
      (E × (Fin N → ℝ)) × (Fin N → Fin N → ℝ) → E × ℝ :=
    fun p ↦ (p.1.1,
      gaussianEuclideanNorm N (Matrix.mulVec p.2 p.1.2))
  have hmulVec : Measurable
      (fun p : (E × (Fin N → ℝ)) × (Fin N → Fin N → ℝ) ↦
        Matrix.mulVec p.2 p.1.2) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp
          (measurable_snd.comp measurable_fst))
  have hmarkMul : Measurable markMul :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_gaussianEuclideanNorm N).comp hmulVec)
  change Measure.map markMul (ν.prod (gaussianMat A N)) = _
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply hmarkMul (hs.prod ht),
    Measure.prod_apply ((hs.prod ht).preimage hmarkMul),
    Measure.prod_prod, Measure.map_apply measurable_fst hs]
  have hsections : ∀ᵐ p ∂ν,
      gaussianMat A N (Prod.mk p ⁻¹' (markMul ⁻¹' (s ×ˢ t))) =
        if p.1 ∈ s then fixedWidthRadialMultiplierLaw A N t else 0 := by
    filter_upwards [hν] with p hp
    have hfix : Measurable
        (fun W : Fin N → Fin N → ℝ ↦
          gaussianEuclideanNorm N (Matrix.mulVec W p.2)) := by
      apply (measurable_gaussianEuclideanNorm N).comp
      apply measurable_pi_iff.mpr
      intro i
      simp only [Matrix.mulVec, dotProduct]
      apply Finset.measurable_sum
      intro j _
      fun_prop
    by_cases hps : p.1 ∈ s
    · rw [show Prod.mk p ⁻¹' (markMul ⁻¹' (s ×ˢ t)) =
          (fun W : Fin N → Fin N → ℝ ↦
            gaussianEuclideanNorm N (Matrix.mulVec W p.2)) ⁻¹' t by
          ext W
          simp [markMul, hps]]
      rw [← Measure.map_apply hfix ht,
        map_gaussianEuclideanNorm_mulVec_gaussianMat_of_unit A p.2 hp,
        if_pos hps]
    · rw [show Prod.mk p ⁻¹' (markMul ⁻¹' (s ×ˢ t)) = ∅ by
          ext W
          simp [markMul, hps]]
      simp [hps]
  calc
    ∫⁻ p, gaussianMat A N
        (Prod.mk p ⁻¹' (markMul ⁻¹' (s ×ˢ t))) ∂ν =
        ∫⁻ p, if p.1 ∈ s then
          fixedWidthRadialMultiplierLaw A N t else 0 ∂ν :=
      lintegral_congr_ae hsections
    _ = ∫⁻ _p in Prod.fst ⁻¹' s,
        fixedWidthRadialMultiplierLaw A N t ∂ν := by
      rw [← lintegral_indicator (hs.preimage measurable_fst)]
      apply lintegral_congr
      intro p
      simp only [Set.indicator, Set.mem_preimage]
    _ = ν (Prod.fst ⁻¹' s) * fixedWidthRadialMultiplierLaw A N t := by
      rw [setLIntegral_const]
      exact mul_comm _ _

/-- The vector of the first `n` multipliers is independent of multiplier `n`.
This is the sequential independence statement behind the iid multiplier
process. -/
lemma indepFun_fixedWidthDiscrepancyMultiplierPrefix_next
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (x0 : Fin N → ℝ) (n : ℕ) :
    IndepFun
      (fixedWidthDiscrepancyMultiplierPrefix hN ρ x0 n)
      (fixedWidthDiscrepancyMultiplier hN ρ x0 n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let past := fixedWidthDiscrepancyMultiplierPrefix hN ρ x0 n
  let direction : fixedWidthMatrixSampleSpace N → (Fin N → ℝ) :=
    fun ω ↦ fixedWidthUnitDirection hN
      (fixedWidthVectorDiscrepancy ρ N x0 n ω)
  let current : fixedWidthMatrixSampleSpace N → (Fin N → Fin N → ℝ) :=
    fun ω ↦ ω n
  let pastDirectionFromPrefix :
      (Fin n → (Fin N → Fin N → ℝ)) →
        ((Fin n → ℝ) × (Fin N → ℝ)) :=
    fun u ↦
      (fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix hN ρ x0 n u,
        fixedWidthDiscrepancyDirectionFromPrefix hN ρ x0 n u)
  let ν := Measure.map (fun ω ↦ (past ω, direction ω)) μ
  let markMul :
      (((Fin n → ℝ) × (Fin N → ℝ)) × (Fin N → Fin N → ℝ)) →
        ((Fin n → ℝ) × ℝ) :=
    fun p ↦ (p.1.1,
      gaussianEuclideanNorm N (Matrix.mulVec p.2 p.1.2))
  have hpast : Measurable past :=
    measurable_fixedWidthDiscrepancyMultiplierPrefix hN ρ x0 n
  have hdirection : Measurable direction :=
    (measurable_fixedWidthUnitDirection hN).comp
      (measurable_fixedWidthVectorDiscrepancy ρ N x0 n)
  have hcurrent : Measurable current := measurable_pi_apply n
  have hpastDirectionFromPrefix : Measurable pastDirectionFromPrefix :=
    (measurable_fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix
      hN ρ x0 n).prodMk
        (measurable_fixedWidthDiscrepancyDirectionFromPrefix hN ρ x0 n)
  have hpastDirection_apply (ω : fixedWidthMatrixSampleSpace N) :
      pastDirectionFromPrefix (fixedWidthMatrixPrefix N n ω) =
        (past ω, direction ω) := by
    apply Prod.ext
    · exact fixedWidthDiscrepancyMultiplierPrefixFromMatrixPrefix_apply
        hN ρ x0 n ω
    · exact fixedWidthDiscrepancyDirectionFromPrefix_apply hN ρ x0 n ω
  have hindCurrent :
      IndepFun (fun ω ↦ (past ω, direction ω)) current μ := by
    have hcomp := (indepFun_fixedWidthMatrixPrefix_eval A N n).comp
      hpastDirectionFromPrefix measurable_id
    convert hcomp using 1
    · funext ω
      exact (hpastDirection_apply ω).symm
    · rfl
  have hcurrentMap : Measure.map current μ = gaussianMat A N := by
    dsimp [current, μ, fixedWidthMatrixGaussianMeasure]
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ gaussianMat A N) n).map_eq
  have hpair :
      Measure.map (fun ω ↦ ((past ω, direction ω), current ω)) μ =
        ν.prod (gaussianMat A N) := by
    have hmap := hindCurrent.map_prod_eq_prod_map_map
      (hpast.prodMk hdirection).aemeasurable hcurrent.aemeasurable
    change Measure.map (fun ω ↦ ((past ω, direction ω), current ω)) μ =
      (Measure.map (fun ω ↦ (past ω, direction ω)) μ).prod
        (Measure.map current μ) at hmap
    rw [hcurrentMap] at hmap
    exact hmap
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map
      (hpast.prodMk hdirection).aemeasurable
  have hν : ∀ᵐ p ∂ν, gaussianEuclideanNorm N p.2 = 1 := by
    change ∀ᵐ p ∂Measure.map (fun ω ↦ (past ω, direction ω)) μ,
      gaussianEuclideanNorm N p.2 = 1
    exact (ae_map_iff (hpast.prodMk hdirection).aemeasurable
      ((measurableSet_singleton 1).preimage
        ((measurable_gaussianEuclideanNorm N).comp measurable_snd))).2
      (Eventually.of_forall fun ω ↦
        gaussianEuclideanNorm_fixedWidthUnitDirection hN
          (fixedWidthVectorDiscrepancy ρ N x0 n ω))
  have hmulVec : Measurable
      (fun p : (((Fin n → ℝ) × (Fin N → ℝ)) ×
          (Fin N → Fin N → ℝ)) ↦ Matrix.mulVec p.2 p.1.2) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp
          (measurable_snd.comp measurable_fst))
  have hmarkMul : Measurable markMul :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_gaussianEuclideanNorm N).comp hmulVec)
  have hjoint :
      Measure.map
          (fun ω ↦
            (past ω, fixedWidthDiscrepancyMultiplier hN ρ x0 n ω)) μ =
        (Measure.map past μ).prod
          (fixedWidthRadialMultiplierLaw A N) := by
    have hmarked := map_mark_mulVec_prod_eq_prod_radialMultiplierLaw A ν hν
    have hmapped :
        Measure.map markMul
            (Measure.map
              (fun ω ↦ ((past ω, direction ω), current ω)) μ) =
          Measure.map markMul (ν.prod (gaussianMat A N)) := by
      rw [hpair]
    rw [Measure.map_map hmarkMul
      ((hpast.prodMk hdirection).prodMk hcurrent)] at hmapped
    have hleft :
        markMul ∘ (fun ω ↦ ((past ω, direction ω), current ω)) =
          fun ω ↦
            (past ω, fixedWidthDiscrepancyMultiplier hN ρ x0 n ω) := by
      funext ω
      rfl
    rw [hleft, hmarked] at hmapped
    have hfst :
        Measure.map Prod.fst ν = Measure.map past μ := by
      dsimp [ν]
      rw [Measure.map_map measurable_fst (hpast.prodMk hdirection)]
      rfl
    rw [hfst] at hmapped
    exact hmapped
  refine (indepFun_iff_map_prod_eq_prod_map_map
    hpast.aemeasurable
    (measurable_fixedWidthDiscrepancyMultiplier
      hN ρ x0 n).aemeasurable).2 ?_
  rw [map_fixedWidthDiscrepancyMultiplier A hN ρ x0 n]
  exact hjoint

end AbsorptionCutoff
