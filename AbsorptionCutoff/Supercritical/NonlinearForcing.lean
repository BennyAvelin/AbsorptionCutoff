/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.LogPolar
import AbsorptionCutoff.Supercritical.PolarPerturbationIntegral

/-!
# The nonlinear renewal forcing

This file begins A-8b, `def:nd-nonlinear-forcing` and
`prop:nd-forcing-admissibility` (tex L5137--5277).  It packages the nonlinear
and linearized indicator integrands on the product of the log-polar stationary
law and the Gaussian matrix law, then defines their exponentially tilted
difference `Ψ_y^π(φ)`.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The nonlinear summand in `eq:nd-forcing-definition`. -/
noncomputable def nonlinearForcingPlusIntegrand (N : ℕ) (y : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) : ℝ :=
  if y < (logPolarStep N q.1.1 q.1.2 q.2).1 then
    φ (logPolarStep N q.1.1 q.1.2 q.2).2
  else 0

/-- The linearized summand in `eq:nd-forcing-definition`. -/
noncomputable def nonlinearForcingZeroIntegrand (N : ℕ) (y : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) : ℝ :=
  let v := Matrix.mulVec q.2 (WithLp.ofLp q.1.2)
  if y < q.1.1 - Real.log (gaussianEuclideanNorm N v) then
    φ (angularZero N v)
  else 0

lemma measurable_nonlinearForcingPlusIntegrand (N : ℕ) (y : ℝ)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ) :
    Measurable (nonlinearForcingPlusIntegrand N y φ) := by
  unfold nonlinearForcingPlusIntegrand
  exact Measurable.ite
    (measurableSet_lt measurable_const (measurable_logPolarStep_fst N))
    (hφ.comp (measurable_logPolarStep_snd N)) measurable_const

lemma measurable_nonlinearForcingZeroIntegrand (N : ℕ) (y : ℝ)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ) :
    Measurable (nonlinearForcingZeroIntegrand N y φ) := by
  unfold nonlinearForcingZeroIntegrand
  have hv : Measurable fun q :
      (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      Matrix.mulVec q.2 (WithLp.ofLp q.1.2) :=
    (measurable_mulVec_ofLp N).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  exact Measurable.ite
    (measurableSet_lt measurable_const ((measurable_fst.comp measurable_fst).sub
      ((measurable_gaussianEuclideanNorm N).comp hv).log))
    (hφ.comp ((measurable_angularZero N).comp hv)) measurable_const

lemma abs_nonlinearForcingPlusIntegrand_le (N : ℕ) (y C : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) (hφ : ∀ θ, |φ θ| ≤ C) (q) :
    |nonlinearForcingPlusIntegrand N y φ q| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφ 0)
  simp only [nonlinearForcingPlusIntegrand]
  split <;> simp_all

lemma abs_nonlinearForcingZeroIntegrand_le (N : ℕ) (y C : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) (hφ : ∀ θ, |φ θ| ≤ C) (q) :
    |nonlinearForcingZeroIntegrand N y φ q| ≤ C := by
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφ 0)
  simp only [nonlinearForcingZeroIntegrand]
  split <;> simp_all

lemma integrable_nonlinearForcingPlusIntegrand (A : ℝ) (N : ℕ)
    {π : Measure (Fin N → ℝ)} [IsProbabilityMeasure π] (y C : ℝ)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφm : Measurable φ)
    (hφ : ∀ θ, |φ θ| ≤ C) :
    Integrable (nonlinearForcingPlusIntegrand N y φ)
      ((logPolarLaw N π).prod (gaussianMat A N)) := by
  refine Integrable.mono' (integrable_const C)
    (measurable_nonlinearForcingPlusIntegrand N y hφm).aestronglyMeasurable ?_
  filter_upwards with q
  simpa [Real.norm_eq_abs] using abs_nonlinearForcingPlusIntegrand_le N y C φ hφ q

lemma integrable_nonlinearForcingZeroIntegrand (A : ℝ) (N : ℕ)
    {π : Measure (Fin N → ℝ)} [IsProbabilityMeasure π] (y C : ℝ)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφm : Measurable φ)
    (hφ : ∀ θ, |φ θ| ≤ C) :
    Integrable (nonlinearForcingZeroIntegrand N y φ)
      ((logPolarLaw N π).prod (gaussianMat A N)) := by
  refine Integrable.mono' (integrable_const C)
    (measurable_nonlinearForcingZeroIntegrand N y hφm).aestronglyMeasurable ?_
  filter_upwards with q
  simpa [Real.norm_eq_abs] using abs_nonlinearForcingZeroIntegrand_le N y C φ hφ q

/-- The scalar nonlinear renewal forcing `Ψ_y^π(φ)` of
`eq:nd-forcing-definition`. -/
noncomputable def nonlinearForcing (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ))
    (β y : ℝ) (φ : EuclideanSpace ℝ (Fin N) → ℝ) : ℝ :=
  Real.exp (β * y) *
    (∫ q, nonlinearForcingPlusIntegrand N y φ q
        ∂(logPolarLaw N π).prod (gaussianMat A N) -
      ∫ q, nonlinearForcingZeroIntegrand N y φ q
        ∂(logPolarLaw N π).prod (gaussianMat A N))

/-- The elementary bounded-functional estimate asserted immediately after
`eq:nd-forcing-definition`. -/
theorem abs_nonlinearForcing_le (A : ℝ) (N : ℕ)
    {π : Measure (Fin N → ℝ)} [IsProbabilityMeasure π]
    (β y C : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : ∀ θ, |φ θ| ≤ C) :
    |nonlinearForcing A N π β y φ| ≤ 2 * Real.exp (β * y) * C := by
  have hp : |∫ q, nonlinearForcingPlusIntegrand N y φ q
      ∂(logPolarLaw N π).prod (gaussianMat A N)| ≤ C := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const
        (μ := (logPolarLaw N π).prod (gaussianMat A N))
        (f := nonlinearForcingPlusIntegrand N y φ) (C := C)
        (Filter.Eventually.of_forall fun q => by
          simpa [Real.norm_eq_abs] using
            (abs_nonlinearForcingPlusIntegrand_le N y C φ hφ q)))
  have hz : |∫ q, nonlinearForcingZeroIntegrand N y φ q
      ∂(logPolarLaw N π).prod (gaussianMat A N)| ≤ C := by
    simpa [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const
        (μ := (logPolarLaw N π).prod (gaussianMat A N))
        (f := nonlinearForcingZeroIntegrand N y φ) (C := C)
        (Filter.Eventually.of_forall fun q => by
          simpa [Real.norm_eq_abs] using
            (abs_nonlinearForcingZeroIntegrand_le N y C φ hφ q)))
  rw [nonlinearForcing, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (β * y) *
        |(∫ q, nonlinearForcingPlusIntegrand N y φ q
            ∂(logPolarLaw N π).prod (gaussianMat A N)) -
          ∫ q, nonlinearForcingZeroIntegrand N y φ q
            ∂(logPolarLaw N π).prod (gaussianMat A N)|
      ≤ Real.exp (β * y) * (C + C) := by
        gcongr
        exact (abs_sub _ _).trans (add_le_add hp hz)
    _ = 2 * Real.exp (β * y) * C := by ring

lemma nonlinearForcingPlusIntegrand_add (N : ℕ) (y : ℝ)
    (φ ψ : EuclideanSpace ℝ (Fin N) → ℝ) (q) :
    nonlinearForcingPlusIntegrand N y (fun θ => φ θ + ψ θ) q =
      nonlinearForcingPlusIntegrand N y φ q + nonlinearForcingPlusIntegrand N y ψ q := by
  simp only [nonlinearForcingPlusIntegrand]
  split <;> simp_all

lemma nonlinearForcingZeroIntegrand_add (N : ℕ) (y : ℝ)
    (φ ψ : EuclideanSpace ℝ (Fin N) → ℝ) (q) :
    nonlinearForcingZeroIntegrand N y (fun θ => φ θ + ψ θ) q =
      nonlinearForcingZeroIntegrand N y φ q + nonlinearForcingZeroIntegrand N y ψ q := by
  simp only [nonlinearForcingZeroIntegrand]
  split <;> simp_all

lemma nonlinearForcingPlusIntegrand_smul (N : ℕ) (y a : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) (q) :
    nonlinearForcingPlusIntegrand N y (fun θ => a * φ θ) q =
      a * nonlinearForcingPlusIntegrand N y φ q := by
  simp only [nonlinearForcingPlusIntegrand]
  split <;> simp_all

lemma nonlinearForcingZeroIntegrand_smul (N : ℕ) (y a : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) (q) :
    nonlinearForcingZeroIntegrand N y (fun θ => a * φ θ) q =
      a * nonlinearForcingZeroIntegrand N y φ q := by
  simp only [nonlinearForcingZeroIntegrand]
  split <;> simp_all

theorem nonlinearForcing_add (A : ℝ) (N : ℕ)
    {π : Measure (Fin N → ℝ)} [IsProbabilityMeasure π] (β y C D : ℝ)
    {φ ψ : EuclideanSpace ℝ (Fin N) → ℝ} (hφm : Measurable φ) (hψm : Measurable ψ)
    (hφ : ∀ θ, |φ θ| ≤ C) (hψ : ∀ θ, |ψ θ| ≤ D) :
    nonlinearForcing A N π β y (fun θ => φ θ + ψ θ) =
      nonlinearForcing A N π β y φ + nonlinearForcing A N π β y ψ := by
  have hpφ := integrable_nonlinearForcingPlusIntegrand A N (π := π) y C hφm hφ
  have hpψ := integrable_nonlinearForcingPlusIntegrand A N (π := π) y D hψm hψ
  have hzφ := integrable_nonlinearForcingZeroIntegrand A N (π := π) y C hφm hφ
  have hzψ := integrable_nonlinearForcingZeroIntegrand A N (π := π) y D hψm hψ
  unfold nonlinearForcing
  simp_rw [nonlinearForcingPlusIntegrand_add, nonlinearForcingZeroIntegrand_add,
    integral_add hpφ hpψ, integral_add hzφ hzψ]
  ring

theorem nonlinearForcing_smul (A : ℝ) (N : ℕ)
    {π : Measure (Fin N → ℝ)} [IsProbabilityMeasure π] (β y a : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) :
    nonlinearForcing A N π β y (fun θ => a * φ θ) =
      a * nonlinearForcing A N π β y φ := by
  unfold nonlinearForcing
  simp_rw [nonlinearForcingPlusIntegrand_smul, nonlinearForcingZeroIntegrand_smul,
    integral_const_mul]
  ring

/-- The measurable-set discrepancies defining `tvDist` are bounded for any
pair of finite measures. The existing project lemma only states this for
probability measures. -/
lemma tvDist_bddAbove_of_isFiniteMeasure {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    BddAbove (Set.range fun s : {s : Set E // MeasurableSet s} =>
      |(μ s.1).toReal - (ν s.1).toReal|) := by
  refine ⟨(μ Set.univ).toReal + (ν Set.univ).toReal, ?_⟩
  rintro _ ⟨s, rfl⟩
  calc
    |(μ s.1).toReal - (ν s.1).toReal|
        ≤ |(μ s.1).toReal| + |(ν s.1).toReal| := abs_sub _ _
    _ = (μ s.1).toReal + (ν s.1).toReal := by
      rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ (μ Set.univ).toReal + (ν Set.univ).toReal := by
      exact add_le_add
        (ENNReal.toReal_mono (measure_ne_top μ Set.univ)
          (measure_mono (Set.subset_univ _)))
        (ENNReal.toReal_mono (measure_ne_top ν Set.univ)
          (measure_mono (Set.subset_univ _)))

/-- The one-sided `[0,1]` bounded-test inequality for finite measures. This is
the finite-measure counterpart of `integral_sub_le_tvDist`. -/
lemma integral_sub_le_tvDist_of_isFiniteMeasure {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : E → ℝ) (hf : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) :
    (∫ x, f x ∂μ) - ∫ x, f x ∂ν ≤ tvDist μ ν := by
  have hf_int_μ : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
        exact hf_le_one x)
  have hf_int_ν : Integrable f ν :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
        exact hf_le_one x)
  have hset (ξ ζ : Measure E) [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
      (s : Set E) (hs : MeasurableSet s) :
      |(ξ s).toReal - (ζ s).toReal| ≤ tvDist ξ ζ := by
    unfold tvDist
    exact le_ciSup (tvDist_bddAbove_of_isFiniteMeasure ξ ζ) ⟨s, hs⟩
  have htail_meas (ξ : Measure E) :
      Measurable fun t : ℝ => ξ.real {x | t ≤ f x} :=
    Measurable.ennreal_toReal <| Antitone.measurable fun _ _ hst =>
      measure_mono fun _ hx => hst.trans hx
  have htail_int (ξ : Measure E) [IsFiniteMeasure ξ] :
      IntegrableOn (fun t : ℝ => ξ.real {x | t ≤ f x}) (Set.Ioc 0 1) := by
    apply (integrableOn_const (C := (ξ Set.univ).toReal)
      (by simp [Real.volume_Ioc])).mono'
      (htail_meas ξ).aestronglyMeasurable.restrict
    filter_upwards [] with t
    rw [measureReal_def, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono (measure_ne_top ξ Set.univ)
      (measure_mono (Set.subset_univ _))
  rw [hf_int_μ.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hf_nonneg) (Filter.Eventually.of_forall hf_le_one),
    hf_int_ν.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hf_nonneg) (Filter.Eventually.of_forall hf_le_one),
    ← integral_sub (htail_int μ) (htail_int ν)]
  calc
    (∫ t in Set.Ioc 0 1,
        μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x})
        ≤ ∫ (_t : ℝ) in Set.Ioc 0 1, tvDist μ ν := by
          apply integral_mono_ae
          · exact (htail_int μ).sub (htail_int ν)
          · exact integrableOn_const (by simp [Real.volume_Ioc])
          · filter_upwards [] with t
            exact le_trans (le_abs_self _)
              (hset μ ν _ (hf measurableSet_Ici))
    _ = tvDist μ ν := by
      rw [setIntegral_const, Real.volume_real_Ioc]
      norm_num

/-- A measurable `[-1,1]`-valued test separates two finite measures by at most
twice their setwise total-variation distance. -/
lemma abs_integral_sub_le_two_mul_tvDist_of_isFiniteMeasure
    {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : E → ℝ) (hf : Measurable f) (habs : ∀ x, |f x| ≤ 1) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 2 * tvDist μ ν := by
  let fp : E → ℝ := fun x => max (f x) 0
  let fn : E → ℝ := fun x => max (-f x) 0
  have hfp : Measurable fp := hf.max measurable_const
  have hfn : Measurable fn := hf.neg.max measurable_const
  have hfp0 : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfn0 : ∀ x, 0 ≤ fn x := fun x => le_max_right _ _
  have hfp1 : ∀ x, fp x ≤ 1 := fun x => by
    exact max_le (le_trans (le_abs_self _) (habs x)) zero_le_one
  have hfn1 : ∀ x, fn x ≤ 1 := fun x => by
    exact max_le (le_trans (neg_le_abs _) (habs x)) zero_le_one
  have hfpμ : Integrable fp μ :=
    (integrable_const (1 : ℝ)).mono' hfp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfp0 x)]
        exact hfp1 x)
  have hfnμ : Integrable fn μ :=
    (integrable_const (1 : ℝ)).mono' hfn.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfn0 x)]
        exact hfn1 x)
  have hfpν : Integrable fp ν :=
    (integrable_const (1 : ℝ)).mono' hfp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfp0 x)]
        exact hfp1 x)
  have hfnν : Integrable fn ν :=
    (integrable_const (1 : ℝ)).mono' hfn.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfn0 x)]
        exact hfn1 x)
  have hdecomp : ∀ x, f x = fp x - fn x := by
    intro x
    by_cases hx : 0 ≤ f x
    · rw [show fp x = f x by simp [fp, hx],
          show fn x = 0 by simp [fn, hx]]
      ring
    · have hx' : f x ≤ 0 := le_of_not_ge hx
      rw [show fp x = 0 by simp [fp, hx'],
          show fn x = -f x by simp [fn, hx']]
      ring
  have hμ : (∫ x, f x ∂μ) = (∫ x, fp x ∂μ) - ∫ x, fn x ∂μ := by
    simp_rw [hdecomp]
    exact integral_sub hfpμ hfnμ
  have hν : (∫ x, f x ∂ν) = (∫ x, fp x ∂ν) - ∫ x, fn x ∂ν := by
    simp_rw [hdecomp]
    exact integral_sub hfpν hfnν
  have hp_le := integral_sub_le_tvDist_of_isFiniteMeasure μ ν fp hfp hfp0 hfp1
  have hp_ge := integral_sub_le_tvDist_of_isFiniteMeasure ν μ fp hfp hfp0 hfp1
  have hn_le := integral_sub_le_tvDist_of_isFiniteMeasure μ ν fn hfn hfn0 hfn1
  have hn_ge := integral_sub_le_tvDist_of_isFiniteMeasure ν μ fn hfn hfn0 hfn1
  have hpabs : |(∫ x, fp x ∂μ) - ∫ x, fp x ∂ν| ≤ tvDist μ ν := by
    rw [abs_le]
    constructor
    · rw [tvDist_comm] at hp_ge
      linarith
    · exact hp_le
  have hnabs : |(∫ x, fn x ∂μ) - ∫ x, fn x ∂ν| ≤ tvDist μ ν := by
    rw [abs_le]
    constructor
    · rw [tvDist_comm] at hn_ge
      linarith
    · exact hn_le
  rw [hμ, hν]
  calc
    |((∫ x, fp x ∂μ) - ∫ x, fn x ∂μ) -
        ((∫ x, fp x ∂ν) - ∫ x, fn x ∂ν)|
      = |((∫ x, fp x ∂μ) - ∫ x, fp x ∂ν) -
          ((∫ x, fn x ∂μ) - ∫ x, fn x ∂ν)| := by ring_nf
    _ ≤ |(∫ x, fp x ∂μ) - ∫ x, fp x ∂ν| +
        |(∫ x, fn x ∂μ) - ∫ x, fn x ∂ν| := abs_sub _ _
    _ ≤ tvDist μ ν + tvDist μ ν := add_le_add hpabs hnabs
    _ = 2 * tvDist μ ν := by ring

/-! ### Shift to the polar-perturbation variables -/

/-- Gaussian isotropy at a unit direction: multiplying the Gaussian weight
matrix by `θ` gives independent centered coordinates of variance `A² / N`.
This is the probabilistic input used in `prop:nd-forcing-admissibility`. -/
lemma map_mulVec_gaussianMat_of_norm_eq_one (A : ℝ) {N : ℕ}
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1) :
    (gaussianMat A N).map
        (fun (W : Fin N → Fin N → ℝ) i => ∑ j, W i j * WithLp.ofLp θ j) =
      Measure.pi (fun _ : Fin N => gaussianReal 0 ((A ^ 2 / N).toNNReal)) := by
  rw [map_rowMap_gaussianMat]
  have hnorm : gaussianEuclideanNorm N (WithLp.ofLp θ) = 1 := by
    rw [gaussianEuclideanNorm_eq_norm]
    simpa using hθ
  have hsum : ∑ j, (WithLp.ofLp θ j) ^ 2 = 1 := by
    have hsqrt : Real.sqrt (∑ j, (WithLp.ofLp θ j) ^ 2) = 1 := by
      simpa [gaussianEuclideanNorm, gaussianSquaredNorm] using hnorm
    have hnonneg : 0 ≤ ∑ j, (WithLp.ofLp θ j) ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnonneg]
  congr 1
  funext i
  congr 1
  unfold radiusSq
  rw [hsum]
  field_simp

/-- The product Gaussian law as the Lebesgue density used in the polar
perturbation estimate. -/
theorem pi_gaussianReal_eq_withDensity {N : ℕ} {σ2 : NNReal} (hσ : σ2 ≠ 0) :
    Measure.pi (fun _ : Fin N => gaussianReal 0 σ2) =
      (volume : Measure (Fin N → ℝ)).withDensity
        (fun v => ∏ i, gaussianPDF 0 σ2 (v i)) := by
  haveI : IsProbabilityMeasure
      ((volume : Measure ℝ).withDensity (gaussianPDF 0 σ2)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hσ]
    infer_instance
  simp_rw [gaussianReal_of_var_ne_zero 0 hσ]
  exact pi_withDensity_volume (measurable_gaussianPDF 0 σ2)

/-- The coordinatewise `T_r` pushforward of the product Gaussian is the polar
density `p_r` used by the perturbation estimate. -/
theorem map_tanhScaleVec_pi_gaussianReal_eq_withDensity {N : ℕ} {σ2 : NNReal}
    (hσ : σ2 ≠ 0) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i))
        (Measure.pi (fun _ : Fin N => gaussianReal 0 σ2)) =
      (volume : Measure (Fin N → ℝ)).withDensity
        (fun v => ENNReal.ofReal (polarDensityReal N σ2 r v)) := by
  haveI : IsProbabilityMeasure
      ((volume : Measure ℝ).withDensity (gaussianPDF 0 σ2)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hσ]
    infer_instance
  simp_rw [gaussianReal_of_var_ne_zero 0 hσ]
  rw [map_tanhScaleVec_withDensity hr (measurable_gaussianPDF 0 σ2)]
  congr 1
  funext v
  exact (ofReal_polarDensityReal hr v).symm

/-- The norm-ball form arising from the log threshold is the squared-radius
ball form used by the polar perturbation theorem. -/
lemma set_gaussianEuclideanNorm_lt_exp_eq (N : ℕ) (t : ℝ) :
    {v : Fin N → ℝ | gaussianEuclideanNorm N v < Real.exp (-t)} =
      {v : Fin N → ℝ | ∑ i, v i ^ 2 < Real.exp (-t) ^ 2} := by
  ext v
  simp only [Set.mem_setOf_eq]
  unfold gaussianEuclideanNorm gaussianSquaredNorm
  exact Real.sqrt_lt' (Real.exp_pos (-t))

/-- Nonlinear fixed-state contribution after the paper's substitutions
`r = exp (-Y)` and `t = y - Y`. -/
noncomputable def nonlinearForcingPlusFiber (N : ℕ) (r t : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) (v : Fin N → ℝ) : ℝ :=
  if t < -Real.log (gaussianEuclideanNorm N v) + etaDefect N r v then
    φ (angularPlus N r v)
  else 0

/-- Linearized fixed-state contribution in the shifted variable `t = y-Y`. -/
noncomputable def nonlinearForcingZeroFiber (N : ℕ) (t : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) (v : Fin N → ℝ) : ℝ :=
  if t < -Real.log (gaussianEuclideanNorm N v) then φ (angularZero N v) else 0

/-- Away from the null vector, the linearized fiber is the angular test
function restricted to the ball of radius `exp (-t)`. -/
lemma nonlinearForcingZeroFiber_eq_ball (N : ℕ) (t : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) {v : Fin N → ℝ} (hv : v ≠ 0) :
    nonlinearForcingZeroFiber N t φ v =
      if gaussianEuclideanNorm N v < Real.exp (-t) then φ (angular N v) else 0 := by
  have hvn : gaussianEuclideanNorm N v ≠ 0 := by
    intro h
    exact hv ((gaussianEuclideanNorm_eq_zero_iff N v).1 h)
  have hvpos : 0 < gaussianEuclideanNorm N v :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity) (Ne.symm hvn)
  have hball : t < -Real.log (gaussianEuclideanNorm N v) ↔
      gaussianEuclideanNorm N v < Real.exp (-t) := by
    constructor
    · intro h
      exact (Real.log_lt_iff_lt_exp hvpos).1 (by linarith)
    · intro h
      have := (Real.log_lt_iff_lt_exp hvpos).2 h
      linarith
  simp only [nonlinearForcingZeroFiber, angularZero, hball]

/-- Away from the null vector, the nonlinear fixed-state fiber is the angular
test function after the paper's substitution `T_r`, restricted to the ball of
radius `exp (-t)`. -/
lemma nonlinearForcingPlusFiber_eq_tanhScale (N : ℕ) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) {v : Fin N → ℝ} (hv : v ≠ 0) :
    nonlinearForcingPlusFiber N r t φ v =
      if gaussianEuclideanNorm N (fun i => tanhScale r (v i)) < Real.exp (-t) then
        φ (angular N (fun i => tanhScale r (v i)))
      else 0 := by
  let u : Fin N → ℝ := fun i => tanhScale r (v i)
  have htanh : tanhVec N (r • v) = r • u := by
    funext i
    simp only [tanhVec, Pi.smul_apply, smul_eq_mul, u, tanhScale]
    field_simp
  have hvn : gaussianEuclideanNorm N v ≠ 0 := by
    intro h
    exact hv ((gaussianEuclideanNorm_eq_zero_iff N v).1 h)
  have htn : tanhVec N (r • v) ≠ 0 := by
    intro h
    have hsmul : r • v = 0 := (tanhVec_eq_zero_iff N (r • v)).1 h
    exact (not_or_intro hr.ne' hv) (smul_eq_zero.mp hsmul)
  have hun : gaussianEuclideanNorm N u ≠ 0 := by
    intro hu
    apply htn
    rw [htanh, (gaussianEuclideanNorm_eq_zero_iff N _).1 hu, smul_zero]
  have hupos : 0 < gaussianEuclideanNorm N u :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity) (Ne.symm hun)
  have hthreshold :
      -Real.log (gaussianEuclideanNorm N v) + etaDefect N r v =
        -Real.log (gaussianEuclideanNorm N u) := by
    rw [etaDefect, htanh, gaussianEuclideanNorm_smul, abs_of_pos hr]
    have hratio :
        r * gaussianEuclideanNorm N v / (r * gaussianEuclideanNorm N u) =
          gaussianEuclideanNorm N v / gaussianEuclideanNorm N u := by
      field_simp
    rw [hratio, Real.log_div hvn hun]
    ring
  have hangular : angularPlus N r v = angular N u := by
    rw [angularPlus, htanh, angular, gaussianEuclideanNorm_smul, abs_of_pos hr]
    simp only [WithLp.toLp_smul, smul_smul]
    congr 1
    field_simp
  have hball :
      t < -Real.log (gaussianEuclideanNorm N u) ↔
        gaussianEuclideanNorm N u < Real.exp (-t) := by
    constructor
    · intro h
      exact (Real.log_lt_iff_lt_exp hupos).1 (by linarith)
    · intro h
      have := (Real.log_lt_iff_lt_exp hupos).2 h
      linarith
  simp only [nonlinearForcingPlusFiber, hthreshold, hangular, u, hball]

/-- At a unit direction, the nonlinear fixed-state fiber integrates against
the angular projection of the `T_r`-transformed product Gaussian restricted to
the ball of radius `exp (-t)`. -/
theorem integral_nonlinearForcingPlusFiber_mulVec_gaussianMat (A : ℝ) {N : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ) :
    (∫ W, nonlinearForcingPlusFiber N r t φ
        (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N) =
      ∫ z, φ z ∂Measure.map (angular N)
        ((Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i))
          (Measure.pi (fun _ : Fin N =>
            gaussianReal 0 ((A ^ 2 / N).toNNReal)))).restrict
              {u | gaussianEuclideanNorm N u < Real.exp (-t)}) := by
  let mulTheta : (Fin N → Fin N → ℝ) → (Fin N → ℝ) :=
    fun W i => ∑ j, W i j * WithLp.ofLp θ j
  let scaleVec : (Fin N → ℝ) → (Fin N → ℝ) := fun v i => tanhScale r (v i)
  let ν : Measure (Fin N → ℝ) :=
    Measure.pi (fun _ : Fin N => gaussianReal 0 ((A ^ 2 / N).toNNReal))
  let ball : Set (Fin N → ℝ) := {u | gaussianEuclideanNorm N u < Real.exp (-t)}
  let rhs : (Fin N → ℝ) → ℝ := fun v =>
    if scaleVec v ∈ ball then φ (angular N (scaleVec v)) else 0
  have hmul : Measurable mulTheta := by
    exact measurable_pi_iff.mpr fun i =>
      Finset.measurable_sum _ fun j _ => by fun_prop
  have hscale : Measurable scaleVec :=
    measurable_pi_iff.mpr fun i => (measurable_tanhScale r).comp (measurable_pi_apply i)
  have hball : MeasurableSet ball :=
    measurableSet_lt (measurable_gaussianEuclideanNorm N) measurable_const
  have hang : Measurable (angular N) := measurable_angular N
  have hrhs : Measurable rhs := by
    exact Measurable.ite (hball.preimage hscale)
      (hφ.comp (hang.comp hscale)) measurable_const
  have hmap : Measure.map mulTheta (gaussianMat A N) = ν :=
    map_mulVec_gaussianMat_of_norm_eq_one A θ hθ
  have hθraw : WithLp.ofLp θ ≠ (0 : Fin N → ℝ) := by
    intro hz
    have hnorm : gaussianEuclideanNorm N (WithLp.ofLp θ) = 1 := by
      rw [gaussianEuclideanNorm_eq_norm]
      simpa using hθ
    have hzero := (gaussianEuclideanNorm_eq_zero_iff N (WithLp.ofLp θ)).2 hz
    linarith
  have hmulzero : gaussianMat A N {W | mulTheta W = 0} = 0 := by
    change gaussianMat A N {W | Matrix.mulVec W (WithLp.ofLp θ) = 0} = 0
    exact gaussianMat_mulVec_eq_zero hA hN hθraw
  have haeW : ∀ᵐ W ∂gaussianMat A N, mulTheta W ≠ 0 := by
    rw [ae_iff]
    simpa using hmulzero
  change (∫ W, nonlinearForcingPlusFiber N r t φ (mulTheta W) ∂gaussianMat A N) = _
  calc
    _ = ∫ W, rhs (mulTheta W) ∂gaussianMat A N := by
      apply integral_congr_ae
      filter_upwards [haeW] with W hW
      rw [nonlinearForcingPlusFiber_eq_tanhScale N hr t φ hW]
      rfl
    _ = ∫ v, rhs v ∂ν := by
      rw [← hmap, integral_map hmul.aemeasurable hrhs.aestronglyMeasurable]
    _ = ∫ z, φ z ∂Measure.map (angular N)
        ((Measure.map scaleVec ν).restrict ball) := by
      rw [integral_map hang.aemeasurable hφ.aestronglyMeasurable]
      rw [← integral_indicator hball]
      rw [integral_map (φ := scaleVec) hscale.aemeasurable
        (f := fun x => ball.indicator (fun x => φ (angular N x)) x)
        ((hφ.comp hang).indicator hball).aestronglyMeasurable]
      rfl

/-- The nonlinear fiber identity in the exact density form consumed by
`exists_gaussianPolarPerturbation_bound`. -/
theorem integral_nonlinearForcingPlusFiber_eq_polarDensity (A : ℝ) {N : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hσ : (A ^ 2 / N).toNNReal ≠ 0)
    {r : ℝ} (hr : 0 < r) (t : ℝ)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ) :
    (∫ W, nonlinearForcingPlusFiber N r t φ
        (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N) =
      ∫ z, φ z ∂Measure.map (angular N)
        (((volume : Measure (Fin N → ℝ)).withDensity
          (fun v => ENNReal.ofReal
            (polarDensityReal N ((A ^ 2 / N).toNNReal) r v))).restrict
              {v | gaussianEuclideanNorm N v < Real.exp (-t)}) := by
  rw [← map_tanhScaleVec_pi_gaussianReal_eq_withDensity hσ hr]
  exact integral_nonlinearForcingPlusFiber_mulVec_gaussianMat
    A hA hN hr t θ hθ hφ

/-- At a unit direction, the linearized fixed-state fiber integrates against
the angular projection of the product Gaussian restricted to the ball of
radius `exp (-t)`. -/
theorem integral_nonlinearForcingZeroFiber_mulVec_gaussianMat (A : ℝ) {N : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (t : ℝ)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ) :
    (∫ W, nonlinearForcingZeroFiber N t φ
        (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N) =
      ∫ z, φ z ∂Measure.map (angular N)
        ((Measure.pi (fun _ : Fin N =>
          gaussianReal 0 ((A ^ 2 / N).toNNReal))).restrict
            {v | gaussianEuclideanNorm N v < Real.exp (-t)}) := by
  let mulTheta : (Fin N → Fin N → ℝ) → (Fin N → ℝ) :=
    fun W i => ∑ j, W i j * WithLp.ofLp θ j
  let ν : Measure (Fin N → ℝ) :=
    Measure.pi (fun _ : Fin N => gaussianReal 0 ((A ^ 2 / N).toNNReal))
  let ball : Set (Fin N → ℝ) := {v | gaussianEuclideanNorm N v < Real.exp (-t)}
  let rhs : (Fin N → ℝ) → ℝ := fun v => if v ∈ ball then φ (angular N v) else 0
  have hmul : Measurable mulTheta := by
    exact measurable_pi_iff.mpr fun i =>
      Finset.measurable_sum _ fun j _ => by fun_prop
  have hball : MeasurableSet ball :=
    measurableSet_lt (measurable_gaussianEuclideanNorm N) measurable_const
  have hang : Measurable (angular N) := measurable_angular N
  have hrhs : Measurable rhs :=
    Measurable.ite hball (hφ.comp hang) measurable_const
  have hmap : Measure.map mulTheta (gaussianMat A N) = ν :=
    map_mulVec_gaussianMat_of_norm_eq_one A θ hθ
  have hθraw : WithLp.ofLp θ ≠ (0 : Fin N → ℝ) := by
    intro hz
    have hnorm : gaussianEuclideanNorm N (WithLp.ofLp θ) = 1 := by
      rw [gaussianEuclideanNorm_eq_norm]
      simpa using hθ
    have hzero := (gaussianEuclideanNorm_eq_zero_iff N (WithLp.ofLp θ)).2 hz
    linarith
  have hmulzero : gaussianMat A N {W | mulTheta W = 0} = 0 := by
    change gaussianMat A N {W | Matrix.mulVec W (WithLp.ofLp θ) = 0} = 0
    exact gaussianMat_mulVec_eq_zero hA hN hθraw
  have haeW : ∀ᵐ W ∂gaussianMat A N, mulTheta W ≠ 0 := by
    rw [ae_iff]
    simpa using hmulzero
  change (∫ W, nonlinearForcingZeroFiber N t φ (mulTheta W) ∂gaussianMat A N) = _
  calc
    _ = ∫ W, rhs (mulTheta W) ∂gaussianMat A N := by
      apply integral_congr_ae
      filter_upwards [haeW] with W hW
      rw [nonlinearForcingZeroFiber_eq_ball N t φ hW]
      rfl
    _ = ∫ v, rhs v ∂ν := by
      rw [← hmap, integral_map hmul.aemeasurable hrhs.aestronglyMeasurable]
    _ = ∫ z, φ z ∂Measure.map (angular N) (ν.restrict ball) := by
      rw [integral_map hang.aemeasurable hφ.aestronglyMeasurable]
      rw [← integral_indicator hball]
      rfl

/-- The linearized fiber identity in the exact density form consumed by
`exists_gaussianPolarPerturbation_bound`. -/
theorem integral_nonlinearForcingZeroFiber_eq_gaussianDensity (A : ℝ) {N : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hσ : (A ^ 2 / N).toNNReal ≠ 0) (t : ℝ)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ) :
    (∫ W, nonlinearForcingZeroFiber N t φ
        (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N) =
      ∫ z, φ z ∂Measure.map (angular N)
        (((volume : Measure (Fin N → ℝ)).withDensity
          (fun v => ENNReal.ofReal
            (∏ i, gaussianPDFReal 0 ((A ^ 2 / N).toNNReal) (v i)))).restrict
              {v | gaussianEuclideanNorm N v < Real.exp (-t)}) := by
  have hdens :
      (fun v : Fin N → ℝ => ∏ i, gaussianPDF 0 ((A ^ 2 / N).toNNReal) (v i)) =
        fun v => ENNReal.ofReal
          (∏ i, gaussianPDFReal 0 ((A ^ 2 / N).toNNReal) (v i)) := by
    funext v
    rw [gaussianPDF_def]
    exact (ENNReal.ofReal_prod_of_nonneg fun i _ =>
      gaussianPDFReal_nonneg 0 ((A ^ 2 / N).toNNReal) (v i)).symm
  rw [← hdens, ← pi_gaussianReal_eq_withDensity hσ]
  exact integral_nonlinearForcingZeroFiber_mulVec_gaussianMat
    A hA hN t θ hθ hφ

/-- The fixed-state nonlinear/linearized fiber discrepancy is controlled by
twice the total-variation distance in the exact A-8a density formulation. -/
theorem abs_integral_nonlinearForcingFiber_sub_le_two_mul_tvDist
    (A : ℝ) {N : ℕ} (hA : A ≠ 0) (hN : 0 < N)
    (hσ : (A ^ 2 / N).toNNReal ≠ 0) {r : ℝ} (hr : 0 < r) (t : ℝ)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ)
    (habs : ∀ z, |φ z| ≤ 1) :
    |(∫ W, nonlinearForcingPlusFiber N r t φ
        (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N) -
      ∫ W, nonlinearForcingZeroFiber N t φ
        (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N| ≤
      2 * tvDist
        (Measure.map (angular N)
          (((volume : Measure (Fin N → ℝ)).withDensity
            (fun v => ENNReal.ofReal
              (polarDensityReal N ((A ^ 2 / N).toNNReal) r v))).restrict
                {v | gaussianEuclideanNorm N v < Real.exp (-t)}))
        (Measure.map (angular N)
          (((volume : Measure (Fin N → ℝ)).withDensity
            (fun v => ENNReal.ofReal
              (∏ i, gaussianPDFReal 0 ((A ^ 2 / N).toNNReal) (v i)))).restrict
                {v | gaussianEuclideanNorm N v < Real.exp (-t)})) := by
  let σ2 : NNReal := (A ^ 2 / N).toNNReal
  let μr : Measure (Fin N → ℝ) :=
    (volume : Measure (Fin N → ℝ)).withDensity
      (fun v => ENNReal.ofReal (polarDensityReal N σ2 r v))
  let μ0 : Measure (Fin N → ℝ) :=
    (volume : Measure (Fin N → ℝ)).withDensity
      (fun v => ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)))
  let ball : Set (Fin N → ℝ) := {v | gaussianEuclideanNorm N v < Real.exp (-t)}
  have hscale : Measurable (fun v : Fin N → ℝ => fun i => tanhScale r (v i)) :=
    measurable_pi_iff.mpr fun i => (measurable_tanhScale r).comp (measurable_pi_apply i)
  have hμr : Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 σ2)) = μr :=
    map_tanhScaleVec_pi_gaussianReal_eq_withDensity hσ hr
  have hdens :
      (fun v : Fin N → ℝ => ∏ i, gaussianPDF 0 σ2 (v i)) =
        fun v => ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) := by
    funext v
    rw [gaussianPDF_def]
    exact (ENNReal.ofReal_prod_of_nonneg fun i _ =>
      gaussianPDFReal_nonneg 0 σ2 (v i)).symm
  have hμ0 : Measure.pi (fun _ : Fin N => gaussianReal 0 σ2) = μ0 := by
    rw [pi_gaussianReal_eq_withDensity hσ, hdens]
  haveI : IsProbabilityMeasure μr := by
    rw [← hμr]
    exact Measure.isProbabilityMeasure_map hscale.aemeasurable
  haveI : IsProbabilityMeasure μ0 := by
    rw [← hμ0]
    infer_instance
  rw [integral_nonlinearForcingPlusFiber_eq_polarDensity A hA hN hσ hr t θ hθ hφ,
    integral_nonlinearForcingZeroFiber_eq_gaussianDensity A hA hN hσ t θ hθ hφ]
  exact abs_integral_sub_le_two_mul_tvDist_of_isFiniteMeasure
    (Measure.map (angular N) (μr.restrict ball))
    (Measure.map (angular N) (μ0.restrict ball)) φ hφ habs

/-- The A-8a polar perturbation estimate transferred to the fixed-state
nonlinear renewal fibers, uniformly in the unit direction and bounded test. -/
theorem exists_nonlinearForcingFiber_polarEnvelope
    (A : ℝ) {N : ℕ} (hA : A ≠ 0) (hN : 0 < N)
    (hσ : (A ^ 2 / N).toNNReal ≠ 0)
    (hσ0 : (0 : ℝ) < (A ^ 2 / N).toNNReal)
    {β δ : ℝ} (hβ : 0 < β) (hβN : β < (N : ℝ))
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      Renewal.driNorm
        (fun t : ℝ => ENNReal.ofReal (Real.exp (β * t) * polarEnvelope N t)) ≠ ⊤ ∧
      ∀ {r : ℝ}, 0 < r → r ≤ √N → ∀ t : ℝ,
        ∀ (θ : EuclideanSpace ℝ (Fin N)), ‖θ‖ = 1 →
        ∀ {φ : EuclideanSpace ℝ (Fin N) → ℝ}, Measurable φ →
          (∀ z, |φ z| ≤ 1) →
          |(∫ W, nonlinearForcingPlusFiber N r t φ
              (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N) -
            ∫ W, nonlinearForcingZeroFiber N t φ
              (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N| ≤
            C * r ^ δ * polarEnvelope N t := by
  obtain ⟨C, hC, hdri, htv⟩ :=
    exists_gaussianPolarPerturbation_bound hσ hσ0 hβ hβN hδ0 hδ2
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, hdri, ?_⟩
  intro r hr hrN t θ hθ φ hφ habs
  have hfiber :=
    abs_integral_nonlinearForcingFiber_sub_le_two_mul_tvDist
      A hA hN hσ hr t θ hθ hφ habs
  have hpolar := htv hr hrN t
  rw [← set_gaussianEuclideanNorm_lt_exp_eq N t] at hpolar
  exact hfiber.trans <|
    (mul_le_mul_of_nonneg_left hpolar (by norm_num)).trans_eq (by ring)

/-- The nonlinear integrand depends on `(Y,Θ,W)` through
`r = exp (-Y)`, `t = y-Y`, and `v=WΘ`, exactly as in tex L5185--5190. -/
lemma nonlinearForcingPlusIntegrand_eq_fiber (N : ℕ) (y Y : ℝ)
    (θ : EuclideanSpace ℝ (Fin N)) (W : Fin N → Fin N → ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) :
    nonlinearForcingPlusIntegrand N y φ ((Y, θ), W) =
      nonlinearForcingPlusFiber N (Real.exp (-Y)) (y - Y) φ
        (Matrix.mulVec W (WithLp.ofLp θ)) := by
  simp only [nonlinearForcingPlusIntegrand, logPolarStep_fst, logPolarStep_snd,
    nonlinearForcingPlusFiber]
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

/-- The analogous shifted-variable identity for the linearized integrand. -/
lemma nonlinearForcingZeroIntegrand_eq_fiber (N : ℕ) (y Y : ℝ)
    (θ : EuclideanSpace ℝ (Fin N)) (W : Fin N → Fin N → ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ) :
    nonlinearForcingZeroIntegrand N y φ ((Y, θ), W) =
      nonlinearForcingZeroFiber N (y - Y) φ
        (Matrix.mulVec W (WithLp.ofLp θ)) := by
  simp only [nonlinearForcingZeroIntegrand, nonlinearForcingZeroFiber]
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

end AbsorptionCutoff
