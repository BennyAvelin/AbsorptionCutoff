/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.PowerSingularity

/-!
# Renewal assembly for the invariant-law power singularity

This continuation module carries the renewal equation, renewal limit, and final
weak-convergence argument for `thm:nd-power-singularity`.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace AbsorptionCutoff

/-- Away from the absorbing origin, every one-step vector transition has a
density with respect to Cartesian Lebesgue measure. Gaussian isotropy first
identifies the linear image as a nondegenerate product Gaussian; the
coordinatewise hyperbolic tangent then has the density constructed for the
polar-perturbation estimate. -/
lemma Pkernel_apply_absolutelyContinuous_volume_of_ne_zero
    {A : ℝ} (hA : A ≠ 0) {N : ℕ} (hN : 0 < N)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    Pkernel A N x ≪ (volume : Measure (Fin N → ℝ)) := by
  have hA2 : 0 < A ^ 2 :=
    lt_of_le_of_ne (sq_nonneg A) (Ne.symm (pow_ne_zero 2 hA))
  have hsq : 0 < ∑ j, (x j) ^ 2 := by
    rcases Function.ne_iff.1 hx with ⟨i, hi⟩
    refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
    exact lt_of_le_of_ne (sq_nonneg _)
      (Ne.symm (pow_ne_zero 2 (by simpa using hi)))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hvarpos : 0 < A ^ 2 * radiusSq N x := by
    unfold radiusSq
    positivity
  have hσ : ((A ^ 2 * radiusSq N x).toNNReal) ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hvarpos
  have htanh : Measurable (fun v : Fin N → ℝ => fun i => Real.tanh (v i)) := by
    exact measurable_pi_iff.mpr fun i =>
      continuous_tanh.measurable.comp (measurable_pi_apply i)
  have hrow : Measurable (fun W : Fin N → Fin N → ℝ =>
      fun i => ∑ j, W i j * x j) := by
    exact measurable_pi_iff.mpr fun i =>
      Finset.measurable_sum _ fun j _ => by fun_prop
  have hstep : Pstep N x =
      (fun v : Fin N → ℝ => fun i => Real.tanh (v i)) ∘
        (fun W i => ∑ j, W i j * x j) := by
    funext W i
    rfl
  rw [Pkernel_apply, hstep, ← Measure.map_map htanh hrow,
    map_rowMap_gaussianMat]
  have htanhScale :
      (fun v : Fin N → ℝ => fun i => Real.tanh (v i)) =
        fun v => fun i => tanhScale 1 (v i) := by
    funext v i
    simp [tanhScale]
  rw [htanhScale,
    map_tanhScaleVec_pi_gaussianReal_eq_withDensity hσ zero_lt_one]
  exact withDensity_absolutelyContinuous volume _

/-- An origin-free invariant probability law of the vector kernel is absolutely
continuous with respect to Cartesian Lebesgue measure. This is the paper's
one-step density argument: stationarity writes the law as a mixture of the
absolutely continuous transitions away from the null absorbing origin. -/
lemma invariant_Pkernel_absolutelyContinuous_volume
    {A : ℝ} (hA : A ≠ 0) {N : ℕ} (hN : 0 < N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (horigin : π ({0} : Set (Fin N → ℝ)) = 0) :
    π ≪ (volume : Measure (Fin N → ℝ)) := by
  rw [← hπ.def]
  refine Measure.AbsolutelyContinuous.mk fun s hs hvol => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)]
  have hne : ∀ᵐ x ∂π, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.setOf_eq_eq_singleton] using horigin
  filter_upwards [hne] with x hx
  exact Pkernel_apply_absolutelyContinuous_volume_of_ne_zero hA hN hx hvol

/-- The closed-endpoint form of `eq:nd-tail-measure-identity` for the paper's
origin-free invariant vector law. Stationarity supplies absolute continuity,
which removes the sphere at radius `exp (-y)`. -/
lemma weightedTailMeasure_apply_le_exp_neg_of_invariant_Pkernel
    {A : ℝ} (hA : A ≠ 0) {N : ℕ} (hN : 0 < N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (horigin : π ({0} : Set (Fin N → ℝ)) = 0)
    (β y : ℝ) {B : Set (EuclideanSpace ℝ (Fin N))}
    (hB : MeasurableSet B) :
    weightedTailMeasure N π β y B =
      ENNReal.ofReal (Real.exp (β * y)) *
        π {x | 0 < gaussianEuclideanNorm N x ∧
          gaussianEuclideanNorm N x ≤ Real.exp (-y) ∧ angular N x ∈ B} := by
  have hac : π ≪ (volume : Measure (Fin N → ℝ)) :=
    invariant_Pkernel_absolutelyContinuous_volume hA hN π hπ horigin
  have horigin' : π {x | gaussianEuclideanNorm N x = 0} = 0 := by
    rw [show {x | gaussianEuclideanNorm N x = 0} =
        ({0} : Set (Fin N → ℝ)) by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
        gaussianEuclideanNorm_eq_zero_iff N]]
    exact horigin
  have hsphere :
      π {x | gaussianEuclideanNorm N x = Real.exp (-y)} = 0 :=
    measure_gaussianEuclideanNorm_level_set_eq_zero_of_absolutelyContinuous
      N π hac (Real.exp_ne_zero (-y))
  exact weightedTailMeasure_apply_le_exp_neg
    N π β y horigin' hsphere hB

/-- Real test-function evaluation of the weighted angular tail measure. This is
the scalar quantity denoted `ℋ_y(φ)` in the renewal equation. -/
noncomputable def weightedTailIntegral (N : ℕ) (π : Measure (Fin N → ℝ))
    (β y : ℝ) (φ : EuclideanSpace ℝ (Fin N) → ℝ) : ℝ :=
  ∫ θ, φ θ ∂weightedTailMeasure N π β y

/-- Evaluation at the constant-one test function is the real total mass of the
weighted angular tail measure. -/
lemma weightedTailIntegral_one (N : ℕ) (π : Measure (Fin N → ℝ))
    (β y : ℝ) :
    weightedTailIntegral N π β y (fun _ => 1) =
      (weightedTailMeasure N π β y).real Set.univ := by
  rw [weightedTailIntegral, integral_const]
  simp

/-- The constant-one weighted tail is bounded by its exponential prefactor. -/
lemma abs_weightedTailIntegral_one_le_exp
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (β y : ℝ) :
    |weightedTailIntegral N π β y (fun _ => 1)| ≤ Real.exp (β * y) := by
  have hmass : weightedTailMeasure N π β y Set.univ ≤
      ENNReal.ofReal (Real.exp (β * y)) := by
    rw [weightedTailMeasure_apply N π β y MeasurableSet.univ]
    calc
      ENNReal.ofReal (Real.exp (β * y)) *
          logPolarLaw N π {p | y < p.1 ∧ p.2 ∈ Set.univ}
        ≤ ENNReal.ofReal (Real.exp (β * y)) * 1 := by
            gcongr
            calc
              logPolarLaw N π {p | y < p.1 ∧ p.2 ∈ Set.univ}
                  ≤ logPolarLaw N π Set.univ :=
                    measure_mono (Set.subset_univ _)
              _ = 1 := measure_univ
      _ = ENNReal.ofReal (Real.exp (β * y)) := mul_one _
  rw [weightedTailIntegral_one]
  have hfinite : weightedTailMeasure N π β y Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hreal : (weightedTailMeasure N π β y).real Set.univ ≤
      (ENNReal.ofReal (Real.exp (β * y))).toReal := by
    exact (ENNReal.toReal_le_toReal hfinite ENNReal.ofReal_ne_top).2 hmass
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  rw [abs_of_nonneg]
  · exact hreal
  · exact ENNReal.toReal_nonneg

/-- The weighted constant-one tail vanishes at the left boundary when the
exponential tilt is positive (`eq:nd-renewal-left-boundary`). -/
lemma tendsto_weightedTailIntegral_one_atBot
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    {β : ℝ} (hβ : 0 < β) :
    Filter.Tendsto (fun y => weightedTailIntegral N π β y (fun _ => 1))
      Filter.atBot (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero
  · intro y
    exact abs_nonneg _
  · intro y
    exact abs_weightedTailIntegral_one_le_exp N π β y
  · exact Real.tendsto_exp_atBot.comp
      (Filter.tendsto_id.const_mul_atBot hβ)

/-- The weighted constant-one tail is uniformly bounded on every left
half-line, the local boundedness hypothesis used in the renewal iteration. -/
lemma exists_bound_weightedTailIntegral_one_Iic
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    {β : ℝ} (hβ : 0 < β) :
    ∀ L : ℝ, ∃ C : ℝ, ∀ u, u ≤ L →
      |weightedTailIntegral N π β u (fun _ => 1)| ≤ C := by
  intro L
  refine ⟨Real.exp (β * L), fun u hu => ?_⟩
  exact (abs_weightedTailIntegral_one_le_exp N π β u).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hβ.le))

/-- Removing the exponential weight from the constant-one tail integral leaves
exactly the log-polar tail probability. -/
lemma exp_neg_mul_abs_weightedTailIntegral_one
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (β y : ℝ) :
    Real.exp (-(β * y)) *
        |weightedTailIntegral N π β y (fun _ => 1)| =
      (logPolarLaw N π {p | y < p.1}).toReal := by
  rw [weightedTailIntegral_one, Measure.real,
    abs_of_nonneg ENNReal.toReal_nonneg]
  rw [weightedTailMeasure_apply N π β y MeasurableSet.univ]
  simp only [Set.mem_univ, and_true]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [← mul_assoc, ← Real.exp_add]
  simp

/-- The first-coordinate upper tail of the finite log-polar law vanishes. -/
lemma tendsto_toReal_logPolarLaw_fst_tail_atTop
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π] :
    Filter.Tendsto (fun y => (logPolarLaw N π {p | y < p.1}).toReal)
      Filter.atTop (nhds 0) := by
  let μY : Measure ℝ := (logPolarLaw N π).map Prod.fst
  haveI : IsProbabilityMeasure μY :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have htail : ∀ y : ℝ,
      (logPolarLaw N π {p | y < p.1}).toReal = 1 - cdf μY y := by
    intro y
    have hevent : {p : ℝ × EuclideanSpace ℝ (Fin N) | y < p.1} =
        Prod.fst ⁻¹' Set.Ioi y := rfl
    rw [hevent, ← Measure.map_apply measurable_fst measurableSet_Ioi]
    change (μY (Set.Ioi y)).toReal = _
    rw [← Set.compl_Iic, measure_compl measurableSet_Iic
      (measure_ne_top μY (Set.Iic y))]
    rw [ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _))
      (measure_ne_top μY Set.univ), measure_univ, cdf_eq_real, Measure.real]
    norm_num
  refine Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun y => (htail y).symm) ?_
  have hconst : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa using hconst.sub (tendsto_cdf_atTop μY)

/-- The exponentially rescaled constant-one tail vanishes at the right
boundary (`eq:nd-renewal-right-minimality`). -/
lemma tendsto_exp_neg_mul_abs_weightedTailIntegral_one_atTop
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (β : ℝ) :
    Filter.Tendsto (fun y => Real.exp (-(β * y)) *
        |weightedTailIntegral N π β y (fun _ => 1)|)
      Filter.atTop (nhds 0) := by
  refine (tendsto_toReal_logPolarLaw_fst_tail_atTop N π).congr' ?_
  exact Filter.Eventually.of_forall fun y =>
    (exp_neg_mul_abs_weightedTailIntegral_one N π β y).symm

/-- Concrete log-polar integral formula for the weighted tail evaluation. This
is the form to which the log-polar stationary equation is applied. -/
lemma weightedTailIntegral_eq_logPolarLaw
    (N : ℕ) (π : Measure (Fin N → ℝ)) (β y : ℝ)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ) :
    weightedTailIntegral N π β y φ =
      Real.exp (β * y) *
        ∫ p, ({p : ℝ × EuclideanSpace ℝ (Fin N) | y < p.1}.indicator
          (fun p => φ p.2)) p ∂logPolarLaw N π := by
  rw [weightedTailIntegral, weightedTailMeasure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have hset : MeasurableSet
      {p : ℝ × EuclideanSpace ℝ (Fin N) | y < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  rw [integral_map measurable_snd.aemeasurable hφ.aestronglyMeasurable]
  rw [← integral_indicator hset]

/-- Log-polar stationarity rewrites the weighted tail as the product expectation
of the true nonlinear one-step tail integrand. -/
lemma weightedTailIntegral_eq_integral_nonlinearForcingPlus
    {A : ℝ} (hA : A ≠ 0) {N : ℕ} (hN : 0 < N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (β y C : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ θ, |φ θ| ≤ C) :
    weightedTailIntegral N π β y φ =
      Real.exp (β * y) *
        ∫ q, nonlinearForcingPlusIntegrand N y φ q
          ∂(logPolarLaw N π).prod (gaussianMat A N) := by
  rw [weightedTailIntegral_eq_logPolarLaw N π β y hφm]
  congr 1
  let Ξ : ℝ × EuclideanSpace ℝ (Fin N) → ℝ :=
    fun p => ({p : ℝ × EuclideanSpace ℝ (Fin N) | y < p.1}.indicator
      (fun p => φ p.2)) p
  have hset : MeasurableSet
      {p : ℝ × EuclideanSpace ℝ (Fin N) | y < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hΞm : Measurable Ξ :=
    (hφm.comp measurable_snd).indicator hset
  have hΞb : ∀ p, ‖Ξ p‖ ≤ C := by
    intro p
    simp only [Ξ, Set.indicator]
    split
    · simpa [Real.norm_eq_abs] using hφ p.2
    · simpa using (abs_nonneg (φ 0)).trans (hφ 0)
  change (∫ p, Ξ p ∂logPolarLaw N π) = _
  rw [logPolar_stationary_equation hA hN π hπ horigin hΞm hΞb]
  have hfun : (fun q : (ℝ × EuclideanSpace ℝ (Fin N)) ×
      (Fin N → Fin N → ℝ) => Ξ (logPolarStep N q.1.1 q.1.2 q.2)) =
      nonlinearForcingPlusIntegrand N y φ := by
    funext q
    simp only [Ξ, nonlinearForcingPlusIntegrand, Set.indicator]
    split <;> simp_all
  have hint : Integrable (fun q : (ℝ × EuclideanSpace ℝ (Fin N)) ×
      (Fin N → Fin N → ℝ) => Ξ (logPolarStep N q.1.1 q.1.2 q.2))
      ((logPolarLaw N π).prod (gaussianMat A N)) := by
    rw [hfun]
    exact integrable_nonlinearForcingPlusIntegrand A N y C hφm hφ
  calc
    (∫ p, (∫ W, Ξ (logPolarStep N p.1 p.2 W) ∂gaussianMat A N)
        ∂logPolarLaw N π) =
      ∫ q, Ξ (logPolarStep N q.1.1 q.1.2 q.2)
        ∂(logPolarLaw N π).prod (gaussianMat A N) :=
          (integral_prod _ hint).symm
    _ = ∫ q, nonlinearForcingPlusIntegrand N y φ q
        ∂(logPolarLaw N π).prod (gaussianMat A N) := by rw [hfun]

/-- Adding and subtracting the linearized tail expectation isolates exactly the
nonlinear forcing `Ψ_y^π(φ)`. -/
lemma weightedTailIntegral_eq_integral_nonlinearForcingZero_add
    {A : ℝ} (hA : A ≠ 0) {N : ℕ} (hN : 0 < N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (β y C : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ θ, |φ θ| ≤ C) :
    weightedTailIntegral N π β y φ =
      Real.exp (β * y) *
        ∫ q, nonlinearForcingZeroIntegrand N y φ q
          ∂(logPolarLaw N π).prod (gaussianMat A N) +
      nonlinearForcing A N π β y φ := by
  rw [weightedTailIntegral_eq_integral_nonlinearForcingPlus
    hA hN π hπ horigin β y C hφm hφ, nonlinearForcing]
  ring

/-- Coordinatewise scaling of a standard Gaussian vector by `A / √N`
produces the product Gaussian law with variance `A² / N`. -/
lemma map_scale_gaussianVec
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    Measure.map (fun g : Fin N → ℝ => fun i => (A / Real.sqrt N) * g i)
        (gaussianVec N) =
      Measure.pi (fun _ : Fin N =>
        gaussianReal 0 ((A ^ 2 / N).toNNReal)) := by
  rw [gaussianVec]
  haveI : ∀ _i : Fin N, IsProbabilityMeasure
      ((gaussianReal 0 1).map (fun g => (A / Real.sqrt N) * g)) :=
    fun _ => Measure.isProbabilityMeasure_map (by fun_prop)
  rw [Measure.pi_map_pi (fun _ => (by fun_prop :
    AEMeasurable (fun g : ℝ => (A / Real.sqrt N) * g) (gaussianReal 0 1)))]
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

/-- At a unit direction, the Gaussian matrix fibre has the same law as a
standard Gaussian vector scaled coordinatewise by `A / √N`. -/
lemma map_mulVec_gaussianMat_eq_map_scale_gaussianVec
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1) :
    (gaussianMat A N).map
        (fun (W : Fin N → Fin N → ℝ) i =>
          ∑ j, W i j * WithLp.ofLp θ j) =
      Measure.map (fun g : Fin N → ℝ =>
        fun i => (A / Real.sqrt N) * g i) (gaussianVec N) := by
  rw [map_mulVec_gaussianMat_of_norm_eq_one A θ hθ,
    map_scale_gaussianVec hA hN]

/-- The log-polar coordinates of the scaled standard Gaussian vector split
into the renewal increment and the unchanged standard-Gaussian angle. -/
lemma logRadius_angular_scale_gaussianVec
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (g : Fin N → ℝ) :
    (logRadius N (fun i => (A / Real.sqrt N) * g i),
        angular N (fun i => (A / Real.sqrt N) * g i)) =
      (logRadialIncrement A N g, angular N g) := by
  have hsqrt : 0 < Real.sqrt N :=
    Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hscale : 0 < A / Real.sqrt N := div_pos hA hsqrt
  apply Prod.ext
  · change logRadius N ((A / Real.sqrt N) • g) = _
    rw [logRadius, gaussianEuclideanNorm_smul, abs_of_pos hscale]
    rfl
  · change angular N ((A / Real.sqrt N) • g) = angular N g
    rw [angular, angular, gaussianEuclideanNorm_smul, abs_of_pos hscale]
    rw [show WithLp.toLp 2 ((A / Real.sqrt N) • g) =
        (A / Real.sqrt N) • WithLp.toLp 2 g by rfl]
    rw [smul_smul]
    congr 1
    field_simp

/-- At a unit direction, the joint log-radius/angular law of the linearized
Gaussian matrix fibre is the standard-Gaussian increment/angle law. -/
lemma map_logRadius_angular_mulVec_gaussianMat
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1) :
    (gaussianMat A N).map
        (fun W =>
          (logRadius N (fun i => ∑ j, W i j * WithLp.ofLp θ j),
            angular N (fun i => ∑ j, W i j * WithLp.ofLp θ j))) =
      (gaussianVec N).map
        (fun g => (logRadialIncrement A N g, angular N g)) := by
  let mulTheta : (Fin N → Fin N → ℝ) → (Fin N → ℝ) :=
    fun W i => ∑ j, W i j * WithLp.ofLp θ j
  let scaleVec : (Fin N → ℝ) → (Fin N → ℝ) :=
    fun g i => (A / Real.sqrt N) * g i
  let polar : (Fin N → ℝ) → ℝ × EuclideanSpace ℝ (Fin N) :=
    fun v => (logRadius N v, angular N v)
  have hmul : Measurable mulTheta := by
    exact measurable_pi_iff.mpr fun i =>
      Finset.measurable_sum _ fun j _ => by fun_prop
  have hscale : Measurable scaleVec := by fun_prop
  have hpolar : Measurable polar :=
    (measurable_logRadius N).prod (measurable_angular N)
  change Measure.map (polar ∘ mulTheta) (gaussianMat A N) = _
  rw [← Measure.map_map hpolar hmul]
  rw [map_mulVec_gaussianMat_eq_map_scale_gaussianVec hA hN θ hθ]
  change Measure.map polar (Measure.map scaleVec (gaussianVec N)) = _
  rw [Measure.map_map hpolar hscale]
  congr 1
  funext g
  exact logRadius_angular_scale_gaussianVec hA hN g

/-- The Cramér-tilted joint law of the standard-Gaussian radial increment and
angle. Its radial marginal is the renewal increment law below. -/
noncomputable def tiltedIncrementAngularLaw (A : ℝ) (N : ℕ) :
    Measure (ℝ × EuclideanSpace ℝ (Fin N)) :=
  ((gaussianVec N).tilted
      (fun g => cramerExponent A N * logRadialIncrement A N g)).map
    (fun g => (logRadialIncrement A N g, angular N g))

/-- The radial marginal of the tilted increment/angle law is exactly the
tilted increment law driving the renewal equation. -/
lemma map_fst_tiltedIncrementAngularLaw (A : ℝ) (N : ℕ) :
    (tiltedIncrementAngularLaw A N).map Prod.fst =
      tiltedIncrementLaw A N := by
  rw [tiltedIncrementAngularLaw, Measure.map_map measurable_fst
    ((measurable_logRadialIncrement A N).prod (measurable_angular N))]
  rfl

/-- The joint density of the standard Gaussian vector is radial: it is the
usual normalization constant times `exp (-‖g‖₂² / 2)`. This is the density
input for the polar-coordinate proof of radial/angular independence. -/
lemma prod_gaussianPDF_standard_eq_radial (N : ℕ) (g : Fin N → ℝ) :
    (∏ i, gaussianPDF 0 1 (g i)) =
      ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ N *
          Real.exp (-(gaussianSquaredNorm N g) / 2)) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun i _ => gaussianPDFReal_nonneg 0 1 (g i))]
  congr 1
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  congr 1
  · simp
  · rw [← Real.exp_sum]
    unfold gaussianSquaredNorm
    congr 1
    simp only [div_eq_mul_inv, neg_mul]
    rw [Finset.sum_mul, Finset.sum_neg_distrib]

/-- The multivariate standard Gaussian has its usual radial density with
respect to Euclidean volume. This transports the product-coordinate density
through the volume-preserving equivalence `WithLp.toLp`. -/
lemma stdGaussian_eq_withDensity_radial (N : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin N)) =
      (volume : Measure (EuclideanSpace ℝ (Fin N))).withDensity
        (fun x => ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi))⁻¹ ^ N *
            Real.exp (-‖x‖ ^ 2 / 2))) := by
  rw [← map_toLp_gaussianVec N, gaussianVec,
    pi_gaussianReal_eq_withDensity (N := N) one_ne_zero]
  have hdens : Measurable (fun v : Fin N → ℝ =>
      ∏ i, gaussianPDF 0 1 (v i)) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have hpush := map_withDensity_of_measurableEmbedding
    (MeasurableEquiv.toLp 2 (Fin N → ℝ)).measurableEmbedding
    (finv := @WithLp.ofLp 2 (Fin N → ℝ))
    (MeasurableEquiv.toLp 2 (Fin N → ℝ)).symm.measurable
    (fun _ => rfl) (volume : Measure (Fin N → ℝ)) hdens
  have hpush' :
      Measure.map (WithLp.toLp 2)
          ((volume : Measure (Fin N → ℝ)).withDensity
            (fun v => ∏ i, gaussianPDF 0 1 (v i))) =
        (Measure.map (WithLp.toLp 2) (volume : Measure (Fin N → ℝ))).withDensity
          (fun x => ∏ i, gaussianPDF 0 1 (WithLp.ofLp x i)) := by
    simpa only [MeasurableEquiv.coe_toLp] using hpush
  rw [hpush', (PiLp.volume_preserving_toLp (Fin N)).map_eq]
  congr 1
  funext x
  rw [prod_gaussianPDF_standard_eq_radial]
  congr 2
  have hsq : gaussianSquaredNorm N (WithLp.ofLp x) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt]
    · unfold gaussianSquaredNorm
      simp only [Real.norm_eq_abs, sq_abs]
    · positivity
  rw [hsq]

/-- Normalized surface measure on the Euclidean unit sphere, the paper's
`σ̄_N`. The normalization is nondegenerate when `0 < N`. -/
noncomputable def normalizedSphereLaw (N : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere

/-- The positive-radius factor in the standard Gaussian polar decomposition.
The surface-area factor is included here so that `normalizedSphereLaw` has
total mass one. -/
noncomputable def standardGaussianRadiusLaw (N : ℕ) :
    Measure (Set.Ioi (0 : ℝ)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ •
    ((Measure.volumeIoiPow (N - 1)).withDensity
      (fun r => ENNReal.ofReal
        ((Real.sqrt (2 * Real.pi))⁻¹ ^ N *
          Real.exp (-(r.1 ^ 2) / 2))))

/-- A nonzero standard Gaussian splits into independent normalized direction
and positive radius. This is the measure-level polar-coordinate form of the
paper's assertion that the Gaussian angle has law `σ̄_N` and is independent of
the radius. -/
lemma map_homeomorphUnitSphereProd_comap_stdGaussian {N : ℕ} (hN : 0 < N) :
    Measure.map (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin N)))
        (Measure.comap Subtype.val
          (stdGaussian (EuclideanSpace ℝ (Fin N)))) =
      (normalizedSphereLaw N).prod (standardGaussianRadiusLaw N) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let E := EuclideanSpace ℝ (Fin N)
  let f : E → ENNReal := fun x => ENNReal.ofReal
    ((Real.sqrt (2 * Real.pi))⁻¹ ^ N * Real.exp (-‖x‖ ^ 2 / 2))
  let g : Set.Ioi (0 : ℝ) → ENNReal := fun r => ENNReal.ofReal
    ((Real.sqrt (2 * Real.pi))⁻¹ ^ N * Real.exp (-(r.1 ^ 2) / 2))
  let σ := (volume : Measure E).toSphere
  let ρ := (Measure.volumeIoiPow (N - 1)).withDensity g
  have hf : Measurable f := by
    unfold f
    fun_prop
  have hg : Measurable g := by
    unfold g
    fun_prop
  have hs : MeasurableSet ({0}ᶜ : Set E) :=
    measurableSet_singleton 0 |>.compl
  have hraw :
      Measure.map (homeomorphUnitSphereProd E)
          (Measure.comap Subtype.val (stdGaussian E)) =
        σ.prod ρ := by
    rw [stdGaussian_eq_withDensity_radial]
    have hcomap :
        Measure.comap (Subtype.val : ({0}ᶜ : Set E) → E)
            ((volume : Measure E).withDensity f) =
          (Measure.comap (Subtype.val : ({0}ᶜ : Set E) → E)
            (volume : Measure E)).withDensity
            (fun x : ({0}ᶜ : Set E) => f x.1) := by
      apply (MeasurableEmbedding.subtype_coe hs).map_injective
      rw [map_comap_subtype_coe hs, restrict_withDensity hs]
      have htransport :
          Measure.map (Subtype.val : ({0}ᶜ : Set E) → E)
              ((Measure.comap (Subtype.val : ({0}ᶜ : Set E) → E)
                (volume : Measure E)).withDensity
                (fun x : ({0}ᶜ : Set E) => f x.1)) =
            (Measure.map (Subtype.val : ({0}ᶜ : Set E) → E)
              (Measure.comap (Subtype.val : ({0}ᶜ : Set E) → E)
                (volume : Measure E))).withDensity f := by
        ext t ht
        rw [Measure.map_apply (MeasurableEmbedding.subtype_coe hs).measurable ht,
          withDensity_apply _ ((MeasurableEmbedding.subtype_coe hs).measurable ht),
          withDensity_apply _ ht,
          Measure.restrict_map (MeasurableEmbedding.subtype_coe hs).measurable ht,
          lintegral_map hf (MeasurableEmbedding.subtype_coe hs).measurable]
      rw [map_comap_subtype_coe hs] at htransport
      exact htransport.symm
    change Measure.map (homeomorphUnitSphereProd E)
        (Measure.comap (Subtype.val : ({0}ᶜ : Set E) → E)
          ((volume : Measure E).withDensity f)) = _
    rw [hcomap]
    change Measure.map (homeomorphUnitSphereProd E)
        ((Measure.comap (Subtype.val : ({0}ᶜ : Set E) → E)
          (volume : Measure E)).withDensity (f ∘ Subtype.val)) = _
    have hpush := map_withDensity_of_measurableEmbedding
      (homeomorphUnitSphereProd E).measurableEmbedding
      (finv := (homeomorphUnitSphereProd E).symm)
      (homeomorphUnitSphereProd E).symm.measurable
      (homeomorphUnitSphereProd E).symm_apply_apply
      (Measure.comap (Subtype.val : ({0}ᶜ : Set E) → E) (volume : Measure E))
      (hf.comp (MeasurableEmbedding.subtype_coe hs).measurable)
    rw [hpush]
    rw [(volume : Measure E).measurePreserving_homeomorphUnitSphereProd.map_eq]
    rw [show Module.finrank ℝ E = N by simp [E]]
    have hfg :
        (fun p => (f ∘ Subtype.val) ((homeomorphUnitSphereProd E).symm p)) =
          fun p => g p.2 := by
      funext p
      have hnorm :
          ‖(((homeomorphUnitSphereProd E).symm p).1 : E)‖ = p.2.1 := by
        rw [homeomorphUnitSphereProd_symm_apply_coe, norm_smul,
          Real.norm_eq_abs, abs_of_pos p.2.2,
          mem_sphere_zero_iff_norm.mp p.1.2, mul_one]
      unfold f g
      simp only [Function.comp_apply]
      rw [hnorm]
    rw [hfg, ← prod_withDensity_right hg]
  have hm0 : σ Set.univ ≠ 0 := by
    intro hm
    exact (Measure.toSphere_ne_zero (volume : Measure E))
      (Measure.measure_univ_eq_zero.mp hm)
  have hm_top : σ Set.univ ≠ ⊤ := measure_ne_top σ Set.univ
  rw [hraw]
  change σ.prod ρ =
    ((σ Set.univ)⁻¹ • σ).prod ((σ Set.univ) • ρ)
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.inv_mul_cancel hm0 hm_top, one_smul]

/-- The paper's normalized surface law, embedded into the ambient Euclidean
space used by `angular`. -/
noncomputable def normalizedAngularLaw (N : ℕ) :
    Measure (EuclideanSpace ℝ (Fin N)) :=
  Measure.map Subtype.val (normalizedSphereLaw N)

/-- Before Cramér tilting, the standard Gaussian log-radius increment and
angle are independent, and the angle has the normalized surface law. The
radial factor is stated as the existing increment marginal so the following
tilting step is purely measure-theoretic. -/
lemma map_logRadialIncrement_angular_gaussianVec_eq_prod
    (A : ℝ) {N : ℕ} (hN : 0 < N) :
    Measure.map (fun g : Fin N → ℝ =>
        (logRadialIncrement A N g, angular N g)) (gaussianVec N) =
      (Measure.map (logRadialIncrement A N) (gaussianVec N)).prod
        (normalizedAngularLaw N) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let E := EuclideanSpace ℝ (Fin N)
  let dir : E → E := fun x => ‖x‖⁻¹ • x
  let joint : E → ℝ × E := fun x => (logRadialIncrementE A N x, dir x)
  let z : Set.Ioi (0 : ℝ) → ℝ :=
    fun r => -Real.log ((A / Real.sqrt N) * r.1)
  let R := Measure.map z (standardGaussianRadiusLaw N)
  have hdir : Measurable dir := by
    unfold dir
    fun_prop
  have hjoint : Measurable joint :=
    (measurable_logRadialIncrementE A N).prodMk hdir
  have hz : Measurable z := by
    unfold z
    fun_prop
  have hs : MeasurableSet ({0}ᶜ : Set E) :=
    measurableSet_singleton 0 |>.compl
  haveI : NullSingletonClass (stdGaussian E) := by
    rw [stdGaussian_eq_withDensity_radial]
    infer_instance
  have hcoord :
      (fun g : Fin N → ℝ =>
        (logRadialIncrement A N g, angular N g)) =
        joint ∘ (WithLp.toLp 2) := by
    funext g
    apply Prod.ext
    · exact logRadialIncrement_eq_logRadialIncrementE A N g
    · unfold joint dir angular
      rw [gaussianEuclideanNorm_eq_norm]
      rfl
  have hexplicit :
      Measure.map (fun g : Fin N → ℝ =>
          (logRadialIncrement A N g, angular N g)) (gaussianVec N) =
        R.prod (normalizedAngularLaw N) := by
    rw [hcoord, ← Measure.map_map hjoint (by fun_prop), map_toLp_gaussianVec]
    rw [← restrict_compl_singleton (μ := stdGaussian E) 0]
    rw [← map_comap_subtype_coe hs]
    rw [Measure.map_map hjoint
      (MeasurableEmbedding.subtype_coe hs).measurable]
    let post : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ × E :=
      fun p => (z p.2, p.1.1)
    have hpost : Measurable post := by
      unfold post
      exact (hz.comp measurable_snd).prodMk
        (measurable_subtype_coe.comp measurable_fst)
    have hjoint_polar :
        (joint ∘ (Subtype.val : ({0}ᶜ : Set E) → E)) =
          post ∘ (homeomorphUnitSphereProd E) := by
      funext x
      apply Prod.ext
      · unfold joint post z logRadialIncrementE
        simp only [Function.comp_apply,
          homeomorphUnitSphereProd_apply_snd_coe]
      · unfold joint post dir
        simp only [Function.comp_apply,
          homeomorphUnitSphereProd_apply_fst_coe]
    rw [hjoint_polar, ← Measure.map_map hpost
      (homeomorphUnitSphereProd E).measurable]
    rw [map_homeomorphUnitSphereProd_comap_stdGaussian hN]
    let ang : Metric.sphere (0 : E) 1 → E := Subtype.val
    have hang : Measurable ang := measurable_subtype_coe
    have hpost_map : post = Prod.swap ∘ Prod.map ang z := by
      funext p
      rfl
    rw [hpost_map, ← Measure.map_map measurable_swap (hang.prodMap hz)]
    letI : SFinite (normalizedSphereLaw N) := by
      unfold normalizedSphereLaw
      infer_instance
    letI : SFinite (standardGaussianRadiusLaw N) := by
      unfold standardGaussianRadiusLaw
      infer_instance
    rw [← Measure.map_prod_map (normalizedSphereLaw N)
      (standardGaussianRadiusLaw N) hang hz]
    rw [Measure.prod_swap]
    rfl
  let σ := (volume : Measure E).toSphere
  have hm0 : σ Set.univ ≠ 0 := by
    intro hm
    exact (Measure.toSphere_ne_zero (volume : Measure E))
      (Measure.measure_univ_eq_zero.mp hm)
  have hm_top : σ Set.univ ≠ ⊤ := measure_ne_top σ Set.univ
  have hang_univ : normalizedAngularLaw N Set.univ = 1 := by
    rw [normalizedAngularLaw, Measure.map_apply measurable_subtype_coe
      MeasurableSet.univ]
    simp only [Set.preimage_univ]
    change ((σ Set.univ)⁻¹ • σ) Set.univ = 1
    rw [Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel hm0 hm_top]
  letI : SFinite (normalizedAngularLaw N) := by
    unfold normalizedAngularLaw normalizedSphereLaw
    infer_instance
  have hradial := congrArg (Measure.map Prod.fst) hexplicit
  rw [Measure.map_map measurable_fst
      ((measurable_logRadialIncrement A N).prodMk (measurable_angular N)),
    Measure.map_fst_prod] at hradial
  have hfst :
      Prod.fst ∘ (fun g : Fin N → ℝ =>
        (logRadialIncrement A N g, angular N g)) =
      logRadialIncrement A N := rfl
  rw [hfst] at hradial
  have hradial' :
      Measure.map (logRadialIncrement A N) (gaussianVec N) = R := by
    simpa only [hang_univ, one_smul] using hradial
  rw [hexplicit, ← hradial']

/-- Exponential tilting commutes with a measurable pushforward when the tilt
weight is pulled back along the same map. -/
private lemma map_tilted_comp {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (g : β → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measure.map f (μ.tilted (g ∘ f)) =
      (Measure.map f μ).tilted g := by
  rw [Measure.tilted, Measure.tilted]
  have hint :
      ∫ x, Real.exp ((g ∘ f) x) ∂μ =
        ∫ y, Real.exp (g y) ∂Measure.map f μ := by
    exact (integral_map hf.aemeasurable hg.exp.aestronglyMeasurable).symm
  let d : β → ENNReal := fun y =>
    ENNReal.ofReal
      (Real.exp (g y) / ∫ z, Real.exp (g z) ∂Measure.map f μ)
  have hd : Measurable d := by
    unfold d
    fun_prop
  have hdcomp :
      (fun x => ENNReal.ofReal
        (Real.exp ((g ∘ f) x) / ∫ x, Real.exp ((g ∘ f) x) ∂μ)) =
        d ∘ f := by
    funext x
    rw [hint]
    rfl
  rw [hdcomp]
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, Measure.restrict_map hf hs,
    lintegral_map hd hf]
  rfl

/-- Tilting a product by a weight on its first coordinate only tilts the first
factor, provided the second factor is a probability measure. -/
private lemma tilted_prod_fst {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite μ] [SFinite ν] [IsProbabilityMeasure ν]
    (g : α → ℝ) (hg : Measurable g) :
    (μ.prod ν).tilted (g ∘ Prod.fst) =
      (μ.tilted g).prod ν := by
  rw [Measure.tilted, Measure.tilted,
    prod_withDensity_left (hg.exp.div_const _).ennreal_ofReal]
  have hint := integral_fun_fst (μ := μ) (ν := ν)
    (fun x => Real.exp (g x))
  congr 1
  funext z
  simp only [Function.comp_apply]
  rw [hint]
  simp

/-- In positive dimension, the normalized angular law is a probability
measure. -/
lemma isProbabilityMeasure_normalizedAngularLaw {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (normalizedAngularLaw N) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let E := EuclideanSpace ℝ (Fin N)
  let σ := (volume : Measure E).toSphere
  have hm0 : σ Set.univ ≠ 0 := by
    intro hm
    exact (Measure.toSphere_ne_zero (volume : Measure E))
      (Measure.measure_univ_eq_zero.mp hm)
  have hm_top : σ Set.univ ≠ ⊤ := measure_ne_top σ Set.univ
  constructor
  rw [normalizedAngularLaw, Measure.map_apply measurable_subtype_coe
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  change ((σ Set.univ)⁻¹ • σ) Set.univ = 1
  rw [Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel hm0 hm_top]

/-- The Cramér tilt changes only the radial increment law: the Gaussian angle
remains independent with its normalized surface distribution. -/
lemma tiltedIncrementAngularLaw_eq_prod
    (A : ℝ) {N : ℕ} (hN : 0 < N) :
    tiltedIncrementAngularLaw A N =
      (tiltedIncrementLaw A N).prod (normalizedAngularLaw N) := by
  let X : (Fin N → ℝ) → ℝ := logRadialIncrement A N
  let J : (Fin N → ℝ) → ℝ × EuclideanSpace ℝ (Fin N) :=
    fun g => (X g, angular N g)
  let w : ℝ → ℝ := fun z => cramerExponent A N * z
  let q : ℝ × EuclideanSpace ℝ (Fin N) → ℝ := w ∘ Prod.fst
  have hX : Measurable X := measurable_logRadialIncrement A N
  have hJ : Measurable J := hX.prodMk (measurable_angular N)
  have hw : Measurable w := by
    unfold w
    fun_prop
  letI : IsProbabilityMeasure (normalizedAngularLaw N) :=
    isProbabilityMeasure_normalizedAngularLaw hN
  rw [tiltedIncrementAngularLaw, tiltedIncrementLaw]
  change Measure.map J ((gaussianVec N).tilted (q ∘ J)) =
    (Measure.map X ((gaussianVec N).tilted (w ∘ X))).prod
      (normalizedAngularLaw N)
  calc
    Measure.map J ((gaussianVec N).tilted (q ∘ J)) =
        (Measure.map J (gaussianVec N)).tilted q :=
      map_tilted_comp (gaussianVec N) J q hJ
        (hw.comp measurable_fst)
    _ = ((Measure.map X (gaussianVec N)).prod
          (normalizedAngularLaw N)).tilted q := by
      congr 1
      simpa [J, X] using
        map_logRadialIncrement_angular_gaussianVec_eq_prod A hN
    _ = ((Measure.map X (gaussianVec N)).tilted w).prod
          (normalizedAngularLaw N) :=
      tilted_prod_fst (Measure.map X (gaussianVec N))
        (normalizedAngularLaw N) w hw
    _ = (Measure.map X ((gaussianVec N).tilted (w ∘ X))).prod
          (normalizedAngularLaw N) := by
      rw [map_tilted_comp (gaussianVec N) X w hX hw]

/-- On a fixed unit-direction Gaussian fibre, the exponentially weighted
linearized tail factors into the normalized angular mean and a scalar tail
kernel under the tilted increment law. -/
lemma exp_mul_integral_nonlinearForcingZeroFiber_eq
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) (t : ℝ)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ) :
    Real.exp (cramerExponent A N * t) *
        ∫ W, nonlinearForcingZeroFiber N t φ
          (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N =
      (∫ a, φ a ∂normalizedAngularLaw N) *
        ∫ z, if t < z then
          Real.exp (cramerExponent A N * (t - z)) else 0
          ∂tiltedIncrementLaw A N := by
  let X : (Fin N → ℝ) → ℝ := logRadialIncrement A N
  let JW : (Fin N → Fin N → ℝ) →
      ℝ × EuclideanSpace ℝ (Fin N) := fun W =>
    (logRadius N (fun i => ∑ j, W i j * WithLp.ofLp θ j),
      angular N (fun i => ∑ j, W i j * WithLp.ofLp θ j))
  let JG : (Fin N → ℝ) → ℝ × EuclideanSpace ℝ (Fin N) :=
    fun g => (X g, angular N g)
  let F : ℝ × EuclideanSpace ℝ (Fin N) → ℝ := fun p =>
    if t < p.1 then φ p.2 else 0
  let G : ℝ × EuclideanSpace ℝ (Fin N) → ℝ := fun p =>
    Real.exp (-(cramerExponent A N * p.1)) * F p
  let k : ℝ → ℝ := fun z =>
    if t < z then Real.exp (cramerExponent A N * (t - z)) else 0
  have hJW : Measurable JW := by
    unfold JW
    apply (measurable_logPolarCoords N).comp
    exact measurable_pi_iff.mpr fun i =>
      Finset.measurable_sum _ fun j _ => by fun_prop
  have hJG : Measurable JG :=
    (measurable_logRadialIncrement A N).prodMk (measurable_angular N)
  have hF : Measurable F := by
    unfold F
    exact Measurable.ite
      (measurableSet_lt measurable_const measurable_fst)
      (hφ.comp measurable_snd) measurable_const
  have hG : Measurable G := by
    unfold G
    fun_prop
  have hzero :
      (fun W => nonlinearForcingZeroFiber N t φ
        (fun i => ∑ j, W i j * WithLp.ofLp θ j)) =
        F ∘ JW := by
    funext W
    rfl
  have hLaw :
      Measure.map JW (gaussianMat A N) =
        Measure.map JG (gaussianVec N) := by
    simpa [JW, JG, X] using
      map_logRadius_angular_mulVec_gaussianMat hA hN θ hθ
  have hbase :
      (∫ W, nonlinearForcingZeroFiber N t φ
          (fun i => ∑ j, W i j * WithLp.ofLp θ j) ∂gaussianMat A N) =
        ∫ p, F p ∂Measure.map JG (gaussianVec N) := by
    calc
      _ = ∫ W, F (JW W) ∂gaussianMat A N := by
        rw [hzero]
        rfl
      _ = ∫ p, F p ∂Measure.map JW (gaussianMat A N) :=
        (integral_map hJW.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by rw [hLaw]
  have htilt :
      (∫ p, G p ∂tiltedIncrementAngularLaw A N) =
        ∫ p, F p ∂Measure.map JG (gaussianVec N) := by
    rw [tiltedIncrementAngularLaw,
      integral_map hJG.aemeasurable hG.aestronglyMeasurable,
      integral_tilted,
      integral_exp_cramerExponent_logRadialIncrement hA hN hsc]
    simp only [div_one, smul_eq_mul]
    rw [integral_map hJG.aemeasurable hF.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards with g
    unfold G JG X
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hpoint :
      (fun p => Real.exp (cramerExponent A N * t) * G p) =
        fun p => k p.1 * φ p.2 := by
    funext p
    unfold G F k
    split_ifs
    · rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · simp
  letI : IsProbabilityMeasure (normalizedAngularLaw N) :=
    isProbabilityMeasure_normalizedAngularLaw hN
  letI : IsProbabilityMeasure (tiltedIncrementLaw A N) :=
    isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  rw [hbase, ← htilt, ← integral_const_mul, hpoint,
    tiltedIncrementAngularLaw_eq_prod A hN, integral_prod_mul]
  ring

/-- The convolution of the constant-one weighted tail with the tilted
increment law is the stationary log-radius average of the scalar fibre kernel.
This is the Fubini step that joins the fixed-fibre factorization to the global
renewal equation. -/
lemma integral_weightedTailIntegral_one_tiltedIncrementLaw_eq
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π] (y : ℝ) :
    ∫ z, weightedTailIntegral N π (cramerExponent A N) (y - z)
        (fun _ => 1) ∂tiltedIncrementLaw A N =
      ∫ p, Real.exp (cramerExponent A N * p.1) *
        (∫ z, if y - p.1 < z then
          Real.exp (cramerExponent A N * ((y - p.1) - z)) else 0
          ∂tiltedIncrementLaw A N) ∂logPolarLaw N π := by
  let β := cramerExponent A N
  let μ := tiltedIncrementLaw A N
  let Ω := logPolarLaw N π
  let F : ℝ → (ℝ × EuclideanSpace ℝ (Fin N)) → ℝ := fun z p =>
    if y - z < p.1 then Real.exp (β * (y - z)) else 0
  let G : (ℝ × EuclideanSpace ℝ (Fin N)) → ℝ → ℝ := fun p z =>
    Real.exp (β * p.1) *
      if y - p.1 < z then Real.exp (β * ((y - p.1) - z)) else 0
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  letI : IsProbabilityMeasure Ω := by
    unfold Ω logPolarLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_logPolarCoords N).aemeasurable
  have hexp : Integrable (fun z : ℝ => Real.exp (-(β * z))) μ := by
    apply integrable_exp_neg_tiltedIncrementLaw hA hN hsc
    change β - β ∈ Set.Ioo (-(N : ℝ)) (N : ℝ)
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    simpa only [sub_self, Set.mem_Ioo] using
      (show -(N : ℝ) < 0 ∧ (0 : ℝ) < N from ⟨neg_lt_zero.mpr hNr, hNr⟩)
  have hF : Measurable (Function.uncurry F) := by
    unfold Function.uncurry F
    exact Measurable.ite
      (measurableSet_lt (measurable_const.sub measurable_fst)
        (measurable_fst.comp measurable_snd))
      (by fun_prop) measurable_const
  have hFint : Integrable (Function.uncurry F) (μ.prod Ω) := by
    have hmajor : Integrable
        (fun q : ℝ × (ℝ × EuclideanSpace ℝ (Fin N)) =>
          (Real.exp (β * y) * Real.exp (-(β * q.1))) * 1)
        (μ.prod Ω) :=
      (hexp.const_mul (Real.exp (β * y))).mul_prod
        (integrable_const 1)
    refine Integrable.mono' hmajor hF.aestronglyMeasurable ?_
    filter_upwards with q
    unfold Function.uncurry F
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      simp only [mul_one, ← Real.exp_add]
      apply le_of_eq
      congr 1
      ring
    · simp only [norm_zero, mul_one]
      positivity
  have hweighted : ∀ z,
      weightedTailIntegral N π β (y - z) (fun _ => 1) =
        ∫ p, F z p ∂Ω := by
    intro z
    rw [weightedTailIntegral_eq_logPolarLaw N π β (y - z)
      measurable_const, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold F
    simp only [Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> simp
  have hFG : ∀ z p, F z p = G p z := by
    intro z p
    unfold F G
    have hcond : y - z < p.1 ↔ y - p.1 < z := by
      constructor <;> intro h <;> linarith
    by_cases h : y - z < p.1
    · rw [if_pos h, if_pos (hcond.mp h), ← Real.exp_add]
      congr 1
      ring
    · have h' : ¬ y - p.1 < z := fun hp => h (hcond.mpr hp)
      simp only [if_neg h, if_neg h', mul_zero]
  calc
    (∫ z, weightedTailIntegral N π (cramerExponent A N) (y - z)
        (fun _ => 1) ∂tiltedIncrementLaw A N) =
        ∫ z, ∫ p, F z p ∂Ω ∂μ := by
      change (∫ z, weightedTailIntegral N π β (y - z)
        (fun _ => 1) ∂μ) = _
      apply integral_congr_ae
      filter_upwards with z
      exact hweighted z
    _ = ∫ p, ∫ z, F z p ∂μ ∂Ω :=
      integral_integral_swap hFint
    _ = ∫ p, ∫ z, G p z ∂μ ∂Ω := by
      apply integral_congr_ae
      filter_upwards with p
      apply integral_congr_ae
      filter_upwards with z
      exact hFG z p
    _ = ∫ p, Real.exp (cramerExponent A N * p.1) *
        (∫ z, if y - p.1 < z then
          Real.exp (cramerExponent A N * ((y - p.1) - z)) else 0
          ∂tiltedIncrementLaw A N) ∂logPolarLaw N π := by
      change (∫ p, ∫ z, G p z ∂μ ∂Ω) =
        ∫ p, Real.exp (β * p.1) *
          (∫ z, if y - p.1 < z then
            Real.exp (β * ((y - p.1) - z)) else 0 ∂μ) ∂Ω
      apply integral_congr_ae
      filter_upwards with p
      unfold G
      rw [integral_const_mul]

/-- After averaging over the stationary log-polar state, the complete
linearized term is the normalized angular mean times convolution of the
constant-one weighted tail with the tilted radial increment law. -/
lemma exp_mul_integral_nonlinearForcingZeroIntegrand_eq
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (y C : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ θ, |φ θ| ≤ C) :
    Real.exp (cramerExponent A N * y) *
        ∫ q, nonlinearForcingZeroIntegrand N y φ q
          ∂(logPolarLaw N π).prod (gaussianMat A N) =
      (∫ a, φ a ∂normalizedAngularLaw N) *
        ∫ z, weightedTailIntegral N π (cramerExponent A N) (y - z)
          (fun _ => 1) ∂tiltedIncrementLaw A N := by
  let β := cramerExponent A N
  let Ω := logPolarLaw N π
  let μ := tiltedIncrementLaw A N
  let a := ∫ θ, φ θ ∂normalizedAngularLaw N
  let I : (ℝ × EuclideanSpace ℝ (Fin N)) → ℝ := fun p =>
    ∫ W, nonlinearForcingZeroFiber N (y - p.1) φ
      (fun i => ∑ j, W i j * WithLp.ofLp p.2 j) ∂gaussianMat A N
  let K : (ℝ × EuclideanSpace ℝ (Fin N)) → ℝ := fun p =>
    ∫ z, if y - p.1 < z then
      Real.exp (β * ((y - p.1) - z)) else 0 ∂μ
  have hz := integrable_nonlinearForcingZeroIntegrand
    A N (π := π) y C hφm hφ
  have hinner : ∀ p,
      (∫ W, nonlinearForcingZeroIntegrand N y φ (p, W)
          ∂gaussianMat A N) = I p := by
    intro p
    apply integral_congr_ae
    filter_upwards with W
    exact nonlinearForcingZeroIntegrand_eq_fiber N y p.1 p.2 W φ
  have hpoint : ∀ᵐ p ∂Ω,
      Real.exp (β * y) * I p =
        a * (Real.exp (β * p.1) * K p) := by
    filter_upwards [ae_norm_snd_logPolarLaw_eq_one N π horigin] with p hp
    have hfib :=
      exp_mul_integral_nonlinearForcingZeroFiber_eq
        hA hN hsc (y - p.1) p.2 hp hφm
    change Real.exp (β * (y - p.1)) * I p = a * K p at hfib
    calc
      Real.exp (β * y) * I p =
          Real.exp (β * p.1) *
            (Real.exp (β * (y - p.1)) * I p) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ = Real.exp (β * p.1) * (a * K p) := by rw [hfib]
      _ = a * (Real.exp (β * p.1) * K p) := by ring
  calc
    Real.exp (cramerExponent A N * y) *
        ∫ q, nonlinearForcingZeroIntegrand N y φ q
          ∂(logPolarLaw N π).prod (gaussianMat A N) =
        Real.exp (β * y) *
          ∫ p, ∫ W, nonlinearForcingZeroIntegrand N y φ (p, W)
            ∂gaussianMat A N ∂Ω := by
      rw [integral_prod _ hz]
    _ = Real.exp (β * y) * ∫ p, I p ∂Ω := by
      congr 1
      apply integral_congr_ae
      filter_upwards with p
      exact hinner p
    _ = ∫ p, Real.exp (β * y) * I p ∂Ω := by
      rw [integral_const_mul]
    _ = ∫ p, a * (Real.exp (β * p.1) * K p) ∂Ω := by
      exact integral_congr_ae hpoint
    _ = a * ∫ p, Real.exp (β * p.1) * K p ∂Ω := by
      rw [integral_const_mul]
    _ = (∫ a, φ a ∂normalizedAngularLaw N) *
        ∫ z, weightedTailIntegral N π (cramerExponent A N) (y - z)
          (fun _ => 1) ∂tiltedIncrementLaw A N := by
      change a * (∫ p, Real.exp (β * p.1) * K p ∂Ω) =
        a * ∫ z, weightedTailIntegral N π β (y - z) (fun _ => 1) ∂μ
      congr 1
      exact (integral_weightedTailIntegral_one_tiltedIncrementLaw_eq
        hA hN hsc π y).symm

/-- The weighted angular tail satisfies the paper's renewal equation: its
linearized part is the scalar constant-one convolution multiplied by the
normalized angular mean, and its remainder is exactly `nonlinearForcing`. -/
lemma weightedTailIntegral_renewalEquation
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (y C : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ θ, |φ θ| ≤ C) :
    weightedTailIntegral N π (cramerExponent A N) y φ =
      (∫ a, φ a ∂normalizedAngularLaw N) *
        (∫ z, weightedTailIntegral N π (cramerExponent A N) (y - z)
          (fun _ => 1) ∂tiltedIncrementLaw A N) +
      nonlinearForcing A N π (cramerExponent A N) y φ := by
  rw [weightedTailIntegral_eq_integral_nonlinearForcingZero_add
    hA.ne' hN π hπ horigin (cramerExponent A N) y C hφm hφ]
  rw [exp_mul_integral_nonlinearForcingZeroIntegrand_eq
    hA hN hsc π horigin y C hφm hφ]

/-- At the constant-one angular test, the weighted tail obeys the scalar
renewal equation driven by `tiltedIncrementLaw`. -/
lemma weightedTailIntegral_one_renewalEquation
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (y : ℝ) :
    weightedTailIntegral N π (cramerExponent A N) y (fun _ => 1) =
      (∫ z, weightedTailIntegral N π (cramerExponent A N) (y - z)
        (fun _ => 1) ∂tiltedIncrementLaw A N) +
      nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1) := by
  letI : IsProbabilityMeasure (normalizedAngularLaw N) :=
    isProbabilityMeasure_normalizedAngularLaw hN
  have h := weightedTailIntegral_renewalEquation
    (φ := fun _ : EuclideanSpace ℝ (Fin N) => 1)
    hA hN hsc π hπ horigin y 1 measurable_const (fun _ => by norm_num)
  simpa using h

/-- The constant-one weighted tail is an exponential factor times the upper
tail of the first log-polar coordinate. -/
lemma weightedTailIntegral_one_eq_exp_mul_one_sub_cdf
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (β y : ℝ) :
    weightedTailIntegral N π β y (fun _ => 1) =
      Real.exp (β * y) *
        (1 - cdf ((logPolarLaw N π).map Prod.fst) y) := by
  let μY : Measure ℝ := (logPolarLaw N π).map Prod.fst
  letI : IsProbabilityMeasure μY :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hset : MeasurableSet
      {p : ℝ × EuclideanSpace ℝ (Fin N) | y < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  rw [weightedTailIntegral_eq_logPolarLaw N π β y measurable_const]
  have hone :
      (fun _ : ℝ × EuclideanSpace ℝ (Fin N) => (1 : ℝ)) =
        (1 : (ℝ × EuclideanSpace ℝ (Fin N)) → ℝ) := by
    funext p
    rfl
  rw [hone, integral_indicator_one hset]
  have hevent : {p : ℝ × EuclideanSpace ℝ (Fin N) | y < p.1} =
      Prod.fst ⁻¹' Set.Ioi y := rfl
  rw [hevent, Measure.real,
    ← Measure.map_apply measurable_fst measurableSet_Ioi]
  change Real.exp (β * y) * (μY.real (Set.Ioi y)) =
    Real.exp (β * y) * (1 - cdf μY y)
  congr 1
  rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic]
  rw [cdf_eq_real]
  simp

/-- The constant-one weighted tail is measurable as a function of its
log-radius threshold. -/
lemma measurable_weightedTailIntegral_one
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (β : ℝ) :
    Measurable (fun y => weightedTailIntegral N π β y (fun _ => 1)) := by
  rw [show (fun y => weightedTailIntegral N π β y (fun _ => 1)) =
      fun y => Real.exp (β * y) *
        (1 - cdf ((logPolarLaw N π).map Prod.fst) y) by
    funext y
    exact weightedTailIntegral_one_eq_exp_mul_one_sub_cdf N π β y]
  exact (measurable_const.mul measurable_id).exp.mul
    (measurable_const.sub
      (monotone_cdf ((logPolarLaw N π).map Prod.fst)).measurable)

/-- Every convolution power of the tilted increment law integrates a shifted
constant-one weighted tail. The exponential tail envelope is matched exactly
by the identity `𝔼[e^{-βSₙ}] = 1`. -/
lemma integrable_weightedTailIntegral_one_comp_sub_convPow
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (n : ℕ) (y : ℝ) :
    Integrable
      (fun s => weightedTailIntegral N π (cramerExponent A N) (y - s)
        (fun _ => 1))
      (Renewal.convPow (tiltedIncrementLaw A N) n) := by
  let β := cramerExponent A N
  let μ := tiltedIncrementLaw A N
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  have hexp : Integrable (fun s : ℝ => Real.exp (-(β * s)))
      (Renewal.convPow μ n) := by
    refine ⟨(by fun_prop), ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ s, ‖Real.exp (-(β * s))‖ₑ ∂(Renewal.convPow μ n)) =
          Renewal.expTransform β (Renewal.convPow μ n) := by
        rw [Renewal.expTransform_def]
        apply lintegral_congr
        intro s
        rw [Real.enorm_eq_ofReal (Real.exp_nonneg _)]
      _ = 1 := expTransform_convPow_tiltedIncrementLaw hA hN hsc n
      _ < ⊤ := ENNReal.one_lt_top
  have hmajor : Integrable
      (fun s : ℝ => Real.exp (β * y) * Real.exp (-(β * s)))
      (Renewal.convPow μ n) :=
    hexp.const_mul (Real.exp (β * y))
  change Integrable
    (fun s => weightedTailIntegral N π β (y - s) (fun _ => 1))
    (Renewal.convPow μ n)
  refine Integrable.mono' hmajor
    (((measurable_weightedTailIntegral_one N π β).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  calc
    |weightedTailIntegral N π β (y - s) (fun _ => 1)| ≤
        Real.exp (β * (y - s)) :=
      abs_weightedTailIntegral_one_le_exp N π β (y - s)
    _ = Real.exp (β * y) * Real.exp (-(β * s)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The rescaled polar tail against a bounded continuous angular test function
converges to its normalized spherical mean times the scalar renewal constant. -/
theorem tendsto_weightedTailIntegral
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφc : Continuous φ) (hφ1 : ∀ θ, |φ θ| ≤ 1) :
    Filter.Tendsto
      (fun y => weightedTailIntegral N π (cramerExponent A N) y φ)
      Filter.atTop
      (nhds ((∫ θ, φ θ ∂normalizedAngularLaw N) *
        ((∫ y, nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1)) /
          (∫ z, z ∂tiltedIncrementLaw A N)))) := by
  have hA0 : 0 < A := by linarith
  have hN0 : 0 < N := by omega
  have hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  have horigin : π {x | gaussianEuclideanNorm N x = 0} = 0 := by
    rw [show {x | gaussianEuclideanNorm N x = 0} =
        ({0} : Set (Fin N → ℝ)) by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
        gaussianEuclideanNorm_eq_zero_iff N]]
    exact hπ0
  have hβ : 0 < cramerExponent A N :=
    (cramerExponent_mem hA0 hN0 hsc).1
  have hψc : Continuous (fun y =>
      nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1)) :=
    continuous_nonlinearForcing A hN0 hσ π horigin
      (cramerExponent A N) measurable_const (fun _ => by norm_num)
  have hψd : Renewal.driNorm (fun y =>
      ‖nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1)‖ₑ) ≠ ⊤ := by
    simpa only [Real.enorm_eq_ofReal_abs] using
      (driNorm_ofReal_abs_nonlinearForcing_ne_top
        hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport
        (φ := fun _ => 1) measurable_const (fun _ => by norm_num))
  have hφd : Renewal.driNorm (fun y =>
      ‖nonlinearForcing A N π (cramerExponent A N) y φ‖ₑ) ≠ ⊤ := by
    simpa only [Real.enorm_eq_ofReal_abs] using
      (driNorm_ofReal_abs_nonlinearForcing_ne_top
        hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport
        hφc.measurable hφ1)
  exact tendsto_angular_of_renewalEquation_tiltedIncrementLaw
    (h := fun y => weightedTailIntegral N π (cramerExponent A N) y (fun _ => 1))
    (ψ := fun y => nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1))
    (Hφ := fun y => weightedTailIntegral N π (cramerExponent A N) y φ)
    (Ψφ := fun y => nonlinearForcing A N π (cramerExponent A N) y φ)
    (a := ∫ θ, φ θ ∂normalizedAngularLaw N)
    hA0 hN0 hsc hψc hψd hφd
    (integrable_weightedTailIntegral_one_comp_sub_convPow hA0 hN0 hsc π)
    (weightedTailIntegral_one_renewalEquation hA0 hN0 hsc π hπ horigin)
    (fun y => weightedTailIntegral_renewalEquation hA0 hN0 hsc π hπ horigin
      y 1 hφc.measurable hφ1)
    (tendsto_weightedTailIntegral_one_atBot
      (β := cramerExponent A N) N π hβ)
    (exists_bound_weightedTailIntegral_one_Iic
      (β := cramerExponent A N) N π hβ)
    (tendsto_exp_neg_mul_abs_weightedTailIntegral_one_atTop N π
      (cramerExponent A N))

/-- The weighted-tail limit for an arbitrary real bounded continuous angular
test function. This removes the unit-bound normalization used by the forcing
estimate and exposes the interface for weak convergence of finite measures. -/
theorem tendsto_weightedTailIntegral_boundedContinuous
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1)
    (φ : BoundedContinuousFunction (EuclideanSpace ℝ (Fin N)) ℝ) :
    Filter.Tendsto
      (fun y => weightedTailIntegral N π (cramerExponent A N) y φ)
      Filter.atTop
      (nhds ((∫ θ, φ θ ∂normalizedAngularLaw N) *
        ((∫ y, nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1)) /
          (∫ z, z ∂tiltedIncrementLaw A N)))) := by
  let C : ℝ := max ‖φ‖ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hbound : ∀ θ, |φ θ / C| ≤ 1 := by
    intro θ
    rw [abs_div, abs_of_pos hC]
    exact (div_le_one hC).2 <| by
      simpa only [Real.norm_eq_abs] using
        (φ.norm_coe_le_norm θ).trans (le_max_left _ _)
  have hlim := tendsto_weightedTailIntegral
    hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport
    (φ := fun θ => φ θ / C) (φ.continuous.div_const C) hbound
  have hscaled := hlim.const_mul C
  convert hscaled using 1
  · funext y
    rw [weightedTailIntegral, weightedTailIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with θ
    exact (mul_div_cancel₀ (φ θ) hC.ne').symm
  · congr 1
    rw [integral_div]
    field_simp

/-- The positive constant multiplying the limiting normalized angular law in
the invariant-law power singularity. -/
noncomputable def powerSingularityConstant
    (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ)) : ℝ :=
  (∫ y, nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1)) /
    (∫ z, z ∂tiltedIncrementLaw A N)

lemma powerSingularityConstant_pos
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    0 < powerSingularityConstant A N π := by
  exact div_pos
    (integral_nonlinearForcing_one_pos
      hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport)
    (integral_id_tiltedIncrementLaw_pos (by linarith) (by omega) hsc)

lemma isFiniteMeasure_weightedTailMeasure
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (β y : ℝ) : IsFiniteMeasure (weightedTailMeasure N π β y) := by
  refine IsFiniteMeasure.mk ?_
  rw [weightedTailMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_snd MeasurableSet.univ]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (measure_lt_top ((logPolarLaw N π).restrict {p | y < p.1}) Set.univ)

/-- The weighted angular tail measure as an element of Mathlib's weakly
topologized space of finite measures. -/
noncomputable def weightedTailFiniteMeasure
    (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (β y : ℝ) : FiniteMeasure (EuclideanSpace ℝ (Fin N)) :=
  ⟨weightedTailMeasure N π β y,
    isFiniteMeasure_weightedTailMeasure N π β y⟩

lemma isFiniteMeasure_smul_normalizedAngularLaw
    (N : ℕ) (hN : 0 < N) (c : ℝ) :
    IsFiniteMeasure (ENNReal.ofReal c • normalizedAngularLaw N) := by
  letI : IsProbabilityMeasure (normalizedAngularLaw N) :=
    isProbabilityMeasure_normalizedAngularLaw hN
  refine IsFiniteMeasure.mk ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (measure_lt_top (normalizedAngularLaw N) Set.univ)

/-- A real nonnegative multiple of the normalized angular law, packaged as a
finite measure. -/
noncomputable def scaledNormalizedAngularFiniteMeasure
    (N : ℕ) (hN : 0 < N) (c : ℝ) :
    FiniteMeasure (EuclideanSpace ℝ (Fin N)) :=
  ⟨ENNReal.ofReal c • normalizedAngularLaw N,
    isFiniteMeasure_smul_normalizedAngularLaw N hN c⟩

/-- The weighted angular tail measures converge weakly to the power-singularity
constant times normalized surface measure. -/
theorem tendsto_weightedTailFiniteMeasure
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    Filter.Tendsto
      (fun y => weightedTailFiniteMeasure N π (cramerExponent A N) y)
      Filter.atTop
      (nhds (scaledNormalizedAngularFiniteMeasure N (by omega)
        (powerSingularityConstant A N π))) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro φ
  have hc : 0 ≤ powerSingularityConstant A N π :=
    (powerSingularityConstant_pos
      hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport).le
  simp only [weightedTailFiniteMeasure, FiniteMeasure.toMeasure_mk,
    scaledNormalizedAngularFiniteMeasure, integral_smul_measure]
  rw [ENNReal.toReal_ofReal hc]
  simpa [weightedTailIntegral, powerSingularityConstant, mul_comm] using
    (tendsto_weightedTailIntegral_boundedContinuous
      hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport φ)

/-- Portmanteau continuity-set convergence for nonzero finite measures. Mathlib
states the direct result for probability measures; normalization and convergence
of total masses give this finite-measure form. -/
lemma tendsto_finiteMeasure_apply_of_null_frontier
    {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] [Nonempty Ω]
    {L : Filter ι} {μs : ι → FiniteMeasure Ω} {μ : FiniteMeasure Ω}
    (hlim : Filter.Tendsto μs L (nhds μ)) (hμ : μ ≠ 0)
    {E : Set Ω} (hE : μ (frontier E) = 0) :
    Filter.Tendsto (fun i => μs i E) L (nhds (μ E)) := by
  have hnorm := FiniteMeasure.tendsto_normalize_of_tendsto hlim hμ
  have hfront : μ.normalize (frontier E) = 0 := by
    rw [μ.normalize_eq_of_nonzero hμ, hE]
    simp
  have hset :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hnorm hfront
  have hmass := hlim.mass
  simpa only [FiniteMeasure.self_eq_mass_mul_normalize] using hmass.mul hset

/-- Portmanteau applied to the weighted angular tails: every continuity set of
normalized surface measure has the expected limiting weighted mass. -/
theorem tendsto_weightedTailMeasure_apply
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1)
    {B : Set (EuclideanSpace ℝ (Fin N))}
    (hB : normalizedAngularLaw N (frontier B) = 0) :
    Filter.Tendsto
      (fun y => weightedTailMeasure N π (cramerExponent A N) y B)
      Filter.atTop
      (nhds (ENNReal.ofReal (powerSingularityConstant A N π) *
        normalizedAngularLaw N B)) := by
  have hc := powerSingularityConstant_pos
    hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport
  let μlim := scaledNormalizedAngularFiniteMeasure N (by omega)
    (powerSingularityConstant A N π)
  have hμlim : μlim ≠ 0 := by
    intro hzero
    have hzero' := congrArg
      (fun ν : FiniteMeasure (EuclideanSpace ℝ (Fin N)) =>
        (ν : Measure (EuclideanSpace ℝ (Fin N))) Set.univ) hzero
    letI : IsProbabilityMeasure (normalizedAngularLaw N) :=
      isProbabilityMeasure_normalizedAngularLaw (by omega)
    have hcoef : ENNReal.ofReal (powerSingularityConstant A N π) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hc).ne'
    simp [μlim, scaledNormalizedAngularFiniteMeasure, Measure.smul_apply,
      hcoef] at hzero'
  have hfront : μlim (frontier B) = 0 := by
    rw [FiniteMeasure.null_iff_toMeasure_null]
    change (ENNReal.ofReal (powerSingularityConstant A N π) •
      normalizedAngularLaw N) (frontier B) = 0
    rw [Measure.smul_apply, smul_eq_mul, hB, mul_zero]
  have hnn := tendsto_finiteMeasure_apply_of_null_frontier
    (tendsto_weightedTailFiniteMeasure
      hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport)
    hμlim hfront
  have henn := ENNReal.tendsto_coe.mpr hnn
  simpa only [weightedTailFiniteMeasure,
    FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    FiniteMeasure.toMeasure_mk, μlim,
    scaledNormalizedAngularFiniteMeasure, Measure.smul_apply, smul_eq_mul] using henn

/-- The weighted continuity-set limit in the original Cartesian coordinates,
with closed radial endpoint and logarithmic radius parameter. -/
theorem tendsto_exp_mul_invariant_smallBall_angular
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1)
    {B : Set (EuclideanSpace ℝ (Fin N))}
    (hBm : MeasurableSet B)
    (hB : normalizedAngularLaw N (frontier B) = 0) :
    Filter.Tendsto
      (fun y =>
        ENNReal.ofReal (Real.exp (cramerExponent A N * y)) *
          π {x | 0 < gaussianEuclideanNorm N x ∧
            gaussianEuclideanNorm N x ≤ Real.exp (-y) ∧ angular N x ∈ B})
      Filter.atTop
      (nhds (ENNReal.ofReal (powerSingularityConstant A N π) *
        normalizedAngularLaw N B)) := by
  have h := tendsto_weightedTailMeasure_apply
    hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport hB
  convert h using 1
  funext y
  exact (weightedTailMeasure_apply_le_exp_neg_of_invariant_Pkernel
    (by linarith) (by omega) π hπ hπ0 (cramerExponent A N) y hBm).symm

/-- The directional small-ball tail normalized by its Cramér power converges
as the radius decreases to zero through positive values. -/
theorem tendsto_rpow_neg_mul_invariant_smallBall_angular
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1)
    {B : Set (EuclideanSpace ℝ (Fin N))}
    (hBm : MeasurableSet B)
    (hB : normalizedAngularLaw N (frontier B) = 0) :
    Filter.Tendsto
      (fun s =>
        ENNReal.ofReal (s ^ (-cramerExponent A N)) *
          π {x | 0 < gaussianEuclideanNorm N x ∧
            gaussianEuclideanNorm N x ≤ s ∧ angular N x ∈ B})
      (𝓝[>] (0 : ℝ))
      (nhds (ENNReal.ofReal (powerSingularityConstant A N π) *
        normalizedAngularLaw N B)) := by
  have hy := tendsto_exp_mul_invariant_smallBall_angular
    hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport hBm hB
  have hlog : Filter.Tendsto (fun s : ℝ => -Real.log s)
      (𝓝[>] (0 : ℝ)) Filter.atTop :=
    Filter.tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  apply (hy.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 < s := hs
  have hpow : Real.exp (cramerExponent A N * (-Real.log s)) =
      s ^ (-cramerExponent A N) := by
    rw [Real.rpow_def_of_pos hs0]
    congr 1
    ring
  have hradius : Real.exp (- -Real.log s) = s := by
    simp only [neg_neg, Real.exp_log hs0]
  simp only [Function.comp_apply]
  rw [hpow, hradius]

/-- The invariant law's full small-ball tail has Cramér exponent
`cramerExponent A N` and positive coefficient `powerSingularityConstant A N π`. -/
theorem tendsto_rpow_neg_mul_invariant_smallBall
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    Filter.Tendsto
      (fun s =>
        ENNReal.ofReal (s ^ (-cramerExponent A N)) *
          π {x | 0 < gaussianEuclideanNorm N x ∧
            gaussianEuclideanNorm N x ≤ s})
      (𝓝[>] (0 : ℝ))
      (nhds (ENNReal.ofReal (powerSingularityConstant A N π))) := by
  letI : IsProbabilityMeasure (normalizedAngularLaw N) :=
    isProbabilityMeasure_normalizedAngularLaw (by omega)
  simpa only [Set.mem_univ, and_true, measure_univ, mul_one] using
    (tendsto_rpow_neg_mul_invariant_smallBall_angular
      hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport
      (B := Set.univ) MeasurableSet.univ (by simp))

/-- Paper-facing capstone for `thm:nd-power-singularity`: the singularity
coefficient is positive, every measurable angular continuity set has the
directional power tail, and the full small ball has the same radial exponent. -/
theorem invariant_powerSingularity
    {A : ℝ} (hA1 : 1 < A) {N : ℕ} (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    0 < powerSingularityConstant A N π ∧
      (∀ (B : Set (EuclideanSpace ℝ (Fin N))), MeasurableSet B →
        normalizedAngularLaw N (frontier B) = 0 →
        Filter.Tendsto
          (fun s =>
            ENNReal.ofReal (s ^ (-cramerExponent A N)) *
              π {x | 0 < gaussianEuclideanNorm N x ∧
                gaussianEuclideanNorm N x ≤ s ∧ angular N x ∈ B})
          (𝓝[>] (0 : ℝ))
          (nhds (ENNReal.ofReal (powerSingularityConstant A N π) *
            normalizedAngularLaw N B))) ∧
      Filter.Tendsto
        (fun s =>
          ENNReal.ofReal (s ^ (-cramerExponent A N)) *
            π {x | 0 < gaussianEuclideanNorm N x ∧
              gaussianEuclideanNorm N x ≤ s})
        (𝓝[>] (0 : ℝ))
        (nhds (ENNReal.ofReal (powerSingularityConstant A N π))) := by
  refine ⟨powerSingularityConstant_pos
    hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport, ?_, ?_⟩
  · intro B hBm hB
    exact tendsto_rpow_neg_mul_invariant_smallBall_angular
      hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport hBm hB
  · exact tendsto_rpow_neg_mul_invariant_smallBall
      hA1 hN hdim hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport

end AbsorptionCutoff
