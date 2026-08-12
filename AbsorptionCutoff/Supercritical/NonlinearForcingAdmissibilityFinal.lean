/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.NonlinearForcingAdmissibilityAssembly

/-!
# Final assembly of nonlinear forcing admissibility

This continuation module carries the forcing d.R.i., continuity, and positivity
conclusions for `prop:nd-forcing-admissibility`.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- A bounded threshold integral is continuous at every level which the
threshold avoids almost everywhere. -/
lemma continuousAt_integral_ite_lt_of_ae_ne
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → ℝ} (hF : Measurable F) {T : α → ℝ} (hT : Measurable T)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ q, |F q| ≤ C) (y : ℝ)
    (hne : ∀ᵐ q ∂μ, T q ≠ y) :
    ContinuousAt (fun y' => ∫ q, if y' < T q then F q else 0 ∂μ) y := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · filter_upwards [] with y'
    exact (Measurable.ite
      (measurableSet_lt measurable_const hT) hF measurable_const).aestronglyMeasurable
  · filter_upwards [] with y'
    exact Filter.Eventually.of_forall fun q => by
      split
      · simpa [Real.norm_eq_abs] using hbound q
      · simpa using hC
  · exact integrable_const C
  · filter_upwards [hne] with q hq
    rcases lt_or_gt_of_ne hq.symm with hy | hy
    · apply tendsto_const_nhds.congr'
      filter_upwards [Iio_mem_nhds hy] with y' hy'
      change y' < T q at hy'
      simp [hy', hy]
    · apply tendsto_const_nhds.congr'
      filter_upwards [Ioi_mem_nhds hy] with y' hy'
      change T q < y' at hy'
      simp [not_lt_of_ge hy.le, not_lt_of_ge hy'.le]

/-- Every radial fibre is null under a nondegenerate product Gaussian law. -/
lemma measure_set_gaussianEuclideanNorm_eq_pi_gaussianReal
    {N : ℕ} (hN : 0 < N) {σ2 : NNReal} (hσ : σ2 ≠ 0) (r : ℝ) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 σ2)
      {v | gaussianEuclideanNorm N v = r} = 0 := by
  have hvol : (volume : Measure (Fin N → ℝ)) ≪ gaussianVec N := by
    rw [gaussianVec, pi_gaussianReal_eq_withDensity (N := N) one_ne_zero]
    apply withDensity_absolutelyContinuous'
    · exact (Finset.measurable_prod _ fun i _ =>
        (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)).aemeasurable
    · filter_upwards [] with v
      exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        ne_of_gt (gaussianPDF_pos 0 one_ne_zero (v i))
  have hac :
      (Measure.pi fun _ : Fin N => gaussianReal 0 σ2) ≪ gaussianVec N := by
    rw [pi_gaussianReal_eq_withDensity hσ]
    exact (withDensity_absolutelyContinuous volume _).trans hvol
  apply hac
  apply measure_mono_null
    (t := gaussianSquaredNorm N ⁻¹' {r ^ 2}) _
    (measure_preimage_gaussianSquaredNorm_singleton hN (r ^ 2))
  intro v hv
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff] at hv ⊢
  have hsq : gaussianSquaredNorm N v = gaussianEuclideanNorm N v ^ 2 := by
    unfold gaussianEuclideanNorm
    rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N v)]
  rw [hsq, hv]

/-- Every radial fibre is null under the coordinatewise `tanhScale` pushforward
of a nondegenerate product Gaussian law. -/
lemma measure_set_gaussianEuclideanNorm_eq_map_tanhScaleVec_pi_gaussianReal
    {N : ℕ} (hN : 0 < N) {σ2 : NNReal} (hσ : σ2 ≠ 0)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i))
      (Measure.pi fun _ : Fin N => gaussianReal 0 σ2))
        {v | gaussianEuclideanNorm N v = R} = 0 := by
  have hvol : (volume : Measure (Fin N → ℝ)) ≪ gaussianVec N := by
    rw [gaussianVec, pi_gaussianReal_eq_withDensity (N := N) one_ne_zero]
    apply withDensity_absolutelyContinuous'
    · exact (Finset.measurable_prod _ fun i _ =>
        (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)).aemeasurable
    · filter_upwards [] with v
      exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        ne_of_gt (gaussianPDF_pos 0 one_ne_zero (v i))
  rw [map_tanhScaleVec_pi_gaussianReal_eq_withDensity hσ hr]
  apply (withDensity_absolutelyContinuous volume _).trans hvol
  apply measure_mono_null
    (t := gaussianSquaredNorm N ⁻¹' {R ^ 2}) _
    (measure_preimage_gaussianSquaredNorm_singleton hN (R ^ 2))
  intro v hv
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff] at hv ⊢
  have hsq : gaussianSquaredNorm N v = gaussianEuclideanNorm N v ^ 2 := by
    unfold gaussianEuclideanNorm
    rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N v)]
  rw [hsq, hv]

/-- At a unit direction, every radial fibre of `Wθ` is null under the Gaussian
matrix law. -/
lemma measure_set_gaussianEuclideanNorm_mulVec_eq_gaussianMat
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0)
    (θ : EuclideanSpace ℝ (Fin N)) (hθ : ‖θ‖ = 1) (r : ℝ) :
    gaussianMat A N
      {W | gaussianEuclideanNorm N (Matrix.mulVec W (WithLp.ofLp θ)) = r} = 0 := by
  let mulTheta : (Fin N → Fin N → ℝ) → (Fin N → ℝ) :=
    fun W i => ∑ j, W i j * WithLp.ofLp θ j
  have hmul : Measurable mulTheta := by
    exact measurable_pi_iff.mpr fun i =>
      Finset.measurable_sum _ fun j _ => by fun_prop
  have hset : MeasurableSet {v : Fin N → ℝ | gaussianEuclideanNorm N v = r} :=
    (measurableSet_singleton r).preimage (measurable_gaussianEuclideanNorm N)
  change gaussianMat A N
    (mulTheta ⁻¹' {v : Fin N → ℝ | gaussianEuclideanNorm N v = r}) = 0
  rw [← Measure.map_apply hmul hset]
  change (Measure.map (fun W i => ∑ j, W i j * WithLp.ofLp θ j)
    (gaussianMat A N)) {v | gaussianEuclideanNorm N v = r} = 0
  rw [map_mulVec_gaussianMat_of_norm_eq_one A θ hθ]
  exact measure_set_gaussianEuclideanNorm_eq_pi_gaussianReal hN hσ r

/-- The linearized log-radius threshold avoids every fixed level almost surely
under the log-polar/Gaussian product law. -/
lemma ae_linearizedLogRadiusThreshold_ne
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0)
    (π : Measure (Fin N → ℝ))
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0) (y : ℝ) :
    ∀ᵐ q ∂(logPolarLaw N π).prod (gaussianMat A N),
      q.1.1 - Real.log (gaussianEuclideanNorm N
        (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) ≠ y := by
  have hv : Measurable fun q :
      (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      Matrix.mulVec q.2 (WithLp.ofLp q.1.2) :=
    (measurable_mulVec_ofLp N).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hT : Measurable fun q :
      (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      q.1.1 - Real.log (gaussianEuclideanNorm N
        (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) :=
    (measurable_fst.comp measurable_fst).sub
      (((measurable_gaussianEuclideanNorm N).comp hv).log)
  have hlevel : MeasurableSet {q :
      (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) |
      q.1.1 - Real.log (gaussianEuclideanNorm N
        (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) ≠ y} :=
    (measurableSet_singleton y).compl.preimage hT
  apply (Measure.ae_prod_iff_ae_ae hlevel).2
  filter_upwards [ae_norm_snd_logPolarLaw_eq_one N π horigin] with p hp
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null
    (t := {W | gaussianEuclideanNorm N
      (Matrix.mulVec W (WithLp.ofLp p.2)) = Real.exp (p.1 - y)} ∪
      {W | gaussianEuclideanNorm N
        (Matrix.mulVec W (WithLp.ofLp p.2)) = 0}) ?_
    (measure_union_null
      (measure_set_gaussianEuclideanNorm_mulVec_eq_gaussianMat
        A hN hσ p.2 hp (Real.exp (p.1 - y)))
      (measure_set_gaussianEuclideanNorm_mulVec_eq_gaussianMat
        A hN hσ p.2 hp 0))
  intro W hW
  by_cases hzero : gaussianEuclideanNorm N
      (Matrix.mulVec W (WithLp.ofLp p.2)) = 0
  · exact Or.inr hzero
  · apply Or.inl
    have hnonneg : 0 ≤ gaussianEuclideanNorm N
        (Matrix.mulVec W (WithLp.ofLp p.2)) := by
      unfold gaussianEuclideanNorm
      positivity
    have hpos : 0 < gaussianEuclideanNorm N
        (Matrix.mulVec W (WithLp.ofLp p.2)) :=
      lt_of_le_of_ne hnonneg (Ne.symm hzero)
    have hW' : p.1 - Real.log (gaussianEuclideanNorm N
        (Matrix.mulVec W (WithLp.ofLp p.2))) = y := by
      apply of_not_not
      exact hW
    have hlog : Real.log (gaussianEuclideanNorm N
        (Matrix.mulVec W (WithLp.ofLp p.2))) = p.1 - y := by
      linarith
    calc
      gaussianEuclideanNorm N (Matrix.mulVec W (WithLp.ofLp p.2)) =
          Real.exp (Real.log (gaussianEuclideanNorm N
            (Matrix.mulVec W (WithLp.ofLp p.2)))) := (Real.exp_log hpos).symm
      _ = Real.exp (p.1 - y) := by rw [hlog]

/-- The nonlinear log-radius threshold avoids every fixed level almost surely
under the log-polar/Gaussian product law. -/
lemma ae_logPolarStep_fst_ne
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0)
    (π : Measure (Fin N → ℝ))
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0) (y : ℝ) :
    ∀ᵐ q ∂(logPolarLaw N π).prod (gaussianMat A N),
      (logPolarStep N q.1.1 q.1.2 q.2).1 ≠ y := by
  have hlevel : MeasurableSet {q :
      (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) |
      (logPolarStep N q.1.1 q.1.2 q.2).1 ≠ y} :=
    (measurableSet_singleton y).compl.preimage (measurable_logPolarStep_fst N)
  apply (Measure.ae_prod_iff_ae_ae hlevel).2
  filter_upwards [ae_norm_snd_logPolarLaw_eq_one N π horigin] with p hp
  let mulTheta : (Fin N → Fin N → ℝ) → (Fin N → ℝ) :=
    fun W i => ∑ j, W i j * WithLp.ofLp p.2 j
  let T : (Fin N → ℝ) → (Fin N → ℝ) :=
    fun v i => tanhScale (Real.exp (-p.1)) (v i)
  have hmul : Measurable mulTheta := by
    exact measurable_pi_iff.mpr fun i =>
      Finset.measurable_sum _ fun j _ => by fun_prop
  have hT : Measurable T := by
    exact measurable_pi_iff.mpr fun i =>
      (measurable_tanhScale (Real.exp (-p.1))).comp (measurable_pi_apply i)
  have hrad (R : ℝ) : MeasurableSet
      {v : Fin N → ℝ | gaussianEuclideanNorm N v = R} :=
    (measurableSet_singleton R).preimage (measurable_gaussianEuclideanNorm N)
  have htrans (R : ℝ) : gaussianMat A N
      {W | gaussianEuclideanNorm N (T (mulTheta W)) = R} = 0 := by
    change gaussianMat A N
      (mulTheta ⁻¹' (T ⁻¹' {v | gaussianEuclideanNorm N v = R})) = 0
    rw [← Measure.map_apply hmul (hT (hrad R))]
    change (Measure.map (fun W i => ∑ j, W i j * WithLp.ofLp p.2 j)
      (gaussianMat A N)) (T ⁻¹' {v | gaussianEuclideanNorm N v = R}) = 0
    rw [map_mulVec_gaussianMat_of_norm_eq_one A p.2 hp]
    rw [← Measure.map_apply hT (hrad R)]
    exact measure_set_gaussianEuclideanNorm_eq_map_tanhScaleVec_pi_gaussianReal
      hN hσ (Real.exp_pos (-p.1)) R
  have hzero : gaussianMat A N {W | mulTheta W = 0} = 0 := by
    apply measure_mono_null
      (t := {W | gaussianEuclideanNorm N (mulTheta W) = 0}) ?_
      (measure_set_gaussianEuclideanNorm_mulVec_eq_gaussianMat
        A hN hσ p.2 hp 0)
    intro W hW
    exact (gaussianEuclideanNorm_eq_zero_iff N (mulTheta W)).2 hW
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null
    (t := {W | gaussianEuclideanNorm N
        (T (mulTheta W)) = Real.exp (p.1 - y)} ∪
      {W | mulTheta W = 0}) ?_
    (measure_union_null (htrans (Real.exp (p.1 - y))) hzero)
  intro W hW
  by_cases hv : mulTheta W = 0
  · exact Or.inr hv
  · apply Or.inl
    have hstep : (logPolarStep N p.1 p.2 W).1 = y := by
      apply of_not_not
      exact hW
    let r := Real.exp (-p.1)
    let v := mulTheta W
    let u := T v
    have hr : 0 < r := Real.exp_pos (-p.1)
    have htanh : tanhVec N (r • v) = r • u := by
      funext i
      simp only [tanhVec, Pi.smul_apply, smul_eq_mul, r, v, u, T, tanhScale]
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
    have hlog : Real.log (gaussianEuclideanNorm N u) = p.1 - y := by
      simp only [logPolarStep_fst] at hstep
      rw [show Matrix.mulVec W (WithLp.ofLp p.2) = v by rfl] at hstep
      change p.1 - Real.log (gaussianEuclideanNorm N v) + etaDefect N r v = y at hstep
      have hstep' : p.1 +
          (-Real.log (gaussianEuclideanNorm N v) + etaDefect N r v) = y := by
        linarith
      rw [hthreshold] at hstep'
      linarith
    change gaussianEuclideanNorm N u = Real.exp (p.1 - y)
    calc
      gaussianEuclideanNorm N u = Real.exp (Real.log (gaussianEuclideanNorm N u)) :=
        (Real.exp_log hupos).symm
      _ = Real.exp (p.1 - y) := by rw [hlog]

/-- For every bounded measurable angular test, the nonlinear renewal forcing
is continuous in its log-radius level. -/
theorem continuous_nonlinearForcing
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (β : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφ : Measurable φ) (hφ1 : ∀ z, |φ z| ≤ 1) :
    Continuous (fun y => nonlinearForcing A N π β y φ) := by
  have hplus : Continuous (fun y =>
      ∫ q, nonlinearForcingPlusIntegrand N y φ q
        ∂(logPolarLaw N π).prod (gaussianMat A N)) := by
    rw [continuous_iff_continuousAt]
    intro y
    unfold nonlinearForcingPlusIntegrand
    exact continuousAt_integral_ite_lt_of_ae_ne
      ((logPolarLaw N π).prod (gaussianMat A N))
      (hφ.comp (measurable_logPolarStep_snd N))
      (measurable_logPolarStep_fst N) zero_le_one (fun q => hφ1 _) y
      (ae_logPolarStep_fst_ne A hN hσ π horigin y)
  have hv : Measurable fun q :
      (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      Matrix.mulVec q.2 (WithLp.ofLp q.1.2) :=
    (measurable_mulVec_ofLp N).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hzero : Continuous (fun y =>
      ∫ q, nonlinearForcingZeroIntegrand N y φ q
        ∂(logPolarLaw N π).prod (gaussianMat A N)) := by
    rw [continuous_iff_continuousAt]
    intro y
    unfold nonlinearForcingZeroIntegrand
    exact continuousAt_integral_ite_lt_of_ae_ne
      ((logPolarLaw N π).prod (gaussianMat A N))
      (hφ.comp ((measurable_angularZero N).comp hv))
      ((measurable_fst.comp measurable_fst).sub
        (((measurable_gaussianEuclideanNorm N).comp hv).log))
      zero_le_one (fun q => hφ1 _) y
      (ae_linearizedLogRadiusThreshold_ne A hN hσ π horigin y)
  unfold nonlinearForcing
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (hplus.sub hzero)

/-- Under the origin-free log-polar law, the Gaussian image `WΘ` is nonzero
almost surely. -/
lemma ae_mulVec_ne_zero_logPolarLaw_prod_gaussianMat
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0)
    (π : Measure (Fin N → ℝ))
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0) :
    ∀ᵐ q ∂(logPolarLaw N π).prod (gaussianMat A N),
      Matrix.mulVec q.2 (WithLp.ofLp q.1.2) ≠ 0 := by
  have hv : Measurable fun q :
      (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      Matrix.mulVec q.2 (WithLp.ofLp q.1.2) :=
    (measurable_mulVec_ofLp N).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hlevel : MeasurableSet {q :
      (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) |
      Matrix.mulVec q.2 (WithLp.ofLp q.1.2) ≠ 0} :=
    (measurableSet_singleton (0 : Fin N → ℝ)).compl.preimage hv
  apply (Measure.ae_prod_iff_ae_ae hlevel).2
  filter_upwards [ae_norm_snd_logPolarLaw_eq_one N π horigin] with p hp
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null
    (t := {W | gaussianEuclideanNorm N
      (Matrix.mulVec W (WithLp.ofLp p.2)) = 0}) ?_
    (measure_set_gaussianEuclideanNorm_mulVec_eq_gaussianMat
      A hN hσ p.2 hp 0)
  intro W hW
  exact (gaussianEuclideanNorm_eq_zero_iff N _).2 (of_not_not hW)

/-- At the constant-one angular test, the nonlinear renewal forcing is
nonnegative at every log-radius level. -/
theorem nonlinearForcing_one_nonneg
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (β y : ℝ) :
    0 ≤ nonlinearForcing A N π β y (fun _ => 1) := by
  have hne : ∀ᵐ q ∂(logPolarLaw N π).prod (gaussianMat A N),
      Matrix.mulVec q.2 (WithLp.ofLp q.1.2) ≠ 0 :=
    ae_mulVec_ne_zero_logPolarLaw_prod_gaussianMat A hN hσ π horigin
  have hpoint : ∀ᵐ q ∂(logPolarLaw N π).prod (gaussianMat A N),
      nonlinearForcingZeroIntegrand N y (fun _ => 1) q ≤
        nonlinearForcingPlusIntegrand N y (fun _ => 1) q := by
    filter_upwards [hne] with q hq
    let v := Matrix.mulVec q.2 (WithLp.ofLp q.1.2)
    let r := Real.exp (-q.1.1)
    have hr : 0 < r := Real.exp_pos (-q.1.1)
    have htanh : tanhVec N (r • v) ≠ 0 := by
      intro h
      have hsmul : r • v = 0 := (tanhVec_eq_zero_iff N (r • v)).1 h
      exact (not_or_intro hr.ne' hq) (smul_eq_zero.mp hsmul)
    have heta : 0 ≤ etaDefect N r v :=
      etaDefect_nonneg N hr
        ((gaussianEuclideanNorm_eq_zero_iff N _).not.mpr htanh)
    change (if y < q.1.1 - Real.log (gaussianEuclideanNorm N v) then 1 else 0) ≤
      if y < (logPolarStep N q.1.1 q.1.2 q.2).1 then 1 else 0
    by_cases hlin : y < q.1.1 - Real.log (gaussianEuclideanNorm N v)
    · have hplus : y < (logPolarStep N q.1.1 q.1.2 q.2).1 := by
        simp only [logPolarStep_fst]
        change y < q.1.1 - Real.log (gaussianEuclideanNorm N v) + etaDefect N r v
        linarith
      change y < q.1.1 - Real.log (gaussianEuclideanNorm N
          (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) +
        etaDefect N (Real.exp (-q.1.1))
          (Matrix.mulVec q.2 (WithLp.ofLp q.1.2)) at hplus
      simp [hlin, hplus]
    · rw [if_neg hlin]
      split <;> norm_num
  have hint := integral_mono_ae
    (integrable_nonlinearForcingZeroIntegrand A N y 1 measurable_const (fun _ => by simp))
    (integrable_nonlinearForcingPlusIntegrand A N y 1 measurable_const (fun _ => by simp))
    hpoint
  unfold nonlinearForcing
  exact mul_nonneg (Real.exp_nonneg _) (sub_nonneg.mpr hint)

/-- The scalar exponential layer integral used in the Tonelli computation of
the constant-one forcing mass. -/
lemma intervalIntegral_exp_mul_add
    {β : ℝ} (hβ : 0 < β) (b η : ℝ) :
    (∫ y in b..(b + η), Real.exp (β * y)) =
      Real.exp (β * b) * (Real.exp (β * η) - 1) / β := by
  calc
    (∫ y in b..(b + η), Real.exp (β * y)) =
        Real.exp (β * (b + η)) / β - Real.exp (β * b) / β := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun y => Real.exp (β * y) / β)
        (f' := fun y => Real.exp (β * y))
        (fun y _ => by
          simpa [hβ.ne'] using (((Real.hasDerivAt_exp (β * y)).comp y
            ((hasDerivAt_const y β).mul (hasDerivAt_id y))).div_const β))
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id) :
          Continuous (fun y : ℝ => Real.exp (β * y))).intervalIntegrable b (b + η))
    _ = Real.exp (β * b) * (Real.exp (β * η) - 1) / β := by
      rw [mul_add, Real.exp_add]
      field_simp

/-- Set-integral form of `intervalIntegral_exp_mul_add`, for the nonnegative
layers produced by `etaDefect_nonneg`. -/
lemma integral_exp_mul_Ioc_add
    {β : ℝ} (hβ : 0 < β) (b : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (∫ y in Set.Ioc b (b + η), Real.exp (β * y)) =
      Real.exp (β * b) * (Real.exp (β * η) - 1) / β := by
  rw [← intervalIntegral.integral_of_le (by linarith : b ≤ b + η)]
  exact intervalIntegral_exp_mul_add hβ b η

/-- The `Ico` endpoint convention arising exactly from the difference
`1_{y < b + η} - 1_{y < b}` has the same exponential layer integral. -/
lemma integral_exp_mul_Ico_add
    {β : ℝ} (hβ : 0 < β) (b : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (∫ y in Set.Ico b (b + η), Real.exp (β * y)) =
      Real.exp (β * b) * (Real.exp (β * η) - 1) / β := by
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
  exact integral_exp_mul_Ioc_add hβ b hη

/-- The difference of two nested threshold indicators is the indicator of the
half-open layer between them. -/
lemma exp_mul_ite_lt_sub_ite_lt_eq_indicator_Ico
    (β y b η : ℝ) (hη : 0 ≤ η) :
    Real.exp (β * y) *
        ((if y < b + η then 1 else 0) - (if y < b then 1 else 0)) =
      Set.indicator (Set.Ico b (b + η)) (fun y => Real.exp (β * y)) y := by
  by_cases hb : y < b
  · have htop : y < b + η := by linarith
    simp [hb, htop, Set.mem_Ico]
  · have hble : b ≤ y := le_of_not_gt hb
    by_cases htop : y < b + η
    · simp [hb, htop, Set.mem_Ico, hble]
    · simp [hb, htop, Set.mem_Ico]

/-- Away from the null vector `WΘ = 0`, the constant-one forcing integrand is
exactly the nonnegative exponential layer between the linearized and nonlinear
log-radius thresholds. -/
lemma exp_mul_nonlinearForcingIntegrand_one_sub_eq_indicator_Ico
    (N : ℕ) (β y : ℝ)
    (q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ))
    (hq : Matrix.mulVec q.2 (WithLp.ofLp q.1.2) ≠ 0) :
    Real.exp (β * y) *
        (nonlinearForcingPlusIntegrand N y (fun _ => 1) q -
          nonlinearForcingZeroIntegrand N y (fun _ => 1) q) =
      Set.indicator
        (Set.Ico
          (q.1.1 - Real.log (gaussianEuclideanNorm N
            (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))))
          (q.1.1 - Real.log (gaussianEuclideanNorm N
              (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) +
            etaDefect N (Real.exp (-q.1.1))
              (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))))
        (fun y => Real.exp (β * y)) y := by
  let v := Matrix.mulVec q.2 (WithLp.ofLp q.1.2)
  let r := Real.exp (-q.1.1)
  have hr : 0 < r := Real.exp_pos (-q.1.1)
  have htanh : tanhVec N (r • v) ≠ 0 := by
    intro h
    have hsmul : r • v = 0 := (tanhVec_eq_zero_iff N (r • v)).1 h
    exact (not_or_intro hr.ne' hq) (smul_eq_zero.mp hsmul)
  have heta : 0 ≤ etaDefect N r v :=
    etaDefect_nonneg N hr
      ((gaussianEuclideanNorm_eq_zero_iff N _).not.mpr htanh)
  simpa only [nonlinearForcingPlusIntegrand, nonlinearForcingZeroIntegrand,
    logPolarStep_fst] using
    exp_mul_ite_lt_sub_ite_lt_eq_indicator_Ico β y
      (q.1.1 - Real.log (gaussianEuclideanNorm N v)) (etaDefect N r v) heta

/-- Every bounded measurable angular test gives a nonlinear forcing with finite
d.R.i. norm after exponential tilting. -/
theorem driNorm_ofReal_abs_nonlinearForcing_ne_top
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1)
    {φ : EuclideanSpace ℝ (Fin N) → ℝ} (hφ : Measurable φ)
    (hφ1 : ∀ z, |φ z| ≤ 1) :
    Renewal.driNorm
      (fun y => ENNReal.ofReal
        |nonlinearForcing A N π (cramerExponent A N) y φ|) ≠ ⊤ := by
  obtain ⟨C, hC, _, hbound⟩ :=
    exists_abs_nonlinearForcing_le_integral_polarEnvelope_of_invariant_Pkernel
      hA hN hsc hδ0 hδ2 hδβ π hπ hπ0 hsupport
  let G : ℝ → ENNReal := fun y => ∫⁻ p,
    ENNReal.ofReal (Real.exp ((cramerExponent A N - δ) * p.1)) *
      ENNReal.ofReal
        (Real.exp (cramerExponent A N * (y - p.1)) *
          polarEnvelope N (y - p.1)) ∂logPolarLaw N π
  have hG : Renewal.driNorm G ≠ ⊤ := by
    exact driNorm_lintegral_exp_tilt_mul_polarEnvelope_of_invariant_Pkernel_ne_top
      hA hN hsc hδ0 hδβ π hπ hπ0
  have hpoint (y : ℝ) :
      ENNReal.ofReal
          |nonlinearForcing A N π (cramerExponent A N) y φ| ≤
        ENNReal.ofReal C * G y := by
    have hi := integrable_rpow_mul_polarEnvelope_of_invariant_Pkernel
      hA hN hsc hδ0 hδβ π hπ hπ0 y
    have htilt : Integrable
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) =>
          Real.exp ((cramerExponent A N - δ) * p.1) *
            (Real.exp (cramerExponent A N * (y - p.1)) *
              polarEnvelope N (y - p.1)))
        (logPolarLaw N π) := by
      apply (hi.const_mul (Real.exp (cramerExponent A N * y))).congr
      filter_upwards [] with p
      exact exp_mul_rpow_polarEnvelope_eq_tilted N
        (cramerExponent A N) δ y p.1
    have hre :
        Real.exp (cramerExponent A N * y) *
            ∫ p, Real.exp (-p.1) ^ δ * polarEnvelope N (y - p.1)
              ∂logPolarLaw N π =
          ∫ p, Real.exp ((cramerExponent A N - δ) * p.1) *
            (Real.exp (cramerExponent A N * (y - p.1)) *
              polarEnvelope N (y - p.1)) ∂logPolarLaw N π := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      exact exp_mul_rpow_polarEnvelope_eq_tilted N
        (cramerExponent A N) δ y p.1
    have hb := hbound y hφ hφ1
    rw [mul_assoc, hre] at hb
    have hof := ENNReal.ofReal_le_ofReal hb
    rw [ENNReal.ofReal_mul hC,
      ofReal_integral_eq_lintegral_ofReal htilt
        (Filter.Eventually.of_forall fun p =>
          mul_nonneg (Real.exp_nonneg _)
            (mul_nonneg (Real.exp_nonneg _) (polarEnvelope_nonneg N _)))] at hof
    simpa only [G, ENNReal.ofReal_mul (Real.exp_nonneg _)] using hof
  apply ne_top_of_le_ne_top _ (Renewal.driNorm_mono hpoint)
  apply ne_top_of_le_ne_top _ (Renewal.driNorm_const_mul_le (ENNReal.ofReal C) G)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG

/-- Tonelli's identity for the total mass of the constant-one nonlinear
renewal forcing. -/
theorem integral_nonlinearForcing_one
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    (∫ y, nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1)) =
      (cramerExponent A N)⁻¹ *
        ∫ q, Real.exp (cramerExponent A N *
              (q.1.1 - Real.log (gaussianEuclideanNorm N
                (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))))) *
            (Real.exp (cramerExponent A N *
              etaDefect N (Real.exp (-q.1.1))
                (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) - 1)
          ∂(logPolarLaw N π).prod (gaussianMat A N) := by
  let μq := (logPolarLaw N π).prod (gaussianMat A N)
  let β := cramerExponent A N
  let F : ℝ × ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) → ℝ :=
    fun z => Real.exp (β * z.1) *
      (nonlinearForcingPlusIntegrand N z.1 (fun _ => 1) z.2 -
        nonlinearForcingZeroIntegrand N z.1 (fun _ => 1) z.2)
  have hA0 : 0 < A := hA
  have hN0 : 0 < N := hN
  have hβ : 0 < β := (cramerExponent_mem hA0 hN0 hsc).1
  have hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  have horigin : π {x | gaussianEuclideanNorm N x = 0} = 0 := by
    rw [show {x | gaussianEuclideanNorm N x = 0} = ({0} : Set (Fin N → ℝ)) by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
        gaussianEuclideanNorm_eq_zero_iff N]]
    exact hπ0
  have hFmeas : Measurable F := by
    have hv : Measurable fun z :
        ℝ × ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) =>
        Matrix.mulVec z.2.2 (WithLp.ofLp z.2.1.2) :=
      (measurable_mulVec_ofLp N).comp
        ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))
    have hp : Measurable fun z :
        ℝ × ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) =>
        nonlinearForcingPlusIntegrand N z.1 (fun _ => 1) z.2 := by
      unfold nonlinearForcingPlusIntegrand
      exact Measurable.ite
        (measurableSet_lt measurable_fst
          ((measurable_logPolarStep_fst N).comp measurable_snd))
        measurable_const measurable_const
    have hz : Measurable fun z :
        ℝ × ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) =>
        nonlinearForcingZeroIntegrand N z.1 (fun _ => 1) z.2 := by
      unfold nonlinearForcingZeroIntegrand
      exact Measurable.ite
        (measurableSet_lt measurable_fst
          (((measurable_fst.comp measurable_fst).comp measurable_snd).sub
            (((measurable_gaussianEuclideanNorm N).comp hv).log)))
        measurable_const measurable_const
    exact ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (hp.sub hz))
  have hFnonneg_all (y : ℝ) : ∀ᵐ q ∂μq, 0 ≤ F (y, q) := by
    filter_upwards [ae_mulVec_ne_zero_logPolarLaw_prod_gaussianMat
      A hN0 hσ π horigin] with q hq
    rw [show F (y, q) = Real.exp (β * y) *
      (nonlinearForcingPlusIntegrand N y (fun _ => 1) q -
        nonlinearForcingZeroIntegrand N y (fun _ => 1) q) by rfl]
    rw [exp_mul_nonlinearForcingIntegrand_one_sub_eq_indicator_Ico N β y q hq]
    exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
  have hFfiber (y : ℝ) :
      ∫ q, F (y, q) ∂μq =
        nonlinearForcing A N π β y (fun _ => 1) := by
    have hp := integrable_nonlinearForcingPlusIntegrand
      A N (π := π) (φ := fun _ => 1) y 1 measurable_const (fun _ => by norm_num)
    have hz := integrable_nonlinearForcingZeroIntegrand
      A N (π := π) (φ := fun _ => 1) y 1 measurable_const (fun _ => by norm_num)
    rw [show (fun q => F (y, q)) = fun q => Real.exp (β * y) *
      (nonlinearForcingPlusIntegrand N y (fun _ => 1) q -
        nonlinearForcingZeroIntegrand N y (fun _ => 1) q) by rfl,
      integral_const_mul, integral_sub hp hz]
    rfl
  have hψcont : Continuous (fun y => nonlinearForcing A N π β y (fun _ => 1)) :=
    continuous_nonlinearForcing A hN0 hσ π horigin β
      (φ := fun _ => 1) measurable_const (fun _ => by norm_num)
  have hψint : Integrable (fun y => nonlinearForcing A N π β y (fun _ => 1)) := by
    refine ⟨hψcont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hψnonneg (y : ℝ) :
        0 ≤ nonlinearForcing A N π β y (fun _ => 1) :=
      nonlinearForcing_one_nonneg A hN0 hσ π horigin β y
    calc
      (∫⁻ y, ‖nonlinearForcing A N π β y (fun _ => 1)‖ₑ) =
          ∫⁻ y, ENNReal.ofReal
            |nonlinearForcing A N π β y (fun _ => 1)| := by
        apply lintegral_congr
        intro y
        rw [Real.enorm_eq_ofReal (hψnonneg y), abs_of_nonneg (hψnonneg y)]
      _ ≤ Renewal.driNorm (fun y => ENNReal.ofReal
            |nonlinearForcing A N π β y (fun _ => 1)|) :=
        Renewal.lintegral_le_driNorm _
      _ < ⊤ := lt_top_iff_ne_top.mpr
        (driNorm_ofReal_abs_nonlinearForcing_ne_top hA hN hsc
          hδ0 hδ2 hδβ π hπ hπ0 hsupport (φ := fun _ => 1)
          measurable_const (fun _ => by norm_num))
  have hFint : Integrable F (volume.prod μq) := by
    rw [integrable_prod_iff hFmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [] with y
      have hi := ((integrable_nonlinearForcingPlusIntegrand
          A N (π := π) (φ := fun _ => 1) y 1
            measurable_const (fun _ => by norm_num)).sub
        (integrable_nonlinearForcingZeroIntegrand
          A N (π := π) (φ := fun _ => 1) y 1
            measurable_const (fun _ => by norm_num))).const_mul (Real.exp (β * y))
      simpa only [F, μq, Pi.sub_apply] using hi
    · apply hψint.congr
      filter_upwards [] with y
      rw [← hFfiber y]
      apply integral_congr_ae
      filter_upwards [hFnonneg_all y] with q hq
      rw [Real.norm_eq_abs, abs_of_nonneg hq]
  have hmain :
      (∫ y, nonlinearForcing A N π β y (fun _ => 1)) =
        β⁻¹ * ∫ q, Real.exp (β *
              (q.1.1 - Real.log (gaussianEuclideanNorm N
                (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))))) *
            (Real.exp (β * etaDefect N (Real.exp (-q.1.1))
              (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) - 1) ∂μq := by
    calc
      (∫ y, nonlinearForcing A N π β y (fun _ => 1)) =
          ∫ y, ∫ q, F (y, q) ∂μq :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => (hFfiber y).symm)
      _ = ∫ q, (∫ y, F (y, q) ∂volume) ∂μq :=
        integral_integral_swap (f := fun y q => F (y, q)) hFint
      _ = ∫ q, β⁻¹ * (Real.exp (β *
              (q.1.1 - Real.log (gaussianEuclideanNorm N
                (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))))) *
            (Real.exp (β * etaDefect N (Real.exp (-q.1.1))
              (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) - 1)) ∂μq := by
        apply integral_congr_ae
        filter_upwards [ae_mulVec_ne_zero_logPolarLaw_prod_gaussianMat
          A hN0 hσ π horigin] with q hq
        let b := q.1.1 - Real.log (gaussianEuclideanNorm N
          (Matrix.mulVec q.2 (WithLp.ofLp q.1.2)))
        let η := etaDefect N (Real.exp (-q.1.1))
          (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))
        have hη : 0 ≤ η := by
          apply etaDefect_nonneg N (Real.exp_pos _)
          apply (gaussianEuclideanNorm_eq_zero_iff N _).not.mpr
          intro htanh
          have hs := (tanhVec_eq_zero_iff N _).1 htanh
          exact hq ((smul_eq_zero.mp hs).resolve_left (Real.exp_pos _).ne')
        rw [show (fun y => F (y, q)) = fun y => Real.exp (β * y) *
          (nonlinearForcingPlusIntegrand N y (fun _ => 1) q -
            nonlinearForcingZeroIntegrand N y (fun _ => 1) q) by rfl]
        apply Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y =>
          exp_mul_nonlinearForcingIntegrand_one_sub_eq_indicator_Ico N β y q hq))
        rw [integral_indicator measurableSet_Ico]
        rw [integral_exp_mul_Ico_add hβ b hη]
        change Real.exp (β * b) * (Real.exp (β * η) - 1) / β =
          β⁻¹ * (Real.exp (β * b) * (Real.exp (β * η) - 1))
        field_simp
      _ = β⁻¹ * ∫ q, Real.exp (β *
              (q.1.1 - Real.log (gaussianEuclideanNorm N
                (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))))) *
            (Real.exp (β * etaDefect N (Real.exp (-q.1.1))
              (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) - 1) ∂μq := by
        rw [← integral_const_mul]
  simpa only [β, μq] using hmain

/-- Away from the origin, the hyperbolic tangent strictly decreases absolute
value. -/
lemma abs_tanh_lt_abs_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    |Real.tanh x| < |x| := by
  have hpos {u : ℝ} (hu : 0 < u) : |Real.tanh u| < |u| := by
    have hratio := tanh_div_self_strictAntiOn
      (show u / 2 ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
      (show u ∈ Set.Ioi (0 : ℝ) by exact hu) (by linarith)
    have hhalf : Real.tanh (u / 2) / (u / 2) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact tanh_le_self (by linarith)
    have ht : Real.tanh u < u := (div_lt_one hu).mp (hratio.trans_le hhalf)
    have htpos : 0 < Real.tanh u := by
      simpa only [Real.tanh_zero] using strictMono_tanh_light hu
    rw [abs_of_pos hu, abs_of_pos htpos]
    exact ht
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have h := hpos (show 0 < -x by linarith)
    simpa only [Real.tanh_neg, abs_neg] using h
  · exact hpos hxpos

/-- Coordinatewise `tanh` strictly contracts Euclidean norm away from the
origin. This is the pointwise strictness input in the positivity argument for
the nonlinear renewal constant. -/
lemma gaussianEuclideanNorm_tanhVec_smul_lt
    (N : ℕ) {r : ℝ} (hr : 0 < r) {v : Fin N → ℝ} (hv : v ≠ 0) :
    gaussianEuclideanNorm N (tanhVec N (r • v)) <
      r * gaussianEuclideanNorm N v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hcoord : Real.tanh ((r • v) i) ^ 2 < ((r • v) i) ^ 2 := by
    have habs := abs_tanh_lt_abs_of_ne_zero
      (mul_ne_zero hr.ne' hi : r * v i ≠ 0)
    simpa only [Pi.smul_apply, smul_eq_mul] using (sq_lt_sq.mpr habs)
  have hsum :
      ∑ j, Real.tanh ((r • v) j) ^ 2 < ∑ j, ((r • v) j) ^ 2 := by
    apply Finset.sum_lt_sum (fun j _ => tanh_sq_le_sq ((r • v) j))
    exact ⟨i, Finset.mem_univ i, hcoord⟩
  calc
    gaussianEuclideanNorm N (tanhVec N (r • v)) <
        gaussianEuclideanNorm N (r • v) := by
      unfold gaussianEuclideanNorm gaussianSquaredNorm tanhVec
      exact Real.sqrt_lt_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _) hsum
    _ = r * gaussianEuclideanNorm N v := by
      rw [gaussianEuclideanNorm_smul, abs_of_pos hr]

/-- The nonlinear log-radius defect is strictly positive away from the origin. -/
lemma etaDefect_pos (N : ℕ) {r : ℝ} (hr : 0 < r) {v : Fin N → ℝ} (hv : v ≠ 0) :
    0 < etaDefect N r v := by
  have htan_ne : tanhVec N (r • v) ≠ 0 := by
    exact (tanhVec_eq_zero_iff N (r • v)).not.mpr
      (smul_eq_zero.not.mpr (not_or_intro hr.ne' hv))
  have htan_pos : 0 < gaussianEuclideanNorm N (tanhVec N (r • v)) :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity)
      (Ne.symm ((gaussianEuclideanNorm_eq_zero_iff N _).not.mpr htan_ne))
  unfold etaDefect
  apply Real.log_pos
  exact (one_lt_div htan_pos).mpr
    (gaussianEuclideanNorm_tanhVec_smul_lt N hr hv)

/-- The total mass of the constant-one nonlinear forcing is strictly positive.
This is the positivity clause of `prop:nd-forcing-admissibility`. -/
theorem integral_nonlinearForcing_one_pos
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    0 < ∫ y, nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1) := by
  let μq := (logPolarLaw N π).prod (gaussianMat A N)
  let β := cramerExponent A N
  let E : ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) → ℝ :=
    fun q => Real.exp (β *
        (q.1.1 - Real.log (gaussianEuclideanNorm N
          (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))))) *
      (Real.exp (β * etaDefect N (Real.exp (-q.1.1))
        (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))) - 1)
  let F : ℝ × ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) → ℝ :=
    fun z => Real.exp (β * z.1) *
      (nonlinearForcingPlusIntegrand N z.1 (fun _ => 1) z.2 -
        nonlinearForcingZeroIntegrand N z.1 (fun _ => 1) z.2)
  have hA0 : 0 < A := hA
  have hN0 : 0 < N := hN
  have hβ : 0 < β := (cramerExponent_mem hA0 hN0 hsc).1
  have hσ : (A ^ 2 / (N : ℝ)).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  have horigin : π {x | gaussianEuclideanNorm N x = 0} = 0 := by
    rw [show {x | gaussianEuclideanNorm N x = 0} = ({0} : Set (Fin N → ℝ)) by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff,
        gaussianEuclideanNorm_eq_zero_iff N]]
    exact hπ0
  have hFmeas : Measurable F := by
    have hv : Measurable fun z :
        ℝ × ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) =>
        Matrix.mulVec z.2.2 (WithLp.ofLp z.2.1.2) :=
      (measurable_mulVec_ofLp N).comp
        ((measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))
    have hp : Measurable fun z :
        ℝ × ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) =>
        nonlinearForcingPlusIntegrand N z.1 (fun _ => 1) z.2 := by
      unfold nonlinearForcingPlusIntegrand
      exact Measurable.ite
        (measurableSet_lt measurable_fst
          ((measurable_logPolarStep_fst N).comp measurable_snd))
        measurable_const measurable_const
    have hz : Measurable fun z :
        ℝ × ((ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) =>
        nonlinearForcingZeroIntegrand N z.1 (fun _ => 1) z.2 := by
      unfold nonlinearForcingZeroIntegrand
      exact Measurable.ite
        (measurableSet_lt measurable_fst
          (((measurable_fst.comp measurable_fst).comp measurable_snd).sub
            (((measurable_gaussianEuclideanNorm N).comp hv).log)))
        measurable_const measurable_const
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (hp.sub hz)
  have hFnonneg (y : ℝ) : ∀ᵐ q ∂μq, 0 ≤ F (y, q) := by
    filter_upwards [ae_mulVec_ne_zero_logPolarLaw_prod_gaussianMat
      A hN0 hσ π horigin] with q hq
    rw [show F (y, q) = Real.exp (β * y) *
      (nonlinearForcingPlusIntegrand N y (fun _ => 1) q -
        nonlinearForcingZeroIntegrand N y (fun _ => 1) q) by rfl]
    rw [exp_mul_nonlinearForcingIntegrand_one_sub_eq_indicator_Ico N β y q hq]
    exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
  have hFfiber (y : ℝ) :
      ∫ q, F (y, q) ∂μq = nonlinearForcing A N π β y (fun _ => 1) := by
    have hp := integrable_nonlinearForcingPlusIntegrand
      A N (π := π) (φ := fun _ => 1) y 1 measurable_const (fun _ => by norm_num)
    have hz := integrable_nonlinearForcingZeroIntegrand
      A N (π := π) (φ := fun _ => 1) y 1 measurable_const (fun _ => by norm_num)
    rw [show (fun q => F (y, q)) = fun q => Real.exp (β * y) *
      (nonlinearForcingPlusIntegrand N y (fun _ => 1) q -
        nonlinearForcingZeroIntegrand N y (fun _ => 1) q) by rfl,
      integral_const_mul, integral_sub hp hz]
    rfl
  have hψcont : Continuous (fun y => nonlinearForcing A N π β y (fun _ => 1)) :=
    continuous_nonlinearForcing A hN0 hσ π horigin β
      (φ := fun _ => 1) measurable_const (fun _ => by norm_num)
  have hψint : Integrable (fun y => nonlinearForcing A N π β y (fun _ => 1)) := by
    refine ⟨hψcont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hψnonneg (y : ℝ) :
        0 ≤ nonlinearForcing A N π β y (fun _ => 1) :=
      nonlinearForcing_one_nonneg A hN0 hσ π horigin β y
    calc
      (∫⁻ y, ‖nonlinearForcing A N π β y (fun _ => 1)‖ₑ) =
          ∫⁻ y, ENNReal.ofReal |nonlinearForcing A N π β y (fun _ => 1)| := by
        apply lintegral_congr
        intro y
        rw [Real.enorm_eq_ofReal (hψnonneg y), abs_of_nonneg (hψnonneg y)]
      _ ≤ Renewal.driNorm (fun y => ENNReal.ofReal
            |nonlinearForcing A N π β y (fun _ => 1)|) :=
        Renewal.lintegral_le_driNorm _
      _ < ⊤ := lt_top_iff_ne_top.mpr
        (driNorm_ofReal_abs_nonlinearForcing_ne_top hA hN hsc
          hδ0 hδ2 hδβ π hπ hπ0 hsupport (φ := fun _ => 1)
          measurable_const (fun _ => by norm_num))
  have hFint : Integrable F (volume.prod μq) := by
    rw [integrable_prod_iff hFmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [] with y
      have hi := ((integrable_nonlinearForcingPlusIntegrand
          A N (π := π) (φ := fun _ => 1) y 1
            measurable_const (fun _ => by norm_num)).sub
        (integrable_nonlinearForcingZeroIntegrand
          A N (π := π) (φ := fun _ => 1) y 1
            measurable_const (fun _ => by norm_num))).const_mul (Real.exp (β * y))
      simpa only [F, μq, Pi.sub_apply] using hi
    · apply hψint.congr
      filter_upwards [] with y
      rw [← hFfiber y]
      apply integral_congr_ae
      filter_upwards [hFnonneg y] with q hq
      rw [Real.norm_eq_abs, abs_of_nonneg hq]
  have hinner : ∀ᵐ q ∂μq, (∫ y, F (y, q)) = β⁻¹ * E q := by
    filter_upwards [ae_mulVec_ne_zero_logPolarLaw_prod_gaussianMat
      A hN0 hσ π horigin] with q hq
    let b := q.1.1 - Real.log (gaussianEuclideanNorm N
      (Matrix.mulVec q.2 (WithLp.ofLp q.1.2)))
    let η := etaDefect N (Real.exp (-q.1.1))
      (Matrix.mulVec q.2 (WithLp.ofLp q.1.2))
    have hη : 0 ≤ η := (etaDefect_pos N (Real.exp_pos _ ) hq).le
    rw [show (fun y => F (y, q)) = fun y => Real.exp (β * y) *
      (nonlinearForcingPlusIntegrand N y (fun _ => 1) q -
        nonlinearForcingZeroIntegrand N y (fun _ => 1) q) by rfl]
    apply Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y =>
      exp_mul_nonlinearForcingIntegrand_one_sub_eq_indicator_Ico N β y q hq))
    rw [integral_indicator measurableSet_Ico, integral_exp_mul_Ico_add hβ b hη]
    simp only [E, b, η]
    field_simp
  have hscaled : Integrable (fun q => β⁻¹ * E q) μq :=
    hFint.integral_prod_right.congr hinner
  have hEint : Integrable E μq := by
    apply (hscaled.const_mul β).congr
    filter_upwards [] with q
    field_simp
  have hEpos : ∀ᵐ q ∂μq, 0 < E q := by
    filter_upwards [ae_mulVec_ne_zero_logPolarLaw_prod_gaussianMat
      A hN0 hσ π horigin] with q hq
    have hη := etaDefect_pos N (Real.exp_pos (-q.1.1)) hq
    exact mul_pos (Real.exp_pos _) (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hβ hη)))
  have hEintpos : 0 < ∫ q, E q ∂μq := by
    apply (integral_pos_iff_support_of_nonneg_ae (hEpos.mono fun _ h => h.le) hEint).2
    have hsupp : ∀ᵐ q ∂μq, q ∈ Function.support E :=
      hEpos.mono fun _ h => ne_of_gt h
    have hcompl : μq (Function.support E)ᶜ = 0 := MeasureTheory.ae_iff.mp hsupp
    rw [measure_of_measure_compl_eq_zero hcompl, measure_univ]
    exact zero_lt_one
  rw [integral_nonlinearForcing_one hA hN hsc hδ0 hδ2 hδβ
    π hπ hπ0 hsupport]
  change 0 < β⁻¹ * ∫ q, E q ∂μq
  exact mul_pos (inv_pos.mpr hβ) hEintpos

end AbsorptionCutoff
