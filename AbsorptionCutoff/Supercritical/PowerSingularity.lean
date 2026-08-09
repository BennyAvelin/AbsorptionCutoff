/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.NonlinearForcingAdmissibilityFinal

/-!
# Power singularity of the invariant law

This module carries the weighted angular tail measure, its renewal equation,
and the final weak-convergence argument for `thm:nd-power-singularity`.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The exponentially weighted angular tail measure `ℋ_y` from
`eq:nd-weighted-tail-measure`. -/
noncomputable def weightedTailMeasure (N : ℕ) (π : Measure (Fin N → ℝ))
    (β y : ℝ) : Measure (EuclideanSpace ℝ (Fin N)) :=
  ENNReal.ofReal (Real.exp (β * y)) •
    Measure.map Prod.snd ((logPolarLaw N π).restrict {p | y < p.1})

/-- Evaluation of the weighted angular tail measure on a measurable set. -/
lemma weightedTailMeasure_apply (N : ℕ) (π : Measure (Fin N → ℝ))
    (β y : ℝ) {B : Set (EuclideanSpace ℝ (Fin N))} (hB : MeasurableSet B) :
    weightedTailMeasure N π β y B =
      ENNReal.ofReal (Real.exp (β * y)) *
        logPolarLaw N π {p | y < p.1 ∧ p.2 ∈ B} := by
  rw [weightedTailMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_snd hB]
  have hset : MeasurableSet
      (Prod.snd ⁻¹' B : Set (ℝ × EuclideanSpace ℝ (Fin N))) :=
    measurable_snd hB
  rw [Measure.restrict_apply hset]
  congr 2
  ext p
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, and_comm]

/-- The weighted tail measure written directly as a Cartesian event under the
original invariant law. -/
lemma weightedTailMeasure_apply_logPolarCoords
    (N : ℕ) (π : Measure (Fin N → ℝ)) (β y : ℝ)
    {B : Set (EuclideanSpace ℝ (Fin N))} (hB : MeasurableSet B) :
    weightedTailMeasure N π β y B =
      ENNReal.ofReal (Real.exp (β * y)) *
        π {x | y < logRadius N x ∧ angular N x ∈ B} := by
  rw [weightedTailMeasure_apply N π β y hB, logPolarLaw]
  have hset : MeasurableSet
      {p : ℝ × EuclideanSpace ℝ (Fin N) | y < p.1 ∧ p.2 ∈ B} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurable_snd hB)
  rw [Measure.map_apply (measurable_logPolarCoords N) hset]
  rfl

/-- Away from the origin, a lower bound on negative log-radius is exactly an
upper bound on radius at the corresponding exponential scale. -/
lemma lt_neg_log_iff_pos_lt_exp_neg {y r : ℝ} (hr : 0 < r) :
    y < -Real.log r ↔ r < Real.exp (-y) := by
  rw [← Real.log_lt_iff_lt_exp hr]
  constructor <;> intro h <;> linarith

/-- The weighted log-polar tail is the exponentially weighted strict small-ball
event in Cartesian coordinates. The origin-free hypothesis removes the sole
point where the totalized logarithm does not satisfy the expected equivalence. -/
lemma weightedTailMeasure_apply_lt_exp_neg
    (N : ℕ) (π : Measure (Fin N → ℝ)) (β y : ℝ)
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    {B : Set (EuclideanSpace ℝ (Fin N))} (hB : MeasurableSet B) :
    weightedTailMeasure N π β y B =
      ENNReal.ofReal (Real.exp (β * y)) *
        π {x | 0 < gaussianEuclideanNorm N x ∧
          gaussianEuclideanNorm N x < Real.exp (-y) ∧ angular N x ∈ B} := by
  rw [weightedTailMeasure_apply_logPolarCoords N π β y hB]
  congr 1
  apply measure_congr
  have hne : ∀ᵐ x ∂π, gaussianEuclideanNorm N x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using horigin
  filter_upwards [hne] with x hx
  have hpos : 0 < gaussianEuclideanNorm N x :=
    lt_of_le_of_ne (by
      rw [gaussianEuclideanNorm_eq_norm]
      exact norm_nonneg _) (Ne.symm hx)
  apply propext
  change (y < logRadius N x ∧ angular N x ∈ B) ↔
    (0 < gaussianEuclideanNorm N x ∧
      gaussianEuclideanNorm N x < Real.exp (-y) ∧ angular N x ∈ B)
  rw [logRadius, lt_neg_log_iff_pos_lt_exp_neg hpos]
  tauto

/-- If the Cartesian law gives no mass to the sphere at radius `exp (-y)`, the
strict radial endpoint in the weighted tail identity can be replaced by the
closed endpoint used in `eq:nd-directional-tail`. -/
lemma weightedTailMeasure_apply_le_exp_neg
    (N : ℕ) (π : Measure (Fin N → ℝ)) (β y : ℝ)
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (hsphere : π {x | gaussianEuclideanNorm N x = Real.exp (-y)} = 0)
    {B : Set (EuclideanSpace ℝ (Fin N))} (hB : MeasurableSet B) :
    weightedTailMeasure N π β y B =
      ENNReal.ofReal (Real.exp (β * y)) *
        π {x | 0 < gaussianEuclideanNorm N x ∧
          gaussianEuclideanNorm N x ≤ Real.exp (-y) ∧ angular N x ∈ B} := by
  rw [weightedTailMeasure_apply_lt_exp_neg N π β y horigin hB]
  congr 1
  apply measure_congr
  have hne : ∀ᵐ x ∂π, gaussianEuclideanNorm N x ≠ Real.exp (-y) := by
    rw [ae_iff]
    simpa only [not_ne_iff] using hsphere
  filter_upwards [hne] with x hx
  apply propext
  change (0 < gaussianEuclideanNorm N x ∧
      gaussianEuclideanNorm N x < Real.exp (-y) ∧ angular N x ∈ B) ↔
    (0 < gaussianEuclideanNorm N x ∧
      gaussianEuclideanNorm N x ≤ Real.exp (-y) ∧ angular N x ∈ B)
  constructor
  · exact fun ⟨hpos, hlt, hBmem⟩ => ⟨hpos, hlt.le, hBmem⟩
  · rintro ⟨hpos, hle, hBmem⟩
    exact ⟨hpos, lt_of_le_of_ne hle hx, hBmem⟩

/-- Every nonzero level set of the Gaussian Euclidean norm is Lebesgue-null.
The coordinate product volume is transported to the canonical volume on
`EuclideanSpace` by `WithLp.toLp`, where this is the standard sphere-null
theorem for Haar measure. -/
lemma volume_gaussianEuclideanNorm_level_set
    (N : ℕ) {r : ℝ} (hr : r ≠ 0) :
    (volume : Measure (Fin N → ℝ))
      {x | gaussianEuclideanNorm N x = r} = 0 := by
  have hs : MeasurableSet
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) r) :=
    Metric.isClosed_sphere.measurableSet
  have hset : {x | gaussianEuclideanNorm N x = r} =
      (WithLp.toLp 2) ⁻¹' Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) r := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_sphere,
      dist_zero_right, gaussianEuclideanNorm_eq_norm]
  rw [hset, ← Measure.map_apply
      (PiLp.volume_preserving_toLp (Fin N)).measurable hs,
    (PiLp.volume_preserving_toLp (Fin N)).map_eq]
  exact Measure.addHaar_sphere_of_ne_zero volume 0 hr

/-- A law absolutely continuous with respect to Cartesian Lebesgue measure
charges no nonzero Gaussian-Euclidean sphere. -/
lemma measure_gaussianEuclideanNorm_level_set_eq_zero_of_absolutelyContinuous
    (N : ℕ) (π : Measure (Fin N → ℝ))
    (hπ : π ≪ (volume : Measure (Fin N → ℝ))) {r : ℝ} (hr : r ≠ 0) :
    π {x | gaussianEuclideanNorm N x = r} = 0 := by
  exact hπ (volume_gaussianEuclideanNorm_level_set N hr)

end AbsorptionCutoff
