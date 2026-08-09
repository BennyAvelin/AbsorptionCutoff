/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidth

/-!
# Fixed-width nonlinear correction assembly

This continuation module owns the summability and limiting-value assembly for
the fixed-width logarithmic-radius correction. The base definitions, pathwise
identities, local quadratic loss estimate, strong-law input, and geometric
majorant live in `AbsorptionCutoff.FixedWidth`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- The nonlinear loss series along the canonical fixed-width radius path is
almost surely summable in the subcritical regime. -/
lemma ae_summable_fixedWidthRadiusLoss
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    {R0 : ℝ} (hR0 : 0 < R0) :
    ∀ᵐ ω ∂fixedWidthGaussianMeasure N,
      Summable (fun n ↦ fixedWidthRadiusLoss A N
        (fixedWidthRadiusPath A N R0 n ω) (ω n)) := by
  have hnz : ∀ᵐ ω ∂fixedWidthGaussianMeasure N, ∀ n, ω n ≠ 0 := by
    rw [ae_iff]
    have hset :
        {ω : fixedWidthSampleSpace N | ¬ ∀ n, ω n ≠ 0} =
          (fixedWidthNonzeroEvent N)ᶜ := by
      ext ω
      simp only [fixedWidthNonzeroEvent, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [hset]
    exact fixedWidthGaussianMeasure_nonzeroEvent_compl hN
  filter_upwards [hnz,
    ae_eventually_fixedWidthRadiusLoss_le_majorant hA hN hsub hR0]
      with ω hω hmajorant
  apply (summable_fixedWidthLossMajorant hsub R0).of_norm_bounded_eventually_nat
  filter_upwards [hmajorant] with n hn
  rw [Real.norm_eq_abs,
    abs_of_nonneg (fixedWidthRadiusLoss_nonneg hA hN
      (fixedWidthRadiusPath_pos hA hN hR0 hω n) (hω n))]
  exact hn

/-- Almost-sure limiting value of the cumulative nonlinear correction,
represented everywhere by the totalized infinite sum of one-step losses. -/
noncomputable def fixedWidthCorrectionLimit
    (A : ℝ) (N : ℕ) (R0 : ℝ) : fixedWidthSampleSpace N → ℝ :=
  fun ω ↦ ∑' n, fixedWidthRadiusLoss A N
    (fixedWidthRadiusPath A N R0 n ω) (ω n)

lemma measurable_fixedWidthCorrectionLimit
    (A : ℝ) (N : ℕ) (R0 : ℝ) :
    Measurable (fixedWidthCorrectionLimit A N R0) := by
  unfold fixedWidthCorrectionLimit
  exact Measurable.tsum fun n =>
    (measurable_fixedWidthRadiusLoss A N).comp
      ((measurable_fixedWidthRadiusPath A N R0 n).prodMk
        (measurable_pi_apply n))

/-- Every finite cumulative correction is bounded by the total loss on a
summable nonzero-innovation path. -/
lemma fixedWidthCorrection_le_limit
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {R0 : ℝ} (hR0 : 0 < R0) {ω : fixedWidthSampleSpace N}
    (hω : ∀ n, ω n ≠ 0)
    (hsum : Summable (fun n ↦ fixedWidthRadiusLoss A N
      (fixedWidthRadiusPath A N R0 n ω) (ω n))) (n : ℕ) :
    fixedWidthCorrection A N R0 n ω ≤
      fixedWidthCorrectionLimit A N R0 ω := by
  unfold fixedWidthCorrection fixedWidthCorrectionLimit
  exact hsum.sum_le_tsum (Finset.range n) fun j _ ↦
    fixedWidthRadiusLoss_nonneg hA hN
      (fixedWidthRadiusPath_pos hA hN hR0 hω j) (hω j)

/-- The canonical nonlinear correction satisfies the abstract good-event
hypotheses almost surely in the fixed-width subcritical regime. -/
lemma fixedWidthGaussianMeasure_correctionGoodEvent_compl
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    {R0 : ℝ} (hR0 : 0 < R0) :
    fixedWidthGaussianMeasure N
      (correctionGoodEvent
        (fixedWidthCorrection A N R0)
        (fixedWidthCorrectionLimit A N R0))ᶜ = 0 := by
  change fixedWidthGaussianMeasure N
    {ω | ¬ ω ∈ correctionGoodEvent
      (fixedWidthCorrection A N R0)
      (fixedWidthCorrectionLimit A N R0)} = 0
  rw [← ae_iff]
  have hnz : ∀ᵐ ω ∂fixedWidthGaussianMeasure N, ∀ n, ω n ≠ 0 := by
    rw [ae_iff]
    have hset :
        {ω : fixedWidthSampleSpace N | ¬ ∀ n, ω n ≠ 0} =
          (fixedWidthNonzeroEvent N)ᶜ := by
      ext ω
      simp only [fixedWidthNonzeroEvent, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [hset]
    exact fixedWidthGaussianMeasure_nonzeroEvent_compl hN
  filter_upwards [hnz,
    ae_summable_fixedWidthRadiusLoss hA hN hsub hR0]
      with ω hω hsum
  exact ⟨fixedWidthCorrection_nonneg hA hN hR0 hω,
    monotone_fixedWidthCorrection hA hN hR0 hω,
    fixedWidthCorrection_le_limit hA hN hR0 hω hsum⟩

/-- First weak entrance time of the canonical unrounded radius path into
`(-∞, ε]`. -/
noncomputable def fixedWidthRadiusEntranceTime
    (A : ℝ) (N : ℕ) (R0 ε : ℝ) :
    fixedWidthSampleSpace N → WithTop ℕ :=
  hittingAfter (fixedWidthRadiusPath A N R0) (Set.Iic ε) 0

/-- On a nonzero-innovation path, radius entrance below `ε` is exactly
corrected passage above the logarithmic level `log (R0 / ε)`. -/
lemma fixedWidthRadiusEntranceTime_eq_correctedFirstPassageTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {R0 : ℝ} (hR0 : 0 < R0) {ε : ℝ} (hε : 0 < ε)
    {ω : fixedWidthSampleSpace N} (hω : ∀ n, ω n ≠ 0) :
    fixedWidthRadiusEntranceTime A N R0 ε ω =
      correctedFirstPassageTime
        (fixedWidthIncrementProcess A N)
        (fixedWidthCorrection A N R0) (Real.log (R0 / ε)) ω := by
  have hmem (n : ℕ) :
      fixedWidthRadiusPath A N R0 n ω ≤ ε ↔
        Real.log (R0 / ε) ≤
          partialSum (fixedWidthIncrementProcess A N) n ω +
            fixedWidthCorrection A N R0 n ω := by
    have hr := fixedWidthRadiusPath_pos hA hN hR0 hω n
    have hdecomp := neg_log_fixedWidthRadiusPath_eq hA hN hR0 hω n
    rw [Real.log_div hR0.ne' hε.ne']
    constructor
    · intro hle
      have hlog : Real.log (fixedWidthRadiusPath A N R0 n ω) ≤
          Real.log ε := (Real.log_le_log_iff hr hε).mpr hle
      linarith
    · intro hle
      apply (Real.log_le_log_iff hr hε).mp
      linarith
  unfold fixedWidthRadiusEntranceTime correctedFirstPassageTime
  apply le_antisymm
  · apply hittingAfter_le_hittingAfter_of_mem_imp
    intro n hn
    exact (hmem n).mpr hn
  · apply hittingAfter_le_hittingAfter_of_mem_imp
    intro n hn
    exact (hmem n).mp hn

/-- Corrected post-floor first-passage profile for the canonical nonlinear
fixed-width radius correction. -/
lemma tendsto_measureReal_fixedWidthRadiusCorrectedFirstPassageTime_gt_postFloorTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    {R0 : ℝ} (hR0 : 0 < R0)
    (L Ltilde v : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ (fixedWidthGaussianMeasure N).real {ω |
        (postFloorTime
            (∫ x, fixedWidthIncrementProcess A N 0 x
              ∂fixedWidthGaussianMeasure N)
            (fixedWidthStdDev A N) a L v r : WithTop ℕ) <
          correctedFirstPassageTime
            (fixedWidthIncrementProcess A N)
            (fixedWidthCorrection A N R0) (Ltilde r) ω})
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  exact tendsto_measureReal_fixedWidthCorrectedFirstPassageTime_gt_postFloorTime
    hA hN hsub
    (fixedWidthCorrection A N R0)
    (fixedWidthCorrectionLimit A N R0)
    (measurable_fixedWidthCorrectionLimit A N R0)
    (fixedWidthGaussianMeasure_correctionGoodEvent_compl hA hN hsub hR0)
    L Ltilde v a hL hv hlevel

/-- Post-floor survival profile for entrance of the canonical unrounded radius
below a positive threshold sequence. -/
lemma tendsto_measureReal_fixedWidthRadiusEntranceTime_gt_postFloorTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    {R0 : ℝ} (hR0 : 0 < R0)
    (L ε v : ℕ → ℝ) (a : ℝ)
    (hε : ∀ r, 0 < ε r)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Real.log (R0 / ε r) - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ (fixedWidthGaussianMeasure N).real {ω |
        (postFloorTime
            (∫ x, fixedWidthIncrementProcess A N 0 x
              ∂fixedWidthGaussianMeasure N)
            (fixedWidthStdDev A N) a L v r : WithTop ℕ) <
          fixedWidthRadiusEntranceTime A N R0 (ε r) ω})
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  have hcorrected :=
    tendsto_measureReal_fixedWidthRadiusCorrectedFirstPassageTime_gt_postFloorTime
      hA hN hsub hR0 L (fun r ↦ Real.log (R0 / ε r)) v a hL hv hlevel
  have hnz : ∀ᵐ ω ∂fixedWidthGaussianMeasure N, ∀ n, ω n ≠ 0 := by
    rw [ae_iff]
    have hset :
        {ω : fixedWidthSampleSpace N | ¬ ∀ n, ω n ≠ 0} =
          (fixedWidthNonzeroEvent N)ᶜ := by
      ext ω
      simp only [fixedWidthNonzeroEvent, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [hset]
    exact fixedWidthGaussianMeasure_nonzeroEvent_compl hN
  refine hcorrected.congr' ?_
  filter_upwards with r
  rw [Measure.real_def, Measure.real_def]
  congr 1
  apply measure_congr
  filter_upwards [hnz] with ω hω
  change
    ((postFloorTime
        (∫ x, fixedWidthIncrementProcess A N 0 x
          ∂fixedWidthGaussianMeasure N)
        (fixedWidthStdDev A N) a L v r : WithTop ℕ) <
      correctedFirstPassageTime
        (fixedWidthIncrementProcess A N)
        (fixedWidthCorrection A N R0) (Real.log (R0 / ε r)) ω) =
    ((postFloorTime
        (∫ x, fixedWidthIncrementProcess A N 0 x
          ∂fixedWidthGaussianMeasure N)
        (fixedWidthStdDev A N) a L v r : WithTop ℕ) <
      fixedWidthRadiusEntranceTime A N R0 (ε r) ω)
  rw [fixedWidthRadiusEntranceTime_eq_correctedFirstPassageTime
    hA hN hR0 (hε r) hω]

end AbsorptionCutoff
