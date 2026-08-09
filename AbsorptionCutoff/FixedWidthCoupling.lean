/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCorrection
import AbsorptionCutoff.RoundedVectorReduction

/-!
# Fixed-width rounded/unrounded coupling

This continuation module owns the synchronous comparison between the rounded
and unrounded fixed-width vector chains, the final finite-grid absorption
estimate, and their assembly with the unrounded radius-entrance profile.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Canonical sequence space of Gaussian weight matrices for the synchronous
fixed-width coupling. -/
abbrev fixedWidthMatrixSampleSpace (N : ℕ) :=
  ℕ → (Fin N → Fin N → ℝ)

/-- Product law of the independent Gaussian weight matrices driving both
members of the synchronous coupling. -/
noncomputable def fixedWidthMatrixGaussianMeasure (A : ℝ) (N : ℕ) :
    Measure (fixedWidthMatrixSampleSpace N) :=
  Measure.infinitePi fun _ ↦ gaussianMat A N

instance (A : ℝ) (N : ℕ) :
    IsProbabilityMeasure (fixedWidthMatrixGaussianMeasure A N) := by
  unfold fixedWidthMatrixGaussianMeasure
  infer_instance

/-- Unrounded vector path driven by the canonical matrix sequence. -/
noncomputable def fixedWidthUnroundedVectorPath
    (N : ℕ) (x0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → (Fin N → ℝ)
  | 0 => fun _ ↦ x0
  | n + 1 => fun ω ↦
      Pstep N (fixedWidthUnroundedVectorPath N x0 n ω) (ω n)

/-- Rounded vector path, started from the rounded deterministic initial state
and driven synchronously by the same matrix sequence. -/
noncomputable def fixedWidthRoundedVectorPath
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → (Fin N → ℝ)
  | 0 => fun _ ↦ Qρ ρ x0
  | n + 1 => fun ω ↦
      roundedPstep ρ N (fixedWidthRoundedVectorPath ρ N x0 n ω) (ω n)

lemma measurable_fixedWidthUnroundedVectorPath
    (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthUnroundedVectorPath N x0 n) := by
  induction n with
  | zero =>
      simp only [fixedWidthUnroundedVectorPath]
      fun_prop
  | succ n ih =>
      simp only [fixedWidthUnroundedVectorPath]
      have hω : Measurable
          (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n) :=
        measurable_pi_apply n
      apply measurable_pi_iff.mpr
      intro i
      unfold Pstep
      apply continuous_tanh.measurable.comp
      apply Finset.measurable_sum
      intro j _
      exact ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hω)).mul
          ((measurable_pi_apply j).comp ih)

lemma measurable_fixedWidthRoundedVectorPath
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthRoundedVectorPath ρ N x0 n) := by
  induction n with
  | zero =>
      simp only [fixedWidthRoundedVectorPath]
      fun_prop
  | succ n ih =>
      simp only [fixedWidthRoundedVectorPath]
      have hω : Measurable
          (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n) :=
        measurable_pi_apply n
      unfold roundedPstep
      apply (measurable_Qρ ρ N).comp
      apply measurable_pi_iff.mpr
      intro i
      unfold Pstep
      apply continuous_tanh.measurable.comp
      apply Finset.measurable_sum
      intro j _
      exact ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hω)).mul
          ((measurable_pi_apply j).comp ih)

/-- The scalar hyperbolic tangent is one-Lipschitz. -/
lemma abs_tanh_sub_tanh_le (x y : ℝ) :
    |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (f := Real.tanh)
    (f' := fun z ↦ 1 - Real.tanh z ^ 2) (C := 1) (x := y) (y := x)
    (fun z _ ↦ (hasDerivAt_tanh z).hasDerivWithinAt)
    (fun z _ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · nlinarith [sq_nonneg (Real.tanh z)]
      · linarith [Real.tanh_sq_lt_one z])
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

/-- Coordinatewise `tanh` contracts the Euclidean distance. -/
lemma gaussianEuclideanNorm_tanhVec_sub_tanhVec_le
    (N : ℕ) (u v : Fin N → ℝ) :
    gaussianEuclideanNorm N (tanhVec N u - tanhVec N v) ≤
      gaussianEuclideanNorm N (u - v) := by
  rw [gaussianEuclideanNorm_eq_norm, gaussianEuclideanNorm_eq_norm,
    PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  change |Real.tanh (u i) - Real.tanh (v i)| ^ 2 ≤ |u i - v i| ^ 2
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_tanh_sub_tanh_le (u i) (v i)) 2

/-- Coordinatewise nearest-grid rounding contributes at most `√N ρ / 2` in
Euclidean norm. -/
lemma gaussianEuclideanNorm_Qρ_sub_le
    {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) (x : Fin N → ℝ) :
    gaussianEuclideanNorm N (Qρ ρ x - x) ≤ Real.sqrt N * (ρ / 2) := by
  rw [gaussianEuclideanNorm_eq_norm, PiLp.norm_eq_of_L2]
  have hsum :
      ∑ i : Fin N, ‖((WithLp.toLp 2 (Qρ ρ x - x) :
        EuclideanSpace ℝ (Fin N)) i)‖ ^ 2 ≤
        ∑ _i : Fin N, (ρ / 2) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (gridRound_sub_le hρ (x i)) 2
  calc
    Real.sqrt (∑ i : Fin N, ‖((WithLp.toLp 2 (Qρ ρ x - x) :
        EuclideanSpace ℝ (Fin N)) i)‖ ^ 2) ≤
        Real.sqrt (∑ _i : Fin N, (ρ / 2) ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = Real.sqrt N * (ρ / 2) := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq_eq_abs,
        abs_of_nonneg (div_nonneg hρ.le (by norm_num))]

/-- Triangle inequality for the explicit Euclidean norm on function-valued
vectors. -/
lemma gaussianEuclideanNorm_add_le
    (N : ℕ) (u v : Fin N → ℝ) :
    gaussianEuclideanNorm N (u + v) ≤
      gaussianEuclideanNorm N u + gaussianEuclideanNorm N v := by
  rw [gaussianEuclideanNorm_eq_norm, gaussianEuclideanNorm_eq_norm,
    gaussianEuclideanNorm_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

/-- Deterministic one-step synchronous comparison: the new discrepancy is at
most the linearized matrix action on the old discrepancy plus one rounding
error. -/
lemma gaussianEuclideanNorm_roundedPstep_sub_Pstep_le
    {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ)
    (x y : Fin N → ℝ) (W : Fin N → Fin N → ℝ) :
    gaussianEuclideanNorm N (roundedPstep ρ N y W - Pstep N x W) ≤
      gaussianEuclideanNorm N (Matrix.mulVec W (y - x)) +
        Real.sqrt N * (ρ / 2) := by
  have htanh := gaussianEuclideanNorm_tanhVec_sub_tanhVec_le N
    (Matrix.mulVec W y) (Matrix.mulVec W x)
  calc
    gaussianEuclideanNorm N (roundedPstep ρ N y W - Pstep N x W) =
        gaussianEuclideanNorm N
          ((Qρ ρ (Pstep N y W) - Pstep N y W) +
            (Pstep N y W - Pstep N x W)) := by
      congr 1
      unfold roundedPstep
      abel
    _ ≤ gaussianEuclideanNorm N (Qρ ρ (Pstep N y W) - Pstep N y W) +
          gaussianEuclideanNorm N (Pstep N y W - Pstep N x W) :=
      gaussianEuclideanNorm_add_le N _ _
    _ ≤ Real.sqrt N * (ρ / 2) +
          gaussianEuclideanNorm N
            (Matrix.mulVec W y - Matrix.mulVec W x) := by
      apply add_le_add
      · exact gaussianEuclideanNorm_Qρ_sub_le hρ N _
      · simpa only [Pstep_eq_tanhVec_mulVec] using htanh
    _ = gaussianEuclideanNorm N (Matrix.mulVec W (y - x)) +
          Real.sqrt N * (ρ / 2) := by
      rw [Matrix.mulVec_sub]
      ring

/-- The canonical synchronous paths satisfy the deterministic one-step error
recursion on every matrix sample. -/
lemma fixedWidthVectorPath_error_succ_le
    {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) (x0 : Fin N → ℝ)
    (n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    gaussianEuclideanNorm N
        (fixedWidthRoundedVectorPath ρ N x0 (n + 1) ω -
          fixedWidthUnroundedVectorPath N x0 (n + 1) ω) ≤
      gaussianEuclideanNorm N
          (Matrix.mulVec (ω n)
            (fixedWidthRoundedVectorPath ρ N x0 n ω -
              fixedWidthUnroundedVectorPath N x0 n ω)) +
        Real.sqrt N * (ρ / 2) := by
  simp only [fixedWidthRoundedVectorPath, fixedWidthUnroundedVectorPath]
  exact gaussianEuclideanNorm_roundedPstep_sub_Pstep_le hρ N _ _ _

/-- Fixed reference unit vector used when the current discrepancy vanishes. -/
noncomputable def fixedWidthReferenceDirection
    {N : ℕ} (hN : 0 < N) : Fin N → ℝ :=
  Pi.single ⟨0, hN⟩ 1

@[simp] lemma gaussianEuclideanNorm_fixedWidthReferenceDirection
    {N : ℕ} (hN : 0 < N) :
    gaussianEuclideanNorm N (fixedWidthReferenceDirection hN) = 1 := by
  classical
  unfold gaussianEuclideanNorm gaussianSquaredNorm fixedWidthReferenceDirection
  have hsum : ∑ i : Fin N,
      ((Pi.single ⟨0, hN⟩ (1 : ℝ) : Fin N → ℝ) i) ^ 2 = 1 := by
    rw [Finset.sum_eq_single ⟨0, hN⟩]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  exact (congrArg Real.sqrt hsum).trans Real.sqrt_one

/-- Unit direction associated with a discrepancy, with a fixed reference
direction at zero. -/
noncomputable def fixedWidthUnitDirection
    {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) : Fin N → ℝ :=
  if d = 0 then fixedWidthReferenceDirection hN
  else (gaussianEuclideanNorm N d)⁻¹ • d

@[simp] lemma gaussianEuclideanNorm_fixedWidthUnitDirection
    {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) :
    gaussianEuclideanNorm N (fixedWidthUnitDirection hN d) = 1 := by
  by_cases hd : d = 0
  · subst d
    simp [fixedWidthUnitDirection]
  · have hnorm : 0 < gaussianEuclideanNorm N d :=
      lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity)
        (Ne.symm ((gaussianEuclideanNorm_eq_zero_iff N d).not.mpr hd))
    rw [fixedWidthUnitDirection, if_neg hd, gaussianEuclideanNorm_smul,
      abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ hnorm.ne']

/-- Reconstruct a discrepancy from its Euclidean norm and chosen unit
direction. -/
lemma gaussianEuclideanNorm_smul_fixedWidthUnitDirection
    {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ) :
    gaussianEuclideanNorm N d • fixedWidthUnitDirection hN d = d := by
  by_cases hd : d = 0
  · subst d
    rw [fixedWidthUnitDirection, if_pos rfl]
    have hzero : gaussianEuclideanNorm N (0 : Fin N → ℝ) = 0 := by
      simp [gaussianEuclideanNorm, gaussianSquaredNorm]
    rw [hzero, zero_smul]
  · have hnorm : gaussianEuclideanNorm N d ≠ 0 :=
      (gaussianEuclideanNorm_eq_zero_iff N d).not.mpr hd
    rw [fixedWidthUnitDirection, if_neg hd, smul_smul,
      mul_inv_cancel₀ hnorm, one_smul]

/-- The matrix action on a discrepancy factors exactly into its Euclidean
size and the matrix action on the selected unit direction. -/
lemma gaussianEuclideanNorm_mulVec_eq_multiplier_mul
    {N : ℕ} (hN : 0 < N) (W : Fin N → Fin N → ℝ)
    (d : Fin N → ℝ) :
    gaussianEuclideanNorm N (Matrix.mulVec W d) =
      gaussianEuclideanNorm N
          (Matrix.mulVec W (fixedWidthUnitDirection hN d)) *
        gaussianEuclideanNorm N d := by
  conv_lhs =>
    rw [← gaussianEuclideanNorm_smul_fixedWidthUnitDirection hN d]
  rw [Matrix.mulVec_smul, gaussianEuclideanNorm_smul,
    abs_of_nonneg (by unfold gaussianEuclideanNorm; positivity)]
  ring

end AbsorptionCutoff
