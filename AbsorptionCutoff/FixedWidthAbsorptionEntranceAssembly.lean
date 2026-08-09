/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthAbsorptionEntranceBounds

/-!
# Fixed-width affine entrance assembly

This continuation module proves shifted-log exponential integrability and
instantiates negative-drift affine entrance for the rounded grid radius.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- Adding any positive constant to an exact-start rounded multiplier preserves
exponential integrability of its logarithm on a neighborhood of zero. The two
endpoint moments are elementary: exponent `1` is the integrable shifted
multiplier, while exponent `-1` is bounded by the inverse shift. -/
lemma zero_mem_interior_integrableExpSet_fixedWidthRoundedRadiusLogShiftFrom
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (0 : ℝ) ∈ interior
      (integrableExpSet
        (fun ω ↦ Real.log
          (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω + ε))
        (fixedWidthMatrixGaussianMeasure A N)) := by
  let M : fixedWidthMatrixSampleSpace N → ℝ :=
    fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n
  let μ : Measure (fixedWidthMatrixSampleSpace N) :=
    fixedWidthMatrixGaussianMeasure A N
  have hMmeas : Measurable M :=
    measurable_fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n
  have hM : Integrable M μ :=
    integrable_fixedWidthRoundedRadiusMultiplierFrom hA hN ρ y0 n
  have hMpos : ∀ᵐ ω ∂μ, 0 < M ω :=
    ae_fixedWidthRoundedRadiusMultiplierFrom_pos hA hN ρ y0 n
  have hone : (1 : ℝ) ∈
      integrableExpSet (fun ω ↦ Real.log (M ω + ε)) μ := by
    have hsum : Integrable (fun ω ↦ M ω + ε) μ :=
      hM.add (integrable_const ε)
    apply hsum.congr
    filter_upwards [hMpos] with ω hω
    simpa using (Real.exp_log (add_pos hω hε)).symm
  have hnegone : (-1 : ℝ) ∈
      integrableExpSet (fun ω ↦ Real.log (M ω + ε)) μ := by
    have hlogmeas : Measurable (fun ω ↦ Real.log (M ω + ε)) :=
      Real.measurable_log.comp (hMmeas.add_const ε)
    have hmeas : Measurable
        (fun ω ↦ Real.exp ((-1 : ℝ) * Real.log (M ω + ε))) :=
      Real.measurable_exp.comp (measurable_const.mul hlogmeas)
    refine (integrable_const (ε⁻¹)).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [hMpos] with ω hω
    have hsum : 0 < M ω + ε := add_pos hω hε
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_one_mul,
      Real.exp_neg, Real.exp_log hsum]
    exact (inv_le_inv₀ hsum hε).2 (le_add_of_nonneg_left hω.le)
  have hIcc : Set.Icc (-1 : ℝ) 1 ⊆
      integrableExpSet (fun ω ↦ Real.log (M ω + ε)) μ := by
    have hsegment :=
      convex_integrableExpSet.segment_subset hnegone hone
    simpa [segment_eq_uIcc,
      Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hsegment
  have hIoo : Set.Ioo (-1 : ℝ) 1 ⊆
      integrableExpSet (fun ω ↦ Real.log (M ω + ε)) μ := by
    intro t ht
    exact hIcc ⟨ht.1.le, ht.2.le⟩
  have hzero : (0 : ℝ) ∈
      interior (integrableExpSet (fun ω ↦ Real.log (M ω + ε)) μ) :=
    interior_maximal hIoo isOpen_Ioo (by norm_num)
  simpa [M, μ] using hzero

/-- The one-indexed multiplier convention used by `affineRecursion`: coordinate
zero is an unused constant, and successor coordinate `n+1` is the rounded
radius multiplier driving the actual update from time `n` to time `n+1`. -/
noncomputable def fixedWidthAffineRoundedRadiusMultiplierFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → ℝ
  | 0 => fun _ ↦ 0
  | n + 1 => fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n

@[simp] lemma fixedWidthAffineRoundedRadiusMultiplierFrom_zero
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) :
    fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 0 = 0 := rfl

@[simp] lemma fixedWidthAffineRoundedRadiusMultiplierFrom_succ
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 (n + 1) =
      fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n := rfl

lemma measurable_fixedWidthAffineRoundedRadiusMultiplierFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 n) := by
  cases n with
  | zero => exact measurable_const
  | succ n =>
      exact measurable_fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n

lemma fixedWidthAffineRoundedRadiusMultiplierFrom_nonneg
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ)
    (ω : fixedWidthMatrixSampleSpace N) (n : ℕ) :
    0 ≤ fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 n ω := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [fixedWidthAffineRoundedRadiusMultiplierFrom_succ]
      unfold fixedWidthRoundedRadiusMultiplierFrom gaussianEuclideanNorm
      positivity

/-- Adding the unused constant zeroth coordinate preserves mutual
independence of the rounded-radius multiplier process. -/
lemma iIndepFun_fixedWidthAffineRoundedRadiusMultiplierFrom
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) :
    iIndepFun (fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0)
      (fixedWidthMatrixGaussianMeasure A N) := by
  apply iIndepFun_of_iIndepFun_fin_prefix
  apply iIndepFun_fin_prefix_of_indepFun_prefix_next
  · exact measurable_fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0
  · intro n
    cases n with
    | zero =>
        exact indepFun_const_right _ 0
    | succ n =>
        have hcons : Measurable
            (fun v : Fin n → ℝ ↦
              (Fin.cons 0 v : Fin (n + 1) → ℝ)) := by
          apply measurable_pi_lambda
          intro i
          refine Fin.cases measurable_const (fun j ↦ ?_) i
          exact measurable_pi_apply j
        have hcomp :=
          (indepFun_fixedWidthRoundedRadiusMultiplierPrefixFrom_next
            A hN ρ y0 n).comp hcons measurable_id
        convert hcomp using 1
        · funext ω i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · rfl
          · rfl
        · rfl

lemma identDistrib_fixedWidthAffineRoundedRadiusMultiplierFrom_one
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (y0 : Fin N → ℝ) (n : ℕ) :
    IdentDistrib
      (fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 (n + 1))
      (fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 1)
      (fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthMatrixGaussianMeasure A N) := by
  simpa only [fixedWidthAffineRoundedRadiusMultiplierFrom_succ] using
    identDistrib_fixedWidthRoundedRadiusMultiplierFrom_zero
      A hN ρ y0 n

/-- The rounded-radius affine comparison enters a fixed bounded region after a
logarithmic time with an exponential excess-time tail. All constants are
uniform in the positive starting radius `K`. -/
theorem exists_fixedWidthAffineRoundedRadiusEntrance_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) (ρ : ℝ)
    (y0 : Fin N → ℝ) :
    ∃ Kstar c1 c2 c3 : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ K : ℝ, 0 < K → ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
          {ω | (⌊c1 * Real.log K + r⌋₊ : ℕ∞) <
            affineEntranceTime
              (fun k ↦
                fixedWidthAffineRoundedRadiusMultiplierFrom
                  hN ρ y0 k ω)
              (Real.sqrt N / 2) K Kstar} ≤
          c2 * Real.exp (-c3 * r) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let M := fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0
  let bound := fixedWidthRoundedRadiusLogEnvelopeFrom hN ρ y0 0
  apply exists_affineEntrance_bound μ M (Real.sqrt N / 2) bound
  · exact fixedWidthAffineRoundedRadiusMultiplierFrom_nonneg hN ρ y0
  · exact measurable_fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0
  · exact iIndepFun_fixedWidthAffineRoundedRadiusMultiplierFrom A hN ρ y0
  · exact identDistrib_fixedWidthAffineRoundedRadiusMultiplierFrom_one
      A hN ρ y0
  · simpa [M, fixedWidthRoundedRadiusLogMultiplierFrom] using
      (integral_fixedWidthRoundedRadiusLogMultiplierFrom_eq_logRadialDrift
        hA hN ρ y0 0).trans_lt hsub
  · intro ε hε
    change (0 : ℝ) ∈ interior
      (integrableExpSet
        (fun ω ↦ Real.log
          (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 0 ω + ε)) μ)
    simpa [μ] using
      (zero_mem_interior_integrableExpSet_fixedWidthRoundedRadiusLogShiftFrom
        hA hN ρ y0 0 hε)
  · simpa [M] using
      (ae_fixedWidthRoundedRadiusMultiplierFrom_pos hA hN ρ y0 0)
  · exact integrable_fixedWidthRoundedRadiusLogEnvelopeFrom
      hA hN ρ y0 0
  · intro n
    simpa [M, bound] using
      (ae_norm_log_fixedWidthRoundedRadiusMultiplierFrom_add_inv_nat_le
        hA hN ρ y0 0 n)

end AbsorptionCutoff
