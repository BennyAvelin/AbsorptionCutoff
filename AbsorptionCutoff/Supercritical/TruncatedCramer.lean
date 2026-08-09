/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.GaussianRadial
import AbsorptionCutoff.LaplaceMoments
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Truncated Gaussian Cramér estimates

This file begins the paper's truncated Cramér argument for the supercritical
dimension cutoff.  Its first input is the polynomial Laplace-transform decay
of one truncated squared standard Gaussian coordinate.
-/

open MeasureTheory ProbabilityTheory BigOperators Filter Topology
open scoped Real

namespace AbsorptionCutoff

/-- The squared Gaussian coordinate truncated at level `L²`. -/
def truncatedGaussianSquare (L x : ℝ) : ℝ :=
  min (x ^ 2) (L ^ 2)

lemma measurable_truncatedGaussianSquare (L : ℝ) :
    Measurable (truncatedGaussianSquare L) := by
  unfold truncatedGaussianSquare
  fun_prop

lemma truncatedGaussianSquare_nonneg (L x : ℝ) :
    0 ≤ truncatedGaussianSquare L x := by
  exact le_min (sq_nonneg x) (sq_nonneg L)

/-- The mean of one truncated squared standard Gaussian coordinate. -/
noncomputable def truncatedGaussianSquareMean (L : ℝ) : ℝ :=
  ∫ x : ℝ, truncatedGaussianSquare L x ∂(gaussianReal 0 1)

/-- A coordinate of the product Gaussian vector has the same truncated-square
mean as one standard Gaussian. -/
lemma integral_gaussianVec_truncatedGaussianSquare_eval_eq_mean
    (L : ℝ) {N : ℕ} (i : Fin N) :
    (∫ g : Fin N → ℝ, truncatedGaussianSquare L (g i) ∂(gaussianVec N)) =
      truncatedGaussianSquareMean L := by
  have hpm :
      (gaussianVec N).map (Function.eval i) = gaussianReal 0 1 := by
    unfold gaussianVec
    rw [Measure.pi_map_eval]
    simp
  have hf :
      AEStronglyMeasurable (truncatedGaussianSquare L)
        ((gaussianVec N).map (Function.eval i)) :=
    (measurable_truncatedGaussianSquare L).aestronglyMeasurable
  have hφ :
      AEMeasurable (Function.eval i) (gaussianVec N) :=
    (measurable_pi_apply i).aemeasurable
  have hmap := integral_map hφ hf
  rw [hpm] at hmap
  exact hmap.symm.trans rfl

/-- Each centered truncated squared Gaussian coordinate is sub-Gaussian with
the Hoeffding parameter supplied by its range `[0, L²]`. -/
lemma hasSubgaussianMGF_truncatedGaussianSquare_eval_sub_mean
    (L : ℝ) {N : ℕ} (i : Fin N) :
    HasSubgaussianMGF
      (fun g : Fin N → ℝ =>
        truncatedGaussianSquare L (g i) - truncatedGaussianSquareMean L)
      ((‖L ^ 2‖₊ / 2) ^ 2) (gaussianVec N) := by
  let X : (Fin N → ℝ) → ℝ :=
    fun g => truncatedGaussianSquare L (g i)
  have hXMeas : AEMeasurable X (gaussianVec N) :=
    ((measurable_truncatedGaussianSquare L).comp
      (measurable_pi_apply i)).aemeasurable
  have hXBounds :
      ∀ᵐ g ∂(gaussianVec N), X g ∈ Set.Icc 0 (L ^ 2) := by
    filter_upwards with g
    exact ⟨truncatedGaussianSquare_nonneg L (g i), min_le_right _ _⟩
  have hsubG := hasSubgaussianMGF_of_mem_Icc hXMeas hXBounds
  rw [show (∫ g, X g ∂(gaussianVec N)) =
      truncatedGaussianSquareMean L by
    exact integral_gaussianVec_truncatedGaussianSquare_eval_eq_mean L i] at hsubG
  simpa only [X, sub_zero] using hsubG

/-- The mean truncated squared Gaussian coordinate converges to the full
standard-Gaussian second moment as the truncation level tends to infinity. -/
theorem tendsto_integral_truncatedGaussianSquare_atTop :
    Tendsto
      (fun L : ℝ =>
        ∫ g : ℝ, truncatedGaussianSquare L g ∂(gaussianReal 0 1))
      atTop (𝓝 1) := by
  have hconv :
      Tendsto
        (fun L : ℝ =>
          ∫ g : ℝ, truncatedGaussianSquare L g ∂(gaussianReal 0 1))
        atTop
        (𝓝 (∫ g : ℝ, g ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun g : ℝ => g ^ 2) ?_ ?_ integrable_sq_gaussian ?_
    · exact Filter.Eventually.of_forall fun L =>
        (measurable_truncatedGaussianSquare L).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun L =>
        Filter.Eventually.of_forall fun g => by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (truncatedGaussianSquare_nonneg L g)]
          exact min_le_left _ _
    · exact Filter.Eventually.of_forall fun g => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop |g|] with L hL
        have hL0 : 0 ≤ L := (abs_nonneg g).trans hL
        have hsquares : g ^ 2 ≤ L ^ 2 := by
          rw [← sq_abs g]
          exact (sq_le_sq₀ (abs_nonneg g) hL0).2 hL
        rw [truncatedGaussianSquare, min_eq_left hsquares]
  simpa only [integral_sq_gaussian] using hconv

/-- For every `A > 1`, some truncation level at least one leaves the truncated
Gaussian second moment strictly above `A⁻²`. -/
theorem exists_one_le_integral_truncatedGaussianSquare_gt_inv_sq
    {A : ℝ} (hA : 1 < A) :
    ∃ L : ℝ, 1 ≤ L ∧
      (A ^ 2)⁻¹ <
        ∫ g : ℝ, truncatedGaussianSquare L g ∂(gaussianReal 0 1) := by
  have hA_sq : 1 < A ^ 2 := by
    nlinarith
  have h_inv : (A ^ 2)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ hA_sq
  have h_mean :
      ∀ᶠ L : ℝ in atTop,
        (A ^ 2)⁻¹ <
          ∫ g : ℝ, truncatedGaussianSquare L g ∂(gaussianReal 0 1) :=
    (tendsto_order.1 tendsto_integral_truncatedGaussianSquare_atTop).1
      _ h_inv
  obtain ⟨L, hL_mean, hL⟩ :=
    (h_mean.and (eventually_ge_atTop (1 : ℝ))).exists
  exact ⟨L, hL, hL_mean⟩

/-- For every supercritical gain, one can choose the truncation and strict
loss parameters needed by the truncated Cramér argument. -/
theorem exists_truncatedGaussianSquare_parameters
    {A : ℝ} (hA : 1 < A) :
    ∃ L ε δ : ℝ,
      1 ≤ L ∧ ε ∈ Set.Ioo 0 1 ∧ 0 < δ ∧
        1 < (1 - ε) * A ^ 2 *
          ((∫ g : ℝ,
            truncatedGaussianSquare L g ∂(gaussianReal 0 1)) - δ) := by
  obtain ⟨L, hL, hmean⟩ :=
    exists_one_le_integral_truncatedGaussianSquare_gt_inv_sq hA
  have hA_sq_pos : 0 < A ^ 2 :=
    sq_pos_of_pos (zero_lt_one.trans hA)
  have hscaled :
      1 < A ^ 2 *
        ∫ g : ℝ, truncatedGaussianSquare L g ∂(gaussianReal 0 1) :=
    (inv_lt_iff_one_lt_mul₀' hA_sq_pos).mp hmean
  obtain ⟨ε, δ, hε, hδ, hgap⟩ :=
    exists_eps_delta_of_one_lt_mul hA_sq_pos hscaled
  exact ⟨L, ε, δ, hL, hε, hδ, hgap⟩

/-- The sum of the truncated squared coordinates of a Gaussian vector. -/
def truncatedGaussianSum (L : ℝ) (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  ∑ i, truncatedGaussianSquare L (g i)

/-- The empirical average of the truncated squared coordinates, in the
normalization used by the paper's truncated Cramér estimate. -/
noncomputable def truncatedGaussianAverage
    (L : ℝ) (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * truncatedGaussianSum L N g

lemma measurable_truncatedGaussianSum (L : ℝ) (N : ℕ) :
    Measurable (truncatedGaussianSum L N) := by
  unfold truncatedGaussianSum
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_truncatedGaussianSquare L).comp (measurable_pi_apply i)

lemma truncatedGaussianSum_nonneg (L : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    0 ≤ truncatedGaussianSum L N g := by
  exact Finset.sum_nonneg fun _ _ => truncatedGaussianSquare_nonneg _ _

lemma measurable_truncatedGaussianAverage (L : ℝ) (N : ℕ) :
    Measurable (truncatedGaussianAverage L N) := by
  unfold truncatedGaussianAverage
  exact (measurable_truncatedGaussianSum L N).const_mul _

lemma truncatedGaussianAverage_nonneg (L : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    0 ≤ truncatedGaussianAverage L N g := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
    (truncatedGaussianSum_nonneg L N g)

/-- In positive dimension, the empirical average of the truncated squared
Gaussian coordinates is almost surely positive. -/
lemma ae_truncatedGaussianAverage_one_pos {N : ℕ} (hN : 0 < N) :
    ∀ᵐ g : Fin N → ℝ ∂gaussianVec N,
      0 < truncatedGaussianAverage 1 N g := by
  let i₀ : Fin N := ⟨0, hN⟩
  have hcoord_ae :
      ∀ᵐ g : Fin N → ℝ ∂gaussianVec N, g i₀ ≠ 0 := by
    rw [ae_iff]
    simp only [not_ne_iff]
    change gaussianVec N {g : Fin N → ℝ | g i₀ = 0} = 0
    have hset :
        {g : Fin N → ℝ | g i₀ = 0} =
          (Function.eval i₀) ⁻¹' ({(0 : ℝ)} : Set ℝ) := by
      ext g
      simp [Function.eval]
    rw [hset, ← Measure.map_apply
      (measurable_pi_apply i₀ : Measurable (Function.eval i₀))
      (measurableSet_singleton 0), gaussianVec, Measure.pi_map_eval]
    simp [gaussianReal_singleton_zero]
  filter_upwards [hcoord_ae] with g hg
  have hterm :
      truncatedGaussianSquare 1 (g i₀) ≤
        truncatedGaussianSum 1 N g := by
    unfold truncatedGaussianSum
    exact Finset.single_le_sum
      (fun j _ => truncatedGaussianSquare_nonneg 1 (g j))
      (Finset.mem_univ i₀)
  have hterm_pos : 0 < truncatedGaussianSquare 1 (g i₀) := by
    unfold truncatedGaussianSquare
    exact lt_min (sq_pos_of_ne_zero hg) (by norm_num)
  unfold truncatedGaussianAverage
  exact mul_pos (inv_pos.mpr (by exact_mod_cast hN))
    (hterm_pos.trans_le hterm)

/-- Truncated squared Gaussian coordinates remain mutually independent. -/
lemma iIndepFun_gaussian_coordinate_truncatedSquare (L : ℝ) (N : ℕ) :
    iIndepFun
      (fun i (g : Fin N → ℝ) => truncatedGaussianSquare L (g i))
      (gaussianVec N) := by
  have hEval :
      iIndepFun (fun i (g : Fin N → ℝ) => g i) (gaussianVec N) := by
    unfold gaussianVec
    exact iIndepFun_pi fun _ => aemeasurable_id
  change iIndepFun
    (fun i => truncatedGaussianSquare L ∘ fun g : Fin N → ℝ => g i)
    (gaussianVec N)
  exact hEval.comp (fun _ => truncatedGaussianSquare L)
    (fun _ => measurable_truncatedGaussianSquare L)

/-- The centered truncated squared Gaussian coordinates remain mutually
independent. -/
lemma iIndepFun_truncatedGaussianSquare_eval_sub_mean
    (L : ℝ) (N : ℕ) :
    iIndepFun
      (fun i (g : Fin N → ℝ) =>
        truncatedGaussianSquare L (g i) - truncatedGaussianSquareMean L)
      (gaussianVec N) := by
  have hcomp :=
    (iIndepFun_gaussian_coordinate_truncatedSquare L N).comp
      (fun _ x => x - truncatedGaussianSquareMean L)
      (fun _ => measurable_id.sub measurable_const)
  change iIndepFun
    (fun i =>
      (fun x => x - truncatedGaussianSquareMean L) ∘
        (fun g : Fin N → ℝ => truncatedGaussianSquare L (g i)))
    (gaussianVec N)
  exact hcomp

/-- The truncated Gaussian empirical average satisfies the lower-tail
Hoeffding bound with range length `L²`. -/
lemma measureReal_truncatedGaussianAverage_le_mean_sub_le
    {L ε : ℝ} {N : ℕ} (hL : 0 < L) (hN : 0 < N)
    (hε : 0 ≤ ε) :
    (gaussianVec N).real
        {g : Fin N → ℝ |
          truncatedGaussianAverage L N g ≤
            truncatedGaussianSquareMean L - ε} ≤
      Real.exp (-2 * (N : ℝ) * ε ^ 2 / L ^ 4) := by
  let c : NNReal :=
    NNReal.mk (((N : ℝ)⁻¹) ^ 2) (sq_nonneg ((N : ℝ)⁻¹)) *
      ∑ _i : Fin N, ((‖L ^ 2‖₊ / 2) ^ 2)
  have hsum :
      HasSubgaussianMGF
        (fun g : Fin N → ℝ =>
          ∑ i : Fin N,
            (truncatedGaussianSquare L (g i) -
              truncatedGaussianSquareMean L))
        (∑ _i : Fin N, ((‖L ^ 2‖₊ / 2) ^ 2))
        (gaussianVec N) := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun
      (iIndepFun_truncatedGaussianSquare_eval_sub_mean L N)
      (s := Finset.univ)
      (fun i _ =>
        hasSubgaussianMGF_truncatedGaussianSquare_eval_sub_mean L i)
  have havg :
      HasSubgaussianMGF
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage L N g -
            truncatedGaussianSquareMean L)
        c (gaussianVec N) := by
    have hscaled := hsum.const_mul ((N : ℝ)⁻¹)
    change HasSubgaussianMGF _ c _ at hscaled
    apply hscaled.congr
    filter_upwards with g
    unfold truncatedGaussianAverage truncatedGaussianSum
    simp only [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
  have hc : (c : ℝ) = L ^ 4 / (4 * N) := by
    dsimp only [c]
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_pow,
      NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      NNReal.coe_natCast]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg L)]
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    ring
  have hset :
      {g : Fin N → ℝ |
          truncatedGaussianAverage L N g ≤
            truncatedGaussianSquareMean L - ε} =
        {g : Fin N → ℝ |
          ε ≤ -(truncatedGaussianAverage L N g -
            truncatedGaussianSquareMean L)} := by
    ext g
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hg <;> linarith
  rw [hset]
  calc
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) :=
      havg.neg.measure_ge_le hε
    _ = Real.exp (-2 * (N : ℝ) * ε ^ 2 / L ^ 4) := by
      congr 1
      rw [hc]
      have hLne : L ≠ 0 := hL.ne'
      have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      ring

/-- The Laplace transform of the truncated coordinate sum factors into the
`N`-th power of the one-coordinate Laplace transform. -/
lemma integral_exp_neg_truncatedGaussianSum
    (L t : ℝ) (N : ℕ) :
    (∫ g : Fin N → ℝ, Real.exp (-t * truncatedGaussianSum L N g)
        ∂(gaussianVec N)) =
      (∫ x : ℝ, Real.exp (-t * truncatedGaussianSquare L x)
        ∂(gaussianReal 0 1)) ^ N := by
  have hcoord (i : Fin N) :
      mgf
          (fun g : Fin N → ℝ => truncatedGaussianSquare L (g i))
          (gaussianVec N) (-t) =
        ∫ x : ℝ, Real.exp (-t * truncatedGaussianSquare L x)
          ∂(gaussianReal 0 1) := by
    change mgf
        (truncatedGaussianSquare L ∘ fun g : Fin N → ℝ => g i)
        (gaussianVec N) (-t) =
      ∫ x : ℝ, Real.exp (-t * truncatedGaussianSquare L x)
        ∂(gaussianReal 0 1)
    rw [← mgf_id_map
      ((measurable_truncatedGaussianSquare L).comp
        (measurable_pi_apply i) |>.aemeasurable)]
    rw [← Measure.map_map (μ := gaussianVec N)
      (f := fun g : Fin N → ℝ => g i)
      (g := truncatedGaussianSquare L)
      (measurable_truncatedGaussianSquare L) (measurable_pi_apply i)]
    unfold gaussianVec
    rw [Measure.pi_map_eval]
    simp only [measure_univ, Finset.prod_const_one, one_smul]
    rw [mgf_id_map (measurable_truncatedGaussianSquare L).aemeasurable]
    rw [mgf]
  have hsum :=
    (iIndepFun_gaussian_coordinate_truncatedSquare L N).mgf_sum
      (fun i =>
        (measurable_truncatedGaussianSquare L).comp (measurable_pi_apply i))
      (Finset.univ : Finset (Fin N)) (t := -t)
  rw [show truncatedGaussianSum L N =
      ∑ i : Fin N,
        (fun g : Fin N → ℝ => truncatedGaussianSquare L (g i)) by
    funext g
    simp only [truncatedGaussianSum, Finset.sum_apply]]
  rw [mgf] at hsum
  rw [hsum]
  simp_rw [hcoord]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The exact one-coordinate comparison behind the paper's truncated
Laplace-transform estimate. -/
lemma integral_exp_neg_truncatedGaussianSquare_one_le_add
    {t : ℝ} (ht : 1 ≤ t) :
    (∫ x : ℝ, Real.exp (-t * truncatedGaussianSquare 1 x)
        ∂(gaussianReal 0 1)) ≤
      ((1 / 2 : ℝ) / (1 / 2 + t)) ^ (1 / 2 : ℝ) + Real.exp (-t) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hleft_int :
      Integrable
        (fun x : ℝ => Real.exp (-t * truncatedGaussianSquare 1 x))
        (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_truncatedGaussianSquare 1).const_mul (-t) |>.exp
        |>.aestronglyMeasurable) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht0)
        (truncatedGaussianSquare_nonneg 1 x)))
  have hsq_int :
      Integrable (fun x : ℝ => Real.exp (-t * x ^ 2))
        (gaussianReal 0 1) := by
    simpa only [neg_mul] using
      integrable_exp_mul_sq_gaussianReal_of_lt
        (t := -t) (by linarith)
  have hconst_int :
      Integrable (fun _x : ℝ => Real.exp (-t)) (gaussianReal 0 1) :=
    integrable_const _
  calc
    (∫ x : ℝ, Real.exp (-t * truncatedGaussianSquare 1 x)
        ∂(gaussianReal 0 1))
        ≤ ∫ x : ℝ, (Real.exp (-t * x ^ 2) + Real.exp (-t))
            ∂(gaussianReal 0 1) := by
          apply integral_mono hleft_int (hsq_int.add hconst_int)
          intro x
          by_cases hx : x ^ 2 ≤ 1
          · simp only [truncatedGaussianSquare, one_pow, min_eq_left hx,
              Pi.add_apply]
            exact le_add_of_nonneg_right (Real.exp_pos _).le
          · have hx' : (1 : ℝ) ≤ x ^ 2 := le_of_not_ge hx
            simp only [truncatedGaussianSquare, one_pow, min_eq_right hx',
              Pi.add_apply, mul_one]
            exact le_add_of_nonneg_left (Real.exp_pos _).le
    _ = (∫ x : ℝ, Real.exp (-t * x ^ 2) ∂(gaussianReal 0 1)) +
          Real.exp (-t) := by
      rw [integral_add hsq_int hconst_int, integral_const]
      simp
    _ = ((1 / 2 : ℝ) / (1 / 2 + t)) ^ (1 / 2 : ℝ) +
          Real.exp (-t) := by
      rw [show (∫ x : ℝ, Real.exp (-t * x ^ 2) ∂(gaussianReal 0 1)) =
          mgf (fun x : ℝ => x ^ 2) (gaussianReal 0 1) (-t) by
        rw [mgf]]
      rw [mgf_sq_gaussianReal_of_lt (by linarith)]
      congr 2
      ring

/-- For `λ ≥ 1`, the Laplace transform of `min(G²,1)` decays at the
paper's `λ⁻¹/²` rate, with the explicit constant `2`. -/
lemma integral_exp_neg_truncatedGaussianSquare_one_le
    {t : ℝ} (ht : 1 ≤ t) :
    (∫ x : ℝ, Real.exp (-t * truncatedGaussianSquare 1 x)
        ∂(gaussianReal 0 1)) ≤
      2 / Real.sqrt t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hsqrtt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hfrac :
      (1 / 2 : ℝ) / (1 / 2 + t) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have hgauss :
      ((1 / 2 : ℝ) / (1 / 2 + t)) ^ (1 / 2 : ℝ) ≤
        1 / Real.sqrt t := by
    rw [← Real.sqrt_eq_rpow]
    calc
      Real.sqrt ((1 / 2 : ℝ) / (1 / 2 + t))
          ≤ Real.sqrt (1 / t) :=
        Real.sqrt_le_sqrt hfrac
      _ = 1 / Real.sqrt t := by
        rw [Real.sqrt_div (by positivity)]
        simp
  have hexp : Real.exp (-t) ≤ 1 / Real.sqrt t := by
    rw [Real.exp_neg]
    have htexp : t ≤ Real.exp t := by
      linarith [Real.add_one_le_exp t]
    have hinv : (Real.exp t)⁻¹ ≤ t⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos t) ht0).2 htexp
    calc
      (Real.exp t)⁻¹ ≤ t⁻¹ := hinv
      _ ≤ (Real.sqrt t)⁻¹ := by
        apply (inv_le_inv₀ ht0 hsqrtt).2
        nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t]
      _ = 1 / Real.sqrt t := by rw [one_div]
  calc
    (∫ x : ℝ, Real.exp (-t * truncatedGaussianSquare 1 x)
        ∂(gaussianReal 0 1))
        ≤ ((1 / 2 : ℝ) / (1 / 2 + t)) ^ (1 / 2 : ℝ) +
            Real.exp (-t) :=
      integral_exp_neg_truncatedGaussianSquare_one_le_add ht
    _ ≤ 1 / Real.sqrt t + 1 / Real.sqrt t :=
      add_le_add hgauss hexp
    _ = 2 / Real.sqrt t := by ring

/-- The one-coordinate Laplace bound tensorizes to the full truncated
Gaussian coordinate sum. -/
lemma integral_exp_neg_truncatedGaussianSum_one_le
    {t : ℝ} (ht : 1 ≤ t) (N : ℕ) :
    (∫ g : Fin N → ℝ,
      Real.exp (-t * truncatedGaussianSum 1 N g) ∂(gaussianVec N)) ≤
        (2 / Real.sqrt t) ^ N := by
  rw [integral_exp_neg_truncatedGaussianSum]
  exact pow_le_pow_left₀
    (integral_nonneg fun _ => (Real.exp_pos _).le)
    (integral_exp_neg_truncatedGaussianSquare_one_le ht) N

/-- For `0 < p < N / 2`, the negative `p`-moment of the empirical average of
the truncated Gaussian squares is finite, with an explicit bound. -/
theorem integrable_neg_rpow_truncatedGaussianAverage_one_and_integral_le
    {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : 0 < p)
    (hpN : p < (N : ℝ) / 2) :
    Integrable
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage 1 N g ^ (-p))
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ,
          truncatedGaussianAverage 1 N g ^ (-p) ∂(gaussianVec N)) ≤
        (Real.Gamma p)⁻¹ *
          ((N : ℝ) ^ p / p +
            ((2 : ℝ) ^ N * (N : ℝ) ^ ((N : ℝ) / 2)) *
              ((N : ℝ) ^ (p - (N : ℝ) / 2) /
                ((N : ℝ) / 2 - p))) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let C : ℝ := (2 : ℝ) ^ N * (N : ℝ) ^ ((N : ℝ) / 2)
  let B : ℝ → ℝ := fun t =>
    if t ≤ (N : ℝ) then 1 else C * t ^ (-(N : ℝ) / 2)
  have htail_identity {t : ℝ} (ht : 0 < t) :
      (2 / Real.sqrt (t / (N : ℝ))) ^ N =
        C * t ^ (-(N : ℝ) / 2) := by
    dsimp only [C]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
    rw [Real.div_rpow (by norm_num)
      (Real.rpow_nonneg (div_nonneg ht.le hNreal.le) _)]
    rw [← Real.rpow_mul (div_nonneg ht.le hNreal.le)]
    rw [Real.div_rpow ht.le hNreal.le]
    rw [show (1 / 2 : ℝ) * N = (N : ℝ) / 2 by ring]
    rw [show -(N : ℝ) / 2 = -((N : ℝ) / 2) by ring]
    rw [Real.rpow_neg ht.le, Real.rpow_natCast]
    have htne : t ^ ((N : ℝ) / 2) ≠ 0 :=
      (Real.rpow_pos_of_pos ht _).ne'
    field_simp
  have hsmall_pow :
      IntegrableOn (fun t : ℝ => t ^ (p - 1)) (Set.Ioc 0 (N : ℝ)) := by
    refine IntegrableOn.congr_set_ae
      ((intervalIntegral.integrableOn_Ioo_rpow_iff hNreal).2 (by linarith)) ?_
    exact
      (Ioo_ae_eq_Ioc :
        Set.Ioo (0 : ℝ) (N : ℝ) =ᵐ[volume]
          Set.Ioc (0 : ℝ) (N : ℝ)).symm
  have htail_pow :
      IntegrableOn
        (fun t : ℝ => t ^ (p - 1 - (N : ℝ) / 2))
        (Set.Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNreal
  have hsmall :
      IntegrableOn (fun t : ℝ => t ^ (p - 1) * B t)
        (Set.Ioc 0 (N : ℝ)) := by
    refine hsmall_pow.congr_fun ?_ measurableSet_Ioc
    intro t ht
    simp only [B, if_pos ht.2, mul_one]
  have htail :
      IntegrableOn (fun t : ℝ => t ^ (p - 1) * B t)
        (Set.Ioi (N : ℝ)) := by
    have htail_const :
        IntegrableOn
          (fun t : ℝ => C * t ^ (p - 1 - (N : ℝ) / 2))
          (Set.Ioi (N : ℝ)) :=
      htail_pow.const_mul C
    refine htail_const.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := hNreal.trans ht
    have htn : ¬t ≤ (N : ℝ) := not_le.mpr ht
    simp only [B, if_neg htn]
    rw [show t ^ (p - 1) * (C * t ^ (-(N : ℝ) / 2)) =
        C * (t ^ (p - 1) * t ^ (-(N : ℝ) / 2)) by ring]
    rw [← Real.rpow_add ht0]
    congr 1
    ring_nf
  have hB :
      IntegrableOn (fun t : ℝ => t ^ (p - 1) * B t) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hNreal.le]
    exact hsmall.union htail
  have hLaplace :
      ∀ t : ℝ, 0 < t →
        (∫ g : Fin N → ℝ,
          Real.exp (-(t * truncatedGaussianAverage 1 N g))
            ∂(gaussianVec N)) ≤ B t := by
    intro t ht
    by_cases htn : t ≤ (N : ℝ)
    · have hint :
          Integrable
            (fun g : Fin N → ℝ =>
              Real.exp (-(t * truncatedGaussianAverage 1 N g)))
            (gaussianVec N) := by
        refine (integrable_const (1 : ℝ)).mono'
          ((measurable_truncatedGaussianAverage 1 N).const_mul t |>.neg
            |>.exp |>.aestronglyMeasurable) ?_
        filter_upwards with g
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr
            (mul_nonneg ht.le
              (truncatedGaussianAverage_nonneg 1 N g)))
      simp only [B, if_pos htn]
      calc
        (∫ g : Fin N → ℝ,
            Real.exp (-(t * truncatedGaussianAverage 1 N g))
              ∂(gaussianVec N))
            ≤ ∫ _g : Fin N → ℝ, (1 : ℝ) ∂(gaussianVec N) := by
              apply integral_mono hint (integrable_const 1)
              intro g
              exact Real.exp_le_one_iff.mpr
                (neg_nonpos.mpr
                  (mul_nonneg ht.le
                    (truncatedGaussianAverage_nonneg 1 N g)))
        _ = 1 := by simp
    · have htN : 1 ≤ t / (N : ℝ) := by
        rw [le_div_iff₀ hNreal]
        simpa using (lt_of_not_ge htn).le
      simp only [B, if_neg htn]
      calc
        (∫ g : Fin N → ℝ,
            Real.exp (-(t * truncatedGaussianAverage 1 N g))
              ∂(gaussianVec N))
            =
            ∫ g : Fin N → ℝ,
              Real.exp (-(t / (N : ℝ)) *
                truncatedGaussianSum 1 N g) ∂(gaussianVec N) := by
              apply integral_congr_ae
              filter_upwards with g
              congr 1
              unfold truncatedGaussianAverage
              field_simp
        _ ≤ (2 / Real.sqrt (t / (N : ℝ))) ^ N :=
          integral_exp_neg_truncatedGaussianSum_one_le htN N
        _ = C * t ^ (-(N : ℝ) / 2) := htail_identity ht
  have hmoment :=
    integrable_neg_rpow_and_integral_le_of_laplace_le
      (measurable_truncatedGaussianAverage 1 N)
      (ae_truncatedGaussianAverage_one_pos hN) hp hB hLaplace
  refine ⟨hmoment.1, hmoment.2.trans_eq ?_⟩
  congr 1
  rw [← Set.Ioc_union_Ioi_eq_Ioi hNreal.le,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      hsmall htail]
  have hsmall_integral :
      (∫ t in Set.Ioc (0 : ℝ) (N : ℝ),
          t ^ (p - 1) * B t) =
        (N : ℝ) ^ p / p := by
    rw [show (∫ t in Set.Ioc (0 : ℝ) (N : ℝ),
        t ^ (p - 1) * B t) =
      ∫ t in Set.Ioc (0 : ℝ) (N : ℝ), t ^ (p - 1) by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp only [B, if_pos ht.2, mul_one]]
    rw [← intervalIntegral.integral_of_le hNreal.le,
      integral_rpow (Or.inl (by linarith))]
    simp [hp.ne']
  have htail_integral :
      (∫ t in Set.Ioi (N : ℝ), t ^ (p - 1) * B t) =
        C * ((N : ℝ) ^ (p - (N : ℝ) / 2) /
          ((N : ℝ) / 2 - p)) := by
    rw [show (∫ t in Set.Ioi (N : ℝ), t ^ (p - 1) * B t) =
      ∫ t in Set.Ioi (N : ℝ),
        C * t ^ (p - 1 - (N : ℝ) / 2) by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := hNreal.trans ht
      have htn : ¬t ≤ (N : ℝ) := not_le.mpr ht
      simp only [B, if_neg htn]
      rw [show t ^ (p - 1) * (C * t ^ (-(N : ℝ) / 2)) =
          C * (t ^ (p - 1) * t ^ (-(N : ℝ) / 2)) by ring]
      rw [← Real.rpow_add ht0]
      congr 1
      ring_nf]
    rw [integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) hNreal]
    congr 1
    rw [show p - 1 - (N : ℝ) / 2 + 1 =
        p - (N : ℝ) / 2 by ring]
    rw [show (N : ℝ) / 2 - p = -(p - (N : ℝ) / 2) by ring,
      div_neg]
    ring
  rw [hsmall_integral, htail_integral]

/-- The truncated-Gaussian negative-moment estimate in the exponential-ready
form used by the paper. -/
theorem integrable_neg_rpow_truncatedGaussianAverage_one_and_integral_le_exp
    {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : 0 < p)
    (hpN : p < (N : ℝ) / 2) :
    Integrable
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage 1 N g ^ (-p))
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ,
          truncatedGaussianAverage 1 N g ^ (-p) ∂(gaussianVec N)) ≤
        Real.exp (p + 1) * ((N : ℝ) / p) ^ p *
          (1 + p * (2 : ℝ) ^ N / ((N : ℝ) / 2 - p)) := by
  have hraw :=
    integrable_neg_rpow_truncatedGaussianAverage_one_and_integral_le
      hN hp hpN
  refine ⟨hraw.1, hraw.2.trans ?_⟩
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) / 2 - p := sub_pos.mpr hpN
  have htail_rpow :
      (N : ℝ) ^ ((N : ℝ) / 2) *
          (N : ℝ) ^ (p - (N : ℝ) / 2) =
        (N : ℝ) ^ p := by
    rw [← Real.rpow_add hNreal]
    congr 1
    ring
  have hbracket :
      (N : ℝ) ^ p / p +
          ((2 : ℝ) ^ N * (N : ℝ) ^ ((N : ℝ) / 2)) *
            ((N : ℝ) ^ (p - (N : ℝ) / 2) /
              ((N : ℝ) / 2 - p)) =
        ((N : ℝ) ^ p / p) *
          (1 + p * (2 : ℝ) ^ N / ((N : ℝ) / 2 - p)) := by
    calc
      _ = (N : ℝ) ^ p / p +
          (2 : ℝ) ^ N *
            ((N : ℝ) ^ ((N : ℝ) / 2) *
              (N : ℝ) ^ (p - (N : ℝ) / 2)) /
                ((N : ℝ) / 2 - p) := by ring
      _ = (N : ℝ) ^ p / p +
          (2 : ℝ) ^ N * (N : ℝ) ^ p /
            ((N : ℝ) / 2 - p) := by rw [htail_rpow]
      _ = ((N : ℝ) ^ p / p) *
          (1 + p * (2 : ℝ) ^ N / ((N : ℝ) / 2 - p)) := by
            field_simp [hp.ne', hden.ne']
  have hGamma_factor :
      (Real.Gamma p)⁻¹ * ((N : ℝ) ^ p / p) =
        (N : ℝ) ^ p / Real.Gamma (p + 1) := by
    simp only [Real.Gamma_add_one hp.ne', div_eq_mul_inv, mul_inv]
    ring
  have hQ :
      0 ≤ 1 + p * (2 : ℝ) ^ N / ((N : ℝ) / 2 - p) := by
    positivity
  rw [hbracket, ← mul_assoc, hGamma_factor]
  exact mul_le_mul_of_nonneg_right
    (rpow_div_Gamma_add_one_le_exp_mul_div_rpow hNreal.le hp) hQ

/-- Fixed-fraction specialization of the truncated-Gaussian negative-moment
estimate, with an exponential-in-dimension upper bound. -/
theorem integrable_neg_rpow_truncatedGaussianAverage_one_mul_dimension_and_integral_le
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (1 / 2 : ℝ))
    {N : ℕ} (hN : 0 < N) :
    Integrable
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage 1 N g ^ (-(α * (N : ℝ))))
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ,
          truncatedGaussianAverage 1 N g ^ (-(α * (N : ℝ)))
            ∂(gaussianVec N)) ≤
        Real.exp 1 / (1 - 2 * α) *
          (2 * Real.exp α * α ^ (-α)) ^ N := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp : 0 < α * (N : ℝ) := mul_pos hα.1 hNreal
  have hpN : α * (N : ℝ) < (N : ℝ) / 2 := by
    have := mul_lt_mul_of_pos_right hα.2 hNreal
    linarith
  have hmoment :=
    integrable_neg_rpow_truncatedGaussianAverage_one_and_integral_le_exp
      hN hp hpN
  refine ⟨hmoment.1, hmoment.2.trans ?_⟩
  have hdenα : 0 < 1 - 2 * α := by linarith [hα.2]
  have hdenN : 0 < (N : ℝ) / 2 - α * (N : ℝ) :=
    sub_pos.mpr hpN
  have hexpN :
      Real.exp (α * (N : ℝ) + 1) =
        Real.exp 1 * (Real.exp α) ^ N := by
    have hexpMul :
        Real.exp (α * (N : ℝ)) = (Real.exp α) ^ N := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [Real.exp_add, hexpMul]
    ring
  have hratioBase :
      (N : ℝ) / (α * (N : ℝ)) = α⁻¹ := by
    field_simp
  have hratioPow :
      ((N : ℝ) / (α * (N : ℝ))) ^ (α * (N : ℝ)) =
        (α ^ (-α)) ^ N := by
    rw [hratioBase]
    calc
      α⁻¹ ^ (α * (N : ℝ)) =
          α ^ (-(α * (N : ℝ))) :=
        (Real.rpow_neg_eq_inv_rpow α (α * (N : ℝ))).symm
      _ = α ^ ((-α) * (N : ℝ)) := by
        congr 1
        ring
      _ = (α ^ (-α)) ^ N :=
        Real.rpow_mul_natCast hα.1.le (-α) N
  have hscale :
      Real.exp (α * (N : ℝ) + 1) *
          ((N : ℝ) / (α * (N : ℝ))) ^ (α * (N : ℝ)) =
        Real.exp 1 * (Real.exp α * α ^ (-α)) ^ N := by
    rw [hexpN, hratioPow, mul_pow]
    ring
  have hQeq :
      1 + (α * (N : ℝ)) * (2 : ℝ) ^ N /
          ((N : ℝ) / 2 - α * (N : ℝ)) =
        1 + 2 * α * (2 : ℝ) ^ N / (1 - 2 * α) := by
    field_simp [hNreal.ne', hdenN.ne', hdenα.ne']
  have htwoPow : 1 ≤ (2 : ℝ) ^ N :=
    one_le_pow₀ (by norm_num)
  have hQle :
      1 + (α * (N : ℝ)) * (2 : ℝ) ^ N /
          ((N : ℝ) / 2 - α * (N : ℝ)) ≤
        (2 : ℝ) ^ N / (1 - 2 * α) := by
    rw [hQeq]
    calc
      1 + 2 * α * (2 : ℝ) ^ N / (1 - 2 * α) =
          ((1 - 2 * α) + 2 * α * (2 : ℝ) ^ N) /
            (1 - 2 * α) := by
              field_simp [hdenα.ne']
      _ ≤ (2 : ℝ) ^ N / (1 - 2 * α) := by
        apply (div_le_div_iff_of_pos_right hdenα).2
        nlinarith
  calc
    Real.exp (α * (N : ℝ) + 1) *
          ((N : ℝ) / (α * (N : ℝ))) ^ (α * (N : ℝ)) *
          (1 + (α * (N : ℝ)) * (2 : ℝ) ^ N /
            ((N : ℝ) / 2 - α * (N : ℝ)))
        =
        Real.exp 1 * (Real.exp α * α ^ (-α)) ^ N *
          (1 + (α * (N : ℝ)) * (2 : ℝ) ^ N /
            ((N : ℝ) / 2 - α * (N : ℝ))) := by rw [hscale]
    _ ≤ Real.exp 1 * (Real.exp α * α ^ (-α)) ^ N *
          ((2 : ℝ) ^ N / (1 - 2 * α)) := by
      exact mul_le_mul_of_nonneg_left hQle
        (mul_nonneg (Real.exp_pos 1).le
          (pow_nonneg
            (mul_nonneg (Real.exp_pos α).le
              (Real.rpow_nonneg hα.1.le _)) N))
    _ = Real.exp 1 / (1 - 2 * α) *
          (2 * Real.exp α * α ^ (-α)) ^ N := by
      simp only [mul_pow]
      ring

/-- Raising the truncation level above one can only decrease the fixed-fraction
negative moment, so the level-one exponential bound remains valid. -/
theorem integrable_neg_rpow_truncatedGaussianAverage_mul_dimension_and_integral_le
    {α : ℝ} (hα : α ∈ Set.Ioo 0 (1 / 2 : ℝ))
    {N : ℕ} (hN : 0 < N) {L : ℝ} (hL : 1 ≤ L) :
    Integrable
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage L N g ^ (-(α * (N : ℝ))))
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ,
          truncatedGaussianAverage L N g ^ (-(α * (N : ℝ)))
            ∂(gaussianVec N)) ≤
        Real.exp 1 / (1 - 2 * α) *
          (2 * Real.exp α * α ^ (-α)) ^ N := by
  have hone :=
    integrable_neg_rpow_truncatedGaussianAverage_one_mul_dimension_and_integral_le
      hα hN
  have hLsq : (1 : ℝ) ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ zero_le_one (zero_le_one.trans hL)).2 hL
  have havg (g : Fin N → ℝ) :
      truncatedGaussianAverage 1 N g ≤
        truncatedGaussianAverage L N g := by
    unfold truncatedGaussianAverage
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
    unfold truncatedGaussianSum
    apply Finset.sum_le_sum
    intro i _
    unfold truncatedGaussianSquare
    exact min_le_min le_rfl hLsq
  have hpow_nonpos : -(α * (N : ℝ)) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg hα.1.le (Nat.cast_nonneg N))
  have hpowle :
      ∀ᵐ g : Fin N → ℝ ∂(gaussianVec N),
        truncatedGaussianAverage L N g ^ (-(α * (N : ℝ))) ≤
          truncatedGaussianAverage 1 N g ^ (-(α * (N : ℝ))) := by
    filter_upwards [ae_truncatedGaussianAverage_one_pos hN] with g hg
    exact Real.rpow_le_rpow_of_nonpos hg (havg g) hpow_nonpos
  have hmeasL :
      AEStronglyMeasurable
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage L N g ^ (-(α * (N : ℝ))))
        (gaussianVec N) := by
    have hrpow :
        Measurable (fun x : ℝ => x ^ (-(α * (N : ℝ)))) := by
      fun_prop
    exact
      (hrpow.comp (measurable_truncatedGaussianAverage L N)).aestronglyMeasurable
  have hLint :
      Integrable
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage L N g ^ (-(α * (N : ℝ))))
        (gaussianVec N) := by
    refine Integrable.mono' hone.1 hmeasL ?_
    filter_upwards [hpowle] with g hg
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (Real.rpow_nonneg (truncatedGaussianAverage_nonneg L N g) _)]
    exact hg
  refine ⟨hLint, ?_⟩
  exact
    (integral_mono_ae hLint hone.1 hpowle).trans hone.2

/-- On the lower-tail bad event, Hölder interpolation combines the
fixed-fraction negative-moment estimate with the truncated Gaussian Hoeffding
bound. -/
theorem integrableOn_neg_rpow_truncatedGaussianAverage_badEvent_and_integral_le
    {α γ : ℝ} (hα : α ∈ Set.Ioo 0 (1 / 2 : ℝ))
    (hγ : 0 < γ) (hγα : γ < α)
    {N : ℕ} (hN : 0 < N) {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ) :
    IntegrableOn
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage L N g ^ (-(γ * (N : ℝ))))
        {g : Fin N → ℝ |
          truncatedGaussianAverage L N g ≤
            truncatedGaussianSquareMean L - δ}
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ in
          {g | truncatedGaussianAverage L N g ≤
            truncatedGaussianSquareMean L - δ},
          truncatedGaussianAverage L N g ^ (-(γ * (N : ℝ)))
            ∂(gaussianVec N)) ≤
        (Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
          ((2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
            Real.exp
              (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hθ0 : 0 < γ / α := div_pos hγ hα.1
  have hθ1 : γ / α < 1 := (div_lt_one hα.1).2 hγα
  have h1θ0 : 0 ≤ 1 - γ / α := sub_nonneg.mpr hθ1.le
  let s : Set (Fin N → ℝ) :=
    {g | truncatedGaussianAverage L N g ≤
      truncatedGaussianSquareMean L - δ}
  have hs : MeasurableSet s := by
    dsimp only [s]
    exact measurableSet_le
      (measurable_truncatedGaussianAverage L N) measurable_const
  have hLsq : (1 : ℝ) ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ zero_le_one (zero_le_one.trans hL)).2 hL
  have havg (g : Fin N → ℝ) :
      truncatedGaussianAverage 1 N g ≤
        truncatedGaussianAverage L N g := by
    unfold truncatedGaussianAverage
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
    unfold truncatedGaussianSum
    apply Finset.sum_le_sum
    intro i _
    unfold truncatedGaussianSquare
    exact min_le_min le_rfl hLsq
  have hXpos :
      ∀ᵐ g : Fin N → ℝ ∂(gaussianVec N),
        0 < truncatedGaussianAverage L N g := by
    filter_upwards [ae_truncatedGaussianAverage_one_pos hN] with g hg
    exact hg.trans_le (havg g)
  have hmoment :=
    integrable_neg_rpow_truncatedGaussianAverage_mul_dimension_and_integral_le
      hα hN hL
  have hmoment_integrable :
      Integrable
        (fun g : Fin N → ℝ =>
          truncatedGaussianAverage L N g ^ (-α * (N : ℝ)))
        (gaussianVec N) := by
    simpa only [neg_mul] using hmoment.1
  have hholder :=
    integrableOn_neg_rpow_and_setIntegral_neg_rpow_le
      hXpos hNreal hγ hγα hmoment_integrable hs
  have hholder_bound :
      (∫ g : Fin N → ℝ in
          {g | truncatedGaussianAverage L N g ≤
            truncatedGaussianSquareMean L - δ},
          truncatedGaussianAverage L N g ^ (-(γ * (N : ℝ)))
            ∂(gaussianVec N)) ≤
        (∫ g : Fin N → ℝ,
          truncatedGaussianAverage L N g ^ (-(α * (N : ℝ)))
            ∂(gaussianVec N)) ^ (γ / α) *
          ((gaussianVec N).real s) ^ (1 - γ / α) := by
    simpa only [s, neg_mul] using hholder.2
  refine ⟨by simpa only [s, neg_mul] using hholder.1,
    hholder_bound.trans ?_⟩
  have hprob :=
    measureReal_truncatedGaussianAverage_le_mean_sub_le hLpos hN hδ
  have hmoment_nonneg :
      0 ≤ ∫ g : Fin N → ℝ,
        truncatedGaussianAverage L N g ^ (-(α * (N : ℝ)))
          ∂(gaussianVec N) :=
    integral_nonneg fun g =>
      Real.rpow_nonneg (truncatedGaussianAverage_nonneg L N g) _
  have hmoment_rpow :
      (∫ g : Fin N → ℝ,
          truncatedGaussianAverage L N g ^ (-(α * (N : ℝ)))
            ∂(gaussianVec N)) ^ (γ / α) ≤
        (Real.exp 1 / (1 - 2 * α) *
          (2 * Real.exp α * α ^ (-α)) ^ N) ^ (γ / α) :=
    Real.rpow_le_rpow hmoment_nonneg hmoment.2 hθ0.le
  have hprob_rpow :
      ((gaussianVec N).real s) ^ (1 - γ / α) ≤
        (Real.exp (-2 * (N : ℝ) * δ ^ 2 / L ^ 4)) ^
          (1 - γ / α) :=
    Real.rpow_le_rpow measureReal_nonneg hprob h1θ0
  calc
    (∫ g : Fin N → ℝ,
        truncatedGaussianAverage L N g ^ (-(α * (N : ℝ)))
          ∂(gaussianVec N)) ^ (γ / α) *
        ((gaussianVec N).real s) ^ (1 - γ / α) ≤
      (Real.exp 1 / (1 - 2 * α) *
        (2 * Real.exp α * α ^ (-α)) ^ N) ^ (γ / α) *
        (Real.exp (-2 * (N : ℝ) * δ ^ 2 / L ^ 4)) ^
          (1 - γ / α) := by
      exact mul_le_mul hmoment_rpow hprob_rpow
        (Real.rpow_nonneg measureReal_nonneg _)
        (Real.rpow_nonneg
          (mul_nonneg
            (div_nonneg (Real.exp_pos 1).le (by linarith [hα.2]))
            (pow_nonneg
              (mul_nonneg
                (mul_nonneg (by norm_num) (Real.exp_pos α).le)
                (Real.rpow_nonneg hα.1.le _)) N)) _)
    _ = (Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
          ((2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
            Real.exp
              (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N := by
      have hC : 0 ≤ Real.exp 1 / (1 - 2 * α) := by
        exact div_nonneg (Real.exp_pos 1).le (by linarith [hα.2])
      have hB : 0 ≤ 2 * Real.exp α * α ^ (-α) :=
        mul_nonneg
          (mul_nonneg (by norm_num) (Real.exp_pos α).le)
          (Real.rpow_nonneg hα.1.le _)
      rw [Real.mul_rpow hC (pow_nonneg hB N)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
      rw [mul_comm (N : ℝ) (γ / α),
        Real.rpow_mul_natCast hB (γ / α) N]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      have hexp :
          Real.exp
              (-2 * (N : ℝ) * δ ^ 2 / L ^ 4 * (1 - γ / α)) =
            (Real.exp
              (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [hexp, mul_pow]
      ring

/-- The bad-event negative-moment estimate is unchanged in form after inserting
the paper's positive deterministic scale `(1 - ε) A²`. -/
theorem
    integrableOn_neg_rpow_scaled_truncatedGaussianAverage_badEvent_and_integral_le
    {A ε α γ : ℝ} (hA : 1 < A) (hε : ε ∈ Set.Ioo 0 1)
    (hα : α ∈ Set.Ioo 0 (1 / 2 : ℝ))
    (hγ : 0 < γ) (hγα : γ < α)
    {N : ℕ} (hN : 0 < N) {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ) :
    IntegrableOn
        (fun g : Fin N → ℝ =>
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))))
        {g : Fin N → ℝ |
          truncatedGaussianAverage L N g ≤
            truncatedGaussianSquareMean L - δ}
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ in
          {g | truncatedGaussianAverage L N g ≤
            truncatedGaussianSquareMean L - δ},
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))) ∂(gaussianVec N)) ≤
        (Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
          (((1 - ε) * A ^ 2) ^ (-γ) *
            (2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
            Real.exp
              (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N := by
  let c : ℝ := (1 - ε) * A ^ 2
  let s : Set (Fin N → ℝ) :=
    {g | truncatedGaussianAverage L N g ≤
      truncatedGaussianSquareMean L - δ}
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (sub_pos.mpr hε.2) (sq_pos_of_pos (zero_lt_one.trans hA))
  have hbad :=
    integrableOn_neg_rpow_truncatedGaussianAverage_badEvent_and_integral_le
      hα hγ hγα hN hL hδ
  have hrpow :
      (fun g : Fin N → ℝ =>
        c ^ (-(γ * (N : ℝ))) *
          truncatedGaussianAverage L N g ^ (-(γ * (N : ℝ)))) =ᵐ[
            (gaussianVec N).restrict s]
        (fun g =>
          (c * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ)))) := by
    filter_upwards with g
    rw [Real.mul_rpow hc.le (truncatedGaussianAverage_nonneg L N g)]
  have hprod_integrable :
      IntegrableOn
        (fun g : Fin N → ℝ =>
          c ^ (-(γ * (N : ℝ))) *
            truncatedGaussianAverage L N g ^ (-(γ * (N : ℝ))))
        s (gaussianVec N) :=
    hbad.1.const_mul _
  have hscaled_integrable :
      IntegrableOn
        (fun g : Fin N → ℝ =>
          (c * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))))
        s (gaussianVec N) :=
    hprod_integrable.congr hrpow
  refine ⟨by simpa only [c, s] using hscaled_integrable, ?_⟩
  calc
    (∫ g : Fin N → ℝ in
        {g | truncatedGaussianAverage L N g ≤
          truncatedGaussianSquareMean L - δ},
        ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
          (-(γ * (N : ℝ))) ∂(gaussianVec N)) =
      c ^ (-(γ * (N : ℝ))) *
        ∫ g : Fin N → ℝ in s,
          truncatedGaussianAverage L N g ^ (-(γ * (N : ℝ)))
            ∂(gaussianVec N) := by
      rw [show (1 - ε) * A ^ 2 = c from rfl]
      rw [show {g : Fin N → ℝ |
          truncatedGaussianAverage L N g ≤
            truncatedGaussianSquareMean L - δ} = s from rfl]
      rw [← integral_const_mul]
      exact (integral_congr_ae hrpow).symm
    _ ≤ c ^ (-(γ * (N : ℝ))) *
        ((Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
          ((2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
            Real.exp
              (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N) := by
      exact mul_le_mul_of_nonneg_left hbad.2 (Real.rpow_nonneg hc.le _)
    _ = (Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
          (((1 - ε) * A ^ 2) ^ (-γ) *
            (2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
            Real.exp
              (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N := by
      have hcPow :
          c ^ (-(γ * (N : ℝ))) = (c ^ (-γ)) ^ N := by
        rw [show -(γ * (N : ℝ)) = (-γ) * (N : ℝ) by ring]
        exact Real.rpow_mul_natCast hc.le (-γ) N
      rw [hcPow]
      simp only [mul_pow]
      rw [show (1 - ε) * A ^ 2 = c from rfl]
      ring

/-- On the complement of the truncated lower-tail event, the paper's scaled
negative moment is bounded by the deterministic threshold `a ^ (-γN)`. -/
theorem
    integrableOn_neg_rpow_scaled_truncatedGaussianAverage_goodEvent_and_integral_le
    {A ε γ : ℝ} (hA : 1 < A) (hε : ε ∈ Set.Ioo 0 1) (hγ : 0 < γ)
    {N : ℕ} {L δ : ℝ}
    (ha : 1 <
      (1 - ε) * A ^ 2 * (truncatedGaussianSquareMean L - δ)) :
    IntegrableOn
        (fun g : Fin N → ℝ =>
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))))
        {g : Fin N → ℝ |
          truncatedGaussianSquareMean L - δ <
            truncatedGaussianAverage L N g}
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ in
          {g | truncatedGaussianSquareMean L - δ <
            truncatedGaussianAverage L N g},
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))) ∂(gaussianVec N)) ≤
        ((1 - ε) * A ^ 2 *
          (truncatedGaussianSquareMean L - δ)) ^
            (-(γ * (N : ℝ))) := by
  let c : ℝ := (1 - ε) * A ^ 2
  let a : ℝ := c * (truncatedGaussianSquareMean L - δ)
  let s : Set (Fin N → ℝ) :=
    {g | truncatedGaussianSquareMean L - δ <
      truncatedGaussianAverage L N g}
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (sub_pos.mpr hε.2) (sq_pos_of_pos (zero_lt_one.trans hA))
  have ha' : 0 < a := zero_lt_one.trans ha
  have hs : MeasurableSet s := by
    dsimp only [s]
    exact measurableSet_lt measurable_const
      (measurable_truncatedGaussianAverage L N)
  have hp_nonpos : -(γ * (N : ℝ)) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg hγ.le (Nat.cast_nonneg N))
  have hpoint :
      ∀ g ∈ s,
        (c * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))) ≤
          a ^ (-(γ * (N : ℝ))) := by
    intro g hg
    apply Real.rpow_le_rpow_of_nonpos ha'
      (mul_le_mul_of_nonneg_left hg.le hc.le) hp_nonpos
  have hfmeas :
      AEStronglyMeasurable
        (fun g : Fin N → ℝ =>
          (c * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))))
        ((gaussianVec N).restrict s) := by
    have hrpow :
        Measurable (fun x : ℝ => x ^ (-(γ * (N : ℝ)))) := by
      fun_prop
    exact
      (hrpow.comp
        ((measurable_truncatedGaussianAverage L N).const_mul c))
        |>.aestronglyMeasurable.restrict
  have hconst :
      IntegrableOn
        (fun _g : Fin N → ℝ => a ^ (-(γ * (N : ℝ))))
        s (gaussianVec N) :=
    (integrable_const _).integrableOn
  have hfint :
      IntegrableOn
        (fun g : Fin N → ℝ =>
          (c * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))))
        s (gaussianVec N) := by
    refine hconst.mono' hfmeas ?_
    filter_upwards [ae_restrict_mem hs] with g hg
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (Real.rpow_nonneg
          (mul_nonneg hc.le (truncatedGaussianAverage_nonneg L N g)) _)]
    exact hpoint g hg
  refine ⟨by simpa only [c, s] using hfint, ?_⟩
  calc
    (∫ g : Fin N → ℝ in
        {g | truncatedGaussianSquareMean L - δ <
          truncatedGaussianAverage L N g},
        ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
          (-(γ * (N : ℝ))) ∂(gaussianVec N)) ≤
      ∫ _g : Fin N → ℝ in s,
        a ^ (-(γ * (N : ℝ))) ∂(gaussianVec N) := by
      apply integral_mono_ae
      · simpa only [IntegrableOn, c, s] using hfint
      · exact hconst
      · filter_upwards [ae_restrict_mem hs] with g hg
        simpa only [c, s] using hpoint g hg
    _ = (gaussianVec N).real s * a ^ (-(γ * (N : ℝ))) := by
      rw [setIntegral_const]
      simp
    _ ≤ a ^ (-(γ * (N : ℝ))) := by
      exact mul_le_of_le_one_left (Real.rpow_nonneg ha'.le _)
        measureReal_le_one
    _ = ((1 - ε) * A ^ 2 *
          (truncatedGaussianSquareMean L - δ)) ^
            (-(γ * (N : ℝ))) := by rfl

/-- Splitting into the truncated lower-tail event and its complement gives the
paper's fixed-parameter full negative-moment estimate. -/
theorem
    integrable_neg_rpow_scaled_truncatedGaussianAverage_and_integral_le
    {A ε α γ : ℝ} (hA : 1 < A) (hε : ε ∈ Set.Ioo 0 1)
    (hα : α ∈ Set.Ioo 0 (1 / 2 : ℝ))
    (hγ : 0 < γ) (hγα : γ < α)
    {N : ℕ} (hN : 0 < N) {L δ : ℝ} (hL : 1 ≤ L) (hδ : 0 ≤ δ)
    (ha : 1 <
      (1 - ε) * A ^ 2 * (truncatedGaussianSquareMean L - δ)) :
    Integrable
        (fun g : Fin N → ℝ =>
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))))
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ,
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))) ∂(gaussianVec N)) ≤
        ((1 - ε) * A ^ 2 *
          (truncatedGaussianSquareMean L - δ)) ^
            (-(γ * (N : ℝ))) +
          (Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
            (((1 - ε) * A ^ 2) ^ (-γ) *
              (2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
              Real.exp
                (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N := by
  let f : (Fin N → ℝ) → ℝ :=
    fun g =>
      ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
        (-(γ * (N : ℝ)))
  let s : Set (Fin N → ℝ) :=
    {g | truncatedGaussianAverage L N g ≤
      truncatedGaussianSquareMean L - δ}
  have hs : MeasurableSet s := by
    dsimp only [s]
    exact measurableSet_le
      (measurable_truncatedGaussianAverage L N) measurable_const
  have hbad :=
    integrableOn_neg_rpow_scaled_truncatedGaussianAverage_badEvent_and_integral_le
      hA hε hα hγ hγα hN hL hδ
  have hgood :=
    integrableOn_neg_rpow_scaled_truncatedGaussianAverage_goodEvent_and_integral_le
      hA hε hγ (N := N) (L := L) (δ := δ) ha
  have hbad_integrable : IntegrableOn f s (gaussianVec N) := by
    simpa only [f, s] using hbad.1
  have hgood_integrable : IntegrableOn f sᶜ (gaussianVec N) := by
    simpa only [f, s, Set.compl_setOf, not_le] using hgood.1
  have hfull : Integrable f (gaussianVec N) := by
    have hunion := hbad_integrable.union hgood_integrable
    simpa only [Set.union_compl_self, integrableOn_univ] using hunion
  have hbad_bound :
      (∫ g : Fin N → ℝ in s, f g ∂(gaussianVec N)) ≤
        (Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
          (((1 - ε) * A ^ 2) ^ (-γ) *
            (2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
            Real.exp
              (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N := by
    simpa only [f, s] using hbad.2
  have hgood_bound :
      (∫ g : Fin N → ℝ in sᶜ, f g ∂(gaussianVec N)) ≤
        ((1 - ε) * A ^ 2 *
          (truncatedGaussianSquareMean L - δ)) ^
            (-(γ * (N : ℝ))) := by
    simpa only [f, s, Set.compl_setOf, not_le] using hgood.2
  refine ⟨by simpa only [f] using hfull, ?_⟩
  calc
    (∫ g : Fin N → ℝ,
        ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
          (-(γ * (N : ℝ))) ∂(gaussianVec N)) =
      (∫ g : Fin N → ℝ in s, f g ∂(gaussianVec N)) +
        ∫ g : Fin N → ℝ in sᶜ, f g ∂(gaussianVec N) := by
      simpa only [f] using (integral_add_compl hs hfull).symm
    _ ≤
        (Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
            (((1 - ε) * A ^ 2) ^ (-γ) *
              (2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
              Real.exp
                (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N +
          ((1 - ε) * A ^ 2 *
            (truncatedGaussianSquareMean L - δ)) ^
              (-(γ * (N : ℝ))) :=
      add_le_add hbad_bound hgood_bound
    _ =
        ((1 - ε) * A ^ 2 *
          (truncatedGaussianSquareMean L - δ)) ^
            (-(γ * (N : ℝ))) +
          (Real.exp 1 / (1 - 2 * α)) ^ (γ / α) *
            (((1 - ε) * A ^ 2) ^ (-γ) *
              (2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
              Real.exp
                (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) ^ N := by
      ring

/-- For fixed truncation and loss parameters, a sufficiently small fractional
exponent makes both bases in the good/bad-event estimate exponentially
contractive with one common positive rate. -/
theorem exists_fractional_exponent_and_rate_for_scaled_truncatedGaussianAverage
    {A ε α L δ : ℝ} (hA : 1 < A) (hε : ε ∈ Set.Ioo 0 1)
    (hα : α ∈ Set.Ioo 0 (1 / 2 : ℝ)) (hL : 1 ≤ L) (hδ : 0 < δ)
    (ha : 1 <
      (1 - ε) * A ^ 2 * (truncatedGaussianSquareMean L - δ)) :
    ∃ γ κ : ℝ,
      γ ∈ Set.Ioo 0 α ∧ 0 < κ ∧
        ((1 - ε) * A ^ 2 *
          (truncatedGaussianSquareMean L - δ)) ^ (-γ) ≤
            Real.exp (-κ) ∧
        ((1 - ε) * A ^ 2) ^ (-γ) *
            (2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
            Real.exp
              (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α)) ≤
          Real.exp (-κ) := by
  let c : ℝ := (1 - ε) * A ^ 2
  let a : ℝ := c * (truncatedGaussianSquareMean L - δ)
  let B : ℝ := 2 * Real.exp α * α ^ (-α)
  let badBase : ℝ → ℝ := fun γ =>
    c ^ (-γ) * B ^ (γ / α) *
      Real.exp (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (sub_pos.mpr hε.2) (sq_pos_of_pos (zero_lt_one.trans hA))
  have ha' : 1 < a := by simpa only [a, c] using ha
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos
      (mul_pos (by norm_num) (Real.exp_pos α))
      (Real.rpow_pos_of_pos hα.1 _)
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hdecay :
      0 < 2 * δ ^ 2 / L ^ 4 := by
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hδ))
      (pow_pos hLpos 4)
  have hbad_cont : ContinuousAt badBase 0 := by
    dsimp only [badBase]
    have hcPow : Continuous (fun γ : ℝ => c ^ (-γ)) :=
      (Real.continuous_const_rpow hc.ne').comp continuous_id.neg
    have hBPow : Continuous (fun γ : ℝ => B ^ (γ / α)) :=
      (Real.continuous_const_rpow hB.ne').comp (continuous_id.div_const α)
    have hExp : Continuous (fun γ : ℝ =>
        Real.exp (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))) := by
      fun_prop
    exact ((hcPow.mul hBPow).mul hExp).continuousAt
  have hbad_zero :
      badBase 0 = Real.exp (-2 * δ ^ 2 / L ^ 4) := by
    simp [badBase]
  have hbad_zero_lt : badBase 0 < 1 := by
    rw [hbad_zero, Real.exp_lt_one_iff]
    rw [show -2 * δ ^ 2 / L ^ 4 =
      -(2 * δ ^ 2 / L ^ 4) by ring]
    exact neg_neg_of_pos hdecay
  have hbad_near :
      ∀ᶠ γ : ℝ in 𝓝 0, badBase γ < 1 :=
    (tendsto_order.1 hbad_cont.tendsto).2 1 hbad_zero_lt
  have hα_near : ∀ᶠ γ : ℝ in 𝓝 0, γ < α :=
    Iio_mem_nhds hα.1
  have hselected :
      ∀ᶠ γ : ℝ in 𝓝[>] 0,
        badBase γ < 1 ∧ γ < α ∧ 0 < γ := by
    filter_upwards [
      Filter.Eventually.filter_mono inf_le_left hbad_near,
      Filter.Eventually.filter_mono inf_le_left hα_near,
      self_mem_nhdsWithin] with γ hbadγ hγα hγ
    exact ⟨hbadγ, hγα, hγ⟩
  obtain ⟨γ, hbadγ, hγα, hγ⟩ := hselected.exists
  let goodBase : ℝ := a ^ (-γ)
  let ρ : ℝ := max goodBase (badBase γ)
  have hgood_pos : 0 < goodBase :=
    Real.rpow_pos_of_pos (zero_lt_one.trans ha') _
  have hgood_lt : goodBase < 1 := by
    dsimp only [goodBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg ha' (neg_neg_of_pos hγ)
  have hρpos : 0 < ρ :=
    hgood_pos.trans_le (le_max_left _ _)
  have hρlt : ρ < 1 := by
    exact max_lt_iff.mpr ⟨hgood_lt, hbadγ⟩
  let κ : ℝ := -Real.log ρ
  have hκ : 0 < κ := by
    dsimp only [κ]
    exact neg_pos.mpr (Real.log_neg hρpos hρlt)
  have hexp : Real.exp (-κ) = ρ := by
    rw [show -κ = Real.log ρ by simp only [κ, neg_neg]]
    exact Real.exp_log hρpos
  refine ⟨γ, κ, ⟨hγ, hγα⟩, hκ, ?_, ?_⟩
  · rw [hexp]
    simpa only [goodBase, a, c] using le_max_left goodBase (badBase γ)
  · rw [hexp]
    simpa only [badBase, B, c] using le_max_right goodBase (badBase γ)

/-- With the truncation and loss parameters fixed, the paper's scaled
truncated negative moment is exponentially small in every sufficiently large
positive dimension. -/
theorem
    exists_eventually_integrable_neg_rpow_scaled_truncatedGaussianAverage
    {A ε α L δ : ℝ} (hA : 1 < A) (hε : ε ∈ Set.Ioo 0 1)
    (hα : α ∈ Set.Ioo 0 (1 / 2 : ℝ)) (hL : 1 ≤ L) (hδ : 0 < δ)
    (ha : 1 <
      (1 - ε) * A ^ 2 * (truncatedGaussianSquareMean L - δ)) :
    ∃ γ κ : ℝ, ∃ N₀ : ℕ,
      γ ∈ Set.Ioo 0 α ∧ 0 < κ ∧
        ∀ N : ℕ, N₀ ≤ N → 0 < N →
          Integrable
              (fun g : Fin N → ℝ =>
                ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
                  (-(γ * (N : ℝ))))
              (gaussianVec N) ∧
            (∫ g : Fin N → ℝ,
                ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
                  (-(γ * (N : ℝ))) ∂(gaussianVec N)) ≤
              Real.exp (-(κ * (N : ℝ))) := by
  obtain ⟨γ, κ₀, hγ, hκ₀, hgoodBase, hbadBase⟩ :=
    exists_fractional_exponent_and_rate_for_scaled_truncatedGaussianAverage
      hA hε hα hL hδ ha
  let C : ℝ := (Real.exp 1 / (1 - 2 * α)) ^ (γ / α)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact Real.rpow_nonneg
      (div_nonneg (Real.exp_pos 1).le (by linarith [hα.2])) _
  have hκhalf : 0 < κ₀ / 2 := half_pos hκ₀
  have hgrowth :
      Tendsto (fun N : ℕ => Real.exp ((κ₀ / 2) * (N : ℝ)))
        atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hκhalf)
  have hprefactor :
      ∀ᶠ N : ℕ in atTop,
        1 + C ≤ Real.exp ((κ₀ / 2) * (N : ℝ)) :=
    hgrowth.eventually_ge_atTop (1 + C)
  rw [Filter.eventually_atTop] at hprefactor
  obtain ⟨N₀, hN₀⟩ := hprefactor
  refine ⟨γ, κ₀ / 2, N₀, hγ, hκhalf, ?_⟩
  intro N hN₀' hN
  have hfixed :=
    integrable_neg_rpow_scaled_truncatedGaussianAverage_and_integral_le
      hA hε hα hγ.1 hγ.2 hN hL hδ.le ha
  let a : ℝ :=
    (1 - ε) * A ^ 2 * (truncatedGaussianSquareMean L - δ)
  let b : ℝ :=
    ((1 - ε) * A ^ 2) ^ (-γ) *
      (2 * Real.exp α * α ^ (-α)) ^ (γ / α) *
      Real.exp (-2 * δ ^ 2 / L ^ 4 * (1 - γ / α))
  have haPos : 0 < a := by
    exact zero_lt_one.trans (by simpa only [a] using ha)
  have hbNonneg : 0 ≤ b := by
    dsimp only [b]
    have hcPos : 0 < (1 - ε) * A ^ 2 :=
      mul_pos (sub_pos.mpr hε.2) (sq_pos_of_pos (zero_lt_one.trans hA))
    have hBPos : 0 < 2 * Real.exp α * α ^ (-α) :=
      mul_pos
        (mul_pos (by norm_num) (Real.exp_pos α))
        (Real.rpow_pos_of_pos hα.1 _)
    exact
      (mul_pos
        (mul_pos
          (Real.rpow_pos_of_pos hcPos _)
          (Real.rpow_pos_of_pos hBPos _))
        (Real.exp_pos _)).le
  have hgoodPow :
      a ^ (-(γ * (N : ℝ))) ≤ (Real.exp (-κ₀)) ^ N := by
    rw [show -(γ * (N : ℝ)) = (-γ) * (N : ℝ) by ring,
      Real.rpow_mul_natCast haPos.le (-γ) N]
    exact pow_le_pow_left₀ (Real.rpow_nonneg haPos.le _) hgoodBase N
  have hbadPow :
      b ^ N ≤ (Real.exp (-κ₀)) ^ N :=
    pow_le_pow_left₀ hbNonneg hbadBase N
  have hmoment :
      (∫ g : Fin N → ℝ,
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))) ∂(gaussianVec N)) ≤
        (1 + C) * (Real.exp (-κ₀)) ^ N := by
    calc
      (∫ g : Fin N → ℝ,
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))) ∂(gaussianVec N)) ≤
        a ^ (-(γ * (N : ℝ))) + C * b ^ N := by
          simpa only [a, b, C] using hfixed.2
      _ ≤ (Real.exp (-κ₀)) ^ N +
          C * (Real.exp (-κ₀)) ^ N := by
        exact add_le_add hgoodPow
          (mul_le_mul_of_nonneg_left hbadPow hC)
      _ = (1 + C) * (Real.exp (-κ₀)) ^ N := by ring
  refine ⟨hfixed.1, hmoment.trans ?_⟩
  calc
    (1 + C) * (Real.exp (-κ₀)) ^ N ≤
        Real.exp ((κ₀ / 2) * (N : ℝ)) *
          (Real.exp (-κ₀)) ^ N := by
      exact mul_le_mul_of_nonneg_right (hN₀ N hN₀')
        (pow_nonneg (Real.exp_nonneg _) N)
    _ = Real.exp (-((κ₀ / 2) * (N : ℝ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- Paper-facing truncated Cramér estimate: every supercritical gain admits
fixed truncation and loss parameters for which a fractional negative moment
decays exponentially in all sufficiently large dimensions. -/
theorem exists_truncatedGaussianAverage_cramer_bound
    {A : ℝ} (hA : 1 < A) :
    ∃ γ κ L ε : ℝ, ∃ N₀ : ℕ,
      γ ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧ 0 < κ ∧
        1 ≤ L ∧ ε ∈ Set.Ioo 0 1 ∧
          ∀ N : ℕ, N₀ ≤ N → 0 < N →
            Integrable
                (fun g : Fin N → ℝ =>
                  ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
                    (-(γ * (N : ℝ))))
                (gaussianVec N) ∧
              (∫ g : Fin N → ℝ,
                  ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
                    (-(γ * (N : ℝ))) ∂(gaussianVec N)) ≤
                Real.exp (-(κ * (N : ℝ))) := by
  obtain ⟨L, ε, δ, hL, hε, hδ, hgap⟩ :=
    exists_truncatedGaussianSquare_parameters hA
  have hα : (1 / 4 : ℝ) ∈ Set.Ioo 0 (1 / 2 : ℝ) := by
    norm_num
  have hgap' :
      1 < (1 - ε) * A ^ 2 *
        (truncatedGaussianSquareMean L - δ) := by
    simpa only [truncatedGaussianSquareMean] using hgap
  obtain ⟨γ, κ, N₀, hγ, hκ, hbound⟩ :=
    exists_eventually_integrable_neg_rpow_scaled_truncatedGaussianAverage
      hA hε hα hL hδ hgap'
  have hγhalf : γ ∈ Set.Ioo 0 (1 / 2 : ℝ) :=
    ⟨hγ.1, hγ.2.trans hα.2⟩
  exact ⟨γ, κ, L, ε, N₀, hγhalf, hκ, hL, hε, hbound⟩

/-- Uniform small-argument form of the linearization
`tanh(x) / x → 1`, with the origin excluded because the quotient is written
without its continuous extension. -/
lemma exists_pos_forall_tanh_div_self_sq_ge_one_sub
    {ε : ℝ} (hε : ε ∈ Set.Ioo 0 1) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x : ℝ, x ≠ 0 → |x| ≤ η →
        1 - ε ≤ (Real.tanh x / x) ^ 2 := by
  have hlim :
      Tendsto (fun x : ℝ => (Real.tanh x / x) ^ 2)
        (𝓝[≠] 0) (𝓝 1) := by
    simpa using tendsto_tanh_div_self_one.pow 2
  have heventually :
      ∀ᶠ x : ℝ in 𝓝[≠] 0,
        1 - ε < (Real.tanh x / x) ^ 2 :=
    (tendsto_order.1 hlim).1 (1 - ε) (by linarith [hε.1])
  obtain ⟨η, hη, hηsub⟩ :=
    Metric.mem_nhdsWithin_iff.1 heventually
  refine ⟨η / 2, half_pos hη, ?_⟩
  intro x hx hxη
  have hxmem : x ∈ Metric.ball 0 η ∩ ({0} : Set ℝ)ᶜ := by
    constructor
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      exact hxη.trans_lt (half_lt_self hη)
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  exact (hηsub hxmem).le

/-- A small positive input radius transfers the uniform `tanh` linearization
to the paper's coordinatewise lower bound by the truncated square. -/
theorem exists_radius_truncatedGaussianSquare_le_tanh_sq_div
    {A L ε : ℝ} (hA : 1 < A) (hL : 1 ≤ L)
    (hε : ε ∈ Set.Ioo 0 1) :
    ∃ R₀ : ℝ, R₀ ∈ Set.Ioc 0 1 ∧
      ∀ g : ℝ,
        (1 - ε) * A ^ 2 * truncatedGaussianSquare L g ≤
          Real.tanh (A * Real.sqrt R₀ * g) ^ 2 / R₀ := by
  obtain ⟨η, hη, hratio⟩ :=
    exists_pos_forall_tanh_div_self_sq_ge_one_sub hε
  have hApos : 0 < A := zero_lt_one.trans hA
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let t : ℝ := min 1 (η / (A * L))
  let R₀ : ℝ := t ^ 2
  have htpos : 0 < t := by
    dsimp only [t]
    exact lt_min zero_lt_one (div_pos hη (mul_pos hApos hLpos))
  have ht_one : t ≤ 1 := min_le_left _ _
  have ht_eta : t ≤ η / (A * L) := min_le_right _ _
  have hR₀pos : 0 < R₀ := by
    dsimp only [R₀]
    exact sq_pos_of_pos htpos
  have hR₀one : R₀ ≤ 1 := by
    dsimp only [R₀]
    nlinarith
  have hsqrt : Real.sqrt R₀ = t := by
    dsimp only [R₀]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos htpos]
  have hscale : A * Real.sqrt R₀ * L ≤ η := by
    calc
      A * Real.sqrt R₀ * L = (A * L) * t := by rw [hsqrt]; ring
      _ ≤ (A * L) * (η / (A * L)) :=
        mul_le_mul_of_nonneg_left ht_eta (mul_pos hApos hLpos).le
      _ = η := by field_simp
  have hsmall (g : ℝ) (hg : g ≠ 0) (hgL : |g| ≤ L) :
      (1 - ε) * A ^ 2 * g ^ 2 ≤
        Real.tanh (A * Real.sqrt R₀ * g) ^ 2 / R₀ := by
    let x : ℝ := A * Real.sqrt R₀ * g
    have hx : x ≠ 0 := by
      dsimp only [x]
      exact mul_ne_zero
        (mul_ne_zero hApos.ne' (Real.sqrt_pos.2 hR₀pos).ne') hg
    have hx_abs : |x| ≤ η := by
      dsimp only [x]
      rw [abs_mul, abs_mul, abs_of_pos hApos,
        abs_of_nonneg (Real.sqrt_nonneg R₀)]
      exact (mul_le_mul_of_nonneg_left hgL
        (mul_nonneg hApos.le (Real.sqrt_nonneg R₀))).trans hscale
    have hratio_x := hratio x hx hx_abs
    have hx_sq : x ^ 2 = A ^ 2 * R₀ * g ^ 2 := by
      dsimp only [x]
      rw [mul_pow, mul_pow, Real.sq_sqrt hR₀pos.le]
    have heq :
        (Real.tanh x / x) ^ 2 * (A ^ 2 * g ^ 2) =
          Real.tanh x ^ 2 / R₀ := by
      rw [div_pow, hx_sq]
      field_simp [hApos.ne', hR₀pos.ne', hg]
    calc
      (1 - ε) * A ^ 2 * g ^ 2 =
          (1 - ε) * (A ^ 2 * g ^ 2) := by ring
      _ ≤ (Real.tanh x / x) ^ 2 * (A ^ 2 * g ^ 2) :=
        mul_le_mul_of_nonneg_right hratio_x
          (mul_nonneg (sq_nonneg A) (sq_nonneg g))
      _ = Real.tanh x ^ 2 / R₀ := heq
      _ = Real.tanh (A * Real.sqrt R₀ * g) ^ 2 / R₀ := by rfl
  refine ⟨R₀, ⟨hR₀pos, hR₀one⟩, ?_⟩
  intro g
  by_cases hg : g = 0
  · subst g
    rw [truncatedGaussianSquare, zero_pow (by norm_num),
      min_eq_left (sq_nonneg L)]
    norm_num
  by_cases hgL : |g| ≤ L
  · calc
      (1 - ε) * A ^ 2 * truncatedGaussianSquare L g ≤
          (1 - ε) * A ^ 2 * g ^ 2 := by
        exact mul_le_mul_of_nonneg_left (min_le_left _ _)
          (mul_nonneg (sub_nonneg.mpr hε.2.le) (sq_nonneg A))
      _ ≤ Real.tanh (A * Real.sqrt R₀ * g) ^ 2 / R₀ :=
        hsmall g hg hgL
  · have hLabs : L < |g| := lt_of_not_ge hgL
    have hLsq : L ^ 2 ≤ g ^ 2 := by
      rw [← sq_abs g]
      exact (sq_le_sq₀ hLpos.le (abs_nonneg g)).2 hLabs.le
    rw [truncatedGaussianSquare, min_eq_right hLsq]
    have hsmallL :
        (1 - ε) * A ^ 2 * L ^ 2 ≤
          Real.tanh (A * Real.sqrt R₀ * L) ^ 2 / R₀ :=
      hsmall L hLpos.ne' (by rw [abs_of_pos hLpos])
    have harg :
        A * Real.sqrt R₀ * L ≤ A * Real.sqrt R₀ * |g| :=
      mul_le_mul_of_nonneg_left hLabs.le
        (mul_nonneg hApos.le (Real.sqrt_nonneg R₀))
    have htanh :
        Real.tanh (A * Real.sqrt R₀ * L) ≤
          Real.tanh (A * Real.sqrt R₀ * |g|) :=
      tanh_strictMono.monotone harg
    have htanh_nonneg :
        0 ≤ Real.tanh (A * Real.sqrt R₀ * L) := by
      rw [← Real.tanh_zero]
      exact tanh_strictMono.monotone
        (mul_nonneg (mul_nonneg hApos.le (Real.sqrt_nonneg R₀)) hLpos.le)
    have htanh_sq :
        Real.tanh (A * Real.sqrt R₀ * L) ^ 2 ≤
          Real.tanh (A * Real.sqrt R₀ * |g|) ^ 2 :=
      pow_le_pow_left₀ htanh_nonneg htanh 2
    have heven :
        Real.tanh (A * Real.sqrt R₀ * |g|) ^ 2 =
          Real.tanh (A * Real.sqrt R₀ * g) ^ 2 := by
      rcases le_total 0 g with hg0 | hg0
      · rw [abs_of_nonneg hg0]
      · rw [abs_of_nonpos hg0]
        have hneg :
            A * Real.sqrt R₀ * -g = -(A * Real.sqrt R₀ * g) := by ring
        rw [hneg, Real.tanh_neg, neg_sq]
    exact hsmallL.trans
      ((div_le_div_iff_of_pos_right hR₀pos).2 (htanh_sq.trans_eq heven))

/-- Summing any coordinatewise truncated lower bound and inserting the common
empirical normalization gives the corresponding radial update-ratio bound. -/
lemma scaled_truncatedGaussianAverage_le_Fmap_div_of_forall
    {A L R c : ℝ}
    (hcoord : ∀ x : ℝ,
      c * truncatedGaussianSquare L x ≤
        Real.tanh (A * Real.sqrt R * x) ^ 2 / R)
    (N : ℕ) (g : Fin N → ℝ) :
    c * truncatedGaussianAverage L N g ≤ Fmap A N R g / R := by
  have hsum :
      ∑ i : Fin N, c * truncatedGaussianSquare L (g i) ≤
        ∑ i : Fin N, Real.tanh (A * Real.sqrt R * g i) ^ 2 / R :=
    Finset.sum_le_sum fun i _ => hcoord (g i)
  have hsum_div :
      (∑ i : Fin N, Real.tanh (A * Real.sqrt R * g i) ^ 2 / R) =
        (∑ i : Fin N, Real.tanh (A * Real.sqrt R * g i) ^ 2) / R := by
    exact
      (Finset.sum_div Finset.univ
        (fun i : Fin N => Real.tanh (A * Real.sqrt R * g i) ^ 2) R).symm
  calc
    c * truncatedGaussianAverage L N g =
        (N : ℝ)⁻¹ *
          ∑ i : Fin N, c * truncatedGaussianSquare L (g i) := by
      rw [truncatedGaussianAverage, truncatedGaussianSum,
        ← Finset.mul_sum]
      ring
    _ ≤ (N : ℝ)⁻¹ *
          ∑ i : Fin N, Real.tanh (A * Real.sqrt R * g i) ^ 2 / R :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = Fmap A N R g / R := by
      rw [hsum_div]
      unfold Fmap
      ring

/-- The coordinatewise truncated lower bound holds at one common positive
radius after summing and normalizing over every dimension. -/
theorem exists_radius_scaled_truncatedGaussianAverage_le_Fmap_div
    {A L ε : ℝ} (hA : 1 < A) (hL : 1 ≤ L)
    (hε : ε ∈ Set.Ioo 0 1) :
    ∃ R₀ : ℝ, R₀ ∈ Set.Ioc 0 1 ∧
      ∀ (N : ℕ) (g : Fin N → ℝ),
        (1 - ε) * A ^ 2 * truncatedGaussianAverage L N g ≤
          Fmap A N R₀ g / R₀ := by
  obtain ⟨R₀, hR₀, hcoord⟩ :=
    exists_radius_truncatedGaussianSquare_le_tanh_sq_div hA hL hε
  exact ⟨R₀, hR₀,
    scaled_truncatedGaussianAverage_le_Fmap_div_of_forall hcoord⟩

/-- Uniformly below one fixed positive radius, the negative moment of the
nonlinear radial update ratio inherits the truncated Cramér estimate. -/
theorem exists_radius_eventually_integrable_neg_rpow_Fmap_div
    {A : ℝ} (hA : 1 < A) :
    ∃ R₀ γ κ : ℝ, ∃ N₀ : ℕ,
      R₀ ∈ Set.Ioc 0 1 ∧ γ ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧ 0 < κ ∧
        ∀ N : ℕ, N₀ ≤ N → 0 < N →
          ∀ q : ℝ, 0 < q → q ≤ R₀ →
            Integrable
                (fun g : Fin N → ℝ =>
                  (Fmap A N q g / q) ^ (-(γ * (N : ℝ))))
                (gaussianVec N) ∧
              (∫ g : Fin N → ℝ,
                  (Fmap A N q g / q) ^ (-(γ * (N : ℝ)))
                    ∂(gaussianVec N)) ≤
                Real.exp (-(κ * (N : ℝ))) := by
  obtain ⟨γ, κ, L, ε, N₀, hγ, hκ, hL, hε, htruncated⟩ :=
    exists_truncatedGaussianAverage_cramer_bound hA
  obtain ⟨R₀, hR₀, hlower⟩ :=
    exists_radius_scaled_truncatedGaussianAverage_le_Fmap_div hA hL hε
  refine ⟨R₀, γ, κ, N₀, hR₀, hγ, hκ, ?_⟩
  intro N hN₀ hN q hq hqR₀
  have hbound := htruncated N hN₀ hN
  have hLsq : (1 : ℝ) ^ 2 ≤ L ^ 2 :=
    (sq_le_sq₀ zero_le_one (zero_le_one.trans hL)).2 hL
  have havg (g : Fin N → ℝ) :
      truncatedGaussianAverage 1 N g ≤
        truncatedGaussianAverage L N g := by
    unfold truncatedGaussianAverage
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
    unfold truncatedGaussianSum
    apply Finset.sum_le_sum
    intro i _
    unfold truncatedGaussianSquare
    exact min_le_min le_rfl hLsq
  have hscale : 0 < (1 - ε) * A ^ 2 :=
    mul_pos (sub_pos.mpr hε.2) (sq_pos_of_pos (zero_lt_one.trans hA))
  have hpow_nonpos : -(γ * (N : ℝ)) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg hγ.1.le (Nat.cast_nonneg N))
  have hpowle :
      ∀ᵐ g : Fin N → ℝ ∂(gaussianVec N),
        (Fmap A N q g / q) ^ (-(γ * (N : ℝ))) ≤
          ((1 - ε) * A ^ 2 * truncatedGaussianAverage L N g) ^
            (-(γ * (N : ℝ))) := by
    filter_upwards [ae_truncatedGaussianAverage_one_pos hN] with g hg
    exact Real.rpow_le_rpow_of_nonpos
      (mul_pos hscale (hg.trans_le (havg g)))
      ((hlower N g).trans (Fmap_div_ge_of_pos_of_le g hq hqR₀)) hpow_nonpos
  have hmeas :
      AEStronglyMeasurable
        (fun g : Fin N → ℝ =>
          (Fmap A N q g / q) ^ (-(γ * (N : ℝ))))
        (gaussianVec N) := by
    have hrpow :
        Measurable (fun x : ℝ => x ^ (-(γ * (N : ℝ)))) := by
      fun_prop
    exact
      (hrpow.comp
        ((continuous_Fmap_right A N q).measurable.div_const q))
        |>.aestronglyMeasurable
  have hint :
      Integrable
        (fun g : Fin N → ℝ =>
          (Fmap A N q g / q) ^ (-(γ * (N : ℝ))))
        (gaussianVec N) := by
    refine Integrable.mono' hbound.1 hmeas ?_
    filter_upwards [hpowle] with g hg
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (Real.rpow_nonneg
          (div_nonneg (Fmap_nonneg A N q g) hq.le) _)]
    exact hg
  exact ⟨hint, (integral_mono_ae hint hbound.1 hpowle).trans hbound.2⟩

/-- The uniform near-zero negative-moment radius may be chosen below any
prescribed positive cap. -/
theorem exists_radius_lt_eventually_integrable_neg_rpow_Fmap_div
    {A r : ℝ} (hA : 1 < A) (hr : 0 < r) :
    ∃ R₀ γ κ : ℝ, ∃ N₀ : ℕ,
      R₀ ∈ Set.Ioc 0 1 ∧ R₀ < r ∧
        γ ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧ 0 < κ ∧
          ∀ N : ℕ, N₀ ≤ N → 0 < N →
            ∀ q : ℝ, 0 < q → q ≤ R₀ →
              Integrable
                  (fun g : Fin N → ℝ =>
                    (Fmap A N q g / q) ^ (-(γ * (N : ℝ))))
                  (gaussianVec N) ∧
                (∫ g : Fin N → ℝ,
                    (Fmap A N q g / q) ^ (-(γ * (N : ℝ)))
                      ∂(gaussianVec N)) ≤
                  Real.exp (-(κ * (N : ℝ))) := by
  obtain ⟨S₀, γ, κ, N₀, hS₀, hγ, hκ, hbound⟩ :=
    exists_radius_eventually_integrable_neg_rpow_Fmap_div hA
  let R₀ : ℝ := min S₀ (r / 2)
  have hR₀pos : 0 < R₀ := by
    dsimp only [R₀]
    exact lt_min hS₀.1 (half_pos hr)
  have hR₀one : R₀ ≤ 1 :=
    (min_le_left S₀ (r / 2)).trans hS₀.2
  have hR₀r : R₀ < r :=
    (min_le_right S₀ (r / 2)).trans_lt (half_lt_self hr)
  refine ⟨R₀, γ, κ, N₀, ⟨hR₀pos, hR₀one⟩, hR₀r, hγ, hκ, ?_⟩
  intro N hN₀ hN q hq hqR₀
  exact hbound N hN₀ hN q hq
    (hqR₀.trans (min_le_left S₀ (r / 2)))

/-- The near-zero contraction radius can be placed strictly below the lower
endpoint of any positive-radius stable interval around the positive fixed
point. -/
theorem
    exists_radius_below_stableInterval_eventually_integrable_neg_rpow_Fmap_div
    {A qStar R : ℝ} (hA : 1 < A)
    (_hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hR : R ∈ Set.Ioo (0 : ℝ) qStar) :
    ∃ R₀ γ κ : ℝ, ∃ N₀ : ℕ,
      R₀ ∈ Set.Ioc 0 1 ∧ R₀ < qStar - R ∧
        γ ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧ 0 < κ ∧
          ∀ N : ℕ, N₀ ≤ N → 0 < N →
            ∀ q : ℝ, 0 < q → q ≤ R₀ →
              Integrable
                  (fun g : Fin N → ℝ =>
                    (Fmap A N q g / q) ^ (-(γ * (N : ℝ))))
                  (gaussianVec N) ∧
                (∫ g : Fin N → ℝ,
                    (Fmap A N q g / q) ^ (-(γ * (N : ℝ)))
                      ∂(gaussianVec N)) ≤
                  Real.exp (-(κ * (N : ℝ))) := by
  exact exists_radius_lt_eventually_integrable_neg_rpow_Fmap_div
    hA (sub_pos.mpr hR.2)

/-- Uniformly over radii bounded away from zero, one positive coefficient
times the coordinatewise truncation `min(g², 1)` bounds the nonlinear squared
coordinate update. -/
theorem exists_pos_forall_truncatedGaussianSquare_one_le_tanh_sq
    {A R₀ : ℝ} (hA : 1 < A) (hR₀ : R₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ q ∈ Set.Icc R₀ 1, ∀ g : ℝ,
        c * truncatedGaussianSquare 1 g ≤
          Real.tanh (A * Real.sqrt q * g) ^ 2 := by
  let α : ℝ := min (A ^ 2 * R₀) 1
  let c : ℝ := Real.tanh 1 ^ 2 * α
  have hApos : 0 < A := zero_lt_one.trans hA
  have hαpos : 0 < α := by
    dsimp only [α]
    exact lt_min (mul_pos (sq_pos_of_pos hApos) hR₀.1) zero_lt_one
  have htanh : 0 < Real.tanh 1 := by
    rw [← Real.tanh_zero]
    exact tanh_strictMono zero_lt_one
  refine ⟨c, mul_pos (sq_pos_of_pos htanh) hαpos, ?_⟩
  intro q hq g
  have hscaled :
      (A ^ 2 * R₀) * g ^ 2 ≤ (A ^ 2 * q) * g ^ 2 := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hq.1 (sq_nonneg A)) (sq_nonneg g)
  have hsq :
      (A * Real.sqrt q * g) ^ 2 = (A ^ 2 * q) * g ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (hR₀.1.le.trans hq.1)]
  have hmin :
      α * min (g ^ 2) 1 ≤ min ((A * Real.sqrt q * g) ^ 2) 1 := by
    apply le_min
    · rw [hsq]
      calc
        α * min (g ^ 2) 1 ≤
            (A ^ 2 * R₀) * min (g ^ 2) 1 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _)
            (le_min (sq_nonneg g) zero_le_one)
        _ ≤ (A ^ 2 * R₀) * g ^ 2 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _)
            (mul_nonneg (sq_nonneg A) hR₀.1.le)
        _ ≤ (A ^ 2 * q) * g ^ 2 := hscaled
    · exact mul_le_one₀ (min_le_right _ _)
        (le_min (sq_nonneg g) zero_le_one) (min_le_right _ _)
  calc
    c * truncatedGaussianSquare 1 g =
        Real.tanh 1 ^ 2 * (α * min (g ^ 2) 1) := by
      unfold c truncatedGaussianSquare
      ring_nf
    _ ≤ Real.tanh 1 ^ 2 * min ((A * Real.sqrt q * g) ^ 2) 1 :=
      mul_le_mul_of_nonneg_left hmin (sq_nonneg _)
    _ ≤ Real.tanh (A * Real.sqrt q * g) ^ 2 :=
      tanh_one_sq_mul_min_sq_one_le _

/-- Summing the coordinatewise lower bound gives one truncated empirical
average bound uniformly over all dimensions and radii bounded away from
zero. -/
theorem exists_pos_forall_scaled_truncatedGaussianAverage_one_le_Fmap
    {A R₀ : ℝ} (hA : 1 < A) (hR₀ : R₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ q ∈ Set.Icc R₀ 1, ∀ (N : ℕ) (g : Fin N → ℝ),
        c * truncatedGaussianAverage 1 N g ≤ Fmap A N q g := by
  obtain ⟨c, hc, hcoord⟩ :=
    exists_pos_forall_truncatedGaussianSquare_one_le_tanh_sq hA hR₀
  refine ⟨c, hc, ?_⟩
  intro q hq N g
  have hsum :
      ∑ i : Fin N, c * truncatedGaussianSquare 1 (g i) ≤
        ∑ i : Fin N, Real.tanh (A * Real.sqrt q * g i) ^ 2 :=
    Finset.sum_le_sum fun i _ => hcoord q hq (g i)
  calc
    c * truncatedGaussianAverage 1 N g =
        (N : ℝ)⁻¹ *
          ∑ i : Fin N, c * truncatedGaussianSquare 1 (g i) := by
      rw [truncatedGaussianAverage, truncatedGaussianSum,
        ← Finset.mul_sum]
      ring
    _ ≤ (N : ℝ)⁻¹ *
          ∑ i : Fin N, Real.tanh (A * Real.sqrt q * g i) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = Fmap A N q g := by
      unfold Fmap
      rfl

/-- The explicit level-one truncated negative-moment estimate transfers
uniformly to the nonlinear update on every radius interval bounded away from
zero. -/
theorem exists_pos_forall_integrable_neg_rpow_Fmap_and_integral_le
    {A R₀ γ : ℝ} (hA : 1 < A) (hR₀ : R₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hγ : γ ∈ Set.Ioo 0 (1 / 2 : ℝ)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ N : ℕ, 0 < N → ∀ q ∈ Set.Icc R₀ 1,
        Integrable
            (fun g : Fin N → ℝ =>
              Fmap A N q g ^ (-(γ * (N : ℝ))))
            (gaussianVec N) ∧
          (∫ g : Fin N → ℝ,
              Fmap A N q g ^ (-(γ * (N : ℝ)))
                ∂(gaussianVec N)) ≤
            Real.exp 1 / (1 - 2 * γ) *
              (c ^ (-γ) * (2 * Real.exp γ * γ ^ (-γ))) ^ N := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_pos_forall_scaled_truncatedGaussianAverage_one_le_Fmap hA hR₀
  refine ⟨c, hc, ?_⟩
  intro N hN q hq
  have htruncated :=
    integrable_neg_rpow_truncatedGaussianAverage_mul_dimension_and_integral_le
      hγ hN (L := 1) (by norm_num)
  have hp_nonpos : -(γ * (N : ℝ)) ≤ 0 :=
    neg_nonpos.mpr (mul_nonneg hγ.1.le (Nat.cast_nonneg N))
  have hpowle :
      ∀ᵐ g : Fin N → ℝ ∂(gaussianVec N),
        Fmap A N q g ^ (-(γ * (N : ℝ))) ≤
          (c * truncatedGaussianAverage 1 N g) ^
            (-(γ * (N : ℝ))) := by
    filter_upwards [ae_truncatedGaussianAverage_one_pos hN] with g hg
    exact Real.rpow_le_rpow_of_nonpos
      (mul_pos hc hg) (hlower q hq N g) hp_nonpos
  have hscale_eq (g : Fin N → ℝ) :
      (c * truncatedGaussianAverage 1 N g) ^
          (-(γ * (N : ℝ))) =
        c ^ (-(γ * (N : ℝ))) *
          truncatedGaussianAverage 1 N g ^ (-(γ * (N : ℝ))) := by
    exact Real.mul_rpow hc.le (truncatedGaussianAverage_nonneg 1 N g)
  have hscaled_int :
      Integrable
        (fun g : Fin N → ℝ =>
          (c * truncatedGaussianAverage 1 N g) ^
            (-(γ * (N : ℝ))))
        (gaussianVec N) := by
    rw [show
      (fun g : Fin N → ℝ =>
        (c * truncatedGaussianAverage 1 N g) ^ (-(γ * (N : ℝ)))) =
      fun g =>
        c ^ (-(γ * (N : ℝ))) *
          truncatedGaussianAverage 1 N g ^ (-(γ * (N : ℝ))) by
        funext g
        exact hscale_eq g]
    exact htruncated.1.const_mul _
  have hmeas :
      AEStronglyMeasurable
        (fun g : Fin N → ℝ =>
          Fmap A N q g ^ (-(γ * (N : ℝ))))
        (gaussianVec N) := by
    have hrpow :
        Measurable (fun x : ℝ => x ^ (-(γ * (N : ℝ)))) := by
      fun_prop
    exact
      (hrpow.comp (continuous_Fmap_right A N q).measurable)
        |>.aestronglyMeasurable
  have hint :
      Integrable
        (fun g : Fin N → ℝ =>
          Fmap A N q g ^ (-(γ * (N : ℝ))))
        (gaussianVec N) := by
    refine Integrable.mono' hscaled_int hmeas ?_
    filter_upwards [hpowle] with g hg
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Fmap_nonneg A N q g) _)]
    exact hg
  refine ⟨hint, (integral_mono_ae hint hscaled_int hpowle).trans ?_⟩
  rw [show
      (fun g : Fin N → ℝ =>
        (c * truncatedGaussianAverage 1 N g) ^ (-(γ * (N : ℝ)))) =
      fun g =>
        c ^ (-(γ * (N : ℝ))) *
          truncatedGaussianAverage 1 N g ^ (-(γ * (N : ℝ))) by
        funext g
        exact hscale_eq g,
    integral_const_mul]
  calc
    c ^ (-(γ * (N : ℝ))) *
        ∫ g : Fin N → ℝ,
          truncatedGaussianAverage 1 N g ^ (-(γ * (N : ℝ)))
            ∂(gaussianVec N) ≤
      c ^ (-(γ * (N : ℝ))) *
        (Real.exp 1 / (1 - 2 * γ) *
          (2 * Real.exp γ * γ ^ (-γ)) ^ N) :=
      mul_le_mul_of_nonneg_left htruncated.2 (Real.rpow_nonneg hc.le _)
    _ = Real.exp 1 / (1 - 2 * γ) *
        (c ^ (-γ) * (2 * Real.exp γ * γ ^ (-γ))) ^ N := by
      rw [show -(γ * (N : ℝ)) = (-γ) * (N : ℝ) by ring,
        Real.rpow_mul_natCast hc.le (-γ) N, mul_pow]
      ring

/-- Paper-facing negative-moment bound away from zero: the fixed prefactor and
the truncated-moment scale are absorbed into one exponential rate. -/
theorem exists_forall_integrable_neg_rpow_Fmap_and_integral_le_exp
    {A R₀ γ : ℝ} (hA : 1 < A) (hR₀ : R₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hγ : γ ∈ Set.Ioo 0 (1 / 2 : ℝ)) :
    ∃ b : ℝ,
      ∀ N : ℕ, 0 < N → ∀ q ∈ Set.Icc R₀ 1,
        Integrable
            (fun g : Fin N → ℝ =>
              Fmap A N q g ^ (-(γ * (N : ℝ))))
            (gaussianVec N) ∧
          (∫ g : Fin N → ℝ,
              Fmap A N q g ^ (-(γ * (N : ℝ)))
                ∂(gaussianVec N)) ≤
            Real.exp (b * (N : ℝ)) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_pos_forall_integrable_neg_rpow_Fmap_and_integral_le hA hR₀ hγ
  let C : ℝ := Real.exp 1 / (1 - 2 * γ)
  let B : ℝ := c ^ (-γ) * (2 * Real.exp γ * γ ^ (-γ))
  let b : ℝ := Real.log (C * B)
  have hden : 0 < 1 - 2 * γ := by
    linarith [hγ.2]
  have hCpos : 0 < C := by
    dsimp only [C]
    exact div_pos (Real.exp_pos 1) hden
  have hCone : 1 ≤ C := by
    dsimp only [C]
    apply (le_div_iff₀ hden).2
    have hexp : 1 < Real.exp 1 :=
      Real.one_lt_exp_iff.mpr zero_lt_one
    linarith [hγ.1]
  have hBpos : 0 < B := by
    dsimp only [B]
    exact mul_pos
      (Real.rpow_pos_of_pos hc _)
      (mul_pos
        (mul_pos (by norm_num) (Real.exp_pos γ))
        (Real.rpow_pos_of_pos hγ.1 _))
  refine ⟨b, ?_⟩
  intro N hN q hq
  have hfixed := hbound N hN q hq
  refine ⟨hfixed.1, hfixed.2.trans ?_⟩
  have hCpow : C ≤ C ^ N := by
    simpa only [pow_one] using
      pow_le_pow_right₀ hCone (Nat.one_le_iff_ne_zero.mpr hN.ne')
  calc
    Real.exp 1 / (1 - 2 * γ) *
        (c ^ (-γ) * (2 * Real.exp γ * γ ^ (-γ))) ^ N =
      C * B ^ N := by rfl
    _ ≤ C ^ N * B ^ N :=
      mul_le_mul_of_nonneg_right hCpow (pow_nonneg hBpos.le N)
    _ = (C * B) ^ N := (mul_pow C B N).symm
    _ = (Real.exp (Real.log (C * B))) ^ N := by
      rw [Real.exp_log (mul_pos hCpos hBpos)]
    _ = Real.exp ((N : ℝ) * Real.log (C * B)) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (b * (N : ℝ)) := by
      congr 1
      dsimp only [b]
      ring

/-- At a positive input radius, a moment of the radial update factors into
the matching input-radius power and update-ratio moment. -/
lemma integrable_rpow_Fmap_and_integral_eq_mul
    {A q p : ℝ} {N : ℕ} (hq : 0 < q)
    (hint :
      Integrable
        (fun g : Fin N → ℝ => (Fmap A N q g / q) ^ p)
        (gaussianVec N)) :
    Integrable
        (fun g : Fin N → ℝ => Fmap A N q g ^ p)
        (gaussianVec N) ∧
      (∫ g : Fin N → ℝ, Fmap A N q g ^ p ∂(gaussianVec N)) =
        q ^ p *
          ∫ g : Fin N → ℝ,
            (Fmap A N q g / q) ^ p ∂(gaussianVec N) := by
  have hfactor (g : Fin N → ℝ) :
      Fmap A N q g ^ p =
        q ^ p * (Fmap A N q g / q) ^ p := by
    have hF :
        Fmap A N q g = q * (Fmap A N q g / q) := by
      field_simp
    calc
      Fmap A N q g ^ p =
          (q * (Fmap A N q g / q)) ^ p :=
        congrArg (fun x : ℝ => x ^ p) hF
      _ = q ^ p * (Fmap A N q g / q) ^ p :=
        Real.mul_rpow hq.le
          (div_nonneg (Fmap_nonneg A N q g) hq.le)
  have hfun :
      (fun g : Fin N → ℝ => Fmap A N q g ^ p) =
        fun g => q ^ p * (Fmap A N q g / q) ^ p := by
    funext g
    exact hfactor g
  constructor
  · rw [hfun]
    exact hint.const_mul _
  · rw [hfun, integral_const_mul]

/-- The near-zero contraction and away-from-zero moment bound combine into
the paper's one-step Foster inequality for `V_N(q) = q^(-γN)`. -/
theorem exists_eventually_integrable_neg_rpow_Fmap_foster
    {A qStar R : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hR : R ∈ Set.Ioo (0 : ℝ) qStar) :
    ∃ R₀ γ κ b : ℝ, ∃ N₀ : ℕ,
      R₀ ∈ Set.Ioc 0 1 ∧ R₀ < qStar - R ∧
        γ ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧ 0 < κ ∧
          ∀ N : ℕ, N₀ ≤ N → 0 < N →
            ∀ q ∈ Set.Ioc (0 : ℝ) 1,
              Integrable
                  (fun g : Fin N → ℝ =>
                    Fmap A N q g ^ (-(γ * (N : ℝ))))
                  (gaussianVec N) ∧
                (∫ g : Fin N → ℝ,
                    Fmap A N q g ^ (-(γ * (N : ℝ)))
                      ∂(gaussianVec N)) ≤
                  Real.exp (-(κ * (N : ℝ))) *
                      q ^ (-(γ * (N : ℝ))) +
                    Real.exp (b * (N : ℝ)) := by
  obtain ⟨R₀, γ, κ, N₀, hR₀, hR₀cap, hγ, hκ, hnear⟩ :=
    exists_radius_below_stableInterval_eventually_integrable_neg_rpow_Fmap_div
      hA hqStar hR
  have hR₀lt : R₀ < 1 := by
    have hcap : qStar - R < 1 := by
      linarith [hqStar.2, hR.1]
    exact hR₀cap.trans hcap
  obtain ⟨b, houtside⟩ :=
    exists_forall_integrable_neg_rpow_Fmap_and_integral_le_exp
      hA ⟨hR₀.1, hR₀lt⟩ hγ
  refine ⟨R₀, γ, κ, b, N₀, hR₀, hR₀cap, hγ, hκ, ?_⟩
  intro N hN₀ hN q hq
  by_cases hqsmall : q ≤ R₀
  · have hratio := hnear N hN₀ hN q hq.1 hqsmall
    have hfactor :=
      integrable_rpow_Fmap_and_integral_eq_mul hq.1 hratio.1
    refine ⟨hfactor.1, ?_⟩
    rw [hfactor.2]
    calc
      q ^ (-(γ * (N : ℝ))) *
          ∫ g : Fin N → ℝ,
            (Fmap A N q g / q) ^ (-(γ * (N : ℝ)))
              ∂(gaussianVec N) ≤
        q ^ (-(γ * (N : ℝ))) *
          Real.exp (-(κ * (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio.2 (Real.rpow_nonneg hq.1.le _)
      _ = Real.exp (-(κ * (N : ℝ))) *
          q ^ (-(γ * (N : ℝ))) := mul_comm _ _
      _ ≤ Real.exp (-(κ * (N : ℝ))) *
              q ^ (-(γ * (N : ℝ))) +
            Real.exp (b * (N : ℝ)) :=
        le_add_of_nonneg_right (Real.exp_nonneg _)
  · have hqR₀ : R₀ ≤ q := (lt_of_not_ge hqsmall).le
    have hout := houtside N hN q ⟨hqR₀, hq.2⟩
    refine ⟨hout.1, hout.2.trans ?_⟩
    exact le_add_of_nonneg_left
      (mul_nonneg (Real.exp_nonneg _)
        (Real.rpow_nonneg hq.1.le _))

/-- Kernel-facing form of the one-step negative-moment Foster inequality. -/
theorem exists_eventually_integrable_neg_rpow_Kchain_foster
    {A qStar R : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hR : R ∈ Set.Ioo (0 : ℝ) qStar) :
    ∃ R₀ γ κ b : ℝ, ∃ N₀ : ℕ,
      R₀ ∈ Set.Ioc 0 1 ∧ R₀ < qStar - R ∧
        γ ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧ 0 < κ ∧
          ∀ N : ℕ, N₀ ≤ N → 0 < N →
            ∀ q ∈ Set.Ioc (0 : ℝ) 1,
              Integrable
                  (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
                  (Kchain A N q) ∧
                (∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
                    ∂(Kchain A N q)) ≤
                  Real.exp (-(κ * (N : ℝ))) *
                      q ^ (-(γ * (N : ℝ))) +
                    Real.exp (b * (N : ℝ)) := by
  obtain ⟨R₀, γ, κ, b, N₀, hR₀, hR₀cap, hγ, hκ, hfoster⟩ :=
    exists_eventually_integrable_neg_rpow_Fmap_foster hA hqStar hR
  refine ⟨R₀, γ, κ, b, N₀, hR₀, hR₀cap, hγ, hκ, ?_⟩
  intro N hN₀ hN q hq
  have hgauss := hfoster N hN₀ hN q hq
  have hkernel :
      Integrable
        (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
        (Kchain A N q) := by
    rw [Kchain_apply]
    exact
      (integrable_map_measure
        (by fun_prop :
          AEStronglyMeasurable
            (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
            ((gaussianVec N).map (Fmap A N q)))
        (continuous_Fmap_right A N q).aemeasurable).2 hgauss.1
  refine ⟨hkernel, ?_⟩
  rw [integral_Kchain A N q
    (by fun_prop :
      Measurable (fun y : ℝ => y ^ (-(γ * (N : ℝ)))))]
  exact hgauss.2

/-- For a fixed eligible dimension, the one-step negative-moment Foster
estimate propagates integrability of `V_N(y) = y^(-γN)` through every kernel
power. -/
lemma integrable_neg_rpow_Kchain_pow_of_foster
    {A γ κ b : ℝ} {N : ℕ} (hN : 0 < N) (hγ : 0 < γ)
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hfoster :
      ∀ x ∈ Set.Ioc (0 : ℝ) 1,
        Integrable
            (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
            (Kchain A N x) ∧
          (∫ y : ℝ, y ^ (-(γ * (N : ℝ))) ∂(Kchain A N x)) ≤
            Real.exp (-(κ * (N : ℝ))) *
                x ^ (-(γ * (N : ℝ))) +
              Real.exp (b * (N : ℝ))) :
    ∀ t : ℕ,
      Integrable
        (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
        (((Kchain A N) ^ t) q) := by
  let V := fun y : ℝ => y ^ (-(γ * (N : ℝ)))
  let a := Real.exp (-(κ * (N : ℝ)))
  let B := Real.exp (b * (N : ℝ))
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2⟩
  have hsupport (t : ℕ) :
      ∀ᵐ x ∂((Kchain A N) ^ t) q, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact Kchain_pow_apply_Icc_compl A hN hqIcc t
  have hstep_integrable (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      Integrable V (Kchain A N x) := by
    by_cases hx0 : x = 0
    · subst x
      rw [Kchain_zero]
      exact integrable_dirac (by simp [V])
    · exact (hfoster x
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩).1
  have hfoster_Icc (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      ∫ y, V y ∂Kchain A N x ≤ a * V x + B := by
    by_cases hx0 : x = 0
    · subst x
      have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
      have hexp : -(γ * (N : ℝ)) ≠ 0 :=
        neg_ne_zero.mpr (mul_ne_zero hγ.ne' hNreal.ne')
      simpa [V, a, B, Kchain_zero, Real.zero_rpow hexp] using
        Real.exp_nonneg (b * (N : ℝ))
    · exact (hfoster x
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩).2
  have hnorm_action (x : ℝ) :
      (∫ y, ‖V y‖ ∂Kchain A N x) =
        ∫ y, V y ∂Kchain A N x := by
    rw [integral_Kchain A N x
      (by fun_prop : Measurable (fun y : ℝ => ‖V y‖)),
      integral_Kchain A N x
        (by fun_prop : Measurable V)]
    apply integral_congr_ae
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact Real.rpow_nonneg (Fmap_nonneg A N x g) _
  intro t
  induction t with
  | zero =>
      rw [pow_zero]
      change Integrable V (Measure.dirac q)
      exact integrable_dirac (by simp [V])
  | succ t iht =>
      rw [pow_succ']
      change Integrable V
        (((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) q)
      refine (ProbabilityTheory.integrable_comp_iff
        (by fun_prop : AEStronglyMeasurable V
          (((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) q))).2 ⟨?_, ?_⟩
      · filter_upwards [hsupport t] with x hx
        exact hstep_integrable x hx
      · have hmajor :
            Integrable (fun x => a * V x + B)
              (((Kchain A N) ^ t) q) :=
          (iht.const_mul a).add (integrable_const B)
        have haction_meas :
            AEStronglyMeasurable
              (fun x => ∫ y, ‖V y‖ ∂Kchain A N x)
              (((Kchain A N) ^ t) q) :=
          ((by fun_prop :
            StronglyMeasurable (fun y : ℝ => ‖V y‖)).integral_kernel :
              StronglyMeasurable
                (fun x => ∫ y, ‖V y‖ ∂Kchain A N x)).aestronglyMeasurable
        refine hmajor.mono' haction_meas ?_
        filter_upwards [hsupport t] with x hx
        have hnonneg :
            0 ≤ ∫ y, ‖V y‖ ∂Kchain A N x :=
          integral_nonneg_of_ae
            (Eventually.of_forall fun y => norm_nonneg _)
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hnorm_action x]
        exact hfoster_Icc x hx

/-- Under the fixed-dimension negative-moment Foster estimate, all kernel
powers have one uniform `V_N(y) = y^(-γN)` moment bound. -/
lemma exists_uniform_integral_neg_rpow_Kchain_pow_le_of_foster
    {A γ κ b : ℝ} {N : ℕ} (hN : 0 < N) (hγ : 0 < γ) (hκ : 0 < κ)
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hfoster :
      ∀ x ∈ Set.Ioc (0 : ℝ) 1,
        Integrable
            (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
            (Kchain A N x) ∧
          (∫ y : ℝ, y ^ (-(γ * (N : ℝ))) ∂(Kchain A N x)) ≤
            Real.exp (-(κ * (N : ℝ))) *
                x ^ (-(γ * (N : ℝ))) +
              Real.exp (b * (N : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      C = max (q ^ (-(γ * (N : ℝ))))
        (Real.exp (b * (N : ℝ)) /
          (1 - Real.exp (-(κ * (N : ℝ))))) ∧
        ∀ t : ℕ, Integrable
          (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
          (((Kchain A N) ^ t) q) ∧
        (∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
            ∂((Kchain A N) ^ t) q) ≤ C := by
  let V := fun y : ℝ => y ^ (-(γ * (N : ℝ)))
  let a := Real.exp (-(κ * (N : ℝ)))
  let B := Real.exp (b * (N : ℝ))
  let m := fun t : ℕ => ∫ y, V y ∂((Kchain A N) ^ t) q
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have ha0 : 0 ≤ a := Real.exp_nonneg _
  have ha1 : a < 1 := by
    dsimp only [a]
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hκ hNreal)
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2⟩
  have hsupport (t : ℕ) :
      ∀ᵐ x ∂((Kchain A N) ^ t) q, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact Kchain_pow_apply_Icc_compl A hN hqIcc t
  have hfoster_Icc (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      ∫ y, V y ∂Kchain A N x ≤ a * V x + B := by
    by_cases hx0 : x = 0
    · subst x
      have hexp : -(γ * (N : ℝ)) ≠ 0 :=
        neg_ne_zero.mpr (mul_ne_zero hγ.ne' hNreal.ne')
      simpa [V, a, B, Kchain_zero, Real.zero_rpow hexp] using
        Real.exp_nonneg (b * (N : ℝ))
    · exact (hfoster x
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩).2
  have hpow_integrable :
      ∀ t : ℕ, Integrable V (((Kchain A N) ^ t) q) := by
    exact integrable_neg_rpow_Kchain_pow_of_foster hN hγ hq hfoster
  have hrec (t : ℕ) : m (t + 1) ≤ a * m t + B := by
    have hsucc : Integrable V
        (((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) q) := by
      have hsucc' := hpow_integrable (t + 1)
      rw [pow_succ'] at hsucc'
      change Integrable V
        (((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) q) at hsucc'
      exact hsucc'
    have haction :
        Integrable (fun x => ∫ y, V y ∂Kchain A N x)
          (((Kchain A N) ^ t) q) :=
      hsucc.integral_comp
    have hmajor :
        Integrable (fun x => a * V x + B)
          (((Kchain A N) ^ t) q) :=
      ((hpow_integrable t).const_mul a).add (integrable_const B)
    have hmono :
        (∫ x, (∫ y, V y ∂Kchain A N x)
            ∂((Kchain A N) ^ t) q) ≤
          ∫ x, (a * V x + B) ∂((Kchain A N) ^ t) q :=
      integral_mono_ae haction hmajor <| by
        filter_upwards [hsupport t] with x hx
        exact hfoster_Icc x hx
    calc
      m (t + 1) =
          ∫ x, (∫ y, V y ∂Kchain A N x)
            ∂((Kchain A N) ^ t) q := by
        dsimp [m]
        rw [pow_succ']
        exact Kernel.integral_comp hsucc
      _ ≤ ∫ x, (a * V x + B) ∂((Kchain A N) ^ t) q := hmono
      _ = a * m t + B := by
        rw [integral_add ((hpow_integrable t).const_mul a)
          (integrable_const B), integral_const_mul]
        simp [m]
  have hm0_eq : m 0 = q ^ (-(γ * (N : ℝ))) := by
    dsimp [m]
    rw [pow_zero]
    change (∫ y, V y ∂Measure.dirac q) = _
    rw [integral_dirac]
  let C :=
    max (q ^ (-(γ * (N : ℝ))))
      (Real.exp (b * (N : ℝ)) /
        (1 - Real.exp (-(κ * (N : ℝ)))))
  have hqmoment : 0 ≤ q ^ (-(γ * (N : ℝ))) :=
    Real.rpow_nonneg hq.1.le _
  have hC : 0 ≤ C := hqmoment.trans (le_max_left _ _)
  refine ⟨C, hC, rfl, fun t => ⟨hpow_integrable t, ?_⟩⟩
  simpa only [C, B, a, hm0_eq] using
    geom_recursion_bound_contraction ha0 ha1 hrec t

/-- The uniform fixed-dimension negative-moment bound passes from kernel powers
to every positive-length Cesàro law. -/
lemma exists_uniform_integral_neg_rpow_cesaroMeasure_le_of_foster
    {A γ κ b : ℝ} {N : ℕ} (hN : 0 < N) (hγ : 0 < γ) (hκ : 0 < κ)
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hfoster :
      ∀ x ∈ Set.Ioc (0 : ℝ) 1,
        Integrable
            (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
            (Kchain A N x) ∧
          (∫ y : ℝ, y ^ (-(γ * (N : ℝ))) ∂(Kchain A N x)) ≤
            Real.exp (-(κ * (N : ℝ))) *
                x ^ (-(γ * (N : ℝ))) +
              Real.exp (b * (N : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      C = max (q ^ (-(γ * (N : ℝ))))
        (Real.exp (b * (N : ℝ)) /
          (1 - Real.exp (-(κ * (N : ℝ))))) ∧
        ∀ T : ℕ, 0 < T → Integrable
          (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
          (cesaroMeasure (Kchain A N) q T) ∧
        (∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
            ∂cesaroMeasure (Kchain A N) q T) ≤ C := by
  obtain ⟨C, hC, hCeq, hpow⟩ :=
    exists_uniform_integral_neg_rpow_Kchain_pow_le_of_foster
      hN hγ hκ hq hfoster
  refine ⟨C, hC, hCeq, ?_⟩
  intro T hT
  have hsum :
      Integrable
        (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
        (∑ t ∈ Finset.range T, ((Kchain A N) ^ t) q) := by
    exact integrable_finsetSum_measure.2 fun t _ => (hpow t).1
  have hcesaro :
      Integrable
        (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
        (cesaroMeasure (Kchain A N) q T) := by
    unfold cesaroMeasure
    exact hsum.smul_measure (by
      exact ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hT.ne'))
  refine ⟨hcesaro, ?_⟩
  have hsum_le :
      (∑ t ∈ Finset.range T,
          ∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
            ∂((Kchain A N) ^ t) q) ≤
        ∑ _t ∈ Finset.range T, C := by
    exact Finset.sum_le_sum fun t _ => (hpow t).2
  calc
    (∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
        ∂cesaroMeasure (Kchain A N) q T) =
        ((T : ENNReal)⁻¹).toReal *
          ∑ t ∈ Finset.range T,
            ∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
              ∂((Kchain A N) ^ t) q := by
      unfold cesaroMeasure
      rw [integral_smul_measure, smul_eq_mul,
        integral_finsetSum_measure (fun t _ => (hpow t).1)]
    _ ≤ ((T : ENNReal)⁻¹).toReal *
        ∑ _t ∈ Finset.range T, C :=
      mul_le_mul_of_nonneg_left hsum_le ENNReal.toReal_nonneg
    _ = C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.toReal_inv]
      norm_cast
      field_simp

/-- Paper-facing eventual-in-dimension package of the uniform kernel-power and
Cesàro negative-moment bounds. -/
theorem exists_eventually_uniform_integral_neg_rpow_Kchain_pow_and_cesaroMeasure_le
    {A qStar R : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hR : R ∈ Set.Ioo (0 : ℝ) qStar) :
    ∃ R₀ γ κ b : ℝ, ∃ N₀ : ℕ,
      R₀ ∈ Set.Ioc 0 1 ∧ R₀ < qStar - R ∧
        γ ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧ 0 < κ ∧
          ∀ N : ℕ, N₀ ≤ N → 0 < N →
            ∀ q ∈ Set.Ioc (0 : ℝ) 1,
              (∃ C : ℝ, 0 ≤ C ∧
                C = max (q ^ (-(γ * (N : ℝ))))
                  (Real.exp (b * (N : ℝ)) /
                    (1 - Real.exp (-(κ * (N : ℝ))))) ∧
                  ∀ t : ℕ, Integrable
                    (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
                    (((Kchain A N) ^ t) q) ∧
                  (∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
                      ∂((Kchain A N) ^ t) q) ≤ C) ∧
              ∃ C : ℝ, 0 ≤ C ∧
                C = max (q ^ (-(γ * (N : ℝ))))
                  (Real.exp (b * (N : ℝ)) /
                    (1 - Real.exp (-(κ * (N : ℝ))))) ∧
                  ∀ T : ℕ, 0 < T → Integrable
                    (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
                    (cesaroMeasure (Kchain A N) q T) ∧
                  (∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
                      ∂cesaroMeasure (Kchain A N) q T) ≤ C := by
  obtain ⟨R₀, γ, κ, b, N₀, hR₀, hR₀cap, hγ, hκ, hfoster⟩ :=
    exists_eventually_integrable_neg_rpow_Kchain_foster hA hqStar hR
  refine ⟨R₀, γ, κ, b, N₀, hR₀, hR₀cap, hγ, hκ, ?_⟩
  intro N hN₀ hN q hq
  have hfixed := hfoster N hN₀ hN
  exact
    ⟨exists_uniform_integral_neg_rpow_Kchain_pow_le_of_foster
        hN hγ.1 hκ hq hfixed,
      exists_uniform_integral_neg_rpow_cesaroMeasure_le_of_foster
        hN hγ.1 hκ hq hfixed⟩

/-- A bounded continuous cap of the negative `p`-moment. The floor
`(k+1)⁻¹` keeps the base uniformly positive while tending to zero. -/
noncomputable def negativeMomentTruncation
    (p : ℝ) (hp : 0 ≤ p) (k : ℕ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q : ℝ => (max |q| (k + 1 : ℝ)⁻¹) ^ (-p))
    ((continuous_abs.max continuous_const).rpow_const fun q =>
      Or.inl <| ne_of_gt <|
        lt_of_lt_of_le (by positivity : 0 < (k + 1 : ℝ)⁻¹)
          (le_max_right |q| (k + 1 : ℝ)⁻¹))
    ((k + 1 : ℝ)⁻¹ ^ (-p))
    (fun q => by
      have heps : 0 < (k + 1 : ℝ)⁻¹ := by positivity
      have hbase : (k + 1 : ℝ)⁻¹ ≤ max |q| (k + 1 : ℝ)⁻¹ :=
        le_max_right _ _
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (le_trans heps.le hbase) _),
        Real.rpow_neg (le_trans heps.le hbase),
        Real.rpow_neg heps.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos heps p)
        (Real.rpow_le_rpow heps.le hbase hp))

@[simp]
lemma negativeMomentTruncation_apply
    (p : ℝ) (hp : 0 ≤ p) (k : ℕ) (q : ℝ) :
    negativeMomentTruncation p hp k q =
      (max |q| (k + 1 : ℝ)⁻¹) ^ (-p) :=
  rfl

lemma negativeMomentTruncation_nonneg
    (p : ℝ) (hp : 0 ≤ p) (k : ℕ) (q : ℝ) :
    0 ≤ negativeMomentTruncation p hp k q := by
  rw [negativeMomentTruncation_apply]
  exact Real.rpow_nonneg
    ((abs_nonneg q).trans (le_max_left |q| (k + 1 : ℝ)⁻¹)) _

/-- On the positive half-line, the capped moment stays below the true negative
moment. -/
lemma negativeMomentTruncation_le
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (k : ℕ) :
    negativeMomentTruncation p hp k q ≤ q ^ (-p) := by
  have heps : 0 < (k + 1 : ℝ)⁻¹ := by positivity
  have hbase : q ≤ max |q| (k + 1 : ℝ)⁻¹ := by
    rw [abs_of_pos hq]
    exact le_max_left _ _
  have hbasepos : 0 < max |q| (k + 1 : ℝ)⁻¹ :=
    heps.trans_le (le_max_right _ _)
  rw [negativeMomentTruncation_apply,
    Real.rpow_neg hbasepos.le, Real.rpow_neg hq.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hq p)
    (Real.rpow_le_rpow hq.le hbase hp)

/-- The negative-moment caps increase with their truncation level. -/
lemma negativeMomentTruncation_mono
    {p : ℝ} (hp : 0 ≤ p) {k l : ℕ} (hkl : k ≤ l) (q : ℝ) :
    negativeMomentTruncation p hp k q ≤
      negativeMomentTruncation p hp l q := by
  have hkpos : 0 < (k + 1 : ℝ) := by positivity
  have heps :
      (l + 1 : ℝ)⁻¹ ≤ (k + 1 : ℝ)⁻¹ := by
    exact inv_anti₀ hkpos (by exact_mod_cast Nat.add_le_add_right hkl 1)
  have hlbase : 0 < max |q| (l + 1 : ℝ)⁻¹ :=
    (by positivity : 0 < (l + 1 : ℝ)⁻¹) |>.trans_le (le_max_right _ _)
  have hbase :
      max |q| (l + 1 : ℝ)⁻¹ ≤ max |q| (k + 1 : ℝ)⁻¹ :=
    max_le_max le_rfl heps
  rw [negativeMomentTruncation_apply, negativeMomentTruncation_apply,
    Real.rpow_neg (hlbase.le.trans hbase),
    Real.rpow_neg hlbase.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hlbase p)
    (Real.rpow_le_rpow hlbase.le hbase hp)

/-- At each positive radius, the bounded continuous caps converge to the true
negative moment. -/
lemma tendsto_negativeMomentTruncation
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Tendsto (fun k : ℕ => negativeMomentTruncation p hp k q)
      atTop (𝓝 (q ^ (-p))) := by
  have heps :
      Tendsto (fun k : ℕ => (k + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbase :
      Tendsto (fun k : ℕ => max |q| (k + 1 : ℝ)⁻¹)
        atTop (𝓝 q) := by
    simpa [abs_of_pos hq, max_eq_left hq.le] using
      (tendsto_const_nhds (x := |q|)).max heps
  simpa only [negativeMomentTruncation_apply] using
    hbase.rpow_const (Or.inl hq.ne')

end AbsorptionCutoff
