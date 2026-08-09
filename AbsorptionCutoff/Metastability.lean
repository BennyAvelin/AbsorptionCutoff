/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.RoundedVectorReduction
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Probability.Moments.SubGaussian

/-!
# Fixed-precision metastability

This file formalizes the one-dimensional profile used to study metastability
for the rounded dynamics.
-/

open Filter MeasureTheory ProbabilityTheory Topology

namespace AbsorptionCutoff

/-- The fixed-precision Gaussian profile from `eq:metastable-rounded-profile`. -/
noncomputable def roundedProfile (ρ α : ℝ) : ℝ :=
  ∫ g, ((Q₁ (ρ⁻¹ * Real.tanh (ρ * α * g)) : ℝ)) ^ 2 ∂gaussianReal 0 1

/-- The rounded mean map is the fixed-precision profile evaluated at
`A * sqrt h`. -/
lemma roundedMeanMap_eq_roundedProfile (A ρ h : ℝ) :
    roundedMeanMap A ρ h = roundedProfile ρ (A * Real.sqrt h) := by
  simp only [roundedMeanMap, roundedProfile]
  apply integral_congr_ae
  filter_upwards with g
  congr 3
  ring_nf

/-- The maximal squared rounded coordinate on `[-ρ⁻¹, ρ⁻¹]`
(paper `eq:metastable-radius-bound`). -/
noncomputable def roundedRadiusBound (ρ : ℝ) : ℝ :=
  (Q₁ ρ⁻¹ : ℝ) ^ 2

/-- The rounded radius bound is nonnegative. -/
lemma roundedRadiusBound_nonneg (ρ : ℝ) : 0 ≤ roundedRadiusBound ρ := by
  unfold roundedRadiusBound
  positivity

/-- The rounded radius bound is strictly positive in the fixed-precision
regime. -/
lemma roundedRadiusBound_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 < roundedRadiusBound ρ := by
  have hinv : 1 < ρ⁻¹ := (one_lt_inv₀ hρ).mpr hρ_lt
  have hQ : Q₁ ρ⁻¹ ≠ 0 := by
    intro hzero
    have hhalf := (Q₁_zero_iff ρ⁻¹).mp hzero
    rw [abs_of_pos (inv_pos.mpr hρ)] at hhalf
    linarith
  have hcast : (Q₁ ρ⁻¹ : ℝ) ≠ 0 := by exact_mod_cast hQ
  exact sq_pos_of_ne_zero hcast

/-- Every nondegenerate symmetric interval has positive standard-Gaussian
mass. -/
lemma gaussianReal_Icc_neg_pos {t : ℝ} (ht : 0 < t) :
    0 < (gaussianReal 0 1).real (Set.Icc (-t) t) := by
  have hne : gaussianReal 0 1 (Set.Icc (-t) t) ≠ 0 := by
    intro hzero
    have hvol :
        volume (Set.Icc (-t) t) = 0 :=
      gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num) hzero
    rw [Real.volume_Icc] at hvol
    have hpos : 0 < ENNReal.ofReal (t - -t) :=
      ENNReal.ofReal_pos.mpr (by linarith)
    exact hpos.ne' hvol
  rw [measureReal_def]
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

/-- The closed-form radius bound dominates every squared rounded coordinate in
the interval used in the paper's definition of `M_ρ`. -/
lemma Q₁_sq_le_roundedRadiusBound {ρ u : ℝ} (hρ : 0 < ρ)
    (hu : |u| ≤ ρ⁻¹) :
    (Q₁ u : ℝ) ^ 2 ≤ roundedRadiusBound ρ := by
  have hinv : |ρ⁻¹| = ρ⁻¹ := abs_of_pos (inv_pos.mpr hρ)
  have hQ : |(Q₁ u : ℝ)| ≤ |(Q₁ ρ⁻¹ : ℝ)| :=
    abs_Q₁_mono (hu.trans_eq hinv.symm)
  rw [roundedRadiusBound, ← sq_abs (Q₁ u : ℝ), ← sq_abs (Q₁ ρ⁻¹ : ℝ)]
  exact pow_le_pow_left₀ (abs_nonneg _) hQ 2

/-- Every coordinate produced by the rounded `tanh` dynamics is bounded by
`M_ρ`. -/
lemma Q₁_inv_tanh_sq_le_roundedRadiusBound {ρ x : ℝ} (hρ : 0 < ρ) :
    (Q₁ (ρ⁻¹ * Real.tanh (ρ * x)) : ℝ) ^ 2 ≤ roundedRadiusBound ρ := by
  apply Q₁_sq_le_roundedRadiusBound hρ
  rw [abs_mul, abs_inv, abs_of_pos hρ]
  exact mul_le_of_le_one_right (inv_nonneg.mpr hρ.le) (Real.abs_tanh_lt_one _).le

/-- Every rounded coordinate observable is bounded by the paper's exact
radius bound. -/
lemma roundedCoordinateObservable_le_roundedRadiusBound
    {A ρ h g : ℝ} (hρ : 0 < ρ) :
    roundedCoordinateObservable A ρ h g ≤ roundedRadiusBound ρ := by
  simpa only [roundedCoordinateObservable, mul_assoc] using
    (Q₁_inv_tanh_sq_le_roundedRadiusBound
      (x := A * Real.sqrt h * g) hρ)

/-- Every realization of the rounded radius step is bounded by the paper's
exact radius bound. -/
lemma Hmap_le_roundedRadiusBound
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N)
    (g : Fin N → ℝ) :
    Hmap A ρ N h g ≤ roundedRadiusBound ρ := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Hmap_eq_average_roundedCoordinateObservable]
  calc
    (N : ℝ)⁻¹ *
        ∑ i, roundedCoordinateObservable A ρ h (g i) ≤
      (N : ℝ)⁻¹ * ∑ _i : Fin N, roundedRadiusBound ρ := by
        gcongr with i
        exact roundedCoordinateObservable_le_roundedRadiusBound hρ
    _ = roundedRadiusBound ρ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [hNreal.ne']

/-- Every Gaussian-vector coordinate observable has mean equal to the rounded
mean map. -/
lemma integral_gaussianVec_roundedCoordinateObservable_eval_eq_roundedMeanMap
    (A ρ h : ℝ) {N : ℕ} (i : Fin N) :
    ∫ g, roundedCoordinateObservable A ρ h (g i) ∂(gaussianVec N) =
      roundedMeanMap A ρ h := by
  have hpm :
      (gaussianVec N).map (Function.eval i) = gaussianReal 0 1 := by
    unfold gaussianVec
    rw [Measure.pi_map_eval]
    simp
  have hf :
      AEStronglyMeasurable (roundedCoordinateObservable A ρ h)
        ((gaussianVec N).map (Function.eval i)) :=
    (measurable_roundedCoordinateObservable A ρ h).aestronglyMeasurable
  have hφ :
      AEMeasurable (Function.eval i) (gaussianVec N) :=
    (measurable_pi_apply i).aemeasurable
  have hmap := integral_map hφ hf
  rw [hpm] at hmap
  exact hmap.symm.trans (integral_roundedCoordinateObservable A ρ h)

/-- Each centered rounded coordinate observable is sub-Gaussian with the
exact parameter supplied by its range `[0, M_ρ]`. -/
lemma hasSubgaussianMGF_roundedCoordinateObservable_eval_sub_mean
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) (i : Fin N) :
    HasSubgaussianMGF
      (fun g : Fin N → ℝ =>
        roundedCoordinateObservable A ρ h (g i) -
          roundedMeanMap A ρ h)
      ((‖roundedRadiusBound ρ‖₊ / 2) ^ 2) (gaussianVec N) := by
  let X : (Fin N → ℝ) → ℝ :=
    fun g => roundedCoordinateObservable A ρ h (g i)
  have hXMeas : AEMeasurable X (gaussianVec N) :=
    ((measurable_roundedCoordinateObservable A ρ h).comp
      (measurable_pi_apply i)).aemeasurable
  have hXBounds :
      ∀ᵐ g ∂(gaussianVec N),
        X g ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
    filter_upwards with g
    exact ⟨roundedCoordinateObservable_nonneg A ρ h (g i),
      roundedCoordinateObservable_le_roundedRadiusBound hρ⟩
  have hsubG :=
    hasSubgaussianMGF_of_mem_Icc hXMeas hXBounds
  rw [show ∫ g, X g ∂(gaussianVec N) = roundedMeanMap A ρ h by
    exact
      integral_gaussianVec_roundedCoordinateObservable_eval_eq_roundedMeanMap
        A ρ h i] at hsubG
  simpa only [X, sub_zero] using hsubG

/-- The centered rounded coordinate observables are mutually independent
under the product Gaussian law. -/
lemma iIndepFun_roundedCoordinateObservable_eval_sub_mean
    (A ρ h : ℝ) (N : ℕ) :
    iIndepFun
      (fun i (g : Fin N → ℝ) =>
        roundedCoordinateObservable A ρ h (g i) -
          roundedMeanMap A ρ h)
      (gaussianVec N) := by
  have hEval :
      iIndepFun (fun i (g : Fin N → ℝ) => g i) (gaussianVec N) := by
    unfold gaussianVec
    exact iIndepFun_pi fun _ => aemeasurable_id
  have hcomp := hEval.comp
    (fun _ x => roundedCoordinateObservable A ρ h x -
      roundedMeanMap A ρ h)
    (fun _ => (measurable_roundedCoordinateObservable A ρ h).sub
      measurable_const)
  change iIndepFun
    (fun i =>
      (fun x => roundedCoordinateObservable A ρ h x -
        roundedMeanMap A ρ h) ∘
      (fun g : Fin N → ℝ => g i))
    (gaussianVec N)
  exact hcomp

/-- The sum of the centered rounded coordinate observables is sub-Gaussian
with parameter equal to the sum of the coordinate parameters. -/
lemma hasSubgaussianMGF_sum_roundedCoordinateObservable_eval_sub_mean
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) :
    HasSubgaussianMGF
      (fun g : Fin N → ℝ =>
        ∑ i : Fin N,
          (roundedCoordinateObservable A ρ h (g i) -
            roundedMeanMap A ρ h))
      (∑ _i : Fin N, ((‖roundedRadiusBound ρ‖₊ / 2) ^ 2))
      (gaussianVec N) := by
  simpa using HasSubgaussianMGF.sum_of_iIndepFun
    (iIndepFun_roundedCoordinateObservable_eval_sub_mean A ρ h N)
    (s := Finset.univ)
    (fun i _ =>
      hasSubgaussianMGF_roundedCoordinateObservable_eval_sub_mean hρ i)

/-- Exact sub-Gaussian parameter obtained by averaging the `N` centered
coordinate observables. -/
noncomputable def roundedHmapSubgaussianParameter (ρ : ℝ) (N : ℕ) : NNReal :=
  NNReal.mk (((N : ℝ)⁻¹) ^ 2) (sq_nonneg ((N : ℝ)⁻¹)) *
    ∑ _i : Fin N, ((‖roundedRadiusBound ρ‖₊ / 2) ^ 2)

/-- The exact averaged-step parameter is the usual Hoeffding variance proxy
`Mρ² / (4N)`. -/
lemma coe_roundedHmapSubgaussianParameter
    {ρ : ℝ} {N : ℕ} (hN : 0 < N) :
    (roundedHmapSubgaussianParameter ρ N : ℝ) =
      roundedRadiusBound ρ ^ 2 / (4 * N) := by
  unfold roundedHmapSubgaussianParameter
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_pow,
    NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_natCast]
  rw [Real.norm_eq_abs, abs_of_nonneg (roundedRadiusBound_nonneg ρ)]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- The centered rounded radius step is the normalized centered coordinate
sum, hence is sub-Gaussian with the correspondingly scaled parameter. -/
lemma hasSubgaussianMGF_Hmap_sub_roundedMeanMap
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N) :
    HasSubgaussianMGF
      (fun g : Fin N → ℝ =>
        Hmap A ρ N h g - roundedMeanMap A ρ h)
      (roundedHmapSubgaussianParameter ρ N)
      (gaussianVec N) := by
  have hscaled :=
    (hasSubgaussianMGF_sum_roundedCoordinateObservable_eval_sub_mean
      (A := A) (h := h) (N := N) hρ).const_mul ((N : ℝ)⁻¹)
  change HasSubgaussianMGF _ (roundedHmapSubgaussianParameter ρ N) _ at hscaled
  apply hscaled.congr
  filter_upwards with g
  rw [Hmap_eq_average_roundedCoordinateObservable]
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Upper one-step deviation bound for the rounded radius average. -/
lemma measureReal_Hmap_sub_roundedMeanMap_ge_le
    {A ρ h ε : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N)
    (hε : 0 ≤ ε) :
    (gaussianVec N).real
        {g : Fin N → ℝ |
          ε ≤ Hmap A ρ N h g - roundedMeanMap A ρ h} ≤
      Real.exp
        (-ε ^ 2 / (2 * roundedHmapSubgaussianParameter ρ N)) :=
  (hasSubgaussianMGF_Hmap_sub_roundedMeanMap hρ hN).measure_ge_le hε

/-- Lower one-step deviation bound for the rounded radius average. -/
lemma measureReal_Hmap_sub_roundedMeanMap_le_neg_le
    {A ρ h ε : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N)
    (hε : 0 ≤ ε) :
    (gaussianVec N).real
        {g : Fin N → ℝ |
          Hmap A ρ N h g - roundedMeanMap A ρ h ≤ -ε} ≤
      Real.exp
        (-ε ^ 2 / (2 * roundedHmapSubgaussianParameter ρ N)) := by
  have hset :
      {g : Fin N → ℝ |
          Hmap A ρ N h g - roundedMeanMap A ρ h ≤ -ε} =
        {g : Fin N → ℝ |
          ε ≤ -(Hmap A ρ N h g - roundedMeanMap A ρ h)} := by
    ext g
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hg <;> linarith
  rw [hset]
  simpa only [Pi.neg_apply] using
    (hasSubgaussianMGF_Hmap_sub_roundedMeanMap hρ hN).neg.measure_ge_le hε

/-- Upper one-step deviation bound with the paper's simplified exponent. -/
lemma measureReal_Hmap_sub_roundedMeanMap_ge_le_exp
    {A ρ h ε : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hε : 0 ≤ ε) :
    (gaussianVec N).real
        {g : Fin N → ℝ |
          ε ≤ Hmap A ρ N h g - roundedMeanMap A ρ h} ≤
      Real.exp
        (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
  calc
    _ ≤ Real.exp
        (-ε ^ 2 / (2 * roundedHmapSubgaussianParameter ρ N)) :=
      measureReal_Hmap_sub_roundedMeanMap_ge_le hρ hN hε
    _ = _ := by
      congr 1
      rw [coe_roundedHmapSubgaussianParameter hN]
      have hMne : roundedRadiusBound ρ ≠ 0 :=
        (roundedRadiusBound_pos hρ hρ_lt).ne'
      have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      ring

/-- Lower one-step deviation bound with the paper's simplified exponent. -/
lemma measureReal_Hmap_sub_roundedMeanMap_le_neg_le_exp
    {A ρ h ε : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hε : 0 ≤ ε) :
    (gaussianVec N).real
        {g : Fin N → ℝ |
          Hmap A ρ N h g - roundedMeanMap A ρ h ≤ -ε} ≤
      Real.exp
        (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
  calc
    _ ≤ Real.exp
        (-ε ^ 2 / (2 * roundedHmapSubgaussianParameter ρ N)) :=
      measureReal_Hmap_sub_roundedMeanMap_le_neg_le hρ hN hε
    _ = _ := by
      congr 1
      rw [coe_roundedHmapSubgaussianParameter hN]
      have hMne : roundedRadiusBound ρ ≠ 0 :=
        (roundedRadiusBound_pos hρ hρ_lt).ne'
      have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
      ring

/-- Paper `eq:metastable-hoeffding`: the rounded one-step radius is
exponentially concentrated about its deterministic mean map. -/
lemma measureReal_abs_Hmap_sub_roundedMeanMap_gt_le
    {A ρ h ε : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hε : 0 < ε) :
    (gaussianVec N).real
        {g : Fin N → ℝ |
          |Hmap A ρ N h g - roundedMeanMap A ρ h| > ε} ≤
      2 * Real.exp
        (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
  let X := fun g : Fin N → ℝ =>
    Hmap A ρ N h g - roundedMeanMap A ρ h
  have hevent :
      {g : Fin N → ℝ | |X g| > ε} =
        {g : Fin N → ℝ | X g < -ε} ∪
          {g : Fin N → ℝ | ε < X g} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hg
      by_cases hx : 0 ≤ X g
      · right
        simpa [abs_of_nonneg hx] using hg
      · left
        have hxneg : X g < 0 := lt_of_not_ge hx
        rw [abs_of_neg hxneg] at hg
        linarith
    · rintro (hg | hg)
      · have hxneg : X g < 0 := hg.trans (neg_neg_of_pos hε)
        rw [abs_of_neg hxneg]
        linarith
      · have hxpos : 0 < X g := hε.trans hg
        simpa [abs_of_pos hxpos] using hg
  rw [show
    {g : Fin N → ℝ |
      |Hmap A ρ N h g - roundedMeanMap A ρ h| > ε} =
        {g : Fin N → ℝ | |X g| > ε} by rfl, hevent]
  have hlowerMono :
      (gaussianVec N).real {g : Fin N → ℝ | X g < -ε} ≤
        (gaussianVec N).real {g : Fin N → ℝ | X g ≤ -ε} := by
    apply measureReal_mono
    · intro g hg
      change X g < -ε at hg
      change X g ≤ -ε
      exact hg.le
    · exact measure_ne_top _ _
  have hupperMono :
      (gaussianVec N).real {g : Fin N → ℝ | ε < X g} ≤
        (gaussianVec N).real {g : Fin N → ℝ | ε ≤ X g} := by
    apply measureReal_mono
    · intro g hg
      change ε < X g at hg
      change ε ≤ X g
      exact hg.le
    · exact measure_ne_top _ _
  have hlower :=
    measureReal_Hmap_sub_roundedMeanMap_le_neg_le_exp
      (A := A) (h := h) hρ hρ_lt hN hε.le
  have hupper :=
    measureReal_Hmap_sub_roundedMeanMap_ge_le_exp
      (A := A) (h := h) hρ hρ_lt hN hε.le
  calc
    _ ≤ (gaussianVec N).real {g : Fin N → ℝ | X g < -ε} +
        (gaussianVec N).real {g : Fin N → ℝ | ε < X g} :=
      measureReal_union_le _ _
    _ ≤ (gaussianVec N).real {g : Fin N → ℝ | X g ≤ -ε} +
        (gaussianVec N).real {g : Fin N → ℝ | ε ≤ X g} :=
      add_le_add hlowerMono hupperMono
    _ ≤ Real.exp (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) +
        Real.exp (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) :=
      add_le_add (by simpa only [X] using hlower)
        (by simpa only [X] using hupper)
    _ = _ := by ring

/-- Kernel form of paper `eq:metastable-hoeffding`. -/
lemma Hkernel_measureReal_abs_sub_roundedMeanMap_gt_le
    {A ρ h ε : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hε : 0 < ε) :
    (Hkernel A ρ N h).real
        {y : ℝ | |y - roundedMeanMap A ρ h| > ε} ≤
      2 * Real.exp
        (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
  rw [Hkernel_apply, measureReal_def,
    Measure.map_apply (measurable_Hmap_right A ρ N h)
      (measurableSet_lt measurable_const
        (measurable_id.sub measurable_const).abs :
        MeasurableSet {y : ℝ | |y - roundedMeanMap A ρ h| > ε})]
  exact measureReal_abs_Hmap_sub_roundedMeanMap_gt_le
    hρ hρ_lt hN hε

/-- Every rounded-radius transition is supported in the paper's exact compact
state interval `[0, Mρ]`. -/
lemma Hkernel_apply_roundedRadiusBound_Icc_compl
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N) :
    Hkernel A ρ N h
        (Set.Icc 0 (roundedRadiusBound ρ))ᶜ = 0 := by
  rw [Hkernel_apply,
    Measure.map_apply (measurable_Hmap_right A ρ N h)
      measurableSet_Icc.compl]
  have hempty :
      Hmap A ρ N h ⁻¹' (Set.Icc 0 (roundedRadiusBound ρ))ᶜ = ∅ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false]
    intro hg
    exact hg ⟨Hmap_nonneg A ρ N h g,
      Hmap_le_roundedRadiusBound hρ hN g⟩
  rw [hempty, measure_empty]

/-- Every positive-time coordinate of the canonical rounded-radius path lies
in the paper's exact compact state interval almost surely. -/
lemma markovPathMeasure_ae_eval_succ_mem_roundedRadiusBound_Icc
    {A ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure μ₀ (Hkernel A ρ N)),
      ω (t + 1) ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
  have hzero : ∀ a : ℝ,
      Hkernel A ρ N a
        (Set.Icc 0 (roundedRadiusBound ρ))ᶜ = 0 :=
    fun _ => Hkernel_apply_roundedRadiusBound_Icc_compl hρ hN
  rw [ae_iff]
  have hset :
      {ω : ℕ → ℝ |
        ω (t + 1) ∉ Set.Icc 0 (roundedRadiusBound ρ)} =
      (fun ω : ℕ → ℝ => ω (t + 1)) ⁻¹'
        (Set.Icc 0 (roundedRadiusBound ρ))ᶜ := rfl
  rw [show {ω : ℕ → ℝ |
      ¬ω (t + 1) ∈ Set.Icc 0 (roundedRadiusBound ρ)} =
      {ω : ℕ → ℝ |
        ω (t + 1) ∉ Set.Icc 0 (roundedRadiusBound ρ)} by rfl,
    hset, ← Measure.map_apply (measurable_pi_apply (t + 1))
      measurableSet_Icc.compl,
    markovPathMeasure_map_eval_succ,
    Measure.bind_apply measurableSet_Icc.compl
      (Hkernel A ρ N).aemeasurable]
  simp only [hzero, lintegral_zero]

/-- A canonical rounded-radius path started in `[0, Mρ]` remains in that
exact compact interval at every fixed time almost surely. -/
lemma markovPathMeasure_dirac_ae_eval_mem_roundedRadiusBound_Icc
    {A ρ q : ℝ} {N : ℕ} (hq : q ∈ Set.Icc 0 (roundedRadiusBound ρ))
    (hρ : 0 < ρ) (hN : 0 < N) (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)),
      ω t ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
  cases t with
  | zero =>
      filter_upwards [
        markovPathMeasure_dirac_ae_eval_zero_eq
          q (Hkernel A ρ N)] with ω hω
      simpa only [hω] using hq
  | succ t =>
      exact
        markovPathMeasure_ae_eval_succ_mem_roundedRadiusBound_Icc
          hρ hN (Measure.dirac q) t

/-- Canonical-path form of paper `eq:metastable-hoeffding`: at every time,
the unconditional probability of a one-step deviation obeys the same uniform
bound as the state-dependent kernel. -/
lemma markovPathMeasure_measureReal_abs_next_sub_roundedMeanMap_gt_le
    {A ρ q ε : ℝ} {N : ℕ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hε : 0 < ε) (t : ℕ) :
    (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
        {ω : ℕ → ℝ |
          |ω (t + 1) - roundedMeanMap A ρ (ω t)| > ε} ≤
      2 * Real.exp
        (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
  let current : ((i : Finset.Iic t) → ℝ) → ℝ :=
    fun p => p ⟨t, Finset.mem_Iic.mpr le_rfl⟩
  let D : Set ((((i : Finset.Iic t) → ℝ) × ℝ)) :=
    {p | ε < |p.2 - roundedMeanMap A ρ (current p.1)|}
  let ψ : ((((i : Finset.Iic t) → ℝ) × ℝ) → ℝ) :=
    D.indicator fun _ => 1
  let E : Set (ℕ → ℝ) :=
    {ω | ε < |ω (t + 1) - roundedMeanMap A ρ (ω t)|}
  have hcurrent : Measurable current :=
    measurable_pi_apply
      (⟨t, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic t)
  have hD : MeasurableSet D := by
    apply measurableSet_lt measurable_const
    exact (measurable_snd.sub
      ((continuous_roundedMeanMap hA hρ hρ_lt).measurable.comp
        (hcurrent.comp measurable_fst))).abs
  have hψ : StronglyMeasurable ψ :=
    measurable_const.indicator hD |>.stronglyMeasurable
  have hE : MeasurableSet E := by
    apply measurableSet_lt measurable_const
    exact ((measurable_pi_apply (t + 1)).sub
      ((continuous_roundedMeanMap hA hρ hρ_lt).measurable.comp
        (measurable_pi_apply t))).abs
  have hpath :
      (fun ω : ℕ → ℝ =>
        ψ (Preorder.frestrictLe t ω, ω (t + 1))) =
        fun ω => E.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp only [ψ, D, E, current, Set.indicator_apply,
      Set.mem_setOf_eq, Preorder.frestrictLe_apply]
    rfl
  have hψint :
      Integrable (fun ω : ℕ → ℝ =>
        ψ (Preorder.frestrictLe t ω, ω (t + 1))) μ := by
    rw [hpath]
    exact (integrable_const (1 : ℝ)).indicator hE
  have hcondEq :=
    condExp_markovPathMeasure_prefix_eval_succ_piLE
      (Measure.dirac q) (Hkernel A ρ N) t hψ hψint
  have hcond :
      μ[fun ω =>
          E.indicator (fun _ => (1 : ℝ)) ω |
        Filtration.piLE t] ≤ᵐ[μ]
          fun _ =>
            2 * Real.exp
              (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
    filter_upwards [hcondEq] with ω hω
    rw [show
      (fun ω =>
        E.indicator (fun _ => (1 : ℝ)) ω) =
          (fun ω =>
            ψ (Preorder.frestrictLe t ω, ω (t + 1))) by
              exact hpath.symm, hω]
    have hstep :=
      Hkernel_measureReal_abs_sub_roundedMeanMap_gt_le
        (A := A) (h := ω t) hρ hρ_lt hN hε
    have hnext :
        (∫ y, ψ (Preorder.frestrictLe t ω, y)
            ∂(Hkernel A ρ N (ω t))) =
          (Hkernel A ρ N (ω t)).real
            {y : ℝ | |y - roundedMeanMap A ρ (ω t)| > ε} := by
      rw [show
        (fun y =>
          ψ (Preorder.frestrictLe t ω, y)) =
            {y : ℝ |
              |y - roundedMeanMap A ρ (ω t)| > ε}.indicator
                (fun _ => (1 : ℝ)) by
                  funext y
                  simp only [ψ, D, current, Set.indicator_apply,
                    Set.mem_setOf_eq, Preorder.frestrictLe_apply]
                  rfl,
        integral_indicator_const, smul_eq_mul, mul_one]
      exact measurableSet_lt measurable_const
        ((measurable_id.sub measurable_const).abs)
    rw [hnext]
    exact hstep
  have hGint :
      Integrable (fun ω =>
        E.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hE
  calc
    μ.real E =
        ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
          rw [integral_indicator_const, smul_eq_mul, mul_one]
          exact hE
    _ = ∫ ω,
          μ[fun ω =>
              E.indicator (fun _ => (1 : ℝ)) ω |
            Filtration.piLE t] ω ∂μ :=
      (integral_condExp (Filtration.piLE.le t)).symm
    _ ≤ ∫ _ω,
          2 * Real.exp
            (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) ∂μ :=
      integral_mono_ae integrable_condExp (integrable_const _) hcond
    _ = 2 * Real.exp
          (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
      rw [integral_const, probReal_univ, one_smul]

/-- The event that at least one rounded-radius transition through time `T`
deviates from its conditional mean by more than `ε`. -/
def finiteHorizonStepDeviationEvent
    (A ρ ε : ℝ) (T : ℕ) : Set (ℕ → ℝ) :=
  ⋃ s ∈ Finset.range T,
    {ω : ℕ → ℝ |
      |ω (s + 1) - roundedMeanMap A ρ (ω s)| > ε}

/-- A union bound upgrades the canonical one-step Hoeffding estimate to every
transition in a fixed finite horizon. -/
lemma markovPathMeasure_measureReal_finiteHorizonStepDeviationEvent_le
    {A ρ q ε : ℝ} {N T : ℕ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hε : 0 < ε) :
    (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
        (finiteHorizonStepDeviationEvent A ρ ε T) ≤
      2 * T * Real.exp
        (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
  let b : ℝ :=
    2 * Real.exp
      (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2)
  rw [finiteHorizonStepDeviationEvent]
  calc
    μ.real
        (⋃ s ∈ Finset.range T,
          {ω : ℕ → ℝ |
            |ω (s + 1) - roundedMeanMap A ρ (ω s)| > ε}) ≤
      ∑ s ∈ Finset.range T,
        μ.real
          {ω : ℕ → ℝ |
            |ω (s + 1) - roundedMeanMap A ρ (ω s)| > ε} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ Finset.range T, b := by
      apply Finset.sum_le_sum
      intro s _hs
      exact
        markovPathMeasure_measureReal_abs_next_sub_roundedMeanMap_gt_le
          hA hρ hρ_lt hN hε s
    _ = 2 * T * Real.exp
          (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, b]
      ring

/-- Abstract finite-horizon tracking induction used in the metastable
entrance argument. A uniformly small one-step perturbation is propagated by
any chosen modulus bound for the deterministic map. -/
lemma abs_sub_iterate_le_errorEnvelope
    (V : ℝ → ℝ) (x : ℕ → ℝ) (q δ : ℝ)
    (ω : ℝ → ℝ) (E : ℕ → ℝ) (T : ℕ)
    (hx0 : x 0 = q) (hE0 : E 0 = 0)
    (hnoise : ∀ s < T, |x (s + 1) - V (x s)| ≤ δ)
    (hmodulus : ∀ s < T,
      |x s - V^[s] q| ≤ E s →
        |V (x s) - V (V^[s] q)| ≤ ω (E s))
    (hEsucc : ∀ s < T, E (s + 1) = δ + ω (E s)) :
    ∀ s ≤ T, |x s - V^[s] q| ≤ E s := by
  intro s hsT
  induction s with
  | zero =>
      simpa only [Function.iterate_zero_apply, hx0, hE0, sub_self, abs_zero]
        using (le_rfl : (0 : ℝ) ≤ 0)
  | succ s ih =>
      have hsT : s < T := Nat.lt_of_succ_le hsT
      have ih' : |x s - V^[s] q| ≤ E s :=
        ih (Nat.le_of_lt hsT)
      calc
        |x (s + 1) - V^[s + 1] q| =
            |(x (s + 1) - V (x s)) +
              (V (x s) - V (V^[s] q))| := by
                rw [Function.iterate_succ_apply']
                congr 1
                ring
        _ ≤ |x (s + 1) - V (x s)| +
              |V (x s) - V (V^[s] q)| := abs_add_le _ _
        _ ≤ δ + ω (E s) :=
          add_le_add (hnoise s hsT) (hmodulus s hsT ih')
        _ = E (s + 1) := (hEsucc s hsT).symm

/-- Recursive deterministic error envelope from the paper's finite-horizon
entrance comparison. -/
def finiteHorizonErrorEnvelope (ω : ℝ → ℝ) (δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | s + 1 => δ + ω (finiteHorizonErrorEnvelope ω δ s)

@[simp]
lemma finiteHorizonErrorEnvelope_zero (ω : ℝ → ℝ) (δ : ℝ) :
    finiteHorizonErrorEnvelope ω δ 0 = 0 := rfl

@[simp]
lemma finiteHorizonErrorEnvelope_succ
    (ω : ℝ → ℝ) (δ : ℝ) (s : ℕ) :
    finiteHorizonErrorEnvelope ω δ (s + 1) =
      δ + ω (finiteHorizonErrorEnvelope ω δ s) := rfl

/-- At every fixed horizon, the recursive envelope vanishes with the
one-step tolerance whenever its modulus vanishes at zero. -/
lemma tendsto_finiteHorizonErrorEnvelope_zero
    {ω : ℝ → ℝ} (hω : Tendsto ω (𝓝 0) (𝓝 0)) (s : ℕ) :
    Tendsto (fun δ : ℝ => finiteHorizonErrorEnvelope ω δ s)
      (𝓝 0) (𝓝 0) := by
  induction s with
  | zero =>
      simpa only [finiteHorizonErrorEnvelope_zero] using
        (tendsto_const_nhds :
          Tendsto (fun _δ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
  | succ s ih =>
      have hid :
          Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0) :=
        tendsto_id
      simpa only [finiteHorizonErrorEnvelope_succ, Function.comp_apply,
        zero_add] using
        hid.add (hω.comp ih)

/-- The fixed-precision profile is the finite sum of Gaussian layer tails from
paper `eq:metastable-rounded-profile-layer`. -/
lemma roundedProfile_eq_sum_upperTail {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α) :
    roundedProfile ρ α =
      2 * ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        gaussianUpperTail (roundedLayerThreshold ρ k / α) := by
  simpa only [roundedMeanMap_eq_roundedProfile, Real.sqrt_one, mul_one] using
    (roundedMeanMap_eq_sum_upperTail (A := α) (ρ := ρ) (h := 1)
      hα hρ zero_lt_one)

/-- The fixed-precision profile is nonnegative. -/
lemma roundedProfile_nonneg (ρ α : ℝ) : 0 ≤ roundedProfile ρ α :=
  integral_nonneg fun g => by positivity

/-- The fixed-precision profile is strictly positive at every positive scale
when the zeroth rounding layer is admissible. -/
lemma roundedProfile_pos {ρ α : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hα : 0 < α) :
    0 < roundedProfile ρ α := by
  simpa only [roundedMeanMap_eq_roundedProfile, Real.sqrt_one, mul_one] using
    (roundedMeanMap_pos (A := α) (ρ := ρ) (h := 1)
      hα hρ hρ_lt zero_lt_one)

/-- On the nonnegative half-line, the profile is the rounded mean map after
the change of variables `h = α²`. -/
lemma roundedProfile_eq_roundedMeanMap_sq {ρ α : ℝ} (hα : 0 ≤ α) :
    roundedProfile ρ α = roundedMeanMap 1 ρ (α ^ 2) := by
  rw [roundedMeanMap_eq_roundedProfile, one_mul, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hα]

/-- The fixed-precision profile is real analytic at every positive scale. -/
@[fun_prop]
lemma analyticAt_roundedProfile {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α) :
    AnalyticAt ℝ (roundedProfile ρ) α := by
  let F : ℝ → ℝ := fun u => roundedMeanMap 1 ρ (u ^ 2)
  have hinner : AnalyticAt ℝ (fun u : ℝ => u ^ 2) α := by
    fun_prop
  have hF : AnalyticAt ℝ F α := by
    dsimp only [F]
    have houter :
        AnalyticAt ℝ (roundedMeanMap 1 ρ)
          ((fun u : ℝ => u ^ 2) α) :=
      analyticAt_roundedMeanMap zero_lt_one hρ (sq_pos_of_pos hα)
    exact AnalyticAt.fun_comp
      (f := fun u : ℝ => u ^ 2) (x := α) houter hinner
  apply hF.congr
  filter_upwards [Ioi_mem_nhds hα] with u hu
  exact (roundedProfile_eq_roundedMeanMap_sq hu.le).symm

/-- The fixed-precision profile is continuous on the positive half-line. -/
lemma continuousOn_roundedProfile_Ioi {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousOn (roundedProfile ρ) (Set.Ioi 0) := by
  have hcomp : ContinuousOn (fun α : ℝ => roundedMeanMap 1 ρ (α ^ 2))
    (Set.Ioi 0) :=
    (continuousOn_roundedMeanMap_Ioi (A := 1) (ρ := ρ) zero_lt_one hρ).comp
      (continuousOn_id.pow 2) (fun α (hα : α ∈ Set.Ioi (0 : ℝ)) => by
        change 0 < α ^ 2
        exact sq_pos_of_pos (show 0 < α from hα))
  exact hcomp.congr fun α hα => roundedProfile_eq_roundedMeanMap_sq hα.le

/-- The quotient whose positive-scale infimum is the squared fixed-precision
existence threshold. -/
noncomputable def roundedThresholdRatio (ρ α : ℝ) : ℝ :=
  α ^ 2 / roundedProfile ρ α

/-- The signed profile drift whose zeros are the paper's `α`-fixed points. -/
noncomputable def roundedProfileDrift (A ρ α : ℝ) : ℝ :=
  A ^ 2 * roundedProfile ρ α - α ^ 2

/-- The positive-drift region from paper
`eq:metastable-positive-region`. -/
noncomputable def roundedPositiveDriftSet (A ρ : ℝ) : Set ℝ :=
  {h | h ∈ Set.Ioo 0 (roundedRadiusBound ρ) ∧
    h < roundedMeanMap A ρ h}

/-- The positive-drift component containing a reference radius. -/
def roundedPositiveDriftComponent (A ρ h : ℝ) : Set ℝ :=
  connectedComponentIn (roundedPositiveDriftSet A ρ) h

/-- A positive-drift component is rightmost when every point of the
positive-drift set lies at or to the left of its upper endpoint. -/
def IsRightmostRoundedPositiveDriftComponent (A ρ h : ℝ) : Prop :=
  ∀ u ∈ roundedPositiveDriftSet A ρ,
    u ≤ sSup (roundedPositiveDriftComponent A ρ h)

/-- Upper endpoints of all positive-drift components. -/
def roundedPositiveDriftUpperEndpoints (A ρ : ℝ) : Set ℝ :=
  {u | ∃ h ∈ roundedPositiveDriftSet A ρ,
    u = sSup (roundedPositiveDriftComponent A ρ h)}

/-- The set of connected components of the positive-drift region. -/
def roundedPositiveDriftComponents (A ρ : ℝ) : Set (Set ℝ) :=
  roundedPositiveDriftComponent A ρ '' roundedPositiveDriftSet A ρ

/-- The squared fixed-precision existence threshold from paper
`eq:metastable-exact-threshold`. -/
noncomputable def roundedExistenceThresholdSq (ρ : ℝ) : ℝ :=
  sInf (roundedThresholdRatio ρ '' Set.Ioi 0)

/-- The fixed-precision existence threshold, chosen as the nonnegative square
root of its defining infimum. -/
noncomputable def roundedExistenceThreshold (ρ : ℝ) : ℝ :=
  Real.sqrt (roundedExistenceThresholdSq ρ)

/-- Every positive-scale threshold ratio is strictly positive. -/
lemma roundedThresholdRatio_pos {ρ α : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hα : 0 < α) :
    0 < roundedThresholdRatio ρ α := by
  exact div_pos (sq_pos_of_pos hα) (roundedProfile_pos hρ hρ_lt hα)

/-- The threshold ratio is continuous on the positive half-line. -/
lemma continuousOn_roundedThresholdRatio_Ioi {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ContinuousOn (roundedThresholdRatio ρ) (Set.Ioi 0) := by
  exact (continuousOn_id.pow 2).div (continuousOn_roundedProfile_Ioi hρ)
    (fun α hα => (roundedProfile_pos hρ hρ_lt hα).ne')

/-- The signed profile drift is continuous on the positive half-line. -/
lemma continuousOn_roundedProfileDrift_Ioi {A ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousOn (roundedProfileDrift A ρ) (Set.Ioi 0) := by
  exact continuousOn_const.mul (continuousOn_roundedProfile_Ioi hρ)
    |>.sub (continuousOn_id.pow 2)

/-- The fixed-precision profile is uniformly bounded by the maximal squared
rounded coordinate `M_ρ`. -/
lemma roundedProfile_le_roundedRadiusBound {ρ α : ℝ} (hρ : 0 < ρ) :
    roundedProfile ρ α ≤ roundedRadiusBound ρ := by
  rw [← show roundedMeanMap α ρ 1 = roundedProfile ρ α by
    simpa only [Real.sqrt_one, mul_one] using
      roundedMeanMap_eq_roundedProfile α ρ 1]
  rw [← integral_roundedCoordinateObservable]
  have hint : Integrable (roundedCoordinateObservable α ρ 1)
      (gaussianReal 0 1) := by
    simpa using
      (integrable_pow_roundedCoordinateObservable
        (A := α) (ρ := ρ) (h := 1) hρ 1)
  calc
    ∫ g, roundedCoordinateObservable α ρ 1 g ∂(gaussianReal 0 1) ≤
        ∫ _g : ℝ, roundedRadiusBound ρ ∂(gaussianReal 0 1) := by
      refine integral_mono hint (integrable_const _) ?_
      intro g
      simpa only [roundedCoordinateObservable, Real.sqrt_one, mul_one, mul_assoc] using
        (Q₁_inv_tanh_sq_le_roundedRadiusBound (ρ := ρ) (x := α * g) hρ)
    _ = roundedRadiusBound ρ := by simp

/-- At every positive scale, the profile is strictly below the maximal rounded
coordinate because the Gaussian zero-bin event has positive probability. -/
lemma roundedProfile_lt_roundedRadiusBound {ρ α : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hα : 0 < α) :
    roundedProfile ρ α < roundedRadiusBound ρ := by
  let t : ℝ := 1 / (2 * α)
  let E : Set ℝ := Set.Icc (-t) t
  let f : ℝ → ℝ := roundedCoordinateObservable α ρ 1
  have ht : 0 < t := by dsimp [t]; positivity
  have hEmeas : MeasurableSet E := measurableSet_Icc
  have hzero : ∀ g ∈ E, f g = 0 := by
    intro g hg
    have habsg : |g| ≤ t := abs_le.mpr ⟨by linarith [hg.1], hg.2⟩
    have htanh :
        |Real.tanh (ρ * α * g)| ≤ |ρ * (α * g)| := by
      simpa only [mul_assoc] using abs_tanh_le_abs (ρ * (α * g))
    have harg :
        |ρ⁻¹ * Real.tanh (ρ * α * g)| ≤ 2⁻¹ := by
      rw [abs_mul, abs_inv, abs_of_pos hρ]
      rw [abs_mul, abs_of_pos hρ] at htanh
      calc
        ρ⁻¹ * |Real.tanh (ρ * α * g)| ≤
            ρ⁻¹ * (ρ * |α * g|) :=
          mul_le_mul_of_nonneg_left htanh (inv_nonneg.mpr hρ.le)
        _ = |α * g| := by field_simp
        _ = α * |g| := by rw [abs_mul, abs_of_pos hα]
        _ ≤ α * t := mul_le_mul_of_nonneg_left habsg hα.le
        _ = 2⁻¹ := by dsimp [t]; field_simp
    have hQ := (Q₁_zero_iff _).mpr harg
    simp [f, roundedCoordinateObservable, hQ]
  have hpoint :
      ∀ g, f g ≤ Eᶜ.indicator (fun _ => roundedRadiusBound ρ) g := by
    intro g
    by_cases hg : g ∈ E
    · rw [hzero g hg, Set.indicator_of_notMem (by simpa using hg)]
    · rw [Set.indicator_of_mem (by simpa using hg)]
      simpa only [f, roundedCoordinateObservable, Real.sqrt_one, mul_one, mul_assoc] using
        (Q₁_inv_tanh_sq_le_roundedRadiusBound (ρ := ρ) (x := α * g) hρ)
  have hfint : Integrable f (gaussianReal 0 1) := by
    dsimp [f]
    simpa using
      (integrable_pow_roundedCoordinateObservable
        (A := α) (ρ := ρ) (h := 1) hρ 1)
  have hright :
      Integrable (Eᶜ.indicator (fun _ : ℝ => roundedRadiusBound ρ))
        (gaussianReal 0 1) :=
    (integrable_const _).indicator hEmeas.compl
  have hEpos :
      0 < (gaussianReal 0 1).real E := by
    simpa [E] using gaussianReal_Icc_neg_pos ht
  have hsum := measureReal_add_measureReal_compl
    (μ := gaussianReal 0 1) hEmeas
  rw [probReal_univ] at hsum
  have hcompl_lt : (gaussianReal 0 1).real Eᶜ < 1 := by linarith
  rw [← show roundedMeanMap α ρ 1 = roundedProfile ρ α by
    simpa only [Real.sqrt_one, mul_one] using
      roundedMeanMap_eq_roundedProfile α ρ 1]
  rw [← integral_roundedCoordinateObservable]
  calc
    ∫ g, f g ∂(gaussianReal 0 1) ≤
        ∫ g, Eᶜ.indicator (fun _ : ℝ => roundedRadiusBound ρ) g
          ∂(gaussianReal 0 1) :=
      integral_mono hfint hright hpoint
    _ = (gaussianReal 0 1).real Eᶜ * roundedRadiusBound ρ := by
      rw [integral_indicator_const _ hEmeas.compl, smul_eq_mul]
    _ < roundedRadiusBound ρ :=
      mul_lt_of_lt_one_left (roundedRadiusBound_pos hρ hρ_lt) hcompl_lt

/-- At every positive radius, the rounded mean map is strictly below `M_ρ`. -/
lemma roundedMeanMap_lt_roundedRadiusBound {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hh : 0 < h) :
    roundedMeanMap A ρ h < roundedRadiusBound ρ := by
  rw [roundedMeanMap_eq_roundedProfile]
  exact roundedProfile_lt_roundedRadiusBound hρ hρ_lt
    (mul_pos hA (Real.sqrt_pos.2 hh))

/-- At large scales, the bounded fixed-precision profile is negligible
compared with `α²`. -/
lemma tendsto_roundedProfile_div_sq_atTop {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun α : ℝ => roundedProfile ρ α / α ^ 2)
      atTop (𝓝 0) := by
  have hupper :
      Tendsto (fun α : ℝ => roundedRadiusBound ρ / α ^ 2)
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun α =>
      div_nonneg (roundedProfile_nonneg ρ α) (sq_nonneg α))
    (Filter.Eventually.of_forall fun α =>
      div_le_div_of_nonneg_right (roundedProfile_le_roundedRadiusBound hρ)
        (sq_nonneg α))
    hupper

/-- The threshold ratio diverges at the large-scale endpoint. -/
lemma tendsto_roundedThresholdRatio_atTop {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    Tendsto (roundedThresholdRatio ρ) atTop atTop := by
  have hpos : ∀ᶠ α : ℝ in atTop, 0 < roundedProfile ρ α / α ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
    exact div_pos (roundedProfile_pos hρ hρ_lt hα) (sq_pos_of_pos hα)
  have hzero :
      Tendsto (fun α : ℝ => roundedProfile ρ α / α ^ 2)
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_roundedProfile_div_sq_atTop hρ, hpos⟩
  refine hzero.inv_tendsto_nhdsGT_zero.congr' ?_
  filter_upwards with α
  simp [roundedThresholdRatio, inv_div]

/-- The rounded mean map is little-o of the radius at the origin. -/
lemma tendsto_roundedMeanMap_div_self_nhdsGT_zero {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    Tendsto (fun h : ℝ => roundedMeanMap A ρ h / h)
      (𝓝[>] 0) (𝓝 0) := by
  simpa [roundedMeanMap_zero, smul_eq_mul, div_eq_inv_mul] using
    (hasDerivAt_roundedMeanMap_zero hA hρ hρ_lt).tendsto_slope_zero_right

/-- At small positive scales, the fixed-precision profile is negligible
compared with `α²`. -/
lemma tendsto_roundedProfile_div_sq_nhdsGT_zero {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    Tendsto (fun α : ℝ => roundedProfile ρ α / α ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hsq : Tendsto (fun α : ℝ => α ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨by
        have hc : ContinuousWithinAt (fun α : ℝ => α ^ 2) (Set.Ioi 0) 0 :=
          (continuousAt_id.pow 2).continuousWithinAt
        change Tendsto (fun α : ℝ => α ^ 2) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ 2)) at hc
        simpa using hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with α hα
    change 0 < α ^ 2
    exact sq_pos_of_pos hα
  refine (tendsto_roundedMeanMap_div_self_nhdsGT_zero
    (A := 1) zero_lt_one hρ hρ_lt).comp hsq |>.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  rw [Function.comp_apply, roundedProfile_eq_roundedMeanMap_sq hα.le]

/-- The threshold ratio diverges at the small-scale endpoint. -/
lemma tendsto_roundedThresholdRatio_nhdsGT_zero {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    Tendsto (roundedThresholdRatio ρ) (𝓝[>] 0) atTop := by
  have hpos : ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < roundedProfile ρ α / α ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact div_pos (roundedProfile_pos hρ hρ_lt hα) (sq_pos_of_pos hα)
  have hzero :
      Tendsto (fun α : ℝ => roundedProfile ρ α / α ^ 2)
        (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_roundedProfile_div_sq_nhdsGT_zero hρ hρ_lt, hpos⟩
  refine hzero.inv_tendsto_nhdsGT_zero.congr' ?_
  filter_upwards with α
  simp [roundedThresholdRatio, inv_div]

/-- The threshold ratio attains a global minimum on the positive half-line. -/
lemma exists_isMinOn_roundedThresholdRatio_Ioi {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧
      ∀ β : ℝ, 0 < β → roundedThresholdRatio ρ α ≤ roundedThresholdRatio ρ β := by
  let f : ℝ → ℝ := roundedThresholdRatio ρ ∘ Real.exp
  have hf : Continuous f :=
    (continuousOn_roundedThresholdRatio_Ioi hρ hρ_lt).comp_continuous
      Real.continuous_exp (fun x => Real.exp_pos x)
  have htop : Tendsto f atTop atTop :=
    (tendsto_roundedThresholdRatio_atTop hρ hρ_lt).comp Real.tendsto_exp_atTop
  have hbot : Tendsto f atBot atTop :=
    (tendsto_roundedThresholdRatio_nhdsGT_zero hρ hρ_lt).comp
      Real.tendsto_exp_atBot_nhdsGT
  have hcocompact : Tendsto f (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_sup.mpr ⟨hbot, htop⟩
  obtain ⟨x, hx⟩ := hf.exists_forall_le hcocompact
  refine ⟨Real.exp x, Real.exp_pos x, ?_⟩
  intro β hβ
  simpa [f, Function.comp_apply, Real.exp_log hβ] using hx (Real.log β)

/-- The squared existence threshold is the ratio at a positive global
minimizer. -/
lemma exists_roundedExistenceThresholdSq_eq_ratio {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧
      roundedExistenceThresholdSq ρ = roundedThresholdRatio ρ α ∧
      ∀ β : ℝ, 0 < β →
        roundedThresholdRatio ρ α ≤ roundedThresholdRatio ρ β := by
  obtain ⟨α, hα, hmin⟩ :=
    exists_isMinOn_roundedThresholdRatio_Ioi hρ hρ_lt
  let S : Set ℝ := roundedThresholdRatio ρ '' Set.Ioi 0
  have hSne : S.Nonempty := ⟨roundedThresholdRatio ρ α, ⟨α, hα, rfl⟩⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro y ⟨β, hβ, rfl⟩
    exact (roundedThresholdRatio_pos hρ hρ_lt hβ).le
  refine ⟨α, hα, ?_, hmin⟩
  rw [roundedExistenceThresholdSq]
  change sInf S = roundedThresholdRatio ρ α
  apply le_antisymm
  · exact csInf_le hSbdd ⟨α, hα, rfl⟩
  · apply le_csInf hSne
    rintro y ⟨β, hβ, rfl⟩
    exact hmin β hβ

/-- The squared fixed-precision existence threshold is strictly positive. -/
lemma roundedExistenceThresholdSq_pos {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 < roundedExistenceThresholdSq ρ := by
  obtain ⟨α, hα, heq, _⟩ :=
    exists_roundedExistenceThresholdSq_eq_ratio hρ hρ_lt
  rw [heq]
  exact roundedThresholdRatio_pos hρ hρ_lt hα

/-- The fixed-precision existence threshold is strictly positive. -/
lemma roundedExistenceThreshold_pos {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 < roundedExistenceThreshold ρ := by
  rw [roundedExistenceThreshold]
  exact Real.sqrt_pos.2 (roundedExistenceThresholdSq_pos hρ hρ_lt)

/-- Squaring the existence threshold recovers its defining infimum. -/
@[simp] lemma roundedExistenceThreshold_sq {ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    roundedExistenceThreshold ρ ^ 2 = roundedExistenceThresholdSq ρ := by
  rw [roundedExistenceThreshold,
    Real.sq_sqrt (roundedExistenceThresholdSq_pos hρ hρ_lt).le]

/-- Above the existence threshold, the profile has strictly positive drift at
some positive scale. -/
lemma exists_pos_sq_mul_roundedProfile_sub_sq {A ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hA : roundedExistenceThreshold ρ < A) :
    ∃ α : ℝ, 0 < α ∧
      0 < A ^ 2 * roundedProfile ρ α - α ^ 2 := by
  obtain ⟨α, hα, heq, _⟩ :=
    exists_roundedExistenceThresholdSq_eq_ratio hρ hρ_lt
  have hthreshold_pos := roundedExistenceThreshold_pos hρ hρ_lt
  have hsq : roundedExistenceThresholdSq ρ < A ^ 2 := by
    rw [← roundedExistenceThreshold_sq hρ hρ_lt]
    nlinarith
  have hratio : roundedThresholdRatio ρ α < A ^ 2 := by
    rwa [heq] at hsq
  have hprofile := roundedProfile_pos hρ hρ_lt hα
  rw [roundedThresholdRatio, div_lt_iff₀ hprofile] at hratio
  refine ⟨α, hα, ?_⟩
  nlinarith

/-- On both sides of every positive scale, sufficiently extreme scales have
negative profile drift. -/
lemma exists_profileDrift_neg_below_above {A ρ α₀ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hα₀ : 0 < α₀) :
    ∃ alphaLow alphaHigh : ℝ,
      0 < alphaLow ∧ alphaLow < α₀ ∧ α₀ < alphaHigh ∧
      roundedProfileDrift A ρ alphaLow < 0 ∧
      roundedProfileDrift A ρ alphaHigh < 0 := by
  have hsmall :
      ∀ᶠ α : ℝ in 𝓝[>] 0, A ^ 2 + 1 ≤ roundedThresholdRatio ρ α :=
    (tendsto_roundedThresholdRatio_nhdsGT_zero hρ hρ_lt).eventually
      (eventually_ge_atTop (A ^ 2 + 1))
  obtain ⟨alphaLow, hratioLow, halphaLow⟩ :=
    (hsmall.and (Ioc_mem_nhdsGT (half_pos hα₀))).exists
  have hlarge :
      ∀ᶠ α : ℝ in atTop, A ^ 2 + 1 ≤ roundedThresholdRatio ρ α :=
    (tendsto_roundedThresholdRatio_atTop hρ hρ_lt).eventually
      (eventually_ge_atTop (A ^ 2 + 1))
  obtain ⟨alphaHigh, hratioHigh, halphaHigh⟩ :=
    (hlarge.and (eventually_gt_atTop α₀)).exists
  have hprofileLow := roundedProfile_pos hρ hρ_lt halphaLow.1
  have hprofileHigh :=
    roundedProfile_pos hρ hρ_lt (hα₀.trans halphaHigh)
  have hltLow :
      A ^ 2 * roundedProfile ρ alphaLow < alphaLow ^ 2 := by
    have hratio : A ^ 2 < roundedThresholdRatio ρ alphaLow := by
      linarith [hratioLow]
    rwa [roundedThresholdRatio, lt_div_iff₀ hprofileLow] at hratio
  have hltHigh :
      A ^ 2 * roundedProfile ρ alphaHigh < alphaHigh ^ 2 := by
    have hratio : A ^ 2 < roundedThresholdRatio ρ alphaHigh := by
      linarith [hratioHigh]
    rwa [roundedThresholdRatio, lt_div_iff₀ hprofileHigh] at hratio
  refine ⟨alphaLow, alphaHigh, halphaLow.1, ?_, halphaHigh, ?_, ?_⟩
  · linarith [halphaLow.2]
  · exact sub_neg.mpr hltLow
  · exact sub_neg.mpr hltHigh

/-- Above the existence threshold, the profile equation has two distinct
positive roots. -/
lemma exists_two_pos_roundedProfile_roots {A ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hA : roundedExistenceThreshold ρ < A) :
    ∃ alphaMinus alphaPlus : ℝ,
      0 < alphaMinus ∧ alphaMinus < alphaPlus ∧
      A ^ 2 * roundedProfile ρ alphaMinus = alphaMinus ^ 2 ∧
      A ^ 2 * roundedProfile ρ alphaPlus = alphaPlus ^ 2 := by
  obtain ⟨α₀, hα₀, hpos⟩ :=
    exists_pos_sq_mul_roundedProfile_sub_sq hρ hρ_lt hA
  have hposDrift : 0 < roundedProfileDrift A ρ α₀ := by
    simpa only [roundedProfileDrift] using hpos
  obtain ⟨alphaLow, alphaHigh, halphaLow, hlow_lt, hlt_high,
      hnegLow, hnegHigh⟩ :=
    exists_profileDrift_neg_below_above (A := A) hρ hρ_lt hα₀
  have hcontLow : ContinuousOn (roundedProfileDrift A ρ)
      (Set.Icc alphaLow α₀) :=
    (continuousOn_roundedProfileDrift_Ioi (A := A) hρ).mono fun α hα =>
      halphaLow.trans_le hα.1
  have hzeroMemLow :
      (0 : ℝ) ∈ Set.Icc
        (roundedProfileDrift A ρ alphaLow)
        (roundedProfileDrift A ρ α₀) :=
    ⟨hnegLow.le, hposDrift.le⟩
  obtain ⟨alphaMinus, hminusMem, hminusZero⟩ :=
    intermediate_value_Icc hlow_lt.le hcontLow hzeroMemLow
  have hcontHigh : ContinuousOn (roundedProfileDrift A ρ)
      (Set.Icc α₀ alphaHigh) :=
    (continuousOn_roundedProfileDrift_Ioi (A := A) hρ).mono fun α hα =>
      hα₀.trans_le hα.1
  have hzeroMemHigh :
      (0 : ℝ) ∈ Set.Icc
        (roundedProfileDrift A ρ alphaHigh)
        (roundedProfileDrift A ρ α₀) :=
    ⟨hnegHigh.le, hposDrift.le⟩
  obtain ⟨alphaPlus, hplusMem, hplusZero⟩ :=
    intermediate_value_Icc' hlt_high.le hcontHigh hzeroMemHigh
  have hminus_pos : 0 < alphaMinus :=
    halphaLow.trans_le hminusMem.1
  have hminus_lt : alphaMinus < α₀ := by
    apply lt_of_le_of_ne hminusMem.2
    intro heq
    have hzero : roundedProfileDrift A ρ α₀ = 0 := by
      rw [← heq]
      exact hminusZero
    exact (ne_of_gt hposDrift) hzero
  have hplus_gt : α₀ < alphaPlus := by
    apply lt_of_le_of_ne hplusMem.1
    intro heq
    have hzero : roundedProfileDrift A ρ α₀ = 0 := by
      rw [heq]
      exact hplusZero
    exact (ne_of_gt hposDrift) hzero
  refine ⟨alphaMinus, alphaPlus, hminus_pos,
    hminus_lt.trans hplus_gt, ?_, ?_⟩
  · rw [roundedProfileDrift] at hminusZero
    linarith
  · rw [roundedProfileDrift] at hplusZero
    linarith

/-- The profile-to-radius change of variables at `h = α² / A²`. -/
lemma roundedMeanMap_sq_div_sq_eq_profile {A ρ α : ℝ}
    (hA : 0 < A) (hα : 0 ≤ α) :
    roundedMeanMap A ρ (α ^ 2 / A ^ 2) = roundedProfile ρ α := by
  have hA0 : A ≠ 0 := hA.ne'
  have hsquare : α ^ 2 / A ^ 2 = (α / A) ^ 2 := by
    field_simp
  have hdiv_nonneg : 0 ≤ α / A := div_nonneg hα hA.le
  have hsqrt : Real.sqrt (α ^ 2 / A ^ 2) = α / A := by
    rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hdiv_nonneg]
  rw [roundedMeanMap_eq_roundedProfile, hsqrt]
  have hmul : A * (α / A) = α := by field_simp
  rw [hmul]

/-- A positive solution of the profile equation becomes a positive fixed
radius under `h = α² / A²`. -/
lemma roundedMeanMap_fixed_of_profile_root {A ρ α : ℝ}
    (hA : 0 < A) (hα : 0 < α)
    (hroot : A ^ 2 * roundedProfile ρ α = α ^ 2) :
    0 < α ^ 2 / A ^ 2 ∧
      roundedMeanMap A ρ (α ^ 2 / A ^ 2) = α ^ 2 / A ^ 2 := by
  have hA0 : A ≠ 0 := hA.ne'
  constructor
  · exact div_pos (sq_pos_of_pos hα) (sq_pos_of_pos hA)
  · rw [roundedMeanMap_sq_div_sq_eq_profile hA hα.le]
    rw [eq_div_iff (pow_ne_zero 2 hA0)]
    simpa only [mul_comm] using hroot

/-- Above the existence threshold, the rounded mean map has two ordered
positive fixed radii. -/
lemma exists_two_pos_roundedMeanMap_fixedPoints {A ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hA : roundedExistenceThreshold ρ < A) :
    ∃ hMinus hPlus : ℝ,
      0 < hMinus ∧ hMinus < hPlus ∧
      roundedMeanMap A ρ hMinus = hMinus ∧
      roundedMeanMap A ρ hPlus = hPlus := by
  obtain ⟨alphaMinus, alphaPlus, hminusPos, hminusLt,
      hminusRoot, hplusRoot⟩ :=
    exists_two_pos_roundedProfile_roots hρ hρ_lt hA
  have hApos : 0 < A :=
    (roundedExistenceThreshold_pos hρ hρ_lt).trans hA
  have hplusPos : 0 < alphaPlus := hminusPos.trans hminusLt
  obtain ⟨hRadiusMinusPos, hRadiusMinusFixed⟩ :=
    roundedMeanMap_fixed_of_profile_root hApos hminusPos hminusRoot
  obtain ⟨hRadiusPlusPos, hRadiusPlusFixed⟩ :=
    roundedMeanMap_fixed_of_profile_root hApos hplusPos hplusRoot
  have hsquares : alphaMinus ^ 2 < alphaPlus ^ 2 := by
    nlinarith
  refine ⟨alphaMinus ^ 2 / A ^ 2, alphaPlus ^ 2 / A ^ 2,
    hRadiusMinusPos, ?_, hRadiusMinusFixed, hRadiusPlusFixed⟩
  exact div_lt_div_of_pos_right hsquares (sq_pos_of_pos hApos)

/-- Above the existence threshold, both positive fixed radii lie strictly
inside the paper's bounded radius interval `(0, M_ρ)`. -/
lemma exists_two_roundedMeanMap_fixedPoints_Ioo {A ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hA : roundedExistenceThreshold ρ < A) :
    ∃ hMinus hPlus : ℝ,
      hMinus ∈ Set.Ioo 0 (roundedRadiusBound ρ) ∧
      hPlus ∈ Set.Ioo 0 (roundedRadiusBound ρ) ∧
      hMinus < hPlus ∧
      roundedMeanMap A ρ hMinus = hMinus ∧
      roundedMeanMap A ρ hPlus = hPlus := by
  obtain ⟨hMinus, hPlus, hminusPos, hminusLt,
      hminusFixed, hplusFixed⟩ :=
    exists_two_pos_roundedMeanMap_fixedPoints hρ hρ_lt hA
  have hApos : 0 < A :=
    (roundedExistenceThreshold_pos hρ hρ_lt).trans hA
  have hplusPos : 0 < hPlus := hminusPos.trans hminusLt
  have hminusBound : hMinus < roundedRadiusBound ρ := by
    rw [← hminusFixed]
    exact roundedMeanMap_lt_roundedRadiusBound hApos hρ hρ_lt hminusPos
  have hplusBound : hPlus < roundedRadiusBound ρ := by
    rw [← hplusFixed]
    exact roundedMeanMap_lt_roundedRadiusBound hApos hρ hρ_lt hplusPos
  exact ⟨hMinus, hPlus, ⟨hminusPos, hminusBound⟩,
    ⟨hplusPos, hplusBound⟩, hminusLt, hminusFixed, hplusFixed⟩

/-- Above the existence threshold, the positive-drift region is nonempty. -/
lemma roundedPositiveDriftSet_nonempty {A ρ : ℝ}
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hA : roundedExistenceThreshold ρ < A) :
    (roundedPositiveDriftSet A ρ).Nonempty := by
  obtain ⟨α, hα, hdrift⟩ :=
    exists_pos_sq_mul_roundedProfile_sub_sq hρ hρ_lt hA
  have hApos : 0 < A :=
    (roundedExistenceThreshold_pos hρ hρ_lt).trans hA
  let h : ℝ := α ^ 2 / A ^ 2
  have hh : 0 < h := by
    exact div_pos (sq_pos_of_pos hα) (sq_pos_of_pos hApos)
  have hmap :
      roundedMeanMap A ρ h = roundedProfile ρ α := by
    exact roundedMeanMap_sq_div_sq_eq_profile hApos hα.le
  have hlt : h < roundedMeanMap A ρ h := by
    rw [hmap]
    dsimp [h]
    rw [div_lt_iff₀ (sq_pos_of_pos hApos)]
    nlinarith
  have hbound : h < roundedRadiusBound ρ :=
    hlt.trans (roundedMeanMap_lt_roundedRadiusBound hApos hρ hρ_lt hh)
  exact ⟨h, ⟨⟨hh, hbound⟩, hlt⟩⟩

/-- The positive-drift region is open. -/
lemma isOpen_roundedPositiveDriftSet {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    IsOpen (roundedPositiveDriftSet A ρ) := by
  change IsOpen
    (Set.Ioo 0 (roundedRadiusBound ρ) ∩
      {h : ℝ | h < roundedMeanMap A ρ h})
  exact isOpen_Ioo.inter
    (isOpen_lt continuous_id (continuous_roundedMeanMap hA hρ hρ_lt))

/-- Every positive-drift component is open. -/
lemma isOpen_roundedPositiveDriftComponent {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    IsOpen (roundedPositiveDriftComponent A ρ h) := by
  exact (isOpen_roundedPositiveDriftSet hA hρ hρ_lt).connectedComponentIn

/-- A component through a point of the positive-drift region is connected. -/
lemma isConnected_roundedPositiveDriftComponent {A ρ h : ℝ}
    (hh : h ∈ roundedPositiveDriftSet A ρ) :
    IsConnected (roundedPositiveDriftComponent A ρ h) := by
  exact isConnected_connectedComponentIn_iff.mpr hh

/-- Each positive-drift component is contained in the positive-drift region. -/
lemma roundedPositiveDriftComponent_subset (A ρ h : ℝ) :
    roundedPositiveDriftComponent A ρ h ⊆ roundedPositiveDriftSet A ρ :=
  connectedComponentIn_subset _ _

/-- A bounded nonempty open connected subset of the real line is the open
interval between its infimum and supremum. -/
lemma eq_Ioo_csInf_csSup_of_isOpen_isConnected {s : Set ℝ}
    (hsOpen : IsOpen s) (hsConnected : IsConnected s)
    (hsBelow : BddBelow s) (hsAbove : BddAbove s) :
    s = Set.Ioo (sInf s) (sSup s) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hsOpen x hx
    have hleft : x - ε / 2 ∈ s := by
      apply hball
      change dist (x - ε / 2) x < ε
      rw [Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hε]
      linarith
    have hright : x + ε / 2 ∈ s := by
      apply hball
      change dist (x + ε / 2) x < ε
      rw [Real.dist_eq]
      simp only [add_sub_cancel_left, abs_div, abs_of_pos hε]
      linarith
    have hinf : sInf s ≤ x - ε / 2 := csInf_le hsBelow hleft
    have hsup : x + ε / 2 ≤ sSup s := le_csSup hsAbove hright
    exact ⟨by linarith, by linarith⟩
  · exact hsConnected.Ioo_csInf_csSup_subset hsBelow hsAbove

/-- Every positive-drift component is exactly the open interval between its
finite endpoints. -/
lemma roundedPositiveDriftComponent_eq_Ioo {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ) :
    roundedPositiveDriftComponent A ρ h =
      Set.Ioo (sInf (roundedPositiveDriftComponent A ρ h))
        (sSup (roundedPositiveDriftComponent A ρ h)) := by
  let C := roundedPositiveDriftComponent A ρ h
  have hsub : C ⊆ roundedPositiveDriftSet A ρ :=
    roundedPositiveDriftComponent_subset A ρ h
  have hbelow : BddBelow C :=
    ⟨0, fun x hx => (hsub hx).1.1.le⟩
  have habove : BddAbove C :=
    ⟨roundedRadiusBound ρ, fun x hx => (hsub hx).1.2.le⟩
  exact eq_Ioo_csInf_csSup_of_isOpen_isConnected
    (isOpen_roundedPositiveDriftComponent hA hρ hρ_lt)
    (isConnected_roundedPositiveDriftComponent hh) hbelow habove

/-- The positive-drift region is separated from the origin. -/
lemma exists_pos_not_mem_roundedPositiveDriftSet_near_zero {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ a : ℝ, 0 < a ∧
      ∀ h : ℝ, 0 < h → h ≤ a → h ∉ roundedPositiveDriftSet A ρ := by
  have hevent :
      {h : ℝ | roundedMeanMap A ρ h / h < 1} ∈ 𝓝[>] 0 :=
    (tendsto_roundedMeanMap_div_self_nhdsGT_zero hA hρ hρ_lt).eventually
      (Iio_mem_nhds zero_lt_one)
  obtain ⟨a, ha, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioc_subset.mp hevent
  refine ⟨a, ha, ?_⟩
  intro h hh hha hmem
  have hratio : roundedMeanMap A ρ h / h < 1 :=
    hsub ⟨hh, hha⟩
  rw [div_lt_one hh] at hratio
  exact (lt_asymm hmem.2 hratio).elim

/-- The positive-drift region is separated from its ambient upper radius
bound. -/
lemma exists_lt_radiusBound_not_mem_roundedPositiveDriftSet_near_top
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ b : ℝ, 0 < b ∧ b < roundedRadiusBound ρ ∧
      ∀ h : ℝ, b ≤ h → h < roundedRadiusBound ρ →
        h ∉ roundedPositiveDriftSet A ρ := by
  let M := roundedRadiusBound ρ
  have hM : 0 < M := roundedRadiusBound_pos hρ hρ_lt
  have hMneg : roundedMeanMap A ρ M < M :=
    roundedMeanMap_lt_roundedRadiusBound hA hρ hρ_lt hM
  have hOpen :
      IsOpen {h : ℝ | roundedMeanMap A ρ h < h} :=
    isOpen_lt (continuous_roundedMeanMap hA hρ hρ_lt) continuous_id
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hOpen M hMneg
  let δ := min (ε / 2) (M / 2)
  let b := M - δ
  have hδ : 0 < δ := lt_min (half_pos hε) (half_pos hM)
  have hδ_le_M : δ ≤ M / 2 := min_le_right _ _
  have hδ_lt_ε : δ < ε :=
    (min_le_left _ _).trans_lt (half_lt_self hε)
  have hb : 0 < b := by
    dsimp [b]
    linarith
  have hbM : b < M := by dsimp [b]; linarith
  refine ⟨b, hb, hbM, ?_⟩
  intro y hby hyM hy
  have hyball : y ∈ Metric.ball M ε := by
    change dist y M < ε
    have hyM' : y ≤ M := by simpa [M] using hyM.le
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hyM')]
    have hdist : M - y ≤ δ := by
      dsimp [b] at hby
      linarith
    linarith
  have hyneg : roundedMeanMap A ρ y < y := hball hyball
  exact (lt_asymm hy.2 hyneg).elim

/-- The endpoints of every positive-drift component lie strictly inside
`(0, M_ρ)` and are strictly ordered. -/
lemma roundedPositiveDriftComponent_endpoints {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ) :
    0 < sInf (roundedPositiveDriftComponent A ρ h) ∧
      sInf (roundedPositiveDriftComponent A ρ h) <
        sSup (roundedPositiveDriftComponent A ρ h) ∧
      sSup (roundedPositiveDriftComponent A ρ h) <
        roundedRadiusBound ρ := by
  let C := roundedPositiveDriftComponent A ρ h
  have hsub : C ⊆ roundedPositiveDriftSet A ρ :=
    roundedPositiveDriftComponent_subset A ρ h
  have hhC : h ∈ C := mem_connectedComponentIn hh
  have hCne : C.Nonempty := ⟨h, hhC⟩
  obtain ⟨a, ha, haExclude⟩ :=
    exists_pos_not_mem_roundedPositiveDriftSet_near_zero hA hρ hρ_lt
  have haLower : ∀ x ∈ C, a ≤ x := by
    intro x hx
    have hxO := hsub hx
    by_contra hax
    have hxa : x ≤ a := le_of_not_ge hax
    exact (haExclude x hxO.1.1 hxa) hxO
  have hinfLower : a ≤ sInf C := le_csInf hCne haLower
  obtain ⟨b, hb, hbM, hbExclude⟩ :=
    exists_lt_radiusBound_not_mem_roundedPositiveDriftSet_near_top
      hA hρ hρ_lt
  have hbUpper : ∀ x ∈ C, x ≤ b := by
    intro x hx
    have hxO := hsub hx
    by_contra hxb
    have hbx : b ≤ x := le_of_not_ge hxb
    exact (hbExclude x hbx hxO.1.2) hxO
  have hsupUpper : sSup C ≤ b := csSup_le hCne hbUpper
  have hinterval :
      C = Set.Ioo (sInf C) (sSup C) := by
    exact roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh
  have hhInterval : h ∈ Set.Ioo (sInf C) (sSup C) := by
    rw [← hinterval]
    exact hhC
  exact ⟨ha.trans_le hinfLower, hhInterval.1.trans hhInterval.2,
    hsupUpper.trans_lt hbM⟩

/-- Both endpoints of a positive-drift component are fixed points of the
rounded mean map. -/
lemma roundedPositiveDriftComponent_endpoints_fixed {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ) :
    roundedMeanMap A ρ (sInf (roundedPositiveDriftComponent A ρ h)) =
        sInf (roundedPositiveDriftComponent A ρ h) ∧
      roundedMeanMap A ρ (sSup (roundedPositiveDriftComponent A ρ h)) =
        sSup (roundedPositiveDriftComponent A ρ h) := by
  let C := roundedPositiveDriftComponent A ρ h
  let lower := sInf C
  let upper := sSup C
  have hends := roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  have hlowerPos : 0 < lower := hends.1
  have hlowerUpper : lower < upper := hends.2.1
  have hupperBound : upper < roundedRadiusBound ρ := hends.2.2
  have hhC : h ∈ C := mem_connectedComponentIn hh
  have hinterval : C = Set.Ioo lower upper := by
    exact roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh
  have hhInterval : h ∈ Set.Ioo lower upper := by
    rw [← hinterval]
    exact hhC
  have hsub : C ⊆ roundedPositiveDriftSet A ρ :=
    roundedPositiveDriftComponent_subset A ρ h
  have hclosed :
      IsClosed {x : ℝ | x ≤ roundedMeanMap A ρ x} :=
    isClosed_le continuous_id (continuous_roundedMeanMap hA hρ hρ_lt)
  have hclosure :
      closure C ⊆ {x : ℝ | x ≤ roundedMeanMap A ρ x} :=
    closure_minimal (fun x hx => (hsub hx).2.le) hclosed
  have hlowerClosure : lower ∈ closure C := by
    rw [hinterval, closure_Ioo hlowerUpper.ne]
    exact ⟨le_rfl, hlowerUpper.le⟩
  have hupperClosure : upper ∈ closure C := by
    rw [hinterval, closure_Ioo hlowerUpper.ne]
    exact ⟨hlowerUpper.le, le_rfl⟩
  have hlowerLe : lower ≤ roundedMeanMap A ρ lower :=
    hclosure hlowerClosure
  have hupperLe : upper ≤ roundedMeanMap A ρ upper :=
    hclosure hupperClosure
  have hlowerNotLt : ¬lower < roundedMeanMap A ρ lower := by
    intro hlowerLt
    have hlowerO : lower ∈ roundedPositiveDriftSet A ρ :=
      ⟨⟨hlowerPos, hlowerUpper.trans hupperBound⟩, hlowerLt⟩
    have hIccSub :
        Set.Icc lower h ⊆ roundedPositiveDriftSet A ρ := by
      intro x hx
      rcases hx.1.eq_or_lt with hxeq | hlowerx
      · rwa [← hxeq]
      · apply hsub
        rw [hinterval]
        exact ⟨hlowerx, hx.2.trans_lt hhInterval.2⟩
    have hIccC :
        Set.Icc lower h ⊆ C :=
      isPreconnected_Icc.subset_connectedComponentIn
        (Set.right_mem_Icc.2 hhInterval.1.le) hIccSub
    have hlowerC := hIccC (Set.left_mem_Icc.2 hhInterval.1.le)
    rw [hinterval] at hlowerC
    exact (lt_irrefl lower hlowerC.1)
  have hupperNotLt : ¬upper < roundedMeanMap A ρ upper := by
    intro hupperLt
    have hupperO : upper ∈ roundedPositiveDriftSet A ρ :=
      ⟨⟨hlowerPos.trans hlowerUpper, hupperBound⟩, hupperLt⟩
    have hIccSub :
        Set.Icc h upper ⊆ roundedPositiveDriftSet A ρ := by
      intro x hx
      rcases hx.2.lt_or_eq with hxupper | hxeq
      · apply hsub
        rw [hinterval]
        exact ⟨hhInterval.1.trans_le hx.1, hxupper⟩
      · rwa [hxeq]
    have hIccC :
        Set.Icc h upper ⊆ C :=
      isPreconnected_Icc.subset_connectedComponentIn
        (Set.left_mem_Icc.2 hhInterval.2.le) hIccSub
    have hupperC := hIccC (Set.right_mem_Icc.2 hhInterval.2.le)
    rw [hinterval] at hupperC
    exact (lt_irrefl upper hupperC.2)
  exact ⟨le_antisymm (le_of_not_gt hlowerNotLt) hlowerLe,
    le_antisymm (le_of_not_gt hupperNotLt) hupperLe⟩

/-- On an interval with no fixed point, the sign of the drift cannot change.
In particular, one strictly negative right endpoint forces strictly negative
drift throughout the half-open interval. -/
lemma lt_self_on_Ioc_of_continuousOn_of_ne_fixed {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hb : f b < b)
    (hne : ∀ x ∈ Set.Ioc a b, f x ≠ x) :
    ∀ x ∈ Set.Ioc a b, f x < x := by
  intro x hx
  by_contra hxneg
  have hxle : x ≤ f x := le_of_not_gt hxneg
  have hxb : x ≤ b := hx.2
  have hcont :
      ContinuousOn (fun y : ℝ => f y - y) (Set.Icc x b) :=
    ((hf.mono fun y hy => ⟨hx.1.le.trans hy.1, hy.2⟩).sub continuousOn_id)
  have hzero :
      (0 : ℝ) ∈ Set.Icc (f b - b) (f x - x) :=
    ⟨sub_nonpos.mpr hb.le, sub_nonneg.mpr hxle⟩
  obtain ⟨y, hy, hyzero⟩ :=
    intermediate_value_Icc' hxb hcont hzero
  have hyIoc : y ∈ Set.Ioc a b :=
    ⟨hx.1.trans_le hy.1, hy.2⟩
  exact hne y hyIoc (sub_eq_zero.mp hyzero)

/-- Complete specification of a positive-drift component, apart from the
isolated-zero/right-stability clause. -/
lemma roundedPositiveDriftComponent_spec {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ) :
    let C := roundedPositiveDriftComponent A ρ h
    C = Set.Ioo (sInf C) (sSup C) ∧
      0 < sInf C ∧ sInf C < sSup C ∧
      sSup C < roundedRadiusBound ρ ∧
      roundedMeanMap A ρ (sInf C) = sInf C ∧
      roundedMeanMap A ρ (sSup C) = sSup C ∧
      ∀ u ∈ Set.Ioo (sInf C) (sSup C), u < roundedMeanMap A ρ u := by
  dsimp only
  let C := roundedPositiveDriftComponent A ρ h
  have hinterval :=
    roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh
  have hends := roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  have hfixed :=
    roundedPositiveDriftComponent_endpoints_fixed hA hρ hρ_lt hh
  refine ⟨hinterval, hends.1, hends.2.1, hends.2.2,
    hfixed.1, hfixed.2, ?_⟩
  intro u hu
  have huC : u ∈ C := by
    change u ∈ roundedPositiveDriftComponent A ρ h
    rw [hinterval]
    exact hu
  exact (roundedPositiveDriftComponent_subset A ρ h huC).2

/-- If the positive-drift set is nonempty, the rounded mean map has only
finitely many fixed points in each compact positive interval. -/
lemma finite_roundedMeanMap_fixedPoints_Icc
    {A ρ a b : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hne : (roundedPositiveDriftSet A ρ).Nonempty) (ha : 0 < a) :
    {u : ℝ | u ∈ Set.Icc a b ∧ roundedMeanMap A ρ u = u}.Finite := by
  obtain ⟨h, hh⟩ := hne
  let f : ℝ → ℝ := fun u => roundedMeanMap A ρ u - u
  have hfAnalytic : AnalyticOnNhd ℝ f (Set.Ioi 0) := by
    intro u hu
    exact (analyticAt_roundedMeanMap hA hρ hu).sub (by fun_prop)
  have hfh : f h ≠ 0 := by
    dsimp only [f]
    linarith [hh.2]
  have hcodiscrete :
      f ⁻¹' ({0} : Set ℝ)ᶜ ∈ Filter.codiscreteWithin (Set.Ioi 0) :=
    hfAnalytic.preimage_zero_mem_codiscreteWithin
      hfh hh.1.1 isConnected_Ioi
  have hIccSub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro u hu
    exact ha.trans_le hu.1
  have hcodiscreteIcc :
      f ⁻¹' ({0} : Set ℝ)ᶜ ∈ Filter.codiscreteWithin (Set.Icc a b) :=
    (Filter.codiscreteWithin_mono hIccSub) hcodiscrete
  have hdiscrete :
      IsDiscrete ((f ⁻¹' ({0} : Set ℝ)) ∩ Set.Icc a b) := by
    apply isDiscrete_of_codiscreteWithin
    simpa only [Set.preimage_compl] using hcodiscreteIcc
  have hfContinuous : Continuous f :=
    (continuous_roundedMeanMap hA hρ hρ_lt).sub continuous_id
  have hcompact :
      IsCompact ((f ⁻¹' ({0} : Set ℝ)) ∩ Set.Icc a b) :=
    isCompact_Icc.inter_left (isClosed_singleton.preimage hfContinuous)
  have hset :
      (f ⁻¹' ({0} : Set ℝ)) ∩ Set.Icc a b =
        {u : ℝ | u ∈ Set.Icc a b ∧ roundedMeanMap A ρ u = u} := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_setOf_eq, f, sub_eq_zero, and_comm]
  rw [← hset]
  exact hcompact.finite hdiscrete

/-- The set of upper endpoints of positive-drift components is finite. -/
lemma finite_roundedPositiveDriftUpperEndpoints
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hne : (roundedPositiveDriftSet A ρ).Nonempty) :
    (roundedPositiveDriftUpperEndpoints A ρ).Finite := by
  obtain ⟨a, ha, haExclude⟩ :=
    exists_pos_not_mem_roundedPositiveDriftSet_near_zero hA hρ hρ_lt
  refine (finite_roundedMeanMap_fixedPoints_Icc
    (b := roundedRadiusBound ρ) hA hρ hρ_lt hne ha).subset ?_
  intro u hu
  rcases hu with ⟨h, hh, rfl⟩
  have hends :=
    roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  have hinterval :=
    roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh
  have hhInterval :
      h ∈ Set.Ioo
        (sInf (roundedPositiveDriftComponent A ρ h))
        (sSup (roundedPositiveDriftComponent A ρ h)) := by
    rw [← hinterval]
    exact mem_connectedComponentIn hh
  have hah : a < h := by
    by_contra hnot
    exact (haExclude h hh.1.1 (le_of_not_gt hnot)) hh
  exact ⟨⟨(hah.trans hhInterval.2).le, hends.2.2.le⟩,
    (roundedPositiveDriftComponent_endpoints_fixed hA hρ hρ_lt hh).2⟩

/-- A nonempty positive-drift set has a rightmost component. -/
lemma exists_isRightmostRoundedPositiveDriftComponent
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hne : (roundedPositiveDriftSet A ρ).Nonempty) :
    ∃ h ∈ roundedPositiveDriftSet A ρ,
      IsRightmostRoundedPositiveDriftComponent A ρ h := by
  let E := roundedPositiveDriftUpperEndpoints A ρ
  have hEFinite : E.Finite :=
    finite_roundedPositiveDriftUpperEndpoints hA hρ hρ_lt hne
  have hENonempty : E.Nonempty := by
    obtain ⟨h, hh⟩ := hne
    exact ⟨sSup (roundedPositiveDriftComponent A ρ h), h, hh, rfl⟩
  have hmaxMem : sSup E ∈ E :=
    hENonempty.csSup_mem hEFinite
  obtain ⟨h, hh, hmax⟩ := hmaxMem
  refine ⟨h, hh, ?_⟩
  intro u hu
  have huInterval :
      u ∈ Set.Ioo
        (sInf (roundedPositiveDriftComponent A ρ u))
        (sSup (roundedPositiveDriftComponent A ρ u)) := by
    rw [← roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hu]
    exact mem_connectedComponentIn hu
  have huEndpoint :
      sSup (roundedPositiveDriftComponent A ρ u) ∈ E :=
    ⟨u, hu, rfl⟩
  have huMax :
      sSup (roundedPositiveDriftComponent A ρ u) ≤ sSup E :=
    le_csSup hEFinite.bddAbove huEndpoint
  exact (huInterval.2.le.trans huMax).trans_eq hmax

/-- The positive-drift region has only finitely many connected components. -/
lemma finite_roundedPositiveDriftComponents
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hne : (roundedPositiveDriftSet A ρ).Nonempty) :
    (roundedPositiveDriftComponents A ρ).Finite := by
  have hinj :
      Set.InjOn sSup (roundedPositiveDriftComponents A ρ) := by
    intro C₁ hC₁ C₂ hC₂ hsup
    rcases hC₁ with ⟨h₁, hh₁, rfl⟩
    rcases hC₂ with ⟨h₂, hh₂, rfl⟩
    let C₁ := roundedPositiveDriftComponent A ρ h₁
    let C₂ := roundedPositiveDriftComponent A ρ h₂
    let lower := max (sInf C₁) (sInf C₂)
    let upper := sSup C₁
    have hends₁ :=
      roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh₁
    have hends₂ :=
      roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh₂
    have hlowerUpper : lower < upper := by
      apply max_lt
      · exact hends₁.2.1
      · dsimp only [upper, C₁, C₂] at hsup ⊢
        rw [hsup]
        exact hends₂.2.1
    let x := (lower + upper) / 2
    have hlowerX : lower < x := by
      dsimp only [x]
      linarith
    have hxUpper : x < upper := by
      dsimp only [x]
      linarith
    have hxC₁ : x ∈ C₁ := by
      change x ∈ roundedPositiveDriftComponent A ρ h₁
      rw [roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh₁]
      exact ⟨(le_max_left _ _).trans_lt hlowerX, hxUpper⟩
    have hxC₂ : x ∈ C₂ := by
      change x ∈ roundedPositiveDriftComponent A ρ h₂
      rw [roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh₂]
      constructor
      · exact (le_max_right _ _).trans_lt hlowerX
      · dsimp only [upper, C₁, C₂] at hsup hxUpper ⊢
        rwa [← hsup]
    exact (connectedComponentIn_eq hxC₁).trans
      (connectedComponentIn_eq hxC₂).symm
  have himage :
      sSup '' roundedPositiveDriftComponents A ρ =
        roundedPositiveDriftUpperEndpoints A ρ := by
    ext u
    constructor
    · rintro ⟨C, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨h, hh, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨roundedPositiveDriftComponent A ρ h, ⟨h, hh, rfl⟩, rfl⟩
  refine Set.Finite.of_finite_image (f := sSup) ?_ hinj
  rw [himage]
  exact finite_roundedPositiveDriftUpperEndpoints hA hρ hρ_lt hne

/-- Analyticity of the rounded mean map at the upper endpoint of a
positive-drift component makes that endpoint an isolated fixed point. The
locally-identically-fixed alternative is excluded by the positive drift
arbitrarily close on the left. -/
lemma roundedPositiveDriftComponent_upper_isolated_of_analyticAt
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hanalytic :
      AnalyticAt ℝ (roundedMeanMap A ρ)
        (sSup (roundedPositiveDriftComponent A ρ h))) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u : ℝ,
        0 < |u - sSup (roundedPositiveDriftComponent A ρ h)| →
        |u - sSup (roundedPositiveDriftComponent A ρ h)| < δ →
        roundedMeanMap A ρ u ≠ u := by
  let C := roundedPositiveDriftComponent A ρ h
  let lower := sInf C
  let upper := sSup C
  have hlowerUpper :
      lower < upper :=
    (roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh).2.1
  have hinterval : C = Set.Ioo lower upper :=
    roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh
  have hanalyticDrift :
      AnalyticAt ℝ (fun u : ℝ => roundedMeanMap A ρ u - u) upper := by
    exact hanalytic.sub (by fun_prop)
  rcases hanalyticDrift.eventually_eq_zero_or_eventually_ne_zero with
      hzero | hne
  · obtain ⟨r, hr, hzero⟩ := Metric.eventually_nhds_iff.mp hzero
    let η := min (r / 2) ((upper - lower) / 2)
    have hη : 0 < η :=
      lt_min (half_pos hr) (half_pos (sub_pos.mpr hlowerUpper))
    have hη_lt_r : η < r :=
      (min_le_left _ _).trans_lt (half_lt_self hr)
    let x := upper - η
    have hxInterval : x ∈ Set.Ioo lower upper := by
      constructor
      · have hη_le : η ≤ (upper - lower) / 2 := min_le_right _ _
        dsimp only [x]
        linarith
      · dsimp only [x]
        linarith
    have hxC : x ∈ C := by
      rw [hinterval]
      exact hxInterval
    have hxpos : x < roundedMeanMap A ρ x :=
      (roundedPositiveDriftComponent_subset A ρ h hxC).2
    have hxdist : dist x upper < r := by
      rw [Real.dist_eq]
      dsimp only [x]
      rw [show upper - η - upper = -η by ring, abs_neg, abs_of_pos hη]
      exact hη_lt_r
    have hxzero : roundedMeanMap A ρ x - x = 0 := hzero hxdist
    linarith
  · have hne' :
        ∀ᶠ u in 𝓝 upper,
          u ∈ ({upper}ᶜ : Set ℝ) →
            roundedMeanMap A ρ u - u ≠ 0 :=
      eventually_nhdsWithin_iff.mp hne
    obtain ⟨δ, hδ, hneBall⟩ := Metric.eventually_nhds_iff.mp hne'
    refine ⟨δ, hδ, ?_⟩
    intro u huPos huLt huEq
    have huDist : dist u upper < δ := by
      rwa [Real.dist_eq]
    have huNe : u ≠ upper :=
      sub_ne_zero.mp (abs_pos.mp huPos)
    exact hneBall huDist (by simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using huNe) (sub_eq_zero.mpr huEq)

/-- The upper fixed point of every positive-drift component is isolated. -/
lemma roundedPositiveDriftComponent_upper_isolated
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u : ℝ,
        0 < |u - sSup (roundedPositiveDriftComponent A ρ h)| →
        |u - sSup (roundedPositiveDriftComponent A ρ h)| < δ →
        roundedMeanMap A ρ u ≠ u := by
  apply roundedPositiveDriftComponent_upper_isolated_of_analyticAt
    hA hρ hρ_lt hh
  have hends :=
    roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  exact analyticAt_roundedMeanMap hA hρ (hends.1.trans hends.2.1)

/-- The right-stability conclusion for a positive-drift component follows
from isolatedness of its upper fixed point together with negative-drift
witnesses arbitrarily close on the right. The latter hypothesis is the
sign-crossing input not supplied by isolatedness alone. -/
lemma roundedPositiveDriftComponent_right_stable_of_isolated_of_right_negative
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hisolated :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ u : ℝ,
          0 < |u - sSup (roundedPositiveDriftComponent A ρ h)| →
          |u - sSup (roundedPositiveDriftComponent A ρ h)| < δ →
          roundedMeanMap A ρ u ≠ u)
    (hrightNegative :
      ∀ ε : ℝ, 0 < ε →
        ∃ u ∈ Set.Ioo
          (sSup (roundedPositiveDriftComponent A ρ h))
          (sSup (roundedPositiveDriftComponent A ρ h) + ε),
          roundedMeanMap A ρ u < u) :
    let C := roundedPositiveDriftComponent A ρ h
    ∃ η₀ : ℝ, 0 < η₀ ∧
      sInf C < sSup C - η₀ ∧
      sSup C + η₀ < roundedRadiusBound ρ ∧
      ∀ u ∈ Set.Ioc (sSup C) (sSup C + η₀),
        roundedMeanMap A ρ u < u := by
  dsimp only
  let C := roundedPositiveDriftComponent A ρ h
  let lower := sInf C
  let upper := sSup C
  let M := roundedRadiusBound ρ
  have hends := roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  have hlowerUpper : lower < upper := hends.2.1
  have hupperM : upper < M := hends.2.2
  obtain ⟨δ, hδ, hisolated⟩ := hisolated
  let ε := min δ (min ((upper - lower) / 2) ((M - upper) / 2))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min hδ (lt_min (half_pos (sub_pos.mpr hlowerUpper))
      (half_pos (sub_pos.mpr hupperM)))
  obtain ⟨y, hy, hyneg⟩ := hrightNegative ε hε
  let η₀ := y - upper
  have hη₀ : 0 < η₀ := sub_pos.mpr hy.1
  have hη₀_lt_ε : η₀ < ε := by
    dsimp only [η₀]
    linarith [hy.2]
  have hε_le_lower : ε ≤ (upper - lower) / 2 :=
    (min_le_right δ _).trans (min_le_left _ _)
  have hε_le_upper : ε ≤ (M - upper) / 2 :=
    (min_le_right δ _).trans (min_le_right _ _)
  have hleft : lower < upper - η₀ := by
    linarith
  have hyM : y < M := by
    dsimp only [η₀] at hη₀_lt_ε
    linarith
  have hne :
      ∀ u ∈ Set.Ioc upper y, roundedMeanMap A ρ u ≠ u := by
    intro u hu
    apply hisolated u
    · rw [abs_of_pos (sub_pos.mpr hu.1)]
      exact sub_pos.mpr hu.1
    · rw [abs_of_pos (sub_pos.mpr hu.1)]
      have huy : u - upper ≤ y - upper := sub_le_sub_right hu.2 upper
      exact huy.trans_lt (hη₀_lt_ε.trans_le (min_le_left _ _))
  have hsign :
      ∀ u ∈ Set.Ioc upper y, roundedMeanMap A ρ u < u :=
    lt_self_on_Ioc_of_continuousOn_of_ne_fixed
      (continuous_roundedMeanMap hA hρ hρ_lt).continuousOn hyneg hne
  refine ⟨η₀, hη₀, hleft, ?_, ?_⟩
  · dsimp only [η₀]
    linarith
  · intro u hu
    apply hsign u
    change u ∈ Set.Ioc upper (upper + η₀) at hu
    refine ⟨hu.1, ?_⟩
    dsimp only [η₀] at hu
    linarith [hu.2]

/-- Repaired right-stability statement: the upper fixed point is automatically
isolated, so the only additional input is negative drift arbitrarily close on
its right. -/
lemma roundedPositiveDriftComponent_right_stable_of_right_negative
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hrightNegative :
      ∀ ε : ℝ, 0 < ε →
        ∃ u ∈ Set.Ioo
          (sSup (roundedPositiveDriftComponent A ρ h))
          (sSup (roundedPositiveDriftComponent A ρ h) + ε),
          roundedMeanMap A ρ u < u) :
    let C := roundedPositiveDriftComponent A ρ h
    ∃ η₀ : ℝ, 0 < η₀ ∧
      sInf C < sSup C - η₀ ∧
      sSup C + η₀ < roundedRadiusBound ρ ∧
      ∀ u ∈ Set.Ioc (sSup C) (sSup C + η₀),
        roundedMeanMap A ρ u < u :=
  roundedPositiveDriftComponent_right_stable_of_isolated_of_right_negative
    hA hρ hρ_lt hh
      (roundedPositiveDriftComponent_upper_isolated hA hρ hρ_lt hh)
      hrightNegative

/-- Rightmostness supplies negative-drift witnesses arbitrarily close to the
right of the isolated upper fixed point. -/
lemma roundedPositiveDriftComponent_right_negative_of_rightmost
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hrightmost : IsRightmostRoundedPositiveDriftComponent A ρ h) :
    ∀ ε : ℝ, 0 < ε →
      ∃ u ∈ Set.Ioo
        (sSup (roundedPositiveDriftComponent A ρ h))
        (sSup (roundedPositiveDriftComponent A ρ h) + ε),
        roundedMeanMap A ρ u < u := by
  let C := roundedPositiveDriftComponent A ρ h
  let upper := sSup C
  let M := roundedRadiusBound ρ
  have hends := roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  have hupperPos : 0 < upper := hends.1.trans hends.2.1
  have hupperM : upper < M := hends.2.2
  obtain ⟨δ, hδ, hisolated⟩ :=
    roundedPositiveDriftComponent_upper_isolated hA hρ hρ_lt hh
  intro ε hε
  let η := min ε (min δ (M - upper)) / 2
  have hmin : 0 < min ε (min δ (M - upper)) :=
    lt_min hε (lt_min hδ (sub_pos.mpr hupperM))
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  have hη_lt_min : η < min ε (min δ (M - upper)) := by
    dsimp only [η]
    linarith
  have hη_lt_ε : η < ε :=
    hη_lt_min.trans_le (min_le_left _ _)
  have hη_lt_δ : η < δ :=
    hη_lt_min.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hη_lt_M : η < M - upper :=
    hη_lt_min.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let u := upper + η
  have huUpper : upper < u := by
    dsimp only [u]
    linarith
  have huEpsilon : u < upper + ε := by
    dsimp only [u]
    linarith
  have huM : u < M := by
    dsimp only [u]
    linarith
  have huNe :
      roundedMeanMap A ρ u ≠ u := by
    apply hisolated u
    · rw [show u - upper = η by dsimp only [u]; ring, abs_of_pos hη]
      exact hη
    · rw [show u - upper = η by dsimp only [u]; ring, abs_of_pos hη]
      exact hη_lt_δ
  have huNotPos : u ∉ roundedPositiveDriftSet A ρ := by
    intro hu
    exact (not_lt_of_ge (hrightmost u hu)) huUpper
  have huNotLt : ¬u < roundedMeanMap A ρ u := by
    intro huLt
    apply huNotPos
    exact ⟨⟨hupperPos.trans huUpper, huM⟩, huLt⟩
  exact ⟨u, ⟨huUpper, huEpsilon⟩,
    lt_of_le_of_ne (le_of_not_gt huNotLt) huNe⟩

/-- The repaired paper statement: the upper endpoint of the rightmost
positive-drift component is stable from the right. -/
lemma roundedPositiveDriftComponent_right_stable_of_rightmost
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hrightmost : IsRightmostRoundedPositiveDriftComponent A ρ h) :
    let C := roundedPositiveDriftComponent A ρ h
    ∃ η₀ : ℝ, 0 < η₀ ∧
      sInf C < sSup C - η₀ ∧
      sSup C + η₀ < roundedRadiusBound ρ ∧
      ∀ u ∈ Set.Ioc (sSup C) (sSup C + η₀),
        roundedMeanMap A ρ u < u :=
  roundedPositiveDriftComponent_right_stable_of_right_negative
    hA hρ hρ_lt hh
      (roundedPositiveDriftComponent_right_negative_of_rightmost
        hA hρ hρ_lt hh hrightmost)

/-- Under the repaired sign-crossing hypothesis, the rounded mean map points
strictly toward the upper endpoint on both sides of the metastable well. -/
lemma exists_roundedPositiveDriftComponent_inward_bounds
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hrightNegative :
      ∀ ε : ℝ, 0 < ε →
        ∃ u ∈ Set.Ioo
          (sSup (roundedPositiveDriftComponent A ρ h))
          (sSup (roundedPositiveDriftComponent A ρ h) + ε),
          roundedMeanMap A ρ u < u) :
    let C := roundedPositiveDriftComponent A ρ h
    ∃ η₀ : ℝ, 0 < η₀ ∧
      sInf C < sSup C - η₀ ∧
      sSup C + η₀ < roundedRadiusBound ρ ∧
      (∀ u ∈ Set.Ioo (sInf C) (sSup C),
        u < roundedMeanMap A ρ u ∧
          roundedMeanMap A ρ u ≤ sSup C) ∧
      ∀ u ∈ Set.Ioc (sSup C) (sSup C + η₀),
        sSup C ≤ roundedMeanMap A ρ u ∧
          roundedMeanMap A ρ u < u := by
  dsimp only
  let C := roundedPositiveDriftComponent A ρ h
  let lower := sInf C
  let upper := sSup C
  obtain ⟨η₀, hη₀, hleft, hright, hneg⟩ :=
    roundedPositiveDriftComponent_right_stable_of_right_negative
      hA hρ hρ_lt hh hrightNegative
  have hends :=
    roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  have hlowerPos : 0 < lower := hends.1
  have hupperPos : 0 < upper := hlowerPos.trans hends.2.1
  have hupperFixed :
      roundedMeanMap A ρ upper = upper :=
    (roundedPositiveDriftComponent_endpoints_fixed hA hρ hρ_lt hh).2
  have hinterval : C = Set.Ioo lower upper :=
    roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh
  have hmono :=
    monotoneOn_roundedMeanMap_Ici hA hρ
  refine ⟨η₀, hη₀, hleft, hright, ?_, ?_⟩
  · intro u hu
    have huC : u ∈ C := by
      rw [hinterval]
      exact hu
    have hudrift :
        u < roundedMeanMap A ρ u :=
      (roundedPositiveDriftComponent_subset A ρ h huC).2
    have huUpper :
        roundedMeanMap A ρ u ≤ roundedMeanMap A ρ upper :=
      hmono (hlowerPos.trans hu.1).le hupperPos.le hu.2.le
    exact ⟨hudrift, by rwa [hupperFixed] at huUpper⟩
  · intro u hu
    have hupperLe :
        roundedMeanMap A ρ upper ≤ roundedMeanMap A ρ u :=
      hmono hupperPos.le (hupperPos.trans hu.1).le hu.1.le
    exact ⟨by rwa [hupperFixed] at hupperLe, hneg u hu⟩

/-- Every deterministic rounded-mean-map orbit started in a positive-drift
component, including its upper endpoint, converges to that upper endpoint. -/
theorem roundedPositiveDriftComponent_orbit_tendsto_upper
    {A ρ h q : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hq : q ∈ Set.Ioc
      (sInf (roundedPositiveDriftComponent A ρ h))
      (sSup (roundedPositiveDriftComponent A ρ h))) :
    Tendsto
      (fun t => (roundedMeanMap A ρ)^[t] q) atTop
      (𝓝 (sSup (roundedPositiveDriftComponent A ρ h))) := by
  let C := roundedPositiveDriftComponent A ρ h
  let lower := sInf C
  let upper := sSup C
  let V := roundedMeanMap A ρ
  let u : ℕ → ℝ := fun t => V^[t] q
  have hends :=
    roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  have hlowerPos : 0 < lower := hends.1
  have hlowerUpper : lower < upper := hends.2.1
  have hupperPos : 0 < upper := hlowerPos.trans hlowerUpper
  have hupperFixed : V upper = upper :=
    (roundedPositiveDriftComponent_endpoints_fixed hA hρ hρ_lt hh).2
  have hinterval : C = Set.Ioo lower upper :=
    roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh
  have hmonoV :=
    monotoneOn_roundedMeanMap_Ici hA hρ
  have hstep {x : ℝ} (hx : x ∈ Set.Ioo lower upper) :
      x < V x ∧ V x ≤ upper := by
    have hxC : x ∈ C := by
      rw [hinterval]
      exact hx
    have hxdrift : x < V x :=
      (roundedPositiveDriftComponent_subset A ρ h hxC).2
    have hxupper : V x ≤ V upper :=
      hmonoV (hlowerPos.trans hx.1).le hupperPos.le hx.2.le
    exact ⟨hxdrift, by rwa [hupperFixed] at hxupper⟩
  have hinv : ∀ t, lower < u t ∧ u t ≤ upper := by
    intro t
    induction t with
    | zero =>
        constructor
        · simpa only [u, Function.iterate_zero_apply, lower, C] using hq.1
        · simpa only [u, Function.iterate_zero_apply, upper, C] using hq.2
    | succ n ih =>
        have hsucc : u (n + 1) = V (u n) :=
          Function.iterate_succ_apply' V n q
        rcases lt_or_eq_of_le ih.2 with hnlt | hneq
        · have hnstep := hstep ⟨ih.1, hnlt⟩
          rw [hsucc]
          exact ⟨ih.1.trans hnstep.1, hnstep.2⟩
        · rw [hsucc, hneq, hupperFixed]
          exact ⟨hlowerUpper, le_rfl⟩
  have hmono : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    have hsucc : u (n + 1) = V (u n) :=
      Function.iterate_succ_apply' V n q
    rcases lt_or_eq_of_le (hinv n).2 with hnlt | hneq
    · have hnstep := hstep ⟨(hinv n).1, hnlt⟩
      rw [hsucc]
      exact hnstep.1.le
    · rw [hsucc, hneq, hupperFixed]
  have hbdd : BddAbove (Set.range u) :=
    ⟨upper, by rintro _ ⟨t, rfl⟩; exact (hinv t).2⟩
  have htends :
      Tendsto u atTop (𝓝 (⨆ t, u t)) :=
    tendsto_atTop_ciSup hmono hbdd
  have hlimitFixed : V (⨆ t, u t) = ⨆ t, u t :=
    isFixedPt_of_tendsto_iterate htends
      (continuous_roundedMeanMap hA hρ hρ_lt).continuousAt
  have hu0 : u 0 = q := by simp only [u, Function.iterate_zero_apply]
  have hqLimit : q ≤ ⨆ t, u t := by
    rw [← hu0]
    exact le_ciSup hbdd 0
  have hlowerLimit : lower < ⨆ t, u t :=
    hq.1.trans_le hqLimit
  have hlimitUpper : (⨆ t, u t) ≤ upper :=
    ciSup_le fun t => (hinv t).2
  have hlimitEq : (⨆ t, u t) = upper := by
    apply le_antisymm hlimitUpper
    by_contra hnot
    have hlimitLt : (⨆ t, u t) < upper := lt_of_not_ge hnot
    have hlimitC : (⨆ t, u t) ∈ C := by
      rw [hinterval]
      exact ⟨hlowerLimit, hlimitLt⟩
    have hlimitDrift :
        (⨆ t, u t) < V (⨆ t, u t) :=
      (roundedPositiveDriftComponent_subset A ρ h hlimitC).2
    rw [hlimitFixed] at hlimitDrift
    exact (lt_irrefl _ hlimitDrift).elim
  change Tendsto u atTop (𝓝 upper)
  rw [← hlimitEq]
  exact htends

/-- Deterministic rounded-mean-map orbits enter every neighborhood of a
positive-drift component's upper endpoint uniformly over compact subsets of
the component together with its upper endpoint. -/
theorem exists_uniform_roundedPositiveDriftComponent_orbit_mem_Icc
    {A ρ h δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ) (hδ : 0 < δ)
    (B : Set ℝ) (hBCompact : IsCompact B)
    (hBSub : B ⊆ Set.Ioc
      (sInf (roundedPositiveDriftComponent A ρ h))
      (sSup (roundedPositiveDriftComponent A ρ h))) :
    ∃ T : ℕ, ∀ q ∈ B,
      (roundedMeanMap A ρ)^[T] q ∈ Set.Icc
        (sSup (roundedPositiveDriftComponent A ρ h) - δ)
        (sSup (roundedPositiveDriftComponent A ρ h) + δ) := by
  let C := roundedPositiveDriftComponent A ρ h
  let lower := sInf C
  let upper := sSup C
  let V := roundedMeanMap A ρ
  by_cases hBNonempty : B.Nonempty
  · obtain ⟨q₀, hq₀B, hq₀Least⟩ :=
      hBCompact.exists_isLeast hBNonempty
    have hq₀Interval : q₀ ∈ Set.Ioc lower upper :=
      hBSub hq₀B
    have htend :
        Tendsto (fun t => V^[t] q₀) atTop (𝓝 upper) :=
      roundedPositiveDriftComponent_orbit_tendsto_upper
        hA hρ hρ_lt hh hq₀Interval
    have hevent :
        {x : ℝ | upper - δ < x} ∈ 𝓝 upper :=
      Ioi_mem_nhds (sub_lt_self upper hδ)
    obtain ⟨T, hT⟩ :=
      mem_atTop_sets.mp (htend.eventually hevent)
    refine ⟨T, ?_⟩
    intro q hqB
    have hq₀q : q₀ ≤ q :=
      hq₀Least hqB
    have hqUpper : q ≤ upper :=
      (hBSub hqB).2
    have hmonoV : Monotone V :=
      monotone_roundedMeanMap hA hρ
    have hlower :
        upper - δ ≤ V^[T] q := by
      exact (hT T le_rfl).le.trans (hmonoV.iterate T hq₀q)
    have hupperFixed : V upper = upper :=
      (roundedPositiveDriftComponent_endpoints_fixed hA hρ hρ_lt hh).2
    have hupper :
        V^[T] q ≤ upper + δ := by
      calc
        V^[T] q ≤ V^[T] upper := hmonoV.iterate T hqUpper
        _ = upper := Function.iterate_fixed hupperFixed T
        _ ≤ upper + δ := by linarith
    exact ⟨hlower, hupper⟩
  · refine ⟨0, ?_⟩
    intro q hqB
    exact (hBNonempty ⟨q, hqB⟩).elim

/-- On the nonnegative state space the rounded mean map remains below the
maximal rounded-coordinate value. -/
lemma roundedMeanMap_le_roundedRadiusBound_of_nonneg
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : 0 ≤ h) :
    roundedMeanMap A ρ h ≤ roundedRadiusBound ρ := by
  rcases eq_or_lt_of_le hh with rfl | hh
  · rw [roundedMeanMap_of_nonpos A ρ le_rfl]
    exact roundedRadiusBound_nonneg ρ
  · exact (roundedMeanMap_lt_roundedRadiusBound hA hρ hρ_lt hh).le

/-- The exact compact rounded-radius interval is invariant under the
deterministic rounded mean map. -/
lemma roundedMeanMap_mem_roundedRadiusBound_Icc
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ Set.Icc 0 (roundedRadiusBound ρ)) :
    roundedMeanMap A ρ h ∈ Set.Icc 0 (roundedRadiusBound ρ) :=
  ⟨roundedMeanMap_nonneg A ρ h,
    roundedMeanMap_le_roundedRadiusBound_of_nonneg
      hA hρ hρ_lt hh.1⟩

/-- Every deterministic rounded-mean-map iterate started in the exact compact
state interval remains there. -/
lemma iterate_roundedMeanMap_mem_roundedRadiusBound_Icc
    {A ρ q : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hq : q ∈ Set.Icc 0 (roundedRadiusBound ρ)) :
    ∀ s : ℕ,
      (roundedMeanMap A ρ)^[s] q ∈
        Set.Icc 0 (roundedRadiusBound ρ) := by
  intro s
  induction s with
  | zero =>
      simpa only [Function.iterate_zero_apply] using hq
  | succ s ih =>
      rw [Function.iterate_succ_apply']
      exact
        roundedMeanMap_mem_roundedRadiusBound_Icc
          hA hρ hρ_lt ih

/-- Through every fixed finite horizon, all coordinates of a canonical
rounded-radius path started in `[0, Mρ]` remain in that interval almost
surely. -/
lemma markovPathMeasure_dirac_ae_forall_le_mem_roundedRadiusBound_Icc
    {A ρ q : ℝ} {N : ℕ}
    (hq : q ∈ Set.Icc 0 (roundedRadiusBound ρ))
    (hρ : 0 < ρ) (hN : 0 < N) (T : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)),
      ∀ s ≤ T, ω s ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
  have hfin :
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)),
        ∀ s ∈ Finset.range (T + 1),
          ω s ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
    rw [Filter.eventually_all_finset]
    intro s _hs
    exact
      markovPathMeasure_dirac_ae_eval_mem_roundedRadiusBound_Icc
        hq hρ hN s
  filter_upwards [hfin] with ω hω
  intro s hsT
  exact hω s (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hsT))

/-- Values attained by the oscillation of the rounded mean map over pairs in
the compact state interval at separation at most `|r|`. -/
def roundedMeanMapOscillationSet (A ρ r : ℝ) : Set ℝ :=
  {d | ∃ u ∈ Set.Icc 0 (roundedRadiusBound ρ),
    ∃ v ∈ Set.Icc 0 (roundedRadiusBound ρ),
      |u - v| ≤ |r| ∧
        d = |roundedMeanMap A ρ u - roundedMeanMap A ρ v|}

/-- Paper's compact-interval modulus of continuity for the rounded mean map. -/
noncomputable def roundedMeanMapModulus (A ρ r : ℝ) : ℝ :=
  sSup (roundedMeanMapOscillationSet A ρ r)

/-- Zero belongs to the oscillation set, using the pair `(0,0)`. -/
lemma zero_mem_roundedMeanMapOscillationSet (A ρ r : ℝ) :
    0 ∈ roundedMeanMapOscillationSet A ρ r := by
  refine ⟨0, ⟨le_rfl, roundedRadiusBound_nonneg ρ⟩,
    0, ⟨le_rfl, roundedRadiusBound_nonneg ρ⟩, ?_, ?_⟩
  · simp
  · simp

/-- The compact-interval oscillation set is nonempty. -/
lemma roundedMeanMapOscillationSet_nonempty (A ρ r : ℝ) :
    (roundedMeanMapOscillationSet A ρ r).Nonempty :=
  ⟨0, zero_mem_roundedMeanMapOscillationSet A ρ r⟩

/-- The state-space bound also bounds every compact-interval oscillation. -/
lemma roundedMeanMapOscillationSet_bddAbove
    {A ρ r : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    BddAbove (roundedMeanMapOscillationSet A ρ r) := by
  refine ⟨roundedRadiusBound ρ, ?_⟩
  intro d hd
  rcases hd with ⟨u, hu, v, hv, _huv, rfl⟩
  have hu0 := roundedMeanMap_nonneg A ρ u
  have hv0 := roundedMeanMap_nonneg A ρ v
  have huM :=
    roundedMeanMap_le_roundedRadiusBound_of_nonneg hA hρ hρ_lt hu.1
  have hvM :=
    roundedMeanMap_le_roundedRadiusBound_of_nonneg hA hρ hρ_lt hv.1
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The rounded mean-map modulus is nonnegative. -/
lemma roundedMeanMapModulus_nonneg
    {A ρ r : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 ≤ roundedMeanMapModulus A ρ r := by
  apply le_csSup (roundedMeanMapOscillationSet_bddAbove hA hρ hρ_lt)
  exact zero_mem_roundedMeanMapOscillationSet A ρ r

/-- The supremum modulus bounds the rounded mean-map oscillation for every
pair of states in the compact interval. -/
lemma abs_roundedMeanMap_sub_le_roundedMeanMapModulus
    {A ρ u v : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hu : u ∈ Set.Icc 0 (roundedRadiusBound ρ))
    (hv : v ∈ Set.Icc 0 (roundedRadiusBound ρ)) :
    |roundedMeanMap A ρ u - roundedMeanMap A ρ v| ≤
      roundedMeanMapModulus A ρ (u - v) := by
  apply le_csSup (roundedMeanMapOscillationSet_bddAbove hA hρ hρ_lt)
  exact ⟨u, hu, v, hv, le_rfl, rfl⟩

/-- Uniform continuity on the compact rounded state interval makes the
paper's oscillation modulus vanish at zero. -/
lemma tendsto_roundedMeanMapModulus_zero
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    Tendsto (roundedMeanMapModulus A ρ) (𝓝 0) (𝓝 0) := by
  have huc :
      UniformContinuousOn (roundedMeanMap A ρ)
        (Set.Icc 0 (roundedRadiusBound ρ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (continuous_roundedMeanMap hA hρ hρ_lt).continuousOn
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨δ, hδ, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc)
      (ε / 2) (half_pos hε)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with r hr
  have hrabs : |r| < δ := by
    change dist r 0 < δ at hr
    simpa only [Real.dist_eq, sub_zero] using hr
  have hsup :
      roundedMeanMapModulus A ρ r ≤ ε / 2 := by
    apply csSup_le (roundedMeanMapOscillationSet_nonempty A ρ r)
    intro d hd
    rcases hd with ⟨u, hu, v, hv, huv, rfl⟩
    have huvδ : dist u v < δ := by
      rw [Real.dist_eq]
      exact huv.trans_lt hrabs
    exact (by
      simpa only [Real.dist_eq] using
        (hcontrol u hu v hv huvδ).le)
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (roundedMeanMapModulus_nonneg hA hρ hρ_lt)]
  exact hsup.trans_lt (half_lt_self hε)

/-- At every fixed horizon, one can choose a positive one-step tolerance
whose rounded deterministic error envelope is smaller than any prescribed
positive terminal error. -/
lemma exists_pos_finiteHorizonErrorEnvelope_roundedMeanMapModulus_lt
    {A ρ η : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hη : 0 < η) (T : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧
      finiteHorizonErrorEnvelope (roundedMeanMapModulus A ρ) δ T < η := by
  have htend :
      Tendsto
        (fun δ : ℝ =>
          finiteHorizonErrorEnvelope (roundedMeanMapModulus A ρ) δ T)
        (𝓝 0) (𝓝 0) :=
    tendsto_finiteHorizonErrorEnvelope_zero
      (tendsto_roundedMeanMapModulus_zero hA hρ hρ_lt) T
  have hevent :
      ∀ᶠ δ : ℝ in 𝓝 0,
        finiteHorizonErrorEnvelope
            (roundedMeanMapModulus A ρ) δ T ∈ Metric.ball 0 η :=
    htend.eventually (Metric.ball_mem_nhds 0 hη)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r / 2, half_pos hr, ?_⟩
  have hδball : r / 2 ∈ Metric.ball (0 : ℝ) r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero,
      abs_of_pos (half_pos hr)]
    linarith
  have hout := hball hδball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hout
  exact (le_abs_self _).trans_lt hout

/-- A path with uniformly small one-step errors tracks the rounded
deterministic orbit through every fixed horizon, with error controlled by the
paper's recursive compact-interval modulus envelope. -/
lemma abs_sub_iterate_roundedMeanMap_le_errorEnvelope
    {A ρ q δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ℕ → ℝ) (T : ℕ)
    (hx0 : x 0 = q)
    (hxmem : ∀ s ≤ T, x s ∈ Set.Icc 0 (roundedRadiusBound ρ))
    (hqmem : ∀ s ≤ T,
      (roundedMeanMap A ρ)^[s] q ∈ Set.Icc 0 (roundedRadiusBound ρ))
    (hnoise : ∀ s < T,
      |x (s + 1) - roundedMeanMap A ρ (x s)| ≤ δ) :
    ∀ s ≤ T,
      |x s - (roundedMeanMap A ρ)^[s] q| ≤
        finiteHorizonErrorEnvelope
          (roundedMeanMapModulus A ρ) δ s := by
  apply abs_sub_iterate_le_errorEnvelope
    (V := roundedMeanMap A ρ) (x := x) (q := q) (δ := δ)
    (ω := roundedMeanMapModulus A ρ)
    (E := finiteHorizonErrorEnvelope (roundedMeanMapModulus A ρ) δ)
    (T := T) hx0 (finiteHorizonErrorEnvelope_zero _ _)
    hnoise
  · intro s hsT hs
    have hsLe : s ≤ T := Nat.le_of_lt hsT
    have hEnonneg :
        0 ≤ finiteHorizonErrorEnvelope
          (roundedMeanMapModulus A ρ) δ s :=
      (abs_nonneg
        (x s - (roundedMeanMap A ρ)^[s] q)).trans hs
    apply le_csSup
      (roundedMeanMapOscillationSet_bddAbove hA hρ hρ_lt)
    exact ⟨x s, hxmem s hsLe,
      (roundedMeanMap A ρ)^[s] q, hqmem s hsLe,
      by simpa only [abs_of_nonneg hEnonneg] using hs, rfl⟩
  · intro s _hsT
    exact finiteHorizonErrorEnvelope_succ _ _ _

/-- Outside the finite-horizon bad-step event, every one-step perturbation is
small enough for the rounded pathwise tracking envelope to apply. -/
lemma abs_sub_iterate_roundedMeanMap_le_errorEnvelope_of_notMem
    {A ρ q δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (ω : ℕ → ℝ) (T : ℕ)
    (hgood : ω ∉ finiteHorizonStepDeviationEvent A ρ δ T)
    (hω0 : ω 0 = q)
    (hωmem : ∀ s ≤ T, ω s ∈ Set.Icc 0 (roundedRadiusBound ρ))
    (hqmem : ∀ s ≤ T,
      (roundedMeanMap A ρ)^[s] q ∈ Set.Icc 0 (roundedRadiusBound ρ)) :
    ∀ s ≤ T,
      |ω s - (roundedMeanMap A ρ)^[s] q| ≤
        finiteHorizonErrorEnvelope
          (roundedMeanMapModulus A ρ) δ s := by
  apply abs_sub_iterate_roundedMeanMap_le_errorEnvelope
    hA hρ hρ_lt ω T hω0 hωmem hqmem
  intro s hsT
  by_contra hnot
  have hlarge :
      δ < |ω (s + 1) - roundedMeanMap A ρ (ω s)| :=
    lt_of_not_ge hnot
  apply hgood
  simp only [finiteHorizonStepDeviationEvent, Set.mem_iUnion,
    Set.mem_setOf_eq]
  exact ⟨s, Finset.mem_range.mpr hsT, hlarge⟩

/-- Finite-horizon stochastic tracking: the terminal deviation from the
rounded deterministic orbit exceeds its recursive envelope only if some
one-step deviation exceeds the chosen tolerance. -/
lemma markovPathMeasure_measureReal_abs_sub_iterate_gt_errorEnvelope_le
    {A ρ q δ : ℝ} {N T : ℕ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hδ : 0 < δ)
    (hq : q ∈ Set.Icc 0 (roundedRadiusBound ρ)) :
    (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
        {ω : ℕ → ℝ |
          |ω T - (roundedMeanMap A ρ)^[T] q| >
            finiteHorizonErrorEnvelope
              (roundedMeanMapModulus A ρ) δ T} ≤
      2 * T * Real.exp
        (-2 * N * δ ^ 2 / roundedRadiusBound ρ ^ 2) := by
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
  let E : Set (ℕ → ℝ) :=
    {ω |
      |ω T - (roundedMeanMap A ρ)^[T] q| >
        finiteHorizonErrorEnvelope
          (roundedMeanMapModulus A ρ) δ T}
  let B : Set (ℕ → ℝ) :=
    finiteHorizonStepDeviationEvent A ρ δ T
  have hω0 :
      ∀ᵐ ω ∂μ, ω 0 = q := by
    exact
      markovPathMeasure_dirac_ae_eval_zero_eq
        q (Hkernel A ρ N)
  have hωmem :
      ∀ᵐ ω ∂μ,
        ∀ s ≤ T, ω s ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
    exact
      markovPathMeasure_dirac_ae_forall_le_mem_roundedRadiusBound_Icc
        hq hρ hN T
  have hqmem :
      ∀ s ≤ T,
        (roundedMeanMap A ρ)^[s] q ∈
          Set.Icc 0 (roundedRadiusBound ρ) :=
    fun s _hs =>
      iterate_roundedMeanMap_mem_roundedRadiusBound_Icc
        hA hρ hρ_lt hq s
  have hsubset : E ≤ᵐ[μ] B := by
    filter_upwards [hω0, hωmem] with ω hω0 hωmem
    intro hterminal
    by_contra hnotBad
    have htrack :=
      abs_sub_iterate_roundedMeanMap_le_errorEnvelope_of_notMem
        hA hρ hρ_lt ω T hnotBad hω0 hωmem hqmem T le_rfl
    exact (not_lt_of_ge htrack) hterminal
  have hreal : μ.real E ≤ μ.real B := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ B)
      (measure_mono_ae hsubset)
  exact hreal.trans
    (markovPathMeasure_measureReal_finiteHorizonStepDeviationEvent_le
      (q := q) hA hρ hρ_lt hN hδ)

/-- Uniform stochastic entrance near the upper endpoint of a positive-drift
component.  The deterministic orbit enters an `η / 4` neighborhood, while a
positive one-step tolerance makes the finite-horizon tracking envelope smaller
than `η / 4`; hence failure to enter the `η / 2` neighborhood forces a tracking
failure. -/
theorem exists_markovPathMeasure_measureReal_abs_sub_upper_gt_half_le
    {A ρ h η : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ) (hη : 0 < η)
    (B : Set ℝ) (hBCompact : IsCompact B)
    (hBSub : B ⊆ Set.Ioc
      (sInf (roundedPositiveDriftComponent A ρ h))
      (sSup (roundedPositiveDriftComponent A ρ h))) :
    ∃ T : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ q ∈ B,
        (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
            {ω : ℕ → ℝ |
              |ω T - sSup (roundedPositiveDriftComponent A ρ h)| >
                η / 2} ≤
          2 * T * Real.exp
            (-2 * N * δ ^ 2 / roundedRadiusBound ρ ^ 2) := by
  obtain ⟨T, hT⟩ :=
    exists_uniform_roundedPositiveDriftComponent_orbit_mem_Icc
      hA hρ hρ_lt hh (by positivity : 0 < η / 4) B hBCompact hBSub
  obtain ⟨δ, hδ, hEnvelope⟩ :=
    exists_pos_finiteHorizonErrorEnvelope_roundedMeanMapModulus_lt
      hA hρ hρ_lt (by positivity : 0 < η / 4) T
  refine ⟨T, δ, hδ, ?_⟩
  intro N hN q hqB
  have hends :=
    roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
  have hqInterval := hBSub hqB
  have hq :
      q ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
    constructor
    · exact (hends.1.trans hqInterval.1).le
    · exact hqInterval.2.trans hends.2.2.le
  have hdet := hT q hqB
  have hdetAbs :
      |(roundedMeanMap A ρ)^[T] q -
          sSup (roundedPositiveDriftComponent A ρ h)| ≤ η / 4 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hdet.1, hdet.2]
  have hsubset :
      {ω : ℕ → ℝ |
          |ω T - sSup (roundedPositiveDriftComponent A ρ h)| > η / 2} ⊆
        {ω : ℕ → ℝ |
          |ω T - (roundedMeanMap A ρ)^[T] q| >
            finiteHorizonErrorEnvelope
              (roundedMeanMapModulus A ρ) δ T} := by
    intro ω hterminal
    by_contra hnotTrack
    have htrack :
        |ω T - (roundedMeanMap A ρ)^[T] q| ≤
          finiteHorizonErrorEnvelope
            (roundedMeanMapModulus A ρ) δ T :=
      le_of_not_gt hnotTrack
    have htrackLt :
        |ω T - (roundedMeanMap A ρ)^[T] q| < η / 4 :=
      htrack.trans_lt hEnvelope
    have hterminalLt :
        |ω T - sSup (roundedPositiveDriftComponent A ρ h)| < η / 2 := by
      calc
        |ω T - sSup (roundedPositiveDriftComponent A ρ h)| =
            |(ω T - (roundedMeanMap A ρ)^[T] q) +
              ((roundedMeanMap A ρ)^[T] q -
                sSup (roundedPositiveDriftComponent A ρ h))| := by ring_nf
        _ ≤ |ω T - (roundedMeanMap A ρ)^[T] q| +
              |(roundedMeanMap A ρ)^[T] q -
                sSup (roundedPositiveDriftComponent A ρ h)| :=
          abs_add_le _ _
        _ < η / 2 := by linarith
    change η / 2 < |ω T - sSup (roundedPositiveDriftComponent A ρ h)|
      at hterminal
    exact (not_lt_of_ge hterminal.le) hterminalLt
  exact
    (measureReal_mono hsubset).trans
      (markovPathMeasure_measureReal_abs_sub_iterate_gt_errorEnvelope_le
        hA hρ hρ_lt hN hδ hq)

/-- Paper form of the uniform stochastic entrance estimate: the entrance time
and positive constants are independent of the population size and of the
starting point in the prescribed compact set. -/
theorem exists_uniform_markovPathMeasure_entrance_exp_bound
    {A ρ h η : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ) (hη : 0 < η)
    (B : Set ℝ) (hBCompact : IsCompact B)
    (hBSub : B ⊆ Set.Ioc
      (sInf (roundedPositiveDriftComponent A ρ h))
      (sSup (roundedPositiveDriftComponent A ρ h))) :
    ∃ T : ℕ, ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧
      ∀ (N : ℕ), 0 < N → ∀ q ∈ B,
        (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
            {ω : ℕ → ℝ |
              |ω T - sSup (roundedPositiveDriftComponent A ρ h)| >
                η / 2} ≤
          C * Real.exp (-c₀ * N) := by
  obtain ⟨T, δ, hδ, hbound⟩ :=
    exists_markovPathMeasure_measureReal_abs_sub_upper_gt_half_le
      hA hρ hρ_lt hh hη B hBCompact hBSub
  let C : ℝ := 2 * ((T : ℝ) + 1)
  let c₀ : ℝ := 2 * δ ^ 2 / roundedRadiusBound ρ ^ 2
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    exact div_pos
      (mul_pos (by norm_num) (sq_pos_of_pos hδ))
      (sq_pos_of_pos (roundedRadiusBound_pos hρ hρ_lt))
  refine ⟨T, C, c₀, hC, hc₀, ?_⟩
  intro N hN q hqB
  calc
    (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
          {ω : ℕ → ℝ |
            |ω T - sSup (roundedPositiveDriftComponent A ρ h)| > η / 2}
        ≤ 2 * T * Real.exp
            (-2 * N * δ ^ 2 / roundedRadiusBound ρ ^ 2) :=
      hbound N hN q hqB
    _ = 2 * T * Real.exp (-c₀ * N) := by
      congr 1
      dsimp [c₀]
      ring_nf
    _ ≤ C * Real.exp (-c₀ * N) := by
      gcongr
      dsimp [C]
      linarith

/-- The rightmost positive-drift component has a compact inward-invariant
neighborhood of its upper endpoint, with a positive uniform margin from the
boundary. This is the deterministic persistence input in the paper. -/
theorem exists_roundedPositiveDriftComponent_inward_margin
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hrightmost : IsRightmostRoundedPositiveDriftComponent A ρ h) :
    let C := roundedPositiveDriftComponent A ρ h
    ∃ η₀ : ℝ, 0 < η₀ ∧
      sInf C < sSup C - η₀ ∧
      sSup C + η₀ < roundedRadiusBound ρ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        roundedMeanMap A ρ '' Set.Icc (sSup C - η) (sSup C + η) ⊆
          Set.Ioo (sSup C - η) (sSup C + η) ∧
        ∃ d : ℝ, 0 < d ∧
          ∀ u ∈ Set.Icc (sSup C - η) (sSup C + η),
            roundedMeanMap A ρ u ∈
              Set.Icc (sSup C - η + d) (sSup C + η - d) := by
  dsimp only
  let C := roundedPositiveDriftComponent A ρ h
  let lower := sInf C
  let upper := sSup C
  let V := roundedMeanMap A ρ
  obtain ⟨η₀, hη₀, hleft₀, hright₀, hstable⟩ :=
    roundedPositiveDriftComponent_right_stable_of_rightmost
      hA hρ hρ_lt hh hrightmost
  refine ⟨η₀, hη₀, hleft₀, hright₀, ?_⟩
  intro η hη hη_lt
  have hleft : lower < upper - η := by
    linarith
  have hleftUpper : upper - η < upper := by
    linarith
  have hrightLower : upper < upper + η := by
    linarith
  have hrightUpper : upper + η ≤ upper + η₀ := by
    linarith
  have hinterval : C = Set.Ioo lower upper :=
    roundedPositiveDriftComponent_eq_Ioo hA hρ hρ_lt hh
  have hleftC : upper - η ∈ C := by
    rw [hinterval]
    exact ⟨hleft, hleftUpper⟩
  have hleftDrift : upper - η < V (upper - η) :=
    (roundedPositiveDriftComponent_subset A ρ h hleftC).2
  have hrightDrift : V (upper + η) < upper + η :=
    hstable (upper + η) ⟨hrightLower, hrightUpper⟩
  have hmono : Monotone V :=
    monotone_roundedMeanMap hA hρ
  have himage :
      V '' Set.Icc (upper - η) (upper + η) ⊆
        Set.Ioo (upper - η) (upper + η) := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hleftDrift.trans_le (hmono hu.1),
      (hmono hu.2).trans_lt hrightDrift⟩
  refine ⟨himage, ?_⟩
  let J := Set.Icc (upper - η) (upper + η)
  let K := V '' J
  have hJNonempty : J.Nonempty :=
    Set.nonempty_Icc.mpr (by linarith)
  have hKNonempty : K.Nonempty :=
    hJNonempty.image V
  have hKCompact : IsCompact K := by
    exact isCompact_Icc.image
      (continuous_roundedMeanMap hA hρ hρ_lt)
  obtain ⟨a, haK, haLeast⟩ :=
    hKCompact.exists_isLeast hKNonempty
  obtain ⟨b, hbK, hbGreatest⟩ :=
    hKCompact.exists_isGreatest hKNonempty
  have haOpen : a ∈ Set.Ioo (upper - η) (upper + η) :=
    himage haK
  have hbOpen : b ∈ Set.Ioo (upper - η) (upper + η) :=
    himage hbK
  let d := min (a - (upper - η)) ((upper + η) - b)
  have hd : 0 < d := by
    dsimp only [d]
    exact lt_min (sub_pos.mpr haOpen.1) (sub_pos.mpr hbOpen.2)
  refine ⟨d, hd, ?_⟩
  intro u hu
  have huK : V u ∈ K :=
    ⟨u, hu, rfl⟩
  have had : d ≤ a - (upper - η) :=
    min_le_left _ _
  have hdb : d ≤ (upper + η) - b :=
    min_le_right _ _
  exact ⟨by linarith [haLeast huK], by linarith [hbGreatest huK]⟩

/-- The event that a path exits the closed `η`-neighborhood of `upper` within
`T` steps after time `t₀`. -/
def metastableExitEvent
    (upper η : ℝ) (t₀ T : ℕ) : Set (ℕ → ℝ) :=
  {ω | ∃ s ≤ T, η < |ω (t₀ + s) - upper|}

/-- The finite-horizon metastable exit event is measurable on canonical path
space. -/
lemma measurableSet_metastableExitEvent
    (upper η : ℝ) (t₀ T : ℕ) :
    MeasurableSet (metastableExitEvent upper η t₀ T) := by
  unfold metastableExitEvent
  measurability

/-- Staying inside a metastable well whose lower endpoint is positive forces
survival through the terminal time. This is the canonical path-space bridge
from the exit estimate to the absorption-time lower bound. -/
lemma one_sub_measureReal_metastableExitEvent_le_survival
    {A ρ upper η q : ℝ} {N t₀ T : ℕ}
    (hleft : 0 < upper - η) :
    let μ :=
      markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
    1 - μ.real (metastableExitEvent upper η t₀ T) ≤
      μ.real
        {ω |
          ((t₀ + T : ℕ) : WithTop ℕ) <
            absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω} := by
  dsimp only
  let μ :=
    markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
  let E := metastableExitEvent upper η t₀ T
  let Z := {ω : ℕ → ℝ | ω (t₀ + T) ≠ 0}
  have hsubset : Eᶜ ⊆ Z := by
    intro ω hω
    have hbound : |ω (t₀ + T) - upper| ≤ η := by
      apply le_of_not_gt
      intro hlarge
      exact hω ⟨T, le_rfl, hlarge⟩
    have hlower : upper - η ≤ ω (t₀ + T) := by
      linarith [(abs_sub_le_iff.mp hbound).2]
    exact ne_of_gt (hleft.trans_le hlower)
  have hmono : μ.real Eᶜ ≤ μ.real Z :=
    measureReal_mono hsubset
  have hEmeas : MeasurableSet E :=
    measurableSet_metastableExitEvent upper η t₀ T
  have hcompl : μ.real Eᶜ = 1 - μ.real E := by
    rw [measureReal_compl hEmeas, probReal_univ]
  have hsurv :
      μ.real
          {ω |
            ((t₀ + T : ℕ) : WithTop ℕ) <
              absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω} =
        μ.real Z := by
    have hmeasure :=
      measure_absorptionTime_gt_eq_of_ae
        (fun s =>
          markovPathMeasure_ae_absorbing
            (Measure.dirac q) (Hkernel A ρ N)
            (isAbsorbing_Hkernel A ρ N) s)
        (t₀ + T)
    simpa only [μ, Z, measureReal_def] using
      congrArg ENNReal.toReal hmeasure
  rw [hcompl] at hmono
  rw [hsurv]
  exact hmono

/-- If a path starts in the half-sized metastable well and exits the full well,
then before its exit it makes a step larger than half the deterministic inward
margin. This is the stopped pathwise inclusion used in the paper's persistence
union bound. -/
lemma exists_preexit_step_deviation_gt_half
    {A ρ upper η d : ℝ} {t₀ T : ℕ}
    (hη : 0 < η) (hd : 0 < d)
    (hmargin :
      ∀ u ∈ Set.Icc (upper - η) (upper + η),
        roundedMeanMap A ρ u ∈
          Set.Icc (upper - η + d) (upper + η - d))
    (ω : ℕ → ℝ)
    (hstart : |ω t₀ - upper| ≤ η / 2)
    (hexit : ω ∈ metastableExitEvent upper η t₀ T) :
    ∃ s < T,
      (∀ r ≤ s, ω (t₀ + r) ∈ Set.Icc (upper - η) (upper + η)) ∧
      d / 2 <
        |ω (t₀ + s + 1) -
          roundedMeanMap A ρ (ω (t₀ + s))| := by
  let J := Set.Icc (upper - η) (upper + η)
  have hstartJ : ω t₀ ∈ J := by
    rw [abs_sub_le_iff] at hstart
    constructor <;> linarith
  have hprogress :
      ∀ n ≤ T,
        (∀ r ≤ n, ω (t₀ + r) ∈ J) ∨
        ∃ s < n,
          (∀ r ≤ s, ω (t₀ + r) ∈ J) ∧
          d / 2 <
            |ω (t₀ + s + 1) -
              roundedMeanMap A ρ (ω (t₀ + s))| := by
    intro n hnT
    induction n with
    | zero =>
        left
        intro r hr
        have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
        subst r
        simpa using hstartJ
    | succ n ih =>
        rcases ih (Nat.le_trans (Nat.le_succ n) hnT) with hall | hbad
        · by_cases hlarge :
            d / 2 <
              |ω (t₀ + n + 1) -
                roundedMeanMap A ρ (ω (t₀ + n))|
          · right
            exact ⟨n, Nat.lt_succ_self n, hall, hlarge⟩
          · left
            intro r hr
            rcases lt_or_eq_of_le hr with hrlt | rfl
            · exact hall r (Nat.lt_succ_iff.mp hrlt)
            · have hnJ : ω (t₀ + n) ∈ J :=
                hall n le_rfl
              have hV := hmargin (ω (t₀ + n)) hnJ
              have hsmall :
                  |ω (t₀ + n + 1) -
                    roundedMeanMap A ρ (ω (t₀ + n))| ≤ d / 2 :=
                le_of_not_gt hlarge
              have hsmall' :
                  |ω (t₀ + (n + 1)) -
                    roundedMeanMap A ρ (ω (t₀ + n))| ≤ d / 2 := by
                simpa only [Nat.add_assoc] using hsmall
              rw [abs_sub_le_iff] at hsmall'
              change ω (t₀ + (n + 1)) ∈ J
              exact ⟨by linarith [hV.1], by linarith [hV.2]⟩
        · right
          obtain ⟨s, hsn, hsJ, hslarge⟩ := hbad
          exact ⟨s, hsn.trans (Nat.lt_succ_self n), hsJ, hslarge⟩
  rcases hprogress T le_rfl with hall | hbad
  · obtain ⟨s, hsT, hsexit⟩ := hexit
    have hsJ := hall s hsT
    have habs : |ω (t₀ + s) - upper| ≤ η := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [hsJ.2], by linarith [hsJ.1]⟩
    exact ((not_lt_of_ge habs) hsexit).elim
  · exact hbad

/-- The event that at least one transition in the shifted horizon
`t₀, ..., t₀ + T - 1` deviates from its conditional mean by more than `ε`. -/
def shiftedFiniteHorizonStepDeviationEvent
    (A ρ ε : ℝ) (t₀ T : ℕ) : Set (ℕ → ℝ) :=
  ⋃ s ∈ Finset.range T,
    {ω : ℕ → ℝ |
      |ω (t₀ + s + 1) - roundedMeanMap A ρ (ω (t₀ + s))| > ε}

/-- The one-step Hoeffding estimate union-bounded over an arbitrary shifted
finite horizon. -/
lemma markovPathMeasure_measureReal_shiftedFiniteHorizonStepDeviationEvent_le
    {A ρ q ε : ℝ} {N t₀ T : ℕ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hε : 0 < ε) :
    (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
        (shiftedFiniteHorizonStepDeviationEvent A ρ ε t₀ T) ≤
      2 * T * Real.exp
        (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
  let b : ℝ :=
    2 * Real.exp
      (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2)
  rw [shiftedFiniteHorizonStepDeviationEvent]
  calc
    μ.real
        (⋃ s ∈ Finset.range T,
          {ω : ℕ → ℝ |
            |ω (t₀ + s + 1) -
              roundedMeanMap A ρ (ω (t₀ + s))| > ε}) ≤
      ∑ s ∈ Finset.range T,
        μ.real
          {ω : ℕ → ℝ |
            |ω (t₀ + s + 1) -
              roundedMeanMap A ρ (ω (t₀ + s))| > ε} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ Finset.range T, b := by
      apply Finset.sum_le_sum
      intro s _hs
      exact
        markovPathMeasure_measureReal_abs_next_sub_roundedMeanMap_gt_le
          hA hρ hρ_lt hN hε (t₀ + s)
    _ = 2 * T * Real.exp
          (-2 * N * ε ^ 2 / roundedRadiusBound ρ ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, b]
      ring

/-- Once the path has entered the half-sized well, exiting the full well
through a shifted finite horizon is controlled by the Hoeffding union bound at
half the deterministic inward margin. -/
lemma markovPathMeasure_measureReal_inter_start_metastableExitEvent_le
    {A ρ q upper η d : ℝ} {N t₀ T : ℕ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hN : 0 < N) (hη : 0 < η) (hd : 0 < d)
    (hmargin :
      ∀ u ∈ Set.Icc (upper - η) (upper + η),
        roundedMeanMap A ρ u ∈
          Set.Icc (upper - η + d) (upper + η - d)) :
    (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
        ({ω : ℕ → ℝ | |ω t₀ - upper| ≤ η / 2} ∩
          metastableExitEvent upper η t₀ T) ≤
      2 * T * Real.exp
        (-2 * N * (d / 2) ^ 2 / roundedRadiusBound ρ ^ 2) := by
  have hsubset :
      ({ω : ℕ → ℝ | |ω t₀ - upper| ≤ η / 2} ∩
          metastableExitEvent upper η t₀ T) ⊆
        shiftedFiniteHorizonStepDeviationEvent A ρ (d / 2) t₀ T := by
    rintro ω ⟨hstart, hexit⟩
    obtain ⟨s, hsT, _hsJ, hlarge⟩ :=
      exists_preexit_step_deviation_gt_half
        hη hd hmargin ω hstart hexit
    simp only [shiftedFiniteHorizonStepDeviationEvent,
      Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨s, Finset.mem_range.mpr hsT, hlarge⟩
  exact
    (measureReal_mono hsubset).trans
      (markovPathMeasure_measureReal_shiftedFiniteHorizonStepDeviationEvent_le
        hA hρ hρ_lt hN (half_pos hd))

/-- Paper-form persistence estimate for the rightmost positive-drift
component, combining stochastic entrance with the stopped Hoeffding bound. -/
theorem exists_uniform_markovPathMeasure_exit_exp_bound
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hrightmost : IsRightmostRoundedPositiveDriftComponent A ρ h)
    (B : Set ℝ) (hBCompact : IsCompact B)
    (hBSub : B ⊆ Set.Ioc
      (sInf (roundedPositiveDriftComponent A ρ h))
      (sSup (roundedPositiveDriftComponent A ρ h))) :
    let Ccomp := roundedPositiveDriftComponent A ρ h
    ∃ η₀ : ℝ, 0 < η₀ ∧
      sInf Ccomp < sSup Ccomp - η₀ ∧
      sSup Ccomp + η₀ < roundedRadiusBound ρ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        ∃ Tη : ℕ, ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧
          ∀ (N : ℕ), 0 < N → ∀ q ∈ B, ∀ T : ℕ,
            (markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)).real
                (metastableExitEvent (sSup Ccomp) η Tη T) ≤
              C * (1 + T) * Real.exp (-c₀ * N) := by
  dsimp only
  let Ccomp := roundedPositiveDriftComponent A ρ h
  let upper := sSup Ccomp
  obtain ⟨η₀, hη₀, hleft, hright, hmarginData⟩ :=
    exists_roundedPositiveDriftComponent_inward_margin
      hA hρ hρ_lt hh hrightmost
  refine ⟨η₀, hη₀, hleft, hright, ?_⟩
  intro η hη hη_lt
  obtain ⟨_himage, d, hd, hmargin⟩ :=
    hmarginData η hη hη_lt
  obtain ⟨Tη, Cent, cent, hCent, hcent, hentrance⟩ :=
    exists_uniform_markovPathMeasure_entrance_exp_bound
      hA hρ hρ_lt hh hη B hBCompact hBSub
  let cpers : ℝ :=
    2 * (d / 2) ^ 2 / roundedRadiusBound ρ ^ 2
  let c₀ : ℝ := min cent cpers
  let C : ℝ := Cent + 2
  have hcpers : 0 < cpers := by
    dsimp only [cpers]
    exact div_pos
      (mul_pos (by norm_num) (sq_pos_of_pos (half_pos hd)))
      (sq_pos_of_pos (roundedRadiusBound_pos hρ hρ_lt))
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    exact lt_min hcent hcpers
  have hC : 0 < C := by
    dsimp only [C]
    linarith
  refine ⟨Tη, C, c₀, hC, hc₀, ?_⟩
  intro N hN q hqB T
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
  let E : Set (ℕ → ℝ) :=
    metastableExitEvent upper η Tη T
  let F : Set (ℕ → ℝ) :=
    {ω | η / 2 < |ω Tη - upper|}
  let S : Set (ℕ → ℝ) :=
    {ω | |ω Tη - upper| ≤ η / 2}
  have hsubset : E ⊆ F ∪ (S ∩ E) := by
    intro ω hωE
    by_cases hωS : |ω Tη - upper| ≤ η / 2
    · exact Or.inr ⟨hωS, hωE⟩
    · exact Or.inl (lt_of_not_ge hωS)
  have hentranceBound :
      μ.real F ≤ Cent * Real.exp (-cent * N) := by
    exact hentrance N hN q hqB
  have hpersistenceBound :
      μ.real (S ∩ E) ≤
        2 * T * Real.exp
          (-2 * N * (d / 2) ^ 2 / roundedRadiusBound ρ ^ 2) := by
    exact
      markovPathMeasure_measureReal_inter_start_metastableExitEvent_le
        hA hρ hρ_lt hN hη hd hmargin
  have hexpEntrance :
      Real.exp (-cent * N) ≤ Real.exp (-c₀ * N) := by
    apply Real.exp_le_exp.mpr
    have hc₀le : c₀ ≤ cent := by
      dsimp only [c₀]
      exact min_le_left _ _
    exact
      mul_le_mul_of_nonneg_right (neg_le_neg hc₀le)
        (Nat.cast_nonneg N)
  have hexpPersistence :
      Real.exp (-cpers * N) ≤ Real.exp (-c₀ * N) := by
    apply Real.exp_le_exp.mpr
    have hc₀le : c₀ ≤ cpers := by
      dsimp only [c₀]
      exact min_le_right _ _
    exact
      mul_le_mul_of_nonneg_right (neg_le_neg hc₀le)
        (Nat.cast_nonneg N)
  calc
    μ.real E ≤ μ.real (F ∪ (S ∩ E)) :=
      measureReal_mono hsubset
    _ ≤ μ.real F + μ.real (S ∩ E) :=
      measureReal_union_le _ _
    _ ≤ Cent * Real.exp (-cent * N) +
          2 * T * Real.exp
            (-2 * N * (d / 2) ^ 2 / roundedRadiusBound ρ ^ 2) :=
      add_le_add hentranceBound hpersistenceBound
    _ = Cent * Real.exp (-cent * N) +
          2 * T * Real.exp (-cpers * N) := by
      congr 2
      dsimp only [cpers]
      congr 1
      ring
    _ ≤ Cent * Real.exp (-c₀ * N) +
          2 * T * Real.exp (-c₀ * N) := by
      gcongr
    _ = (Cent + 2 * T) * Real.exp (-c₀ * N) := by ring
    _ ≤ C * (1 + T) * Real.exp (-c₀ * N) := by
      gcongr
      dsimp only [C]
      nlinarith [mul_nonneg hCent.le (Nat.cast_nonneg T)]

/-- The scalar exponential estimate used when the persistence horizon is
`floor (exp (c₁ N))` with `c₁ < c₀`. -/
lemma tendsto_one_add_floor_exp_mul_exp_neg
    {C c₀ c₁ : ℝ} (hC : 0 ≤ C) (hc₁ : 0 < c₁) (hc₁_lt : c₁ < c₀) :
    Tendsto
      (fun N : ℕ =>
        C * (1 + (⌊Real.exp (c₁ * N)⌋₊ : ℝ)) *
          Real.exp (-c₀ * N))
      atTop (𝓝 0) := by
  have hgap : 0 < c₀ - c₁ :=
    sub_pos.mpr hc₁_lt
  have hlin :
      Tendsto (fun N : ℕ => -(c₀ - c₁) * (N : ℝ)) atTop atBot := by
    convert
      tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg
        (neg_lt_zero.mpr hgap) using 1
    ext N
    ring
  have hexp :
      Tendsto (fun N : ℕ => Real.exp (-(c₀ - c₁) * (N : ℝ)))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hupper :
      Tendsto
        (fun N : ℕ =>
          2 * C * Real.exp (-(c₀ - c₁) * (N : ℝ)))
        atTop (𝓝 0) := by
    simpa using (hexp.const_mul (2 * C))
  apply squeeze_zero
  · intro N
    positivity
  · intro N
    have hfloor :
        (⌊Real.exp (c₁ * N)⌋₊ : ℝ) ≤ Real.exp (c₁ * N) :=
      Nat.floor_le (Real.exp_pos _).le
    have hexpOne : 1 ≤ Real.exp (c₁ * N) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      positivity
    calc
      C * (1 + (⌊Real.exp (c₁ * N)⌋₊ : ℝ)) *
            Real.exp (-c₀ * N)
          ≤ C * (2 * Real.exp (c₁ * N)) *
              Real.exp (-c₀ * N) := by
            gcongr
            linarith
      _ = 2 * C * Real.exp (-(c₀ - c₁) * (N : ℝ)) := by
        have hexp_mul :
            Real.exp (c₁ * (N : ℝ)) * Real.exp (-c₀ * (N : ℝ)) =
              Real.exp (-(c₀ - c₁) * (N : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [← hexp_mul]
        ring
  · exact hupper

/-- Uniform exponential persistence in the rightmost metastable well. The
initial state may depend on `N`, provided it remains in the prescribed compact
set. For a suitable `c₁ > 0`, the canonical absorption time exceeds
`Tη + floor (exp (c₁ N))` with probability tending to one. -/
theorem exists_exponential_absorption_survival
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : h ∈ roundedPositiveDriftSet A ρ)
    (hrightmost : IsRightmostRoundedPositiveDriftComponent A ρ h)
    (B : Set ℝ) (hBCompact : IsCompact B)
    (hBSub : B ⊆ Set.Ioc
      (sInf (roundedPositiveDriftComponent A ρ h))
      (sSup (roundedPositiveDriftComponent A ρ h))) :
    let Ccomp := roundedPositiveDriftComponent A ρ h
    ∃ η₀ : ℝ, 0 < η₀ ∧
      sInf Ccomp < sSup Ccomp - η₀ ∧
      sSup Ccomp + η₀ < roundedRadiusBound ρ ∧
      ∀ η : ℝ, 0 < η → η < η₀ →
        ∃ Tη : ℕ, ∃ c₁ : ℝ, 0 < c₁ ∧
          ∀ q : ℕ → ℝ, (∀ N, q N ∈ B) →
            Tendsto
              (fun N : ℕ =>
                (markovPathMeasure (Measure.dirac (q N))
                    (Hkernel A ρ N)).real
                  {ω |
                    ((Tη + ⌊Real.exp (c₁ * N)⌋₊ : ℕ) :
                        WithTop ℕ) <
                      absorptionTime
                        (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω})
              atTop (𝓝 1) := by
  dsimp only
  let Ccomp := roundedPositiveDriftComponent A ρ h
  obtain ⟨η₀, hη₀, hleft₀, hright₀, hboundData⟩ :=
    exists_uniform_markovPathMeasure_exit_exp_bound
      hA hρ hρ_lt hh hrightmost B hBCompact hBSub
  refine ⟨η₀, hη₀, hleft₀, hright₀, ?_⟩
  intro η hη hη_lt
  obtain ⟨Tη, C, c₀, hC, hc₀, hbound⟩ :=
    hboundData η hη hη_lt
  let c₁ := c₀ / 2
  have hc₁ : 0 < c₁ := half_pos hc₀
  have hc₁_lt : c₁ < c₀ := half_lt_self hc₀
  refine ⟨Tη, c₁, hc₁, ?_⟩
  intro q hqB
  let b : ℕ → ℝ :=
    fun N =>
      C * (1 + (⌊Real.exp (c₁ * N)⌋₊ : ℝ)) *
        Real.exp (-c₀ * N)
  let p : ℕ → ℝ :=
    fun N =>
      (markovPathMeasure (Measure.dirac (q N))
          (Hkernel A ρ N)).real
        {ω |
          ((Tη + ⌊Real.exp (c₁ * N)⌋₊ : ℕ) :
              WithTop ℕ) <
            absorptionTime
              (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω}
  have hb : Tendsto b atTop (𝓝 0) := by
    exact tendsto_one_add_floor_exp_mul_exp_neg hC.le hc₁ hc₁_lt
  have hwell : 0 < sSup Ccomp - η := by
    have hendpoints :=
      roundedPositiveDriftComponent_endpoints hA hρ hρ_lt hh
    exact hendpoints.1.trans (by linarith)
  have hlower : ∀ᶠ N in atTop, 1 - b N ≤ p N := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hexit :=
      hbound N (by omega) (q N) (hqB N)
        ⌊Real.exp (c₁ * N)⌋₊
    have hbridge :=
      one_sub_measureReal_metastableExitEvent_le_survival
        (A := A) (ρ := ρ) (upper := sSup Ccomp) (η := η)
        (q := q N) (N := N) (t₀ := Tη)
        (T := ⌊Real.exp (c₁ * N)⌋₊) hwell
    exact (sub_le_sub_left hexit 1).trans hbridge
  have hlower_tendsto : Tendsto (fun N => 1 - b N) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hb
  have hupper : ∀ᶠ N in atTop, p N ≤ 1 :=
    Eventually.of_forall fun N => measureReal_le_one
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower_tendsto tendsto_const_nhds hlower hupper

/-- For fixed dimension, one rounded Gaussian step has a uniformly positive
chance of hitting the absorbing state from every radius in the canonical
compact interval. A fixed coordinatewise Gaussian box is sent entirely to
zero, uniformly over the starting radius. -/
theorem exists_pos_le_measureReal_Hkernel_singleton_zero
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (N : ℕ) :
    ∃ p : ℝ, 0 < p ∧
      ∀ h ∈ Set.Icc 0 (roundedRadiusBound ρ),
        p ≤ (Hkernel A ρ N h).real {(0 : ℝ)} := by
  let M := roundedRadiusBound ρ
  let t : ℝ := 1 / (2 * A * Real.sqrt M)
  let I : Set ℝ := Set.Icc (-t) t
  let E : Set (Fin N → ℝ) := Set.univ.pi fun _ => I
  let p : ℝ := ((gaussianReal 0 1).real I) ^ N
  have hM : 0 < M :=
    roundedRadiusBound_pos hρ hρ_lt
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hIpos : 0 < (gaussianReal 0 1).real I := by
    simpa only [I] using gaussianReal_Icc_neg_pos ht
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  refine ⟨p, hp, ?_⟩
  intro h hh
  have hsubset : E ⊆ (Hmap A ρ N h) ⁻¹' {(0 : ℝ)} := by
    intro g hg
    have hzero : Hmap A ρ N h g = 0 := by
      rw [Hmap_eq_zero_iff_forall_observable]
      intro i
      have hgi : g i ∈ I := hg i (Set.mem_univ i)
      have habsg : |g i| ≤ t := by
        rw [abs_le]
        exact hgi
      have hsqrt : Real.sqrt h ≤ Real.sqrt M :=
        Real.sqrt_le_sqrt hh.2
      have htanh :
          |Real.tanh (ρ * (A * Real.sqrt h * g i))| ≤
            |ρ * (A * Real.sqrt h * g i)| :=
        abs_tanh_le_abs _
      have harg :
          |ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g i)| ≤ 2⁻¹ := by
        rw [abs_mul, abs_inv, abs_of_pos hρ]
        rw [abs_mul, abs_of_pos hρ] at htanh
        calc
          ρ⁻¹ * |Real.tanh (ρ * A * Real.sqrt h * g i)|
              ≤ ρ⁻¹ * (ρ * |A * Real.sqrt h * g i|) :=
                mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using htanh)
                  (inv_nonneg.mpr hρ.le)
          _ = |A * Real.sqrt h * g i| := by field_simp
          _ = A * Real.sqrt h * |g i| := by
                rw [abs_mul, abs_mul, abs_of_pos hA,
                  abs_of_nonneg (Real.sqrt_nonneg h)]
          _ ≤ A * Real.sqrt M * t := by
                gcongr
          _ = 2⁻¹ := by
                dsimp only [t]
                field_simp [hA.ne', (Real.sqrt_pos.2 hM).ne']
      have hQ := (Q₁_zero_iff _).mpr harg
      simp [roundedCoordinateObservable, hQ]
    exact hzero
  have hEmeasure :
      (gaussianVec N).real E = p := by
    simp only [gaussianVec, E, I, p, measureReal_def]
    rw [Measure.pi_pi]
    simp
  rw [Hkernel_apply, measureReal_def,
    Measure.map_apply (measurable_Hmap_right A ρ N h)
      (measurableSet_singleton (0 : ℝ))]
  change p ≤ (gaussianVec N).real ((Hmap A ρ N h) ⁻¹' {(0 : ℝ)})
  rw [← hEmeasure]
  exact measureReal_mono hsubset

/-- The uniform one-step absorption chance iterates to a geometric survival
bound for every fixed dimension and every initial radius in the canonical
compact interval. -/
theorem exists_geometric_Hkernel_survival_bound
    {A ρ q : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N)
    (hq : q ∈ Set.Icc 0 (roundedRadiusBound ρ)) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
      ∀ t : ℕ,
        (((Hkernel A ρ N) ^ t) q).real {(0 : ℝ)}ᶜ ≤
          (1 - p) ^ t := by
  obtain ⟨p, hp, hpzero⟩ :=
    exists_pos_le_measureReal_Hkernel_singleton_zero hA hρ hρ_lt N
  have hp_le : p ≤ 1 :=
    (hpzero 0 ⟨le_rfl, roundedRadiusBound_nonneg ρ⟩).trans
      measureReal_le_one
  have hcp : 0 ≤ 1 - p := sub_nonneg.mpr hp_le
  let c : ENNReal := ENNReal.ofReal (1 - p)
  have hc : c.toReal = 1 - p := ENNReal.toReal_ofReal hcp
  have hENN :
      ∀ t : ℕ,
        ((Hkernel A ρ N) ^ t) q {(0 : ℝ)}ᶜ ≤ c ^ t := by
    intro t
    induction t with
    | zero =>
        calc
          ((Hkernel A ρ N) ^ 0) q {(0 : ℝ)}ᶜ ≤
              ((Hkernel A ρ N) ^ 0) q Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
          _ = c ^ 0 := by simp
    | succ t ih =>
        let ν := ((Hkernel A ρ N) ^ t) q
        haveI : IsProbabilityMeasure ν := by
          dsimp only [ν]
          infer_instance
        have hstate :
            ∀ᵐ h ∂ν, h ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
          let μ :=
            markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
          have hpath :
              ∀ᵐ ω ∂μ,
                ω t ∈ Set.Icc 0 (roundedRadiusBound ρ) := by
            dsimp only [μ]
            exact
              markovPathMeasure_dirac_ae_eval_mem_roundedRadiusBound_Icc
                hq hρ hN t
          have hmap :
              μ.map (fun ω => ω t) = ν := by
            dsimp only [μ, ν]
            exact markovPathMeasure_dirac_map_eval
              q (Hkernel A ρ N) t
          have hmapped :
              ∀ᵐ h ∂μ.map (fun ω => ω t),
                h ∈ Set.Icc 0 (roundedRadiusBound ρ) :=
            (MeasureTheory.ae_map_iff
              (measurable_pi_apply t).aemeasurable measurableSet_Icc).2 hpath
          rwa [hmap] at hmapped
        have hpoint :
            ∀ᵐ h ∂ν,
              Hkernel A ρ N h {(0 : ℝ)}ᶜ ≤
                ({(0 : ℝ)}ᶜ : Set ℝ).indicator (fun _ => c) h := by
          filter_upwards [hstate] with h hh
          by_cases hz : h = 0
          · subst h
            rw [isAbsorbing_Hkernel,
              Set.indicator_of_notMem (by simp)]
            simp
          · rw [Set.indicator_of_mem (by simpa)]
            have hreal :
                (Hkernel A ρ N h).real {(0 : ℝ)}ᶜ ≤ 1 - p := by
              rw [measureReal_compl (measurableSet_singleton (0 : ℝ)),
                probReal_univ]
              linarith [hpzero h hh]
            calc
              Hkernel A ρ N h {(0 : ℝ)}ᶜ =
                  ENNReal.ofReal
                    ((Hkernel A ρ N h).real {(0 : ℝ)}ᶜ) := by
                    rw [measureReal_def,
                      ENNReal.ofReal_toReal (measure_ne_top _ _)]
              _ ≤ ENNReal.ofReal (1 - p) :=
                ENNReal.ofReal_le_ofReal hreal
              _ = c := rfl
        rw [pow_succ',
          show Hkernel A ρ N * (Hkernel A ρ N) ^ t =
              Kernel.comp (Hkernel A ρ N) ((Hkernel A ρ N) ^ t) from rfl]
        calc
          (Kernel.comp (Hkernel A ρ N) ((Hkernel A ρ N) ^ t) q)
                {(0 : ℝ)}ᶜ =
              ∫⁻ h, Hkernel A ρ N h {(0 : ℝ)}ᶜ ∂ν := by
                simpa only [ν] using
                  Kernel.comp_apply' (Hkernel A ρ N)
                    ((Hkernel A ρ N) ^ t) q
                    (measurableSet_singleton (0 : ℝ)).compl
          _ ≤
              ∫⁻ h,
                ({(0 : ℝ)}ᶜ : Set ℝ).indicator (fun _ => c) h ∂ν :=
            lintegral_mono_ae hpoint
          _ = c * ν {(0 : ℝ)}ᶜ := by
            rw [lintegral_indicator (measurableSet_singleton (0 : ℝ)).compl,
              setLIntegral_const]
          _ ≤ c * c ^ t := by gcongr
          _ = c ^ (t + 1) := by
            rw [pow_succ]
            exact mul_comm _ _
  refine ⟨p, hp, hp_le, ?_⟩
  intro t
  rw [measureReal_def]
  calc
    ((((Hkernel A ρ N) ^ t) q {(0 : ℝ)}ᶜ).toReal)
        ≤ (c ^ t).toReal :=
      ENNReal.toReal_mono (by finiteness) (hENN t)
    _ = (1 - p) ^ t := by rw [ENNReal.toReal_pow, hc]

/-- For every fixed positive dimension, rounded-radius survival tends to zero
and the canonical absorption time is finite almost surely. -/
theorem tendsto_Hkernel_survival_and_ae_absorption
    {A ρ q : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N)
    (hq : q ∈ Set.Icc 0 (roundedRadiusBound ρ)) :
    Tendsto
        (fun t : ℕ =>
          (((Hkernel A ρ N) ^ t) q).real {(0 : ℝ)}ᶜ)
        atTop (𝓝 0) ∧
      ∀ᵐ ω ∂markovPathMeasure (Measure.dirac q) (Hkernel A ρ N),
        absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω ≠ ⊤ := by
  obtain ⟨p, hp, hp_le, hbound⟩ :=
    exists_geometric_Hkernel_survival_bound hA hρ hρ_lt hN hq
  have hbase0 : 0 ≤ 1 - p := sub_nonneg.mpr hp_le
  have hbase1 : 1 - p < 1 := by linarith
  have hgeom :
      Tendsto (fun t : ℕ => (1 - p) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  have hsurv :
      Tendsto
        (fun t : ℕ =>
          (((Hkernel A ρ N) ^ t) q).real {(0 : ℝ)}ᶜ)
        atTop (𝓝 0) := by
    apply squeeze_zero
    · intro t
      exact measureReal_nonneg
    · exact hbound
    · exact hgeom
  refine ⟨hsurv, ?_⟩
  let μ :=
    markovPathMeasure (Measure.dirac q) (Hkernel A ρ N)
  let Einf : Set (ℕ → ℝ) :=
    {ω |
      absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω = ⊤}
  have hsubset :
      ∀ t : ℕ,
        Einf ⊆
          {ω |
            (t : WithTop ℕ) <
              absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω} := by
    intro t ω hω
    change
      absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω = ⊤ at hω
    change
      (t : WithTop ℕ) <
        absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω
    rw [hω]
    simp
  have hsurvEq :
      ∀ t : ℕ,
        μ.real
            {ω |
              (t : WithTop ℕ) <
                absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω} =
          (((Hkernel A ρ N) ^ t) q).real {(0 : ℝ)}ᶜ := by
    intro t
    rw [measureReal_def,
      measure_roundedAbsorptionTime_gt_eq A ρ N q t]
    rfl
  have hInfLe :
      μ.real Einf ≤ 0 := by
    apply ge_of_tendsto' hsurv
    intro t
    rw [← hsurvEq t]
    exact measureReal_mono (hsubset t)
  have hInfZero : μ Einf = 0 := by
    apply (measureReal_eq_zero_iff).mp
    exact le_antisymm hInfLe measureReal_nonneg
  change ∀ᵐ ω ∂μ,
    absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω ≠ ⊤
  rw [ae_iff]
  simpa only [Einf, not_ne_iff] using hInfZero

end AbsorptionCutoff
