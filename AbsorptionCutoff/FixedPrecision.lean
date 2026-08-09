/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Lattice
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Fixed-precision rounded mean-map estimates

Begins the paper's `lem:subcritical-fixed-precision-map-estimates` (§4).  The exact
finite-layer representation of the rounded mean map uses the threshold

`b_{ρ,k} = ρ⁻¹ artanh(ρ(k+1/2))`

for precisely those nonnegative integer layers with `ρ(k+1/2) < 1`.
-/

open Set
open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The standard-Gaussian upper tail `barΦ(t)=ℙ(G>t)`, as a real number. -/
noncomputable def gaussianUpperTail (t : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Ioi t)

/-- The standard-Gaussian upper tail is the improper integral of its density. -/
lemma gaussianUpperTail_eq_integral (t : ℝ) :
    gaussianUpperTail t = ∫ x in Set.Ioi t, gaussianPDFReal 0 1 x := by
  rw [gaussianUpperTail, measureReal_def,
    gaussianReal_apply_eq_integral (μ := 0) (v := 1)
    (by norm_num) (Set.Ioi t), ENNReal.toReal_ofReal]
  exact integral_nonneg fun x => gaussianPDFReal_nonneg 0 1 x

/-- Every finite threshold has strictly positive standard-Gaussian upper tail. -/
lemma gaussianUpperTail_pos (t : ℝ) : 0 < gaussianUpperTail t := by
  have hne : gaussianReal 0 1 (Set.Ioi t) ≠ 0 := by
    intro hzero
    have hvol := gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num) hzero
    simp at hvol
  rw [gaussianUpperTail, measureReal_def]
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

/-- The standard-Gaussian upper tail is antitone in its threshold. -/
lemma antitone_gaussianUpperTail : Antitone gaussianUpperTail := by
  intro s t hst
  exact measureReal_mono (Set.Ioi_subset_Ioi hst)

/-- Chernoff's bound for the standard-Gaussian upper tail. -/
lemma gaussianUpperTail_le_exp_neg_sq_div_two {t : ℝ} (ht : 0 ≤ t) :
    gaussianUpperTail t ≤ Real.exp (-t ^ 2 / 2) := by
  let μ := gaussianReal 0 1
  calc
    gaussianUpperTail t = μ.real {g : ℝ | t < g} := rfl
    _ ≤ μ.real {g : ℝ | t ≤ id g} := measureReal_mono (by
      intro g hg
      change t < g at hg
      change t ≤ id g
      exact hg.le)
    _ ≤ Real.exp (-t * t) * mgf id μ t :=
      measure_ge_le_exp_mul_mgf t ht (integrable_exp_mul_gaussianReal t)
    _ = Real.exp (-t ^ 2 / 2) := by
      rw [mgf_id_gaussianReal]
      simp only [NNReal.coe_one, zero_mul, zero_add]
      rw [← Real.exp_add]
      congr 1
      ring

/-- The standard-Gaussian density in the real-valued normalization used below. -/
lemma gaussianPDFReal_zero_one_eq (t : ℝ) :
    gaussianPDFReal 0 1 t =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
  rw [gaussianPDFReal]
  norm_num

/-- The derivative of the standard-Gaussian upper tail is minus its density. -/
lemma hasDerivAt_gaussianUpperTail (t : ℝ) :
    HasDerivAt gaussianUpperTail (-gaussianPDFReal 0 1 t) t := by
  have hcont : Continuous (gaussianPDFReal 0 1) := by
    rw [gaussianPDFReal_def]
    fun_prop
  have hint : Integrable (gaussianPDFReal 0 1) :=
    integrable_gaussianPDFReal 0 1
  have heq : gaussianUpperTail =
      fun u => (∫ x in Set.Ioi 0, gaussianPDFReal 0 1 x) -
        ∫ x in (0 : ℝ)..u, gaussianPDFReal 0 1 x := by
    funext u
    rw [gaussianUpperTail_eq_integral]
    have hsub := intervalIntegral.integral_Ioi_sub_Ioi'
      (μ := volume) (a := 0) (b := u) hint.integrableOn hint.integrableOn
    linarith
  rw [heq]
  exact HasDerivAt.const_sub (∫ x in Set.Ioi 0, gaussianPDFReal 0 1 x)
    (intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 t)
      hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt)

/-- The entire complex extension of the standard-Gaussian density. -/
noncomputable def complexStandardGaussianPDF (z : ℂ) : ℂ :=
  ((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) * Complex.exp (-z ^ 2 / 2)

/-- The complex Gaussian density restricts to the usual real density. -/
lemma complexStandardGaussianPDF_ofReal_re (t : ℝ) :
    (complexStandardGaussianPDF t).re = gaussianPDFReal 0 1 t := by
  rw [gaussianPDFReal_zero_one_eq]
  have hexp :
      (Complex.exp (-((t : ℂ) ^ 2) / 2)).re =
        Real.exp (-t ^ 2 / 2) := by
    rw [show -((t : ℂ) ^ 2) / 2 = ((-t ^ 2 / 2 : ℝ) : ℂ) by
      push_cast
      ring]
    exact Complex.exp_ofReal_re _
  unfold complexStandardGaussianPDF
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hexp]

/-- The standard-Gaussian upper tail is real analytic. -/
@[fun_prop]
lemma analyticAt_gaussianUpperTail (t : ℝ) :
    AnalyticAt ℝ gaussianUpperTail t := by
  have hcomplexDiff : Differentiable ℂ complexStandardGaussianPDF := by
    intro z
    unfold complexStandardGaussianPDF
    fun_prop
  obtain ⟨F, hF⟩ := hcomplexDiff.isExactOn_univ
  let P : ℝ → ℝ := fun x => (F x).re
  have hFDiff : Differentiable ℂ F :=
    fun z => (hF z (Set.mem_univ z)).differentiableAt
  have hPAnalytic (x : ℝ) : AnalyticAt ℝ P x := by
    dsimp only [P]
    exact (hFDiff.analyticAt (x : ℂ)).re_ofReal
  have hPDeriv (x : ℝ) :
      HasDerivAt P (gaussianPDFReal 0 1 x) x := by
    dsimp only [P]
    rw [← complexStandardGaussianPDF_ofReal_re]
    exact (hF (x : ℂ) (Set.mem_univ _)).real_of_complex
  let H : ℝ → ℝ := gaussianUpperTail + P
  have hHDeriv (x : ℝ) : HasDerivAt H 0 x := by
    dsimp only [H]
    simpa only [neg_add_cancel] using
      (hasDerivAt_gaussianUpperTail x).add (hPDeriv x)
  have hHConst (x : ℝ) : H t = H x :=
    is_const_of_deriv_eq_zero
      (fun y => (hHDeriv y).differentiableAt)
      (fun y => (hHDeriv y).deriv) t x
  have heq :
      gaussianUpperTail =
        fun x => gaussianUpperTail t + P t - P x := by
    funext x
    have := hHConst x
    change gaussianUpperTail t + P t = gaussianUpperTail x + P x at this
    linarith
  rw [heq]
  fun_prop

/-- The real square root is analytic at every positive point. -/
@[fun_prop]
lemma analyticAt_real_sqrt_of_pos {h : ℝ} (hh : 0 < h) :
    AnalyticAt ℝ Real.sqrt h := by
  let y := Real.sqrt h
  let sq : ℝ → ℝ := fun x => x ^ 2
  have hy : 0 < y := Real.sqrt_pos.2 hh
  have hsq : AnalyticAt ℝ sq y := by
    dsimp only [sq]
    fun_prop
  have hderiv : deriv sq y ≠ 0 := by
    dsimp only [sq]
    rw [deriv_pow_field]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    exact mul_ne_zero (by norm_num) hy.ne'
  have hevent :
      (id : ℝ → ℝ) =ᶠ[nhds y] Real.sqrt ∘ sq := by
    filter_upwards [Ioi_mem_nhds hy] with x hx
    simp only [id_eq, Function.comp_apply, sq, Real.sqrt_sq_eq_abs,
      abs_of_pos (show 0 < x from hx)]
  have hcomp : AnalyticAt ℝ (Real.sqrt ∘ sq) y :=
    (analyticAt_id : AnalyticAt ℝ (id : ℝ → ℝ) y).congr hevent
  have hsqrtSq : AnalyticAt ℝ Real.sqrt (sq y) :=
    (analyticAt_comp_iff_of_deriv_ne_zero hsq hderiv).mp hcomp
  simpa only [sq, y, Real.sq_sqrt hh.le] using hsqrtSq

/-- One differentiated Gaussian layer, in the exact normalization used by the paper. -/
lemma hasDerivAt_two_mul_gaussianUpperTail_div_sqrt {b A h : ℝ}
    (hA : 0 < A) (hh : 0 < h) :
    HasDerivAt
      (fun u => 2 * gaussianUpperTail (b / (A * Real.sqrt u)))
      (b / (A * h ^ (3 / 2 : ℝ)) *
        gaussianPDFReal 0 1 (b / (A * Real.sqrt h))) h := by
  have hs : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  have hdenom : A * Real.sqrt h ≠ 0 := mul_ne_zero hA.ne' hs
  have hinner := (hasDerivAt_const (x := h) b).div
    ((hasDerivAt_const (x := h) A).mul (Real.hasDerivAt_sqrt hh.ne'))
    hdenom
  have hcomp := (hasDerivAt_gaussianUpperTail (b / (A * Real.sqrt h))).comp h hinner
  have hmul := hcomp.const_mul 2
  have hderiv :
      2 * (-gaussianPDFReal 0 1 (b / (A * Real.sqrt h)) *
        ((0 * (A * Real.sqrt h) -
          b * (0 * Real.sqrt h + A * (1 / (2 * Real.sqrt h)))) /
          (A * Real.sqrt h) ^ 2)) =
        b / (A * h ^ (3 / 2 : ℝ)) *
          gaussianPDFReal 0 1 (b / (A * Real.sqrt h)) := by
    rw [Real.sqrt_eq_rpow]
    have hp : h ^ (3 / 2 : ℝ) = (h ^ (1 / 2 : ℝ)) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hh)]
      norm_num
    rw [hp]
    field_simp
    ring
  simpa only [Function.comp_apply, Pi.div_apply, Pi.mul_apply] using
    hmul.congr_deriv hderiv

/-- The preimage of the rounding layer `k+1/2` under `u ↦ ρ⁻¹ tanh(ρu)`. -/
noncomputable def roundedLayerThreshold (ρ : ℝ) (k : ℕ) : ℝ :=
  ρ⁻¹ * Real.artanh (ρ * ((k : ℝ) + 1 / 2))

/-- The finite candidate set of rounding layers satisfying `ρ(k+1/2)<1`.
The range bound is deliberately one integer loose; the filter is the exact condition. -/
noncomputable def roundedLayerIndices (ρ : ℝ) : Finset ℕ :=
  (Finset.range (⌈ρ⁻¹⌉₊ + 1)).filter fun k => ρ * ((k : ℝ) + 1 / 2) < 1

/-- The total odd-layer weight, including the factor two from Gaussian symmetry. -/
noncomputable def roundedLayerWeight (ρ : ℝ) : ℝ :=
  2 * ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ)

/-- The common zeroth-layer exponential rate in the small-radius estimates. -/
noncomputable def roundedSmallRate (A ρ : ℝ) : ℝ :=
  roundedLayerThreshold ρ 0 ^ 2 / (2 * A ^ 2)

/-- The finite coefficient in the differentiated small-radius estimate. -/
noncomputable def roundedDerivativeWeight (A ρ : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ *
    ∑ k ∈ roundedLayerIndices ρ,
      ((2 * k + 1 : ℕ) : ℝ) * (roundedLayerThreshold ρ k / A)

/-- Membership in the finite layer set is exactly the paper's admissibility inequality. -/
lemma mem_roundedLayerIndices_iff {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    k ∈ roundedLayerIndices ρ ↔ ρ * ((k : ℝ) + 1 / 2) < 1 := by
  rw [roundedLayerIndices, Finset.mem_filter, Finset.mem_range]
  refine ⟨And.right, fun hk => ⟨?_, hk⟩⟩
  have hkhalf : (k : ℝ) + 1 / 2 < ρ⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hρ]
    simpa [mul_comm] using hk
  have hkreal : (k : ℝ) < ρ⁻¹ := lt_trans (by norm_num) hkhalf
  have hkceil : k < ⌈ρ⁻¹⌉₊ := Nat.lt_ceil.mpr hkreal
  omega

/-- For `0<ρ<1`, the zeroth layer is admissible. -/
lemma zero_mem_roundedLayerIndices {ρ : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 ∈ roundedLayerIndices ρ := by
  simp [roundedLayerIndices]
  nlinarith

/-- The total layer weight is positive whenever the zeroth layer is admissible. -/
lemma roundedLayerWeight_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 < roundedLayerWeight ρ := by
  have hzero := zero_mem_roundedLayerIndices hρ hρ_lt
  have hsum : (1 : ℝ) ≤
      ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) := by
    have hsingle := Finset.single_le_sum
      (s := roundedLayerIndices ρ)
      (f := fun k => (((2 * k + 1 : ℕ) : ℝ)))
      (fun k hk => by positivity) hzero
    simpa using hsingle
  rw [roundedLayerWeight]
  positivity

/-- The first positive rounding boundary has a strictly positive preimage. -/
lemma roundedLayerThreshold_zero_pos {ρ : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 < roundedLayerThreshold ρ 0 := by
  rw [roundedLayerThreshold]
  apply mul_pos (inv_pos.mpr hρ)
  apply Real.artanh_pos
  constructor <;> norm_num <;> nlinarith

/-- The common small-radius exponential rate is strictly positive. -/
lemma roundedSmallRate_pos {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 < roundedSmallRate A ρ := by
  rw [roundedSmallRate]
  exact div_pos (sq_pos_of_pos (roundedLayerThreshold_zero_pos hρ hρ_lt))
    (mul_pos (by norm_num) (sq_pos_of_pos hA))

/-- Every admissible layer has a strictly positive preimage threshold. -/
lemma roundedLayerThreshold_pos {ρ : ℝ} (hρ : 0 < ρ) {k : ℕ}
    (hk : k ∈ roundedLayerIndices ρ) :
    0 < roundedLayerThreshold ρ k := by
  rw [roundedLayerThreshold]
  apply mul_pos (inv_pos.mpr hρ)
  apply Real.artanh_pos
  refine ⟨by positivity, (mem_roundedLayerIndices_iff hρ k).mp hk⟩

/-- The differentiated small-radius coefficient is strictly positive. -/
lemma roundedDerivativeWeight_pos {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    0 < roundedDerivativeWeight A ρ := by
  have hzero := zero_mem_roundedLayerIndices hρ hρ_lt
  have hsum : 0 <
      ∑ k ∈ roundedLayerIndices ρ,
        ((2 * k + 1 : ℕ) : ℝ) * (roundedLayerThreshold ρ k / A) := by
    have hsingle := Finset.single_le_sum
      (s := roundedLayerIndices ρ)
      (f := fun k => ((2 * k + 1 : ℕ) : ℝ) *
        (roundedLayerThreshold ρ k / A))
      (fun k hk => mul_nonneg (by positivity)
        (div_nonneg (roundedLayerThreshold_pos hρ hk).le hA.le)) hzero
    norm_num at hsingle ⊢
    exact (div_pos (roundedLayerThreshold_zero_pos hρ hρ_lt) hA).trans_le hsingle
  rw [roundedDerivativeWeight]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.2 (by positivity))) hsum

/-- The zeroth admissible layer has the smallest positive threshold. -/
lemma roundedLayerThreshold_zero_le {ρ : ℝ} (hρ : 0 < ρ) {k : ℕ}
    (hk : k ∈ roundedLayerIndices ρ) :
    roundedLayerThreshold ρ 0 ≤ roundedLayerThreshold ρ k := by
  rw [roundedLayerThreshold, roundedLayerThreshold]
  gcongr
  apply Real.artanh_le_artanh
  · norm_num
    linarith
  · exact (mem_roundedLayerIndices_iff hρ k).mp hk
  · have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    nlinarith

/-- Every admissible layer tail is controlled by the common zeroth-layer exponential
rate. -/
lemma gaussianUpperTail_layer_le_common_exp {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hh : 0 < h) {k : ℕ}
    (hk : k ∈ roundedLayerIndices ρ) :
    gaussianUpperTail (roundedLayerThreshold ρ k / (A * Real.sqrt h)) ≤
      Real.exp (-(roundedLayerThreshold ρ 0 ^ 2 / (2 * A ^ 2)) / h) := by
  have hzero : 0 ∈ roundedLayerIndices ρ := by
    rw [mem_roundedLayerIndices_iff hρ]
    have hadm := (mem_roundedLayerIndices_iff hρ k).mp hk
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    norm_num at *
    nlinarith
  have hb0 : 0 ≤ roundedLayerThreshold ρ 0 :=
    (roundedLayerThreshold_pos hρ hzero).le
  have hbk : 0 ≤ roundedLayerThreshold ρ k :=
    (roundedLayerThreshold_pos hρ hk).le
  have hb_le := roundedLayerThreshold_zero_le hρ hk
  have hb_sq : roundedLayerThreshold ρ 0 ^ 2 ≤ roundedLayerThreshold ρ k ^ 2 := by
    nlinarith
  calc
    gaussianUpperTail (roundedLayerThreshold ρ k / (A * Real.sqrt h)) ≤
        Real.exp (-(roundedLayerThreshold ρ k / (A * Real.sqrt h)) ^ 2 / 2) :=
      gaussianUpperTail_le_exp_neg_sq_div_two
        (div_nonneg hbk (mul_nonneg hA.le (Real.sqrt_nonneg _)))
    _ ≤ Real.exp (-(roundedLayerThreshold ρ 0 ^ 2 / (2 * A ^ 2)) / h) := by
      apply Real.exp_le_exp.mpr
      rw [div_pow, mul_pow, Real.sq_sqrt hh.le]
      field_simp [hA.ne', hh.ne']
      nlinarith

/-- Every admissible layer density is controlled by the common zeroth-layer
exponential rate. -/
lemma gaussianPDFReal_layer_le_common_exp {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hh : 0 < h) {k : ℕ}
    (hk : k ∈ roundedLayerIndices ρ) :
    gaussianPDFReal 0 1 (roundedLayerThreshold ρ k / (A * Real.sqrt h)) ≤
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(roundedSmallRate A ρ) / h) := by
  have hzero : 0 ∈ roundedLayerIndices ρ := by
    rw [mem_roundedLayerIndices_iff hρ]
    have hadm := (mem_roundedLayerIndices_iff hρ k).mp hk
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    norm_num at *
    nlinarith
  have hb0 : 0 ≤ roundedLayerThreshold ρ 0 :=
    (roundedLayerThreshold_pos hρ hzero).le
  have hbk : 0 ≤ roundedLayerThreshold ρ k :=
    (roundedLayerThreshold_pos hρ hk).le
  have hb_le := roundedLayerThreshold_zero_le hρ hk
  have hb_sq : roundedLayerThreshold ρ 0 ^ 2 ≤ roundedLayerThreshold ρ k ^ 2 := by
    nlinarith
  rw [gaussianPDFReal_zero_one_eq, roundedSmallRate]
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    rw [div_pow, mul_pow, Real.sq_sqrt hh.le]
    field_simp [hA.ne', hh.ne']
    nlinarith
  · exact inv_nonneg.mpr (Real.sqrt_nonneg _)

/-- The square of an integer magnitude is the sum of the odd layer weights below it. -/
lemma sq_eq_sum_odd_below_natAbs (z : ℤ) :
    (z : ℝ) ^ 2 =
      ∑ k ∈ Finset.range z.natAbs, (((2 * k + 1 : ℕ) : ℝ)) := by
  have hodd : ∀ n : ℕ, (∑ k ∈ Finset.range n, (2 * k + 1 : ℕ)) = n ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  rw [show (∑ k ∈ Finset.range z.natAbs, (((2 * k + 1 : ℕ) : ℝ))) =
      ((z.natAbs : ℕ) : ℝ) ^ 2 by exact_mod_cast hodd z.natAbs]
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-- Pointwise odd-layer decomposition of the squared unit-grid rounding map. -/
lemma Q₁_sq_eq_sum_odd (u : ℝ) :
    (Q₁ u : ℝ) ^ 2 =
      ∑ k ∈ Finset.range (Q₁ u).natAbs, (((2 * k + 1 : ℕ) : ℝ)) :=
  sq_eq_sum_odd_below_natAbs (Q₁ u)

/-- A rounding layer occurs exactly when the input crosses its half-integer boundary. -/
lemma lt_natAbs_Q₁_iff (u : ℝ) (k : ℕ) :
    k < (Q₁ u).natAbs ↔ (k : ℝ) + 1 / 2 < |u| := by
  have habs : |(Q₁ u : ℝ)| = (⌈|u| - 2⁻¹⌉ : ℤ) :=
    abs_Q₁_eq_ceil_abs_sub u
  constructor
  · intro hk
    have hkreal : (k : ℝ) < |(Q₁ u : ℝ)| := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (show
        ((k : ℕ) : ℝ) < (((Q₁ u).natAbs : ℕ) : ℝ) by exact_mod_cast hk)
    rw [habs] at hkreal
    have hkceil : (k : ℤ) < ⌈|u| - 2⁻¹⌉ := by exact_mod_cast hkreal
    have := Int.lt_ceil.mp hkceil
    norm_num at *
    linarith
  · intro hk
    have hkbase : (k : ℝ) < |u| - 2⁻¹ := by
      norm_num at *
      linarith
    have hkceil : (k : ℤ) < ⌈|u| - 2⁻¹⌉ := Int.lt_ceil.mpr hkbase
    have hkreal : (k : ℝ) < |(Q₁ u : ℝ)| := by
      rw [habs]
      exact_mod_cast hkceil
    have hkabs : (k : ℤ) < |Q₁ u| := by exact_mod_cast hkreal
    have hknat : (k : ℤ) < ((Q₁ u).natAbs : ℤ) := by
      simpa only [Int.natCast_natAbs] using hkabs
    exact_mod_cast hknat

/-- Oddness and monotonicity identify the magnitude of `tanh` with `tanh` of the
magnitude. -/
lemma abs_tanh_eq_tanh_abs (x : ℝ) : |Real.tanh x| = Real.tanh |x| := by
  by_cases hx : 0 ≤ x
  · have ht : 0 ≤ Real.tanh x := by
      have := strictMono_tanh_light.monotone hx
      simpa using this
    rw [abs_of_nonneg hx, abs_of_nonneg ht]
  · have hx' : x < 0 := not_le.mp hx
    have ht : Real.tanh x ≤ 0 := by
      have := strictMono_tanh_light.monotone hx'.le
      simpa using this
    rw [abs_of_neg hx', abs_of_nonpos ht, ← Real.tanh_neg]

/-- The preimage of an admissible rounded layer is the corresponding `artanh` threshold. -/
lemma abs_inv_mul_tanh_gt_iff {ρ : ℝ} (hρ : 0 < ρ) {k : ℕ}
    (hk : ρ * ((k : ℝ) + 1 / 2) < 1) (x : ℝ) :
    (k : ℝ) + 1 / 2 < |ρ⁻¹ * Real.tanh (ρ * x)| ↔
      roundedLayerThreshold ρ k < |x| := by
  have hkpos : 0 < ρ * ((k : ℝ) + 1 / 2) := by positivity
  have hmem : ρ * ((k : ℝ) + 1 / 2) ∈ Set.Ioo (-1 : ℝ) 1 :=
    ⟨by linarith, hk⟩
  rw [abs_mul, abs_inv, abs_of_pos hρ, abs_tanh_eq_tanh_abs, abs_mul,
    abs_of_pos hρ, lt_inv_mul_iff₀ hρ, roundedLayerThreshold,
    inv_mul_lt_iff₀ hρ]
  constructor
  · intro h
    apply strictMono_tanh_light.lt_iff_lt.mp
    rw [Real.tanh_artanh hmem]
    exact h
  · intro h
    have ht := strictMono_tanh_light.lt_iff_lt.mpr h
    rwa [Real.tanh_artanh hmem] at ht

/-- Every layer activated by the bounded rounded argument belongs to the finite
admissible layer set. -/
lemma active_layer_mem_roundedLayerIndices {ρ : ℝ} (hρ : 0 < ρ) {x : ℝ} {k : ℕ}
    (hk : (k : ℝ) + 1 / 2 < |ρ⁻¹ * Real.tanh (ρ * x)|) :
    k ∈ roundedLayerIndices ρ := by
  rw [mem_roundedLayerIndices_iff hρ]
  rw [abs_mul, abs_inv, abs_of_pos hρ] at hk
  have hmul :
      ρ * ((k : ℝ) + 1 / 2) < |Real.tanh (ρ * x)| :=
    (lt_inv_mul_iff₀ hρ).mp hk
  exact hmul.trans (Real.abs_tanh_lt_one _)

/-- Pointwise finite-layer formula for the rounded coordinate square. -/
lemma Q₁_inv_tanh_sq_eq_sum_layers {ρ : ℝ} (hρ : 0 < ρ) (x : ℝ) :
    (Q₁ (ρ⁻¹ * Real.tanh (ρ * x)) : ℝ) ^ 2 =
      ∑ k ∈ roundedLayerIndices ρ,
        if roundedLayerThreshold ρ k < |x| then ((2 * k + 1 : ℕ) : ℝ) else 0 := by
  let u : ℝ := ρ⁻¹ * Real.tanh (ρ * x)
  let S : Finset ℕ := Finset.range (Q₁ u).natAbs
  have hsubset : S ⊆ roundedLayerIndices ρ := by
    intro k hk
    apply active_layer_mem_roundedLayerIndices hρ
    exact (lt_natAbs_Q₁_iff u k).mp (Finset.mem_range.mp hk)
  rw [show (Q₁ (ρ⁻¹ * Real.tanh (ρ * x)) : ℝ) ^ 2 =
      ∑ k ∈ S, (((2 * k + 1 : ℕ) : ℝ)) by
        simpa [u, S] using Q₁_sq_eq_sum_odd u]
  calc
    (∑ k ∈ S, (((2 * k + 1 : ℕ) : ℝ))) =
        ∑ k ∈ S,
          if roundedLayerThreshold ρ k < |x| then ((2 * k + 1 : ℕ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hu := (lt_natAbs_Q₁_iff u k).mp (Finset.mem_range.mp hk)
      have hadm := (mem_roundedLayerIndices_iff hρ k).mp (hsubset hk)
      have hthreshold := (abs_inv_mul_tanh_gt_iff hρ hadm x).mp (by simpa [u] using hu)
      rw [if_pos hthreshold]
    _ = ∑ k ∈ roundedLayerIndices ρ,
          if roundedLayerThreshold ρ k < |x| then ((2 * k + 1 : ℕ) : ℝ) else 0 := by
      apply Finset.sum_subset hsubset
      intro k hkK hkS
      have hadm := (mem_roundedLayerIndices_iff hρ k).mp hkK
      have hnot : ¬roundedLayerThreshold ρ k < |x| := by
        intro hthreshold
        have hu := (abs_inv_mul_tanh_gt_iff hρ hadm x).mpr hthreshold
        have hs : k ∈ S := Finset.mem_range.mpr
          ((lt_natAbs_Q₁_iff u k).mpr (by simpa [u] using hu))
        exact hkS hs
      rw [if_neg hnot]

/-- By symmetry, the standard-Gaussian absolute tail is twice its upper tail. -/
lemma gaussianReal_abs_gt_eq_two_mul_upperTail {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real {g : ℝ | t < |g|} = 2 * gaussianUpperTail t := by
  let μ := gaussianReal 0 1
  have hset : {g : ℝ | t < |g|} = Set.Iio (-t) ∪ Set.Ioi t := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
    by_cases hg : 0 ≤ g
    · rw [abs_of_nonneg hg]
      constructor
      · exact fun h => Or.inr h
      · rintro (h | h)
        · linarith
        · exact h
    · have hg' : g < 0 := not_le.mp hg
      rw [abs_of_neg hg']
      constructor
      · exact fun h => Or.inl (by linarith)
      · rintro (h | h)
        · linarith
        · linarith
  have hsymm : μ (Set.Iio (-t)) = μ (Set.Ioi t) := by
    have hmap := congrArg (fun ν : Measure ℝ => ν (Set.Iio (-t)))
      (gaussianReal_map_neg (μ := 0) (v := 1))
    rw [Measure.map_apply (by fun_prop) measurableSet_Iio] at hmap
    simpa [μ] using hmap.symm
  have hsymmReal : μ.real (Set.Iio (-t)) = μ.real (Set.Ioi t) := by
    exact congrArg ENNReal.toReal hsymm
  have hdisj : Disjoint (Set.Iio (-t)) (Set.Ioi t) :=
    Set.disjoint_left.2 fun x hx hy => by
      change x < -t at hx
      change t < x at hy
      linarith
  rw [hset, measureReal_union hdisj measurableSet_Ioi, hsymmReal]
  simp [gaussianUpperTail, μ, two_mul]

/-- Scaling a standard Gaussian converts an absolute threshold into the corresponding
upper-tail argument. -/
lemma gaussianReal_abs_scale_gt {A h b : ℝ} (hA : 0 < A) (hh : 0 < h) (hb : 0 ≤ b) :
    (gaussianReal 0 1).real {g : ℝ | b < |A * Real.sqrt h * g|} =
      2 * gaussianUpperTail (b / (A * Real.sqrt h)) := by
  have hs : 0 < A * Real.sqrt h := mul_pos hA (Real.sqrt_pos.2 hh)
  have hset : {g : ℝ | b < |A * Real.sqrt h * g|} =
      {g : ℝ | b / (A * Real.sqrt h) < |g|} := by
    ext g
    simp only [Set.mem_setOf_eq]
    rw [show A * Real.sqrt h * g = (A * Real.sqrt h) * g by ring,
      abs_mul, abs_of_pos hs]
    constructor
    · intro hscale
      apply (div_lt_iff₀ hs).2
      simpa [mul_comm] using hscale
    · intro hdiv
      have hscale := (div_lt_iff₀ hs).1 hdiv
      simpa [mul_comm] using hscale
  rw [hset]
  exact gaussianReal_abs_gt_eq_two_mul_upperTail (div_nonneg hb hs.le)

/-- First exact formula in `eq:subcritical-layer-formulas-exact`: the rounded mean map
is a finite sum of Gaussian layer tails. -/
lemma roundedMeanMap_eq_sum_upperTail {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hh : 0 < h) :
    roundedMeanMap A ρ h =
      2 * ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        gaussianUpperTail (roundedLayerThreshold ρ k / (A * Real.sqrt h)) := by
  let μ := gaussianReal 0 1
  have hpoint : ∀ g : ℝ,
      ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) : ℝ)) ^ 2 =
        ∑ k ∈ roundedLayerIndices ρ,
          if roundedLayerThreshold ρ k < |A * Real.sqrt h * g|
          then ((2 * k + 1 : ℕ) : ℝ) else 0 := by
    intro g
    simpa only [mul_assoc] using Q₁_inv_tanh_sq_eq_sum_layers hρ (A * Real.sqrt h * g)
  rw [roundedMeanMap]
  conv_lhs =>
    enter [2, g]
    rw [hpoint g]
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    let S : Set ℝ := {g : ℝ | roundedLayerThreshold ρ k < |A * Real.sqrt h * g|}
    have hS : MeasurableSet S := by
      exact measurableSet_lt measurable_const (by fun_prop)
    have hind : (fun g : ℝ =>
        if roundedLayerThreshold ρ k < |A * Real.sqrt h * g|
        then ((2 * k + 1 : ℕ) : ℝ) else 0) =
        S.indicator (fun _ => ((2 * k + 1 : ℕ) : ℝ)) := by
      funext g
      simp [S, Set.indicator]
    rw [hind, integral_indicator_const _ hS, smul_eq_mul]
    rw [gaussianReal_abs_scale_gt hA hh (roundedLayerThreshold_pos hρ hk).le]
    ring
  · intro k hk
    let S : Set ℝ := {g : ℝ | roundedLayerThreshold ρ k < |A * Real.sqrt h * g|}
    have hS : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
    have hind : (fun g : ℝ =>
        if roundedLayerThreshold ρ k < |A * Real.sqrt h * g|
        then ((2 * k + 1 : ℕ) : ℝ) else 0) =
        S.indicator (fun _ => ((2 * k + 1 : ℕ) : ℝ)) := by
      funext g
      simp [S, Set.indicator]
    rw [hind]
    exact (integrable_const _).integrableOn.integrable_indicator hS

/-- The rounded mean map is real analytic at every positive radius. -/
@[fun_prop]
lemma analyticAt_roundedMeanMap {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hh : 0 < h) :
    AnalyticAt ℝ (roundedMeanMap A ρ) h := by
  let S : ℝ → ℝ := fun u =>
    2 * ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
      gaussianUpperTail
        (roundedLayerThreshold ρ k / (A * Real.sqrt u))
  have hS : AnalyticAt ℝ S h := by
    dsimp only [S]
    have hsqrt : AnalyticAt ℝ Real.sqrt h :=
      analyticAt_real_sqrt_of_pos hh
    have hdenom :
        AnalyticAt ℝ (fun u : ℝ => A * Real.sqrt u) h :=
      AnalyticAt.fun_mul analyticAt_const hsqrt
    have hdenomNe : A * Real.sqrt h ≠ 0 :=
      mul_ne_zero hA.ne' (Real.sqrt_pos.2 hh).ne'
    have hinner (k : ℕ) :
        AnalyticAt ℝ
          (fun u : ℝ =>
            roundedLayerThreshold ρ k / (A * Real.sqrt u)) h :=
      AnalyticAt.fun_div analyticAt_const hdenom hdenomNe
    have hterm (k : ℕ) :
        AnalyticAt ℝ
          (fun u : ℝ => ((2 * k + 1 : ℕ) : ℝ) *
            gaussianUpperTail
              (roundedLayerThreshold ρ k / (A * Real.sqrt u))) h :=
      AnalyticAt.fun_mul analyticAt_const
        ((analyticAt_gaussianUpperTail _).comp (hinner k))
    have hsum :
        AnalyticAt ℝ
          (fun u : ℝ =>
            ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
              gaussianUpperTail
                (roundedLayerThreshold ρ k / (A * Real.sqrt u))) h :=
      Finset.analyticAt_fun_sum (roundedLayerIndices ρ) fun k _ => hterm k
    exact AnalyticAt.fun_mul analyticAt_const hsum
  apply hS.congr
  filter_upwards [Ioi_mem_nhds hh] with u hu
  exact (roundedMeanMap_eq_sum_upperTail hA hρ hu).symm

/-- The rounded mean map vanishes on the nonpositive half-line. -/
lemma roundedMeanMap_eq_zero_of_nonpos (A ρ : ℝ) {h : ℝ} (hh : h ≤ 0) :
    roundedMeanMap A ρ h = 0 := by
  have hQ : Q₁ (0 : ℝ) = 0 := (Q₁_zero_iff 0).mpr (by norm_num)
  simp [roundedMeanMap, Real.sqrt_eq_zero_of_nonpos hh, hQ]

/-- The rounded mean map is nondecreasing on the nonnegative half-line. -/
lemma monotoneOn_roundedMeanMap_Ici {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) :
    MonotoneOn (roundedMeanMap A ρ) (Set.Ici 0) := by
  intro x hx y hy hxy
  by_cases hxzero : x = 0
  · rw [hxzero, roundedMeanMap_zero]
    exact integral_nonneg fun g => by positivity
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hypos : 0 < y := hxpos.trans_le hxy
  rw [roundedMeanMap_eq_sum_upperTail hA hρ hxpos,
    roundedMeanMap_eq_sum_upperTail hA hρ hypos]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply antitone_gaussianUpperTail
  have hsqrt : Real.sqrt x ≤ Real.sqrt y :=
    Real.sqrt_le_sqrt hxy
  have hdenomPos : 0 < A * Real.sqrt x :=
    mul_pos hA (Real.sqrt_pos.2 hxpos)
  have hdenom :
      A * Real.sqrt x ≤ A * Real.sqrt y :=
    mul_le_mul_of_nonneg_left hsqrt hA.le
  exact div_le_div_of_nonneg_left
    (roundedLayerThreshold_pos hρ hk).le hdenomPos hdenom

/-- The rounded mean map is globally nondecreasing, with its flat extension on
the nonpositive half-line. -/
lemma monotone_roundedMeanMap {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) :
    Monotone (roundedMeanMap A ρ) := by
  intro x y hxy
  by_cases hy : y ≤ 0
  · rw [roundedMeanMap_eq_zero_of_nonpos A ρ hy,
      roundedMeanMap_eq_zero_of_nonpos A ρ (hxy.trans hy)]
  by_cases hx : x ≤ 0
  · rw [roundedMeanMap_eq_zero_of_nonpos A ρ hx]
    exact integral_nonneg fun g => by positivity
  exact monotoneOn_roundedMeanMap_Ici hA hρ
    (le_of_not_ge hx) (le_trans (le_of_not_ge hx) hxy) hxy

/-- The explicit finite layer sum for the positive-radius derivative of the rounded
mean map. -/
noncomputable def roundedMeanMapDerivative (A ρ h : ℝ) : ℝ :=
  ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
    (roundedLayerThreshold ρ k / (A * h ^ (3 / 2 : ℝ)) *
      gaussianPDFReal 0 1 (roundedLayerThreshold ρ k / (A * Real.sqrt h)))

/-- Second exact formula in `eq:subcritical-layer-formulas-exact`: the derivative of
the rounded mean map is the finite sum of differentiated Gaussian layers. -/
lemma hasDerivAt_roundedMeanMap {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hh : 0 < h) :
    HasDerivAt (roundedMeanMap A ρ) (roundedMeanMapDerivative A ρ h) h := by
  rw [roundedMeanMapDerivative]
  have hsum : HasDerivAt
      (fun u => ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        (2 * gaussianUpperTail (roundedLayerThreshold ρ k / (A * Real.sqrt u))))
      (∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        (roundedLayerThreshold ρ k / (A * h ^ (3 / 2 : ℝ)) *
          gaussianPDFReal 0 1
            (roundedLayerThreshold ρ k / (A * Real.sqrt h)))) h := by
    apply HasDerivAt.fun_sum
    intro k hk
    exact (hasDerivAt_two_mul_gaussianUpperTail_div_sqrt hA hh).const_mul
      (((2 * k + 1 : ℕ) : ℝ))
  apply hsum.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hh] with u hu
  rw [roundedMeanMap_eq_sum_upperTail hA hρ hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- On the positive half-line, the actual derivative agrees with the explicit layer sum. -/
lemma deriv_roundedMeanMap_eq {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hh : 0 < h) :
    deriv (roundedMeanMap A ρ) h = roundedMeanMapDerivative A ρ h :=
  (hasDerivAt_roundedMeanMap hA hρ hh).deriv

/-- The explicit rounded-map derivative is continuous at every positive radius. -/
lemma continuousOn_roundedMeanMapDerivative_Ioi {A ρ : ℝ} (hA : 0 < A) :
    ContinuousOn (roundedMeanMapDerivative A ρ) (Set.Ioi 0) := by
  intro h hh
  apply ContinuousAt.continuousWithinAt
  unfold roundedMeanMapDerivative
  apply tendsto_finsetSum
  intro k hk
  have hpow : A * h ^ (3 / 2 : ℝ) ≠ 0 :=
    mul_ne_zero hA.ne' (Real.rpow_pos_of_pos hh _).ne'
  have hsqrt : A * Real.sqrt h ≠ 0 :=
    mul_ne_zero hA.ne' (Real.sqrt_pos.2 hh).ne'
  have hrpow : h ≠ 0 ∨ 0 ≤ (3 / 2 : ℝ) := Or.inl hh.ne'
  have hpdf : Continuous (gaussianPDFReal 0 1) := by
    rw [gaussianPDFReal_def]
    fun_prop
  change ContinuousAt
    (fun u => ((2 * k + 1 : ℕ) : ℝ) *
      (roundedLayerThreshold ρ k / (A * u ^ (3 / 2 : ℝ)) *
        gaussianPDFReal 0 1 (roundedLayerThreshold ρ k / (A * Real.sqrt u)))) h
  have hleft : ContinuousAt
      (fun u => roundedLayerThreshold ρ k / (A * u ^ (3 / 2 : ℝ))) h := by
    fun_prop
  have harg : ContinuousAt
      (fun u => roundedLayerThreshold ρ k / (A * Real.sqrt u)) h := by
    fun_prop
  exact continuousAt_const.mul (hleft.mul (hpdf.continuousAt.comp harg))

/-- The rounded mean map is continuous at every positive radius. -/
lemma continuousOn_roundedMeanMap_Ioi {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) :
    ContinuousOn (roundedMeanMap A ρ) (Set.Ioi 0) := by
  intro h hh
  exact (hasDerivAt_roundedMeanMap hA hρ hh).continuousAt.continuousWithinAt

/-- The rounded mean map is strictly positive at every positive radius when the zeroth
rounding layer is admissible. -/
lemma roundedMeanMap_pos {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hh : 0 < h) :
    0 < roundedMeanMap A ρ h := by
  have hzero : 0 ∈ roundedLayerIndices ρ :=
    zero_mem_roundedLayerIndices hρ hρ_lt
  have hsum :
      gaussianUpperTail (roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ≤
        ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
          gaussianUpperTail (roundedLayerThreshold ρ k / (A * Real.sqrt h)) := by
    have hsingle := Finset.single_le_sum
      (s := roundedLayerIndices ρ)
      (f := fun k => ((2 * k + 1 : ℕ) : ℝ) *
        gaussianUpperTail (roundedLayerThreshold ρ k / (A * Real.sqrt h)))
      (fun k hk => mul_nonneg (by positivity) (gaussianUpperTail_pos _).le) hzero
    simpa using hsingle
  rw [roundedMeanMap_eq_sum_upperTail hA hρ hh]
  exact mul_pos (by norm_num) ((gaussianUpperTail_pos _).trans_le hsum)

/-- The rounded mean map has the paper's exponential small-radius bound. -/
lemma roundedMeanMap_le_weight_mul_exp {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hh : 0 < h) :
    roundedMeanMap A ρ h ≤
      roundedLayerWeight ρ * Real.exp (-(roundedSmallRate A ρ) / h) := by
  rw [roundedMeanMap_eq_sum_upperTail hA hρ hh,
    roundedLayerWeight, roundedSmallRate]
  have hsum :
      (∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        gaussianUpperTail (roundedLayerThreshold ρ k / (A * Real.sqrt h))) ≤
      ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        Real.exp (-(roundedLayerThreshold ρ 0 ^ 2 / (2 * A ^ 2)) / h) := by
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left
      (gaussianUpperTail_layer_le_common_exp hA hρ hh hk) (by positivity)
  calc
    2 * (∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        gaussianUpperTail (roundedLayerThreshold ρ k / (A * Real.sqrt h))) ≤
      2 * ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        Real.exp (-(roundedLayerThreshold ρ 0 ^ 2 / (2 * A ^ 2)) / h) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (2 * ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ)) *
        Real.exp (-(roundedLayerThreshold ρ 0 ^ 2 / (2 * A ^ 2)) / h) := by
      rw [← Finset.sum_mul]
      ring

/-- The explicit derivative has the paper's preliminary
`h⁻³ᐟ² exp (-c / h)` small-radius bound. -/
lemma roundedMeanMapDerivative_le_weight_mul_rpow_exp {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hh : 0 < h) :
    roundedMeanMapDerivative A ρ h ≤
      roundedDerivativeWeight A ρ * h ^ (-3 / 2 : ℝ) *
        Real.exp (-(roundedSmallRate A ρ) / h) := by
  rw [roundedMeanMapDerivative]
  have hsum :
      (∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        (roundedLayerThreshold ρ k / (A * h ^ (3 / 2 : ℝ)) *
          gaussianPDFReal 0 1
            (roundedLayerThreshold ρ k / (A * Real.sqrt h)))) ≤
      ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        (roundedLayerThreshold ρ k / (A * h ^ (3 / 2 : ℝ)) *
          ((Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(roundedSmallRate A ρ) / h))) := by
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left
      (gaussianPDFReal_layer_le_common_exp hA hρ hh hk)
    exact div_nonneg (roundedLayerThreshold_pos hρ hk).le
      (mul_nonneg hA.le (Real.rpow_nonneg hh.le _))
  calc
    (∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
        (roundedLayerThreshold ρ k / (A * h ^ (3 / 2 : ℝ)) *
          gaussianPDFReal 0 1
            (roundedLayerThreshold ρ k / (A * Real.sqrt h)))) ≤
        ∑ k ∈ roundedLayerIndices ρ, ((2 * k + 1 : ℕ) : ℝ) *
          (roundedLayerThreshold ρ k / (A * h ^ (3 / 2 : ℝ)) *
            ((Real.sqrt (2 * Real.pi))⁻¹ *
              Real.exp (-(roundedSmallRate A ρ) / h))) := hsum
    _ = roundedDerivativeWeight A ρ * h ^ (-3 / 2 : ℝ) *
          Real.exp (-(roundedSmallRate A ρ) / h) := by
      rw [roundedDerivativeWeight]
      have hpow : h ^ (3 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hh _).ne'
      have hinv : h ^ (-3 / 2 : ℝ) = (h ^ (3 / 2 : ℝ))⁻¹ := by
        rw [← Real.rpow_neg (le_of_lt hh)]
        congr 1
        ring
      rw [hinv, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      field_simp [hA.ne', hpow]

/-- The two small-radius estimates in
`eq:subcritical-fixed-small-radius-map-derivative`, with shared positive constants. -/
lemma exists_roundedMeanMap_small_radius_bounds {A ρ r : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (_hr : 0 < r) (hr_lt : r < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ r →
      roundedMeanMap A ρ h ≤ C * Real.exp (-c / h) ∧
      deriv (roundedMeanMap A ρ) h ≤ C * h ^ (-2 : ℝ) * Real.exp (-c / h) := by
  let C := max (roundedLayerWeight ρ) (roundedDerivativeWeight A ρ)
  have hmapWeight : 0 < roundedLayerWeight ρ :=
    roundedLayerWeight_pos hρ hρ_lt
  have hderivWeight : 0 < roundedDerivativeWeight A ρ :=
    roundedDerivativeWeight_pos hA hρ hρ_lt
  have hC : 0 < C := hmapWeight.trans_le (le_max_left _ _)
  refine ⟨roundedSmallRate A ρ, C,
    roundedSmallRate_pos hA hρ hρ_lt, hC, ?_⟩
  intro h hh hhr
  have hh_one : h ≤ 1 := hhr.trans hr_lt.le
  have hrpow :
      h ^ (-3 / 2 : ℝ) ≤ h ^ (-2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_ge hh hh_one
    norm_num
  constructor
  · calc
      roundedMeanMap A ρ h ≤
          roundedLayerWeight ρ *
            Real.exp (-(roundedSmallRate A ρ) / h) :=
        roundedMeanMap_le_weight_mul_exp hA hρ hh
      _ ≤ C * Real.exp (-(roundedSmallRate A ρ) / h) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  · rw [deriv_roundedMeanMap_eq hA hρ hh]
    calc
      roundedMeanMapDerivative A ρ h ≤
          roundedDerivativeWeight A ρ * h ^ (-3 / 2 : ℝ) *
            Real.exp (-(roundedSmallRate A ρ) / h) :=
        roundedMeanMapDerivative_le_weight_mul_rpow_exp hA hρ hh
      _ ≤ C * h ^ (-3 / 2 : ℝ) *
            Real.exp (-(roundedSmallRate A ρ) / h) := by
        gcongr
        exact le_max_right _ _
      _ ≤ C * h ^ (-2 : ℝ) *
            Real.exp (-(roundedSmallRate A ρ) / h) := by
        gcongr

/-- On every positive compact radius interval, the rounded mean map has a uniform
strictly positive lower bound. -/
lemma exists_pos_le_roundedMeanMap_on_Icc {A ρ r R : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ m : ℝ, 0 < m ∧ ∀ h ∈ Set.Icc r R, m ≤ roundedMeanMap A ρ h := by
  have hne : (Set.Icc r R).Nonempty := Set.nonempty_Icc.mpr hrR
  have hcont : ContinuousOn (roundedMeanMap A ρ) (Set.Icc r R) :=
    (continuousOn_roundedMeanMap_Ioi hA hρ).mono fun h hh =>
      lt_of_lt_of_le hr hh.1
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  refine ⟨roundedMeanMap A ρ x,
    roundedMeanMap_pos hA hρ hρ_lt (lt_of_lt_of_le hr hx.1), hmin⟩

/-- On every positive compact radius interval, the rounded mean-map derivative has a
finite strictly positive upper bound. -/
lemma exists_pos_deriv_roundedMeanMap_le_on_Icc {A ρ r R : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ L : ℝ, 0 < L ∧ ∀ h ∈ Set.Icc r R, deriv (roundedMeanMap A ρ) h ≤ L := by
  have hne : (Set.Icc r R).Nonempty := Set.nonempty_Icc.mpr hrR
  have hcont : ContinuousOn (roundedMeanMapDerivative A ρ) (Set.Icc r R) :=
    (continuousOn_roundedMeanMapDerivative_Ioi hA).mono fun h hh =>
      lt_of_lt_of_le hr hh.1
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨max 1 (roundedMeanMapDerivative A ρ x),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro h hhmem
  rw [deriv_roundedMeanMap_eq hA hρ (lt_of_lt_of_le hr hhmem.1)]
  exact (hmax hhmem).trans (le_max_right _ _)

/-- The compact-radius bounds in `eq:subcritical-fixed-compact-bounds`, packaged with
the paper's two positive constants. -/
lemma exists_roundedMeanMap_compact_bounds {A ρ r R : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hr : 0 < r) (hrR : r ≤ R) :
    ∃ m L : ℝ, 0 < m ∧ 0 < L ∧ ∀ h ∈ Set.Icc r R,
      m ≤ roundedMeanMap A ρ h ∧ deriv (roundedMeanMap A ρ) h ≤ L := by
  obtain ⟨m, hm, hmle⟩ :=
    exists_pos_le_roundedMeanMap_on_Icc hA hρ hρ_lt hr hrR
  obtain ⟨L, hL, hderiv⟩ :=
    exists_pos_deriv_roundedMeanMap_le_on_Icc hA hρ hr hrR
  exact ⟨m, L, hm, hL, fun h hh => ⟨hmle h hh, hderiv h hh⟩⟩

end AbsorptionCutoff
