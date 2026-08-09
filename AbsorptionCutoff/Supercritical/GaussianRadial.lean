/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Chains
import AbsorptionCutoff.Estimates
import AbsorptionCutoff.InvariantSelection
import AbsorptionCutoff.MeanMap.Dynamics
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Moments.ComplexMGF

/-!
# Gaussian radial laws and Gamma negative moments

This module starts the radial-moment infrastructure used in the paper's
supercritical dimension cutoff. It identifies the squared norm of `gaussianVec N`
with a sum of independent squared standard Gaussians, the representation of
`χ_N²` that will be sent to the Gamma law with shape `N / 2` and rate `1 / 2`.

It also proves the analytic half of the exact negative-moment calculation:
the sharp integrability condition and Gamma-function integral for a negative
real power against a Gamma density.
-/

open MeasureTheory ProbabilityTheory BigOperators Filter Topology Set
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Squared Euclidean norm of a vector in `ℝ^N`. Under `gaussianVec N`, this is
the paper's `χ_N²`. -/
noncomputable def gaussianSquaredNorm (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  ∑ i, (g i) ^ 2

/-- Euclidean norm associated with `gaussianSquaredNorm`. This is explicit
because the default norm on the function space `Fin N → ℝ` is the sup norm. -/
noncomputable def gaussianEuclideanNorm (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  Real.sqrt (gaussianSquaredNorm N g)

lemma measurable_gaussianSquaredNorm (N : ℕ) : Measurable (gaussianSquaredNorm N) := by
  unfold gaussianSquaredNorm
  fun_prop

lemma gaussianSquaredNorm_nonneg (N : ℕ) (g : Fin N → ℝ) :
    0 ≤ gaussianSquaredNorm N g := by
  unfold gaussianSquaredNorm
  positivity

/-- Coordinatewise squaring sends the standard Gaussian product to the product
of the one-dimensional squared-Gaussian laws. -/
lemma map_coordinatewise_sq_gaussianVec (N : ℕ) :
    (gaussianVec N).map (fun g i => (g i) ^ 2) =
      Measure.pi (fun _ : Fin N => (gaussianReal 0 1).map (fun x : ℝ => x ^ 2)) := by
  unfold gaussianVec
  exact Measure.pi_map_pi (μ := fun _ : Fin N => gaussianReal 0 1)
    (f := fun _ : Fin N => fun x : ℝ => x ^ 2) (fun _ => by fun_prop)

/-- `χ_N²` is represented as the sum of `N` independent squared standard
Gaussians. This is the distributional bridge to the Gamma law with shape
`N / 2` and rate `1 / 2`. -/
lemma map_gaussianSquaredNorm_gaussianVec (N : ℕ) :
    (gaussianVec N).map (gaussianSquaredNorm N) =
      (Measure.pi (fun _ : Fin N => (gaussianReal 0 1).map (fun x : ℝ => x ^ 2))).map
        (fun y => ∑ i, y i) := by
  rw [← map_coordinatewise_sq_gaussianVec]
  rw [Measure.map_map]
  · congr 1
  · fun_prop
  · fun_prop

/-- MGF of a Gamma law on its interval of convergence. -/
lemma mgf_id_gammaMeasure_of_lt {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    mgf id (gammaMeasure a r) t = (r / (r - t)) ^ a := by
  have hpdf : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [mgf, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul hpdf
      (ae_of_all _ fun x => by simp [gammaPDF])]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), id_eq,
    smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ici 0) (f :=
    fun x : ℝ => gammaPDFReal a r x * Real.exp (t * x)) (by
      intro x hx
      rw [gammaPDFReal, if_neg]
      · simp
      · exact not_le.mpr (lt_of_not_ge hx))]
  rw [integral_Ici_eq_integral_Ioi]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun x => r ^ a / Real.Gamma a *
      (x ^ (a - 1) * Real.exp (-((r - t) * x))))]
  · rw [integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a) (r := r - t) ha (sub_pos.mpr ht)]
    rw [one_div, Real.inv_rpow (sub_pos.mpr ht).le]
    rw [Real.div_rpow hr.le (sub_pos.mpr ht).le]
    field_simp [(Real.Gamma_pos_of_pos ha).ne']
  · intro x hx
    have hx0 : 0 < x := hx
    simp only [gammaPDFReal, if_pos hx0.le]
    have hexp : Real.exp (-(r * x)) * Real.exp (t * x) =
        Real.exp (-((r - t) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexp]
    exact mul_assoc _ _ _

/-- MGF of the square of a standard real Gaussian. -/
lemma mgf_sq_gaussianReal_of_lt {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun x : ℝ => x ^ 2) (gaussianReal 0 1) t =
      ((1 / 2 : ℝ) / (1 / 2 - t)) ^ (1 / 2 : ℝ) := by
  rw [mgf, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
  change (∫ x : ℝ, (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) *
      Real.exp (t * x ^ 2)) =
    ((1 / 2 : ℝ) / (1 / 2 - t)) ^ (1 / 2 : ℝ)
  rw [show (fun x : ℝ => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) *
      Real.exp (t * x ^ 2)) =
      fun x => (√(2 * π))⁻¹ * Real.exp (-((1 / 2 - t) * x ^ 2)) by
    funext x
    have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (t * x ^ 2) =
        Real.exp (-((1 / 2 - t) * x ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexp]]
  rw [integral_const_mul]
  rw [show (∫ a : ℝ, Real.exp (-((1 / 2 - t) * a ^ 2))) =
      √(π / (1 / 2 - t)) by
    convert integral_gaussian (1 / 2 - t) using 1
    ring_nf]
  have hden : 0 < 1 / 2 - t := sub_pos.mpr ht
  rw [show ((1 / 2 : ℝ) / (1 / 2 - t)) ^ (1 / 2 : ℝ) =
      √((1 / 2) / (1 / 2 - t)) by rw [Real.sqrt_eq_rpow]]
  rw [inv_mul_eq_div]
  rw [← Real.sqrt_div (div_nonneg Real.pi_pos.le hden.le)]
  congr 1
  field_simp [ne_of_gt hden, ne_of_gt Real.pi_pos]

lemma integrable_exp_mul_id_gammaMeasure_of_lt {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure a r) := by
  have hpdf : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integrable_withDensity_iff hpdf
    (ae_of_all _ fun x => by simp [gammaPDF])]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  let f : ℝ → ℝ := fun x =>
    Real.exp (t * x) * gammaPDFReal a r x
  have hbase :
      IntegrableOn (fun x : ℝ => r ^ a / Real.Gamma a *
        (x ^ (a - 1) * Real.exp (-((r - t) * x)))) (Ioi 0) := by
    have hb : IntegrableOn (fun x : ℝ => r ^ a / Real.Gamma a *
        (x ^ (a - 1) * Real.exp (-(r - t) * x ^ (1 : ℝ)))) (Ioi 0) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := a - 1) (b := r - t)
        (by linarith) le_rfl (sub_pos.mpr ht)).const_mul
          (r ^ a / Real.Gamma a)
    refine hb.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    congr 2
    ring_nf
  have hici : IntegrableOn f (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine hbase.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := hx
    simp only [f, gammaPDFReal, if_pos hx0.le]
    have hexp : Real.exp (t * x) * Real.exp (-(r * x)) =
        Real.exp (-((r - t) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    symm
    calc
      Real.exp (t * x) *
          (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
          r ^ a / Real.Gamma a * x ^ (a - 1) *
            (Real.exp (t * x) * Real.exp (-(r * x))) := by ring
      _ = r ^ a / Real.Gamma a *
          (x ^ (a - 1) * Real.exp (-((r - t) * x))) := by rw [hexp]; ring
  refine (hici.integrable_indicator measurableSet_Ici).congr (ae_of_all _ fun x => ?_)
  by_cases hx : 0 ≤ x
  · simp [f, hx]
  · simp [f, gammaPDFReal, hx]

lemma integrable_exp_mul_sq_gaussianReal_of_lt {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff (by fun_prop)
    (ae_of_all _ fun x => by simp [gaussianPDF])]
  simp only [gaussianPDF]
  simp_rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  have hbase : Integrable (fun x : ℝ => Real.exp (-((1 / 2 - t) * x ^ 2))) := by
    convert integrable_exp_neg_mul_sq (sub_pos.mpr ht) using 1
    ring_nf
  refine hbase.const_mul (√(2 * π))⁻¹ |>.congr (ae_of_all _ fun x => ?_)
  have hexp : Real.exp (t * x ^ 2) * Real.exp (-(x ^ 2) / 2) =
      Real.exp (-((1 / 2 - t) * x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  symm
  calc
    Real.exp (t * x ^ 2) * ((√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2)) =
        (√(2 * π))⁻¹ *
          (Real.exp (t * x ^ 2) * Real.exp (-(x ^ 2) / 2)) := by ring
    _ = (√(2 * π))⁻¹ * Real.exp (-((1 / 2 - t) * x ^ 2)) := by rw [hexp]

/-- Equality of MGFs on an open interval around zero determines the pushforward law. -/
lemma map_eq_of_mgf_eq_on_Ioo
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {μ' : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {X : Ω → ℝ} {Y : Ω' → ℝ} {a b : ℝ}
    (hX : Measurable X) (hY : Measurable Y) (ha : a < 0) (hb : 0 < b)
    (hXint : ∀ t ∈ Set.Ioo a b, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hYint : ∀ t ∈ Set.Ioo a b, Integrable (fun ω => Real.exp (t * Y ω)) μ')
    (hmgf : Set.EqOn (mgf X μ) (mgf Y μ') (Set.Ioo a b)) :
    μ.map X = μ'.map Y := by
  let D : Set ℂ := {z | z.re ∈ Set.Ioo a b}
  have hXsub : D ⊆ {z | z.re ∈ interior (integrableExpSet X μ)} := by
    intro z hz
    refine mem_interior_iff_mem_nhds.mpr (mem_of_superset (Ioo_mem_nhds hz.1 hz.2) ?_)
    intro t ht
    exact hXint t ht
  have hYsub : D ⊆ {z | z.re ∈ interior (integrableExpSet Y μ')} := by
    intro z hz
    refine mem_interior_iff_mem_nhds.mpr (mem_of_superset (Ioo_mem_nhds hz.1 hz.2) ?_)
    intro t ht
    exact hYint t ht
  have hCX : AnalyticOnNhd ℂ (complexMGF X μ) D :=
    analyticOnNhd_complexMGF.mono hXsub
  have hCY : AnalyticOnNhd ℂ (complexMGF Y μ') D :=
    analyticOnNhd_complexMGF.mono hYsub
  have h_real : ∃ᶠ x : ℝ in 𝓝[≠] 0, complexMGF X μ x = complexMGF Y μ' x := by
    apply Filter.Eventually.frequently
    filter_upwards [Filter.Eventually.filter_mono inf_le_left (Ioo_mem_nhds ha hb)] with x hx
    simpa only [complexMGF_ofReal] using
      congr_arg ((↑) : ℝ → ℂ) (hmgf hx)
  have hCEq : Set.EqOn (complexMGF X μ) (complexMGF Y μ') D := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hCX hCY
      ((convex_Ioo a b).linear_preimage Complex.reLm).isPreconnected
      (z₀ := (0 : ℂ)) (by simp [D, ha, hb]) ?_
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n => xs n, ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · change Tendsto (Complex.ofReal ∘ xs) atTop (𝓝 (0 : ℂ))
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp hx_tendsto.1
      · simpa using hx_tendsto.2
    · simp [hx_eq]
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I hX.aemeasurable, ← complexMGF_mul_I hY.aemeasurable]
  exact hCEq (by simp [D, ha, hb])

lemma iIndepFun_gaussian_coordinate_sq (N : ℕ) :
    iIndepFun (fun i (g : Fin N → ℝ) => (g i) ^ 2) (gaussianVec N) := by
  have hEval : iIndepFun (fun i (g : Fin N → ℝ) => g i) (gaussianVec N) := by
    unfold gaussianVec
    exact iIndepFun_pi fun _ => aemeasurable_id
  change iIndepFun
    (fun i => (fun x : ℝ => x ^ 2) ∘ fun g : Fin N → ℝ => g i) (gaussianVec N)
  exact hEval.comp (fun (_ : Fin N) (x : ℝ) => x ^ 2)
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => x ^ 2)))

lemma mgf_gaussianSquaredNorm_of_lt (N : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    mgf (gaussianSquaredNorm N) (gaussianVec N) t =
      ((1 / 2 : ℝ) / (1 / 2 - t)) ^ ((N : ℝ) / 2) := by
  have hcoord (i : Fin N) :
      mgf (fun g : Fin N → ℝ => (g i) ^ 2) (gaussianVec N) t =
        ((1 / 2 : ℝ) / (1 / 2 - t)) ^ (1 / 2 : ℝ) := by
    rw [← mgf_id_map (by fun_prop :
      Measurable (fun g : Fin N → ℝ => (g i) ^ 2)).aemeasurable]
    rw [show (fun g : Fin N → ℝ => (g i) ^ 2) =
        (fun x : ℝ => x ^ 2) ∘ (fun g : Fin N → ℝ => g i) from rfl]
    rw [← Measure.map_map (μ := gaussianVec N) (f := fun g : Fin N → ℝ => g i)
      (g := fun x : ℝ => x ^ 2) (by fun_prop) (measurable_pi_apply i)]
    unfold gaussianVec
    rw [Measure.pi_map_eval]
    simp only [measure_univ, Finset.prod_const_one, one_smul, one_div]
    rw [mgf_id_map (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aemeasurable]
    simpa [one_div] using mgf_sq_gaussianReal_of_lt ht
  have hsum := (iIndepFun_gaussian_coordinate_sq N).mgf_sum
    (fun _ => by fun_prop) (Finset.univ : Finset (Fin N)) (t := t)
  rw [show gaussianSquaredNorm N =
      ∑ i : Fin N, (fun g : Fin N → ℝ => (g i) ^ 2) by
    funext g
    simp [gaussianSquaredNorm, Finset.sum_apply]]
  rw [hsum]
  simp_rw [hcoord]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbase : 0 ≤ (1 / 2 : ℝ) / (1 / 2 - t) := by positivity
  rw [← Real.rpow_mul_natCast hbase]
  congr 1
  ring

lemma integrable_exp_mul_gaussianSquaredNorm_of_lt (N : ℕ) {t : ℝ}
    (ht : t < 1 / 2) :
    Integrable (fun g => Real.exp (t * gaussianSquaredNorm N g)) (gaussianVec N) := by
  have hsum := (iIndepFun_gaussian_coordinate_sq N).integrable_exp_mul_sum
    (fun _ => by fun_prop) (s := Finset.univ)
    (fun i _ => by
      refine Integrable.comp_measurable (f := fun g : Fin N → ℝ => g i)
        (g := fun x : ℝ => Real.exp (t * x ^ 2)) ?_ (measurable_pi_apply i)
      unfold gaussianVec
      rw [Measure.pi_map_eval]
      simp only [measure_univ, Finset.prod_const_one, one_smul]
      exact integrable_exp_mul_sq_gaussianReal_of_lt ht)
  simpa only [gaussianSquaredNorm, Finset.sum_apply] using hsum

/-- The squared norm of an `N`-dimensional standard Gaussian vector has the
Gamma law with shape `N / 2` and rate `1 / 2`. -/
lemma map_gaussianSquaredNorm_eq_gammaMeasure {N : ℕ} (hN : 0 < N) :
    (gaussianVec N).map (gaussianSquaredNorm N) =
      gammaMeasure ((N : ℝ) / 2) (1 / 2) := by
  letI : IsProbabilityMeasure (gammaMeasure ((N : ℝ) / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  have hmap := map_eq_of_mgf_eq_on_Ioo
    (μ := gaussianVec N) (μ' := gammaMeasure ((N : ℝ) / 2) (1 / 2))
    (X := gaussianSquaredNorm N) (Y := id) (a := -1) (b := 1 / 4)
    (measurable_gaussianSquaredNorm N) measurable_id (by norm_num) (by norm_num)
    (fun t ht => integrable_exp_mul_gaussianSquaredNorm_of_lt N (by linarith [ht.2]))
    (fun t ht => integrable_exp_mul_id_gammaMeasure_of_lt
      (by positivity) (by positivity) (by linarith [ht.2]))
    (fun t ht => by
      rw [mgf_gaussianSquaredNorm_of_lt N (by linarith [ht.2])]
      exact (mgf_id_gammaMeasure_of_lt
        (by positivity) (by positivity) (by linarith [ht.2])).symm)
  simpa using hmap

/-- On the positive half-line, multiplying a Gamma density of shape `a` by
`x⁻ᵖ` changes the power in the Gamma integrand from `a - 1` to
`a - p - 1`. -/
lemma neg_rpow_mul_gammaPDFReal_of_pos {a r p x : ℝ} (hx : 0 < x) :
    x ^ (-p) * gammaPDFReal a r x =
      r ^ a / Real.Gamma a *
        (x ^ (a - p - 1) * Real.exp (-(r * x))) := by
  rw [gammaPDFReal, if_pos hx.le]
  calc
    x ^ (-p) * (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
        r ^ a / Real.Gamma a * (x ^ (-p) * x ^ (a - 1)) *
          Real.exp (-(r * x)) := by ring
    _ = r ^ a / Real.Gamma a *
        (x ^ (a - p - 1) * Real.exp (-(r * x))) := by
      rw [← Real.rpow_add hx]
      rw [show -p + (a - 1) = a - p - 1 by ring]
      ring

/-- The negative `p`-moment integrand of a Gamma density is integrable on
`(0, ∞)` under the sharp condition `p < a`. -/
lemma integrableOn_neg_rpow_mul_gammaPDFReal {a r p : ℝ}
    (hap : p < a) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x ^ (-p) * gammaPDFReal a r x) (Set.Ioi 0) := by
  have hbase :
      IntegrableOn (fun x : ℝ => x ^ (a - p - 1) * Real.exp (-(r * x))) (Set.Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := a - p - 1) (b := r) (by linarith) le_rfl hr
  refine (hbase.const_mul (r ^ a / Real.Gamma a)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (neg_rpow_mul_gammaPDFReal_of_pos hx).symm

/-- Exact negative-moment integral for a Gamma density:
`∫₀∞ x⁻ᵖ f_{a,r}(x) dx = rᵖ Γ(a-p) / Γ(a)` for `p < a`.

After the remaining chi-square pushforward is established, specializing to
`a = N / 2` and `r = 1 / 2` gives the paper's exact negative moments of
`χ_N²`. -/
lemma integral_neg_rpow_mul_gammaPDFReal_Ioi {a r p : ℝ}
    (hr : 0 < r) (hp : p < a) :
    ∫ x : ℝ in Set.Ioi 0, x ^ (-p) * gammaPDFReal a r x =
      r ^ p * Real.Gamma (a - p) / Real.Gamma a := by
  rw [setIntegral_congr_fun measurableSet_Ioi]
  · rw [integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0 < a - p by linarith) hr]
    change (r ^ a / Real.Gamma a) *
        ((1 / r) ^ (a - p) * Real.Gamma (a - p)) =
      r ^ p * Real.Gamma (a - p) / Real.Gamma a
    rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
    have hpow : r ^ a * r ^ (-(a - p)) = r ^ p := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    calc
      r ^ a / Real.Gamma a * (r ^ (-(a - p)) * Real.Gamma (a - p)) =
          (r ^ a * r ^ (-(a - p))) * Real.Gamma (a - p) / Real.Gamma a := by ring
      _ = r ^ p * Real.Gamma (a - p) / Real.Gamma a := by rw [hpow]
  · intro x hx
    exact neg_rpow_mul_gammaPDFReal_of_pos hx

/-- Exact negative moments of the squared norm of a standard Gaussian vector.
For `p < N / 2`,
`𝔼[(χ_N²)⁻ᵖ] = (1/2)ᵖ Γ(N/2-p) / Γ(N/2)`. -/
lemma integral_neg_rpow_gaussianSquaredNorm {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : p < (N : ℝ) / 2) :
    ∫ g, (gaussianSquaredNorm N g) ^ (-p) ∂gaussianVec N =
      (1 / 2 : ℝ) ^ p * Real.Gamma ((N : ℝ) / 2 - p) /
        Real.Gamma ((N : ℝ) / 2) := by
  rw [← integral_map (measurable_gaussianSquaredNorm N).aemeasurable
    (by fun_prop : Measurable (fun x : ℝ => x ^ (-p))).aestronglyMeasurable]
  rw [map_gaussianSquaredNorm_eq_gammaMeasure hN]
  rw [gammaMeasure]
  change (∫ y : ℝ, y ^ (-p) ∂volume.withDensity
      (fun x => ENNReal.ofReal (gammaPDFReal ((N : ℝ) / 2) (1 / 2) x))) =
    (1 / 2 : ℝ) ^ p * Real.Gamma ((N : ℝ) / 2 - p) /
      Real.Gamma ((N : ℝ) / 2)
  rw [
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_gammaPDFReal ((N : ℝ) / 2) (1 / 2)).ennreal_ofReal)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg (by positivity : 0 < (N : ℝ) / 2)
      (by positivity : 0 < (1 / 2 : ℝ)) _), smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici 0) (f :=
    fun x : ℝ => gammaPDFReal ((N : ℝ) / 2) (1 / 2) x * x ^ (-p)) (by
      intro x hx
      rw [gammaPDFReal, if_neg]
      · simp
      · exact not_le.mpr (lt_of_not_ge hx))]
  rw [integral_Ici_eq_integral_Ioi]
  rw [setIntegral_congr_fun measurableSet_Ioi]
  · exact integral_neg_rpow_mul_gammaPDFReal_Ioi (by positivity) hp
  · intro x hx
    ring

/-- Exact negative moments of the Euclidean norm of a standard Gaussian vector.
For `q < N`,
`𝔼[|G|⁻ᑫ] = (1/2)^(q/2) Γ((N-q)/2) / Γ(N/2)`. -/
lemma integral_neg_rpow_gaussianEuclideanNorm {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq : q < (N : ℝ)) :
    ∫ g, (gaussianEuclideanNorm N g) ^ (-q) ∂gaussianVec N =
      (1 / 2 : ℝ) ^ (q / 2) * Real.Gamma (((N : ℝ) - q) / 2) /
        Real.Gamma ((N : ℝ) / 2) := by
  rw [show (fun g => (gaussianEuclideanNorm N g) ^ (-q)) =
      (fun g => (gaussianSquaredNorm N g) ^ (-(q / 2))) by
    funext g
    rw [gaussianEuclideanNorm, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (gaussianSquaredNorm_nonneg N g)]
    congr 1
    ring_nf]
  rw [integral_neg_rpow_gaussianSquaredNorm hN (by linarith : q / 2 < (N : ℝ) / 2)]
  congr 2
  ring_nf

/-- The inverse squared Euclidean norm has the elementary expectation
`𝔼[|G|⁻²] = 1 / (N - 2)` in dimensions `N > 2`. -/
lemma integral_neg_two_gaussianEuclideanNorm {N : ℕ} (hN : 2 < N) :
    ∫ g, (gaussianEuclideanNorm N g) ^ (-(2 : ℝ)) ∂gaussianVec N =
      1 / ((N : ℝ) - 2) := by
  rw [integral_neg_rpow_gaussianEuclideanNorm (N := N) (by omega)
    (by exact_mod_cast hN : (2 : ℝ) < N)]
  have hNreal : (2 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < ((N : ℝ) - 2) / 2 := by
    linarith
  rw [show (N : ℝ) / 2 = ((N : ℝ) - 2) / 2 + 1 by ring,
    Real.Gamma_add_one hx.ne']
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  field_simp [Real.Gamma_pos_of_pos hx |>.ne']

/-- After the natural `√N` normalization, the inverse squared Gaussian norm
has expectation `N / (N - 2)`. -/
lemma integral_neg_two_normalized_gaussianEuclideanNorm {N : ℕ} (hN : 2 < N) :
    ∫ g, (gaussianEuclideanNorm N g / Real.sqrt N) ^ (-(2 : ℝ)) ∂gaussianVec N =
      (N : ℝ) / ((N : ℝ) - 2) := by
  have hNpos : 0 < (N : ℝ) := by positivity
  rw [show (fun g => (gaussianEuclideanNorm N g / Real.sqrt N) ^ (-(2 : ℝ))) =
      (fun g => (N : ℝ) * (gaussianEuclideanNorm N g) ^ (-(2 : ℝ))) by
    funext g
    have hg : 0 ≤ gaussianEuclideanNorm N g := by
      unfold gaussianEuclideanNorm
      positivity
    rw [Real.div_rpow hg (Real.sqrt_nonneg _) (-2),
      Real.rpow_neg hg 2,
      Real.rpow_neg (Real.sqrt_nonneg _) 2,
      Real.rpow_two, Real.rpow_two, Real.sq_sqrt hNpos.le]
    field_simp]
  rw [integral_const_mul, integral_neg_two_gaussianEuclideanNorm hN]
  ring

/-- A dimension-uniform inverse-square bound for normalized Gaussian norms. -/
lemma integral_neg_two_normalized_gaussianEuclideanNorm_le_two {N : ℕ}
    (hN : 4 ≤ N) :
    ∫ g, (gaussianEuclideanNorm N g / Real.sqrt N) ^ (-(2 : ℝ)) ∂gaussianVec N ≤ 2 := by
  rw [integral_neg_two_normalized_gaussianEuclideanNorm (by omega)]
  have hden : 0 < (N : ℝ) - 2 := by
    exact sub_pos.mpr (by exact_mod_cast (show 2 < N by omega))
  apply (div_le_iff₀ hden).2
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- With the paper's `A / √N` scaling, the inverse-square moment is exactly
`N / (A² (N - 2))`. -/
lemma integral_neg_two_scaled_gaussianEuclideanNorm {N : ℕ} {A : ℝ}
    (hA : 0 < A) (hN : 2 < N) :
    ∫ g, ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-(2 : ℝ))
        ∂gaussianVec N =
      (N : ℝ) / (A ^ 2 * ((N : ℝ) - 2)) := by
  rw [show
      (fun g => ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-(2 : ℝ))) =
        (fun g => (A ^ 2)⁻¹ *
          (gaussianEuclideanNorm N g / Real.sqrt N) ^ (-(2 : ℝ))) by
    funext g
    have hg : 0 ≤ gaussianEuclideanNorm N g := by
      unfold gaussianEuclideanNorm
      positivity
    have hnormalized : 0 ≤ gaussianEuclideanNorm N g / Real.sqrt N :=
      div_nonneg hg (Real.sqrt_nonneg _)
    rw [show (A / Real.sqrt N) * gaussianEuclideanNorm N g =
        A * (gaussianEuclideanNorm N g / Real.sqrt N) by ring,
      Real.mul_rpow hA.le hnormalized, Real.rpow_neg hA.le 2, Real.rpow_two]]
  rw [integral_const_mul, integral_neg_two_normalized_gaussianEuclideanNorm hN]
  field_simp [hA.ne']

/-- For `N ≥ 4`, the inverse-square moment under the paper's scaling is bounded
uniformly in the dimension by `2 / A²`. -/
lemma integral_neg_two_scaled_gaussianEuclideanNorm_le {N : ℕ} {A : ℝ}
    (hA : 0 < A) (hN : 4 ≤ N) :
    ∫ g, ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-(2 : ℝ))
        ∂gaussianVec N ≤
      2 / A ^ 2 := by
  rw [integral_neg_two_scaled_gaussianEuclideanNorm hA (by omega)]
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
  have hden : 0 < (N : ℝ) - 2 := by
    exact sub_pos.mpr (by exact_mod_cast (show 2 < N by omega))
  apply (div_le_iff₀ (mul_pos hA2 hden)).2
  field_simp [hA.ne']
  have hNreal : (4 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

/-- The paper's explicit finite-dimensional criterion for strict contraction of
the inverse-square moment. -/
lemma integral_neg_two_scaled_gaussianEuclideanNorm_lt_one_of_dimension
    {N : ℕ} {A : ℝ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N) :
    ∫ g, ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-(2 : ℝ))
        ∂gaussianVec N < 1 := by
  rw [integral_neg_two_scaled_gaussianEuclideanNorm (by linarith) hN]
  have hA2 : 0 < A ^ 2 := sq_pos_of_pos (by linarith)
  have hden : 0 < (N : ℝ) - 2 := by
    exact sub_pos.mpr (by exact_mod_cast hN)
  apply (div_lt_one (mul_pos hA2 hden)).2
  nlinarith

/-- For every fixed `A > 1`, all sufficiently large dimensions exceed two
and satisfy the paper's explicit reciprocal-moment criterion. -/
lemma exists_dimension_threshold_for_reciprocal_moment
    {A : ℝ} (hA : 1 < A) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      2 < N ∧ 2 * A ^ 2 < (A ^ 2 - 1) * N := by
  have hcoef : 0 < A ^ 2 - 1 := by nlinarith
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (2 * A ^ 2 / (A ^ 2 - 1))
  refine ⟨max 3 N₀, fun N hN => ⟨by omega, ?_⟩⟩
  have hN₀N : N₀ ≤ N := le_trans (Nat.le_max_right 3 N₀) hN
  have hN₀Nreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
  have hquot : 2 * A ^ 2 / (A ^ 2 - 1) < (N : ℝ) :=
    hN₀.trans_le hN₀Nreal
  simpa [mul_comm] using (div_lt_iff₀ hcoef).1 hquot

/-- For every fixed `A > 1`, the inverse-square moment of the paper's
linearized radius multiplier is strictly contractive in all sufficiently large
dimensions. -/
lemma eventually_integral_neg_two_scaled_gaussianEuclideanNorm_lt_one
    {A : ℝ} (hA : 1 < A) :
    ∀ᶠ N : ℕ in atTop,
      ∫ g, ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-(2 : ℝ))
          ∂gaussianVec N < 1 := by
  have hcoef : 0 < A ^ 2 - 1 := by nlinarith
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (2 * A ^ 2 / (A ^ 2 - 1))
  filter_upwards [eventually_atTop.2
    ⟨max 3 N₀, fun N hN => hN⟩] with N hN
  apply integral_neg_two_scaled_gaussianEuclideanNorm_lt_one_of_dimension hA
  · omega
  · have hN₀N : N₀ ≤ N := le_trans (Nat.le_max_right 3 N₀) hN
    have hN₀Nreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
    have hquot : 2 * A ^ 2 / (A ^ 2 - 1) < (N : ℝ) :=
      hN₀.trans_le hN₀Nreal
    have := (div_lt_iff₀ hcoef).1 hquot
    nlinarith

/-- At fixed dimension and Gaussian sample, the squared-radius update divided
by its input converges at the origin to the paper's linearized multiplier
`A² ‖g‖₂² / N`. -/
lemma Fmap_div_tendsto_gaussianSquaredNorm {A : ℝ} (hA : A ≠ 0)
    (N : ℕ) (g : Fin N → ℝ) :
    Tendsto (fun q => Fmap A N q g / q) (𝓝[>] 0)
      (𝓝 (A ^ 2 * gaussianSquaredNorm N g / N)) := by
  have hcoord (i : Fin N) :
      Tendsto (fun q => Real.tanh (A * Real.sqrt q * g i) ^ 2 / q)
        (𝓝[>] 0) (𝓝 ((A * g i) ^ 2)) := by
    by_cases hi : g i = 0
    · simp [hi]
    · exact tendsto_tanh_sq_div_ratio hA hi
  have hsum :
      Tendsto
        (fun q => ∑ i : Fin N, Real.tanh (A * Real.sqrt q * g i) ^ 2 / q)
        (𝓝[>] 0) (𝓝 (∑ i : Fin N, (A * g i) ^ 2)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  have hscaled := hsum.const_mul ((N : ℝ)⁻¹)
  have hlimit :
      (N : ℝ)⁻¹ * ∑ i : Fin N, (A * g i) ^ 2 =
        A ^ 2 * gaussianSquaredNorm N g / N := by
    unfold gaussianSquaredNorm
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    ring
  rw [hlimit] at hscaled
  refine hscaled.congr' ?_
  exact Filter.Eventually.of_forall fun q => by
    unfold Fmap
    simp only
    rw [mul_div_assoc, Finset.sum_div]

/-- For each fixed Gaussian sample, the radial update-to-input ratio is
nonincreasing on the positive half-line. -/
lemma antitoneOn_Fmap_div (A : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    AntitoneOn (fun q => Fmap A N q g / q) (Set.Ioi (0 : ℝ)) := by
  intro q hq R hR hqR
  unfold Fmap
  simp only
  rw [mul_div_assoc, mul_div_assoc, Finset.sum_div, Finset.sum_div]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_le_sum
  intro i _
  have harg (s : ℝ) :
      A * Real.sqrt s * g i = (A * g i) * Real.sqrt s := by ring
  by_cases hi : A * g i = 0
  · simp [harg, hi]
  · by_cases hqRne : q = R
    · subst R
      exact le_rfl
    · rw [harg q, harg R]
      exact (tanh_sq_comp_div_strictAnti' hi hq hR
        (lt_of_le_of_ne hqR hqRne)).le

/-- In particular, a smaller positive input gives the lower bound used to
dominate reciprocal radial-update ratios. -/
lemma Fmap_div_ge_of_pos_of_le {A : ℝ} {N : ℕ} {q R : ℝ}
    (g : Fin N → ℝ) (hq : 0 < q) (hqR : q ≤ R) :
    Fmap A N R g / R ≤ Fmap A N q g / q :=
  antitoneOn_Fmap_div A N g hq (hq.trans_le hqR) hqR

/-- A global quadratic-near-zero, constant-away-from-zero lower bound for
`tanh²`. This is the pointwise small-ball input for fixed-radius reciprocal
integrability. -/
lemma tanh_one_sq_mul_min_sq_one_le (x : ℝ) :
    Real.tanh 1 ^ 2 * min (x ^ 2) 1 ≤ Real.tanh x ^ 2 := by
  have htanh_abs : Real.tanh |x| ^ 2 = Real.tanh x ^ 2 := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, Real.tanh_neg, neg_sq]
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hxsmall : x ^ 2 ≤ 1
  · rw [min_eq_left hxsmall]
    have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    have hratio :=
      (tanh_sq_comp_div_strictAnti (c := (1 : ℝ)) zero_lt_one).antitoneOn
        (Set.mem_Ioi.mpr hx2pos) (Set.mem_Ioi.mpr zero_lt_one) hxsmall
    norm_num [Real.sqrt_sq_eq_abs] at hratio
    rw [htanh_abs] at hratio
    exact (le_div_iff₀ hx2pos).1 hratio
  · rw [min_eq_right (le_of_not_ge hxsmall)]
    have habs : 1 ≤ |x| := by
      have habssq : |x| ^ 2 = x ^ 2 := sq_abs x
      nlinarith [abs_nonneg x]
    have htanh_mono : Real.tanh 1 ≤ Real.tanh |x| :=
      tanh_strictMono.monotone habs
    have htanh_one_nonneg : 0 ≤ Real.tanh 1 := by
      rw [← Real.tanh_zero]
      exact tanh_strictMono.monotone zero_le_one
    have htanh_abs_nonneg : 0 ≤ Real.tanh |x| := by
      rw [← Real.tanh_zero]
      exact tanh_strictMono.monotone (abs_nonneg x)
    calc
      Real.tanh 1 ^ 2 * 1 = Real.tanh 1 ^ 2 := mul_one _
      _ ≤ Real.tanh |x| ^ 2 := by nlinarith
      _ = Real.tanh x ^ 2 := htanh_abs

/-- Summing the global `tanh²` lower bound controls the Gaussian radial update
by `S / (1 + S)`, where `S = ‖g‖₂²`. -/
lemma sum_tanh_sq_lower_gaussianSquaredNorm {A R : ℝ} (hR : 0 ≤ R)
    (N : ℕ) (g : Fin N → ℝ) :
    Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1 *
        (gaussianSquaredNorm N g / (1 + gaussianSquaredNorm N g)) ≤
      ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 := by
  let S := gaussianSquaredNorm N g
  let α := min (A ^ 2 * R) 1
  have hS : 0 ≤ S := gaussianSquaredNorm_nonneg N g
  have hα : 0 ≤ α := by
    dsimp [α]
    exact le_min (mul_nonneg (sq_nonneg A) hR) zero_le_one
  have hden : 0 < 1 + S := by linarith
  have hcoord (i : Fin N) :
      Real.tanh 1 ^ 2 * (α * (g i) ^ 2 / (1 + S)) ≤
        Real.tanh (A * Real.sqrt R * g i) ^ 2 := by
    have hgiS : (g i) ^ 2 ≤ S := by
      dsimp [S, gaussianSquaredNorm]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (g j)) (Finset.mem_univ i)
    have hαc : α ≤ A ^ 2 * R := min_le_left _ _
    have hα1 : α ≤ 1 := min_le_right _ _
    have hscaled_sq :
        (A * Real.sqrt R * g i) ^ 2 = (A ^ 2 * R) * (g i) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hR]
    have hmin :
        α * (g i) ^ 2 / (1 + S) ≤
          min ((A * Real.sqrt R * g i) ^ 2) 1 := by
      apply le_min
      · rw [hscaled_sq]
        apply (div_le_iff₀ hden).2
        have hbase :
            α * (g i) ^ 2 ≤ (A ^ 2 * R) * (g i) ^ 2 :=
          mul_le_mul_of_nonneg_right hαc (sq_nonneg _)
        have hscaled_nonneg : 0 ≤ (A ^ 2 * R) * (g i) ^ 2 :=
          mul_nonneg (mul_nonneg (sq_nonneg A) hR) (sq_nonneg _)
        nlinarith
      · apply (div_le_iff₀ hden).2
        have hbase : α * (g i) ^ 2 ≤ (g i) ^ 2 :=
          mul_le_of_le_one_left (sq_nonneg _) hα1
        linarith
    calc
      Real.tanh 1 ^ 2 * (α * (g i) ^ 2 / (1 + S)) ≤
          Real.tanh 1 ^ 2 * min ((A * Real.sqrt R * g i) ^ 2) 1 :=
        mul_le_mul_of_nonneg_left hmin (sq_nonneg _)
      _ ≤ Real.tanh (A * Real.sqrt R * g i) ^ 2 :=
        tanh_one_sq_mul_min_sq_one_le _
  change Real.tanh 1 ^ 2 * α * (S / (1 + S)) ≤ _
  calc
    Real.tanh 1 ^ 2 * α * (S / (1 + S)) =
        ∑ i, Real.tanh 1 ^ 2 * (α * (g i) ^ 2 / (1 + S)) := by
      dsimp [S, gaussianSquaredNorm]
      calc
        Real.tanh 1 ^ 2 * α *
            ((∑ i, (g i) ^ 2) / (1 + ∑ i, (g i) ^ 2)) =
            Real.tanh 1 ^ 2 *
              (α * ∑ i, (g i) ^ 2 / (1 + ∑ j, (g j) ^ 2)) := by
            rw [Finset.sum_div]
            ring
        _ = Real.tanh 1 ^ 2 *
              ∑ i, α * ((g i) ^ 2 / (1 + ∑ j, (g j) ^ 2)) := by
            rw [Finset.mul_sum]
        _ = ∑ i, Real.tanh 1 ^ 2 *
              (α * ((g i) ^ 2 / (1 + ∑ j, (g j) ^ 2))) := by
            rw [Finset.mul_sum]
        _ = ∑ i, Real.tanh 1 ^ 2 *
              (α * (g i) ^ 2 / (1 + ∑ j, (g j) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ ≤ ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 :=
      Finset.sum_le_sum fun i _ => hcoord i

/-- The reciprocal fixed-radius update ratio is controlled pointwise by a
constant times `1 + ‖g‖₂⁻²`. -/
lemma inv_Fmap_div_le_one_add_inv_gaussianSquaredNorm
    {A R : ℝ} {N : ℕ} (hA : A ≠ 0) (hR : 0 < R) (hN : 0 < N)
    (g : Fin N → ℝ) :
    (Fmap A N R g / R)⁻¹ ≤
      ((N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) *
        (1 + (gaussianSquaredNorm N g)⁻¹) := by
  let S := gaussianSquaredNorm N g
  let β := Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1
  have hS : 0 ≤ S := gaussianSquaredNorm_nonneg N g
  have htanh : 0 < Real.tanh 1 := by
    rw [← Real.tanh_zero]
    exact tanh_strictMono zero_lt_one
  have hα : 0 < min (A ^ 2 * R) 1 := by
    exact lt_min (mul_pos (sq_pos_of_ne_zero hA) hR) zero_lt_one
  have hβ : 0 < β := mul_pos (sq_pos_of_pos htanh) hα
  have hNR : 0 < (N : ℝ) * R :=
    mul_pos (by exact_mod_cast hN) hR
  have hraw :
      β * (S / (1 + S)) ≤
        ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 := by
    exact sum_tanh_sq_lower_gaussianSquaredNorm hR.le N g
  have hlower :
      β * (S / (1 + S)) / ((N : ℝ) * R) ≤ Fmap A N R g / R := by
    calc
      β * (S / (1 + S)) / ((N : ℝ) * R) =
          ((N : ℝ) * R)⁻¹ * (β * (S / (1 + S))) := by ring
      _ ≤ ((N : ℝ) * R)⁻¹ *
          ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 :=
        mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hNR.le)
      _ = Fmap A N R g / R := by
        unfold Fmap
        field_simp [hNR.ne']
  by_cases hS0 : S = 0
  · have hgi (i : Fin N) : g i = 0 := by
      have hsqi : (g i) ^ 2 = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => sq_nonneg (g j))).1
            (show (∑ j, (g j) ^ 2) = 0 by simpa [S, gaussianSquaredNorm] using hS0)
        exact Finset.mem_univ i
      exact sq_eq_zero_iff.mp hsqi
    have hconst_nonneg :
        0 ≤ (N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1) :=
      div_nonneg hNR.le hβ.le
    simp [Fmap, hgi, hS0, S, hconst_nonneg]
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    have hLpos :
        0 < β * (S / (1 + S)) / ((N : ℝ) * R) := by positivity
    calc
      (Fmap A N R g / R)⁻¹ ≤
          (β * (S / (1 + S)) / ((N : ℝ) * R))⁻¹ :=
        inv_anti₀ hLpos hlower
      _ = ((N : ℝ) * R / β) * (1 + S⁻¹) := by
        field_simp [hβ.ne', hNR.ne', hSpos.ne']
        ring
      _ = ((N : ℝ) * R /
            (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) *
          (1 + (gaussianSquaredNorm N g)⁻¹) := by
        rfl

/-- At every fixed positive input, the reciprocal radial update ratio is
integrable in dimensions greater than two. -/
lemma integrable_inv_Fmap_div {A R : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hR : 0 < R) (hN : 2 < N) :
    Integrable (fun g : Fin N → ℝ => (Fmap A N R g / R)⁻¹)
      (gaussianVec N) := by
  have hNpos : 0 < N := by omega
  have hSinv_val :
      ∫ g : Fin N → ℝ, (gaussianSquaredNorm N g)⁻¹ ∂gaussianVec N =
        1 / ((N : ℝ) - 2) := by
    calc
      ∫ g : Fin N → ℝ, (gaussianSquaredNorm N g)⁻¹ ∂gaussianVec N =
          ∫ g, (gaussianEuclideanNorm N g) ^ (-(2 : ℝ)) ∂gaussianVec N := by
        apply integral_congr_ae
        filter_upwards with g
        symm
        rw [gaussianEuclideanNorm,
          Real.rpow_neg (Real.sqrt_nonneg _) 2,
          Real.rpow_two,
          Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
      _ = 1 / ((N : ℝ) - 2) :=
        integral_neg_two_gaussianEuclideanNorm hN
  have hSinv :
      Integrable (fun g : Fin N → ℝ => (gaussianSquaredNorm N g)⁻¹)
        (gaussianVec N) := by
    by_contra hnot
    rw [integral_undef hnot] at hSinv_val
    have hden : 0 < (N : ℝ) - 2 := by
      exact sub_pos.mpr (by exact_mod_cast hN)
    have : 0 < 1 / ((N : ℝ) - 2) := one_div_pos.mpr hden
    linarith
  let C :=
    (N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)
  have hdom :
      Integrable
        (fun g : Fin N → ℝ =>
          C * (1 + (gaussianSquaredNorm N g)⁻¹))
        (gaussianVec N) := by
    exact ((integrable_const (1 : ℝ)).add hSinv).const_mul C
  have htarget_meas :
      AEStronglyMeasurable
        (fun g : Fin N → ℝ => (Fmap A N R g / R)⁻¹)
        (gaussianVec N) := by
    have hF : Measurable (Fmap A N R) :=
      Continuous.measurable (by
        unfold Fmap
        apply Continuous.const_mul
        apply continuous_finsetSum
        intro i _
        exact (continuous_tanh.comp (by fun_prop)).pow 2)
    exact ((hF.div_const R).inv).aestronglyMeasurable
  refine hdom.mono_nonneg htarget_meas ?_ ?_
  · filter_upwards with g
    exact inv_nonneg.mpr (div_nonneg (Fmap_nonneg A N R g) hR.le)
  · filter_upwards with g
    exact inv_Fmap_div_le_one_add_inv_gaussianSquaredNorm
      hA hR hNpos g

/-- At every positive state, the reciprocal radius is integrable after one
step of the squared-radius chain. -/
lemma integrable_inv_Kchain {A q : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hq : 0 < q) (hN : 2 < N) :
    Integrable (fun y : ℝ => y⁻¹) (Kchain A N q) := by
  rw [Kchain_apply]
  refine (integrable_map_measure
    (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y⁻¹)
      ((gaussianVec N).map (Fmap A N q)))
    (continuous_Fmap_right A N q).aemeasurable).2 ?_
  have hratio := integrable_inv_Fmap_div hA hq hN
  change Integrable (fun g : Fin N → ℝ => (Fmap A N q g)⁻¹)
    (gaussianVec N)
  rw [show
      (fun g : Fin N → ℝ => (Fmap A N q g)⁻¹) =
        fun g => q⁻¹ * (Fmap A N q g / q)⁻¹ by
    funext g
    rw [inv_div, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ hq.ne', one_mul]]
  exact hratio.const_mul q⁻¹

/-- On every radius interval bounded away from zero, the expected reciprocal
radial update has one finite uniform upper bound. -/
lemma exists_integral_inv_Fmap_le_on_Icc
    {A R₀ : ℝ} {N : ℕ} (hA : A ≠ 0) (hR₀ : 0 < R₀) (hN : 2 < N) :
    ∃ B : ℝ, ∀ q ∈ Set.Icc R₀ 1,
      ∫ g : Fin N → ℝ, (Fmap A N q g)⁻¹ ∂gaussianVec N ≤ B := by
  let β₀ := Real.tanh 1 ^ 2 * min (A ^ 2 * R₀) 1
  let C := (N : ℝ) / β₀
  let D := fun g : Fin N → ℝ =>
    C * (1 + (gaussianSquaredNorm N g)⁻¹)
  have hNpos : 0 < N := by omega
  have htanh : 0 < Real.tanh 1 := by
    rw [← Real.tanh_zero]
    exact tanh_strictMono zero_lt_one
  have hα₀ : 0 < min (A ^ 2 * R₀) 1 :=
    lt_min (mul_pos (sq_pos_of_ne_zero hA) hR₀) zero_lt_one
  have hβ₀ : 0 < β₀ := mul_pos (sq_pos_of_pos htanh) hα₀
  have hSinv_val :
      ∫ g : Fin N → ℝ, (gaussianSquaredNorm N g)⁻¹ ∂gaussianVec N =
        1 / ((N : ℝ) - 2) := by
    calc
      ∫ g : Fin N → ℝ, (gaussianSquaredNorm N g)⁻¹ ∂gaussianVec N =
          ∫ g, (gaussianEuclideanNorm N g) ^ (-(2 : ℝ)) ∂gaussianVec N := by
        apply integral_congr_ae
        filter_upwards with g
        symm
        rw [gaussianEuclideanNorm,
          Real.rpow_neg (Real.sqrt_nonneg _) 2,
          Real.rpow_two,
          Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
      _ = 1 / ((N : ℝ) - 2) :=
        integral_neg_two_gaussianEuclideanNorm hN
  have hSinv :
      Integrable (fun g : Fin N → ℝ => (gaussianSquaredNorm N g)⁻¹)
        (gaussianVec N) := by
    by_contra hnot
    rw [integral_undef hnot] at hSinv_val
    have hden : 0 < (N : ℝ) - 2 := by
      exact sub_pos.mpr (by exact_mod_cast hN)
    have : 0 < 1 / ((N : ℝ) - 2) := one_div_pos.mpr hden
    linarith
  have hD : Integrable D (gaussianVec N) := by
    exact ((integrable_const (1 : ℝ)).add hSinv).const_mul C
  refine ⟨∫ g, D g ∂gaussianVec N, ?_⟩
  intro q hq
  have hqpos : 0 < q := hR₀.trans_le hq.1
  have htarget :
      Integrable (fun g : Fin N → ℝ => (Fmap A N q g)⁻¹)
        (gaussianVec N) := by
    have hratio := integrable_inv_Fmap_div hA hqpos hN
    rw [show
        (fun g : Fin N → ℝ => (Fmap A N q g)⁻¹) =
          fun g => q⁻¹ * (Fmap A N q g / q)⁻¹ by
      funext g
      rw [inv_div, div_eq_mul_inv, ← mul_assoc,
        inv_mul_cancel₀ hqpos.ne', one_mul]]
    exact hratio.const_mul q⁻¹
  apply integral_mono htarget hD
  intro g
  have hα_le :
      min (A ^ 2 * R₀) 1 ≤ min (A ^ 2 * q) 1 := by
    exact min_le_min
      (mul_le_mul_of_nonneg_left hq.1 (sq_nonneg A)) le_rfl
  have hβq :
      0 < Real.tanh 1 ^ 2 * min (A ^ 2 * q) 1 := by
    exact mul_pos (sq_pos_of_pos htanh)
      (lt_min (mul_pos (sq_pos_of_ne_zero hA) hqpos) zero_lt_one)
  have hβ_le :
      β₀ ≤ Real.tanh 1 ^ 2 * min (A ^ 2 * q) 1 := by
    exact mul_le_mul_of_nonneg_left hα_le (sq_nonneg _)
  have hcoef :
      (N : ℝ) /
          (Real.tanh 1 ^ 2 * min (A ^ 2 * q) 1) ≤ C := by
    dsimp [C]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) hβ₀ hβ_le
  have hfactor :
      0 ≤ 1 + (gaussianSquaredNorm N g)⁻¹ := by
    exact add_nonneg zero_le_one
      (inv_nonneg.mpr (gaussianSquaredNorm_nonneg N g))
  calc
    (Fmap A N q g)⁻¹ =
        q⁻¹ * (Fmap A N q g / q)⁻¹ := by
      rw [inv_div, div_eq_mul_inv, ← mul_assoc,
        inv_mul_cancel₀ hqpos.ne', one_mul]
    _ ≤ q⁻¹ *
        (((N : ℝ) * q /
            (Real.tanh 1 ^ 2 * min (A ^ 2 * q) 1)) *
          (1 + (gaussianSquaredNorm N g)⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (inv_Fmap_div_le_one_add_inv_gaussianSquaredNorm
          hA hqpos hNpos g)
        (inv_nonneg.mpr hqpos.le)
    _ = ((N : ℝ) /
          (Real.tanh 1 ^ 2 * min (A ^ 2 * q) 1)) *
        (1 + (gaussianSquaredNorm N g)⁻¹) := by
      field_simp [hqpos.ne', hβq.ne']
    _ ≤ C * (1 + (gaussianSquaredNorm N g)⁻¹) :=
      mul_le_mul_of_nonneg_right hcoef hfactor
    _ = D g := rfl

/-- The nonlinear inverse update moment converges, through positive inputs, to
the paper's explicit inverse-square Gaussian multiplier moment. -/
lemma integral_inv_Fmap_div_tendsto {A : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hN : 2 < N) :
    Tendsto
      (fun q => ∫ g : Fin N → ℝ, (Fmap A N q g / q)⁻¹ ∂gaussianVec N)
      (𝓝[>] 0) (𝓝 ((N : ℝ) / (A ^ 2 * ((N : ℝ) - 2)))) := by
  have hNpos : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  let i₀ : Fin N := ⟨0, hNpos⟩
  have hcoord_ae : ∀ᵐ g : Fin N → ℝ ∂gaussianVec N, g i₀ ≠ 0 := by
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
  have hSpos :
      ∀ᵐ g : Fin N → ℝ ∂gaussianVec N, 0 < gaussianSquaredNorm N g := by
    filter_upwards [hcoord_ae] with g hg
    have hterm : (g i₀) ^ 2 ≤ gaussianSquaredNorm N g := by
      unfold gaussianSquaredNorm
      exact Finset.single_le_sum (fun j _ => sq_nonneg (g j)) (Finset.mem_univ i₀)
    exact (sq_pos_of_ne_zero hg).trans_le hterm
  have htanh : 0 < Real.tanh 1 := by
    rw [← Real.tanh_zero]
    exact tanh_strictMono zero_lt_one
  have hFonepos (g : Fin N → ℝ) (hg : 0 < gaussianSquaredNorm N g) :
      0 < Fmap A N 1 g / 1 := by
    have hα : 0 < min (A ^ 2 * 1) 1 :=
      lt_min (mul_pos (sq_pos_of_ne_zero hA) zero_lt_one) zero_lt_one
    have hraw := sum_tanh_sq_lower_gaussianSquaredNorm
      (A := A) (R := (1 : ℝ)) zero_le_one N g
    have hlower :
        0 < Real.tanh 1 ^ 2 * min (A ^ 2 * 1) 1 *
          (gaussianSquaredNorm N g / (1 + gaussianSquaredNorm N g)) := by
      positivity
    have hsum :
        0 < ∑ i, Real.tanh (A * Real.sqrt 1 * g i) ^ 2 :=
      hlower.trans_le hraw
    simp only [div_one]
    unfold Fmap
    exact mul_pos (inv_pos.mpr hNreal) hsum
  have hFmeas (q : ℝ) :
      AEStronglyMeasurable
        (fun g : Fin N → ℝ => (Fmap A N q g / q)⁻¹)
        (gaussianVec N) := by
    have hF : Measurable (Fmap A N q) :=
      Continuous.measurable (by
        unfold Fmap
        apply Continuous.const_mul
        apply continuous_finsetSum
        intro i _
        exact (continuous_tanh.comp (by fun_prop)).pow 2)
    exact ((hF.div_const q).inv).aestronglyMeasurable
  have hconv :
      Tendsto
        (fun q => ∫ g : Fin N → ℝ, (Fmap A N q g / q)⁻¹ ∂gaussianVec N)
        (𝓝[>] 0)
        (𝓝 (∫ g : Fin N → ℝ,
          (A ^ 2 * gaussianSquaredNorm N g / N)⁻¹ ∂gaussianVec N)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun g : Fin N → ℝ => (Fmap A N 1 g / 1)⁻¹) ?_ ?_
      (integrable_inv_Fmap_div hA zero_lt_one hN) ?_
    · exact Filter.Eventually.of_forall hFmeas
    · have hle_one :
          ∀ᶠ q : ℝ in 𝓝[>] 0, q ≤ 1 :=
        Filter.Eventually.filter_mono inf_le_left (Iic_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, hle_one] with q hq hq1
      filter_upwards [hSpos] with g hg
      rw [Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr
          (div_nonneg (Fmap_nonneg A N q g) hq.le))]
      exact inv_anti₀ (hFonepos g hg)
        (Fmap_div_ge_of_pos_of_le g hq hq1)
    · filter_upwards [hSpos] with g hg
      exact (Fmap_div_tendsto_gaussianSquaredNorm hA N g).inv₀ (by positivity)
  have hSinv_val :
      ∫ g : Fin N → ℝ, (gaussianSquaredNorm N g)⁻¹ ∂gaussianVec N =
        1 / ((N : ℝ) - 2) := by
    calc
      ∫ g : Fin N → ℝ, (gaussianSquaredNorm N g)⁻¹ ∂gaussianVec N =
          ∫ g, (gaussianEuclideanNorm N g) ^ (-(2 : ℝ)) ∂gaussianVec N := by
        apply integral_congr_ae
        filter_upwards with g
        symm
        rw [gaussianEuclideanNorm,
          Real.rpow_neg (Real.sqrt_nonneg _) 2,
          Real.rpow_two,
          Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
      _ = 1 / ((N : ℝ) - 2) :=
        integral_neg_two_gaussianEuclideanNorm hN
  have hlimit :
      (∫ g : Fin N → ℝ,
          (A ^ 2 * gaussianSquaredNorm N g / N)⁻¹ ∂gaussianVec N) =
        (N : ℝ) / (A ^ 2 * ((N : ℝ) - 2)) := by
    rw [show
        (fun g : Fin N → ℝ =>
          (A ^ 2 * gaussianSquaredNorm N g / N)⁻¹) =
        (fun g => ((N : ℝ) / A ^ 2) *
          (gaussianSquaredNorm N g)⁻¹) by
      funext g
      by_cases hg : gaussianSquaredNorm N g = 0
      · simp [hg]
      · field_simp [hA, hNreal.ne', hg]]
    rw [integral_const_mul, hSinv_val]
    field_simp [hA, hNreal.ne']
  rwa [hlimit] at hconv

/-- Under the explicit finite-dimensional supercritical criterion, one strict
contraction factor uniformly bounds the nonlinear inverse update moment at all
sufficiently small positive radii. -/
lemma exists_small_radius_integral_inv_Fmap_div_lt
    {A : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N) :
    ∃ R₀ > 0, ∃ a < 1, ∀ q, 0 < q → q ≤ R₀ →
      ∫ g : Fin N → ℝ, (Fmap A N q g / q)⁻¹ ∂gaussianVec N < a := by
  have hlimit :
      (N : ℝ) / (A ^ 2 * ((N : ℝ) - 2)) < 1 := by
    have hcontract :=
      integral_neg_two_scaled_gaussianEuclideanNorm_lt_one_of_dimension
        hA hN hdim
    rwa [integral_neg_two_scaled_gaussianEuclideanNorm (by linarith) hN] at hcontract
  let a := ((N : ℝ) / (A ^ 2 * ((N : ℝ) - 2)) + 1) / 2
  have hlimit_lt_a :
      (N : ℝ) / (A ^ 2 * ((N : ℝ) - 2)) < a := by
    dsimp [a]
    linarith
  have ha : a < 1 := by
    dsimp [a]
    linarith
  have heventually :
      ∀ᶠ q : ℝ in 𝓝[>] 0,
        ∫ g : Fin N → ℝ, (Fmap A N q g / q)⁻¹ ∂gaussianVec N < a :=
    (integral_inv_Fmap_div_tendsto (by linarith) hN).eventually
      (Iio_mem_nhds hlimit_lt_a)
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhdsWithin_iff.1 heventually
  refine ⟨ε / 2, by positivity, a, ha, ?_⟩
  intro q hq hqR
  apply hεsub
  constructor
  · rw [Metric.mem_ball, Real.dist_eq]
    rw [sub_zero, abs_of_pos hq]
    linarith
  · exact hq

/-- Under the explicit finite-dimensional supercritical criterion, the
nonlinear inverse update moment is uniformly contractive at all sufficiently
small positive radii. -/
lemma exists_small_radius_integral_inv_Fmap_div_lt_one
    {A : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N) :
    ∃ R₀ > 0, ∀ q, 0 < q → q ≤ R₀ →
      ∫ g : Fin N → ℝ, (Fmap A N q g / q)⁻¹ ∂gaussianVec N < 1 := by
  obtain ⟨R₀, hR₀, a, ha, hsmall⟩ :=
    exists_small_radius_integral_inv_Fmap_div_lt hA hN hdim
  exact ⟨R₀, hR₀, fun q hq hqR => (hsmall q hq hqR).trans ha⟩

/-- Under the explicit finite-dimensional supercritical criterion, the
reciprocal Lyapunov function `V(q) = q⁻¹` satisfies a one-step Foster bound
throughout the positive radius interval. -/
lemma exists_Kchain_inv_foster_bound
    {A : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N) :
    ∃ R₀ : ℝ, R₀ > 0 ∧ ∃ a : ℝ, a < 1 ∧ ∃ B : ℝ,
      ∀ q ∈ Set.Ioc (0 : ℝ) 1,
        ∫ y, y⁻¹ ∂Kchain A N q ≤ a * q⁻¹ + B := by
  obtain ⟨R₀, hR₀, a, ha, hsmall⟩ :=
    exists_small_radius_integral_inv_Fmap_div_lt hA hN hdim
  obtain ⟨B, hlarge⟩ :=
    exists_integral_inv_Fmap_le_on_Icc
      (A := A) (R₀ := R₀) (N := N) (by linarith) hR₀ hN
  let a' := max a 0
  let B' := max B 0
  have ha' : a' < 1 := max_lt ha zero_lt_one
  have ha'nonneg : 0 ≤ a' := le_max_right _ _
  have hB'nonneg : 0 ≤ B' := le_max_right _ _
  refine ⟨R₀, hR₀, a', ha', B', ?_⟩
  intro q hq
  rw [integral_Kchain A N q
    (by fun_prop : Measurable (fun y : ℝ => y⁻¹))]
  by_cases hqR : q ≤ R₀
  · have hmoment :
        ∫ g : Fin N → ℝ, (Fmap A N q g / q)⁻¹ ∂gaussianVec N < a' :=
      (hsmall q hq.1 hqR).trans_le (le_max_left _ _)
    have hratio :
        (∫ g : Fin N → ℝ,
            (Fmap A N q g / q)⁻¹ ∂gaussianVec N) =
          q * ∫ g : Fin N → ℝ, (Fmap A N q g)⁻¹ ∂gaussianVec N := by
      rw [show
          (fun g : Fin N → ℝ => (Fmap A N q g / q)⁻¹) =
            fun g => q * (Fmap A N q g)⁻¹ by
        funext g
        rw [inv_div, div_eq_mul_inv]]
      rw [integral_const_mul]
    rw [hratio] at hmoment
    have hcontract :
        (∫ g : Fin N → ℝ, (Fmap A N q g)⁻¹ ∂gaussianVec N) <
          a' * q⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (lt_div_iff₀ hq.1).2
      simpa [mul_comm] using hmoment
    exact (le_of_lt hcontract).trans
      (le_add_of_nonneg_right hB'nonneg)
  · have houtside :
        ∫ g : Fin N → ℝ, (Fmap A N q g)⁻¹ ∂gaussianVec N ≤ B :=
      hlarge q ⟨le_of_not_ge hqR, hq.2⟩
    have hterm : 0 ≤ a' * q⁻¹ :=
      mul_nonneg ha'nonneg (inv_nonneg.mpr hq.1.le)
    exact houtside.trans <| (le_max_left B 0).trans <| by linarith

/-- From every positive initial radius, all iterated squared-radius laws have
integrable reciprocal radius, uniformly bounded in time. -/
lemma exists_uniform_integral_inv_Kchain_pow_le
    {A : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ,
      Integrable (fun y : ℝ => y⁻¹) (((Kchain A N) ^ t) q) ∧
      ∫ y, y⁻¹ ∂((Kchain A N) ^ t) q ≤ C := by
  obtain ⟨_, _, a, ha, B, hfoster⟩ :=
    exists_Kchain_inv_foster_bound hA hN hdim
  let a' := max a 0
  let B' := max B 0
  have ha'0 : 0 ≤ a' := le_max_right _ _
  have ha'1 : a' < 1 := max_lt ha zero_lt_one
  have hB'0 : 0 ≤ B' := le_max_right _ _
  let V := fun y : ℝ => y⁻¹
  let m := fun t : ℕ => ∫ y, V y ∂((Kchain A N) ^ t) q
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2⟩
  have hsupport (t : ℕ) :
      ∀ᵐ x ∂((Kchain A N) ^ t) q, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact Kchain_pow_apply_Icc_compl A (by omega) hqIcc t
  have hstep_integrable (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      Integrable V (Kchain A N x) := by
    by_cases hx0 : x = 0
    · subst x
      rw [Kchain_zero]
      exact integrable_dirac (by simp [V])
    · exact integrable_inv_Kchain (by linarith)
        (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hN
  have hfoster_Icc (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      ∫ y, V y ∂Kchain A N x ≤ a' * V x + B' := by
    by_cases hx0 : x = 0
    · subst x
      simp [V, Kchain_zero, hB'0]
    · exact (hfoster x ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩).trans
        (add_le_add
          (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (inv_nonneg.mpr hx.1))
          (le_max_left _ _))
  have hnorm_action (x : ℝ) :
      (∫ y, ‖V y‖ ∂Kchain A N x) = ∫ y, V y ∂Kchain A N x := by
    rw [integral_Kchain A N x
      (by fun_prop : Measurable (fun y : ℝ => ‖V y‖)),
      integral_Kchain A N x
        (by fun_prop : Measurable V)]
    apply integral_congr_ae
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact inv_nonneg.mpr (Fmap_nonneg A N x g)
  have hpow_integrable :
      ∀ t : ℕ, Integrable V (((Kchain A N) ^ t) q) := by
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
              Integrable (fun x => a' * V x + B')
                (((Kchain A N) ^ t) q) :=
            (iht.const_mul a').add (integrable_const B')
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
            integral_nonneg_of_ae (Eventually.of_forall fun y => norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hnorm_action x]
          exact hfoster_Icc x hx
  have hrec (t : ℕ) : m (t + 1) ≤ a' * m t + B' := by
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
        Integrable (fun x => a' * V x + B')
          (((Kchain A N) ^ t) q) :=
      ((hpow_integrable t).const_mul a').add (integrable_const B')
    have hmono :
        (∫ x, (∫ y, V y ∂Kchain A N x)
            ∂((Kchain A N) ^ t) q) ≤
          ∫ x, (a' * V x + B') ∂((Kchain A N) ^ t) q :=
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
      _ ≤ ∫ x, (a' * V x + B') ∂((Kchain A N) ^ t) q := hmono
      _ = a' * m t + B' := by
        rw [integral_add ((hpow_integrable t).const_mul a')
          (integrable_const B'), integral_const_mul]
        simp [m]
  let C := max (m 0) (B' / (1 - a'))
  have hm0 : 0 ≤ m 0 := by
    dsimp [m]
    rw [pow_zero]
    change 0 ≤ ∫ y, V y ∂Measure.dirac q
    rw [integral_dirac]
    exact inv_nonneg.mpr hq.1.le
  have hC : 0 ≤ C := hm0.trans (le_max_left _ _)
  refine ⟨C, hC, fun t => ⟨hpow_integrable t, ?_⟩⟩
  exact geom_recursion_bound_contraction ha'0 ha'1 hrec t

/-- The positive-length Cesàro averages started from a positive radius have
integrable reciprocal radius, with the same uniform bound as the kernel
powers entering the average. -/
lemma exists_uniform_integral_inv_cesaroMeasure_le
    {A : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N)
    {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, 0 < T →
      Integrable (fun y : ℝ => y⁻¹)
        (cesaroMeasure (Kchain A N) q T) ∧
      ∫ y, y⁻¹ ∂cesaroMeasure (Kchain A N) q T ≤ C := by
  obtain ⟨C, hC, hpow⟩ :=
    exists_uniform_integral_inv_Kchain_pow_le hA hN hdim hq
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hsum :
      Integrable (fun y : ℝ => y⁻¹)
        (∑ t ∈ Finset.range T, ((Kchain A N) ^ t) q) := by
    exact integrable_finsetSum_measure.2 fun t _ => (hpow t).1
  have hcesaro :
      Integrable (fun y : ℝ => y⁻¹)
        (cesaroMeasure (Kchain A N) q T) := by
    unfold cesaroMeasure
    exact hsum.smul_measure (by
      exact ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hT.ne'))
  refine ⟨hcesaro, ?_⟩
  have hsum_le :
      (∑ t ∈ Finset.range T,
          ∫ y, y⁻¹ ∂((Kchain A N) ^ t) q) ≤
        ∑ _t ∈ Finset.range T, C := by
    exact Finset.sum_le_sum fun t _ => (hpow t).2
  calc
    (∫ y, y⁻¹ ∂cesaroMeasure (Kchain A N) q T) =
        ((T : ENNReal)⁻¹).toReal *
          ∑ t ∈ Finset.range T,
            ∫ y, y⁻¹ ∂((Kchain A N) ^ t) q := by
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

end AbsorptionCutoff
