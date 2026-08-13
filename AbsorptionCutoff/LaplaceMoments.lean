/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Negative moments from Laplace-transform bounds

This file packages the Mellin--Laplace identity and Tonelli argument used to
deduce negative real moments from integrable Laplace-transform envelopes.
-/

open MeasureTheory Set
open scoped Real

namespace AbsorptionCutoff

/-- An integrable envelope for the Laplace transform of an almost surely
positive random variable controls its negative real moment.

The almost-everywhere positivity assumption is essential: Mathlib defines
`0 ^ (-p) = 0` for `Real.rpow`, whereas the Mellin integral at zero diverges. -/
theorem integrable_neg_rpow_and_integral_le_of_laplace_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    {p : ℝ} (hp : 0 < p) {B : ℝ → ℝ}
    (hB : IntegrableOn (fun t : ℝ => t ^ (p - 1) * B t) (Ioi 0))
    (hLaplace : ∀ t : ℝ, 0 < t →
      (∫ ω, Real.exp (-(t * X ω)) ∂μ) ≤ B t) :
    Integrable (fun ω => X ω ^ (-p)) μ ∧
      (∫ ω, X ω ^ (-p) ∂μ) ≤
        (Real.Gamma p)⁻¹ *
          ∫ t in Ioi (0 : ℝ), t ^ (p - 1) * B t := by
  let K : ℝ × Ω → ℝ :=
    fun z => z.1 ^ (p - 1) * Real.exp (-(z.1 * X z.2))
  have hK : Measurable K := by
    dsimp only [K]
    fun_prop
  have hexp_int :
      ∀ t : ℝ, 0 < t →
        Integrable (fun ω => Real.exp (-(t * X ω))) μ := by
    intro t ht
    refine (integrable_const (1 : ℝ)).mono'
      ((hX.const_mul t).neg.exp.aestronglyMeasurable) ?_
    filter_upwards [hXpos] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg ht.le hω.le))
  let L : ℝ → ℝ :=
    fun t => t ^ (p - 1) * ∫ ω, Real.exp (-(t * X ω)) ∂μ
  have hL_eq :
      ∀ t : ℝ, 0 < t → (∫ ω, K (t, ω) ∂μ) = L t := by
    intro t ht
    dsimp only [K, L]
    rw [integral_const_mul]
  have hL_nonneg :
      ∀ t : ℝ, 0 < t → 0 ≤ L t := by
    intro t ht
    dsimp only [L]
    exact mul_nonneg (Real.rpow_nonneg ht.le _)
      (integral_nonneg fun _ => Real.exp_pos _ |>.le)
  have hL_le :
      ∀ t : ℝ, 0 < t → L t ≤ t ^ (p - 1) * B t := by
    intro t ht
    dsimp only [L]
    exact mul_le_mul_of_nonneg_left (hLaplace t ht)
      (Real.rpow_nonneg ht.le _)
  have hL_meas :
      AEStronglyMeasurable L (volume.restrict (Ioi 0)) := by
    have hint :
        StronglyMeasurable (fun t : ℝ => ∫ ω, K (t, ω) ∂μ) :=
      hK.stronglyMeasurable.integral_prod_right
    refine hint.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hL_eq t ht
  have hL_int : IntegrableOn L (Ioi 0) := by
    refine hB.mono' hL_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have henv_nonneg : 0 ≤ t ^ (p - 1) * B t :=
      (hL_nonneg t ht).trans (hL_le t ht)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hL_nonneg t ht),
      abs_of_nonneg henv_nonneg] using hL_le t ht
  have hK_int :
      Integrable K ((volume.restrict (Ioi 0)).prod μ) := by
    rw [integrable_prod_iff hK.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hexp_int t ht).const_mul (t ^ (p - 1))
    · refine hL_int.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      calc
        L t = ∫ ω, K (t, ω) ∂μ := (hL_eq t ht).symm
        _ = ∫ ω, ‖K (t, ω)‖ ∂μ := by
              apply integral_congr_ae
              filter_upwards [hXpos] with ω hω
              have hK_nonneg : 0 ≤ K (t, ω) := by
                dsimp only [K]
                exact mul_nonneg (Real.rpow_nonneg ht.le _)
                  (Real.exp_pos _).le
              rw [Real.norm_eq_abs, abs_of_nonneg hK_nonneg]
  have hswap :
      (∫ t in Ioi (0 : ℝ), ∫ ω, K (t, ω) ∂μ) =
        ∫ ω, (∫ t in Ioi (0 : ℝ), K (t, ω)) ∂μ := by
    exact integral_integral_swap
      (f := fun t ω => K (t, ω))
      (by
        change Integrable K ((volume.restrict (Ioi 0)).prod μ)
        exact hK_int)
  have hpoint :
      ∀ᵐ ω ∂μ,
        (∫ t in Ioi (0 : ℝ), K (t, ω)) =
          Real.Gamma p * X ω ^ (-p) := by
    filter_upwards [hXpos] with ω hω
    dsimp only [K]
    rw [show (∫ t in Ioi (0 : ℝ),
        t ^ (p - 1) * Real.exp (-(t * X ω))) =
        (1 / X ω) ^ p * Real.Gamma p by
      simpa only [mul_comm] using
        Real.integral_rpow_mul_exp_neg_mul_Ioi hp hω]
    rw [one_div, Real.inv_rpow hω.le, ← Real.rpow_neg hω.le]
    ring
  have hinner_int :
      Integrable (fun ω => ∫ t in Ioi (0 : ℝ), K (t, ω)) μ :=
    hK_int.integral_prod_right
  have hGamma : 0 < Real.Gamma p :=
    Real.Gamma_pos_of_pos hp
  have hneg_int : Integrable (fun ω => X ω ^ (-p)) μ := by
    have hscaled :
        Integrable (fun ω => Real.Gamma p * X ω ^ (-p)) μ :=
      hinner_int.congr hpoint
    exact (integrable_const_mul_iff
      (isUnit_iff_ne_zero.mpr hGamma.ne') _).mp hscaled
  have hMellin :
      (∫ ω, X ω ^ (-p) ∂μ) =
        (Real.Gamma p)⁻¹ * ∫ t in Ioi (0 : ℝ), L t := by
    calc
      (∫ ω, X ω ^ (-p) ∂μ) =
          (Real.Gamma p)⁻¹ *
            (Real.Gamma p * ∫ ω, X ω ^ (-p) ∂μ) := by
              field_simp
      _ = (Real.Gamma p)⁻¹ *
          (∫ ω, Real.Gamma p * X ω ^ (-p) ∂μ) := by
            rw [integral_const_mul]
      _ = (Real.Gamma p)⁻¹ *
          (∫ ω, (∫ t in Ioi (0 : ℝ), K (t, ω)) ∂μ) := by
            rw [integral_congr_ae (hpoint.mono fun _ h => h.symm)]
      _ = (Real.Gamma p)⁻¹ *
          ∫ t in Ioi (0 : ℝ), ∫ ω, K (t, ω) ∂μ := by
            rw [← hswap]
      _ = (Real.Gamma p)⁻¹ *
          ∫ t in Ioi (0 : ℝ), L t := by
            congr 1
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact hL_eq t ht
  refine ⟨hneg_int, ?_⟩
  rw [hMellin]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hGamma.le)
  apply integral_mono_ae hL_int hB
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hL_le t ht

/-- A unit interval below the peak scale gives an elementary lower bound for
the Gamma function.  This bound is sufficient to turn the truncated-Gaussian
moment estimate into an exponential-in-dimension estimate without invoking
Stirling's formula. -/
lemma exp_neg_add_one_mul_self_rpow_le_Gamma_add_one
    {p : ℝ} (hp : 0 < p) :
    Real.exp (-(p + 1)) * p ^ p ≤ Real.Gamma (p + 1) := by
  let f : ℝ → ℝ := fun x => Real.exp (-x) * x ^ p
  have hGammaInt : IntegrableOn f (Ioi 0) := by
    simpa only [f, add_sub_cancel_right] using
      Real.GammaIntegral_convergent (s := p + 1) (by linarith)
  have hlocal : IntervalIntegrable f volume p (p + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hGammaInt.mono_set
      (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hp.le))
  calc
    Real.exp (-(p + 1)) * p ^ p =
        ∫ _x : ℝ in p..p + 1, Real.exp (-(p + 1)) * p ^ p := by
          simp
    _ ≤ ∫ x : ℝ in p..p + 1, f x := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact intervalIntegrable_const
      · exact hlocal
      · intro x hx
        have hexp :
            Real.exp (-(p + 1)) ≤ Real.exp (-x) :=
          Real.exp_le_exp.mpr (by linarith [hx.2])
        have hpow : p ^ p ≤ x ^ p :=
          Real.rpow_le_rpow hp.le hx.1 hp.le
        exact mul_le_mul hexp hpow
          (Real.rpow_nonneg hp.le _) (Real.exp_pos _).le
    _ ≤ ∫ x : ℝ in Ioi 0, f x := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_mono_set hGammaInt
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (Real.exp_pos _).le
          (Real.rpow_nonneg hx.le _)
      · exact
          (Ioc_subset_Ioi_self.trans
            (Ioi_subset_Ioi hp.le)).eventuallyLE
    _ = Real.Gamma (p + 1) := by
      simpa only [f, add_sub_cancel_right] using
        (Real.Gamma_eq_integral (s := p + 1) (by linarith)).symm

/-- The elementary Gamma lower bound controls the Gamma-normalized power by
an explicit exponential factor. -/
lemma rpow_div_Gamma_add_one_le_exp_mul_div_rpow
    {n p : ℝ} (hn : 0 ≤ n) (hp : 0 < p) :
    n ^ p / Real.Gamma (p + 1) ≤
      Real.exp (p + 1) * (n / p) ^ p := by
  have hGammaLower :
      Real.exp (-(p + 1)) * p ^ p ≤ Real.Gamma (p + 1) :=
    exp_neg_add_one_mul_self_rpow_le_Gamma_add_one hp
  have hden :
      0 < Real.exp (-(p + 1)) * p ^ p :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hp _)
  calc
    n ^ p / Real.Gamma (p + 1) ≤
        n ^ p / (Real.exp (-(p + 1)) * p ^ p) :=
      div_le_div_of_nonneg_left
        (Real.rpow_nonneg hn _) hden hGammaLower
    _ = Real.exp (p + 1) * (n / p) ^ p := by
      rw [Real.div_rpow hn hp.le, Real.exp_neg]
      field_simp

end AbsorptionCutoff
