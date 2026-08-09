/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.PolarPerturbation
import AbsorptionCutoff.Lattice

/-!
# Integrating the polar perturbation estimate

Focused continuation of `AbsorptionCutoff/Supercritical/PolarPerturbation.lean`, which
reached 1038 lines and 85 s focused builds. That module owns the *pointwise*
half of `lem:nd-gaussian-polar-perturbation` — the change of variables, the
densities `p_r` and `p₀`, the Taylor bound, the annulus comparison, and the
envelope check. This module owns the *integrated* half, unit A-8a step 6f of the
same §7 argument:

`∫_{‖v‖₂<ρ} |p_r(v) − p₀(v)| dv ≤ C r^δ min{1, ρ^N}`,

which is `eq:nd-density-error-ball`, and then `lem:nd-gaussian-polar-perturbation`
itself with `ρ = e^{-t}` and the envelope `h(t) = min{1, e^{-Nt}}`.

The inputs it consumes from the base module are, in the order the paper uses
them: `abs_prod_sub_prod_gaussianPDFReal_le_of_box` (the pointwise bound on
`|r vᵢ| ≤ 1/2`), `volume_sum_sq_lt_le` and `one_add_sq_sum_sq_le_prod` (the two
elementary integration inputs), `lintegral_pi_prod` (to factor the product
weight), and `driNorm_exp_mul_polarEnvelope_ne_top` (the envelope condition).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AbsorptionCutoff

/-! ### The polynomial-weighted Gaussian integral, `ρ ≥ 1` branch

`eq:nd-density-error-ball`'s right-hand side is `min{1, ρ^N}`. The `1` branch
needs only that `∫_{ℝ^N}(1+‖v‖₂⁴)p₀ < ∞`, and `one_add_sq_sum_sq_le_prod`
reduces that to a *scalar* Gaussian fourth moment, which Mathlib has
(`memLp_id_gaussianReal`, all exponents). No constant is computed: the value of
this integral *is* the constant. -/

/-- The second and fourth moments of `gaussianReal`, in the `Integrable` form
the expansion of `(1+x²)²` needs. Extracted from `memLp_id_gaussianReal` — the
only work is converting an `rpow` norm bound into a natural power. -/
theorem integrable_pow_gaussianReal {σ2 : ℝ≥0} {n : ℕ} (hn : n = 2 ∨ n = 4) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 σ2) := by
  rcases hn with rfl | rfl
  · have h2 : MemLp id 2 (gaussianReal 0 σ2) := memLp_id_gaussianReal 2
    have h := h2.integrable_norm_rpow (by norm_num) (by norm_num)
    simp only [id_eq, Real.norm_eq_abs, ENNReal.toReal_ofNat] at h
    refine (integrable_congr ?_).1 h
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
  · have h4 : MemLp id 4 (gaussianReal 0 σ2) := memLp_id_gaussianReal 4
    have h := h4.integrable_norm_rpow (by norm_num) (by norm_num)
    simp only [id_eq, Real.norm_eq_abs, ENNReal.toReal_ofNat] at h
    refine (integrable_congr ?_).1 h
    filter_upwards with x
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]

theorem integrable_one_add_sq_sq (σ2 : ℝ≥0) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ 2) (gaussianReal 0 σ2) := by
  have h := ((integrable_const (1 : ℝ) (μ := gaussianReal 0 σ2)).add
    ((integrable_pow_gaussianReal (σ2 := σ2) (Or.inl rfl)).const_mul 2)).add
    (integrable_pow_gaussianReal (σ2 := σ2) (Or.inr rfl))
  refine (integrable_congr ?_).1 h
  filter_upwards with x
  simp only [Pi.add_apply]
  ring

/-- The scalar weighted integral is finite: `∫ (1+x²)² g(x) dx < ∞`. -/
theorem lintegral_one_add_sq_sq_gaussianPDFReal_ne_top {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ 2 * gaussianPDFReal 0 σ2 x) ≠ ∞ := by
  have hmeasG : Measurable fun x : ℝ => ENNReal.ofReal ((1 + x ^ 2) ^ 2) := by fun_prop
  have hrw : ∀ x : ℝ, ENNReal.ofReal ((1 + x ^ 2) ^ 2 * gaussianPDFReal 0 σ2 x)
      = (gaussianPDF 0 σ2 * fun x : ℝ => ENNReal.ofReal ((1 + x ^ 2) ^ 2)) x := by
    intro x
    rw [ENNReal.ofReal_mul (by positivity), gaussianPDF_def]
    simp only [Pi.mul_apply]
    ring
  simp only [hrw]
  rw [← lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF 0 σ2) hmeasG,
    ← gaussianReal_of_var_ne_zero 0 hσ]
  have hfin := (integrable_one_add_sq_sq σ2).hasFiniteIntegral
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hfin)
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (by positivity)]

/-- **`∫_{ℝ^N}(1 + ‖v‖₂⁴) p₀(v) dv < ∞`** — the `ρ ≥ 1` branch of
`eq:nd-density-error-ball`.

`one_add_sq_sum_sq_le_prod` dominates the integrand by the coordinatewise
product `∏ᵢ (1+vᵢ²)² g(vᵢ)`, `lintegral_pi_prod` factors that into the `N`-th
power of the scalar integral, and the scalar integral is finite by the Gaussian
fourth moment. -/
theorem lintegral_poly_gaussProd_ne_top {N : ℕ} {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) :
    ∫⁻ v : Fin N → ℝ,
        ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)) ≠ ∞ := by
  have hmeas : Measurable fun x : ℝ =>
      ENNReal.ofReal ((1 + x ^ 2) ^ 2 * gaussianPDFReal 0 σ2 x) :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun x : ℝ => (1 + x ^ 2) ^ 2).mul
      (measurable_gaussianPDFReal 0 σ2))
  have hdom : ∀ v : Fin N → ℝ,
      ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i))
        ≤ ∏ i, ENNReal.ofReal ((1 + (v i) ^ 2) ^ 2 * gaussianPDFReal 0 σ2 (v i)) := by
    intro v
    have hP : 0 ≤ ∏ i, gaussianPDFReal 0 σ2 (v i) :=
      Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
    have hstep : (1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)
        ≤ ∏ i, ((1 + (v i) ^ 2) ^ 2 * gaussianPDFReal 0 σ2 (v i)) := by
      rw [Finset.prod_mul_distrib]
      exact mul_le_mul_of_nonneg_right (one_add_sq_sum_sq_le_prod v) hP
    calc ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i))
        ≤ ENNReal.ofReal (∏ i, ((1 + (v i) ^ 2) ^ 2 * gaussianPDFReal 0 σ2 (v i))) :=
          ENNReal.ofReal_le_ofReal hstep
      _ = ∏ i, ENNReal.ofReal ((1 + (v i) ^ 2) ^ 2 * gaussianPDFReal 0 σ2 (v i)) :=
          ENNReal.ofReal_prod_of_nonneg fun i _ =>
            mul_nonneg (by positivity) (gaussianPDFReal_nonneg 0 σ2 (v i))
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hdom)
  rw [volume_pi, lintegral_pi_prod _ _ fun _ => hmeas, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  exact ENNReal.pow_ne_top (lintegral_one_add_sq_sq_gaussianPDFReal_ne_top hσ)

/-! ### The polynomial-weighted Gaussian integral, `ρ ≤ 1` branch

The paper's "the integrand is bounded near the origin" (tex L5113–5115), made
explicit: on `‖v‖₂ < ρ ≤ 1` the weight is at most `2` and the density at most
`p₀(0) = g(0)^N`, so the integral is at most a constant times the volume of the
ball — and `volume_sum_sq_lt_le` bounds that by `(2ρ)^N`. -/

/-- `∫_{‖v‖₂<ρ}(1 + ‖v‖₂⁴) p₀(v) dv ≤ C ρ^N` for `ρ ≤ 1`, with the explicit
constant `2 g(0)^N 2^N`. -/
theorem setLIntegral_poly_gaussProd_le {N : ℕ} {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i))
      ≤ ENNReal.ofReal (2 * gaussianPDFReal 0 σ2 0 ^ N) * ENNReal.ofReal ((2 * ρ) ^ N) := by
  set s : Set (Fin N → ℝ) := {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2} with hs
  have hsmeas : MeasurableSet s :=
    measurableSet_lt (by fun_prop : Measurable fun v : Fin N → ℝ => ∑ i, v i ^ 2)
      measurable_const
  have hM0 : 0 ≤ gaussianPDFReal 0 σ2 0 := gaussianPDFReal_nonneg 0 σ2 0
  have hpt : ∀ v ∈ s,
      ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i))
        ≤ ENNReal.ofReal (2 * gaussianPDFReal 0 σ2 0 ^ N) := by
    intro v hv
    simp only [hs, Set.mem_setOf_eq] at hv
    have hS0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hS1 : ∑ i, v i ^ 2 ≤ 1 := by nlinarith
    have hpoly : 1 + (∑ i, v i ^ 2) ^ 2 ≤ 2 := by nlinarith
    have hprod : ∏ i, gaussianPDFReal 0 σ2 (v i) ≤ gaussianPDFReal 0 σ2 0 ^ N := by
      calc ∏ i, gaussianPDFReal 0 σ2 (v i) ≤ ∏ _i : Fin N, gaussianPDFReal 0 σ2 0 :=
            Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i))
              (fun i _ => gaussianPDFReal_le_of_abs_le hσ0 (by simp))
        _ = gaussianPDFReal 0 σ2 0 ^ N := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hprod0 : 0 ≤ ∏ i, gaussianPDFReal 0 σ2 (v i) :=
      Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
    exact ENNReal.ofReal_le_ofReal (by nlinarith [pow_nonneg hM0 N])
  calc ∫⁻ v in s, ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i))
      ≤ ∫⁻ _v in s, ENNReal.ofReal (2 * gaussianPDFReal 0 σ2 0 ^ N) :=
        setLIntegral_mono_ae (by fun_prop) (by filter_upwards with v hv using hpt v hv)
    _ = ENNReal.ofReal (2 * gaussianPDFReal 0 σ2 0 ^ N) * volume s := by rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (2 * gaussianPDFReal 0 σ2 0 ^ N) * ENNReal.ofReal ((2 * ρ) ^ N) := by
        gcongr
        exact volume_sum_sq_lt_le hρ0

/-! ### The density error over a ball

The pointwise bound of `abs_prod_sub_prod_gaussianPDFReal_le_of_box`, integrated.
The hypothesis `ρ ≤ (2r)⁻¹` is exactly what puts the whole ball inside the box
`|r vᵢ| ≤ 1/2` where that bound holds; the region beyond `(2r)⁻¹` is the paper's
Gaussian-tail branch (tex L5111–5115) and is not treated here. -/

/-- The constant of `abs_prod_sub_prod_gaussianPDFReal_le_of_box`, named. -/
noncomputable def polarConst (N : ℕ) (σ2 : ℝ≥0) : ℝ :=
  max (((28 / 9) * (2 * (σ2 : ℝ))⁻¹ + 2)
        * Real.exp (2 * ((28 / 9) * (2 * (σ2 : ℝ))⁻¹ + 2))) ((4 / 3 : ℝ) ^ N + 1)

lemma polarConst_nonneg (N : ℕ) (σ2 : ℝ≥0) : 0 ≤ polarConst N σ2 :=
  le_trans (by positivity) (le_max_right _ _)

/-- **`∫_{‖v‖₂<ρ}|p_r − p₀| ≤ C r² ∫_{‖v‖₂<ρ}(1+‖v‖₂⁴)p₀`** for `ρ ≤ (2r)⁻¹`.

Combining this with `setLIntegral_poly_gaussProd_le` (`ρ ≤ 1`) and
`lintegral_poly_gaussProd_ne_top` (`ρ ≥ 1`) gives both branches of
`eq:nd-density-error-ball`'s `min{1, ρ^N}`, on the region where the pointwise
bound applies. -/
theorem setLIntegral_abs_density_sub_le {N : ℕ} {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0)
    (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρr : ρ ≤ (2 * r)⁻¹) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹
              * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
            - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (polarConst N σ2 * r ^ 2)
          * ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
              ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)) := by
  have hmeas : Measurable fun v : Fin N → ℝ =>
      ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul (by fun_prop) ?_)
    exact Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 σ2).comp (measurable_pi_apply i)
  have hρr' : ρ * (2 * r) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hρr (by positivity : (0 : ℝ) ≤ 2 * r)
    rwa [inv_mul_cancel₀ (by positivity : (2 * r) ≠ 0)] at h
  have hpt : ∀ v ∈ {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
      ENNReal.ofReal |∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹
              * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
            - ∏ i, gaussianPDFReal 0 σ2 (v i)|
        ≤ ENNReal.ofReal (polarConst N σ2 * r ^ 2)
            * ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)) := by
    intro v hv
    simp only [Set.mem_setOf_eq] at hv
    -- `‖v‖₂ < ρ ≤ (2r)⁻¹` gives the coordinatewise box condition
    have hbox : ∀ i, |r * v i| ≤ 1 / 2 := by
      intro i
      have hle : v i ^ 2 ≤ ∑ j, v j ^ 2 := Finset.single_le_sum (f := fun j => v j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have h2 : v i ^ 2 < ρ ^ 2 := lt_of_le_of_lt hle hv
      rw [abs_mul, abs_of_pos hr]
      nlinarith [abs_nonneg (v i), sq_abs (v i), sq_nonneg (|v i| - ρ)]
    have hb := abs_prod_sub_prod_gaussianPDFReal_le_of_box hσ hσ0 hr hr4 v hbox
    have hnn : (0 : ℝ) ≤ (1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i) :=
      mul_nonneg (by positivity)
        (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i))
    rw [← ENNReal.ofReal_mul (mul_nonneg (polarConst_nonneg N σ2) (sq_nonneg r))]
    refine ENNReal.ofReal_le_ofReal (hb.trans (le_of_eq ?_))
    rw [polarConst]
    ring
  calc ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2}, _
      ≤ ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
          ENNReal.ofReal (polarConst N σ2 * r ^ 2)
            * ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)) :=
        setLIntegral_mono_ae (hmeas.const_mul _).aemeasurable
          (by filter_upwards with v hv using hpt v hv)
    _ = _ := lintegral_const_mul _ hmeas

/-! ### The Gaussian tail beyond `(2r)⁻¹`

Tex L5111–5115. The region `‖v‖₂ > (2r)⁻¹` is not covered by the pointwise
density bound, and the paper handles it by the Gaussian tail alone. The estimate
is Chernoff's, done directly: on `‖v‖₂ ≥ R` we have `1 ≤ e^{c(‖v‖₂² − R²)}`, so
the tail integral is at most `e^{-cR²}` times a finite exponential moment, and
that moment factors over coordinates by `lintegral_pi_prod`.

The scalar exponential moment is *not* taken from `GaussianRadial.lean` — the
lemmas there (`mgf_sq_gaussianReal_of_lt`) are for variance `1`, and rescaling
them costs more than the direct computation, which is one line of algebra plus
Mathlib's `integrable_exp_neg_mul_sq`. -/

/-- The scalar Gaussian exponential moment `∫ e^{cx²} g(x) dx < ∞` for
`c < 1/(2σ²)`: the integrand is a constant times `e^{-bx²}` with
`b = 1/(2σ²) − c > 0`. -/
theorem lintegral_exp_mul_sq_gaussianPDFReal_ne_top {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2) {c : ℝ}
    (hc : c < (2 * (σ2 : ℝ))⁻¹) :
    ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x) ≠ ∞ := by
  set b : ℝ := (2 * (σ2 : ℝ))⁻¹ - c with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  set K : ℝ := (Real.sqrt (2 * Real.pi * σ2))⁻¹ with hK
  have hexp : ∀ x : ℝ, Real.exp (c * x ^ 2) * Real.exp (-x ^ 2 / (2 * (σ2 : ℝ)))
      = Real.exp (-b * x ^ 2) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    rw [hb]
    field_simp
    ring
  have hrw : ∀ x : ℝ, Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x
      = K * Real.exp (-b * x ^ 2) := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [sub_zero]
    calc Real.exp (c * x ^ 2) * (K * Real.exp (-x ^ 2 / (2 * (σ2 : ℝ))))
        = K * (Real.exp (c * x ^ 2) * Real.exp (-x ^ 2 / (2 * (σ2 : ℝ)))) := by ring
      _ = K * Real.exp (-b * x ^ 2) := by rw [hexp x]
  simp only [hrw]
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hfin := ((integrable_exp_neg_mul_sq hb0).const_mul K).hasFiniteIntegral
  refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hfin)
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (by positivity)]

/-- **The Gaussian tail** `∫_{‖v‖₂≥R} p₀ ≤ e^{-cR²} M^N`, `M` the scalar
exponential moment. Chernoff: `1 ≤ e^{c(‖v‖₂²−R²)}` on the tail region. -/
theorem setLIntegral_gaussProd_tail_le {N : ℕ} {σ2 : ℝ≥0} {c : ℝ} (hc0 : 0 < c) (R : ℝ) :
    ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
        ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i))
      ≤ ENNReal.ofReal (Real.exp (-c * R ^ 2))
          * (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N := by
  have hmeas : Measurable fun x : ℝ =>
      ENNReal.ofReal (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x) :=
    ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun x : ℝ =>
      Real.exp (c * x ^ 2)).mul (measurable_gaussianPDFReal 0 σ2))
  have hpt : ∀ v ∈ {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i))
        ≤ ENNReal.ofReal (Real.exp (-c * R ^ 2))
            * ∏ i, ENNReal.ofReal (Real.exp (c * (v i) ^ 2) * gaussianPDFReal 0 σ2 (v i)) := by
    intro v hv
    simp only [Set.mem_setOf_eq] at hv
    have hprodrw : ∏ i, ENNReal.ofReal (Real.exp (c * (v i) ^ 2) * gaussianPDFReal 0 σ2 (v i))
        = ENNReal.ofReal (∏ i, (Real.exp (c * (v i) ^ 2) * gaussianPDFReal 0 σ2 (v i))) :=
      (ENNReal.ofReal_prod_of_nonneg fun i _ =>
        mul_nonneg (Real.exp_nonneg _) (gaussianPDFReal_nonneg 0 σ2 (v i))).symm
    rw [hprodrw, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsplit : ∏ i, (Real.exp (c * (v i) ^ 2) * gaussianPDFReal 0 σ2 (v i))
        = Real.exp (c * ∑ i, (v i) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum]
    rw [hsplit, ← mul_assoc, ← Real.exp_add]
    have hP : 0 ≤ ∏ i, gaussianPDFReal 0 σ2 (v i) :=
      Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
    have hge : (1 : ℝ) ≤ Real.exp (-c * R ^ 2 + c * ∑ i, (v i) ^ 2) := by
      rw [Real.one_le_exp_iff]
      nlinarith
    nlinarith
  calc ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
        ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i))
      ≤ ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
          ENNReal.ofReal (Real.exp (-c * R ^ 2))
            * ∏ i, ENNReal.ofReal (Real.exp (c * (v i) ^ 2) * gaussianPDFReal 0 σ2 (v i)) :=
        setLIntegral_mono_ae (by fun_prop) (by filter_upwards with v hv using hpt v hv)
    _ ≤ ∫⁻ v : Fin N → ℝ, ENNReal.ofReal (Real.exp (-c * R ^ 2))
            * ∏ i, ENNReal.ofReal (Real.exp (c * (v i) ^ 2) * gaussianPDFReal 0 σ2 (v i)) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (Real.exp (-c * R ^ 2))
          * ∫⁻ v : Fin N → ℝ,
              ∏ i, ENNReal.ofReal (Real.exp (c * (v i) ^ 2) * gaussianPDFReal 0 σ2 (v i)) :=
        lintegral_const_mul _ (by fun_prop)
    _ = _ := by
        rw [volume_pi, lintegral_pi_prod _ _ fun _ => hmeas, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- **`e^{-c/r²} ≤ c⁻¹ r^δ`** for `0 < r ≤ 1` and `δ ≤ 2` (tex L5115: "the
Gaussian tail is then bounded by `Ce^{-c/r²} ≤ Cr^δ`").

Only `e^x ≥ x` is needed, because the paper fixes `δ < 2`: that gives
`e^{-c/r²} ≤ r²/c`, and `r² ≤ r^δ` for `r ≤ 1`. A larger `δ` would need a
higher-order term of the exponential series. -/
theorem exp_neg_div_sq_le {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : δ ≤ 2) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) : Real.exp (-(c / r ^ 2)) ≤ c⁻¹ * r ^ δ := by
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hexp : c / r ^ 2 ≤ Real.exp (c / r ^ 2) := by
    have := Real.add_one_le_exp (c / r ^ 2)
    linarith
  have hpos : (0 : ℝ) < Real.exp (c / r ^ 2) := Real.exp_pos _
  rw [div_le_iff₀ hr2] at hexp
  have hstep : Real.exp (-(c / r ^ 2)) ≤ r ^ 2 / c := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos,
      show r ^ 2 / c * Real.exp (c / r ^ 2) = Real.exp (c / r ^ 2) * r ^ 2 / c by ring,
      le_div_iff₀ hc]
    linarith
  refine hstep.trans ?_
  have hrpow : r ^ (2 : ℝ) ≤ r ^ δ := Real.rpow_le_rpow_of_exponent_ge hr hr1 hδ
  rw [show r ^ (2 : ℕ) = r ^ (2 : ℝ) by rw [← Real.rpow_natCast r 2]; norm_num, div_eq_inv_mul]
  gcongr

/-- The tail scale used in `eq:nd-density-error-ball`, rewritten in the form
accepted by `exp_neg_div_sq_le`. -/
theorem exp_neg_mul_two_mul_inv_sq_le {c : ℝ} (hc : 0 < c) {δ : ℝ} (hδ : δ ≤ 2)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Real.exp (-c * ((2 * r)⁻¹) ^ 2) ≤ (4 / c) * r ^ δ := by
  calc
    Real.exp (-c * ((2 * r)⁻¹) ^ 2) = Real.exp (-((c / 4) / r ^ 2)) := by
      congr 1
      field_simp [ne_of_gt hr]
      norm_num
    _ ≤ (c / 4)⁻¹ * r ^ δ := exp_neg_div_sq_le (by positivity) hδ hr hr1
    _ = (4 / c) * r ^ δ := by
      congr 1
      field_simp [ne_of_gt hc]

/-- **`eq:nd-density-error-ball`, the `ρ ≤ 1` branch**:
`∫_{‖v‖₂<ρ}|p_r − p₀| ≤ C r² ρ^N` for `0 < r ≤ 1/4`.

Here the paper's outer region is **empty**, and that is worth recording: `r ≤ 1/4`
forces `(2r)⁻¹ ≥ 2 > 1 ≥ ρ`, so the whole ball already lies inside the box where
the pointwise bound holds and no tail estimate is needed. (This is why the
paper's `ρ < 1` bookkeeping at tex L5117–5122 — which concludes `r > 1/2` — is
vacuous in this branch.) -/
theorem setLIntegral_abs_density_sub_le_pow {N : ℕ} {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0)
    (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹
              * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
            - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (polarConst N σ2 * r ^ 2
          * (2 * gaussianPDFReal 0 σ2 0 ^ N * (2 * ρ) ^ N)) := by
  have hg0 : (0 : ℝ) ≤ gaussianPDFReal 0 σ2 0 := gaussianPDFReal_nonneg 0 σ2 0
  have hρr : ρ ≤ (2 * r)⁻¹ := by
    have h2 : (2 : ℝ) ≤ (2 * r)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]
      linarith
    linarith
  calc ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹
              * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
            - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (polarConst N σ2 * r ^ 2)
          * ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
              ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)) :=
        setLIntegral_abs_density_sub_le hσ hσ0 hr hr4 hρ0 hρr
    _ ≤ ENNReal.ofReal (polarConst N σ2 * r ^ 2)
          * (ENNReal.ofReal (2 * gaussianPDFReal 0 σ2 0 ^ N) * ENNReal.ofReal ((2 * ρ) ^ N)) := by
        gcongr
        exact setLIntegral_poly_gaussProd_le hσ0 hρ0 hρ1
    _ = ENNReal.ofReal (polarConst N σ2 * r ^ 2
          * (2 * gaussianPDFReal 0 σ2 0 ^ N * (2 * ρ) ^ N)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul
          (mul_nonneg (polarConst_nonneg N σ2) (sq_nonneg r))]

/-! ### Bridge: the density product is the law's density

The pointwise estimates are stated for the explicit real product
`∏ᵢ((1−r²vᵢ²)⁻¹ g(T_r⁻¹vᵢ))`, while `map_tanhScaleVec_withDensity` produces
`∏ᵢ tanhScaleDensity r p (vᵢ)` in `ℝ≥0∞`. On the box the two agree; this is the
bookkeeping that lets the measure-level and density-level halves compose. -/

/-- On the box `(−r⁻¹, r⁻¹)^N`, the `ℝ≥0∞`-valued density of `T_r U` is the
`ofReal` of the explicit real product the estimates use. -/
theorem prod_tanhScaleDensity_gaussianPDF {N : ℕ} {σ2 : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (v : Fin N → ℝ) (hv : ∀ i, v i ∈ Set.Ioo (-r⁻¹) r⁻¹) :
    ∏ i, tanhScaleDensity r (gaussianPDF 0 σ2) (v i)
      = ENNReal.ofReal
          (∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))) := by
  have hpos : ∀ i, (0 : ℝ) < 1 - r ^ 2 * (v i) ^ 2 := fun i =>
    one_sub_sq_pos (mul_mem_Ioo_of_mem_Ioo_inv hr (hv i))
  have hfac : ∀ i : Fin N, tanhScaleDensity r (gaussianPDF 0 σ2) (v i)
      = ENNReal.ofReal ((1 - r ^ 2 * (v i) ^ 2)⁻¹
          * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i))) := by
    intro i
    rw [tanhScaleDensity, Set.indicator_of_mem (hv i), gaussianPDF_def,
      ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 (hpos i)))]
  simp only [hfac]
  exact (ENNReal.ofReal_prod_of_nonneg fun i _ =>
    mul_nonneg (le_of_lt (inv_pos.2 (hpos i))) (gaussianPDFReal_nonneg 0 σ2 _)).symm

/-! ### `p_r` as a real density on all of `ℝ^N`

A formulation point that matters for the large-`ρ` branch. The estimates above
are stated for the explicit product `∏ᵢ((1−r²vᵢ²)⁻¹g(T_r⁻¹vᵢ))`, which is the
density only *inside* the box — outside it the factors are meaningless while the
true density is `0`. `eq:nd-nonlinear-linearized-density` says so explicitly: the
paper's `p_r` carries the indicator `1_{|rvᵢ|<1, 1≤i≤N}`.

For `ρ ≤ 1` this never showed, because `r ≤ 1/4` keeps the whole ball inside the
box. For `ρ > (2r)⁻¹` it does, so `p_r` is defined here *with* the indicator, and
`ofReal_polarDensityReal` identifies it with the `ℝ≥0∞` density of the law
everywhere — inside the box by the bridge, outside because a factor vanishes. -/

/-- The box `(−r⁻¹, r⁻¹)^N` on which `T_r` is a diffeomorphism. -/
def polarBox (N : ℕ) (r : ℝ) : Set (Fin N → ℝ) := {v | ∀ i, v i ∈ Set.Ioo (-r⁻¹) r⁻¹}

lemma measurableSet_polarBox (N : ℕ) (r : ℝ) : MeasurableSet (polarBox N r) := by
  rw [polarBox, Set.setOf_forall]
  exact MeasurableSet.iInter fun i => (measurable_pi_apply i) measurableSet_Ioo

/-- The paper's `p_r` (tex L5053–5058), indicator included. -/
noncomputable def polarDensityReal (N : ℕ) (σ2 : ℝ≥0) (r : ℝ) : (Fin N → ℝ) → ℝ :=
  (polarBox N r).indicator
    (fun v => ∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i))))

/-- **`p_r` really is the density of `T_r U`**, at every `v`: `ofReal ∘ p_r` is
the `ℝ≥0∞` density produced by `map_tanhScaleVec_withDensity`. Inside the box
this is `prod_tanhScaleDensity_gaussianPDF`; outside, both sides vanish — the
left by the indicator, the right because the offending coordinate's factor is
`0`. -/
theorem ofReal_polarDensityReal {N : ℕ} {σ2 : ℝ≥0} {r : ℝ} (hr : 0 < r) (v : Fin N → ℝ) :
    ENNReal.ofReal (polarDensityReal N σ2 r v)
      = ∏ i, tanhScaleDensity r (gaussianPDF 0 σ2) (v i) := by
  by_cases hv : v ∈ polarBox N r
  · rw [polarDensityReal, Set.indicator_of_mem hv, prod_tanhScaleDensity_gaussianPDF hr v hv]
  · rw [polarDensityReal, Set.indicator_of_notMem hv, ENNReal.ofReal_zero]
    rw [polarBox, Set.mem_setOf_eq, not_forall] at hv
    obtain ⟨i, hi⟩ := hv
    exact (Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [tanhScaleDensity, Set.indicator_of_notMem hi])).symm

/-- The pointwise regime `|r vᵢ| ≤ 1/2` puts `v` in the box, where the indicator
is inactive. -/
lemma mem_polarBox_of_abs_le {N : ℕ} {r : ℝ} (hr : 0 < r) {v : Fin N → ℝ}
    (hbox : ∀ i, |r * v i| ≤ 1 / 2) : v ∈ polarBox N r := by
  intro i
  have h := hbox i
  rw [abs_mul, abs_of_pos hr] at h
  have h1 : |v i| ≤ 1 / (2 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
  have h2 : 1 / (2 * r) < r⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt hr (by linarith)
  exact Set.mem_Ioo.2 (abs_lt.1 (lt_of_le_of_lt h1 h2))

/-- **The pointwise density bound, for `p_r` proper** — `abs_prod_sub_prod_…_of_box`
restated for `polarDensityReal`, which is what the large-`ρ` branch integrates.
On the regime `|r vᵢ| ≤ 1/2` the indicator is inactive, so the two agree. -/
theorem abs_polarDensityReal_sub_le {N : ℕ} {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0)
    (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (v : Fin N → ℝ)
    (hbox : ∀ i, |r * v i| ≤ 1 / 2) :
    |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ polarConst N σ2 * r ^ 2 * (1 + (∑ i, v i ^ 2) ^ 2)
          * ∏ i, gaussianPDFReal 0 σ2 (v i) := by
  rw [polarDensityReal, Set.indicator_of_mem (mem_polarBox_of_abs_le hr hbox)]
  exact abs_prod_sub_prod_gaussianPDFReal_le_of_box hσ hσ0 hr hr4 v hbox

/-- Off the box `p_r` vanishes, so there `|p_r − p₀| = p₀` and the Gaussian tail
bound alone covers the difference. -/
lemma polarDensityReal_of_notMem {N : ℕ} {σ2 : ℝ≥0} {r : ℝ} {v : Fin N → ℝ}
    (hv : v ∉ polarBox N r) : polarDensityReal N σ2 r v = 0 := by
  rw [polarDensityReal, Set.indicator_of_notMem hv]

/-! ### The transformed law's tail is dominated by the Gaussian one

The paper's reason for not estimating `p_r`'s tail separately (tex L5109–5110):
"for the `p_r` term this is because `‖T_rU‖₂ ≤ ‖U‖₂`". That is a statement about
*measures*, not densities, and it is cleanest to prove it that way — the
inclusion of preimages holds for an arbitrary law, no Gaussianity and no density
involved. `tanh` contracts, so `T_r` does too, coordinatewise. -/

/-- `T_r` contracts the Euclidean norm, coordinatewise. Uses the project's own
`abs_tanh_le_abs` (`Lattice.lean`) — this is why the module imports it. -/
theorem sum_sq_tanhScale_le {N : ℕ} {r : ℝ} (hr : 0 < r) (u : Fin N → ℝ) :
    ∑ i, (tanhScale r (u i)) ^ 2 ≤ ∑ i, (u i) ^ 2 := by
  refine Finset.sum_le_sum fun i _ => ?_
  have h : |tanhScale r (u i)| ≤ |u i| := by
    rw [tanhScale, abs_mul, abs_of_pos (inv_pos.2 hr)]
    have h2 := abs_tanh_le_abs (r * u i)
    rw [abs_mul, abs_of_pos hr] at h2
    calc r⁻¹ * |Real.tanh (r * u i)| ≤ r⁻¹ * (r * |u i|) := by gcongr
      _ = |u i| := by field_simp
  nlinarith [sq_abs (tanhScale r (u i)), sq_abs (u i), abs_nonneg (tanhScale r (u i)),
    abs_nonneg (u i)]

/-- **The tail of `T_r U` is no heavier than the tail of `U`**, for *any* law
`ν`: `{u : ‖T_r u‖₂ ≥ R} ⊆ {u : ‖u‖₂ ≥ R}`. Applied at the Gaussian law this is
the `p_r` half of the tail region `‖v‖₂ > (2r)⁻¹`, and it means
`setLIntegral_gaussProd_tail_le` covers both densities. -/
theorem map_tanhScaleVec_tail_le {N : ℕ} {r : ℝ} (hr : 0 < r) (ν : Measure (Fin N → ℝ))
    (R : ℝ) :
    (Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i)) ν)
        {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2}
      ≤ ν {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2} := by
  have hmeas : Measurable fun v : Fin N → ℝ => fun i => tanhScale r (v i) :=
    measurable_pi_lambda _ fun i => (measurable_tanhScale r).comp (measurable_pi_apply i)
  have hset : MeasurableSet {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [Measure.map_apply hmeas hset]
  refine measure_mono fun u hu => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hu ⊢
  exact hu.trans (sum_sq_tanhScale_le hr u)

/-- **The `p_r` tail is bounded by the `p₀` tail**, as an integral of densities.

This is where the measure-level `map_tanhScaleVec_tail_le` is cashed in: the
integral of `p_r` over the tail *is* the law of `T_r U` there
(`ofReal_polarDensityReal` and `map_tanhScaleVec_withDensity`), that law's tail
is dominated by `U`'s, and `U`'s tail is the integral of `p₀`. -/
theorem setLIntegral_polarDensityReal_tail_le {N : ℕ} {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) {r : ℝ}
    (hr : 0 < r) (R : ℝ) :
    ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
        ENNReal.ofReal (polarDensityReal N σ2 r v)
      ≤ ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
          ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) := by
  set s : Set (Fin N → ℝ) := {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2} with hsdef
  have hs : MeasurableSet s :=
    measurableSet_le measurable_const (by fun_prop)
  haveI hprob : IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF 0 σ2)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hσ]; infer_instance
  have hdens : Measurable fun v : Fin N → ℝ =>
      ∏ i, tanhScaleDensity r (gaussianPDF 0 σ2) (v i) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_tanhScaleDensity (measurable_gaussianPDF 0 σ2)).comp (measurable_pi_apply i)
  have hdens0 : Measurable fun v : Fin N → ℝ => ∏ i, gaussianPDF 0 σ2 (v i) :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF 0 σ2).comp (measurable_pi_apply i)
  calc ∫⁻ v in s, ENNReal.ofReal (polarDensityReal N σ2 r v)
      = ∫⁻ v in s, ∏ i, tanhScaleDensity r (gaussianPDF 0 σ2) (v i) :=
        lintegral_congr fun v => ofReal_polarDensityReal hr v
    _ = ((volume : Measure (Fin N → ℝ)).withDensity
          (fun v => ∏ i, tanhScaleDensity r (gaussianPDF 0 σ2) (v i))) s :=
        (withDensity_apply _ hs).symm
    _ = (Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i))
          (Measure.pi fun _ : Fin N => (volume : Measure ℝ).withDensity (gaussianPDF 0 σ2))) s := by
        rw [map_tanhScaleVec_withDensity hr (measurable_gaussianPDF 0 σ2)]
    _ ≤ (Measure.pi fun _ : Fin N => (volume : Measure ℝ).withDensity (gaussianPDF 0 σ2)) s :=
        map_tanhScaleVec_tail_le hr _ R
    _ = ((volume : Measure (Fin N → ℝ)).withDensity (fun v => ∏ i, gaussianPDF 0 σ2 (v i))) s := by
        rw [pi_withDensity_volume (measurable_gaussianPDF 0 σ2)]
    _ = ∫⁻ v in s, ∏ i, gaussianPDF 0 σ2 (v i) := withDensity_apply _ hs
    _ = ∫⁻ v in s, ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) := by
        refine lintegral_congr fun v => ?_
        rw [gaussianPDF_def]
        exact (ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)).symm

/-! ### `eq:nd-density-error-ball`, assembled

The inner estimate restated for `p_r` proper, then the two regions added. -/

lemma polarDensityReal_nonneg {N : ℕ} {σ2 : ℝ≥0} {r : ℝ} (hr : 0 < r) (v : Fin N → ℝ) :
    0 ≤ polarDensityReal N σ2 r v := by
  refine Set.indicator_nonneg (fun w hw => Finset.prod_nonneg fun i _ => ?_) v
  exact mul_nonneg (le_of_lt (inv_pos.2 (one_sub_sq_pos (mul_mem_Ioo_of_mem_Ioo_inv hr (hw i)))))
    (gaussianPDFReal_nonneg 0 σ2 _)

lemma measurable_polarDensityReal {N : ℕ} {σ2 : ℝ≥0} {r : ℝ} :
    Measurable (polarDensityReal N σ2 r) := by
  refine Measurable.indicator (Finset.measurable_prod _ fun i _ => ?_) (measurableSet_polarBox N r)
  exact (by fun_prop : Measurable fun v : Fin N → ℝ => (1 - r ^ 2 * (v i) ^ 2)⁻¹).mul
    (((measurable_gaussianPDFReal 0 σ2).comp (measurable_tanhScaleInv r)).comp
      (measurable_pi_apply i))

/-- On a ball of radius `ρ ≤ (2r)⁻¹` the indicator in `p_r` is inactive, so the
two integrands — `p_r` and the bare product — agree. This is the single
congruence that transfers every estimate stated for the explicit product to
`p_r` proper. -/
lemma setLIntegral_abs_polarDensityReal_congr {N : ℕ} {σ2 : ℝ≥0} {r : ℝ} (hr : 0 < r)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρr : ρ ≤ (2 * r)⁻¹) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      = ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
          ENNReal.ofReal |∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹
                * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
              - ∏ i, gaussianPDFReal 0 σ2 (v i)| := by
  have hρr' : ρ * (2 * r) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hρr (by positivity : (0 : ℝ) ≤ 2 * r)
    rwa [inv_mul_cancel₀ (by positivity : (2 * r) ≠ 0)] at h
  refine setLIntegral_congr_fun (measurableSet_lt (by fun_prop) measurable_const) ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  have hbox : ∀ i, |r * v i| ≤ 1 / 2 := by
    intro i
    have hle : v i ^ 2 ≤ ∑ j, v j ^ 2 := Finset.single_le_sum (f := fun j => v j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : v i ^ 2 < ρ ^ 2 := lt_of_le_of_lt hle hv
    rw [abs_mul, abs_of_pos hr]
    nlinarith [abs_nonneg (v i), sq_abs (v i), sq_nonneg (|v i| - ρ)]
  change ENNReal.ofReal
      |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)| = _
  rw [polarDensityReal, Set.indicator_of_mem (mem_polarBox_of_abs_le hr hbox)]

/-- `setLIntegral_abs_density_sub_le` for `polarDensityReal`. -/
theorem setLIntegral_abs_polarDensityReal_sub_le {N : ℕ} {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0)
    (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρr : ρ ≤ (2 * r)⁻¹) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (polarConst N σ2 * r ^ 2)
          * ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
              ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)) := by
  rw [setLIntegral_abs_polarDensityReal_congr hr hρ0 hρr]
  exact setLIntegral_abs_density_sub_le hσ hσ0 hr hr4 hρ0 hρr

/-- `setLIntegral_abs_density_sub_le_pow` for `polarDensityReal`: the `ρ ≤ 1`
branch of `eq:nd-density-error-ball`, stated for `p_r` proper. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_pow {N : ℕ} {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0)
    (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (polarConst N σ2 * r ^ 2
          * (2 * gaussianPDFReal 0 σ2 0 ^ N * (2 * ρ) ^ N)) := by
  have hρr : ρ ≤ (2 * r)⁻¹ := by
    have h2 : (2 : ℝ) ≤ (2 * r)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]
      linarith
    linarith
  rw [setLIntegral_abs_polarDensityReal_congr hr hρ0 hρr]
  exact setLIntegral_abs_density_sub_le_pow hσ hσ0 hr hr4 hρ0 hρ1

/-- **`eq:nd-density-error-ball`, the unrestricted-`ρ` branch** (tex L5111–5115):

`∫_{‖v‖₂<ρ}|p_r − p₀| ≤ C r² · I + 2 e^{-c/(4r²)} M^N`  for **every** `ρ`,

with no `ρ^N` factor (`I` the finite weighted Gaussian integral, `M` the scalar
exponential moment). The ball is enlarged to all of `ℝ^N` and split at
`R = (2r)⁻¹`: inside, the pointwise bound; outside, `|p_r − p₀| ≤ p_r + p₀` with
both tails bounded by the Gaussian one. Converting the two `r`-factors to `r^δ`
is `exp_neg_div_sq_le`. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_const {N : ℕ} {σ2 : ℝ≥0} (hσ : σ2 ≠ 0)
    (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) {c : ℝ} (hc0 : 0 < c)
    (ρ : ℝ) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (polarConst N σ2 * r ^ 2)
            * (∫⁻ v : Fin N → ℝ,
                ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i)))
          + 2 * (ENNReal.ofReal (Real.exp (-c * ((2 * r)⁻¹) ^ 2))
            * (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N) := by
  set R : ℝ := (2 * r)⁻¹ with hR
  set f : (Fin N → ℝ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)| with hf
  have hball : MeasurableSet {v : Fin N → ℝ | ∑ i, v i ^ 2 < R ^ 2} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hR0 : 0 ≤ R := by positivity
  have hσ' : (σ2 : ℝ) ≠ 0 := ne_of_gt hσ0
  have hsplit : ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2}, f v
      ≤ (∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < R ^ 2}, f v)
        + ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < R ^ 2}ᶜ, f v := by
    rw [lintegral_add_compl _ hball]
    exact setLIntegral_le_lintegral _ _
  refine hsplit.trans (add_le_add ?_ ?_)
  · refine (setLIntegral_abs_polarDensityReal_sub_le hσ' hσ0 hr hr4 hR0 le_rfl).trans ?_
    gcongr
    exact Measure.restrict_le_self
  · have hcompl : {v : Fin N → ℝ | ∑ i, v i ^ 2 < R ^ 2}ᶜ
        = {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2} := by
      ext v; simp [Set.mem_compl_iff, not_lt]
    rw [hcompl]
    have hpt : ∀ v : Fin N → ℝ, f v
        ≤ ENNReal.ofReal (polarDensityReal N σ2 r v)
          + ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) := by
      intro v
      have ha := polarDensityReal_nonneg (σ2 := σ2) hr v
      have hb : (0 : ℝ) ≤ ∏ i, gaussianPDFReal 0 σ2 (v i) :=
        Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
      have h1 : |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
          ≤ polarDensityReal N σ2 r v + ∏ i, gaussianPDFReal 0 σ2 (v i) := by
        rw [abs_le]; constructor <;> linarith
      rw [hf]
      exact (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq (ENNReal.ofReal_add ha hb))
    calc ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2}, f v
        ≤ ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
            (ENNReal.ofReal (polarDensityReal N σ2 r v)
              + ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i))) := lintegral_mono hpt
      _ = (∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
              ENNReal.ofReal (polarDensityReal N σ2 r v))
          + ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
              ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) :=
          lintegral_add_left (ENNReal.measurable_ofReal.comp measurable_polarDensityReal) _
      _ ≤ (∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
              ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)))
          + ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
              ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) :=
          add_le_add (setLIntegral_polarDensityReal_tail_le hσ hr R) le_rfl
      _ = 2 * ∫⁻ v in {v : Fin N → ℝ | R ^ 2 ≤ ∑ i, v i ^ 2},
              ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) := (two_mul _).symm
      _ ≤ 2 * (ENNReal.ofReal (Real.exp (-c * R ^ 2))
            * (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N) := by
          gcongr
          exact setLIntegral_gaussProd_tail_le hc0 R

/-- The unrestricted-radius branch of `eq:nd-density-error-ball`, with both
small parameters converted to `r ^ δ`.  The remaining factor is independent of
`r` and `ρ`. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_rpow {N : ℕ} {σ2 : ℝ≥0}
    (hσ : σ2 ≠ 0) (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    {c δ : ℝ} (hc0 : 0 < c) (hδ : δ ≤ 2) (ρ : ℝ) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (r ^ δ) *
          (ENNReal.ofReal (polarConst N σ2) *
              (∫⁻ v : Fin N → ℝ,
                ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) *
                  ∏ i, gaussianPDFReal 0 σ2 (v i)))
            + 2 * (ENNReal.ofReal (4 / c) *
              (∫⁻ x : ℝ, ENNReal.ofReal
                (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N)) := by
  refine (setLIntegral_abs_polarDensityReal_sub_le_const hσ hσ0 hr hr4 hc0 ρ).trans ?_
  have hr1 : r ≤ 1 := by linarith
  have hrpow : r ^ (2 : ℕ) ≤ r ^ δ := by
    rw [show r ^ (2 : ℕ) = r ^ (2 : ℝ) by rw [← Real.rpow_natCast r 2]; norm_num]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 hδ
  have htail := exp_neg_mul_two_mul_inv_sq_le hc0 hδ hr hr1
  rw [ENNReal.ofReal_mul (polarConst_nonneg N σ2)]
  rw [mul_add]
  refine add_le_add ?_ ?_
  · calc
      ENNReal.ofReal (polarConst N σ2) * ENNReal.ofReal (r ^ 2) *
          (∫⁻ v : Fin N → ℝ, ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) *
            ∏ i, gaussianPDFReal 0 σ2 (v i)))
        ≤ ENNReal.ofReal (polarConst N σ2) * ENNReal.ofReal (r ^ δ) *
          (∫⁻ v : Fin N → ℝ, ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) *
            ∏ i, gaussianPDFReal 0 σ2 (v i))) := by
          exact mul_le_mul_left (mul_le_mul_right (ENNReal.ofReal_le_ofReal hrpow) _) _
      _ = ENNReal.ofReal (r ^ δ) *
          (ENNReal.ofReal (polarConst N σ2) *
            (∫⁻ v : Fin N → ℝ, ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) *
              ∏ i, gaussianPDFReal 0 σ2 (v i)))) := by ac_rfl
  · have hof : ENNReal.ofReal (Real.exp (-c * ((2 * r)⁻¹) ^ 2)) ≤
        ENNReal.ofReal (4 / c) * ENNReal.ofReal (r ^ δ) := by
      calc
        ENNReal.ofReal (Real.exp (-c * ((2 * r)⁻¹) ^ 2))
            ≤ ENNReal.ofReal ((4 / c) * r ^ δ) := ENNReal.ofReal_le_ofReal htail
        _ = ENNReal.ofReal (4 / c) * ENNReal.ofReal (r ^ δ) := by
          rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 / c)]
    calc
      2 * (ENNReal.ofReal (Real.exp (-c * ((2 * r)⁻¹) ^ 2)) *
          (∫⁻ x : ℝ, ENNReal.ofReal
            (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N)
        ≤ 2 * ((ENNReal.ofReal (4 / c) * ENNReal.ofReal (r ^ δ)) *
          (∫⁻ x : ℝ, ENNReal.ofReal
            (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N) := by
          exact mul_le_mul_right (mul_le_mul_left hof _) _
      _ = ENNReal.ofReal (r ^ δ) *
          (2 * (ENNReal.ofReal (4 / c) *
            (∫⁻ x : ℝ, ENNReal.ofReal
              (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N)) := by ac_rfl

/-- The small-ball branch of `eq:nd-density-error-ball`, with its dependence on
the radius exposed as `r ^ δ * ρ ^ N`. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_rpow_mul_pow {N : ℕ} {σ2 : ℝ≥0}
    (hσ : (σ2 : ℝ) ≠ 0) (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r)
    (hr4 : r ≤ 1 / 4) {δ ρ : ℝ} (hδ : δ ≤ 2) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (r ^ δ * ρ ^ N) *
          ENNReal.ofReal (polarConst N σ2 *
            (2 * gaussianPDFReal 0 σ2 0 ^ N * 2 ^ N)) := by
  refine (setLIntegral_abs_polarDensityReal_sub_le_pow hσ hσ0 hr hr4 hρ0 hρ1).trans ?_
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (Real.rpow_nonneg hr.le δ) (pow_nonneg hρ0 N))]
  apply ENNReal.ofReal_le_ofReal
  have hr1 : r ≤ 1 := by linarith
  have hrpow : r ^ (2 : ℕ) ≤ r ^ δ := by
    rw [show r ^ (2 : ℕ) = r ^ (2 : ℝ) by rw [← Real.rpow_natCast r 2]; norm_num]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 hδ
  calc
    polarConst N σ2 * r ^ 2 *
        (2 * gaussianPDFReal 0 σ2 0 ^ N * (2 * ρ) ^ N) =
        r ^ 2 * ρ ^ N *
          (polarConst N σ2 * (2 * gaussianPDFReal 0 σ2 0 ^ N * 2 ^ N)) := by
          rw [mul_pow]
          ring
    _ ≤ r ^ δ * ρ ^ N *
          (polarConst N σ2 * (2 * gaussianPDFReal 0 σ2 0 ^ N * 2 ^ N)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hrpow (pow_nonneg hρ0 N))
        (mul_nonneg (polarConst_nonneg N σ2)
          (mul_nonneg
            (mul_nonneg (by norm_num) (pow_nonneg (gaussianPDFReal_nonneg 0 σ2 0) N))
            (pow_nonneg (by norm_num) N)))
    _ = r ^ δ * ρ ^ N *
          (polarConst N σ2 * (2 * gaussianPDFReal 0 σ2 0 ^ N * 2 ^ N)) := rfl

/-! ### The moderate-`r` branch

The paper bounds the transformed density on a compact range of positive `r`.
The scalar analytic input is that a Gaussian beats the two powers of `cosh`
arising from the Jacobian. -/

/-- A Gaussian uniformly absorbs the squared hyperbolic-cosine Jacobian:
`e^{-c x²} cosh(x)² ≤ e^{1/c}`. -/
theorem exp_neg_mul_sq_mul_cosh_sq_le {c x : ℝ} (hc : 0 < c) :
    Real.exp (-c * x ^ 2) * Real.cosh x ^ 2 ≤ Real.exp c⁻¹ := by
  have hcosh : Real.cosh x ≤ Real.exp |x| := by
    rw [Real.cosh_eq]
    have hx : x ≤ |x| := le_abs_self x
    have hnx : -x ≤ |x| := neg_le_abs x
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      (add_le_add (Real.exp_le_exp.mpr hx) (Real.exp_le_exp.mpr hnx) |>.trans_eq (mul_two _).symm)
  have harg : -c * x ^ 2 + 2 * |x| ≤ c⁻¹ := by
    rw [show c⁻¹ = 1 / c by ring, le_div_iff₀ hc]
    have hs := sq_nonneg (c * |x| - 1)
    ring_nf at hs ⊢
    nlinarith [sq_abs x]
  have hexpSq : Real.exp |x| ^ 2 = Real.exp (2 * |x|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-c * x ^ 2) * Real.cosh x ^ 2
        ≤ Real.exp (-c * x ^ 2) * (Real.exp |x|) ^ 2 := by gcongr
    _ = Real.exp (-c * x ^ 2) * Real.exp (2 * |x|) := by rw [hexpSq]
    _ = Real.exp (-c * x ^ 2 + 2 * |x|) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp c⁻¹ := Real.exp_le_exp.mpr harg

/-- The Jacobian denominator in the transformed density is exactly the square
of `cosh (artanh s)` on `(-1,1)`. -/
theorem inv_one_sub_sq_eq_cosh_artanh_sq {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - s ^ 2)⁻¹ = Real.cosh (Real.artanh s) ^ 2 := by
  rw [Real.cosh_artanh hs, div_pow, one_pow, Real.sq_sqrt]
  · simp
  · nlinarith [hs.1, hs.2]

/-- The one-coordinate transformed Gaussian density in the scalar form used by
the paper's compact-range argument. -/
theorem gaussianPDFReal_tanhScaleInv_eq_cosh {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2)
    {r v : ℝ} (hr : 0 < r) (hv : r * v ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - r ^ 2 * v ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r v) =
      gaussianPDFReal 0 σ2 0 *
        (Real.exp (-((2 * (σ2 : ℝ) * r ^ 2)⁻¹ * Real.artanh (r * v) ^ 2)) *
          Real.cosh (Real.artanh (r * v)) ^ 2) := by
  rw [show 1 - r ^ 2 * v ^ 2 = 1 - (r * v) ^ 2 by ring,
    inv_one_sub_sq_eq_cosh_artanh_sq hv]
  simp only [gaussianPDFReal_def, sub_zero, tanhScaleInv]
  have he : -(r⁻¹ * Real.artanh (r * v)) ^ 2 / (2 * (σ2 : ℝ)) =
      -((2 * (σ2 : ℝ) * r ^ 2)⁻¹ * Real.artanh (r * v) ^ 2) := by
    field_simp [ne_of_gt hr, ne_of_gt hσ0]
  rw [he]
  norm_num
  ring

/-- Uniform scalar transformed-density bound on a compact positive `r`-range.
This is the one-dimensional boundedness assertion used in tex L5071--5080. -/
theorem gaussianPDFReal_tanhScaleInv_le_of_le {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2)
    {r R v : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hv : r * v ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 - r ^ 2 * v ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r v) ≤
      gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * R ^ 2) := by
  rw [gaussianPDFReal_tanhScaleInv_eq_cosh hσ0 hr hv]
  have hc : 0 < (2 * (σ2 : ℝ) * r ^ 2)⁻¹ := by positivity
  calc
    gaussianPDFReal 0 σ2 0 *
        (Real.exp (-((2 * (σ2 : ℝ) * r ^ 2)⁻¹ * Real.artanh (r * v) ^ 2)) *
          Real.cosh (Real.artanh (r * v)) ^ 2)
      ≤ gaussianPDFReal 0 σ2 0 * Real.exp ((2 * (σ2 : ℝ) * r ^ 2)⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (by simpa only [neg_mul] using
            exp_neg_mul_sq_mul_cosh_sq_le (x := Real.artanh (r * v)) hc)
          (gaussianPDFReal_nonneg 0 σ2 0)
    _ = gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * r ^ 2) := by
      congr 2
      field_simp [ne_of_gt hr, ne_of_gt hσ0]
    _ ≤ gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * R ^ 2) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
        (gaussianPDFReal_nonneg 0 σ2 0)
      have hR0 : 0 ≤ R := hr.le.trans hrR
      have hsquares : r ^ 2 ≤ R ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hsquares (by positivity)

/-- Uniform pointwise bound for the full product density on a compact positive
`r`-range. -/
theorem polarDensityReal_le_of_le {N : ℕ} {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (v : Fin N → ℝ) :
    polarDensityReal N σ2 r v ≤
      (gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * R ^ 2)) ^ N := by
  rw [polarDensityReal]
  by_cases hv : v ∈ polarBox N r
  · rw [Set.indicator_of_mem hv]
    calc
      ∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
          ≤ ∏ _i : Fin N,
              (gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * R ^ 2)) := by
        refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
        · have hi := hv i
          have hri : r * v i ∈ Set.Ioo (-1 : ℝ) 1 := by
            have hlo := mul_lt_mul_of_pos_left hi.1 hr
            have hhi := mul_lt_mul_of_pos_left hi.2 hr
            have hcan : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
            constructor <;> nlinarith
          have hpos : 0 < 1 - r ^ 2 * (v i) ^ 2 := by
            nlinarith [hri.1, hri.2, sq_nonneg (r * v i)]
          exact mul_nonneg (inv_nonneg.mpr (le_of_lt hpos))
            (gaussianPDFReal_nonneg 0 σ2 (tanhScaleInv r (v i)))
        · exact gaussianPDFReal_tanhScaleInv_le_of_le hσ0 hr hrR (by
            have hi := hv i
            have hlo := mul_lt_mul_of_pos_left hi.1 hr
            have hhi := mul_lt_mul_of_pos_left hi.2 hr
            have hcan : r * r⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
            constructor <;> nlinarith)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [Set.indicator_of_notMem hv]
    exact pow_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 σ2 0) (Real.exp_nonneg _)) N

/-- The local-volume half of the compact-range argument: uniform boundedness
of both densities gives a `ρ ^ N` bound on a radius-`ρ` ball. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_pow_of_le {N : ℕ} {σ2 : ℝ≥0}
    (hσ0 : (0 : ℝ) < σ2) {r R ρ : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hρ0 : 0 ≤ ρ) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal
          ((gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * R ^ 2)) ^ N +
            gaussianPDFReal 0 σ2 0 ^ N) * ENNReal.ofReal ((2 * ρ) ^ N) := by
  set s : Set (Fin N → ℝ) := {v | ∑ i, v i ^ 2 < ρ ^ 2} with hs
  set C : ℝ :=
    (gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * R ^ 2)) ^ N +
      gaussianPDFReal 0 σ2 0 ^ N with hC
  have hpt : ∀ v : Fin N → ℝ,
      ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)| ≤
        ENNReal.ofReal C := by
    intro v
    have ha := polarDensityReal_nonneg (σ2 := σ2) hr v
    have hb : 0 ≤ ∏ i, gaussianPDFReal 0 σ2 (v i) :=
      Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
    apply ENNReal.ofReal_le_ofReal
    have habs : |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)| ≤
        polarDensityReal N σ2 r v + ∏ i, gaussianPDFReal 0 σ2 (v i) := by
      rw [abs_le]
      constructor <;> linarith
    refine habs.trans (add_le_add (polarDensityReal_le_of_le hσ0 hr hrR v) ?_)
    calc
      ∏ i, gaussianPDFReal 0 σ2 (v i) ≤ ∏ _i : Fin N, gaussianPDFReal 0 σ2 0 :=
        Finset.prod_le_prod (fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i))
          (fun i _ => gaussianPDFReal_le_of_abs_le hσ0 (by simp))
      _ = gaussianPDFReal 0 σ2 0 ^ N := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    ∫⁻ v in s,
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ∫⁻ _v in s, ENNReal.ofReal C := lintegral_mono hpt
    _ = ENNReal.ofReal C * volume s := by rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((2 * ρ) ^ N) := by
      gcongr
      exact volume_sum_sq_lt_le hρ0

/-- The product Gaussian density has total mass one. -/
theorem lintegral_gaussProd_eq_one {N : ℕ} {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) :
    ∫⁻ v : Fin N → ℝ, ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) = 1 := by
  haveI hprob : IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF 0 σ2)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hσ]
    infer_instance
  calc
    ∫⁻ v : Fin N → ℝ, ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)) =
        ∫⁻ v : Fin N → ℝ, ∏ i, gaussianPDF 0 σ2 (v i) := by
          refine lintegral_congr fun v => ?_
          rw [gaussianPDF_def]
          exact ENNReal.ofReal_prod_of_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
    _ = ((volume : Measure (Fin N → ℝ)).withDensity
          (fun v => ∏ i, gaussianPDF 0 σ2 (v i))) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = (Measure.pi fun _ : Fin N =>
          (volume : Measure ℝ).withDensity (gaussianPDF 0 σ2)) Set.univ := by
        rw [pi_withDensity_volume (measurable_gaussianPDF 0 σ2)]
    _ = 1 := measure_univ

set_option maxHeartbeats 800000 in
-- Elaborating the product/map normalization needs more than the project-wide heartbeat budget.
/-- The transformed product density `p_r` also has total mass one. -/
theorem lintegral_polarDensityReal_eq_one {N : ℕ} {σ2 : ℝ≥0} (hσ : σ2 ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ v : Fin N → ℝ, ENNReal.ofReal (polarDensityReal N σ2 r v) = 1 := by
  haveI hprob : IsProbabilityMeasure ((volume : Measure ℝ).withDensity (gaussianPDF 0 σ2)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hσ]
    infer_instance
  calc
    ∫⁻ v : Fin N → ℝ, ENNReal.ofReal (polarDensityReal N σ2 r v) =
        ∫⁻ v : Fin N → ℝ, ∏ i, tanhScaleDensity r (gaussianPDF 0 σ2) (v i) :=
          lintegral_congr fun v => ofReal_polarDensityReal hr v
    _ = ((volume : Measure (Fin N → ℝ)).withDensity
          (fun v => ∏ i, tanhScaleDensity r (gaussianPDF 0 σ2) (v i))) Set.univ := by
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = (Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i))
          (Measure.pi fun _ : Fin N =>
            (volume : Measure ℝ).withDensity (gaussianPDF 0 σ2))) Set.univ := by
        rw [map_tanhScaleVec_withDensity hr (measurable_gaussianPDF 0 σ2)]
    _ = 1 := by
      have hm : Measurable fun v : Fin N → ℝ => fun i => tanhScale r (v i) :=
        measurable_pi_lambda _ fun i => (measurable_tanhScale r).comp (measurable_pi_apply i)
      rw [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- The `L¹` distance of two nonnegative densities on a set is at most the sum
of their full-space masses. -/
theorem setLIntegral_ofReal_abs_sub_le_add_lintegral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (p q : E → ℝ) (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hq0 : ∀ x, 0 ≤ q x) (s : Set E) :
    ∫⁻ x in s, ENNReal.ofReal |p x - q x| ∂μ ≤
      (∫⁻ x, ENNReal.ofReal (p x) ∂μ) + ∫⁻ x, ENNReal.ofReal (q x) ∂μ := by
  have hpt : ∀ x, ENNReal.ofReal |p x - q x| ≤
      ENNReal.ofReal (p x) + ENNReal.ofReal (q x) := by
    intro x
    have habs : |p x - q x| ≤ p x + q x := by
      rw [abs_le]
      constructor <;> linarith [hp0 x, hq0 x]
    exact (ENNReal.ofReal_le_ofReal habs).trans
      (le_of_eq (ENNReal.ofReal_add (hp0 x) (hq0 x)))
  calc
    ∫⁻ x in s, ENNReal.ofReal |p x - q x| ∂μ
      ≤ ∫⁻ x in s, (ENNReal.ofReal (p x) + ENNReal.ofReal (q x)) ∂μ :=
        lintegral_mono hpt
    _ = (∫⁻ x in s, ENNReal.ofReal (p x) ∂μ) +
        ∫⁻ x in s, ENNReal.ofReal (q x) ∂μ :=
      lintegral_add_left (ENNReal.measurable_ofReal.comp hp) _
    _ ≤ (∫⁻ x, ENNReal.ofReal (p x) ∂μ) + ∫⁻ x, ENNReal.ofReal (q x) ∂μ :=
      add_le_add (setLIntegral_le_lintegral _ _) (setLIntegral_le_lintegral _ _)

/-- The trivial total-mass bound for the density error, valid on every ball. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_two {N : ℕ} {σ2 : ℝ≥0}
    (hσ : σ2 ≠ 0) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)| ≤ 2 := by
  refine (setLIntegral_ofReal_abs_sub_le_add_lintegral volume
    (polarDensityReal N σ2 r) (fun v => ∏ i, gaussianPDFReal 0 σ2 (v i))
    measurable_polarDensityReal (polarDensityReal_nonneg hr)
    (fun v => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)) _).trans_eq ?_
  rw [lintegral_polarDensityReal_eq_one hσ hr, lintegral_gaussProd_eq_one hσ]
  norm_num

/-- On the moderate-`r` branch, the total-mass estimate has the required
`r ^ δ` factor because `r` is bounded below by `1/4`. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_rpow_of_quarter_le {N : ℕ}
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) {r δ : ℝ} (hr : 0 < r) (hrq : 1 / 4 ≤ r)
    (hδ : 0 < δ) (ρ : ℝ) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (r ^ δ) * ENNReal.ofReal (2 * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
  refine (setLIntegral_abs_polarDensityReal_sub_le_two hσ hr ρ).trans ?_
  have hqpos : 0 < (1 / 4 : ℝ) ^ δ := Real.rpow_pos_of_pos (by norm_num) δ
  have hrpow : (1 / 4 : ℝ) ^ δ ≤ r ^ δ :=
    Real.rpow_le_rpow (by norm_num) hrq hδ.le
  have hreal : (2 : ℝ) ≤ r ^ δ * (2 * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
    calc
      (2 : ℝ) = (1 / 4 : ℝ) ^ δ * (2 * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
        field_simp [ne_of_gt hqpos]
      _ ≤ r ^ δ * (2 * ((1 / 4 : ℝ) ^ δ)⁻¹) := by gcongr
  calc
    (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
    _ ≤ ENNReal.ofReal (r ^ δ * (2 * ((1 / 4 : ℝ) ^ δ)⁻¹)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (r ^ δ) * ENNReal.ofReal (2 * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hr.le δ)]

/-- The local-volume estimate on the moderate-`r` branch, at the target
`r ^ δ * ρ ^ N` scale. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_rpow_mul_pow_of_quarter_le
    {N : ℕ} {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2) {r R δ ρ : ℝ} (hr : 0 < r)
    (hrq : 1 / 4 ≤ r) (hrR : r ≤ R) (hδ : 0 < δ) (hρ0 : 0 ≤ ρ) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (r ^ δ * ρ ^ N) *
          ENNReal.ofReal
            (((gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * R ^ 2)) ^ N +
                gaussianPDFReal 0 σ2 0 ^ N) * 2 ^ N * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
  refine (setLIntegral_abs_polarDensityReal_sub_le_pow_of_le hσ0 hr hrR hρ0).trans ?_
  set C : ℝ :=
    (gaussianPDFReal 0 σ2 0 * Real.exp (2 * (σ2 : ℝ) * R ^ 2)) ^ N +
      gaussianPDFReal 0 σ2 0 ^ N with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact add_nonneg
      (pow_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 σ2 0) (Real.exp_nonneg _)) N)
      (pow_nonneg (gaussianPDFReal_nonneg 0 σ2 0) N)
  have hqpos : 0 < (1 / 4 : ℝ) ^ δ := Real.rpow_pos_of_pos (by norm_num) δ
  have hrpow : (1 / 4 : ℝ) ^ δ ≤ r ^ δ :=
    Real.rpow_le_rpow (by norm_num) hrq hδ.le
  have hreal : C * (2 * ρ) ^ N ≤
      r ^ δ * ρ ^ N * (C * 2 ^ N * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
    calc
      C * (2 * ρ) ^ N =
          (1 / 4 : ℝ) ^ δ * ρ ^ N * (C * 2 ^ N * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
        rw [mul_pow]
        field_simp [ne_of_gt hqpos]
      _ ≤ r ^ δ * ρ ^ N * (C * 2 ^ N * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
        gcongr
  calc
    ENNReal.ofReal C * ENNReal.ofReal ((2 * ρ) ^ N) =
        ENNReal.ofReal (C * (2 * ρ) ^ N) := by rw [ENNReal.ofReal_mul hC0]
    _ ≤ ENNReal.ofReal
        (r ^ δ * ρ ^ N * (C * 2 ^ N * ((1 / 4 : ℝ) ^ δ)⁻¹)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (r ^ δ * ρ ^ N) *
        ENNReal.ofReal (C * 2 ^ N * ((1 / 4 : ℝ) ^ δ)⁻¹) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hr.le δ) (pow_nonneg hρ0 N))]

/-! ### Both `r` regimes assembled -/

/-- The unrestricted-radius density-error estimate on the full range
`0 < r ≤ √N`, combining the Taylor and compact-scale branches. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_rpow_of_le_sqrt {N : ℕ}
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (hσ0 : (0 : ℝ) < σ2) {r c δ : ℝ} (hr : 0 < r)
    (_hrN : r ≤ √N) (hc0 : 0 < c) (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) (ρ : ℝ) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (r ^ δ) *
          ((ENNReal.ofReal (polarConst N σ2) *
              (∫⁻ v : Fin N → ℝ,
                ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) *
                  ∏ i, gaussianPDFReal 0 σ2 (v i)))
            + 2 * (ENNReal.ofReal (4 / c) *
              (∫⁻ x : ℝ, ENNReal.ofReal
                (Real.exp (c * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N)) +
            ENNReal.ofReal (2 * ((1 / 4 : ℝ) ^ δ)⁻¹)) := by
  by_cases hr4 : r ≤ 1 / 4
  · refine (setLIntegral_abs_polarDensityReal_sub_le_rpow hσ hσ0 hr hr4 hc0 hδ2 ρ).trans ?_
    exact mul_le_mul_right (le_add_right le_rfl) _
  · have hrq : 1 / 4 ≤ r := le_of_lt (lt_of_not_ge hr4)
    refine (setLIntegral_abs_polarDensityReal_sub_le_rpow_of_quarter_le
      hσ hr hrq hδ0 ρ).trans ?_
    exact mul_le_mul_right (le_add_left le_rfl) _

/-- The `ρ ≤ 1` density-error estimate on the full range `0 < r ≤ √N`, with
the target `r ^ δ * ρ ^ N` factor. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_rpow_mul_pow_of_le_sqrt {N : ℕ}
    {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0) (hσ0 : (0 : ℝ) < σ2) {r δ ρ : ℝ}
    (hr : 0 < r) (hrN : r ≤ √N) (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (r ^ δ * ρ ^ N) *
          (ENNReal.ofReal (polarConst N σ2 *
              (2 * gaussianPDFReal 0 σ2 0 ^ N * 2 ^ N)) +
            ENNReal.ofReal
              (((gaussianPDFReal 0 σ2 0 *
                    Real.exp (2 * (σ2 : ℝ) * (√N) ^ 2)) ^ N +
                  gaussianPDFReal 0 σ2 0 ^ N) * 2 ^ N *
                ((1 / 4 : ℝ) ^ δ)⁻¹)) := by
  by_cases hr4 : r ≤ 1 / 4
  · refine (setLIntegral_abs_polarDensityReal_sub_le_rpow_mul_pow
      hσ hσ0 hr hr4 hδ2 hρ0 hρ1).trans ?_
    gcongr
    exact le_add_right le_rfl
  · have hrq : 1 / 4 ≤ r := le_of_lt (lt_of_not_ge hr4)
    refine (setLIntegral_abs_polarDensityReal_sub_le_rpow_mul_pow_of_quarter_le
      hσ0 hr hrq hrN hδ0 hρ0).trans ?_
    gcongr
    exact le_add_left le_rfl

/-! ### `eq:nd-density-error-reduction` -/

/-- Restricting two finite densities to a measurable set and then pushing them
through a measurable map bounds their TV distance by the `L¹` density error on
the restricting set.  This is the abstract data-processing step behind tex
L5060--5065; unlike `tvDist_map_le`, it applies to the resulting subprobability
measures. -/
theorem tvDist_map_restrict_withDensity_le_lintegral {E F : Type*}
    [MeasurableSpace E] [MeasurableSpace F] {μ : Measure E} {p q : E → ℝ}
    (hp : Measurable p) (hq : Measurable q) (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hpfin : ∫⁻ x, ENNReal.ofReal (p x) ∂μ ≠ ∞)
    (hqfin : ∫⁻ x, ENNReal.ofReal (q x) ∂μ ≠ ∞) {s : Set E} (hs : MeasurableSet s)
    (f : E → F) (hf : Measurable f) :
    tvDist (Measure.map f ((μ.withDensity fun x => ENNReal.ofReal (p x)).restrict s))
        (Measure.map f ((μ.withDensity fun x => ENNReal.ofReal (q x)).restrict s))
      ≤ (∫⁻ x in s, ENNReal.ofReal |p x - q x| ∂μ).toReal := by
  unfold tvDist
  refine ciSup_le fun B => ?_
  set A : Set E := s ∩ f ⁻¹' B.1 with hA
  have hAmeas : MeasurableSet A := hs.inter (hf B.2)
  rw [Measure.map_apply hf B.2, Measure.map_apply hf B.2,
    Measure.restrict_apply (hf B.2), Measure.restrict_apply (hf B.2),
    show f ⁻¹' B.1 ∩ s = A by rw [hA, Set.inter_comm],
    withDensity_apply _ hAmeas, withDensity_apply _ hAmeas]
  set a : ℝ≥0∞ := ∫⁻ x in A, ENNReal.ofReal (p x) ∂μ with ha
  set b : ℝ≥0∞ := ∫⁻ x in A, ENNReal.ofReal (q x) ∂μ with hb
  set d : ℝ≥0∞ := ∫⁻ x in s, ENNReal.ofReal |p x - q x| ∂μ with hd
  have ha_top : a ≠ ∞ := ne_top_of_le_ne_top hpfin (by
    rw [ha]
    exact setLIntegral_le_lintegral _ _)
  have hb_top : b ≠ ∞ := ne_top_of_le_ne_top hqfin (by
    rw [hb]
    exact setLIntegral_le_lintegral _ _)
  have hd_top : d ≠ ∞ := by
    refine ne_top_of_le_ne_top (show (∫⁻ x, ENNReal.ofReal (p x) ∂μ) +
      ∫⁻ x, ENNReal.ofReal (q x) ∂μ ≠ ∞ by exact ENNReal.add_ne_top.mpr ⟨hpfin, hqfin⟩) ?_
    rw [hd]
    have hdiff : ∀ x, |p x - q x| ≤ p x + q x := by
      intro x
      rw [abs_le]
      constructor <;> linarith [hp0 x, hq0 x]
    calc
      ∫⁻ x in s, ENNReal.ofReal |p x - q x| ∂μ
        ≤ ∫⁻ x in s, (ENNReal.ofReal (p x) + ENNReal.ofReal (q x)) ∂μ := by
          refine lintegral_mono fun x => ?_
          exact (ENNReal.ofReal_le_ofReal (hdiff x)).trans
              (le_of_eq (ENNReal.ofReal_add (hp0 x) (hq0 x)))
      _ = (∫⁻ x in s, ENNReal.ofReal (p x) ∂μ) +
          ∫⁻ x in s, ENNReal.ofReal (q x) ∂μ :=
        lintegral_add_left (ENNReal.measurable_ofReal.comp hp) _
      _ ≤ (∫⁻ x, ENNReal.ofReal (p x) ∂μ) + ∫⁻ x, ENNReal.ofReal (q x) ∂μ :=
        add_le_add (setLIntegral_le_lintegral _ _) (setLIntegral_le_lintegral _ _)
  have hA_sub : A ⊆ s := by intro x hx; exact hx.1
  have hab : a ≤ b + d := by
    rw [ha, hb]
    calc
      ∫⁻ x in A, ENNReal.ofReal (p x) ∂μ
        ≤ ∫⁻ x in A, (ENNReal.ofReal (q x) + ENNReal.ofReal |p x - q x|) ∂μ := by
          refine lintegral_mono fun x => ?_
          calc
            ENNReal.ofReal (p x) ≤ ENNReal.ofReal (q x + |p x - q x|) :=
              ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (p x - q x)])
            _ = ENNReal.ofReal (q x) + ENNReal.ofReal |p x - q x| := by
              rw [ENNReal.ofReal_add (hq0 x) (abs_nonneg _)]
      _ = (∫⁻ x in A, ENNReal.ofReal (q x) ∂μ) +
          ∫⁻ x in A, ENNReal.ofReal |p x - q x| ∂μ := by
        exact lintegral_add_left (μ := μ.restrict A) (ENNReal.measurable_ofReal.comp hq) _
      _ ≤ (∫⁻ x in A, ENNReal.ofReal (q x) ∂μ) + d := by
        gcongr
        rw [hd]
        exact lintegral_mono_set hA_sub
  have hba : b ≤ a + d := by
    rw [ha, hb]
    calc
      ∫⁻ x in A, ENNReal.ofReal (q x) ∂μ
        ≤ ∫⁻ x in A, (ENNReal.ofReal (p x) + ENNReal.ofReal |p x - q x|) ∂μ := by
          refine lintegral_mono fun x => ?_
          calc
            ENNReal.ofReal (q x) ≤ ENNReal.ofReal (p x + |p x - q x|) :=
              ENNReal.ofReal_le_ofReal (by linarith [neg_le_abs (p x - q x)])
            _ = ENNReal.ofReal (p x) + ENNReal.ofReal |p x - q x| := by
              rw [ENNReal.ofReal_add (hp0 x) (abs_nonneg _)]
      _ = (∫⁻ x in A, ENNReal.ofReal (p x) ∂μ) +
          ∫⁻ x in A, ENNReal.ofReal |p x - q x| ∂μ := by
        exact lintegral_add_left (μ := μ.restrict A) (ENNReal.measurable_ofReal.comp hp) _
      _ ≤ (∫⁻ x in A, ENNReal.ofReal (p x) ∂μ) + d := by
        gcongr
        rw [hd]
        exact lintegral_mono_set hA_sub
  apply (abs_le).2
  constructor
  · have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ha_top, hd_top⟩) hba
    rw [ENNReal.toReal_add ha_top hd_top] at this
    linarith
  · have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hb_top, hd_top⟩) hab
    rw [ENNReal.toReal_add hb_top hd_top] at this
    linarith

/-- **`eq:nd-density-error-reduction`**: after restricting the transformed and
linearized Gaussian laws to a Euclidean ball, angular projection cannot make
their discrepancy exceed the density `L¹` error on that ball. -/
theorem tvDist_map_angular_restrict_polar_le {N : ℕ} {σ2 : ℝ≥0} (hσ : σ2 ≠ 0)
    {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    tvDist
        (Measure.map (angular N)
          (((volume : Measure (Fin N → ℝ)).withDensity
            (fun v => ENNReal.ofReal (polarDensityReal N σ2 r v))).restrict
              {v | ∑ i, v i ^ 2 < ρ ^ 2}))
        (Measure.map (angular N)
          (((volume : Measure (Fin N → ℝ)).withDensity
            (fun v => ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)))).restrict
              {v | ∑ i, v i ^ 2 < ρ ^ 2}))
      ≤ (∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2},
          ENNReal.ofReal |polarDensityReal N σ2 r v -
            ∏ i, gaussianPDFReal 0 σ2 (v i)|).toReal := by
  apply tvDist_map_restrict_withDensity_le_lintegral
  · exact measurable_polarDensityReal
  · exact Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDFReal 0 σ2).comp (measurable_pi_apply i)
  · exact polarDensityReal_nonneg hr
  · exact fun v => Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
  · rw [lintegral_polarDensityReal_eq_one hσ hr]
    norm_num
  · rw [lintegral_gaussProd_eq_one hσ]
    norm_num
  · exact measurableSet_lt (by fun_prop) measurable_const
  · exact measurable_angular N

/-! ### The final envelope constant -/

/-- A fixed Gaussian tail rate strictly below the integrability threshold. -/
noncomputable def polarTailRate (σ2 : ℝ≥0) : ℝ := (4 * (σ2 : ℝ))⁻¹

lemma polarTailRate_pos {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2) : 0 < polarTailRate σ2 := by
  rw [polarTailRate]
  positivity

lemma polarTailRate_lt {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2) :
    polarTailRate σ2 < (2 * (σ2 : ℝ))⁻¹ := by
  rw [polarTailRate, inv_lt_inv₀ (by positivity) (by positivity)]
  linarith

/-- A common constant for the unrestricted and local-volume branches on
`0 < r ≤ √N`. -/
noncomputable def polarErrorConst (N : ℕ) (σ2 : ℝ≥0) (δ : ℝ) : ℝ≥0∞ :=
  ((ENNReal.ofReal (polarConst N σ2) *
        (∫⁻ v : Fin N → ℝ,
          ENNReal.ofReal ((1 + (∑ i, v i ^ 2) ^ 2) *
            ∏ i, gaussianPDFReal 0 σ2 (v i)))
      + 2 * (ENNReal.ofReal (4 / polarTailRate σ2) *
        (∫⁻ x : ℝ, ENNReal.ofReal
          (Real.exp (polarTailRate σ2 * x ^ 2) * gaussianPDFReal 0 σ2 x)) ^ N)) +
      ENNReal.ofReal (2 * ((1 / 4 : ℝ) ^ δ)⁻¹)) +
    (ENNReal.ofReal (polarConst N σ2 *
        (2 * gaussianPDFReal 0 σ2 0 ^ N * 2 ^ N)) +
      ENNReal.ofReal
        (((gaussianPDFReal 0 σ2 0 *
              Real.exp (2 * (σ2 : ℝ) * (√N) ^ 2)) ^ N +
            gaussianPDFReal 0 σ2 0 ^ N) * 2 ^ N *
          ((1 / 4 : ℝ) ^ δ)⁻¹))

theorem polarErrorConst_ne_top {N : ℕ} {σ2 : ℝ≥0} (hσ : σ2 ≠ 0)
    (hσ0 : (0 : ℝ) < σ2) (δ : ℝ) : polarErrorConst N σ2 δ ≠ ∞ := by
  have hpoly := lintegral_poly_gaussProd_ne_top (N := N) hσ
  have hexp := lintegral_exp_mul_sq_gaussianPDFReal_ne_top hσ0 (polarTailRate_lt hσ0)
  rw [polarErrorConst]
  finiteness

lemma polarEnvelope_of_nonneg {N : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    polarEnvelope N t = Real.exp (-t) ^ N := by
  rw [polarEnvelope, min_eq_right]
  · rw [← Real.exp_nat_mul]
    congr 1
    ring
  · rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg N) ht)

lemma polarEnvelope_of_nonpos {N : ℕ} {t : ℝ} (ht : t ≤ 0) :
    polarEnvelope N t = 1 := by
  rw [polarEnvelope, min_eq_left]
  rw [Real.one_le_exp_iff]
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) ht)

/-- The full density-error estimate with the paper's envelope
`h(t)=min{1,e^{-Nt}}`. -/
theorem setLIntegral_abs_polarDensityReal_sub_le_polarEnvelope {N : ℕ}
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (hσ0 : (0 : ℝ) < σ2) {r δ : ℝ} (hr : 0 < r)
    (hrN : r ≤ √N) (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) (t : ℝ) :
    ∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < Real.exp (-t) ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ ENNReal.ofReal (r ^ δ * polarEnvelope N t) * polarErrorConst N σ2 δ := by
  by_cases ht : 0 ≤ t
  · have hρ1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    have h := setLIntegral_abs_polarDensityReal_sub_le_rpow_mul_pow_of_le_sqrt
      (ne_of_gt hσ0) hσ0 hr hrN hδ0 hδ2 (Real.exp_nonneg _) hρ1
    rw [polarEnvelope_of_nonneg ht, polarErrorConst]
    refine h.trans ?_
    exact mul_le_mul_right (le_add_left le_rfl) _
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    have h := setLIntegral_abs_polarDensityReal_sub_le_rpow_of_le_sqrt
      hσ hσ0 hr hrN (polarTailRate_pos hσ0) hδ0 hδ2 (Real.exp (-t))
    rw [polarEnvelope_of_nonpos ht', mul_one, polarErrorConst]
    refine h.trans ?_
    exact mul_le_mul_right (le_add_right le_rfl) _

/-- **`eq:nd-polar-kernel-error`**, in the density-law formulation: the angular
parts of the nonlinear and linearized Gaussian laws, restricted at log-radius
`t`, differ by at most `C r^δ h(t)`. -/
theorem tvDist_map_angular_restrict_polar_le_polarEnvelope {N : ℕ}
    {σ2 : ℝ≥0} (hσ : σ2 ≠ 0) (hσ0 : (0 : ℝ) < σ2) {r δ : ℝ} (hr : 0 < r)
    (hrN : r ≤ √N) (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) (t : ℝ) :
    tvDist
        (Measure.map (angular N)
          (((volume : Measure (Fin N → ℝ)).withDensity
            (fun v => ENNReal.ofReal (polarDensityReal N σ2 r v))).restrict
              {v | ∑ i, v i ^ 2 < Real.exp (-t) ^ 2}))
        (Measure.map (angular N)
          (((volume : Measure (Fin N → ℝ)).withDensity
            (fun v => ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)))).restrict
              {v | ∑ i, v i ^ 2 < Real.exp (-t) ^ 2}))
      ≤ (polarErrorConst N σ2 δ).toReal * r ^ δ * polarEnvelope N t := by
  refine (tvDist_map_angular_restrict_polar_le hσ hr (Real.exp (-t))).trans ?_
  have hden := setLIntegral_abs_polarDensityReal_sub_le_polarEnvelope
    hσ hσ0 hr hrN hδ0 hδ2 t
  have hright_top : ENNReal.ofReal (r ^ δ * polarEnvelope N t) *
      polarErrorConst N σ2 δ ≠ ∞ := ENNReal.mul_ne_top
        (ENNReal.ofReal_ne_top) (polarErrorConst_ne_top hσ hσ0 δ)
  have hreal := ENNReal.toReal_mono hright_top hden
  calc
    (∫⁻ v in {v : Fin N → ℝ | ∑ i, v i ^ 2 < Real.exp (-t) ^ 2},
        ENNReal.ofReal |polarDensityReal N σ2 r v -
          ∏ i, gaussianPDFReal 0 σ2 (v i)|).toReal
      ≤ (ENNReal.ofReal (r ^ δ * polarEnvelope N t) *
          polarErrorConst N σ2 δ).toReal := hreal
    _ = (polarErrorConst N σ2 δ).toReal * r ^ δ * polarEnvelope N t := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (mul_nonneg (Real.rpow_nonneg hr.le δ) (polarEnvelope_nonneg N t))]
      ring

/-- **`lem:nd-gaussian-polar-perturbation`**, assembled: the explicit envelope
`polarEnvelope N` has finite exponentially weighted d.R.i. norm, and one finite
constant controls the nonlinear angular perturbation for every
`0 < r ≤ √N` and `t ∈ ℝ`. -/
theorem exists_gaussianPolarPerturbation_bound {N : ℕ} {σ2 : ℝ≥0}
    (hσ : σ2 ≠ 0) (hσ0 : (0 : ℝ) < σ2) {β δ : ℝ} (hβ : 0 < β)
    (hβN : β < (N : ℝ)) (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      Renewal.driNorm
          (fun t : ℝ => ENNReal.ofReal (Real.exp (β * t) * polarEnvelope N t)) ≠ ∞ ∧
      ∀ {r : ℝ}, 0 < r → r ≤ √N → ∀ t : ℝ,
        tvDist
            (Measure.map (angular N)
              (((volume : Measure (Fin N → ℝ)).withDensity
                (fun v => ENNReal.ofReal (polarDensityReal N σ2 r v))).restrict
                  {v | ∑ i, v i ^ 2 < Real.exp (-t) ^ 2}))
            (Measure.map (angular N)
              (((volume : Measure (Fin N → ℝ)).withDensity
                (fun v => ENNReal.ofReal (∏ i, gaussianPDFReal 0 σ2 (v i)))).restrict
                  {v | ∑ i, v i ^ 2 < Real.exp (-t) ^ 2}))
          ≤ C * r ^ δ * polarEnvelope N t := by
  refine ⟨(polarErrorConst N σ2 δ).toReal, ENNReal.toReal_nonneg, ?_, ?_⟩
  · exact driNorm_exp_mul_polarEnvelope_ne_top hβ hβN
  · intro r hr hrN t
    exact tvDist_map_angular_restrict_polar_le_polarEnvelope
      hσ hσ0 hr hrN hδ0 hδ2 t

end AbsorptionCutoff
