/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.InvariantSelection
import AbsorptionCutoff.KernelIrreducible
import Mathlib.Analysis.LConvolution
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Kernel.Irreducible

/-!
# Transition positivity for the supercritical invariant law

This file begins the paper's proof of
`prop:gaussian-unique-nonzero-invariant`.  Its first input is that the
unrounded squared-radius chain has positive one-step mass on every nonempty
open subset of `(0,1)`, from every positive radius.

The paper derives this from the explicit density of
`tanh² (A √q G)` and positivity of its convolutions.  The result below proves
the same paper-faithful support leaf directly: `Fmap A N q` is continuous,
every `r ∈ (0,1)` has an explicit constant-vector preimage, and the product
Gaussian measure is positive on nonempty open sets.
-/

open MeasureTheory ProbabilityTheory BigOperators

namespace AbsorptionCutoff

/-! ## The one-coordinate transition density -/

/-- The analytic expression in paper
`eq:gaussian-one-coordinate-density`, before extension by zero:
for `A > 0`, `q > 0`, and `y ∈ (0,1)`, this is the density of
`tanh²(A √q G)` at `y`.

The two inverse branches of the square contribute the factor cancelling the
`2` in the derivative of `√y`; the remaining inverse Jacobian is
`1 / (A √(2πq) √y (1-y))`. -/
noncomputable def gaussianOneCoordinateDensityFormula (A q y : ℝ) : ℝ :=
  (A * Real.sqrt (2 * Real.pi * q))⁻¹ *
    (Real.sqrt y * (1 - y))⁻¹ *
      Real.exp (-(Real.artanh (Real.sqrt y)) ^ 2 / (2 * A ^ 2 * q))

/-- The paper's one-coordinate density `f_q`, extended by zero away from `(0,1)`.
This global version is the object to be convolved `N` times in the next density
unit, yielding positivity of the sum density on `(0,N)` and, after scaling,
the transition density of `Kchain` on `(0,1)`. -/
noncomputable def gaussianOneCoordinateDensity (A q y : ℝ) : ℝ :=
  if y ∈ Set.Ioo (0 : ℝ) 1 then gaussianOneCoordinateDensityFormula A q y else 0

/-- On `(0,1)`, the globally defined density is exactly the formula displayed
in `eq:gaussian-one-coordinate-density`. -/
lemma gaussianOneCoordinateDensity_eq_formula (A q : ℝ) {y : ℝ}
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    gaussianOneCoordinateDensity A q y = gaussianOneCoordinateDensityFormula A q y := by
  simp [gaussianOneCoordinateDensity, hy]

/-- The one-coordinate density, extended by zero, is Borel measurable. -/
lemma measurable_gaussianOneCoordinateDensity (A q : ℝ) :
    Measurable (gaussianOneCoordinateDensity A q) := by
  apply Measurable.ite measurableSet_Ioo
  · unfold gaussianOneCoordinateDensityFormula Real.artanh
    fun_prop
  · fun_prop

/-- The one-coordinate `q`-score from the paper's total-variation smoothing
argument. -/
noncomputable def gaussianOneCoordinateScore (A q y : ℝ) : ℝ :=
  -(1 / (2 * q)) +
    Real.artanh (Real.sqrt y) ^ 2 / (2 * A ^ 2 * q ^ 2)

/-- The one-coordinate score is Borel measurable in its observation. -/
lemma measurable_gaussianOneCoordinateScore (A q : ℝ) :
    Measurable (gaussianOneCoordinateScore A q) := by
  unfold gaussianOneCoordinateScore Real.artanh
  fun_prop

/-- The one-coordinate density is strictly positive at every interior point
of its support, as used in the paper's convolution-positivity argument. -/
lemma gaussianOneCoordinateDensity_pos {A q y : ℝ} (hA : 0 < A) (hq : 0 < q)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    0 < gaussianOneCoordinateDensity A q y := by
  rw [gaussianOneCoordinateDensity_eq_formula A q hy]
  unfold gaussianOneCoordinateDensityFormula
  have hnorm : 0 < A * Real.sqrt (2 * Real.pi * q) := by positivity
  have hsing : 0 < Real.sqrt y * (1 - y) :=
    mul_pos (Real.sqrt_pos.2 hy.1) (sub_pos.2 hy.2)
  exact mul_pos (mul_pos (inv_pos.mpr hnorm) (inv_pos.mpr hsing)) (Real.exp_pos _)

/-- The extended one-coordinate density is nonnegative everywhere. -/
lemma gaussianOneCoordinateDensity_nonneg {A q : ℝ} (hA : 0 < A) (hq : 0 < q)
    (y : ℝ) :
    0 ≤ gaussianOneCoordinateDensity A q y := by
  by_cases hy : y ∈ Set.Ioo (0 : ℝ) 1
  · exact (gaussianOneCoordinateDensity_pos hA hq hy).le
  · simp [gaussianOneCoordinateDensity, hy]

/-! ## Positive-branch change of variables -/

/-- The one-coordinate random map whose density is
`gaussianOneCoordinateDensity A q`. -/
noncomputable def gaussianOneCoordinateMap (A q x : ℝ) : ℝ :=
  Real.tanh (A * Real.sqrt q * x) ^ 2

/-- The positive inverse branch in the paper's change of variables:
`y ↦ artanh(√y) / (A√q)`. -/
noncomputable def gaussianOneCoordinateInverse (A q y : ℝ) : ℝ :=
  Real.artanh (Real.sqrt y) / (A * Real.sqrt q)

/-- Derivative of `artanh` on its natural open interval.  Mathlib's pinned
`Artanh` module provides the inverse identities but not this derivative lemma,
so we derive it locally from
`artanh x = (1/2) log ((1+x)/(1-x))`. -/
lemma hasDerivAt_artanh_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have heq : Real.artanh =ᶠ[nhds x]
      (fun y : ℝ => (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩
  have h1mx : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have h1px : (1 : ℝ) + x ≠ 0 := by linarith [hx.1]
  have hsquare : (1 : ℝ) - x ^ 2 ≠ 0 := by
    rw [show (1 : ℝ) - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero h1mx h1px
  have hratio : (1 + x) / (1 - x) ≠ 0 := div_ne_zero h1px h1mx
  have hdiv := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).div
    ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)) h1mx
  have hlog := hdiv.log hratio
  have hmul := (hasDerivAt_const x (1 / 2 : ℝ)).mul hlog
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert hmul using 1
  · rfl
  · ext y
    rfl
  · change 1 / (1 - x ^ 2) =
      0 * Real.log ((1 + x) / (1 - x)) +
        1 / 2 * (((0 + 1) * (1 - x) - (1 + x) * (0 - 1)) /
          (1 - x) ^ 2 / ((1 + x) / (1 - x)))
    norm_num
    field_simp [h1mx, h1px, hsquare]
    ring

/-- The positive inverse branch is a right inverse of the one-coordinate map
on `(0,1)`. -/
lemma gaussianOneCoordinateMap_inverse {A q y : ℝ} (hA : 0 < A) (hq : 0 < q)
    (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    gaussianOneCoordinateMap A q (gaussianOneCoordinateInverse A q y) = y := by
  have ha : A * Real.sqrt q ≠ 0 := by positivity
  have hsqrt_pos : 0 < Real.sqrt y := Real.sqrt_pos.2 hy.1
  have hsqrt_lt_one : Real.sqrt y < 1 := by
    simpa using Real.sqrt_lt_sqrt hy.1.le hy.2
  unfold gaussianOneCoordinateMap gaussianOneCoordinateInverse
  have harg :
      A * Real.sqrt q * (Real.artanh (Real.sqrt y) / (A * Real.sqrt q)) =
        Real.artanh (Real.sqrt y) := by field_simp
  rw [harg, Real.tanh_artanh ⟨by linarith, hsqrt_lt_one⟩, Real.sq_sqrt hy.1.le]

/-- The positive inverse branch is a left inverse on positive Gaussian
coordinates. -/
lemma gaussianOneCoordinateInverse_map {A q x : ℝ} (hA : 0 < A) (hq : 0 < q)
    (hx : 0 < x) :
    gaussianOneCoordinateInverse A q (gaussianOneCoordinateMap A q x) = x := by
  have ha : 0 < A * Real.sqrt q := mul_pos hA (Real.sqrt_pos.2 hq)
  have harg : 0 < A * Real.sqrt q * x := mul_pos ha hx
  have htanh : 0 < Real.tanh (A * Real.sqrt q * x) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 harg) (Real.cosh_pos _)
  unfold gaussianOneCoordinateInverse gaussianOneCoordinateMap
  rw [Real.sqrt_sq_eq_abs, abs_of_pos htanh, Real.artanh_tanh]
  field_simp

/-- Evaluating the score at the transformed Gaussian coordinate gives the
centered chi-square score `(x²-1)/(2q)`. -/
lemma gaussianOneCoordinateScore_map {A q x : ℝ}
    (hA : 0 < A) (hq : 0 < q) :
    gaussianOneCoordinateScore A q
        (gaussianOneCoordinateMap A q x) =
      (x ^ 2 - 1) / (2 * q) := by
  have hAq : A * Real.sqrt q ≠ 0 := by positivity
  have hscore_pos :
      ∀ z : ℝ, 0 < z →
        gaussianOneCoordinateScore A q
            (gaussianOneCoordinateMap A q z) =
          (z ^ 2 - 1) / (2 * q) := by
    intro z hz
    have hinv :=
      gaussianOneCoordinateInverse_map hA hq hz
    have hartanh :
        Real.artanh
            (Real.sqrt (gaussianOneCoordinateMap A q z)) =
          A * Real.sqrt q * z := by
      unfold gaussianOneCoordinateInverse at hinv
      simpa only [mul_comm] using (div_eq_iff hAq).mp hinv
    unfold gaussianOneCoordinateScore
    rw [hartanh, mul_pow, mul_pow, Real.sq_sqrt hq.le]
    field_simp [hA.ne', hq.ne']
    ring
  by_cases hx : 0 < x
  · exact hscore_pos x hx
  by_cases hx0 : x = 0
  · subst x
    simp [gaussianOneCoordinateScore, gaussianOneCoordinateMap]
    field_simp [hq.ne']
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
  have hmap :
      gaussianOneCoordinateMap A q x =
        gaussianOneCoordinateMap A q (-x) := by
    unfold gaussianOneCoordinateMap
    rw [show A * Real.sqrt q * -x =
        -(A * Real.sqrt q * x) by ring, Real.tanh_neg]
    ring
  rw [hmap]
  simpa only [neg_sq] using hscore_pos (-x) (neg_pos.mpr hxneg)

/-- Derivative of the positive inverse branch on `(0,1)`. -/
lemma hasDerivAt_gaussianOneCoordinateInverse {A q y : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (gaussianOneCoordinateInverse A q)
      (1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y))) y := by
  have hsqrt_pos : 0 < Real.sqrt y := Real.sqrt_pos.2 hy.1
  have hsqrt_lt_one : Real.sqrt y < 1 := by
    simpa using Real.sqrt_lt_sqrt hy.1.le hy.2
  have hart := hasDerivAt_artanh_of_mem_Ioo
    (x := Real.sqrt y) ⟨by linarith, hsqrt_lt_one⟩
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt hy.1)
  have hcomp := hart.comp y hsqrt
  have hdiv := hcomp.div_const (A * Real.sqrt q)
  have ha : A * Real.sqrt q ≠ 0 := by positivity
  have hsy : Real.sqrt y ≠ 0 := ne_of_gt hsqrt_pos
  have h1y : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
  have hsquare : (1 : ℝ) - (Real.sqrt y) ^ 2 = 1 - y := by
    rw [Real.sq_sqrt hy.1.le]
  have hcoef :
      1 / (1 - (Real.sqrt y) ^ 2) * (1 / (2 * Real.sqrt y)) /
          (A * Real.sqrt q) =
        1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y)) := by
    rw [hsquare]
    field_simp [ha, hsy, h1y]
  rw [hcoef] at hdiv
  change HasDerivAt
    (fun x : ℝ => Real.artanh (Real.sqrt x) / (A * Real.sqrt q))
    (1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y))) y
  exact hdiv

/-- The positive inverse branch maps `(0,1)` exactly onto `(0,∞)`. -/
lemma gaussianOneCoordinateInverse_image {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    gaussianOneCoordinateInverse A q '' Set.Ioo (0 : ℝ) 1 = Set.Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact div_pos (Real.artanh_pos ⟨Real.sqrt_pos.2 hy.1,
      by simpa using Real.sqrt_lt_sqrt hy.1.le hy.2⟩)
      (mul_pos hA (Real.sqrt_pos.2 hq))
  · intro hx
    refine ⟨gaussianOneCoordinateMap A q x, ?_,
      gaussianOneCoordinateInverse_map hA hq hx⟩
    unfold gaussianOneCoordinateMap
    exact ⟨sq_pos_of_pos (by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.2
        (mul_pos (mul_pos hA (Real.sqrt_pos.2 hq)) hx)) (Real.cosh_pos _)),
      Real.tanh_sq_lt_one _⟩

/-- The positive inverse branch is injective on `(0,1)`. -/
lemma gaussianOneCoordinateInverse_injOn {A q : ℝ} (hA : 0 < A) (hq : 0 < q) :
    Set.InjOn (gaussianOneCoordinateInverse A q) (Set.Ioo (0 : ℝ) 1) := by
  intro y hy z hz h
  rw [← gaussianOneCoordinateMap_inverse hA hq hy,
    ← gaussianOneCoordinateMap_inverse hA hq hz, h]

/-- **Positive-branch Jacobian identity.** Pushing the inverse-Jacobian
weighted Lebesgue measure on `(0,1)` through the positive inverse branch gives
Lebesgue measure on `(0,∞)`.  This is the branchwise change-of-variables core
needed to prove that `gaussianOneCoordinateDensity` is the pushforward density
of `tanh²(A√q G)`. -/
theorem map_gaussianOneCoordinateInverse_jacobian {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) :
    Measure.map (gaussianOneCoordinateInverse A q)
        ((volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity
          (fun y => ENNReal.ofReal
            |1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y))|))
      = volume.restrict (Set.Ioi 0) := by
  have hbase := MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
    (μ := (volume : Measure ℝ)) (s := Set.Ioo (0 : ℝ) 1)
    (f := gaussianOneCoordinateInverse A q)
    (f' := fun y =>
      ContinuousLinearMap.toSpanSingleton ℝ
        (1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y))))
    measurableSet_Ioo.nullMeasurableSet
    (fun y hy =>
      (hasDerivAt_gaussianOneCoordinateInverse hA hq hy).hasDerivWithinAt.hasFDerivWithinAt)
    (gaussianOneCoordinateInverse_injOn hA hq)
  rw [gaussianOneCoordinateInverse_image hA hq] at hbase
  simpa only [ContinuousLinearMap.det_toSpanSingleton] using hbase

private lemma map_withDensity_comp_of_map_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → β} (hf : Measurable f) (hmap : Measure.map f μ = ν)
    {g : β → ENNReal} (hg : Measurable g) :
    Measure.map f (μ.withDensity (g ∘ f)) = ν.withDensity g := by
  rw [← hmap]
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, Measure.restrict_map hf hs, lintegral_map hg hf]
  rfl

/-- Adding the standard Gaussian weight to the positive-branch Jacobian
identity gives the standard Gaussian law restricted to positive coordinates. -/
lemma map_gaussianOneCoordinateInverse_gaussianWeight {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) :
    Measure.map (gaussianOneCoordinateInverse A q)
        (((volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity
          (fun y => ENNReal.ofReal
            |1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y))|)).withDensity
              (gaussianPDF 0 1 ∘ gaussianOneCoordinateInverse A q))
      = (gaussianReal 0 1).restrict (Set.Ioi 0) := by
  have hinv : Measurable (gaussianOneCoordinateInverse A q) := by
    unfold gaussianOneCoordinateInverse Real.artanh
    fun_prop
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, restrict_withDensity measurableSet_Ioi]
  apply map_withDensity_comp_of_map_eq
  · exact hinv
  · exact map_gaussianOneCoordinateInverse_jacobian hA hq
  · exact measurable_gaussianPDF 0 1

/-- On the positive branch, the Gaussian weight times the inverse Jacobian
is one half of the paper's density formula. -/
lemma gaussianOneCoordinate_positiveBranch_weight {A q y : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    ENNReal.ofReal
          |1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y))| *
        gaussianPDF 0 1 (gaussianOneCoordinateInverse A q y)
      = ENNReal.ofReal (gaussianOneCoordinateDensityFormula A q y / 2) := by
  rw [gaussianPDF, ← ENNReal.ofReal_mul (by positivity : 0 ≤
    |1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y))|)]
  congr 1
  have hden : 0 < 2 * A * Real.sqrt q * Real.sqrt y * (1 - y) := by
    have h2A : 0 < 2 * A := mul_pos (by norm_num) hA
    have h2Asqrtq : 0 < 2 * A * Real.sqrt q :=
      mul_pos h2A (Real.sqrt_pos.2 hq)
    have h2Asqrtqy : 0 < 2 * A * Real.sqrt q * Real.sqrt y :=
      mul_pos h2Asqrtq (Real.sqrt_pos.2 hy.1)
    exact mul_pos h2Asqrtqy (sub_pos.2 hy.2)
  rw [abs_of_pos (one_div_pos.mpr hden)]
  unfold gaussianPDFReal
  norm_num
  unfold gaussianOneCoordinateInverse gaussianOneCoordinateDensityFormula
  have hq0 : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  have hsqrtq :
      Real.sqrt (2 * Real.pi * q) = Real.sqrt (2 * Real.pi) * Real.sqrt q := by
    rw [show 2 * Real.pi * q = (2 * Real.pi) * q by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  rw [hsqrtq]
  field_simp [ne_of_gt hA, hq0]
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)), Real.sq_sqrt hq.le]
  ring_nf

/-- The positive Gaussian half-line contributes exactly one half of the
one-coordinate density. -/
theorem map_gaussianOneCoordinateMap_restrict_Ioi {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) :
    Measure.map (gaussianOneCoordinateMap A q)
        ((gaussianReal 0 1).restrict (Set.Ioi 0))
      = volume.withDensity
          (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y / 2)) := by
  let J : ℝ → ENNReal := fun y => ENNReal.ofReal
    |1 / (2 * A * Real.sqrt q * Real.sqrt y * (1 - y))|
  let G : ℝ → ENNReal :=
    gaussianPDF 0 1 ∘ gaussianOneCoordinateInverse A q
  let H : ℝ → ENNReal := fun y =>
    ENNReal.ofReal (gaussianOneCoordinateDensityFormula A q y / 2)
  have hinv : Measurable (gaussianOneCoordinateInverse A q) := by
    unfold gaussianOneCoordinateInverse Real.artanh
    fun_prop
  have hmap : Measurable (gaussianOneCoordinateMap A q) := by
    unfold gaussianOneCoordinateMap
    simp_rw [Real.tanh_eq]
    fun_prop
  have hJ : Measurable J := by
    dsimp [J]
    fun_prop
  have hG : Measurable G :=
    (measurable_gaussianPDF 0 1).comp hinv
  have hsource :
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity J).withDensity G
        = (volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity H := by
    rw [← withDensity_mul _ hJ hG]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact gaussianOneCoordinate_positiveBranch_weight hA hq hy
  have hpositive :
      Measure.map (gaussianOneCoordinateMap A q)
          ((gaussianReal 0 1).restrict (Set.Ioi 0))
        = (volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity H := by
    rw [← map_gaussianOneCoordinateInverse_gaussianWeight hA hq, hsource,
      Measure.map_map hmap hinv]
    have hsupp : ∀ᵐ y
        ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity H,
        y ∈ Set.Ioo (0 : ℝ) 1 :=
      (withDensity_absolutelyContinuous _ _) (ae_restrict_mem measurableSet_Ioo)
    calc
      Measure.map
          (gaussianOneCoordinateMap A q ∘ gaussianOneCoordinateInverse A q)
          ((volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity H)
          = Measure.map id
              ((volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity H) := by
                apply Measure.map_congr
                filter_upwards [hsupp] with y hy
                exact gaussianOneCoordinateMap_inverse hA hq hy
      _ = (volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity H :=
        Measure.map_id
  rw [hpositive]
  calc
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity H
        = volume.withDensity
            ((Set.Ioo (0 : ℝ) 1).indicator H) := by
              rw [withDensity_indicator measurableSet_Ioo]
    _ = volume.withDensity
          (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y / 2)) := by
            apply withDensity_congr_ae
            filter_upwards with y
            by_cases hy : y ∈ Set.Ioo (0 : ℝ) 1
            · simp [H, hy, gaussianOneCoordinateDensity_eq_formula A q hy]
            · simp [H, hy, gaussianOneCoordinateDensity]

/-- The negative and positive Gaussian half-lines have the same image under
the even one-coordinate map. -/
lemma map_gaussianOneCoordinateMap_restrict_Iio_eq_Ioi {A q : ℝ} :
    Measure.map (gaussianOneCoordinateMap A q)
        ((gaussianReal 0 1).restrict (Set.Iio 0))
      = Measure.map (gaussianOneCoordinateMap A q)
          ((gaussianReal 0 1).restrict (Set.Ioi 0)) := by
  have hneg : Measure.map (fun x : ℝ => -x)
      ((gaussianReal 0 1).restrict (Set.Iio 0))
      = (gaussianReal 0 1).restrict (Set.Ioi 0) := by
    have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioi 0 = Set.Iio 0 := by
      ext x
      simp
    rw [← hpre, ← Measure.restrict_map measurable_neg measurableSet_Ioi,
      gaussianReal_map_neg]
    norm_num
  rw [← hneg]
  have hmap : Measurable (gaussianOneCoordinateMap A q) := by
    unfold gaussianOneCoordinateMap
    simp_rw [Real.tanh_eq]
    fun_prop
  rw [Measure.map_map hmap measurable_neg]
  · apply Measure.map_congr
    filter_upwards with x
    simp [gaussianOneCoordinateMap]

/-- **One-coordinate pushforward density.**  The law of
`tanh²(A √q G)` for a standard Gaussian `G` is the paper's explicit density
`gaussianOneCoordinateDensity A q` with respect to Lebesgue measure. -/
theorem map_gaussianOneCoordinateMap_eq_withDensity {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) :
    Measure.map (gaussianOneCoordinateMap A q) (gaussianReal 0 1)
      = volume.withDensity
          (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y)) := by
  have hmap : Measurable (gaussianOneCoordinateMap A q) := by
    unfold gaussianOneCoordinateMap
    simp_rw [Real.tanh_eq]
    fun_prop
  haveI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  have hdisj : Disjoint (Set.Iio (0 : ℝ)) (Set.Ioi 0) := by
    rw [Set.disjoint_left]
    intro x hx h'x
    change x < 0 at hx
    change 0 < x at h'x
    linarith
  have hsplit :
      gaussianReal 0 1 =
        (gaussianReal 0 1).restrict (Set.Iio 0) +
          (gaussianReal 0 1).restrict (Set.Ioi 0) := by
    rw [← Measure.restrict_union hdisj measurableSet_Ioi]
    symm
    apply Measure.restrict_eq_self_of_ae_mem
    have hne : ∀ᵐ x ∂gaussianReal 0 1, x ≠ 0 := by
      rw [ae_iff]
      have hset : {x : ℝ | ¬x ≠ 0} = {(0 : ℝ)} := by
        ext x
        simp
      rw [hset]
      exact measure_singleton 0
    filter_upwards [hne] with x hx
    rcases lt_or_gt_of_ne hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  rw [hsplit, Measure.map_add _ _ hmap,
    map_gaussianOneCoordinateMap_restrict_Iio_eq_Ioi,
    map_gaussianOneCoordinateMap_restrict_Ioi hA hq]
  let H : ℝ → ENNReal := fun y =>
    ENNReal.ofReal (gaussianOneCoordinateDensity A q y / 2)
  have hH : Measurable H := by
    dsimp [H]
    exact ((measurable_gaussianOneCoordinateDensity A q).div
      measurable_const).ennreal_ofReal
  rw [← withDensity_add_left hH]
  apply withDensity_congr_ae
  filter_upwards with y
  have hd : 0 ≤ gaussianOneCoordinateDensity A q y :=
    gaussianOneCoordinateDensity_nonneg hA hq y
  change ENNReal.ofReal (gaussianOneCoordinateDensity A q y / 2) +
      ENNReal.ofReal (gaussianOneCoordinateDensity A q y / 2) =
    ENNReal.ofReal (gaussianOneCoordinateDensity A q y)
  rw [← ENNReal.ofReal_add (div_nonneg hd (by norm_num))
    (div_nonneg hd (by norm_num))]
  congr 1
  ring

/-! ## The two-coordinate convolution density -/

/-- The density of the sum of two independent one-coordinate variables,
written as the Lebesgue convolution used in the paper.  The `ENNReal`-valued
form is the one naturally consumed by `Measure.withDensity`. -/
noncomputable def gaussianTwoCoordinateDensity (A q : ℝ) : ℝ → ENNReal :=
  MeasureTheory.lconvolution
    (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y))
    (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y))
    volume

/-- The two-coordinate convolution density is Borel measurable. -/
lemma measurable_gaussianTwoCoordinateDensity (A q : ℝ) :
    Measurable (gaussianTwoCoordinateDensity A q) := by
  unfold gaussianTwoCoordinateDensity
  apply MeasureTheory.measurable_lconvolution volume
  · exact (measurable_gaussianOneCoordinateDensity A q).ennreal_ofReal
  · exact (measurable_gaussianOneCoordinateDensity A q).ennreal_ofReal

/-- Convolving the two one-coordinate laws gives the measure whose Lebesgue
density is `gaussianTwoCoordinateDensity`.  This is the two-summand instance
of the paper's convolution-density argument. -/
theorem conv_gaussianOneCoordinateMeasure_eq_withDensity (A q : ℝ) :
    Measure.conv
        (volume.withDensity
          (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y)))
        (volume.withDensity
          (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y)))
      = volume.withDensity (gaussianTwoCoordinateDensity A q) := by
  have hf : Measurable
      (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y)) :=
    (measurable_gaussianOneCoordinateDensity A q).ennreal_ofReal
  simpa only [gaussianTwoCoordinateDensity] using
    (MeasureTheory.conv_withDensity_eq_lconvolution (μ := volume) hf hf)

/-- The two-coordinate convolution density is nonnegative everywhere. -/
lemma gaussianTwoCoordinateDensity_nonneg (A q z : ℝ) :
    0 ≤ gaussianTwoCoordinateDensity A q z :=
  bot_le

/-- The convolution of two copies of the one-coordinate density is strictly
positive throughout the interior `(0,2)` of its support. -/
lemma gaussianTwoCoordinateDensity_pos {A q z : ℝ}
    (hA : 0 < A) (hq : 0 < q) (hz : z ∈ Set.Ioo (0 : ℝ) 2) :
    0 < gaussianTwoCoordinateDensity A q z := by
  rw [gaussianTwoCoordinateDensity, MeasureTheory.lconvolution_def]
  let f : ℝ → ENNReal :=
    fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y)
  have hf : Measurable f :=
    (measurable_gaussianOneCoordinateDensity A q).ennreal_ofReal
  have hshift : Measurable (fun y : ℝ => -y + z) := by fun_prop
  have hint :
      max 0 (z - 1) < min 1 z := by
    refine (max_lt_iff).2 ⟨?_, ?_⟩
    · exact (lt_min_iff).2 ⟨by norm_num, hz.1⟩
    · exact (lt_min_iff).2 ⟨by linarith [hz.2], by linarith⟩
  have hsub :
      Set.Ioo (max 0 (z - 1)) (min 1 z) ⊆
        Function.support (fun y => f y * f (-y + z)) := by
    intro y hy
    have hy_pos : 0 < y :=
      (le_max_left 0 (z - 1)).trans_lt hy.1
    have hy_lt_one : y < 1 :=
      hy.2.trans_le (min_le_left 1 z)
    have hy_lt_z : y < z :=
      hy.2.trans_le (min_le_right 1 z)
    have hz_sub_y_lt_one : -y + z < 1 := by
      have hz_sub_one_lt_y : z - 1 < y :=
        (le_max_right 0 (z - 1)).trans_lt hy.1
      linarith
    have hyI : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy_pos, hy_lt_one⟩
    have hzyI : -y + z ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨by linarith, hz_sub_y_lt_one⟩
    exact (ENNReal.mul_pos
      (ENNReal.ofReal_pos.2
        (gaussianOneCoordinateDensity_pos hA hq hyI)).ne'
      (ENNReal.ofReal_pos.2
        (gaussianOneCoordinateDensity_pos hA hq hzyI)).ne').ne'
  refine (lintegral_pos_iff_support (hf.mul (hf.comp hshift))).2 ?_
  exact ((Measure.measure_Ioo_pos volume).2 hint).trans_le (measure_mono hsub)

/-! ## Recursive coordinate-sum densities -/

/-- The density of the sum of `n + 1` independent one-coordinate variables.
Indexing by the number of *additional* coordinates avoids assigning a
Lebesgue density to the zero-coordinate Dirac mass. -/
noncomputable def gaussianCoordinateSumDensity (A q : ℝ) : ℕ → ℝ → ENNReal
  | 0 => fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y)
  | n + 1 => MeasureTheory.lconvolution
      (gaussianCoordinateSumDensity A q n)
      (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y))
      volume

/-- The recursive sum density starts with the one-coordinate density. -/
@[simp]
lemma gaussianCoordinateSumDensity_zero (A q : ℝ) :
    gaussianCoordinateSumDensity A q 0 =
      fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y) :=
  rfl

/-- Adding one coordinate convolves the preceding sum density with the
one-coordinate density. -/
lemma gaussianCoordinateSumDensity_succ (A q : ℝ) (n : ℕ) :
    gaussianCoordinateSumDensity A q (n + 1) =
      MeasureTheory.lconvolution
        (gaussianCoordinateSumDensity A q n)
        (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y))
        volume :=
  rfl

/-- At index one, the recursive density agrees with the explicit
two-coordinate convolution density. -/
@[simp]
lemma gaussianCoordinateSumDensity_one (A q : ℝ) :
    gaussianCoordinateSumDensity A q 1 = gaussianTwoCoordinateDensity A q :=
  rfl

/-- Every recursive coordinate-sum density is Borel measurable. -/
lemma measurable_gaussianCoordinateSumDensity (A q : ℝ) (n : ℕ) :
    Measurable (gaussianCoordinateSumDensity A q n) := by
  induction n with
  | zero =>
      exact (measurable_gaussianOneCoordinateDensity A q).ennreal_ofReal
  | succ n ih =>
      rw [gaussianCoordinateSumDensity_succ]
      exact MeasureTheory.measurable_lconvolution volume ih
        (measurable_gaussianOneCoordinateDensity A q).ennreal_ofReal

/-- Convolving an `(n + 1)`-coordinate sum law with one more coordinate
produces the measure having the next recursive density. -/
theorem conv_gaussianCoordinateSumMeasure_succ_eq_withDensity
    (A q : ℝ) (n : ℕ) :
    Measure.conv
        (volume.withDensity (gaussianCoordinateSumDensity A q n))
        (volume.withDensity
          (fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y)))
      = volume.withDensity (gaussianCoordinateSumDensity A q (n + 1)) := by
  simpa only [gaussianCoordinateSumDensity_succ] using
    (MeasureTheory.conv_withDensity_eq_lconvolution (μ := volume)
      (measurable_gaussianCoordinateSumDensity A q n)
      (measurable_gaussianOneCoordinateDensity A q).ennreal_ofReal)

/-- The law of the sum of `n + 1` independent one-coordinate variables,
defined as the corresponding recursive convolution power. -/
noncomputable def gaussianCoordinateSumLaw (A q : ℝ) : ℕ → Measure ℝ
  | 0 => Measure.map (gaussianOneCoordinateMap A q) (gaussianReal 0 1)
  | n + 1 => Measure.conv
      (gaussianCoordinateSumLaw A q n)
      (Measure.map (gaussianOneCoordinateMap A q) (gaussianReal 0 1))

/-- The recursive sum law starts with one coordinate. -/
@[simp]
lemma gaussianCoordinateSumLaw_zero (A q : ℝ) :
    gaussianCoordinateSumLaw A q 0 =
      Measure.map (gaussianOneCoordinateMap A q) (gaussianReal 0 1) :=
  rfl

/-- Adding one independent coordinate convolves its law with the preceding
coordinate-sum law. -/
lemma gaussianCoordinateSumLaw_succ (A q : ℝ) (n : ℕ) :
    gaussianCoordinateSumLaw A q (n + 1) =
      Measure.conv
        (gaussianCoordinateSumLaw A q n)
        (Measure.map (gaussianOneCoordinateMap A q) (gaussianReal 0 1)) :=
  rfl

instance sFinite_gaussianCoordinateSumLaw (A q : ℝ) (n : ℕ) :
    SFinite (gaussianCoordinateSumLaw A q n) := by
  induction n with
  | zero =>
      rw [gaussianCoordinateSumLaw_zero]
      infer_instance
  | succ n _ =>
      rw [gaussianCoordinateSumLaw_succ]
      infer_instance

/-- **Recursive coordinate-sum law.**  The sum of `n + 1` independent
one-coordinate variables has density `gaussianCoordinateSumDensity A q n`. -/
theorem gaussianCoordinateSumLaw_eq_withDensity {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) (n : ℕ) :
    gaussianCoordinateSumLaw A q n =
      volume.withDensity (gaussianCoordinateSumDensity A q n) := by
  induction n with
  | zero =>
      rw [gaussianCoordinateSumLaw_zero, gaussianCoordinateSumDensity_zero,
        map_gaussianOneCoordinateMap_eq_withDensity hA hq]
  | succ n ih =>
      rw [gaussianCoordinateSumLaw_succ, ih,
        map_gaussianOneCoordinateMap_eq_withDensity hA hq,
        conv_gaussianCoordinateSumMeasure_succ_eq_withDensity]

/-- The unscaled sum of the transformed coordinates appearing in `Fmap`. -/
noncomputable def gaussianCoordinateSumMap (A q : ℝ) (N : ℕ)
    (g : Fin N → ℝ) : ℝ :=
  ∑ i, gaussianOneCoordinateMap A q (g i)

/-- The transformed-coordinate sum is Borel measurable. -/
lemma measurable_gaussianCoordinateSumMap (A q : ℝ) (N : ℕ) :
    Measurable (gaussianCoordinateSumMap A q N) := by
  have hcoord : Measurable (gaussianOneCoordinateMap A q) := by
    unfold gaussianOneCoordinateMap
    simp_rw [Real.tanh_eq]
    fun_prop
  unfold gaussianCoordinateSumMap
  exact Finset.measurable_sum _ fun i _ =>
    hcoord.comp (measurable_pi_apply i)

private lemma map_add_prod_eq_conv_map {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measure.map (fun p : α × β => f p.1 + g p.2) (μ.prod ν) =
      Measure.conv (Measure.map f μ) (Measure.map g ν) := by
  unfold Measure.conv
  rw [Measure.map_prod_map μ ν hf hg,
    Measure.map_map (by fun_prop) (hf.prodMap hg)]
  rfl

/-- **Finite-vector coordinate-sum law.**  The transformed-coordinate sum
under `gaussianVec (n + 1)` has the recursive convolution law of `n + 1`
independent one-coordinate variables. -/
theorem map_gaussianCoordinateSumMap_gaussianVec_succ (A q : ℝ) (n : ℕ) :
    Measure.map (gaussianCoordinateSumMap A q (n + 1)) (gaussianVec (n + 1)) =
      gaussianCoordinateSumLaw A q n := by
  induction n with
  | zero =>
      have hcoord : Measurable (gaussianOneCoordinateMap A q) := by
        unfold gaussianOneCoordinateMap
        simp_rw [Real.tanh_eq]
        fun_prop
      have hsum :
          gaussianCoordinateSumMap A q 1 =
            gaussianOneCoordinateMap A q ∘ Function.eval (0 : Fin 1) := by
        ext g
        simp [gaussianCoordinateSumMap]
      have heval :
          Measure.map (Function.eval (0 : Fin 1)) (gaussianVec 1) =
            gaussianReal 0 1 := by
        unfold gaussianVec
        rw [Measure.pi_map_eval]
        simp
      rw [hsum, ← Measure.map_map hcoord (measurable_pi_apply (0 : Fin 1)),
        heval, gaussianCoordinateSumLaw_zero]
  | succ n ih =>
      change
        Measure.map (gaussianCoordinateSumMap A q (n + 2)) (gaussianVec (n + 2)) =
          gaussianCoordinateSumLaw A q (n + 1)
      let e : (Fin (n + 2) → ℝ) ≃ᵐ ℝ × (Fin (n + 1) → ℝ) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0
      have he :
          Measure.map e (gaussianVec (n + 2)) =
            (gaussianReal 0 1).prod (gaussianVec (n + 1)) := by
        have h := (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 2) => gaussianReal 0 1) 0).map_eq
        simpa only [gaussianVec] using h
      have hsum :
          gaussianCoordinateSumMap A q (n + 2) =
            (fun p : ℝ × (Fin (n + 1) → ℝ) =>
              gaussianOneCoordinateMap A q p.1 +
                gaussianCoordinateSumMap A q (n + 1) p.2) ∘ e := by
        ext g
        simp [gaussianCoordinateSumMap, e, Fin.sum_univ_succ, Fin.tail]
      have hcoord : Measurable (gaussianOneCoordinateMap A q) := by
        unfold gaussianOneCoordinateMap
        simp_rw [Real.tanh_eq]
        fun_prop
      have hsumMeas :
          Measurable (gaussianCoordinateSumMap A q (n + 1)) :=
        measurable_gaussianCoordinateSumMap A q (n + 1)
      have hpair : Measurable
          (fun p : ℝ × (Fin (n + 1) → ℝ) =>
            gaussianOneCoordinateMap A q p.1 +
              gaussianCoordinateSumMap A q (n + 1) p.2) := by
        fun_prop
      rw [hsum, ← Measure.map_map hpair e.measurable, he,
        map_add_prod_eq_conv_map hcoord hsumMeas, ih,
        Measure.conv_comm, ← gaussianCoordinateSumLaw_succ]

/-- For every positive dimension `N`, the transformed sum of the `Fin N`
Gaussian coordinates has recursive convolution index `N - 1`. -/
theorem map_gaussianCoordinateSumMap_gaussianVec {A q : ℝ} {N : ℕ}
    (hN : 0 < N) :
    Measure.map (gaussianCoordinateSumMap A q N) (gaussianVec N) =
      gaussianCoordinateSumLaw A q (N - 1) := by
  cases N with
  | zero => simp at hN
  | succ n =>
      simpa using map_gaussianCoordinateSumMap_gaussianVec_succ A q n

private lemma map_withDensity_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} (e : α ≃ᵐ β) {f : α → ENNReal}
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [e.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  rw [setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable]
  simp

private lemma map_inv_mul_withDensity
    {f : ℝ → ENNReal} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    Measure.map (fun x : ℝ => a⁻¹ * x) (volume.withDensity f) =
      volume.withDensity (fun y => ENNReal.ofReal a * f (a * y)) := by
  let e : ℝ ≃ᵐ ℝ :=
    (Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero ha.ne')).toMeasurableEquiv
  rw [show (fun x : ℝ => a⁻¹ * x) = e by rfl,
    map_withDensity_equiv e hf]
  have hemap :
      Measure.map e volume =
        Measure.map (fun x : ℝ => a⁻¹ * x) volume := rfl
  have hcomp : f ∘ e.symm = fun y => f (a * y) := by
    funext y
    simp [e]
  rw [hemap, hcomp]
  rw [Real.map_volume_mul_left (inv_ne_zero ha.ne')]
  simp only [inv_inv, abs_of_pos ha]
  rw [withDensity_smul_measure, ← withDensity_smul]
  · rfl
  · exact hf.comp (by fun_prop)

/-- The density obtained by scaling the sum of `N` transformed Gaussian
coordinates by `1 / N`, as in the random map `Fmap`. -/
noncomputable def gaussianAverageDensity (A q : ℝ) (N : ℕ) (y : ℝ) :
    ENNReal :=
  ENNReal.ofReal N *
    gaussianCoordinateSumDensity A q (N - 1) ((N : ℝ) * y)

/-- The scaled `N`-coordinate average density is Borel measurable. -/
lemma measurable_gaussianAverageDensity (A q : ℝ) (N : ℕ) :
    Measurable (gaussianAverageDensity A q N) := by
  unfold gaussianAverageDensity
  exact measurable_const.mul <|
    (measurable_gaussianCoordinateSumDensity A q (N - 1)).comp <| by
      fun_prop

/-- **Transition density of the squared-radius chain.**  In every positive
dimension, the one-step law from `q > 0` is the `1 / N` scaling of the
recursive transformed-coordinate sum density. -/
theorem Kchain_apply_eq_withDensity_gaussianAverageDensity
    {A q : ℝ} {N : ℕ} (hA : 0 < A) (hq : 0 < q) (hN : 0 < N) :
    Kchain A N q =
      volume.withDensity (gaussianAverageDensity A q N) := by
  rw [Kchain_apply]
  have hF :
      Fmap A N q =
        (fun x : ℝ => (N : ℝ)⁻¹ * x) ∘
          gaussianCoordinateSumMap A q N := by
    funext g
    rfl
  rw [hF, ← Measure.map_map (by fun_prop)
    (measurable_gaussianCoordinateSumMap A q N)]
  rw [map_gaussianCoordinateSumMap_gaussianVec hN,
    gaussianCoordinateSumLaw_eq_withDensity hA hq]
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  change
    Measure.map (fun x : ℝ => (N : ℝ)⁻¹ * x)
        (volume.withDensity (gaussianCoordinateSumDensity A q (N - 1))) =
      volume.withDensity (fun y =>
        ENNReal.ofReal N *
          gaussianCoordinateSumDensity A q (N - 1) ((N : ℝ) * y))
  exact map_inv_mul_withDensity
    (measurable_gaussianCoordinateSumDensity A q (N - 1)) hNreal

/-- From every positive state, the `Kchain` transition law is absolutely
continuous with respect to Lebesgue measure. -/
lemma Kchain_apply_absolutelyContinuous_volume
    {A q : ℝ} {N : ℕ} (hA : 0 < A) (hq : 0 < q) (hN : 0 < N) :
    Kchain A N q ≪ volume := by
  rw [Kchain_apply_eq_withDensity_gaussianAverageDensity hA hq hN]
  exact withDensity_absolutelyContinuous volume _

/-- From every positive state, the `Kchain` transition lies in the open
interior `(0, 1)` almost surely. -/
lemma Kchain_apply_Ioo_eq_one
    {A q : ℝ} {N : ℕ} (hA : 0 < A) (hq : 0 < q) (hN : 0 < N) :
    Kchain A N q (Set.Ioo (0 : ℝ) 1) = 1 := by
  have hboundary : Kchain A N q ({0, 1} : Set ℝ) = 0 :=
    Kchain_apply_absolutelyContinuous_volume hA hq hN <| by
      rw [Set.insert_eq]
      exact measure_union_null Real.volume_singleton Real.volume_singleton
  have hcover :
      (Set.Ioo (0 : ℝ) 1)ᶜ ⊆
        (Set.Icc (0 : ℝ) 1)ᶜ ∪ ({0, 1} : Set ℝ) := by
    intro x hx
    by_cases hIcc : x ∈ Set.Icc (0 : ℝ) 1
    · right
      simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt] at hx
      simp only [Set.mem_Icc] at hIcc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hx with hx | hx
      · exact Or.inl (le_antisymm hx hIcc.1)
      · exact Or.inr (le_antisymm hIcc.2 hx)
    · exact Or.inl hIcc
  have hcompl : Kchain A N q ((Set.Ioo (0 : ℝ) 1)ᶜ) = 0 :=
    measure_mono_null hcover <|
      measure_union_null (Kchain_apply_Icc_compl A hN q) hboundary
  rw [measure_of_measure_compl_eq_zero hcompl]
  simp

/-- The squared-radius transition kernel restricted to the positive interior
state space `(0, 1)`.  The positivity hypotheses ensure that this restriction
is a Markov kernel. -/
noncomputable def KchainInterior (A : ℝ) (N : ℕ) (_hA : 0 < A) (_hN : 0 < N) :
    Kernel (Set.Ioo (0 : ℝ) 1) (Set.Ioo (0 : ℝ) 1) :=
  Kernel.comapRight
    ((Kchain A N).comap
      ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ) measurable_subtype_coe)
    (MeasurableEmbedding.subtype_coe measurableSet_Ioo)

instance (A : ℝ) (N : ℕ) (hA : 0 < A) (hN : 0 < N) :
    IsMarkovKernel (KchainInterior A N hA hN) := by
  unfold KchainInterior
  apply Kernel.IsMarkovKernel.comapRight
  intro q
  rw [Kernel.comap_apply, Subtype.range_coe_subtype]
  exact Kchain_apply_Ioo_eq_one hA q.property.1 hN

/-- Evaluation of the interior kernel is evaluation of `Kchain` on the
corresponding image in `(0, 1)`. -/
lemma KchainInterior_apply
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (q : Set.Ioo (0 : ℝ) 1) {B : Set (Set.Ioo (0 : ℝ) 1)}
    (hB : MeasurableSet B) :
    KchainInterior A N hA hN q B = Kchain A N q (Subtype.val '' B) := by
  unfold KchainInterior
  rw [Kernel.comapRight_apply' _ _ _ hB, Kernel.comap_apply]

/-- Mapping the interior transition law back into `ℝ` recovers the full
`Kchain` transition from the corresponding interior state. -/
lemma KchainInterior_map_subtype_val
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N) :
    (KchainInterior A N hA hN).map
        ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ) =
      (Kchain A N).comap
        ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ) measurable_subtype_coe := by
  unfold KchainInterior
  ext1 q
  rw [Kernel.map_apply _ measurable_subtype_coe,
    Kernel.comapRight_apply, Kernel.comap_apply,
    map_comap_subtype_coe measurableSet_Ioo]
  apply Measure.restrict_eq_self_of_ae_mem
  exact (mem_ae_iff_prob_eq_one measurableSet_Ioo).2
    (Kchain_apply_Ioo_eq_one hA q.property.1 hN)

private lemma comp_map_measure
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (κ : Kernel β γ)
    {f : α → β} (hf : Measurable f) :
    κ ∘ₘ (μ.map f) = (κ.comap f hf) ∘ₘ μ := by
  ext s hs
  rw [Measure.bind_apply hs κ.aemeasurable,
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe κ hs) hf]
  rfl

/-- A measure pushed forward from the interior subtype is carried by
`(0, 1)`; for a probability measure, the left-hand side is therefore one. -/
lemma map_subtype_val_apply_Ioo (μ : Measure (Set.Ioo (0 : ℝ) 1)) :
    (μ.map Subtype.val) (Set.Ioo (0 : ℝ) 1) = μ Set.univ := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Ioo]
  simp

/-- Every invariant measure of the interior kernel pushes forward under the
subtype inclusion to an invariant measure of the full squared-radius kernel.
The pushed-forward measure is automatically carried by `(0, 1)`. -/
theorem invariant_Kchain_map_subtype_val_of_invariant_KchainInterior
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (μ : Measure (Set.Ioo (0 : ℝ) 1))
    (hμ : Kernel.Invariant (KchainInterior A N hA hN) μ) :
    Kernel.Invariant (Kchain A N) (μ.map Subtype.val) := by
  unfold Kernel.Invariant at hμ ⊢
  calc
    (Kchain A N) ∘ₘ (μ.map Subtype.val) =
        ((Kchain A N).comap Subtype.val measurable_subtype_coe) ∘ₘ μ :=
      comp_map_measure μ (Kchain A N) measurable_subtype_coe
    _ = ((KchainInterior A N hA hN).map Subtype.val) ∘ₘ μ := by
      rw [KchainInterior_map_subtype_val hA hN]
    _ = ((KchainInterior A N hA hN) ∘ₘ μ).map Subtype.val :=
      (Measure.map_comp μ (KchainInterior A N hA hN) measurable_subtype_coe).symm
    _ = μ.map Subtype.val := by rw [hμ]

/-- Pulling an interior-supported probability measure back to the subtype and
then mapping it into `ℝ` recovers the original measure. -/
lemma map_comap_subtype_val_eq_of_apply_Ioo_eq_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνIoo : ν (Set.Ioo (0 : ℝ) 1) = 1) :
    (ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)).map Subtype.val = ν := by
  rw [map_comap_subtype_coe measurableSet_Ioo]
  apply Measure.restrict_eq_self_of_ae_mem
  exact (mem_ae_iff_prob_eq_one measurableSet_Ioo).2 hνIoo

/-- The pullback of an interior-supported probability measure along the
subtype inclusion is again a probability measure. -/
lemma isProbabilityMeasure_comap_subtype_val_of_apply_Ioo_eq_one
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνIoo : ν (Set.Ioo (0 : ℝ) 1) = 1) :
    IsProbabilityMeasure
      (ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)) := by
  apply (MeasurableEmbedding.subtype_coe measurableSet_Ioo).isProbabilityMeasure_comap
  rw [Subtype.range_coe_subtype]
  exact (mem_ae_iff_prob_eq_one measurableSet_Ioo).2 hνIoo

/-- A full `Kchain`-invariant probability measure carried by `(0, 1)` pulls
back along the subtype inclusion to a `KchainInterior`-invariant measure. -/
theorem invariant_KchainInterior_comap_subtype_val_of_invariant_Kchain
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνIoo : ν (Set.Ioo (0 : ℝ) 1) = 1)
    (hν : Kernel.Invariant (Kchain A N) ν) :
    Kernel.Invariant (KchainInterior A N hA hN)
      (ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)) := by
  unfold Kernel.Invariant at hν ⊢
  apply (MeasurableEmbedding.subtype_coe measurableSet_Ioo).map_injective
  calc
    ((KchainInterior A N hA hN) ∘ₘ
          ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)).map Subtype.val =
        ((KchainInterior A N hA hN).map Subtype.val) ∘ₘ
          ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ) :=
      Measure.map_comp _ _ measurable_subtype_coe
    _ = ((Kchain A N).comap Subtype.val measurable_subtype_coe) ∘ₘ
          ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ) := by
      rw [KchainInterior_map_subtype_val hA hN]
    _ = (Kchain A N) ∘ₘ
          ((ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)).map Subtype.val) :=
      (comp_map_measure _ (Kchain A N) measurable_subtype_coe).symm
    _ = (Kchain A N) ∘ₘ ν := by
      rw [map_comap_subtype_val_eq_of_apply_Ioo_eq_one ν hνIoo]
    _ = ν := hν
    _ = (ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)).map Subtype.val :=
      (map_comap_subtype_val_eq_of_apply_Ioo_eq_one ν hνIoo).symm

/-- Lebesgue measure pulled back to the positive interior subtype `(0, 1)`. -/
noncomputable def KchainInteriorVolume : Measure (Set.Ioo (0 : ℝ) 1) :=
  Measure.comap Subtype.val volume

/-- The interior Lebesgue measure of a subtype set is the Lebesgue measure of
its image in `ℝ`. -/
lemma KchainInteriorVolume_apply (B : Set (Set.Ioo (0 : ℝ) 1)) :
    KchainInteriorVolume B = volume (Subtype.val '' B) := by
  exact comap_subtype_coe_apply measurableSet_Ioo volume B

/-- Every recursive coordinate-sum density is nonnegative. -/
lemma gaussianCoordinateSumDensity_nonneg (A q : ℝ) (n : ℕ) (z : ℝ) :
    0 ≤ gaussianCoordinateSumDensity A q n z :=
  bot_le

/-- The density of a sum of `n + 1` coordinates is strictly positive
throughout the interior `(0, n + 1)` of its support. -/
lemma gaussianCoordinateSumDensity_pos {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) (n : ℕ) {z : ℝ}
    (hz : z ∈ Set.Ioo (0 : ℝ) ((n + 1 : ℕ) : ℝ)) :
    0 < gaussianCoordinateSumDensity A q n z := by
  induction n generalizing z with
  | zero =>
      rw [gaussianCoordinateSumDensity_zero]
      apply ENNReal.ofReal_pos.2
      exact gaussianOneCoordinateDensity_pos hA hq (by simpa using hz)
  | succ n ih =>
      rw [gaussianCoordinateSumDensity_succ, MeasureTheory.lconvolution_def]
      let f : ℝ → ENNReal := gaussianCoordinateSumDensity A q n
      let g : ℝ → ENNReal :=
        fun y => ENNReal.ofReal (gaussianOneCoordinateDensity A q y)
      have hf : Measurable f :=
        measurable_gaussianCoordinateSumDensity A q n
      have hg : Measurable g :=
        (measurable_gaussianOneCoordinateDensity A q).ennreal_ofReal
      have hshift : Measurable (fun y : ℝ => -y + z) := by fun_prop
      have hz_upper :
          z < ((n + 1 : ℕ) : ℝ) + 1 := by
        norm_num [Nat.cast_add, Nat.succ_eq_add_one] at hz ⊢
        exact hz.2
      have hint :
          max 0 (z - 1) < min (((n + 1 : ℕ) : ℝ)) z := by
        refine (max_lt_iff).2 ⟨?_, ?_⟩
        · exact (lt_min_iff).2 ⟨by positivity, hz.1⟩
        · exact (lt_min_iff).2 ⟨by linarith, by linarith⟩
      have hsub :
          Set.Ioo (max 0 (z - 1)) (min (((n + 1 : ℕ) : ℝ)) z) ⊆
            Function.support (fun y => f y * g (-y + z)) := by
        intro y hy
        have hy_pos : 0 < y :=
          (le_max_left 0 (z - 1)).trans_lt hy.1
        have hy_lt_upper : y < ((n + 1 : ℕ) : ℝ) :=
          hy.2.trans_le (min_le_left (((n + 1 : ℕ) : ℝ)) z)
        have hy_lt_z : y < z :=
          hy.2.trans_le (min_le_right (((n + 1 : ℕ) : ℝ)) z)
        have hz_sub_y_lt_one : -y + z < 1 := by
          have hz_sub_one_lt_y : z - 1 < y :=
            (le_max_right 0 (z - 1)).trans_lt hy.1
          linarith
        have hyI : y ∈ Set.Ioo (0 : ℝ) ((n + 1 : ℕ) : ℝ) :=
          ⟨hy_pos, hy_lt_upper⟩
        have hzyI : -y + z ∈ Set.Ioo (0 : ℝ) 1 :=
          ⟨by linarith, hz_sub_y_lt_one⟩
        exact (ENNReal.mul_pos (ih hyI).ne'
          (ENNReal.ofReal_pos.2
            (gaussianOneCoordinateDensity_pos hA hq hzyI)).ne').ne'
      refine (lintegral_pos_iff_support (hf.mul (hg.comp hshift))).2 ?_
      exact ((Measure.measure_Ioo_pos volume).2 hint).trans_le (measure_mono hsub)

/-- The `Kchain` transition density is strictly positive throughout its
interior support `(0, 1)`. -/
lemma gaussianAverageDensity_pos
    {A q : ℝ} {N : ℕ} (hA : 0 < A) (hq : 0 < q) (hN : 0 < N)
    {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    0 < gaussianAverageDensity A q N y := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hindex : N - 1 + 1 = N := by omega
  unfold gaussianAverageDensity
  exact (ENNReal.mul_pos
    (ENNReal.ofReal_pos.mpr hNreal).ne'
    (gaussianCoordinateSumDensity_pos
      (z := (N : ℝ) * y) hA hq (N - 1) <| by
      rw [hindex]
      exact ⟨mul_pos hNreal hy.1,
        by simpa using mul_lt_mul_of_pos_left hy.2 hNreal⟩).ne')

/-- Every measurable positive-Lebesgue-measure subset of `(0, 1)` has
positive one-step `Kchain` mass from every positive state. -/
theorem Kchain_apply_pos_of_volume_pos
    {A q : ℝ} {N : ℕ} (hA : 0 < A) (hq : 0 < q) (hN : 0 < N)
    {B : Set ℝ} (hB : MeasurableSet B) (hBvol : 0 < volume B)
    (hBsub : B ⊆ Set.Ioo (0 : ℝ) 1) :
    0 < Kchain A N q B := by
  rw [Kchain_apply_eq_withDensity_gaussianAverageDensity hA hq hN,
    withDensity_apply _ hB]
  rw [setLIntegral_pos_iff (measurable_gaussianAverageDensity A q N)]
  have hsupp : B ⊆ Function.support (gaussianAverageDensity A q N) :=
    fun _ hy => ne_of_gt (gaussianAverageDensity_pos hA hq hN (hBsub hy))
  simpa [Set.inter_eq_right.mpr hsupp] using hBvol

/-- On the interior `(0, 1)`, Lebesgue measure is absolutely continuous with
respect to every `Kchain` transition law from a positive state. -/
lemma volume_restrict_Ioo_absolutelyContinuous_Kchain_apply
    {A q : ℝ} {N : ℕ} (hA : 0 < A) (hq : 0 < q) (hN : 0 < N) :
    volume.restrict (Set.Ioo (0 : ℝ) 1) ≪ Kchain A N q := by
  refine Measure.AbsolutelyContinuous.mk fun B hB hKB => ?_
  rw [Measure.restrict_apply hB]
  by_contra hvol
  have hpos : 0 < Kchain A N q (B ∩ Set.Ioo (0 : ℝ) 1) :=
    Kchain_apply_pos_of_volume_pos hA hq hN
      (hB.inter measurableSet_Ioo) (pos_iff_ne_zero.mpr hvol) Set.inter_subset_right
  have hposB : 0 < Kchain A N q B :=
    hpos.trans_le (measure_mono Set.inter_subset_left)
  exact (ne_of_gt hposB) hKB

/-- Restricting to `(0, 1)` preserves absolute continuity of the `Kchain`
transition law with respect to Lebesgue measure. -/
lemma Kchain_apply_restrict_Ioo_absolutelyContinuous_volume_restrict_Ioo
    {A q : ℝ} {N : ℕ} (hA : 0 < A) (hq : 0 < q) (hN : 0 < N) :
    (Kchain A N q).restrict (Set.Ioo (0 : ℝ) 1) ≪
      volume.restrict (Set.Ioo (0 : ℝ) 1) :=
  (Kchain_apply_absolutelyContinuous_volume hA hq hN).restrict _

/-- On `(0, 1)`, the restricted `Kchain` transition law also dominates
Lebesgue measure. -/
lemma volume_restrict_Ioo_absolutelyContinuous_Kchain_apply_restrict_Ioo
    {A q : ℝ} {N : ℕ} (hA : 0 < A) (hq : 0 < q) (hN : 0 < N) :
    volume.restrict (Set.Ioo (0 : ℝ) 1) ≪
      (Kchain A N q).restrict (Set.Ioo (0 : ℝ) 1) := by
  have h := (volume_restrict_Ioo_absolutelyContinuous_Kchain_apply
    hA hq hN).restrict (Set.Ioo (0 : ℝ) 1)
  simpa only [Measure.restrict_restrict measurableSet_Ioo,
    Set.inter_self] using h

/-- The interior squared-radius kernel is Lebesgue-irreducible.  In fact every
positive-interior state reaches every positive-interior-volume measurable set
in one step. -/
instance (A : ℝ) (N : ℕ) (hA : 0 < A) (hN : 0 < N) :
    Kernel.IsIrreducible KchainInteriorVolume (KchainInterior A N hA hN) where
  irreducible B hB hBvol q := by
    rw [KchainInteriorVolume_apply] at hBvol
    have hBimage :
        MeasurableSet (Subtype.val '' B : Set ℝ) :=
      (MeasurableEmbedding.subtype_coe measurableSet_Ioo).measurableSet_image.mpr hB
    have hBsub : Subtype.val '' B ⊆ Set.Ioo (0 : ℝ) 1 := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    refine ⟨1, ?_⟩
    simpa only [pow_one, KchainInterior_apply hA hN q hB] using
      Kchain_apply_pos_of_volume_pos hA q.property.1 hN hBimage hBvol hBsub

/-- Interior Lebesgue measure on `(0, 1)` is nonzero. -/
lemma KchainInteriorVolume_ne_zero : KchainInteriorVolume ≠ 0 := by
  rw [← Measure.measure_univ_ne_zero, KchainInteriorVolume_apply]
  simpa only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq] using
    ((Measure.measure_Ioo_pos volume).2 (by norm_num : (0 : ℝ) < 1)).ne'

/-- The interior squared-radius kernel has at most one invariant probability
measure. -/
theorem invariant_probability_unique_KchainInterior
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (μ ν : Measure (Set.Ioo (0 : ℝ) 1))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Kernel.Invariant (KchainInterior A N hA hN) μ)
    (hν : Kernel.Invariant (KchainInterior A N hA hN) ν) :
    μ = ν :=
  invariant_probability_unique KchainInteriorVolume_ne_zero hμ hν

/-- The full squared-radius chain has at most one invariant probability
measure carried by the positive interior `(0, 1)`. -/
theorem invariant_probability_unique_Kchain_of_apply_Ioo_eq_one
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμIoo : μ (Set.Ioo (0 : ℝ) 1) = 1)
    (hνIoo : ν (Set.Ioo (0 : ℝ) 1) = 1)
    (hμ : Kernel.Invariant (Kchain A N) μ)
    (hν : Kernel.Invariant (Kchain A N) ν) :
    μ = ν := by
  let μI := μ.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)
  let νI := ν.comap ((↑) : Set.Ioo (0 : ℝ) 1 → ℝ)
  letI : IsProbabilityMeasure μI := by
    dsimp [μI]
    exact isProbabilityMeasure_comap_subtype_val_of_apply_Ioo_eq_one μ hμIoo
  letI : IsProbabilityMeasure νI := by
    dsimp [νI]
    exact isProbabilityMeasure_comap_subtype_val_of_apply_Ioo_eq_one ν hνIoo
  have hμI : Kernel.Invariant (KchainInterior A N hA hN) μI := by
    dsimp [μI]
    exact invariant_KchainInterior_comap_subtype_val_of_invariant_Kchain
      hA hN μ hμIoo hμ
  have hνI : Kernel.Invariant (KchainInterior A N hA hN) νI := by
    dsimp [νI]
    exact invariant_KchainInterior_comap_subtype_val_of_invariant_Kchain
      hA hN ν hνIoo hν
  have hI : μI = νI :=
    invariant_probability_unique_KchainInterior hA hN μI νI hμI hνI
  calc
    μ = μI.map Subtype.val := by
      dsimp [μI]
      exact (map_comap_subtype_val_eq_of_apply_Ioo_eq_one μ hμIoo).symm
    _ = νI.map Subtype.val := congrArg (fun ρ => ρ.map Subtype.val) hI
    _ = ν := by
      dsimp [νI]
      exact map_comap_subtype_val_eq_of_apply_Ioo_eq_one ν hνIoo

/-- An invariant probability carried by `(0, 1]` is in fact carried by the
open interior `(0, 1)`. -/
theorem invariant_Kchain_apply_Ioo_eq_one_of_Ioc_compl
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν)
    (hνIoc : ν ((Set.Ioc (0 : ℝ) 1)ᶜ) = 0) :
    ν (Set.Ioo (0 : ℝ) 1) = 1 := by
  calc
    ν (Set.Ioo (0 : ℝ) 1) =
        (Kchain A N ∘ₘ ν) (Set.Ioo (0 : ℝ) 1) :=
      congrArg (fun ρ : Measure ℝ => ρ (Set.Ioo (0 : ℝ) 1)) hν.def.symm
    _ = ∫⁻ q, Kchain A N q (Set.Ioo (0 : ℝ) 1) ∂ν :=
      Measure.bind_apply measurableSet_Ioo (Kchain A N).aemeasurable
    _ = ∫⁻ _q, (1 : ENNReal) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [(mem_ae_iff.mpr hνIoc)] with q hq
      exact Kchain_apply_Ioo_eq_one hA hq.1 hN
    _ = 1 := by simp

/-- The normalized nonzero component of an invariant probability carried by
`[0, 1]` assigns mass one to `(0, 1)`. -/
theorem nonzeroPart_apply_Ioo_eq_one
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν)
    (hν_support : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hν0 : ν ({0} : Set ℝ) < 1) :
    nonzeroPart ν (Set.Ioo (0 : ℝ) 1) = 1 := by
  letI : IsProbabilityMeasure (nonzeroPart ν) :=
    nonzeroPart_isProbabilityMeasure ν hν0
  exact invariant_Kchain_apply_Ioo_eq_one_of_Ioc_compl hA hN
    (nonzeroPart ν) (invariant_nonzeroPart A N ν hν)
    (nonzeroPart_Ioc_compl ν hν_support)

/-- Any two invariant probabilities carried by `[0, 1]` and not concentrated
at the absorbing origin have the same normalized nonzero component. -/
theorem nonzeroPart_eq_of_invariant_Kchain
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Kernel.Invariant (Kchain A N) μ)
    (hν : Kernel.Invariant (Kchain A N) ν)
    (hμ_support : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hν_support : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hμ0 : μ ({0} : Set ℝ) < 1)
    (hν0 : ν ({0} : Set ℝ) < 1) :
    nonzeroPart μ = nonzeroPart ν := by
  letI : IsProbabilityMeasure (nonzeroPart μ) :=
    nonzeroPart_isProbabilityMeasure μ hμ0
  letI : IsProbabilityMeasure (nonzeroPart ν) :=
    nonzeroPart_isProbabilityMeasure ν hν0
  exact invariant_probability_unique_Kchain_of_apply_Ioo_eq_one hA hN
    (nonzeroPart μ) (nonzeroPart ν)
    (nonzeroPart_apply_Ioo_eq_one hA hN μ hμ hμ_support hμ0)
    (nonzeroPart_apply_Ioo_eq_one hA hN ν hν hν_support hν0)
    (invariant_nonzeroPart A N μ hμ)
    (invariant_nonzeroPart A N ν hν)

/-- A standard finite-dimensional Gaussian vector assigns positive mass to
every nonempty open set. -/
lemma gaussianVec_pos_of_isOpen {N : ℕ} {U : Set (Fin N → ℝ)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    0 < gaussianVec N U := by
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).isOpenPosMeasure
  haveI : Measure.IsOpenPosMeasure (gaussianVec N) := by
    unfold gaussianVec
    infer_instance
  exact hU.measure_pos _ hne

/-- **One-step topological positivity for `K_{A,N}`.**
For nonzero gain, positive dimension, and positive starting radius, the
squared-radius chain assigns positive mass to every nonempty open subset of
`(0,1)`.  This is the open-set consequence of the strictly positive transition
density in `prop:gaussian-unique-nonzero-invariant`. -/
theorem Kchain_apply_pos_of_isOpen {A : ℝ} {N : ℕ} (hA : A ≠ 0) (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) {O : Set ℝ} (hO : IsOpen O) (hne : O.Nonempty)
    (hOsub : O ⊆ Set.Ioo (0 : ℝ) 1) :
    0 < Kchain A N q O := by
  rw [Kchain_apply, Measure.map_apply (continuous_Fmap_right A N q).measurable
    hO.measurableSet]
  apply gaussianVec_pos_of_isOpen
  · exact hO.preimage (continuous_Fmap_right A N q)
  · obtain ⟨r, hr⟩ := hne
    have hrIoo := hOsub hr
    have hsqrt_pos : 0 < Real.sqrt r := Real.sqrt_pos.2 hrIoo.1
    have hsqrt_lt_one : Real.sqrt r < 1 := by
      simpa using Real.sqrt_lt_sqrt hrIoo.1.le hrIoo.2
    have hden : A * Real.sqrt q ≠ 0 :=
      mul_ne_zero hA (Real.sqrt_ne_zero'.2 hq)
    let g : Fin N → ℝ := fun _ => Real.artanh (Real.sqrt r) / (A * Real.sqrt q)
    refine ⟨g, ?_⟩
    change Fmap A N q g ∈ O
    suffices Fmap A N q g = r by simpa [this] using hr
    have harg (i : Fin N) :
        A * Real.sqrt q * g i = Real.artanh (Real.sqrt r) := by
      dsimp [g]
      field_simp
    unfold Fmap
    simp_rw [harg, Real.tanh_artanh ⟨by linarith, hsqrt_lt_one⟩]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Real.sq_sqrt hrIoo.1.le]
    field_simp

end AbsorptionCutoff
