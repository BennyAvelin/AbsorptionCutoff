/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.InvariantLaw

/-!
# Score smoothing for the supercritical radius chain

This module develops the one-coordinate score calculation and its
tensorization into the paper's one-step total-variation smoothing estimate.
Keeping these estimates separate from the transition-density construction
allows fast incremental builds while the smoothing proof is assembled.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- On the interior support, the radius derivative of the one-coordinate
density factors as the score times the density. -/
lemma hasDerivAt_gaussianOneCoordinateDensityFormula_q
    {A q y : ℝ} (hA : 0 < A) (hq : 0 < q) :
    HasDerivAt
      (fun r => gaussianOneCoordinateDensityFormula A r y)
      (gaussianOneCoordinateScore A q y *
        gaussianOneCoordinateDensityFormula A q y) q := by
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  let u : ℝ := Real.artanh (Real.sqrt y)
  let c : ℝ := (Real.sqrt y * (1 - y))⁻¹
  let n : ℝ → ℝ :=
    fun r => (A * Real.sqrt (2 * Real.pi * r))⁻¹
  let e : ℝ → ℝ :=
    fun r => Real.exp (-u ^ 2 / (2 * A ^ 2 * r))
  have hlin :
      HasDerivAt (fun r : ℝ => 2 * Real.pi * r) (2 * Real.pi) q := by
    exact hasDerivAt_const_mul (x := q) (2 * Real.pi)
  have hsqrt :=
    hlin.sqrt (by positivity : 2 * Real.pi * q ≠ 0)
  have hscaled := hsqrt.const_mul A
  have hinv :=
    hscaled.inv (by positivity : A * Real.sqrt (2 * Real.pi * q) ≠ 0)
  have hn :
      HasDerivAt n (-1 / (2 * q) * n q) q := by
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * q) := by positivity
    have hsqrt_sq :
        Real.sqrt (2 * Real.pi * q) ^ 2 = 2 * Real.pi * q :=
      Real.sq_sqrt (by positivity)
    have hcoef :
        -(A * (2 * Real.pi / (2 * Real.sqrt (2 * Real.pi * q)))) /
            (A * Real.sqrt (2 * Real.pi * q)) ^ 2 =
          -1 / (2 * q) * (A * Real.sqrt (2 * Real.pi * q))⁻¹ := by
      field_simp [hA.ne', hq.ne', ne_of_gt hsqrt_pos]
      nlinarith [hsqrt_sq]
    change HasDerivAt n
      (-(A * (2 * Real.pi / (2 * Real.sqrt (2 * Real.pi * q)))) /
        (A * Real.sqrt (2 * Real.pi * q)) ^ 2) q at hinv
    rw [hcoef] at hinv
    exact hinv
  have hden :
      HasDerivAt (fun r : ℝ => 2 * A ^ 2 * r) (2 * A ^ 2) q := by
    exact hasDerivAt_const_mul (x := q) (2 * A ^ 2)
  have hquot :=
    (hasDerivAt_const q (-u ^ 2)).div hden
      (by positivity : 2 * A ^ 2 * q ≠ 0)
  have he :
      HasDerivAt e
        (u ^ 2 / (2 * A ^ 2 * q ^ 2) * e q) q := by
    have hexp := hquot.exp
    have hcoef :
        Real.exp (-u ^ 2 / (2 * A ^ 2 * q)) *
            ((0 * (2 * A ^ 2 * q) - -u ^ 2 * (2 * A ^ 2)) /
              (2 * A ^ 2 * q) ^ 2) =
          u ^ 2 / (2 * A ^ 2 * q ^ 2) *
            Real.exp (-u ^ 2 / (2 * A ^ 2 * q)) := by
      field_simp [hA.ne', hq.ne']
      ring
    change HasDerivAt e
      (Real.exp (-u ^ 2 / (2 * A ^ 2 * q)) *
        ((0 * (2 * A ^ 2 * q) - -u ^ 2 * (2 * A ^ 2)) /
          (2 * A ^ 2 * q) ^ 2)) q at hexp
    rw [hcoef] at hexp
    exact hexp
  have hfull := (hn.mul_const c).mul he
  have hcoef :
      -1 / (2 * q) * n q * c * e q +
          n q * c * (u ^ 2 / (2 * A ^ 2 * q ^ 2) * e q) =
        gaussianOneCoordinateScore A q y *
          gaussianOneCoordinateDensityFormula A q y := by
    unfold gaussianOneCoordinateScore gaussianOneCoordinateDensityFormula
    dsimp [n, e, u, c]
    ring
  change HasDerivAt (fun r => n r * c * e r)
    (-1 / (2 * q) * n q * c * e q +
      n q * c * (u ^ 2 / (2 * A ^ 2 * q ^ 2) * e q)) q at hfull
  rw [hcoef] at hfull
  exact hfull

/-- The evaluated one-coordinate score is integrable under the standard
Gaussian law. -/
lemma integrable_gaussianOneCoordinateScore_map {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) :
    Integrable
      (fun x => gaussianOneCoordinateScore A q
        (gaussianOneCoordinateMap A q x))
      (gaussianReal 0 1) := by
  have hsub :=
    integrable_sq_gaussian.sub (integrable_const (1 : ℝ))
  have hpoly :
      Integrable (fun x : ℝ => (x ^ 2 - 1) / (2 * q))
        (gaussianReal 0 1) := by
    simpa only [Pi.sub_apply, div_eq_mul_inv] using
      hsub.mul_const (2 * q)⁻¹
  exact hpoly.congr (Filter.Eventually.of_forall fun x =>
    (gaussianOneCoordinateScore_map hA hq).symm)

/-- The evaluated one-coordinate score has mean zero under the standard
Gaussian law. -/
lemma integral_gaussianOneCoordinateScore_map_eq_zero {A q : ℝ}
    (hA : 0 < A) (hq : 0 < q) :
    ∫ x, gaussianOneCoordinateScore A q
        (gaussianOneCoordinateMap A q x) ∂gaussianReal 0 1 = 0 := by
  have hsqint :
      ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have hv := variance_id_gaussianReal (μ := 0) (v := 1)
    have hi : ∫ x : ℝ, x ∂gaussianReal 0 1 = 0 :=
      integral_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral (by fun_prop)] at hv
    simp only [id_eq, hi, sub_zero] at hv
    simpa using hv
  simp_rw [gaussianOneCoordinateScore_map hA hq]
  rw [integral_div,
    integral_sub integrable_sq_gaussian (integrable_const (1 : ℝ)),
    hsqint, integral_const, probReal_univ, one_smul]
  norm_num

end AbsorptionCutoff
