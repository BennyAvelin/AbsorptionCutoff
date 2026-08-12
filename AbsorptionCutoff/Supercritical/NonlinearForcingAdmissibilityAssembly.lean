/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.NonlinearForcingAdmissibility

/-!
# Assembly of nonlinear forcing admissibility

This continuation module carries the remaining directly Riemann integrable,
continuity, and positivity assembly for `prop:nd-forcing-admissibility`.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

namespace Renewal

/-- Multiplying a nonnegative kernel by a constant multiplies its d.R.i. norm
by at most that constant. -/
lemma driNorm_const_mul_le (c : ENNReal) (g : ℝ → ENNReal) :
    driNorm (fun x => c * g x) ≤ c * driNorm g := by
  have hcell (k : ℤ) : cellSup (fun x => c * g x) k ≤ c * cellSup g k :=
    iSup₂_le fun _ hx => mul_le_mul_right (le_cellSup hx) c
  rw [driNorm_def, driNorm_def, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hcell

/-- The d.R.i. norm of an average of real translates is controlled by twice the
original norm times the mass of the averaging measure. -/
lemma driNorm_lintegral_comp_sub_le_two_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (g : ℝ → ENNReal) (hg : Continuous g) (s : α → ℝ) (hs : Measurable s) :
    driNorm (fun y => ∫⁻ p, g (y - s p) ∂μ) ≤
      (2 * driNorm g) * μ Set.univ := by
  calc
    driNorm (fun y => ∫⁻ p, g (y - s p) ∂μ) ≤
        ∫⁻ p, driNorm (fun y => g (y - s p)) ∂μ := by
      apply driNorm_lintegral_le_lintegral_driNorm
      intro k
      exact ((continuous_cellSup_comp_sub g hg k).measurable.comp hs).aemeasurable
    _ ≤ ∫⁻ _ : α, 2 * driNorm g ∂μ := by
      exact lintegral_mono fun p => driNorm_comp_sub_le_two_mul g (s p)
    _ = (2 * driNorm g) * μ Set.univ := lintegral_const _

/-- A measurable weight enters the averaged-translate d.R.i. bound through its
nonnegative integral. -/
lemma driNorm_lintegral_mul_comp_sub_le_two_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : α → ENNReal) (hw : Measurable w)
    (g : ℝ → ENNReal) (hg : Continuous g) (s : α → ℝ) (hs : Measurable s) :
    driNorm (fun y => ∫⁻ p, w p * g (y - s p) ∂μ) ≤
      (2 * driNorm g) * ∫⁻ p, w p ∂μ := by
  have h := driNorm_lintegral_comp_sub_le_two_mul (μ.withDensity w) g hg s hs
  have hleft : (fun y => ∫⁻ p, g (y - s p) ∂μ.withDensity w) =
      fun y => ∫⁻ p, w p * g (y - s p) ∂μ := by
    funext y
    rw [lintegral_withDensity_eq_lintegral_mul μ hw
      (g := fun p => g (y - s p))
      (hg.measurable.comp (measurable_const.sub hs))]
    rfl
  rw [hleft] at h
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at h
  exact h

end Renewal

/-- A finite tilted radial moment gives finite d.R.i. norm for the averaged
shifted polar envelope. -/
theorem driNorm_lintegral_exp_tilt_mul_polarEnvelope_ne_top
    {N : ℕ} {β δ : ℝ} (hβ : 0 < β) (hβN : β < N)
    (μ : Measure (ℝ × EuclideanSpace ℝ (Fin N)))
    (hmoment : (∫⁻ p, ENNReal.ofReal (Real.exp ((β - δ) * p.1)) ∂μ) ≠ ⊤) :
    Renewal.driNorm
      (fun y => ∫⁻ p,
        ENNReal.ofReal (Real.exp ((β - δ) * p.1)) *
          ENNReal.ofReal
            (Real.exp (β * (y - p.1)) * polarEnvelope N (y - p.1)) ∂μ) ≠ ⊤ := by
  let g : ℝ → ENNReal := fun t =>
    ENNReal.ofReal (Real.exp (β * t) * polarEnvelope N t)
  have hg : Continuous g := by
    exact ENNReal.continuous_ofReal.comp (by dsimp [polarEnvelope]; fun_prop)
  have hle := Renewal.driNorm_lintegral_mul_comp_sub_le_two_mul μ
    (fun p : ℝ × EuclideanSpace ℝ (Fin N) =>
      ENNReal.ofReal (Real.exp ((β - δ) * p.1)))
    (by fun_prop) g hg (fun p => p.1) measurable_fst
  have hbase : Renewal.driNorm g ≠ ⊤ :=
    driNorm_exp_mul_polarEnvelope_ne_top hβ hβN
  apply ne_top_of_le_ne_top _ hle
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) hbase) hmoment

/-- The invariant-law subcritical moment makes the actual averaged polar
envelope directly Riemann integrable. -/
theorem driNorm_lintegral_exp_tilt_mul_polarEnvelope_of_invariant_Pkernel_ne_top
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0) :
    Renewal.driNorm
      (fun y => ∫⁻ p,
        ENNReal.ofReal (Real.exp ((cramerExponent A N - δ) * p.1)) *
          ENNReal.ofReal
            (Real.exp (cramerExponent A N * (y - p.1)) *
              polarEnvelope N (y - p.1)) ∂logPolarLaw N π) ≠ ⊤ := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hm :=
    integrable_exp_cramerExponent_sub_fst_logPolarLaw_of_invariant_Pkernel
      hA hN hsc hδ0 hδβ π hπ hπ0
  have hfinite := (hasFiniteIntegral_iff_enorm).mp hm.hasFiniteIntegral
  have heq :
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) =>
        ‖Real.exp ((cramerExponent A N - δ) * p.1)‖ₑ) =
      fun p => ENNReal.ofReal (Real.exp ((cramerExponent A N - δ) * p.1)) := by
    funext p
    exact Real.enorm_eq_ofReal (Real.exp_nonneg _)
  rw [heq] at hfinite
  exact driNorm_lintegral_exp_tilt_mul_polarEnvelope_ne_top
    hβmem.1 hβmem.2 (logPolarLaw N π) (ne_of_lt hfinite)

end AbsorptionCutoff
