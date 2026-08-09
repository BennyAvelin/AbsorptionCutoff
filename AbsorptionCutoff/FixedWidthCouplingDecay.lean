/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingMoments
import AbsorptionCutoff.AffineEntrance

/-!
# Fixed-width coupling multiplier decay

This continuation module selects a decaying positive exponential moment for
the synchronous log multipliers and proves the logarithmic-horizon subproduct
bound used to accumulate rounding errors.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Every path-specific log multiplier has exponential moments throughout a
neighborhood of zero. -/
lemma zero_mem_interior_integrableExpSet_fixedWidthDiscrepancyLogMultiplier
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    0 ∈ interior
      (integrableExpSet (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n)
        (fixedWidthMatrixGaussianMeasure A N)) := by
  apply interior_maximal
    (Ioo_subset_integrableExpSet_fixedWidthDiscrepancyLogMultiplier
      hA hN ρ x0 n) isOpen_Ioo
  constructor
  · exact neg_neg_of_pos (by exact_mod_cast hN)
  · exact_mod_cast hN

/-- In the fixed-width subcritical regime, every path-specific log multiplier
has a positive integrable exponential moment whose mgf is strictly below one. -/
lemma exists_pos_integrable_mgf_fixedWidthDiscrepancyLogMultiplier_lt_one
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    ∃ s : ℝ, 0 < s ∧
      Integrable (fun ω ↦ Real.exp
        (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 n ω))
        (fixedWidthMatrixGaussianMeasure A N) ∧
      mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n)
        (fixedWidthMatrixGaussianMeasure A N) s < 1 := by
  apply exists_pos_integrable_mgf_lt_one
    (fixedWidthMatrixGaussianMeasure A N)
    (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n)
    (zero_mem_interior_integrableExpSet_fixedWidthDiscrepancyLogMultiplier
      hA hN ρ x0 n)
  rw [integral_fixedWidthDiscrepancyLogMultiplier_eq_logRadialDrift
    hA hN ρ x0 n]
  exact hsub

end AbsorptionCutoff
