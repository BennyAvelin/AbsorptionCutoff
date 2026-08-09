/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingBounds

/-!
# Fixed-width coupling multiplier moments

This continuation module transfers exponential moments of the Gaussian radial
increment to the synchronous discrepancy multipliers and proves the resulting
logarithmic-horizon subproduct bounds.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Negating the Gaussian log-radial increment reflects the exponential
parameter, so it retains the symmetric integrability interval `(-N, N)`. -/
lemma Ioo_subset_integrableExpSet_neg_logRadialIncrement
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    Set.Ioo (-(N : ℝ)) (N : ℝ) ⊆
      integrableExpSet (fun g : Fin N → ℝ ↦ -logRadialIncrement A N g)
        (gaussianVec N) := by
  intro t ht
  have hneg : -t ∈ Set.Ioo (-(N : ℝ)) (N : ℝ) := by
    constructor <;> linarith [ht.1, ht.2]
  have hint :=
    Ioo_subset_integrableExpSet_logRadialIncrement hA hN hneg
  change Integrable
    (fun g ↦ Real.exp (t * (-logRadialIncrement A N g))) (gaussianVec N)
  change Integrable
    (fun g ↦ Real.exp ((-t) * logRadialIncrement A N g)) (gaussianVec N) at hint
  simpa only [mul_neg, neg_mul] using hint

/-- Every path-specific log multiplier inherits the common symmetric
exponential-integrability interval `(-N, N)`. -/
lemma Ioo_subset_integrableExpSet_fixedWidthDiscrepancyLogMultiplier
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Set.Ioo (-(N : ℝ)) (N : ℝ) ⊆
      integrableExpSet (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n)
        (fixedWidthMatrixGaussianMeasure A N) := by
  intro t ht
  have href :=
    Ioo_subset_integrableExpSet_neg_logRadialIncrement hA hN ht
  have hident :=
    (identDistrib_fixedWidthDiscrepancyLogMultiplier hA hN ρ x0 n).comp
      (u := fun z : ℝ ↦ Real.exp (t * z)) (by fun_prop)
  change Integrable
    (fun ω ↦ Real.exp
      (t * fixedWidthDiscrepancyLogMultiplier hN ρ x0 n ω))
      (fixedWidthMatrixGaussianMeasure A N)
  exact (hident.integrable_iff).mpr href

end AbsorptionCutoff
