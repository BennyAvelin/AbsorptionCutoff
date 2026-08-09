/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingAdapted

/-!
# Fixed-width coupling multiplier law

This continuation module combines finite-prefix adaptedness with independence
of the next product-space matrix innovation, identifies the discrepancy
multiplier's Gaussian radial law, and owns the resulting accumulated rounding
comparison.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

lemma iIndepFun_fixedWidthMatrixCoordinate (A : ℝ) (N : ℕ) :
    iIndepFun (fun n (ω : fixedWidthMatrixSampleSpace N) ↦ ω n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ ↦ gaussianMat A N)
    (X := fun _ : ℕ ↦ fun (W : Fin N → Fin N → ℝ) ↦ W)
    (by fun_prop)

/-- Under the canonical product Gaussian law, the strict matrix prefix before
time `n` is independent of the matrix innovation at time `n`. -/
lemma indepFun_fixedWidthMatrixPrefix_eval
    (A : ℝ) (N n : ℕ) :
    IndepFun (fixedWidthMatrixPrefix N n)
      (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  let S := Finset.range n
  let T : Finset ℕ := {n}
  have hbase := (iIndepFun_fixedWidthMatrixCoordinate A N).indepFun_finset
    S T (by simp [S, T]) (fun k ↦ measurable_pi_apply k)
  have hleft : Measurable
      (fun u : ((i : S) → (Fin N → Fin N → ℝ)) ↦
        fun k : Fin n ↦ u ⟨k, by simp [S]⟩) :=
    measurable_pi_lambda _ fun k ↦
      measurable_pi_apply (⟨k, by simp [S]⟩ : S)
  have hright : Measurable
      (fun u : ((i : T) → (Fin N → Fin N → ℝ)) ↦
        u ⟨n, by simp [T]⟩) :=
    measurable_pi_apply (⟨n, by simp [T]⟩ : T)
  have hcomp := hbase.comp hleft hright
  convert hcomp using 1
  · funext ω k
    rfl
  · funext ω
    rfl

/-- The normalized discrepancy direction is adapted to the strict past and is
therefore independent of the current matrix innovation. -/
lemma indepFun_fixedWidthDiscrepancyDirection_eval
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (x0 : Fin N → ℝ) (n : ℕ) :
    IndepFun
      (fun ω : fixedWidthMatrixSampleSpace N ↦
        fixedWidthUnitDirection hN
          (fixedWidthVectorDiscrepancy ρ N x0 n ω))
      (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hcomp := (indepFun_fixedWidthMatrixPrefix_eval A N n).comp
    (measurable_fixedWidthDiscrepancyDirectionFromPrefix hN ρ x0 n)
    measurable_id
  convert hcomp using 1
  · funext ω
    exact (fixedWidthDiscrepancyDirectionFromPrefix_apply hN ρ x0 n ω).symm
  · rfl

end AbsorptionCutoff
