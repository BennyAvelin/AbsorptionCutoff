/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingProbability

/-!
# Adapted fixed-width coupling multipliers

This continuation module identifies the synchronous discrepancy multiplier as
an adapted transform of the matrix innovations and proves its common Gaussian
radial law. It then owns the resulting high-probability accumulated rounding
comparison on logarithmic time horizons.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

lemma fixedWidthUnroundedVectorPath_eq_of_forall_lt
    (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ)
    {ω ω' : fixedWidthMatrixSampleSpace N}
    (hω : ∀ k < n, ω k = ω' k) :
    fixedWidthUnroundedVectorPath N x0 n ω =
      fixedWidthUnroundedVectorPath N x0 n ω' := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [fixedWidthUnroundedVectorPath]
      rw [hω n (Nat.lt_succ_self n)]
      rw [ih (fun k hk ↦ hω k (Nat.lt_succ_of_lt hk))]

lemma fixedWidthRoundedVectorPath_eq_of_forall_lt
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ)
    {ω ω' : fixedWidthMatrixSampleSpace N}
    (hω : ∀ k < n, ω k = ω' k) :
    fixedWidthRoundedVectorPath ρ N x0 n ω =
      fixedWidthRoundedVectorPath ρ N x0 n ω' := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [fixedWidthRoundedVectorPath]
      rw [hω n (Nat.lt_succ_self n)]
      rw [ih (fun k hk ↦ hω k (Nat.lt_succ_of_lt hk))]

/-- The discrepancy direction at time `n` only depends on matrix innovations
with index strictly below `n`. -/
lemma fixedWidthDiscrepancyDirection_eq_of_forall_lt
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ)
    {ω ω' : fixedWidthMatrixSampleSpace N}
    (hω : ∀ k < n, ω k = ω' k) :
    fixedWidthUnitDirection hN
        (fixedWidthVectorDiscrepancy ρ N x0 n ω) =
      fixedWidthUnitDirection hN
        (fixedWidthVectorDiscrepancy ρ N x0 n ω') := by
  congr 1
  unfold fixedWidthVectorDiscrepancy
  rw [fixedWidthRoundedVectorPath_eq_of_forall_lt ρ N x0 n hω,
    fixedWidthUnroundedVectorPath_eq_of_forall_lt N x0 n hω]

/-- Restriction of the canonical matrix sequence to the innovations strictly
before time `n`. -/
def fixedWidthMatrixPrefix (N n : ℕ) :
    fixedWidthMatrixSampleSpace N →
      (Fin n → (Fin N → Fin N → ℝ)) :=
  fun ω k ↦ ω k

lemma measurable_fixedWidthMatrixPrefix (N n : ℕ) :
    Measurable (fixedWidthMatrixPrefix N n) := by
  unfold fixedWidthMatrixPrefix
  exact measurable_pi_lambda _ fun k ↦
    measurable_pi_apply (k : ℕ)

/-- Extend a finite matrix prefix by zero matrices. The values at and after
`n` are irrelevant to every time-`n` path observable. -/
noncomputable def fixedWidthExtendMatrixPrefix (N n : ℕ) :
    (Fin n → (Fin N → Fin N → ℝ)) → fixedWidthMatrixSampleSpace N :=
  fun u k ↦ if hk : k < n then u ⟨k, hk⟩ else 0

lemma measurable_fixedWidthExtendMatrixPrefix (N n : ℕ) :
    Measurable (fixedWidthExtendMatrixPrefix N n) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k < n
  · simp only [fixedWidthExtendMatrixPrefix, dif_pos hk]
    exact measurable_pi_apply (⟨k, hk⟩ : Fin n)
  · simp only [fixedWidthExtendMatrixPrefix, dif_neg hk]
    exact measurable_const

/-- The selected time-`n` discrepancy direction as an explicit measurable
function of the strict matrix prefix. -/
noncomputable def fixedWidthDiscrepancyDirectionFromPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    (Fin n → (Fin N → Fin N → ℝ)) → (Fin N → ℝ) :=
  fun u ↦ fixedWidthUnitDirection hN
    (fixedWidthVectorDiscrepancy ρ N x0 n
      (fixedWidthExtendMatrixPrefix N n u))

lemma measurable_fixedWidthDiscrepancyDirectionFromPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthDiscrepancyDirectionFromPrefix hN ρ x0 n) :=
  (measurable_fixedWidthUnitDirection hN).comp
    ((measurable_fixedWidthVectorDiscrepancy ρ N x0 n).comp
      (measurable_fixedWidthExtendMatrixPrefix N n))

lemma fixedWidthDiscrepancyDirectionFromPrefix_apply
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthDiscrepancyDirectionFromPrefix hN ρ x0 n
        (fixedWidthMatrixPrefix N n ω) =
      fixedWidthUnitDirection hN
        (fixedWidthVectorDiscrepancy ρ N x0 n ω) := by
  unfold fixedWidthDiscrepancyDirectionFromPrefix
  apply fixedWidthDiscrepancyDirection_eq_of_forall_lt hN ρ x0 n
  intro k hk
  simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix, hk]

end AbsorptionCutoff
