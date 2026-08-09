/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Finite sums of independent real Gaussians

The reusable heart of the Gaussian isotropy step of `prop:gaussian-tv-reduction`: a finite
sum of independent real Gaussian variables is again Gaussian, with the means and variances
added. Filling the Mathlib gap (only the two-variable `gaussianReal_add_gaussianReal_of_indepFun`
is provided upstream).
-/

open MeasureTheory ProbabilityTheory BigOperators

namespace AbsorptionCutoff

/-- **Law of a finite sum of independent real Gaussians.** If `(Xᵢ)` are independent
(`iIndepFun`) with `Xᵢ ∼ 𝒩(mᵢ, vᵢ)`, then `∑_{i∈s} Xᵢ ∼ 𝒩(∑_{i∈s} mᵢ, ∑_{i∈s} vᵢ)`.
Induction on `s` via the two-variable `gaussianReal_add_gaussianReal_of_indepFun`, with the
partial-sum ⊥ next-term independence from `iIndepFun.indepFun_finsetSum_of_notMem`. -/
lemma map_finsetSum_gaussianReal {ι Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ι → Ω → ℝ} {m : ι → ℝ} {v : ι → NNReal}
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, μ.map (X i) = gaussianReal (m i) (v i)) (s : Finset ι) :
    μ.map (∑ i ∈ s, X i) = gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty, gaussianReal_zero_var]
      rw [show (0 : Ω → ℝ) = fun _ => (0 : ℝ) from rfl, Measure.map_const]
      simp
  | insert i s hi ih =>
      have hstep : IndepFun (X i) (∑ j ∈ s, X j) μ :=
        (hindep.indepFun_finsetSum_of_notMem hmeas hi).symm
      simp only [Finset.sum_insert hi]
      rw [gaussianReal_add_gaussianReal_of_indepFun hstep (hlaw i) ih]

/-- **Gaussian linear combination over a product measure.** Under the standard product
`⊗ᵢ 𝒩(0, v)` on `Fin N → ℝ`, the linear form `w ↦ ∑ⱼ wⱼ xⱼ` is `𝒩(0, (∑ⱼ xⱼ²)·v)`. This
is the scalar Gaussian isotropy identity: a linear image of an i.i.d. centered Gaussian
vector has variance `‖x‖²·v`. -/
lemma map_sum_mul_gaussianPi {N : ℕ} (v : NNReal) (x : Fin N → ℝ) :
    (Measure.pi (fun _ : Fin N => gaussianReal 0 v)).map (fun w => ∑ j, w j * x j)
      = gaussianReal 0 ((∑ j, (x j) ^ 2).toNNReal * v) := by
  set μ := Measure.pi (fun _ : Fin N => gaussianReal 0 v) with hμ
  have hindep : iIndepFun (fun (j : Fin N) (w : Fin N → ℝ) => w j * x j) μ :=
    iIndepFun_pi (fun j => (by fun_prop : Measurable (fun t : ℝ => t * x j)).aemeasurable)
  have hmeas : ∀ j : Fin N, Measurable (fun w : Fin N → ℝ => w j * x j) := by
    intro j; fun_prop
  have hlaw : ∀ j : Fin N, μ.map (fun w : Fin N → ℝ => w j * x j)
      = gaussianReal 0 (((x j) ^ 2).toNNReal * v) := by
    intro j
    have hmarg : μ.map (fun w : Fin N → ℝ => w j) = gaussianReal 0 v := by
      rw [hμ, Measure.pi_map_eval]; simp
    rw [show (fun w : Fin N → ℝ => w j * x j)
        = (fun t : ℝ => t * x j) ∘ (fun w => w j) from rfl,
      ← Measure.map_map (by fun_prop : Measurable (fun t : ℝ => t * x j))
        (measurable_pi_apply j), hmarg, gaussianReal_map_mul_const, mul_zero,
      ← Real.toNNReal_of_nonneg (sq_nonneg (x j))]
  have hsum := map_finsetSum_gaussianReal hindep hmeas hlaw (Finset.univ : Finset (Fin N))
  have hfun : (fun w : Fin N → ℝ => ∑ j, w j * x j)
      = ∑ j : Fin N, (fun w : Fin N → ℝ => w j * x j) := by
    funext w; simp [Finset.sum_apply]
  rw [hfun, hsum, Finset.sum_const_zero, ← Finset.sum_mul,
    ← Real.toNNReal_sum_of_nonneg (fun j _ => sq_nonneg (x j))]

end AbsorptionCutoff
