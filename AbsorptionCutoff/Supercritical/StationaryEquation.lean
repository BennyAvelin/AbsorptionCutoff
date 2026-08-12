/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.GaussianRadial
import AbsorptionCutoff.Supercritical.InvariantSelection
import AbsorptionCutoff.Supercritical.Renewal

/-!
# The `N`-dimensional supercritical stationary equation (§7)

This module begins the formalization of the paper's §7, the fixed-dimensional
stationary law of the supercritical unrounded vector chain. In log-polar
coordinates the stationary equation becomes a Markov additive renewal problem;
exponential tilting at the Cramér root identifies the power-law exponent.

The first ingredient is the Gaussian transfer operator's spectral radius, which
by isotropy collapses to the scalar negative moment
`ℳ_{A,N}(β) = 𝔼‖(A/√N) G‖₂^{-β}` (paper `eq:nd-gaussian-negative-moment`). This
file proves its exact Gamma-function closed form, reusing the negative-moment
calculation from `AbsorptionCutoff.Supercritical.GaussianRadial`.
-/

open MeasureTheory ProbabilityTheory BigOperators Filter Topology Set
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- The Gaussian transfer-operator spectral radius `ℳ_{A,N}(β)` from the paper's
log-polar renewal analysis (paper `eq:nd-transfer-rank-one`,
`eq:nd-gaussian-negative-moment`). By isotropy the rank-one transfer operator
`ℒ_{A,N,β}` reduces to this scalar negative moment of the one-step radial
multiplier `ℓ_{A,N} = (A/√N) χ_N`, i.e. `𝔼‖(A/√N) G‖₂^{-β}`. -/
noncomputable def gaussianTransferMoment (A : ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  ∫ g, ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-β) ∂gaussianVec N

/-- Exact Gamma-function closed form of the Gaussian transfer moment
(paper `eq:nd-gaussian-negative-moment`): for `0 < A` and `β < N`,
`ℳ_{A,N}(β) = (√N/A)^β · (1/2)^{β/2} · Γ((N-β)/2) / Γ(N/2)`. -/
lemma gaussianTransferMoment_eq {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {β : ℝ} (hβ : β < N) :
    gaussianTransferMoment A N β =
      (Real.sqrt N / A) ^ β *
        ((1 / 2 : ℝ) ^ (β / 2) * Real.Gamma (((N : ℝ) - β) / 2) /
          Real.Gamma ((N : ℝ) / 2)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- Split the scaled power into the constant factor and the bare norm power.
  have hsplit : gaussianTransferMoment A N β =
      (A / Real.sqrt N) ^ (-β) *
        ∫ g, (gaussianEuclideanNorm N g) ^ (-β) ∂gaussianVec N := by
    unfold gaussianTransferMoment
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have hnorm : 0 ≤ gaussianEuclideanNorm N g := by
      unfold gaussianEuclideanNorm; positivity
    have hconst : 0 ≤ A / Real.sqrt N := by positivity
    exact Real.mul_rpow hconst hnorm
  rw [hsplit, integral_neg_rpow_gaussianEuclideanNorm hN hβ]
  -- Convert the constant factor `(A/√N)^{-β}` into `(√N/A)^β`.
  congr 1
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity),
    inv_div]

/-- The same Gaussian transfer moment in the exact factorization used in the
statement of `thm:nd-power-singularity:intro`. -/
lemma gaussianTransferMoment_eq_paper {A : ℝ} (hA : 0 < A)
    {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : β < N) :
    gaussianTransferMoment A N β =
      A ^ (-β) * (N : ℝ) ^ (β / 2) * 2 ^ (-β / 2) *
        Real.Gamma (((N : ℝ) - β) / 2) / Real.Gamma ((N : ℝ) / 2) := by
  rw [gaussianTransferMoment_eq hA hN hβ]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  rw [Real.div_rpow hsqrt hA.le, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hNR.le, Real.rpow_neg hA.le,
    show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (2 ^ (β / 2))⁻¹ = (2 : ℝ) ^ (-β / 2) by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring]
  ring

/-- Pressure scaling of the transfer spectral radius (paper
`eq:nd-pressure-scaling`): the amplitude `A` enters only through the prefactor
`A^{-β}`, so `r_{A,N}(β) = ℳ_{A,N}(β) = A^{-β} · ℳ_{1,N}(β)`. -/
lemma gaussianTransferMoment_scaling {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {β : ℝ} (hβ : β < N) :
    gaussianTransferMoment A N β = A ^ (-β) * gaussianTransferMoment 1 N β := by
  rw [gaussianTransferMoment_eq hA hN hβ, gaussianTransferMoment_eq one_pos hN hβ,
    div_one, ← mul_assoc]
  congr 1
  rw [Real.div_rpow (Real.sqrt_nonneg _) hA.le, Real.rpow_neg hA.le]
  ring

/-- Logarithm of the transfer moment, the paper's cumulant/pressure function
`F(β) = log ℳ_{A,N}(β)` whose zero locates the Cramér exponent. From the closed
form (`gaussianTransferMoment_eq`),
`log ℳ_{A,N}(β) = β log(√N/A) − (β/2) log 2 + log Γ((N−β)/2) − log Γ(N/2)`. -/
lemma log_gaussianTransferMoment_eq {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {β : ℝ} (hβ : β < N) :
    Real.log (gaussianTransferMoment A N β) =
      β * Real.log (Real.sqrt N / A) - β / 2 * Real.log 2
        + Real.log (Real.Gamma (((N : ℝ) - β) / 2))
        - Real.log (Real.Gamma ((N : ℝ) / 2)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsa : 0 < Real.sqrt N / A := div_pos (Real.sqrt_pos.mpr hNpos) hA
  have hg1 : 0 < Real.Gamma (((N : ℝ) - β) / 2) :=
    Real.Gamma_pos_of_pos (by linarith)
  have hg2 : 0 < Real.Gamma ((N : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [gaussianTransferMoment_eq hA hN hβ,
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hsa,
    Real.log_div (by positivity) hg2.ne',
    Real.log_mul (by positivity) hg1.ne',
    Real.log_rpow (by norm_num : (0 : ℝ) < 1 / 2),
    show Real.log (1 / 2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]]
  ring

/-- Left endpoint of the pressure: `ℳ_{A,N}(0) = 1`, so `F(0) = log ℳ_{A,N}(0) = 0`
(paper proof of `lem:nd-gaussian-cramer-exponent`). The integrand collapses to the
constant `1` over the Gaussian probability measure. -/
lemma gaussianTransferMoment_zero (A : ℝ) (N : ℕ) :
    gaussianTransferMoment A N 0 = 1 := by
  unfold gaussianTransferMoment
  simp [neg_zero, Real.rpow_zero, integral_const]

/-- The Euclidean norm of a Gaussian vector is a.e. positive (for `0 < N`): the
zero vector is the only null point of the norm, and it lies in a single-coordinate
fibre that the product Gaussian gives measure zero (marginal is atomless). This is
the prerequisite for identifying `gaussianTransferMoment` with a moment-generating
function of `−log‖(A/√N)G‖`. -/
lemma ae_gaussianEuclideanNorm_pos {N : ℕ} (hN : 0 < N) :
    ∀ᵐ g ∂gaussianVec N, 0 < gaussianEuclideanNorm N g := by
  haveI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hbad : gaussianVec N {g : Fin N → ℝ | gaussianEuclideanNorm N g = 0} = 0 := by
    refine measure_mono_null (t := Function.eval (⟨0, hN⟩ : Fin N) ⁻¹' {0}) ?_ ?_
    · intro g hg
      simp only [Set.mem_setOf_eq] at hg
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.eval]
      unfold gaussianEuclideanNorm at hg
      have hs : gaussianSquaredNorm N g = 0 :=
        (Real.sqrt_eq_zero (gaussianSquaredNorm_nonneg N g)).mp hg
      unfold gaussianSquaredNorm at hs
      have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (g j))).mp hs
        (⟨0, hN⟩ : Fin N) (Finset.mem_univ _)
      exact pow_eq_zero_iff (by norm_num) |>.mp hj
    · unfold gaussianVec
      rw [(measurePreserving_eval (fun _ => gaussianReal 0 1)
            (⟨0, hN⟩ : Fin N)).measure_preimage
          (measurableSet_singleton (0 : ℝ)).nullMeasurableSet]
      exact measure_singleton _
  rw [ae_iff]
  refine measure_mono_null ?_ hbad
  intro g hg
  simp only [Set.mem_setOf_eq, not_lt] at hg ⊢
  exact le_antisymm hg (by unfold gaussianEuclideanNorm; positivity)

/-- The transfer moment is the moment-generating function of the log-radial
increment `X = −log‖(A/√N)G‖` (paper §7, tilting at the Cramér root): for `0<A`,
`0<N`, `ℳ_{A,N}(β) = 𝔼[e^{βX}] = mgf X (gaussianVec N) β`. Consequently the
pressure `F(β) = log ℳ_{A,N}(β)` is the cumulant generating function `cgf X`,
whose strict convexity (tilted-variance positivity) drives the Cramér-exponent
argument. -/
lemma gaussianTransferMoment_eq_mgf {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (β : ℝ) :
    gaussianTransferMoment A N β =
      mgf (fun g => -Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g))
        (gaussianVec N) β := by
  unfold gaussianTransferMoment ProbabilityTheory.mgf
  refine integral_congr_ae ?_
  filter_upwards [ae_gaussianEuclideanNorm_pos hN] with g hg
  have hr : 0 < (A / Real.sqrt N) * gaussianEuclideanNorm N g :=
    mul_pos (div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))) hg
  rw [Real.rpow_def_of_pos hr]
  congr 1
  ring

/-- Negative-power integrability under the Gamma law: for `p < a`, `0 < a`,
`0 < r`, `x ↦ x^{-p}` is integrable against `gammaMeasure a r`. The value is the
Gamma quotient already computed in `GaussianRadial`; this is the companion
integrability statement (an integral value alone does not entail integrability). -/
lemma integrable_neg_rpow_gammaMeasure {a r p : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hp : p < a) :
    Integrable (fun x => x ^ (-p)) (gammaMeasure a r) := by
  have hbase :
      IntegrableOn (fun x : ℝ => x ^ (a - p - 1) * Real.exp (-(r * x))) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := a - p - 1) (b := r) (by linarith) le_rfl hr
  have hInt : IntegrableOn
      (fun x : ℝ => r ^ a / Real.Gamma a * (x ^ (a - p - 1) * Real.exp (-(r * x))))
      (Ioi 0) := hbase.const_mul _
  rw [gammaMeasure]
  change Integrable (fun x => x ^ (-p))
    (volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff (measurable_gammaPDFReal a r).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  -- The density-weighted integrand agrees a.e. with the `Ioi 0` indicator of the
  -- integrable base (they differ only at the null point `0`).
  refine (hInt.integrable_indicator measurableSet_Ioi).congr ?_
  have hnull : volume ({(0 : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null ?_ hnull
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  by_contra hx0
  simp only [Set.mem_singleton_iff] at hx0
  apply hx
  rcases lt_or_gt_of_ne hx0 with h | h
  · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; linarith),
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x),
      gammaPDFReal, if_neg (not_le.mpr h)]
    ring
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h),
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x),
      gammaPDFReal, if_pos h.le]
    have hx1 : x ^ (a - p - 1) = x ^ (a - 1) * x ^ (-p) := by
      rw [← Real.rpow_add h]; congr 1; ring
    rw [hx1]; ring

/-- Negative-power integrability of the Gaussian Euclidean norm: for `t < N`,
`g ↦ ‖g‖^{-t}` is integrable against `gaussianVec N`. Equivalently, every
`t ∈ (−N, N)` lies in the interior of the increment's `integrableExpSet`, so the
pressure `F = cgf X` is analytic there. -/
lemma integrable_neg_rpow_gaussianEuclideanNorm {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : t < N) :
    Integrable (fun g => (gaussianEuclideanNorm N g) ^ (-t)) (gaussianVec N) := by
  have hfun : (fun g => (gaussianEuclideanNorm N g) ^ (-t)) =
      (fun g => (gaussianSquaredNorm N g) ^ (-(t / 2))) := by
    funext g
    rw [gaussianEuclideanNorm, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (gaussianSquaredNorm_nonneg N g)]
    congr 1
    ring
  rw [hfun]
  have hmap : Integrable (fun x : ℝ => x ^ (-(t / 2)))
      (gammaMeasure ((N : ℝ) / 2) (1 / 2)) :=
    integrable_neg_rpow_gammaMeasure (by positivity) (by norm_num)
      (by have : (t : ℝ) < N := ht; linarith)
  rw [← map_gaussianSquaredNorm_eq_gammaMeasure hN] at hmap
  exact (integrable_map_measure (by fun_prop)
    (measurable_gaussianSquaredNorm N).aemeasurable).mp hmap

/-- The log-radial increment `X_{A,N}(g) = −log‖(A/√N) g‖` of paper §7. Under
`gaussianVec N` it is the summand of the additive renewal walk; the transfer
moment `ℳ_{A,N}` is its moment-generating function
(`gaussianTransferMoment_eq_mgf`) and the pressure `F` is its `cgf`. -/
noncomputable def logRadialIncrement (A : ℝ) (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  -Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g)

/-- Every `t ∈ (−N, N)` lies in the increment's `integrableExpSet`: with
`X = logRadialIncrement A N`, the map `g ↦ e^{t · X g}` is integrable against
`gaussianVec N`. Indeed `e^{t·X g} = ((A/√N)‖g‖)^{−t}` a.e., which splits into a
constant times `‖g‖^{−t}` and is integrable by
`integrable_neg_rpow_gaussianEuclideanNorm` whenever `t < N`. Since `(−N, N)` is
open, `0` and every point of `(0, N)` are interior to `integrableExpSet`, so the
cgf machinery (`deriv_cgf`, `iteratedDeriv_two_cgf`) applies there. -/
lemma Ioo_subset_integrableExpSet_logRadialIncrement {A : ℝ} (hA : 0 < A)
    {N : ℕ} (hN : 0 < N) :
    Set.Ioo (-(N : ℝ)) (N : ℝ) ⊆
      integrableExpSet (logRadialIncrement A N) (gaussianVec N) := by
  intro t ht
  -- `e^{t·X}` is a.e. equal to the negative power `((A/√N)‖g‖)^{−t}`.
  change Integrable (fun g => Real.exp (t * logRadialIncrement A N g)) (gaussianVec N)
  have key : Integrable
      (fun g => ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-t))
      (gaussianVec N) := by
    have he : (fun g => ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-t)) =
        (fun g => (A / Real.sqrt N) ^ (-t) * (gaussianEuclideanNorm N g) ^ (-t)) := by
      funext g
      exact Real.mul_rpow (by positivity) (by unfold gaussianEuclideanNorm; positivity)
    rw [he]
    exact (integrable_neg_rpow_gaussianEuclideanNorm hN ht.2).const_mul _
  refine key.congr ?_
  filter_upwards [ae_gaussianEuclideanNorm_pos hN] with g hg
  have hr : 0 < (A / Real.sqrt N) * gaussianEuclideanNorm N g :=
    mul_pos (div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))) hg
  rw [Real.rpow_def_of_pos hr]
  congr 1
  unfold logRadialIncrement
  ring

/-- Nondegeneracy of the squared Gaussian norm (for `0 < N`): it is not a.e.
equal to any constant `c`. Its law is `gammaMeasure (N/2) (1/2)`, which is
absolutely continuous with respect to Lebesgue measure and hence assigns zero
mass to every singleton; if the norm were a.e. `c`, that fibre would carry full
mass. This is the source of strict positivity of the pressure's tilted variance
(and hence of strict convexity). -/
lemma gaussianSquaredNorm_not_ae_const {N : ℕ} (hN : 0 < N) (c : ℝ) :
    ¬ (∀ᵐ g ∂gaussianVec N, gaussianSquaredNorm N g = c) := by
  intro h
  -- The fibre `{gaussianSquaredNorm = c}` carries full mass under `gaussianVec N`.
  have hnull : gaussianVec N (gaussianSquaredNorm N ⁻¹' {c})ᶜ = 0 := by
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro g hg
    simpa using hg
  have hfull : gaussianVec N (gaussianSquaredNorm N ⁻¹' {c}) = 1 :=
    (prob_compl_eq_zero_iff
      ((measurable_gaussianSquaredNorm N) (measurableSet_singleton c))).mp hnull
  -- Pushing forward to the Gamma law, the singleton `{c}` would then carry full
  -- mass, contradicting its absolute continuity with respect to Lebesgue.
  have hmapc : (gammaMeasure ((N : ℝ) / 2) (1 / 2)) {c} = 1 := by
    rw [← map_gaussianSquaredNorm_eq_gammaMeasure hN,
      Measure.map_apply (measurable_gaussianSquaredNorm N) (measurableSet_singleton c)]
    exact hfull
  have hzero : (gammaMeasure ((N : ℝ) / 2) (1 / 2)) {c} = 0 := by
    have hac : gammaMeasure ((N : ℝ) / 2) (1 / 2) ≪ volume := by
      rw [gammaMeasure]
      exact withDensity_absolutelyContinuous _ _
    exact hac Real.volume_singleton
  rw [hzero] at hmapc
  exact one_ne_zero hmapc.symm

/-- Strict positivity of the second derivative of a cumulant generating function
at an interior point, provided the variable is not a.e. constant. By
`iteratedDeriv_two_cgf_eq_integral` the second derivative is the tilted variance
`𝔼[(X − F'(v))² e^{vX}] / mgf`; the integrand is nonnegative and its integral is
strictly positive exactly when `X` is not a.e. equal to `F'(v)`. This is the
analytic engine behind strict convexity of the pressure. -/
lemma iteratedDeriv_two_cgf_pos_of_not_ae_const {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {v : ℝ}
    (hv : v ∈ interior (integrableExpSet X μ))
    (hne : ¬ (∀ᵐ g ∂μ, X g = deriv (cgf X μ) v)) :
    0 < iteratedDeriv 2 (cgf X μ) v := by
  set c := deriv (cgf X μ) v with hc
  rw [iteratedDeriv_two_cgf_eq_integral hv]
  have hmgf : 0 < mgf X μ v :=
    mgf_pos (interior_subset (s := integrableExpSet X μ) hv)
  apply div_pos _ hmgf
  set f := fun g => (X g - c) ^ 2 * Real.exp (v * X g) with hf
  have hf_nonneg : 0 ≤ f := by intro g; positivity
  have hf_int : Integrable f μ := by
    have e : f = (fun g => X g ^ 2 * Real.exp (v * X g)
          - 2 * c * (X g ^ 1 * Real.exp (v * X g))
          + c ^ 2 * (X g ^ 0 * Real.exp (v * X g))) := by funext g; simp only [hf]; ring
    rw [e]
    exact ((integrable_pow_mul_exp_of_mem_interior_integrableExpSet hv 2).sub
        ((integrable_pow_mul_exp_of_mem_interior_integrableExpSet hv 1).const_mul (2 * c))).add
      ((integrable_pow_mul_exp_of_mem_interior_integrableExpSet hv 0).const_mul (c ^ 2))
  rw [integral_pos_iff_support_of_nonneg hf_nonneg hf_int]
  have hsupp : Function.support f = {g | X g ≠ c} := by
    ext g
    simp only [Function.mem_support, hf, Set.mem_setOf_eq, ne_eq, mul_eq_zero,
      Real.exp_ne_zero, or_false]
    rw [pow_eq_zero_iff (two_ne_zero), sub_eq_zero]
  rw [hsupp, pos_iff_ne_zero]
  rwa [ae_iff] at hne

/-- Positivity of the pressure's second derivative at every interior tilt: the
tilted variance of the log-radial increment `X = logRadialIncrement A N` is
strictly positive because `X` is not a.e. constant (a.e.-constancy of `X` would
force `‖G‖²` to be a.e. constant, contradicting
`gaussianSquaredNorm_not_ae_const`). This is the analytic core shared by the
`(0,N)` and `[0,N)` strict-convexity statements. -/
lemma iteratedDeriv_two_cgf_logRadialIncrement_pos {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) {x : ℝ}
    (hx : x ∈ interior (integrableExpSet (logRadialIncrement A N) (gaussianVec N))) :
    0 < iteratedDeriv 2 (cgf (logRadialIncrement A N) (gaussianVec N)) x := by
  refine iteratedDeriv_two_cgf_pos_of_not_ae_const hx ?_
  -- `X` is not a.e. equal to `F'(x)`: a.e.-constancy would make the squared norm
  -- a.e. constant, contradicting `gaussianSquaredNorm_not_ae_const`.
  intro hXc
  refine gaussianSquaredNorm_not_ae_const hN
    ((Real.exp (-(deriv (cgf (logRadialIncrement A N) (gaussianVec N)) x))) ^ 2
      / (A / Real.sqrt N) ^ 2) ?_
  filter_upwards [hXc, ae_gaussianEuclideanNorm_pos hN] with g hgX hgpos
  have hk : 0 < A / Real.sqrt N :=
    div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))
  have hlog : Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g)
      = -(deriv (cgf (logRadialIncrement A N) (gaussianVec N)) x) := by
    have h : -Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g)
        = deriv (cgf (logRadialIncrement A N) (gaussianVec N)) x := hgX
    linarith
  have hval : (A / Real.sqrt N) * gaussianEuclideanNorm N g
      = Real.exp (-(deriv (cgf (logRadialIncrement A N) (gaussianVec N)) x)) := by
    rw [← hlog, Real.exp_log (mul_pos hk hgpos)]
  have hsq : gaussianSquaredNorm N g = (gaussianEuclideanNorm N g) ^ 2 := by
    unfold gaussianEuclideanNorm
    rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
  rw [hsq, eq_div_iff (by positivity)]
  have hval2 : ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ 2
      = (Real.exp (-(deriv (cgf (logRadialIncrement A N) (gaussianVec N)) x))) ^ 2 := by
    rw [hval]
  rw [mul_pow] at hval2
  rw [mul_comm (gaussianEuclideanNorm N g ^ 2)]
  exact hval2

/-- Strict convexity of the pressure `F = cgf X` on `(0, N)`
(`lem:nd-gaussian-cramer-exponent`, the convexity half): the log-radial
increment `X = logRadialIncrement A N` has strictly positive tilted variance at
every interior tilt, because it is not a.e. constant
(`gaussianSquaredNorm_not_ae_const`). Combined with continuity from
`analyticOn_cgf`, `strictConvexOn_of_deriv2_pos` yields strict convexity. This is
what forces the Cramér root `β_{A,N}` to be unique. -/
lemma strictConvexOn_cgf_logRadialIncrement {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) :
    StrictConvexOn ℝ (Set.Ioo (0 : ℝ) (N : ℝ))
      (cgf (logRadialIncrement A N) (gaussianVec N)) := by
  -- `(0, N)` sits inside the interior of the increment's `integrableExpSet`.
  have hsub : Set.Ioo (0 : ℝ) (N : ℝ) ⊆
      interior (integrableExpSet (logRadialIncrement A N) (gaussianVec N)) := by
    have h1 : Set.Ioo (0 : ℝ) (N : ℝ) ⊆ Set.Ioo (-(N : ℝ)) (N : ℝ) := by
      intro x hx
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      exact ⟨by linarith [hx.1], hx.2⟩
    exact h1.trans (interior_maximal
      (Ioo_subset_integrableExpSet_logRadialIncrement hA hN) isOpen_Ioo)
  refine strictConvexOn_of_deriv2_pos (convex_Ioo _ _)
    ((analyticOn_cgf.mono hsub).continuousOn) ?_
  intro x hx
  rw [interior_Ioo] at hx
  rw [← iteratedDeriv_eq_iterate]
  exact iteratedDeriv_two_cgf_logRadialIncrement_pos hA hN (hsub hx)

/-- Strict convexity of the pressure on the half-open interval `[0, N)`. The
Cramér-root uniqueness argument compares an interior root against the left
endpoint `F(0) = 0`, so the domain must contain `0`; the second-derivative
criterion still applies because `[0,N)` has interior `(0,N)`. -/
lemma strictConvexOn_cgf_logRadialIncrement_Ico {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) :
    StrictConvexOn ℝ (Set.Ico (0 : ℝ) (N : ℝ))
      (cgf (logRadialIncrement A N) (gaussianVec N)) := by
  have hsub : Set.Ico (0 : ℝ) (N : ℝ) ⊆
      interior (integrableExpSet (logRadialIncrement A N) (gaussianVec N)) := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : Set.Ico (0 : ℝ) (N : ℝ) ⊆ Set.Ioo (-(N : ℝ)) (N : ℝ) :=
      fun x hx => ⟨by linarith [hx.1], hx.2⟩
    exact h1.trans (interior_maximal
      (Ioo_subset_integrableExpSet_logRadialIncrement hA hN) isOpen_Ioo)
  refine strictConvexOn_of_deriv2_pos (convex_Ico _ _)
    ((analyticOn_cgf.mono hsub).continuousOn) ?_
  intro x hx
  rw [interior_Ico] at hx
  rw [← iteratedDeriv_eq_iterate]
  exact iteratedDeriv_two_cgf_logRadialIncrement_pos hA hN
    (hsub (Set.Ioo_subset_Ico_self hx))

/-- The mean log-radial multiplier `𝔼 log ℓ_{A,N} = 𝔼 log‖(A/√N) G‖` of paper
§7. By `eq:fixed-width-critical` the supercriticality condition `A > A_c(N)` is
equivalent to `0 < logRadialDrift A N`. -/
noncomputable def logRadialDrift (A : ℝ) (N : ℕ) : ℝ :=
  ∫ g, Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ∂gaussianVec N

/-- Fixed-dimension supercriticality (the paper's `A > A_c(N)`,
`eq:fixed-width-critical`): the log-radial multiplier has positive drift. This
is equivalent to the paper's digamma-based condition, and is adopted as the
working hypothesis for the stationary theory (Mathlib has no digamma function). -/
def Supercritical (A : ℝ) (N : ℕ) : Prop := 0 < logRadialDrift A N

/-- The origin is interior to the increment's `integrableExpSet`: it lies in the
open interval `(−N, N) ⊆ integrableExpSet` (unit 3d-mem), since `−N < 0 < N`. -/
lemma zero_mem_interior_integrableExpSet_logRadialIncrement {A : ℝ} (hA : 0 < A)
    {N : ℕ} (hN : 0 < N) :
    (0 : ℝ) ∈
      interior (integrableExpSet (logRadialIncrement A N) (gaussianVec N)) := by
  refine interior_maximal
    (Ioo_subset_integrableExpSet_logRadialIncrement hA hN) isOpen_Ioo ?_
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact ⟨by linarith, hNpos⟩

/-- The pressure's derivative at the origin is minus the drift:
`F'(0) = 𝔼[X] = −𝔼 log ℓ_{A,N}` (paper, in the proof of
`lem:nd-gaussian-cramer-exponent`). Via `deriv_cgf_zero` (the mean of the
increment, the total mass being one) and `integral_neg`; no integrability of
`log ℓ` is required, as the negation pulls through the integral unconditionally. -/
lemma deriv_cgf_logRadialIncrement_zero {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    deriv (cgf (logRadialIncrement A N) (gaussianVec N)) 0 = -logRadialDrift A N := by
  rw [deriv_cgf_zero (zero_mem_interior_integrableExpSet_logRadialIncrement hA hN),
    probReal_univ, div_one]
  unfold logRadialIncrement logRadialDrift
  exact integral_neg _

/-- Supercriticality is exactly the sign condition `F'(0) < 0` demanded by the
Cramér-exponent IVT (paper: `A > A_c ⟺ 𝔼 log ℓ > 0 ⟺ F'(0) < 0`). -/
lemma deriv_cgf_logRadialIncrement_zero_neg_iff {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) :
    deriv (cgf (logRadialIncrement A N) (gaussianVec N)) 0 < 0 ↔ Supercritical A N := by
  unfold Supercritical
  rw [deriv_cgf_logRadialIncrement_zero hA hN, neg_lt_zero]

/-- The real Gamma function blows up at the origin from the right:
`Γ(z) → +∞` as `z → 0⁺`. This is the analytic engine for the right-endpoint
divergence of the transfer moment (`ℳ_{A,N}(β) → ∞` as `β ↑ N`, since
`(N−β)/2 → 0⁺`). Proof via the functional equation `Γ(z) = Γ(z+1)/z`: the
numerator tends to `Γ(1) = 1` and the reciprocal `z⁻¹ → +∞`. -/
lemma tendsto_gamma_atTop_nhdsGT_zero :
    Tendsto (fun z : ℝ => Real.Gamma z) (𝓝[>] (0 : ℝ)) atTop := by
  have hcontGamma : ContinuousAt Real.Gamma 1 :=
    (Real.differentiableAt_Gamma
      (fun m => by intro h; linarith [Nat.cast_nonneg (α := ℝ) m])).continuousAt
  have htend : Tendsto (fun z : ℝ => z + 1) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h0 : Tendsto (fun z : ℝ => z + 1) (𝓝 (0 : ℝ)) (𝓝 1) :=
      (continuous_id.add continuous_const).tendsto' 0 1 (by norm_num)
    exact h0.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun z : ℝ => Real.Gamma (z + 1)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [Real.Gamma_one, Function.comp_def] using hcontGamma.tendsto.comp htend
  have key : Tendsto (fun z : ℝ => Real.Gamma (z + 1) * z⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    hnum.pos_mul_atTop one_pos tendsto_inv_nhdsGT_zero
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  rw [Real.Gamma_add_one hz0, mul_comm z (Real.Gamma z), mul_assoc,
    mul_inv_cancel₀ hz0, mul_one]

/-- Right-endpoint divergence of the transfer moment: `ℳ_{A,N}(β) → +∞` as
`β ↑ N` (paper §7, the right end of the Cramér-exponent interval). From the
Gamma closed form (`gaussianTransferMoment_eq`), the prefactor
`(√N/A)^β (1/2)^{β/2} / Γ(N/2)` converges to a positive constant while
`Γ((N−β)/2) → +∞` because `(N−β)/2 → 0⁺` (`tendsto_gamma_atTop_nhdsGT_zero`). -/
lemma gaussianTransferMoment_tendsto_atTop {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) :
    Tendsto (fun β => gaussianTransferMoment A N β) (𝓝[<] (N : ℝ)) atTop := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : 0 < Real.sqrt N / A := div_pos (Real.sqrt_pos.mpr hNR) hA
  have hGammaN : 0 < Real.Gamma ((N : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  -- The prefactor converges to a positive constant.
  have hC : Tendsto
      (fun β : ℝ => (Real.sqrt N / A) ^ β * (1 / 2 : ℝ) ^ (β / 2)
        / Real.Gamma ((N : ℝ) / 2))
      (𝓝[<] (N : ℝ))
      (𝓝 ((Real.sqrt N / A) ^ (N : ℝ) * (1 / 2 : ℝ) ^ ((N : ℝ) / 2)
        / Real.Gamma ((N : ℝ) / 2))) := by
    apply Tendsto.div_const
    apply Tendsto.mul
    · exact (Real.continuousAt_const_rpow (ne_of_gt hsq)).tendsto.mono_left nhdsWithin_le_nhds
    · have h2 : Tendsto (fun β : ℝ => β / 2) (𝓝[<] (N : ℝ)) (𝓝 ((N : ℝ) / 2)) :=
        ((continuous_id.div_const 2).tendsto _).mono_left nhdsWithin_le_nhds
      exact (Real.continuousAt_const_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)).tendsto.comp h2
  have hL_pos : 0 < (Real.sqrt N / A) ^ (N : ℝ) * (1 / 2 : ℝ) ^ ((N : ℝ) / 2)
      / Real.Gamma ((N : ℝ) / 2) :=
    div_pos (mul_pos (Real.rpow_pos_of_pos hsq _)
      (Real.rpow_pos_of_pos (by norm_num) _)) hGammaN
  -- The Gamma factor diverges, since its argument tends to `0⁺`.
  have hmap : Tendsto (fun β : ℝ => ((N : ℝ) - β) / 2) (𝓝[<] (N : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun β : ℝ => ((N : ℝ) - β) / 2) (𝓝 (N : ℝ))
          (𝓝 (((N : ℝ) - N) / 2)) :=
        ((continuous_const.sub continuous_id).div_const 2).tendsto _
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with β hβ
      simp only [Set.mem_Ioi]
      have hlt : β < N := hβ
      linarith
  have hG : Tendsto (fun β : ℝ => Real.Gamma (((N : ℝ) - β) / 2))
      (𝓝[<] (N : ℝ)) atTop := by
    simpa [Function.comp_def] using tendsto_gamma_atTop_nhdsGT_zero.comp hmap
  have hprod : Tendsto
      (fun β : ℝ => ((Real.sqrt N / A) ^ β * (1 / 2 : ℝ) ^ (β / 2)
          / Real.Gamma ((N : ℝ) / 2)) * Real.Gamma (((N : ℝ) - β) / 2))
      (𝓝[<] (N : ℝ)) atTop :=
    hC.pos_mul_atTop hL_pos hG
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with β hβ
  have hβN : β < N := hβ
  rw [gaussianTransferMoment_eq hA hN hβN]
  ring

/-- Abstract shape of the paper's Cramér-root argument: a strictly convex
function on `[0, b)` vanishing at the left endpoint, with negative derivative
there and blowing up at the right endpoint, has a **unique** zero in `(0, b)`.

Existence is the intermediate value theorem applied between a point where `F`
has dipped below `F 0 = 0` (produced by the negative slope at the origin) and a
point near `b` where `F` is already positive. Uniqueness is strict convexity: if
`0 < γ₁ < γ₂` were two zeros, writing `γ₁` as the strict convex combination
`(1 - γ₁/γ₂) · 0 + (γ₁/γ₂) · γ₂` gives `F γ₁ < 0`, a contradiction. -/
lemma exists_unique_zero_of_strictConvex_deriv_neg (F : ℝ → ℝ) (b c : ℝ) (hb : 0 < b)
    (hconvex : StrictConvexOn ℝ (Set.Ico 0 b) F) (hcont : ContinuousOn F (Set.Ico 0 b))
    (hF0 : F 0 = 0) (hderiv : HasDerivAt F c 0) (hc : c < 0)
    (htop : Tendsto F (𝓝[<] b) atTop) :
    ∃! β, β ∈ Set.Ioo (0 : ℝ) b ∧ F β = 0 := by
  -- Uniqueness: two distinct zeros contradict strict convexity through `F 0 = 0`.
  have key : ∀ γ₁ ∈ Set.Ioo (0 : ℝ) b, F γ₁ = 0 → ∀ γ₂ ∈ Set.Ioo (0 : ℝ) b, F γ₂ = 0 →
      γ₁ < γ₂ → False := by
    intro γ₁ hγ₁ hFγ₁ γ₂ hγ₂ hFγ₂ hlt
    have hγ₂0 : γ₂ ≠ 0 := ne_of_gt hγ₂.1
    have ht0 : 0 < γ₁ / γ₂ := div_pos hγ₁.1 hγ₂.1
    have ht1 : 0 < 1 - γ₁ / γ₂ := by
      have : γ₁ / γ₂ < 1 := (div_lt_one hγ₂.1).mpr hlt
      linarith
    have hcomb := hconvex.2 (⟨le_refl _, hb⟩ : (0 : ℝ) ∈ Set.Ico 0 b)
      (⟨le_of_lt hγ₂.1, hγ₂.2⟩ : γ₂ ∈ Set.Ico 0 b) (ne_of_lt hγ₂.1) ht1 ht0 (by ring)
    rw [hF0, hFγ₂] at hcomb
    simp only [smul_eq_mul, mul_zero, add_zero, zero_add] at hcomb
    have harg : γ₁ / γ₂ * γ₂ = γ₁ := by field_simp
    rw [harg, hFγ₁] at hcomb
    exact lt_irrefl 0 hcomb
  have huniq : ∀ γ₁ ∈ Set.Ioo (0 : ℝ) b, F γ₁ = 0 → ∀ γ₂ ∈ Set.Ioo (0 : ℝ) b, F γ₂ = 0 →
      γ₁ = γ₂ := by
    intro γ₁ hγ₁ hFγ₁ γ₂ hγ₂ hFγ₂
    rcases lt_trichotomy γ₁ γ₂ with h | h | h
    · exact (key γ₁ hγ₁ hFγ₁ γ₂ hγ₂ hFγ₂ h).elim
    · exact h
    · exact (key γ₂ hγ₂ hFγ₂ γ₁ hγ₁ hFγ₁ h).elim
  -- The negative slope at the origin produces a point where `F` is negative.
  have hdip : ∃ β₁ ∈ Set.Ioo (0 : ℝ) b, F β₁ < F 0 := by
    have hs : Tendsto (slope F 0) (𝓝[>] (0 : ℝ)) (𝓝 c) :=
      (hasDerivAt_iff_tendsto_slope.mp hderiv).mono_left
        (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    have hev : ∀ᶠ β in 𝓝[>] (0 : ℝ), slope F 0 β < 0 := hs.eventually (eventually_lt_nhds hc)
    have hb' : ∀ᶠ β in 𝓝[>] (0 : ℝ), β < b := (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds
    have hp : ∀ᶠ β in 𝓝[>] (0 : ℝ), (0 : ℝ) < β := eventually_mem_nhdsWithin.mono fun x hx => hx
    obtain ⟨β₁, hsl, hbb, hpp⟩ := (hev.and (hb'.and hp)).exists
    refine ⟨β₁, ⟨hpp, hbb⟩, ?_⟩
    rw [slope_def_field, div_neg_iff] at hsl
    rcases hsl with ⟨_, _⟩ | ⟨_, _⟩ <;> linarith
  obtain ⟨β₁, hβ₁, hFβ₁⟩ := hdip
  rw [hF0] at hFβ₁
  -- Divergence at the right endpoint produces a point where `F` is positive.
  have e1 : ∀ᶠ β in 𝓝[<] b, 0 < F β := htop.eventually (eventually_gt_atTop 0)
  have e2 : ∀ᶠ β in 𝓝[<] b, β₁ < β := (eventually_gt_nhds hβ₁.2).filter_mono nhdsWithin_le_nhds
  have e3 : ∀ᶠ β in 𝓝[<] b, β < b := eventually_mem_nhdsWithin.mono fun x hx => hx
  obtain ⟨β₂, hFβ₂, h12, h2b⟩ := (e1.and (e2.and e3)).exists
  have hsub : Set.Icc β₁ β₂ ⊆ Set.Ico 0 b :=
    fun x hx => ⟨le_trans (le_of_lt hβ₁.1) hx.1, lt_of_le_of_lt hx.2 h2b⟩
  obtain ⟨β, hβ, hFβ⟩ := intermediate_value_Ioo (le_of_lt h12) (hcont.mono hsub) ⟨hFβ₁, hFβ₂⟩
  have hβmem : β ∈ Set.Ioo (0 : ℝ) b := ⟨lt_trans hβ₁.1 hβ.1, lt_trans hβ.2 h2b⟩
  exact ⟨β, ⟨hβmem, hFβ⟩, fun y ⟨hy, hFy⟩ => huniq y hy hFy β hβmem hFβ⟩

/-- **Cramér exponent** (paper `lem:nd-gaussian-cramer-exponent`): in the
supercritical regime `A > A_c(N)` there is a *unique* `β_{A,N} ∈ (0, N)` with
`ℳ_{A,N}(β_{A,N}) = 1`, the exponent driving the power-law singularity of the
stationary law (`thm:nd-power-singularity`).

The proof is the paper's: the pressure `F = log ℳ = cgf X` satisfies `F(0) = 0`,
`F'(0) = -𝔼 log ℓ_{A,N} < 0` (supercriticality), `F(β) → ∞` as `β ↑ N`, and is
strictly convex on `[0, N)`; so it dips below zero and comes back, crossing zero
exactly once. -/
theorem existsUnique_gaussianTransferMoment_eq_one {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) :
    ∃! β, β ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧ gaussianTransferMoment A N β = 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set X := logRadialIncrement A N with hX
  set μ := gaussianVec N with hμ
  set F := cgf X μ with hF
  have hsub : Set.Ico (0 : ℝ) (N : ℝ) ⊆ interior (integrableExpSet X μ) := by
    have h1 : Set.Ico (0 : ℝ) (N : ℝ) ⊆ Set.Ioo (-(N : ℝ)) (N : ℝ) :=
      fun x hx => ⟨by linarith [hx.1], hx.2⟩
    exact h1.trans (interior_maximal
      (Ioo_subset_integrableExpSet_logRadialIncrement hA hN) isOpen_Ioo)
  -- `F` is the logarithm of the transfer moment, which is a positive mgf on `(0,N)`.
  have hmom : ∀ β : ℝ, gaussianTransferMoment A N β = mgf X μ β := fun β =>
    gaussianTransferMoment_eq_mgf hA hN β
  have hmom_pos : ∀ β ∈ Set.Ico (0 : ℝ) (N : ℝ), 0 < gaussianTransferMoment A N β := by
    intro β hβ
    rw [hmom β]
    exact mgf_pos (Ioo_subset_integrableExpSet_logRadialIncrement hA hN
      ⟨by linarith [hβ.1], hβ.2⟩)
  have hFlog : ∀ β : ℝ, F β = Real.log (gaussianTransferMoment A N β) := by
    intro β; rw [hmom β]; rfl
  -- The four hypotheses of the abstract root lemma.
  have hF0 : F 0 = 0 := by rw [hF, cgf_zero', probReal_univ, Real.log_one]
  have hderiv : HasDerivAt F (deriv F 0) 0 :=
    (analyticAt_cgf
      (zero_mem_interior_integrableExpSet_logRadialIncrement hA hN)).differentiableAt.hasDerivAt
  have hc : deriv F 0 < 0 := (deriv_cgf_logRadialIncrement_zero_neg_iff hA hN).mpr hsc
  have htop : Tendsto F (𝓝[<] (N : ℝ)) atTop := by
    have := Real.tendsto_log_atTop.comp (gaussianTransferMoment_tendsto_atTop hA hN)
    exact this.congr fun β => (hFlog β).symm
  obtain ⟨β, ⟨hβmem, hFβ⟩, hβuniq⟩ :=
    exists_unique_zero_of_strictConvex_deriv_neg F (N : ℝ) (deriv F 0) hNpos
      (strictConvexOn_cgf_logRadialIncrement_Ico hA hN)
      ((analyticOn_cgf.mono hsub).continuousOn) hF0 hderiv hc htop
  -- Transfer the zero of `F` to the level set `ℳ = 1` using positivity of `ℳ`.
  have hbridge : ∀ γ ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      (F γ = 0 ↔ gaussianTransferMoment A N γ = 1) := by
    intro γ hγ
    have hpos := hmom_pos γ ⟨le_of_lt hγ.1, hγ.2⟩
    constructor
    · intro h
      have := Real.exp_log hpos
      rw [hFlog γ] at h
      rw [← this, h, Real.exp_zero]
    · intro h; rw [hFlog γ, h, Real.log_one]
  refine ⟨β, ⟨hβmem, (hbridge β hβmem).mp hFβ⟩, ?_⟩
  rintro y ⟨hy, hMy⟩
  exact hβuniq y ⟨hy, (hbridge y hy).mpr hMy⟩

/-- The **Gaussian Cramér exponent** `β_{A,N}` of paper §7: the unique root of
`ℳ_{A,N}(β) = 1` in `(0, N)` (`lem:nd-gaussian-cramer-exponent`), which is the
power-law exponent of the stationary law in `thm:nd-power-singularity`.

Defined as the infimum of the root set so that no supercriticality hypothesis is
needed to write it down; `cramerExponent_mem` and
`gaussianTransferMoment_cramerExponent` pin it down as *the* root under
`Supercritical A N`. -/
noncomputable def cramerExponent (A : ℝ) (N : ℕ) : ℝ :=
  sInf {β | β ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧ gaussianTransferMoment A N β = 1}

/-- Under supercriticality the root set is the singleton `{β_{A,N}}`. -/
lemma root_set_gaussianTransferMoment_eq_singleton {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) :
    {β | β ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧ gaussianTransferMoment A N β = 1}
      = {cramerExponent A N} := by
  obtain ⟨β, hβ, huniq⟩ := existsUnique_gaussianTransferMoment_eq_one hA hN hsc
  have hset : {β' | β' ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧ gaussianTransferMoment A N β' = 1}
      = {β} := Set.eq_singleton_iff_unique_mem.mpr ⟨hβ, fun y hy => huniq y hy⟩
  have hcr : cramerExponent A N = β := by
    rw [cramerExponent, hset, csInf_singleton]
  rw [hset, hcr]

/-- `β_{A,N} ∈ (0, N)` in the supercritical regime. -/
lemma cramerExponent_mem {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) : cramerExponent A N ∈ Set.Ioo (0 : ℝ) (N : ℝ) := by
  have h : cramerExponent A N ∈
      {β | β ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧ gaussianTransferMoment A N β = 1} := by
    rw [root_set_gaussianTransferMoment_eq_singleton hA hN hsc]; rfl
  exact h.1

/-- `β_{A,N}` is a root: `ℳ_{A,N}(β_{A,N}) = 1`. -/
lemma gaussianTransferMoment_cramerExponent {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) :
    gaussianTransferMoment A N (cramerExponent A N) = 1 := by
  have h : cramerExponent A N ∈
      {β | β ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧ gaussianTransferMoment A N β = 1} := by
    rw [root_set_gaussianTransferMoment_eq_singleton hA hN hsc]; rfl
  exact h.2

/-- Any root in `(0, N)` is `β_{A,N}`. -/
lemma eq_cramerExponent {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {β : ℝ} (hβ : β ∈ Set.Ioo (0 : ℝ) (N : ℝ))
    (hroot : gaussianTransferMoment A N β = 1) : β = cramerExponent A N := by
  have h : β ∈ {β' | β' ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧ gaussianTransferMoment A N β' = 1} :=
    ⟨hβ, hroot⟩
  rw [root_set_gaussianTransferMoment_eq_singleton hA hN hsc] at h
  exact h

/-- The pressure is the logarithm of the transfer moment: `F(β) = log ℳ_{A,N}(β)`. -/
lemma cgf_logRadialIncrement_eq_log {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) (β : ℝ) :
    cgf (logRadialIncrement A N) (gaussianVec N) β
      = Real.log (gaussianTransferMoment A N β) := by
  rw [gaussianTransferMoment_eq_mgf hA hN β]
  rfl

/-- The transfer moment is positive wherever it is finite, i.e. on `(-N, N)`,
being an mgf of the log-radial increment there. -/
lemma gaussianTransferMoment_pos {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {β : ℝ} (hβ : β ∈ Set.Ioo (-(N : ℝ)) (N : ℝ)) : 0 < gaussianTransferMoment A N β := by
  rw [gaussianTransferMoment_eq_mgf hA hN β]
  exact mgf_pos (Ioo_subset_integrableExpSet_logRadialIncrement hA hN hβ)

/-- **Strict subcriticality below the Cramér exponent** (used in the paper's
proof of `lem:nd-subcritical-exponential-moments`): for `0 < α < β_{A,N}` the
transfer moment is *strictly* below one, `ℳ_{A,N}(α) < 1`.

Paper argument: the pressure `F = log ℳ` is strictly convex on `[0, N)` and
vanishes at both `0` and `β_{A,N}`, so writing `α` as the strict convex
combination `(1 - α/β_{A,N}) · 0 + (α/β_{A,N}) · β_{A,N}` gives `F(α) < 0`. -/
lemma gaussianTransferMoment_lt_one_of_lt_cramerExponent {A : ℝ} (hA : 0 < A)
    {N : ℕ} (hN : 0 < N) (hsc : Supercritical A N) {α : ℝ} (hα : 0 < α)
    (hlt : α < cramerExponent A N) : gaussianTransferMoment A N α < 1 := by
  have hβmem := cramerExponent_mem hA hN hsc
  set β := cramerExponent A N with hβdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  -- The pressure vanishes at both endpoints of the convex combination.
  have hF0 : cgf (logRadialIncrement A N) (gaussianVec N) 0 = 0 := by
    rw [cgf_zero', probReal_univ, Real.log_one]
  have hFβ : cgf (logRadialIncrement A N) (gaussianVec N) β = 0 := by
    rw [cgf_logRadialIncrement_eq_log hA hN,
      gaussianTransferMoment_cramerExponent hA hN hsc, Real.log_one]
  -- Strict convexity through the combination `α = (1 - α/β)·0 + (α/β)·β`.
  have ht0 : 0 < α / β := div_pos hα hβmem.1
  have ht1 : 0 < 1 - α / β := by
    have : α / β < 1 := (div_lt_one hβmem.1).mpr hlt
    linarith
  have hcomb := (strictConvexOn_cgf_logRadialIncrement_Ico hA hN).2
    (⟨le_refl _, hNpos⟩ : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (N : ℝ))
    (⟨le_of_lt hβmem.1, hβmem.2⟩ : β ∈ Set.Ico (0 : ℝ) (N : ℝ))
    (ne_of_lt hβmem.1) ht1 ht0 (by ring)
  rw [hF0, hFβ] at hcomb
  simp only [smul_eq_mul, mul_zero, add_zero, zero_add] at hcomb
  have hβ0 : β ≠ 0 := ne_of_gt hβmem.1
  have harg : α / β * β = α := by field_simp
  rw [harg] at hcomb
  -- Exponentiate: `ℳ(α) = exp (F α) < exp 0 = 1`.
  have hpos : 0 < gaussianTransferMoment A N α :=
    gaussianTransferMoment_pos hA hN ⟨by linarith, lt_trans hlt hβmem.2⟩
  have hexp : gaussianTransferMoment A N α
      = Real.exp (cgf (logRadialIncrement A N) (gaussianVec N) α) := by
    rw [cgf_logRadialIncrement_eq_log hA hN, Real.exp_log hpos]
  rw [hexp, show (1 : ℝ) = Real.exp 0 by rw [Real.exp_zero]]
  exact Real.exp_lt_exp.mpr hcomb

/-- The pressure is strictly negative strictly between its two zeros:
`F(α) < 0` for `0 < α < β_{A,N}`. Logarithmic form of
`gaussianTransferMoment_lt_one_of_lt_cramerExponent`. -/
lemma cgf_logRadialIncrement_neg_of_lt_cramerExponent {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) {α : ℝ} (hα : 0 < α)
    (hlt : α < cramerExponent A N) :
    cgf (logRadialIncrement A N) (gaussianVec N) α < 0 := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hpos : 0 < gaussianTransferMoment A N α :=
    gaussianTransferMoment_pos hA hN ⟨by linarith [hβmem.1], lt_trans hlt hβmem.2⟩
  rw [cgf_logRadialIncrement_eq_log hA hN]
  exact Real.log_neg hpos
    (gaussianTransferMoment_lt_one_of_lt_cramerExponent hA hN hsc hα hlt)

/-- **Positive drift after tilting** (paper, proof of `lem:nd-gaussian-renewal`):
the tilted increment law `\hat μ_{A,N}` has drift
`\hat m_{A,N} = (d/dβ) log ℳ_{A,N}(β) |_{β = β_{A,N}} > 0`.

Paper argument: `F = log ℳ` is strictly convex with `F(0) = F(β_{A,N}) = 0`, so
it is strictly negative in between and its derivative at the *upper* zero is
positive. Formally, convexity bounds `deriv F β_{A,N}` below by the chord slope
from any `α ∈ (0, β_{A,N})`, and that slope is `-F(α)/(β_{A,N}-α) > 0`. -/
lemma deriv_cgf_logRadialIncrement_cramerExponent_pos {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) :
    0 < deriv (cgf (logRadialIncrement A N) (gaussianVec N)) (cramerExponent A N) := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set β := cramerExponent A N with hβdef
  set F := cgf (logRadialIncrement A N) (gaussianVec N) with hFdef
  -- The midpoint of `(0, β)` is a point where `F` is strictly negative.
  have hα0 : 0 < β / 2 := by linarith [hβmem.1]
  have hαβ : β / 2 < β := by linarith [hβmem.1]
  have hFα : F (β / 2) < 0 :=
    cgf_logRadialIncrement_neg_of_lt_cramerExponent hA hN hsc hα0 hαβ
  have hFβ : F β = 0 := by
    rw [hFdef, cgf_logRadialIncrement_eq_log hA hN,
      gaussianTransferMoment_cramerExponent hA hN hsc, Real.log_one]
  -- `F` is differentiable at `β`, an interior point of the `integrableExpSet`.
  have hint : β ∈ interior (integrableExpSet (logRadialIncrement A N) (gaussianVec N)) :=
    interior_maximal (Ioo_subset_integrableExpSet_logRadialIncrement hA hN) isOpen_Ioo
      ⟨by linarith [hβmem.1], hβmem.2⟩
  have hdiff : DifferentiableAt ℝ F β := (analyticAt_cgf hint).differentiableAt
  -- Convexity: the chord slope from `β/2` to `β` lower-bounds `deriv F β`.
  have hslope : slope F (β / 2) β ≤ deriv F β :=
    (strictConvexOn_cgf_logRadialIncrement_Ico hA hN).convexOn.slope_le_deriv
      ⟨le_of_lt hα0, by linarith [hβmem.2]⟩
      ⟨le_of_lt hβmem.1, hβmem.2⟩ hαβ hdiff
  have hβpos : 0 < β := hβmem.1
  have hslope_pos : 0 < slope F (β / 2) β := by
    rw [slope_def_field, hFβ]
    exact div_pos_iff.mpr (Or.inl ⟨by linarith, by linarith⟩)
  linarith

/-- The log-radial increment is measurable (it is a composition of the
Euclidean norm with `log`). -/
lemma measurable_logRadialIncrement (A : ℝ) (N : ℕ) :
    Measurable (logRadialIncrement A N) := by
  unfold logRadialIncrement gaussianEuclideanNorm
  exact ((measurable_gaussianSquaredNorm N).sqrt.const_mul _).log.neg

/-- The **tilted increment law** `\hat μ_{A,N}` of paper
`eq:nd-tilted-increment-law`: the law of the log-radial increment
`Z = -log ℓ_{A,N}` after exponential tilting at the Cramér exponent, i.e. under
the weight `ℓ_{A,N}^{-β_{A,N}} = e^{β_{A,N} Z}`. This is the increment law of the
random walk driving the linear renewal equation. -/
noncomputable def tiltedIncrementLaw (A : ℝ) (N : ℕ) : Measure ℝ :=
  ((gaussianVec N).tilted
      (fun g => cramerExponent A N * logRadialIncrement A N g)).map
    (logRadialIncrement A N)

/-- `\hat μ_{A,N}` is a probability measure. Paper: "the identity
`r_{A,N}(β_{A,N}) = 1` says precisely that `\hat μ_{A,N}` has total mass one".
Here the normalization is carried by `Measure.tilted`, whose normalizing constant
is `ℳ_{A,N}(β_{A,N})`; that constant equals one is
`gaussianTransferMoment_cramerExponent`, recorded in
`integral_tiltedIncrementLaw` below. -/
lemma isProbabilityMeasure_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) :
    IsProbabilityMeasure (tiltedIncrementLaw A N) := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : Integrable
      (fun g => Real.exp (cramerExponent A N * logRadialIncrement A N g))
      (gaussianVec N) :=
    Ioo_subset_integrableExpSet_logRadialIncrement hA hN
      ⟨by linarith [hβmem.1], hβmem.2⟩
  haveI : IsProbabilityMeasure
      ((gaussianVec N).tilted
        (fun g => cramerExponent A N * logRadialIncrement A N g)) :=
    isProbabilityMeasure_tilted hint
  constructor
  rw [tiltedIncrementLaw,
    Measure.map_apply (measurable_logRadialIncrement A N) MeasurableSet.univ]
  simp

/-- The normalizing constant of the tilt is one: `𝔼[e^{β_{A,N} Z}] = ℳ_{A,N}(β_{A,N}) = 1`. -/
lemma integral_exp_cramerExponent_logRadialIncrement {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) :
    ∫ g, Real.exp (cramerExponent A N * logRadialIncrement A N g) ∂gaussianVec N = 1 := by
  have h := gaussianTransferMoment_eq_mgf hA hN (cramerExponent A N)
  rw [gaussianTransferMoment_cramerExponent hA hN hsc] at h
  exact h.symm

/-- Defining identity of the tilted increment law (paper
`eq:nd-tilted-increment-law`): `∫ φ d\hat μ_{A,N} = 𝔼[ℓ_{A,N}^{-β_{A,N}} φ(-log ℓ_{A,N})]`,
with **no** normalizing constant — because that constant is
`ℳ_{A,N}(β_{A,N}) = 1`. -/
lemma integral_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∫ z, φ z ∂tiltedIncrementLaw A N
      = ∫ g, Real.exp (cramerExponent A N * logRadialIncrement A N g)
          * φ (logRadialIncrement A N g) ∂gaussianVec N := by
  rw [tiltedIncrementLaw, integral_map (measurable_logRadialIncrement A N).aemeasurable
      hφ.aestronglyMeasurable, integral_tilted]
  simp_rw [integral_exp_cramerExponent_logRadialIncrement hA hN hsc, div_one, smul_eq_mul]

/-- **The tilted walk has positive drift** (paper `eq:nd-tilted-drift`):
`\hat m_{A,N} = ∫ z d\hat μ_{A,N} = (d/dβ) log ℳ_{A,N}(β)|_{β=β_{A,N}} > 0`.
This is the hypothesis the key renewal theorem needs. -/
lemma integral_id_tiltedIncrementLaw_pos {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) : 0 < ∫ z, z ∂tiltedIncrementLaw A N := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : cramerExponent A N ∈
      interior (integrableExpSet (logRadialIncrement A N) (gaussianVec N)) :=
    interior_maximal (Ioo_subset_integrableExpSet_logRadialIncrement hA hN) isOpen_Ioo
      ⟨by linarith [hβmem.1], hβmem.2⟩
  -- The drift is exactly `F'(β_{A,N})`, since the tilt normalizes to one.
  have hderiv := deriv_cgf (X := logRadialIncrement A N) (μ := gaussianVec N) hint
  rw [show mgf (logRadialIncrement A N) (gaussianVec N) (cramerExponent A N) = 1 from
      (integral_exp_cramerExponent_logRadialIncrement hA hN hsc), div_one] at hderiv
  have h1 := integral_tiltedIncrementLaw hA hN hsc (measurable_id : Measurable fun z : ℝ => z)
  have h2 : ∫ z, z ∂tiltedIncrementLaw A N
      = ∫ x, logRadialIncrement A N x
          * Real.exp (cramerExponent A N * logRadialIncrement A N x) ∂gaussianVec N :=
    h1.trans (integral_congr_ae (Filter.Eventually.of_forall fun g => by simp [mul_comm]))
  have hval : ∫ z, z ∂tiltedIncrementLaw A N
      = deriv (cgf (logRadialIncrement A N) (gaussianVec N)) (cramerExponent A N) :=
    h2.trans hderiv.symm
  rw [hval]
  exact deriv_cgf_logRadialIncrement_cramerExponent_pos hA hN hsc

/-- **The tilted drift is finite** (paper: "the drift is finite because
`𝔼[χ_N^{-β}|log χ_N|] < ∞` for `β < N`"): the identity is integrable against
`\hat μ_{A,N}`. Formally this is `𝔼[|Z| e^{β_{A,N} Z}] < ∞`, an instance of the
interior-of-`integrableExpSet` moment bound. Together with
`integral_id_tiltedIncrementLaw_pos` this gives `\hat m_{A,N} ∈ (0, ∞)`. -/
lemma integrable_id_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) :
    Integrable (fun z : ℝ => z) (tiltedIncrementLaw A N) := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmem : cramerExponent A N ∈ Set.Ioo (-(N : ℝ)) (N : ℝ) :=
    ⟨by linarith [hβmem.1], hβmem.2⟩
  have hint : cramerExponent A N ∈
      interior (integrableExpSet (logRadialIncrement A N) (gaussianVec N)) :=
    interior_maximal (Ioo_subset_integrableExpSet_logRadialIncrement hA hN) isOpen_Ioo hmem
  have hexp : Integrable
      (fun g => Real.exp (cramerExponent A N * logRadialIncrement A N g))
      (gaussianVec N) := Ioo_subset_integrableExpSet_logRadialIncrement hA hN hmem
  rw [tiltedIncrementLaw,
    integrable_map_measure (g := fun z : ℝ => z)
      (measurable_id : Measurable fun z : ℝ => z).aestronglyMeasurable
      (measurable_logRadialIncrement A N).aemeasurable,
    integrable_tilted_iff hexp]
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using
    integrable_pow_mul_exp_of_mem_interior_integrableExpSet hint 1

/-- **The tilted increment law has a finite second moment**: `MemLp id 2 μ̂_{A,N}`.

This is the remaining analytic hypothesis of the key renewal theorem
(`Renewal.tendsto_tsum_integral_comp_sub_of_driNorm`), where it is what makes the
characteristic function of `μ̂_{A,N}` twice differentiable at the origin and hence
`1 - χ` quantitatively invertible near `0`. The proof is the same
`integrableExpSet` argument as `integrable_id_tiltedIncrementLaw`, at the second
power instead of the first: `β_{A,N}` lies in the *interior* of the exponential
moment set, so `𝔼[|Z|^n e^{β_{A,N} Z}] < ∞` for every `n`. -/
lemma memLp_id_two_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) :
    MemLp (id : ℝ → ℝ) 2 (tiltedIncrementLaw A N) := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmem : cramerExponent A N ∈ Set.Ioo (-(N : ℝ)) (N : ℝ) :=
    ⟨by linarith [hβmem.1], hβmem.2⟩
  have hint : cramerExponent A N ∈
      interior (integrableExpSet (logRadialIncrement A N) (gaussianVec N)) :=
    interior_maximal (Ioo_subset_integrableExpSet_logRadialIncrement hA hN) isOpen_Ioo hmem
  have hexp : Integrable
      (fun g => Real.exp (cramerExponent A N * logRadialIncrement A N g))
      (gaussianVec N) := Ioo_subset_integrableExpSet_logRadialIncrement hA hN hmem
  rw [memLp_two_iff_integrable_sq aestronglyMeasurable_id, tiltedIncrementLaw,
    integrable_map_measure (g := fun z : ℝ => id z ^ 2)
      ((measurable_id.pow_const 2 : Measurable fun z : ℝ => id z ^ 2)).aestronglyMeasurable
      (measurable_logRadialIncrement A N).aemeasurable,
    integrable_tilted_iff hexp]
  simpa [Function.comp_def, smul_eq_mul, mul_comm] using
    integrable_pow_mul_exp_of_mem_interior_integrableExpSet hint 2

/-- Every fibre of the squared Gaussian norm is null: its law is the Gamma law,
which is absolutely continuous with respect to Lebesgue measure. (Extracted from
the argument inside `gaussianSquaredNorm_not_ae_const`.) -/
lemma measure_preimage_gaussianSquaredNorm_singleton {N : ℕ} (hN : 0 < N) (c : ℝ) :
    gaussianVec N (gaussianSquaredNorm N ⁻¹' {c}) = 0 := by
  rw [← Measure.map_apply (measurable_gaussianSquaredNorm N) (measurableSet_singleton c),
    map_gaussianSquaredNorm_eq_gammaMeasure hN]
  have hac : gammaMeasure ((N : ℝ) / 2) (1 / 2) ≪ volume := by
    rw [gammaMeasure]
    exact withDensity_absolutelyContinuous _ _
  exact hac Real.volume_singleton

/-- Every fibre of the log-radial increment is null. A level set `{Z = z}` is,
off the null set `{‖g‖ = 0}`, the sphere `{‖g‖² = ((√N/A)e^{-z})²}`, which is a
fibre of the squared norm. This is the paper's "the law of `\hat μ_{A,N}` has a
density, since `χ_N` has a density on `(0,∞)`" in the weaker atomless form that
nonlatticeness actually needs. -/
lemma measure_preimage_logRadialIncrement_singleton {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (z : ℝ) :
    gaussianVec N (logRadialIncrement A N ⁻¹' {z}) = 0 := by
  have hk : 0 < A / Real.sqrt N :=
    div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))
  -- The degenerate fibre `{‖g‖ = 0}` is null.
  have hzero : gaussianVec N {g | gaussianEuclideanNorm N g = 0} = 0 := by
    have h := ae_gaussianEuclideanNorm_pos hN
    rw [ae_iff] at h
    refine measure_mono_null ?_ h
    intro g hg
    simp only [Set.mem_setOf_eq, not_lt] at hg ⊢
    exact le_of_eq hg
  refine measure_mono_null (t := gaussianSquaredNorm N ⁻¹' {((Real.sqrt N / A) * Real.exp (-z)) ^ 2}
      ∪ {g | gaussianEuclideanNorm N g = 0}) ?_ ?_
  · intro g hg
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg
    rcases eq_or_lt_of_le (by unfold gaussianEuclideanNorm; positivity :
        (0 : ℝ) ≤ gaussianEuclideanNorm N g) with hnorm | hnorm
    · exact Or.inr (by simpa using hnorm.symm)
    · refine Or.inl ?_
      have hprod : 0 < (A / Real.sqrt N) * gaussianEuclideanNorm N g := mul_pos hk hnorm
      have hlog : Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g) = -z := by
        have : -Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g) = z := hg
        linarith
      have hval : (A / Real.sqrt N) * gaussianEuclideanNorm N g = Real.exp (-z) := by
        rw [← hlog, Real.exp_log hprod]
      have hnormval : gaussianEuclideanNorm N g = (Real.sqrt N / A) * Real.exp (-z) := by
        field_simp at hval ⊢
        nlinarith [hval, Real.sqrt_pos.mpr (by exact_mod_cast hN : (0:ℝ) < N)]
      have hsq : gaussianSquaredNorm N g = (gaussianEuclideanNorm N g) ^ 2 := by
        unfold gaussianEuclideanNorm
        rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hsq, hnormval]
  · exact measure_union_null (measure_preimage_gaussianSquaredNorm_singleton hN _) hzero

/-- `\hat μ_{A,N}` is atomless. Tilting keeps null sets null
(`tilted_absolutelyContinuous`) and the pushforward fibres are null by
`measure_preimage_logRadialIncrement_singleton`. -/
lemma nullSingletonClass_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) : NullSingletonClass (tiltedIncrementLaw A N) := by
  constructor
  intro z
  rw [tiltedIncrementLaw,
    Measure.map_apply (measurable_logRadialIncrement A N) (measurableSet_singleton z)]
  exact tilted_absolutelyContinuous _ _
    (measure_preimage_logRadialIncrement_singleton hA hN z)

/-- **`\hat μ_{A,N}` is nonlattice** (paper, proof of `lem:nd-gaussian-renewal`):
every arithmetic progression `a + rℤ` is null for the tilted increment law. This
is the hypothesis under which the key renewal theorem applies on the whole line
(rather than the lattice renewal theorem). It follows from atomlessness alone,
a lattice being countable. -/
lemma tiltedIncrementLaw_lattice_eq_zero {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (a r : ℝ) : tiltedIncrementLaw A N {x : ℝ | ∃ k : ℤ, x = a + k * r} = 0 := by
  haveI := nullSingletonClass_tiltedIncrementLaw hA hN
  have hcount : {x : ℝ | ∃ k : ℤ, x = a + k * r}.Countable := by
    have hrange : {x : ℝ | ∃ k : ℤ, x = a + k * r} = Set.range (fun k : ℤ => a + k * r) := by
      ext x; simp [eq_comm]
    rw [hrange]
    exact Set.countable_range _
  exact hcount.measure_zero _

/-- Restatement of nonlatticeness in the form the renewal theorem uses: the
tilted increment law is not concentrated on any lattice `a + rℤ`. -/
lemma tiltedIncrementLaw_not_concentrated_on_lattice {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (a r : ℝ) :
    tiltedIncrementLaw A N {x : ℝ | ∃ k : ℤ, x = a + k * r} ≠ 1 := by
  rw [tiltedIncrementLaw_lattice_eq_zero hA hN a r]
  exact zero_ne_one

/-- Bridge to Mathlib's multivariate standard Gaussian: transporting
`gaussianVec N` (a product measure on `Fin N → ℝ`) to `EuclideanSpace ℝ (Fin N)`
gives `stdGaussian`. This is what makes the paper's isotropy arguments — "in the
present Gaussian ensemble, isotropy collapses the angular part" — available,
since `stdGaussian` is invariant under every linear isometry
(`stdGaussian_map`). -/
lemma map_toLp_gaussianVec (N : ℕ) :
    Measure.map (WithLp.toLp 2) (gaussianVec N)
      = stdGaussian (EuclideanSpace ℝ (Fin N)) := by
  rw [gaussianVec]
  exact map_pi_eq_stdGaussian

/-- The paper's radial coordinate is the `EuclideanSpace` norm. -/
lemma gaussianEuclideanNorm_eq_norm (N : ℕ) (g : Fin N → ℝ) :
    gaussianEuclideanNorm N g = ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin N))‖ := by
  unfold gaussianEuclideanNorm gaussianSquaredNorm
  rw [EuclideanSpace.norm_eq]
  simp [sq_abs]

/-- The log-radial increment written on `EuclideanSpace`, where the rotation
group acts: `Z(x) = -log((A/√N)‖x‖)`. -/
noncomputable def logRadialIncrementE (A : ℝ) (N : ℕ)
    (x : EuclideanSpace ℝ (Fin N)) : ℝ :=
  -Real.log ((A / Real.sqrt N) * ‖x‖)

lemma measurable_logRadialIncrementE (A : ℝ) (N : ℕ) :
    Measurable (logRadialIncrementE A N) := by
  unfold logRadialIncrementE
  fun_prop

/-- The coordinate and `EuclideanSpace` forms of the increment agree. -/
lemma logRadialIncrement_eq_logRadialIncrementE (A : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    logRadialIncrement A N g = logRadialIncrementE A N (WithLp.toLp 2 g) := by
  unfold logRadialIncrement logRadialIncrementE
  rw [gaussianEuclideanNorm_eq_norm]

/-- The increment law is the same computed in coordinates or on
`EuclideanSpace` against `stdGaussian`. -/
lemma map_logRadialIncrement_eq (A : ℝ) (N : ℕ) :
    Measure.map (logRadialIncrement A N) (gaussianVec N)
      = Measure.map (logRadialIncrementE A N) (stdGaussian (EuclideanSpace ℝ (Fin N))) := by
  have hR := measurable_logRadialIncrementE A N
  rw [show logRadialIncrement A N
        = (logRadialIncrementE A N) ∘ (WithLp.toLp 2) from
      funext (logRadialIncrement_eq_logRadialIncrementE A N),
    ← Measure.map_map hR (by fun_prop), map_toLp_gaussianVec]

/-- **Isotropy of the log-radial increment** (paper §7, before
`eq:nd-linear-markov-additive`: "in the present Gaussian ensemble, isotropy
collapses the angular part; conditionally on any direction, `WΘ` has the same
centered Gaussian law"). Precomposing with any rotation of `ℝ^N` leaves the
increment law unchanged, because `stdGaussian` is invariant under linear
isometries. -/
lemma map_logRadialIncrementE_rotation (A : ℝ) (N : ℕ)
    (f : EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)) :
    Measure.map (fun x => logRadialIncrementE A N (f x))
        (stdGaussian (EuclideanSpace ℝ (Fin N)))
      = Measure.map (logRadialIncrementE A N)
        (stdGaussian (EuclideanSpace ℝ (Fin N))) := by
  have hR := measurable_logRadialIncrementE A N
  rw [show (fun x => logRadialIncrementE A N (f x))
        = (logRadialIncrementE A N) ∘ f from rfl,
    ← Measure.map_map hR f.continuous.measurable, stdGaussian_map f]

/-! ### Subcritical exponential moments (paper `lem:nd-subcritical-exponential-moments`)

The paper's Lyapunov argument runs with `V(q) = q^{-p}`, `p = α/2`, for
`0 ≤ α < β_{A,N}`. `AbsorptionCutoff.Supercritical.GaussianRadial` develops the whole
chain at `p = 1` (the reciprocal moment used in Chapter 6); the lemmas below
generalize the two analytic inputs to arbitrary `p` with `2p < N`. -/

/-- For `0 ≤ u` and `0 ≤ p`, `(1 + u)^p ≤ 2^p (1 + u^p)`. -/
lemma one_add_rpow_le_two_rpow_mul {u p : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p) :
    (1 + u) ^ p ≤ 2 ^ p * (1 + u ^ p) := by
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ p ≤ (2 : ℝ) ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp
      _ ≤ 2 ^ p * (1 + u ^ p) := by
          nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p, Real.rpow_nonneg hu p]
  · calc (1 + u) ^ p ≤ (2 * u) ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp
      _ = 2 ^ p * u ^ p := Real.mul_rpow (by norm_num) hu
      _ ≤ 2 ^ p * (1 + u ^ p) := by
          nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p, Real.rpow_nonneg hu p]

/-- Off the origin the normalized squared-radius update is strictly positive.
(The `R = 1` case is inlined in `integral_inv_Fmap_div_tendsto`; this is the
same argument at an arbitrary radius.) -/
lemma Fmap_div_pos_of_gaussianSquaredNorm_pos {A R : ℝ} {N : ℕ} (hA : A ≠ 0)
    (hR : 0 < R) (hN : 0 < N) {g : Fin N → ℝ} (hg : 0 < gaussianSquaredNorm N g) :
    0 < Fmap A N R g / R := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hmin : 0 < min (A ^ 2 * R) 1 :=
    lt_min (mul_pos (sq_pos_of_ne_zero hA) hR) zero_lt_one
  have htanh : 0 < Real.tanh 1 := by
    rw [← Real.tanh_zero]
    exact tanh_strictMono zero_lt_one
  have hraw := sum_tanh_sq_lower_gaussianSquaredNorm (A := A) (R := R) hR.le N g
  have hlower : 0 < Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1 *
      (gaussianSquaredNorm N g / (1 + gaussianSquaredNorm N g)) := by positivity
  have hsum : 0 < ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 := hlower.trans_le hraw
  have hF : 0 < Fmap A N R g := by
    unfold Fmap
    exact mul_pos (inv_pos.mpr hNreal) hsum
  exact div_pos hF hR

/-- Pointwise domination of the negative `p`-th power of the normalized update
by a constant multiple of `1 + ‖g‖₂^{-2p}`, the `p`-analogue of
`inv_Fmap_div_le_one_add_inv_gaussianSquaredNorm`. -/
lemma neg_rpow_Fmap_div_le {A R : ℝ} {N : ℕ} (hA : A ≠ 0) (hR : 0 < R) (hN : 0 < N)
    {p : ℝ} (hp : 0 ≤ p) {g : Fin N → ℝ} (hg : 0 < gaussianSquaredNorm N g) :
    (Fmap A N R g / R) ^ (-p)
      ≤ (((N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) ^ p * 2 ^ p)
          * (1 + (gaussianSquaredNorm N g) ^ (-p)) := by
  have hFpos := Fmap_div_pos_of_gaussianSquaredNorm_pos hA hR hN hg
  have hC : 0 ≤ (N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1) := by
    have hmin : 0 < min (A ^ 2 * R) 1 :=
      lt_min (mul_pos (sq_pos_of_ne_zero hA) hR) zero_lt_one
    have htanh : 0 < Real.tanh 1 := by
      rw [← Real.tanh_zero]
      exact tanh_strictMono zero_lt_one
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hbound := inv_Fmap_div_le_one_add_inv_gaussianSquaredNorm hA hR hN g
  have hinv_nonneg : (0 : ℝ) ≤ (Fmap A N R g / R)⁻¹ := (inv_pos.mpr hFpos).le
  -- Raise the `p = 1` bound to the power `p`.
  calc (Fmap A N R g / R) ^ (-p)
      = ((Fmap A N R g / R)⁻¹) ^ p := by
        rw [Real.rpow_neg hFpos.le, Real.inv_rpow hFpos.le]
    _ ≤ (((N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1))
          * (1 + (gaussianSquaredNorm N g)⁻¹)) ^ p :=
        Real.rpow_le_rpow hinv_nonneg hbound hp
    _ = ((N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) ^ p
          * (1 + (gaussianSquaredNorm N g)⁻¹) ^ p :=
        Real.mul_rpow hC (by positivity)
    _ ≤ ((N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) ^ p
          * (2 ^ p * (1 + ((gaussianSquaredNorm N g)⁻¹) ^ p)) := by
        refine mul_le_mul_of_nonneg_left
          (one_add_rpow_le_two_rpow_mul (by positivity) hp) (Real.rpow_nonneg hC p)
    _ = (((N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) ^ p * 2 ^ p)
          * (1 + (gaussianSquaredNorm N g) ^ (-p)) := by
        rw [Real.inv_rpow hg.le, ← Real.rpow_neg hg.le]
        ring

/-- Negative powers of the squared Gaussian norm are integrable below the
dimension threshold: `𝔼‖G‖₂^{-2p} < ∞` for `2p < N`. -/
lemma integrable_neg_rpow_gaussianSquaredNorm {N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : 2 * p < N) :
    Integrable (fun g : Fin N → ℝ => (gaussianSquaredNorm N g) ^ (-p))
      (gaussianVec N) := by
  have h := integrable_neg_rpow_gaussianEuclideanNorm hN hp
  have hfun : (fun g : Fin N → ℝ => (gaussianEuclideanNorm N g) ^ (-(2 * p)))
      = (fun g : Fin N → ℝ => (gaussianSquaredNorm N g) ^ (-p)) := by
    funext g
    rw [gaussianEuclideanNorm, Real.sqrt_eq_rpow,
      ← Real.rpow_mul (gaussianSquaredNorm_nonneg N g)]
    congr 1
    ring
  rwa [hfun] at h

/-- **Integrability of the negative `p`-power of the normalized update** for
`0 ≤ p` with `2p < N`. This is the dominating-function input for the paper's
Lyapunov function `V(q) = q^{-p}` (`lem:nd-subcritical-exponential-moments`);
the `p = 1` case is `integrable_inv_Fmap_div`. -/
lemma integrable_neg_rpow_Fmap_div {A R : ℝ} {N : ℕ} (hA : A ≠ 0) (hR : 0 < R)
    (hN : 0 < N) {p : ℝ} (hp : 0 ≤ p) (hpN : 2 * p < N) :
    Integrable (fun g : Fin N → ℝ => (Fmap A N R g / R) ^ (-p)) (gaussianVec N) := by
  have hSpos : ∀ᵐ g ∂gaussianVec N, 0 < gaussianSquaredNorm N g := by
    filter_upwards [ae_gaussianEuclideanNorm_pos hN] with g hg
    have hsq : gaussianSquaredNorm N g = (gaussianEuclideanNorm N g) ^ 2 := by
      unfold gaussianEuclideanNorm
      rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
    rw [hsq]
    positivity
  have hmeas : AEStronglyMeasurable
      (fun g : Fin N → ℝ => (Fmap A N R g / R) ^ (-p)) (gaussianVec N) := by
    have hF : Measurable (Fmap A N R) :=
      Continuous.measurable (by
        unfold Fmap
        apply Continuous.const_mul
        apply continuous_finsetSum
        intro i _
        exact (continuous_tanh.comp (by fun_prop)).pow 2)
    have hmeas' : Measurable (fun g : Fin N → ℝ => (Fmap A N R g / R) ^ (-p)) := by
      fun_prop
    exact hmeas'.aestronglyMeasurable
  refine Integrable.mono' (g := fun g : Fin N → ℝ =>
    (((N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) ^ p * 2 ^ p)
      * (1 + (gaussianSquaredNorm N g) ^ (-p)))
    (((integrable_const 1).add (integrable_neg_rpow_gaussianSquaredNorm hN hpN)).const_mul _)
    hmeas ?_
  filter_upwards [hSpos] with g hg
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (div_nonneg (Fmap_nonneg A N R g) hR.le) _)]
  exact neg_rpow_Fmap_div_le hA hR hN hp hg

/-- The scaled radial power in the transfer moment, rewritten through the
squared norm: `((A/√N)‖g‖)^{-2p} = (A²‖g‖²/N)^{-p}`. -/
lemma neg_rpow_scaled_norm_eq {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) (p : ℝ)
    (g : Fin N → ℝ) :
    ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-(2 * p))
      = (A ^ 2 * gaussianSquaredNorm N g / N) ^ (-p) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 ≤ (A / Real.sqrt N) * gaussianEuclideanNorm N g := by
    unfold gaussianEuclideanNorm
    positivity
  have hsq : ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (2 : ℕ)
      = A ^ 2 * gaussianSquaredNorm N g / N := by
    unfold gaussianEuclideanNorm
    rw [mul_pow, div_pow, Real.sq_sqrt hNreal.le,
      Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
    ring
  rw [← hsq, ← Real.rpow_natCast ((A / Real.sqrt N) * gaussianEuclideanNorm N g) 2,
    ← Real.rpow_mul ht]
  congr 1
  push_cast
  ring

/-- **The negative `p`-moment of the normalized update converges to the transfer
moment** as the radius shrinks: `𝔼[(F_{A,N}(q,G)/q)^{-p}] → ℳ_{A,N}(2p)` as
`q ↓ 0`, for `0 ≤ p` with `2p < N`. This is the paper's truncation step in
`lem:nd-subcritical-exponential-moments` ("the fixed-`N` version of the
truncation argument in `prop:gaussian-near-zero-negative-moment`"); the `p = 1`
case is `integral_inv_Fmap_div_tendsto`. Dominated convergence applies with the
monotone dominator `(F_{A,N}(1,·))^{-p}`, integrable by
`integrable_neg_rpow_Fmap_div`. -/
lemma integral_neg_rpow_Fmap_div_tendsto {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {p : ℝ} (hp : 0 ≤ p) (hpN : 2 * p < N) :
    Tendsto (fun q => ∫ g : Fin N → ℝ, (Fmap A N q g / q) ^ (-p) ∂gaussianVec N)
      (𝓝[>] 0) (𝓝 (gaussianTransferMoment A N (2 * p))) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hA' : A ≠ 0 := ne_of_gt hA
  have hSpos : ∀ᵐ g ∂gaussianVec N, 0 < gaussianSquaredNorm N g := by
    filter_upwards [ae_gaussianEuclideanNorm_pos hN] with g hg
    have hsq : gaussianSquaredNorm N g = (gaussianEuclideanNorm N g) ^ 2 := by
      unfold gaussianEuclideanNorm
      rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
    rw [hsq]
    positivity
  have hmeas (q : ℝ) : AEStronglyMeasurable
      (fun g : Fin N → ℝ => (Fmap A N q g / q) ^ (-p)) (gaussianVec N) := by
    have hF : Measurable (Fmap A N q) :=
      Continuous.measurable (by
        unfold Fmap
        apply Continuous.const_mul
        apply continuous_finsetSum
        intro i _
        exact (continuous_tanh.comp (by fun_prop)).pow 2)
    have hmeas' : Measurable (fun g : Fin N → ℝ => (Fmap A N q g / q) ^ (-p)) := by
      fun_prop
    exact hmeas'.aestronglyMeasurable
  -- Dominated convergence towards the linearized integrand.
  have hconv : Tendsto
      (fun q => ∫ g : Fin N → ℝ, (Fmap A N q g / q) ^ (-p) ∂gaussianVec N)
      (𝓝[>] 0)
      (𝓝 (∫ g : Fin N → ℝ,
        (A ^ 2 * gaussianSquaredNorm N g / N) ^ (-p) ∂gaussianVec N)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun g : Fin N → ℝ => (Fmap A N 1 g / 1) ^ (-p))
      (Filter.Eventually.of_forall hmeas) ?_
      (integrable_neg_rpow_Fmap_div hA' zero_lt_one hN hp hpN) ?_
    · have hle_one : ∀ᶠ q : ℝ in 𝓝[>] 0, q ≤ 1 :=
        Filter.Eventually.filter_mono inf_le_left (Iic_mem_nhds zero_lt_one)
      filter_upwards [self_mem_nhdsWithin, hle_one] with q hq hq1
      filter_upwards [hSpos] with g hg
      have hqpos : (0 : ℝ) < q := hq
      have h1pos := Fmap_div_pos_of_gaussianSquaredNorm_pos hA' zero_lt_one hN hg
      have hqposF := Fmap_div_pos_of_gaussianSquaredNorm_pos hA' hqpos hN hg
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (div_nonneg (Fmap_nonneg A N q g) hqpos.le) _)]
      -- `x ↦ x^{-p}` is antitone on the positives, and `F(1)/1 ≤ F(q)/q`.
      rw [Real.rpow_neg hqposF.le, Real.rpow_neg h1pos.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos h1pos p)
        (Real.rpow_le_rpow h1pos.le (Fmap_div_ge_of_pos_of_le g hqpos hq1) hp)
    · filter_upwards [hSpos] with g hg
      have hlim := Fmap_div_tendsto_gaussianSquaredNorm hA' N g
      exact hlim.rpow_const (Or.inl (by positivity))
  -- Identify the limit with the transfer moment.
  have hval : (∫ g : Fin N → ℝ, (A ^ 2 * gaussianSquaredNorm N g / N) ^ (-p)
        ∂gaussianVec N) = gaussianTransferMoment A N (2 * p) := by
    unfold gaussianTransferMoment
    exact integral_congr_ae (Filter.Eventually.of_forall fun g =>
      (neg_rpow_scaled_norm_eq hA hN p g).symm)
  rwa [hval] at hconv

/-- **Strict contraction of the `p`-Lyapunov moment at small radii** (paper
`lem:nd-subcritical-exponential-moments`: "hence we may choose `R₀ > 0` and
`a < 1` such that, for `0 < q ≤ R₀`, `K_{A,N}V(q) ≤ aV(q)`").

For `0 < 2p < β_{A,N}` the limit `ℳ_{A,N}(2p)` of the negative `p`-moment is
strictly below one (`gaussianTransferMoment_lt_one_of_lt_cramerExponent`), so the
moment itself is below a fixed `a < 1` on a whole interval `(0, R₀]`. The `p = 1`
analogue in Chapter 6 is `exists_small_radius_integral_inv_Fmap_div_lt`. -/
lemma exists_small_radius_integral_neg_rpow_Fmap_div_lt {A : ℝ} (hA : 0 < A)
    {N : ℕ} (hN : 0 < N) (hsc : Supercritical A N) {p : ℝ} (hp : 0 < p)
    (hpβ : 2 * p < cramerExponent A N) :
    ∃ R₀ > 0, ∃ a < 1, ∀ q, 0 < q → q ≤ R₀ →
      ∫ g : Fin N → ℝ, (Fmap A N q g / q) ^ (-p) ∂gaussianVec N < a := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hpN : 2 * p < N := hpβ.trans hβmem.2
  have hlimit : gaussianTransferMoment A N (2 * p) < 1 :=
    gaussianTransferMoment_lt_one_of_lt_cramerExponent hA hN hsc (by linarith) hpβ
  set M := gaussianTransferMoment A N (2 * p) with hM
  set a := (M + 1) / 2 with hadef
  have hlimit_lt_a : M < a := by
    rw [hadef]; linarith
  have ha : a < 1 := by
    rw [hadef]; linarith
  have heventually : ∀ᶠ q : ℝ in 𝓝[>] 0,
      ∫ g : Fin N → ℝ, (Fmap A N q g / q) ^ (-p) ∂gaussianVec N < a :=
    (integral_neg_rpow_Fmap_div_tendsto hA hN hp.le hpN).eventually
      (Iio_mem_nhds hlimit_lt_a)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.1 heventually
  refine ⟨ε / 2, by positivity, a, ha, ?_⟩
  intro q hq hqR
  refine hεsub ⟨?_, hq⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hq]
  linarith

/-- The Lyapunov moment of one step, in terms of the normalized update:
`∫ y^{-p} K_{A,N}(q, dy) = q^{-p} 𝔼[(F_{A,N}(q,G)/q)^{-p}]`. -/
lemma integral_neg_rpow_Kchain {A : ℝ} {N : ℕ} {q : ℝ} (hq : 0 < q) {p : ℝ} :
    ∫ y : ℝ, y ^ (-p) ∂(Kchain A N q)
      = q ^ (-p) * ∫ g : Fin N → ℝ, (Fmap A N q g / q) ^ (-p) ∂gaussianVec N := by
  rw [Kchain_apply, integral_map (continuous_Fmap_right A N q).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y ^ (-p))
      ((gaussianVec N).map (Fmap A N q))), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  change (Fmap A N q g) ^ (-p) = q ^ (-p) * (Fmap A N q g / q) ^ (-p)
  rw [← Real.mul_rpow hq.le (div_nonneg (Fmap_nonneg A N q g) hq.le),
    mul_div_cancel₀ _ hq.ne']

/-- One-step integrability of the Lyapunov function under the squared-radius
kernel, for `0 ≤ p` with `2p < N` (the `p = 1` case is
`integrable_inv_Kchain`). -/
lemma integrable_neg_rpow_Kchain {A : ℝ} {N : ℕ} (hA : A ≠ 0) {q : ℝ} (hq : 0 < q)
    (hN : 0 < N) {p : ℝ} (hp : 0 ≤ p) (hpN : 2 * p < N) :
    Integrable (fun y : ℝ => y ^ (-p)) (Kchain A N q) := by
  rw [Kchain_apply]
  refine (integrable_map_measure
    (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y ^ (-p))
      ((gaussianVec N).map (Fmap A N q)))
    (continuous_Fmap_right A N q).aemeasurable).2 ?_
  have hratio := integrable_neg_rpow_Fmap_div hA hq hN hp hpN
  have hfun : ((fun y : ℝ => y ^ (-p)) ∘ Fmap A N q)
      = fun g : Fin N → ℝ => q ^ (-p) * (Fmap A N q g / q) ^ (-p) := by
    funext g
    change (Fmap A N q g) ^ (-p) = q ^ (-p) * (Fmap A N q g / q) ^ (-p)
    rw [← Real.mul_rpow hq.le (div_nonneg (Fmap_nonneg A N q g) hq.le),
      mul_div_cancel₀ _ hq.ne']
  rw [hfun]
  exact hratio.const_mul _

/-- **Foster–Lyapunov drift bound for `V(q) = q^{-p}`** (paper
`lem:nd-subcritical-exponential-moments`: "therefore `K_{A,N}V(q) ≤ aV(q)+B`,
`q ∈ (0,1]`"). For `0 < 2p < β_{A,N}` there are a contraction factor `a < 1` and
a finite constant `B` with

`∫ y^{-p} K_{A,N}(q, dy) ≤ a q^{-p} + B` for all `q ∈ (0,1]`.

Near zero this is the strict contraction
`exists_small_radius_integral_neg_rpow_Fmap_div_lt`; away from zero it is the
antitonicity of `q ↦ F_{A,N}(q,g)/q`, which bounds the moment by its value at
`q = 1` uniformly. The `p = 1` analogue is `exists_Kchain_inv_foster_bound`. -/
lemma exists_Kchain_neg_rpow_foster_bound {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {p : ℝ} (hp : 0 < p)
    (hpβ : 2 * p < cramerExponent A N) :
    ∃ a < 1, ∃ B : ℝ, 0 ≤ B ∧ ∀ q, 0 < q → q ≤ 1 →
      ∫ y : ℝ, y ^ (-p) ∂(Kchain A N q) ≤ a * q ^ (-p) + B := by
  have hA' : A ≠ 0 := ne_of_gt hA
  have hβmem := cramerExponent_mem hA hN hsc
  have hpN : 2 * p < N := hpβ.trans hβmem.2
  obtain ⟨R₀, hR₀, a, ha, hsmall⟩ :=
    exists_small_radius_integral_neg_rpow_Fmap_div_lt hA hN hsc hp hpβ
  -- The moment is nonnegative, so the contraction factor is positive.
  have hint_nonneg (q : ℝ) (hq : 0 < q) :
      0 ≤ ∫ g : Fin N → ℝ, (Fmap A N q g / q) ^ (-p) ∂gaussianVec N :=
    integral_nonneg fun g => Real.rpow_nonneg (div_nonneg (Fmap_nonneg A N q g) hq.le) _
  have hapos : 0 < a := lt_of_le_of_lt (hint_nonneg R₀ hR₀) (hsmall R₀ hR₀ le_rfl)
  -- Away from zero, the moment is bounded by its value at `q = 1`.
  set C := ∫ g : Fin N → ℝ, (Fmap A N 1 g / 1) ^ (-p) ∂gaussianVec N with hC
  have hCnonneg : 0 ≤ C := hint_nonneg 1 zero_lt_one
  have hmono (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
      ∫ g : Fin N → ℝ, (Fmap A N q g / q) ^ (-p) ∂gaussianVec N ≤ C := by
    have hSpos : ∀ᵐ g ∂gaussianVec N, 0 < gaussianSquaredNorm N g := by
      filter_upwards [ae_gaussianEuclideanNorm_pos hN] with g hg
      have hsq : gaussianSquaredNorm N g = (gaussianEuclideanNorm N g) ^ 2 := by
        unfold gaussianEuclideanNorm
        rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
      rw [hsq]
      positivity
    refine integral_mono_ae (integrable_neg_rpow_Fmap_div hA' hq hN hp.le hpN)
      (integrable_neg_rpow_Fmap_div hA' zero_lt_one hN hp.le hpN) ?_
    filter_upwards [hSpos] with g hg
    have h1pos := Fmap_div_pos_of_gaussianSquaredNorm_pos hA' zero_lt_one hN hg
    have hqposF := Fmap_div_pos_of_gaussianSquaredNorm_pos hA' hq hN hg
    rw [Real.rpow_neg hqposF.le, Real.rpow_neg h1pos.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos h1pos p)
      (Real.rpow_le_rpow h1pos.le (Fmap_div_ge_of_pos_of_le g hq hq1) hp.le)
  refine ⟨a, ha, R₀ ^ (-p) * C, by positivity, ?_⟩
  intro q hq hq1
  rw [integral_neg_rpow_Kchain hq]
  rcases le_total q R₀ with hqR | hqR
  · -- Contractive regime.
    have h := (hsmall q hq hqR).le
    have hqp : 0 < q ^ (-p) := Real.rpow_pos_of_pos hq _
    nlinarith [Real.rpow_nonneg hR₀.le (-p), mul_nonneg (Real.rpow_nonneg hR₀.le (-p)) hCnonneg]
  · -- Bounded regime: `q^{-p} ≤ R₀^{-p}` and the moment is at most `C`.
    have hqp : q ^ (-p) ≤ R₀ ^ (-p) := by
      rw [Real.rpow_neg hq.le, Real.rpow_neg hR₀.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hR₀ p) (Real.rpow_le_rpow hR₀.le hqR hp.le)
    have hmoment := hmono q hq hq1
    have hqppos : 0 < q ^ (-p) := Real.rpow_pos_of_pos hq _
    nlinarith [hint_nonneg q hq, Real.rpow_pos_of_pos hR₀ (-p),
      mul_pos hapos hqppos]

/-- **Uniform-in-time Lyapunov bound along the kernel iterates** (paper
`lem:nd-subcritical-exponential-moments`, the input to "the Cesàro construction
in the proof of `prop:gaussian-nonzero-invariant-existence`"). Iterating the
Foster bound `K V ≤ aV + B` from any starting radius `q ∈ (0,1]` keeps
`∫ y^{-p}` integrable and bounded by one constant, uniformly in the number of
steps. The `p = 1` case is `exists_uniform_integral_inv_Kchain_pow_le`. -/
lemma exists_uniform_integral_neg_rpow_Kchain_pow_le {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) {p : ℝ} (hp : 0 < p)
    (hpβ : 2 * p < cramerExponent A N) {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ,
      Integrable (fun y : ℝ => y ^ (-p)) (((Kchain A N) ^ t) q) ∧
      ∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ t) q ≤ C := by
  have hA' : A ≠ 0 := ne_of_gt hA
  have hβmem := cramerExponent_mem hA hN hsc
  have hpN : 2 * p < N := hpβ.trans hβmem.2
  obtain ⟨a, ha, B, hB0, hfoster⟩ :=
    exists_Kchain_neg_rpow_foster_bound hA hN hsc hp hpβ
  have ha'0 : 0 ≤ max a 0 := le_max_right _ _
  have ha'1 : max a 0 < 1 := max_lt ha zero_lt_one
  have hV0 : (0 : ℝ) ^ (-p) = 0 := Real.zero_rpow (neg_ne_zero.mpr hp.ne')
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2⟩
  have hsupport (t : ℕ) : ∀ᵐ x ∂((Kchain A N) ^ t) q, x ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact Kchain_pow_apply_Icc_compl A hN hqIcc t
  have hstep_integrable (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      Integrable (fun y : ℝ => y ^ (-p)) (Kchain A N x) := by
    by_cases hx0 : x = 0
    · subst x
      rw [Kchain_zero]
      refine integrable_dirac ?_
      simp [hV0]
    · exact integrable_neg_rpow_Kchain hA'
        (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hN hp.le hpN
  have hfoster_Icc (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
      ∫ y : ℝ, y ^ (-p) ∂Kchain A N x ≤ max a 0 * x ^ (-p) + B := by
    by_cases hx0 : x = 0
    · subst x
      rw [Kchain_zero, integral_dirac, hV0, mul_zero, zero_add]
      exact hB0
    · refine (hfoster x (lt_of_le_of_ne hx.1 (Ne.symm hx0)) hx.2).trans ?_
      have hVx : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx.1 _
      have hstep : a * x ^ (-p) ≤ max a 0 * x ^ (-p) :=
        mul_le_mul_of_nonneg_right (le_max_left a 0) hVx
      linarith
  have hnorm_action (x : ℝ) :
      (∫ y : ℝ, ‖y ^ (-p)‖ ∂Kchain A N x) = ∫ y : ℝ, y ^ (-p) ∂Kchain A N x := by
    rw [integral_Kchain A N x (by fun_prop : Measurable (fun y : ℝ => ‖y ^ (-p)‖)),
      integral_Kchain A N x (by fun_prop : Measurable (fun y : ℝ => y ^ (-p)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Fmap_nonneg A N x g) (-p))]
  have hpow_integrable : ∀ t : ℕ,
      Integrable (fun y : ℝ => y ^ (-p)) (((Kchain A N) ^ t) q) := by
    intro t
    induction t with
    | zero =>
        rw [pow_zero]
        change Integrable (fun y : ℝ => y ^ (-p)) (Measure.dirac q)
        refine integrable_dirac ?_
        simp
    | succ t iht =>
        rw [pow_succ']
        change Integrable (fun y : ℝ => y ^ (-p))
          (((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) q)
        refine (ProbabilityTheory.integrable_comp_iff
          (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y ^ (-p))
            (((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) q))).2 ⟨?_, ?_⟩
        · filter_upwards [hsupport t] with x hx
          exact hstep_integrable x hx
        · have hmajor : Integrable (fun x : ℝ => max a 0 * x ^ (-p) + B)
              (((Kchain A N) ^ t) q) :=
            (iht.const_mul (max a 0)).add (integrable_const B)
          have haction_meas : AEStronglyMeasurable
              (fun x => ∫ y : ℝ, ‖y ^ (-p)‖ ∂Kchain A N x) (((Kchain A N) ^ t) q) :=
            ((by fun_prop :
              StronglyMeasurable (fun y : ℝ => ‖y ^ (-p)‖)).integral_kernel :
              StronglyMeasurable
                (fun x => ∫ y : ℝ, ‖y ^ (-p)‖ ∂Kchain A N x)).aestronglyMeasurable
          refine hmajor.mono' haction_meas ?_
          filter_upwards [hsupport t] with x hx
          have hnonneg : 0 ≤ ∫ y : ℝ, ‖y ^ (-p)‖ ∂Kchain A N x :=
            integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hnorm_action x]
          exact hfoster_Icc x hx
  have hrec : ∀ t : ℕ,
      (∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ (t + 1)) q)
        ≤ max a 0 * (∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ t) q) + B := by
    intro t
    have hsucc : Integrable (fun y : ℝ => y ^ (-p))
        (((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) q) := by
      have hsucc' := hpow_integrable (t + 1)
      rw [pow_succ'] at hsucc'
      change Integrable (fun y : ℝ => y ^ (-p))
        (((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) q) at hsucc'
      exact hsucc'
    have haction : Integrable (fun x => ∫ y : ℝ, y ^ (-p) ∂Kchain A N x)
        (((Kchain A N) ^ t) q) := hsucc.integral_comp
    have hmajor : Integrable (fun x : ℝ => max a 0 * x ^ (-p) + B)
        (((Kchain A N) ^ t) q) :=
      ((hpow_integrable t).const_mul (max a 0)).add (integrable_const B)
    calc
      (∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ (t + 1)) q)
          = ∫ x, (∫ y : ℝ, y ^ (-p) ∂Kchain A N x) ∂((Kchain A N) ^ t) q := by
          rw [pow_succ']
          exact Kernel.integral_comp hsucc
      _ ≤ ∫ x, (max a 0 * x ^ (-p) + B) ∂((Kchain A N) ^ t) q :=
          integral_mono_ae haction hmajor <| by
            filter_upwards [hsupport t] with x hx
            exact hfoster_Icc x hx
      _ = max a 0 * (∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ t) q) + B := by
          rw [integral_add ((hpow_integrable t).const_mul (max a 0))
            (integrable_const B), integral_const_mul]
          simp
  have hm0 : 0 ≤ ∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ 0) q := by
    rw [pow_zero]
    change 0 ≤ ∫ y : ℝ, y ^ (-p) ∂Measure.dirac q
    rw [integral_dirac]
    exact Real.rpow_nonneg hq.1.le _
  refine ⟨max (∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ 0) q) (B / (1 - max a 0)),
    hm0.trans (le_max_left _ _), fun t => ⟨hpow_integrable t, ?_⟩⟩
  exact geom_recursion_bound_contraction
    (m := fun t : ℕ => ∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ t) q) ha'0 ha'1 hrec t

/-- The Cesàro averages inherit the uniform Lyapunov bound (paper
`lem:nd-subcritical-exponential-moments`, "the Cesàro construction therefore
produces a nonzero invariant law `ν̄` with `∫ q^{-p} ν̄(dq) < ∞`"). The `p = 1`
case is `exists_uniform_integral_inv_cesaroMeasure_le`. -/
lemma exists_uniform_integral_neg_rpow_cesaroMeasure_le {A : ℝ} (hA : 0 < A)
    {N : ℕ} (hN : 0 < N) (hsc : Supercritical A N) {p : ℝ} (hp : 0 < p)
    (hpβ : 2 * p < cramerExponent A N) {q : ℝ} (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, 0 < T →
      Integrable (fun y : ℝ => y ^ (-p)) (cesaroMeasure (Kchain A N) q T) ∧
      ∫ y : ℝ, y ^ (-p) ∂cesaroMeasure (Kchain A N) q T ≤ C := by
  obtain ⟨C, hC, hpow⟩ :=
    exists_uniform_integral_neg_rpow_Kchain_pow_le hA hN hsc hp hpβ hq
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hsum : Integrable (fun y : ℝ => y ^ (-p))
      (∑ t ∈ Finset.range T, ((Kchain A N) ^ t) q) :=
    integrable_finsetSum_measure.2 fun t _ => (hpow t).1
  have hcesaro : Integrable (fun y : ℝ => y ^ (-p))
      (cesaroMeasure (Kchain A N) q T) := by
    unfold cesaroMeasure
    exact hsum.smul_measure (ENNReal.inv_ne_top.2 (Nat.cast_ne_zero.2 hT.ne'))
  refine ⟨hcesaro, ?_⟩
  have hsum_le : (∑ t ∈ Finset.range T, ∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ t) q)
      ≤ ∑ _t ∈ Finset.range T, C := Finset.sum_le_sum fun t _ => (hpow t).2
  calc
    (∫ y : ℝ, y ^ (-p) ∂cesaroMeasure (Kchain A N) q T)
        = ((T : ENNReal)⁻¹).toReal *
            ∑ t ∈ Finset.range T, ∫ y : ℝ, y ^ (-p) ∂((Kchain A N) ^ t) q := by
        unfold cesaroMeasure
        rw [integral_smul_measure, smul_eq_mul,
          integral_finsetSum_measure (fun t _ => (hpow t).1)]
    _ ≤ ((T : ENNReal)⁻¹).toReal * ∑ _t ∈ Finset.range T, C :=
        mul_le_mul_of_nonneg_left hsum_le ENNReal.toReal_nonneg
    _ = C := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.toReal_inv]
        norm_cast
        field_simp

/-- **A nonzero invariant law of the squared-radius chain with a finite negative
`p`-moment** (paper `lem:nd-subcritical-exponential-moments`, steps 3–4): the
Cesàro construction produces an invariant probability `ν` on `[0,1]` with no atom
at the absorbing origin and `∫ q^{-p} ν(dq) < ∞`, for every `p` with
`0 < 2p < β_{A,N}`.

The Cesàro selection with a uniform negative-moment bound is Chapter 6's
`exists_invariant_Kchain_integrable_neg_rpow_of_uniform_cesaro`; the new content
is the uniform bound itself
(`exists_uniform_integral_neg_rpow_cesaroMeasure_le`), which is what the Cramér
exponent buys.

The same negative moment that gives tightness also rules out an atom at the
origin, so no auxiliary dimension condition is needed. -/
theorem exists_invariant_Kchain_integrable_neg_rpow {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N)
    {p : ℝ} (hp : 0 < p) (hpβ : 2 * p < cramerExponent A N) :
    ∃ ν : ProbabilityMeasure ℝ,
      Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
      (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
      (ν : Measure ℝ) ({0} : Set ℝ) = 0 ∧
      Integrable (fun y : ℝ => y ^ (-p)) (ν : Measure ℝ) := by
  have hqIoo : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  obtain ⟨C, _hC, hces⟩ :=
    exists_uniform_integral_neg_rpow_cesaroMeasure_le hA hN hsc hp hpβ
      (⟨by norm_num, by norm_num⟩ : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1)
  obtain ⟨ν, hinv, hsupp, hzero, hintegr, _hbound⟩ :=
    exists_invariant_Kchain_integrable_neg_rpow_of_uniform_cesaro hA hN hp
      hqIoo hces
  exact ⟨ν, hinv, hsupp, hzero, hintegr⟩

/-- **Every nonzero invariant law of the squared-radius chain has finite negative
`p`-moments below the Cramér exponent** (paper
`lem:nd-subcritical-exponential-moments`, step 5: "by the uniqueness of the
nonzero invariant law, `ν̄ = ν`"). Uniqueness
(`exists_unique_invariant_probability_Kchain_of_apply_singleton_zero`) identifies
the law produced by the Cesàro construction with the given one, transporting the
moment bound. -/
theorem integrable_neg_rpow_of_invariant_Kchain {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N)
    {p : ℝ} (hp : 0 < p) (hpβ : 2 * p < cramerExponent A N)
    (ν : ProbabilityMeasure ℝ) (hinv : Kernel.Invariant (Kchain A N) (ν : Measure ℝ))
    (hν0 : (ν : Measure ℝ) ({0} : Set ℝ) = 0) :
    Integrable (fun y : ℝ => y ^ (-p)) (ν : Measure ℝ) := by
  obtain ⟨ν₀, hinv₀, _hsupp₀, hzero₀, hintegr₀⟩ :=
    exists_invariant_Kchain_integrable_neg_rpow hA hN hsc hp hpβ
  have huniq : ν = ν₀ :=
    invariant_probability_unique_Kchain_of_apply_singleton_zero
      hA hN ν ν₀ hinv hinv₀ hν0 hzero₀
  rw [huniq]
  exact hintegr₀

/-- **Subcritical exponential moments of the stationary law**
(paper `lem:nd-subcritical-exponential-moments`, `eq:nd-subcritical-exponential-moment`).

For every nonzero invariant law `π_{A,N}` of the unrounded vector chain and every
`0 < α < β_{A,N}` (here `α = 2p`),
`𝔼 e^{αY} = 𝔼‖x‖₂^{-α} < ∞`, where `Y = -log‖x‖₂` is the log-polar radial
coordinate. The proof is the paper's: push `π_{A,N}` forward by the squared-radius
map `r_N` (`prop:gaussian-tv-reduction`), apply the Lyapunov/uniqueness argument
on the scalar chain (`integrable_neg_rpow_of_invariant_Kchain`), and pull back
through `‖x‖₂^{-2p} = N^{-p} r_N(x)^{-p}`. -/
theorem integrable_neg_rpow_gaussianEuclideanNorm_of_invariant_Pkernel {A : ℝ}
    (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {p : ℝ} (hp : 0 < p)
    (hpβ : 2 * p < cramerExponent A N) (μ : Measure (Fin N → ℝ))
    [IsProbabilityMeasure μ] (hmu : Kernel.Invariant (Pkernel A N) μ)
    (hmu0 : μ ({0} : Set (Fin N → ℝ)) = 0) :
    Integrable (fun x => (gaussianEuclideanNorm N x) ^ (-(2 * p))) μ := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  haveI : IsProbabilityMeasure (μ.map (radiusSq N)) := by
    constructor
    rw [Measure.map_apply (measurable_radiusSq N) MeasurableSet.univ]
    simp
  -- The squared-radius pushforward is a nonzero invariant law of the scalar chain.
  have hinvν : Kernel.Invariant (Kchain A N) (μ.map (radiusSq N)) :=
    invariant_Kchain_map_radiusSq_of_invariant_Pkernel A N μ hmu
  have hν0 : (μ.map (radiusSq N)) ({0} : Set ℝ) = 0 := by
    rw [map_radiusSq_apply_singleton_zero hN μ]
    exact hmu0
  have hscalar : Integrable (fun y : ℝ => y ^ (-p)) (μ.map (radiusSq N)) :=
    integrable_neg_rpow_of_invariant_Kchain hA hN hsc hp hpβ
      (⟨μ.map (radiusSq N), inferInstance⟩ : ProbabilityMeasure ℝ) hinvν hν0
  -- Pull back along `r_N`.
  have hpull : Integrable (fun x => (radiusSq N x) ^ (-p)) μ :=
    (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y ^ (-p)) (μ.map (radiusSq N)))
      (measurable_radiusSq N).aemeasurable).1 hscalar
  have hconst := hpull.const_mul ((N : ℝ) ^ (-p))
  refine hconst.congr (Filter.Eventually.of_forall fun x => ?_)
  -- `N^{-p} r_N(x)^{-p} = ‖x‖₂^{-2p}`.
  have hS : gaussianSquaredNorm N x = (N : ℝ) * radiusSq N x := by
    unfold gaussianSquaredNorm radiusSq
    field_simp
  have hSnonneg : 0 ≤ gaussianSquaredNorm N x := gaussianSquaredNorm_nonneg N x
  have hrnonneg : 0 ≤ radiusSq N x := by
    rw [hS] at hSnonneg
    nlinarith
  calc (N : ℝ) ^ (-p) * (radiusSq N x) ^ (-p)
      = ((N : ℝ) * radiusSq N x) ^ (-p) := (Real.mul_rpow hNreal.le hrnonneg).symm
    _ = (gaussianSquaredNorm N x) ^ (-p) := by rw [hS]
    _ = (gaussianEuclideanNorm N x) ^ (-(2 * p)) := by
        rw [gaussianEuclideanNorm, Real.sqrt_eq_rpow, ← Real.rpow_mul hSnonneg]
        congr 1
        ring

/-!
### The tilted increment law as a renewal increment law

Feeding `μ̂_{A,N}` into the mini-library. The one computation that does the work
is that the exponential transform of the tilt is a *shift* of the transfer
moment,

  `∫ e^{-θ z} μ̂_{A,N}(dz) = ℳ_{A,N}(β_{A,N} - θ)`,

which at `θ = β_{A,N}` reads `𝔼 e^{-β_{A,N} S_n} = 1` — exactly the identity the
paper uses for the terminal term of the iterated renewal equation ("the equality
uses the defining tilt `eq:nd-tilted-increment-law`") — and for `0 < θ < β_{A,N}`
is `< 1`, which is the Chernoff hypothesis of
`Renewal.renewalMeasure_lt_top_of_expTransform_lt_one`.
-/

/-- `z ↦ e^{-θz}` is integrable against `μ̂_{A,N}` whenever `β_{A,N} - θ` lies in
the increment's exponential-moment window `(-N, N)`: under the tilt the
integrand becomes `e^{(β_{A,N}-θ)Z}`. -/
lemma integrable_exp_neg_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {θ : ℝ}
    (hθ : cramerExponent A N - θ ∈ Set.Ioo (-(N : ℝ)) (N : ℝ)) :
    Integrable (fun z : ℝ => Real.exp (-(θ * z))) (tiltedIncrementLaw A N) := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hmem : cramerExponent A N ∈ Set.Ioo (-(N : ℝ)) (N : ℝ) :=
    ⟨by linarith [hβmem.1], hβmem.2⟩
  have hexp : Integrable
      (fun g => Real.exp (cramerExponent A N * logRadialIncrement A N g))
      (gaussianVec N) := Ioo_subset_integrableExpSet_logRadialIncrement hA hN hmem
  have hI : Integrable
      (fun g => Real.exp ((cramerExponent A N - θ) * logRadialIncrement A N g))
      (gaussianVec N) := Ioo_subset_integrableExpSet_logRadialIncrement hA hN hθ
  rw [tiltedIncrementLaw,
    integrable_map_measure (g := fun z : ℝ => Real.exp (-(θ * z)))
      (by fun_prop : Measurable fun z : ℝ => Real.exp (-(θ * z))).aestronglyMeasurable
      (measurable_logRadialIncrement A N).aemeasurable,
    integrable_tilted_iff hexp]
  refine hI.congr (Filter.Eventually.of_forall fun g => ?_)
  simp only [Function.comp_def, smul_eq_mul, ← Real.exp_add]
  congr 1
  ring

/-- **The tilt shifts the transfer moment**:
`∫ e^{-θz} μ̂_{A,N}(dz) = ℳ_{A,N}(β_{A,N} - θ)`. Immediate from the defining
identity `integral_tiltedIncrementLaw` (whose normalizer is `1`) together with
`gaussianTransferMoment_eq_mgf`. -/
lemma integral_exp_neg_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) (θ : ℝ) :
    ∫ z, Real.exp (-(θ * z)) ∂tiltedIncrementLaw A N
      = gaussianTransferMoment A N (cramerExponent A N - θ) := by
  rw [integral_tiltedIncrementLaw hA hN hsc
      (by fun_prop : Measurable fun z : ℝ => Real.exp (-(θ * z))),
    gaussianTransferMoment_eq_mgf hA hN]
  unfold ProbabilityTheory.mgf logRadialIncrement
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  -- `simp only` beta-reduces first; a bare `rw` cannot see through the redex.
  simp only [← Real.exp_add]
  congr 1
  ring

/-- The mini-library's exponential transform of `μ̂_{A,N}`, in `ℝ≥0∞`. -/
lemma expTransform_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {θ : ℝ}
    (hθ : cramerExponent A N - θ ∈ Set.Ioo (-(N : ℝ)) (N : ℝ)) :
    Renewal.expTransform θ (tiltedIncrementLaw A N)
      = ENNReal.ofReal (gaussianTransferMoment A N (cramerExponent A N - θ)) := by
  rw [Renewal.expTransform_def, ← integral_exp_neg_tiltedIncrementLaw hA hN hsc θ]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_tiltedIncrementLaw hA hN hsc hθ)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm

/-- **`𝔼 e^{-β_{A,N} Z} = 1`**: at the Cramér exponent the transform is exactly
one, because `ℳ_{A,N}(0) = 1`. -/
lemma expTransform_tiltedIncrementLaw_cramerExponent {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) :
    Renewal.expTransform (cramerExponent A N) (tiltedIncrementLaw A N) = 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [expTransform_tiltedIncrementLaw hA hN hsc
      (by rw [Set.mem_Ioo, sub_self]; exact ⟨by linarith, hNpos⟩),
    sub_self, gaussianTransferMoment_zero, ENNReal.ofReal_one]

/-- **`𝔼 e^{-β_{A,N} S_n} = 1` for every `n`** — the identity the paper invokes
when bounding the terminal term `𝔼‖ℋ_{y-S_n}‖_TV` on the event
`{y - S_n > L}`. -/
lemma expTransform_convPow_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) (n : ℕ) :
    Renewal.expTransform (cramerExponent A N)
        (Renewal.convPow (tiltedIncrementLaw A N) n) = 1 := by
  haveI := isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  rw [Renewal.expTransform_convPow,
    expTransform_tiltedIncrementLaw_cramerExponent hA hN hsc, one_pow]

/-- The Chernoff hypothesis holds strictly below the Cramér exponent:
`∫ e^{-θz} μ̂_{A,N}(dz) = ℳ_{A,N}(β_{A,N}-θ) < 1` for `0 < θ < β_{A,N}`. -/
theorem expTransform_tiltedIncrementLaw_lt_one {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {θ : ℝ} (hθ0 : 0 < θ) (hθβ : θ < cramerExponent A N) :
    Renewal.expTransform θ (tiltedIncrementLaw A N) < 1 := by
  have hβmem := cramerExponent_mem hA hN hsc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hθ : cramerExponent A N - θ ∈ Set.Ioo (-(N : ℝ)) (N : ℝ) :=
    ⟨by linarith [hβmem.1, hβmem.2], by linarith [hβmem.2]⟩
  rw [expTransform_tiltedIncrementLaw hA hN hsc hθ]
  exact ENNReal.ofReal_lt_one.2
    (gaussianTransferMoment_lt_one_of_lt_cramerExponent hA hN hsc (by linarith)
      (by linarith))

/-- **The renewal measure of the tilted walk is locally finite.** This is the
standing hypothesis of Blackwell's theorem and of the key renewal theorem, and
it is where the whole first paragraph of `lem:nd-gaussian-renewal` pays off. -/
theorem renewalMeasure_tiltedIncrementLaw_Icc_lt_top {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) (a b : ℝ) :
    Renewal.renewalMeasure (tiltedIncrementLaw A N) (Set.Icc a b) < ∞ := by
  haveI := isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  have hβmem := cramerExponent_mem hA hN hsc
  exact Renewal.renewalMeasure_Icc_lt_top (θ := cramerExponent A N / 2)
    (by linarith [hβmem.1])
    (expTransform_tiltedIncrementLaw_lt_one hA hN hsc (by linarith [hβmem.1])
      (by linarith [hβmem.1])) a b

end AbsorptionCutoff
