/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FirstPassageCLT
import AbsorptionCutoff.Supercritical.LogPolar
import AbsorptionCutoff.Supercritical.PolarPerturbation
import AbsorptionCutoff.Supercritical.StationaryEquation

/-!
# Fixed-width vanishing-mesh cutoff

This module specializes the abstract corrected first-passage profile to the
fixed-dimensional Gaussian log-radius increment. The increment itself and its
radial law are shared with the stationary theory and defined in
`AbsorptionCutoff.Supercritical.StationaryEquation`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Fixed-width subcriticality in the drift formulation used by the Lean
development: the mean logarithm of the linearized radius multiplier is
negative. -/
def FixedWidthSubcritical (A : ℝ) (N : ℕ) : Prop :=
  logRadialDrift A N < 0

/-- Paper-facing fixed-width critical width.  This is the drift
characterization of
`sqrt (N / 2) * exp (-digamma (N / 2) / 2)` used in the manuscript; Mathlib
does not currently provide the digamma function needed to use that closed
form as the definition. -/
noncomputable def fixedWidthCriticalWidth (N : ℕ) : ℝ :=
  Real.exp (-logRadialDrift 1 N)

/-- The paper's positive subcritical drift
`gamma_{A,N} = log (A_c(N) / A)`. -/
noncomputable def fixedWidthGamma (A : ℝ) (N : ℕ) : ℝ :=
  Real.log (fixedWidthCriticalWidth N / A)

/-- Geometric rate arising from half of the negative fixed-width log-radius
drift. -/
noncomputable def fixedWidthGeometricRate (A : ℝ) (N : ℕ) : ℝ :=
  Real.exp (logRadialDrift A N / 2)

lemma fixedWidthGeometricRate_pos (A : ℝ) (N : ℕ) :
    0 < fixedWidthGeometricRate A N := by
  unfold fixedWidthGeometricRate
  positivity

lemma fixedWidthGeometricRate_lt_one
    {A : ℝ} {N : ℕ} (hsub : FixedWidthSubcritical A N) :
    fixedWidthGeometricRate A N < 1 := by
  unfold fixedWidthGeometricRate
  rw [Real.exp_lt_one_iff]
  exact div_neg_of_neg_of_pos hsub (by norm_num)

/-- Deterministic geometric majorant used for the eventual nonlinear loss. -/
noncomputable def fixedWidthLossMajorant
    (A : ℝ) (N : ℕ) (R0 : ℝ) (n : ℕ) : ℝ :=
  2 * (R0 * fixedWidthGeometricRate A N ^ (n + 1)) ^ 2

lemma summable_fixedWidthLossMajorant
    {A : ℝ} {N : ℕ} (hsub : FixedWidthSubcritical A N) (R0 : ℝ) :
    Summable (fixedWidthLossMajorant A N R0) := by
  let q := fixedWidthGeometricRate A N
  have hq0 : 0 < q := fixedWidthGeometricRate_pos A N
  have hq1 : q < 1 := fixedWidthGeometricRate_lt_one hsub
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos hq0)]
    nlinarith [sq_nonneg (q - 1)]
  have hs : Summable (fun n : ℕ ↦ (q ^ 2) ^ n) :=
    summable_geometric_of_norm_lt_one hq2
  have hs' := hs.mul_left (2 * R0 ^ 2 * q ^ 2)
  unfold fixedWidthLossMajorant
  exact hs'.congr fun n => by
    rw [pow_succ, mul_pow, ← pow_mul]
    ring

/-- The mean of the paper's positive first-passage increment is the negative
logarithmic radial drift. -/
lemma integral_logRadialIncrement_eq_neg_logRadialDrift
    (A : ℝ) (N : ℕ) :
    ∫ g, logRadialIncrement A N g ∂gaussianVec N =
      -logRadialDrift A N := by
  unfold logRadialIncrement logRadialDrift
  exact integral_neg _

/-- Fixed-width subcriticality gives the positive drift required by the
first-passage theorem. -/
lemma integral_logRadialIncrement_pos_of_fixedWidthSubcritical
    {A : ℝ} {N : ℕ} (hsub : FixedWidthSubcritical A N) :
    0 < ∫ g, logRadialIncrement A N g ∂gaussianVec N := by
  rw [integral_logRadialIncrement_eq_neg_logRadialDrift]
  exact neg_pos.mpr hsub

/-- The Gaussian log-radius increment is square-integrable in every positive
dimension. -/
lemma memLp_logRadialIncrement_two
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    MemLp (logRadialIncrement A N) 2 (gaussianVec N) := by
  simpa using memLp_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_logRadialIncrement hA hN) (2 : NNReal)

lemma fixedWidthCriticalWidth_pos (N : ℕ) :
    0 < fixedWidthCriticalWidth N := by
  unfold fixedWidthCriticalWidth
  positivity

/-- Changing `A` translates the log-radius increment by the deterministic
constant `-log A`. -/
lemma logRadialIncrement_ae_eq_one_sub_log
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    logRadialIncrement A N =ᵐ[gaussianVec N]
      fun g ↦ logRadialIncrement 1 N g - Real.log A := by
  filter_upwards [ae_gaussianEuclideanNorm_pos hN] with g hg
  have hsqrt : 0 < Real.sqrt (N : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hN)
  unfold logRadialIncrement
  rw [show (A / Real.sqrt (N : ℝ)) * gaussianEuclideanNorm N g =
      A * ((1 / Real.sqrt (N : ℝ)) * gaussianEuclideanNorm N g) by ring,
    Real.log_mul hA.ne' (mul_ne_zero (one_div_ne_zero hsqrt.ne') hg.ne')]
  ring

/-- Scaling the width adds `log A` to the logarithmic radial drift. -/
lemma logRadialDrift_eq_log_add
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    logRadialDrift A N = Real.log A + logRadialDrift 1 N := by
  have hAint := (memLp_logRadialIncrement_two hA hN).integrable one_le_two
  have h1int := (memLp_logRadialIncrement_two zero_lt_one hN).integrable one_le_two
  have hcongr := integral_congr_ae (logRadialIncrement_ae_eq_one_sub_log hA hN)
  rw [integral_sub h1int (integrable_const (Real.log A)),
    integral_logRadialIncrement_eq_neg_logRadialDrift,
    integral_logRadialIncrement_eq_neg_logRadialDrift] at hcongr
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hcongr
  linarith

/-- The paper's inequality `A < A_c(N)` is exactly fixed-width
subcriticality. -/
lemma fixedWidthSubcritical_iff_lt_criticalWidth
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    FixedWidthSubcritical A N ↔ A < fixedWidthCriticalWidth N := by
  rw [FixedWidthSubcritical, logRadialDrift_eq_log_add hA hN]
  constructor
  · intro h
    rw [← Real.log_lt_log_iff hA (fixedWidthCriticalWidth_pos N)]
    simp only [fixedWidthCriticalWidth, Real.log_exp]
    linarith
  · intro h
    rw [← Real.log_lt_log_iff hA (fixedWidthCriticalWidth_pos N)] at h
    simp only [fixedWidthCriticalWidth, Real.log_exp] at h
    linarith

/-- The paper's `gamma_{A,N}` is the negative log-radius drift. -/
lemma fixedWidthGamma_eq_neg_logRadialDrift
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    fixedWidthGamma A N = -logRadialDrift A N := by
  rw [fixedWidthGamma,
    Real.log_div (fixedWidthCriticalWidth_pos N).ne' hA.ne',
    fixedWidthCriticalWidth, Real.log_exp,
    logRadialDrift_eq_log_add hA hN]
  ring

/-- In the subcritical regime the paper's `gamma_{A,N}` is positive. -/
lemma fixedWidthGamma_pos_of_lt_criticalWidth
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hcritical : A < fixedWidthCriticalWidth N) :
    0 < fixedWidthGamma A N := by
  rw [fixedWidthGamma_eq_neg_logRadialDrift hA hN]
  exact neg_pos.mpr
    ((fixedWidthSubcritical_iff_lt_criticalWidth hA hN).2 hcritical)

/-- In positive dimension, the Gaussian log-radius increment is not almost
surely equal to any constant. -/
lemma logRadialIncrement_not_ae_const
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) (c : ℝ) :
    ¬ (∀ᵐ g ∂gaussianVec N, logRadialIncrement A N g = c) := by
  intro hconst
  have hnull :
      gaussianVec N (logRadialIncrement A N ⁻¹' {c})ᶜ = 0 := by
    rw [ae_iff] at hconst
    refine measure_mono_null ?_ hconst
    intro g hg
    simpa using hg
  have hfull :
      gaussianVec N (logRadialIncrement A N ⁻¹' {c}) = 1 :=
    (prob_compl_eq_zero_iff
      ((measurable_logRadialIncrement A N) (measurableSet_singleton c))).mp
        hnull
  rw [measure_preimage_logRadialIncrement_singleton hA hN c] at hfull
  norm_num at hfull

/-- In positive dimension, the Gaussian log-radius increment has strictly
positive variance. -/
lemma variance_logRadialIncrement_pos
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    0 < variance (logRadialIncrement A N) (gaussianVec N) := by
  refine lt_of_le_of_ne
    (variance_nonneg (logRadialIncrement A N) (gaussianVec N)) ?_
  intro hzero
  exact (logRadialIncrement_not_ae_const hA hN
    (∫ g, logRadialIncrement A N g ∂gaussianVec N))
    (ae_eq_integral_of_variance_eq_zero
      (memLp_logRadialIncrement_two hA hN) hzero.symm)

/-- Standard deviation of the fixed-width Gaussian log-radius increment. -/
noncomputable def fixedWidthStdDev (A : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (variance (logRadialIncrement A N) (gaussianVec N))

/-- The paper's `N`-dependent standard deviation
`sigma_N = sqrt (Var (log chi_N))`. -/
noncomputable def fixedWidthSigma (N : ℕ) : ℝ :=
  Real.sqrt
    (variance (fun g : Fin N → ℝ ↦ Real.log (gaussianEuclideanNorm N g))
      (gaussianVec N))

/-- The width-dependent helper standard deviation is the manuscript's
`N`-only quantity `sigma_N`. -/
lemma fixedWidthStdDev_eq_fixedWidthSigma
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    fixedWidthStdDev A N = fixedWidthSigma N := by
  have hscale : 0 < A / Real.sqrt (N : ℝ) := by
    positivity
  have hae : logRadialIncrement A N =ᵐ[gaussianVec N]
      fun g ↦ -Real.log (A / Real.sqrt (N : ℝ)) -
        Real.log (gaussianEuclideanNorm N g) := by
    filter_upwards [ae_gaussianEuclideanNorm_pos hN] with g hg
    unfold logRadialIncrement
    rw [Real.log_mul hscale.ne' hg.ne']
    ring
  unfold fixedWidthStdDev fixedWidthSigma
  congr 1
  calc
    variance (logRadialIncrement A N) (gaussianVec N) =
        variance
          (fun g ↦ -Real.log (A / Real.sqrt (N : ℝ)) -
            Real.log (gaussianEuclideanNorm N g))
          (gaussianVec N) := variance_congr hae
    _ = variance (fun g ↦ Real.log (gaussianEuclideanNorm N g))
          (gaussianVec N) := by
      exact variance_const_sub
        ((measurable_gaussianEuclideanNorm N).log.aestronglyMeasurable)
        (-Real.log (A / Real.sqrt (N : ℝ)))

/-- The fixed-width standard deviation is positive in positive dimension. -/
lemma fixedWidthStdDev_pos
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    0 < fixedWidthStdDev A N :=
  Real.sqrt_pos.2 (variance_logRadialIncrement_pos hA hN)

/-- The variance is the square of `fixedWidthStdDev`, in the orientation
required by the abstract first-passage profile. -/
lemma variance_logRadialIncrement_eq_fixedWidthStdDev_sq
    (A : ℝ) (N : ℕ) :
    variance (logRadialIncrement A N) (gaussianVec N) =
      fixedWidthStdDev A N ^ 2 := by
  unfold fixedWidthStdDev
  rw [Real.sq_sqrt (variance_nonneg _ _)]

/-- Canonical sample space for an iid sequence of standard Gaussian vectors. -/
abbrev fixedWidthSampleSpace (N : ℕ) := ℕ → (Fin N → ℝ)

/-- Countable product law of standard Gaussian vectors. -/
noncomputable def fixedWidthGaussianMeasure (N : ℕ) :
    Measure (fixedWidthSampleSpace N) :=
  Measure.infinitePi (fun _ : ℕ ↦ gaussianVec N)

instance (N : ℕ) : IsProbabilityMeasure (fixedWidthGaussianMeasure N) := by
  unfold fixedWidthGaussianMeasure
  infer_instance

/-- Event that every innovation in the canonical Gaussian sequence is
nonzero. -/
def fixedWidthNonzeroEvent (N : ℕ) : Set (fixedWidthSampleSpace N) :=
  {ω | ∀ n, ω n ≠ 0}

lemma measurableSet_fixedWidthNonzeroEvent (N : ℕ) :
    MeasurableSet (fixedWidthNonzeroEvent N) := by
  have h : MeasurableSet
      (⋂ n : ℕ, (Function.eval n) ⁻¹'
        ({0} : Set (Fin N → ℝ))ᶜ) :=
    MeasurableSet.iInter fun n =>
      ((measurableSet_singleton (0 : Fin N → ℝ)).preimage
        (measurable_pi_apply n)).compl
  convert h using 1
  ext ω
  simp [fixedWidthNonzeroEvent]

/-- In positive dimension the standard product Gaussian assigns zero mass to
the zero vector. -/
lemma gaussianVec_singleton_zero
    {N : ℕ} (hN : 0 < N) :
    gaussianVec N ({0} : Set (Fin N → ℝ)) = 0 := by
  let i : Fin N := ⟨0, hN⟩
  have hev : MeasurePreserving
      (Function.eval i)
      (Measure.pi (fun _ : Fin N ↦ gaussianReal 0 1))
      (gaussianReal 0 1) :=
    MeasureTheory.measurePreserving_eval
      (μ := fun _ : Fin N ↦ gaussianReal 0 1) i
  refine measure_mono_null
    (t := (Function.eval i) ⁻¹' ({0} : Set ℝ)) ?_ ?_
  · intro g hg
    simp only [Set.mem_singleton_iff] at hg
    subst g
    simp
  · unfold gaussianVec
    rw [← Measure.map_apply hev.measurable (measurableSet_singleton 0),
      hev.map_eq]
    exact gaussianReal_singleton_zero

/-- All coordinates of the canonical Gaussian innovation sequence are
simultaneously nonzero almost surely. -/
lemma fixedWidthGaussianMeasure_nonzeroEvent_compl
    {N : ℕ} (hN : 0 < N) :
    fixedWidthGaussianMeasure N (fixedWidthNonzeroEvent N)ᶜ = 0 := by
  change fixedWidthGaussianMeasure N {ω | ¬ ∀ n, ω n ≠ 0} = 0
  rw [← ae_iff, ae_all_iff]
  intro n
  rw [ae_iff]
  have hset :
      {ω : fixedWidthSampleSpace N | ¬ ω n ≠ 0} =
        (Function.eval n) ⁻¹' ({0} : Set (Fin N → ℝ)) := by
    ext ω
    simp
  rw [hset]
  have hev := measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ gaussianVec N) n
  rw [← Measure.map_apply hev.measurable
      (measurableSet_singleton (0 : Fin N → ℝ)),
    fixedWidthGaussianMeasure, hev.map_eq]
  exact gaussianVec_singleton_zero hN

/-- Canonical iid sequence of fixed-width positive first-passage increments. -/
noncomputable def fixedWidthIncrementProcess (A : ℝ) (N : ℕ) :
    ℕ → fixedWidthSampleSpace N → ℝ :=
  fun j ω ↦ logRadialIncrement A N (ω j)

lemma measurable_fixedWidthIncrementProcess (A : ℝ) (N : ℕ) (j : ℕ) :
    Measurable (fixedWidthIncrementProcess A N j) := by
  exact (measurable_logRadialIncrement A N).comp (measurable_pi_apply j)

lemma iIndepFun_fixedWidthIncrementProcess (A : ℝ) (N : ℕ) :
    iIndepFun (fixedWidthIncrementProcess A N) (fixedWidthGaussianMeasure N) := by
  exact iIndepFun_infinitePi
    (P := fun _ : ℕ ↦ gaussianVec N)
    (X := fun _ : ℕ ↦ logRadialIncrement A N)
    (fun _ ↦ measurable_logRadialIncrement A N)

lemma map_fixedWidthIncrementProcess (A : ℝ) (N : ℕ) (j : ℕ) :
    Measure.map (fixedWidthIncrementProcess A N j) (fixedWidthGaussianMeasure N) =
      Measure.map (logRadialIncrement A N) (gaussianVec N) := by
  rw [show fixedWidthIncrementProcess A N j =
      logRadialIncrement A N ∘ Function.eval j from rfl,
    ← Measure.map_map (measurable_logRadialIncrement A N)
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ ↦ gaussianVec N) j).measurable,
    fixedWidthGaussianMeasure,
    (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ gaussianVec N) j).map_eq]

lemma identDistrib_fixedWidthIncrementProcess (A : ℝ) (N : ℕ) (j : ℕ) :
    IdentDistrib (fixedWidthIncrementProcess A N j)
      (fixedWidthIncrementProcess A N 0)
      (fixedWidthGaussianMeasure N) (fixedWidthGaussianMeasure N) := by
  refine ⟨(measurable_fixedWidthIncrementProcess A N j).aemeasurable,
    (measurable_fixedWidthIncrementProcess A N 0).aemeasurable, ?_⟩
  rw [map_fixedWidthIncrementProcess A N j,
    map_fixedWidthIncrementProcess A N 0]

/-- Square-integrability of the canonical coordinate-zero increment. -/
lemma memLp_fixedWidthIncrementProcess_zero
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    MemLp (fixedWidthIncrementProcess A N 0) 2
      (fixedWidthGaussianMeasure N) := by
  have hev : MeasurePreserving
      (fun ω : fixedWidthSampleSpace N ↦ ω 0)
      (fixedWidthGaussianMeasure N) (gaussianVec N) := by
    simpa only [fixedWidthGaussianMeasure] using
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ ↦ gaussianVec N) 0)
  have h := (memLp_logRadialIncrement_two hA hN).comp_measurePreserving hev
  change MemLp
    (fun ω : fixedWidthSampleSpace N ↦ logRadialIncrement A N (ω 0)) 2
      (fixedWidthGaussianMeasure N)
  simpa only [Function.comp_def] using h

/-- Mean of coordinate zero of the canonical increment process. -/
lemma integral_fixedWidthIncrementProcess_zero_eq_neg_logRadialDrift
    (A : ℝ) (N : ℕ) :
    ∫ ω, fixedWidthIncrementProcess A N 0 ω ∂fixedWidthGaussianMeasure N =
      -logRadialDrift A N := by
  rw [← integral_logRadialIncrement_eq_neg_logRadialDrift]
  have hproc := integral_map
    (measurable_fixedWidthIncrementProcess A N 0).aemeasurable
    (aestronglyMeasurable_id :
      AEStronglyMeasurable (id : ℝ → ℝ)
        (Measure.map (fixedWidthIncrementProcess A N 0)
          (fixedWidthGaussianMeasure N)))
  have hrad := integral_map
    (measurable_logRadialIncrement A N).aemeasurable
    (aestronglyMeasurable_id :
      AEStronglyMeasurable (id : ℝ → ℝ)
        (Measure.map (logRadialIncrement A N) (gaussianVec N)))
  rw [map_fixedWidthIncrementProcess A N 0] at hproc
  simpa only [id_eq] using hproc.symm.trans hrad

/-- The mean first-passage increment is exactly the paper's
`gamma_{A,N}`. -/
lemma integral_fixedWidthIncrementProcess_zero_eq_fixedWidthGamma
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    ∫ ω, fixedWidthIncrementProcess A N 0 ω
        ∂fixedWidthGaussianMeasure N = fixedWidthGamma A N := by
  rw [integral_fixedWidthIncrementProcess_zero_eq_neg_logRadialDrift,
    fixedWidthGamma_eq_neg_logRadialDrift hA hN]

lemma integral_fixedWidthIncrementProcess_zero_pos_of_subcritical
    {A : ℝ} {N : ℕ} (hsub : FixedWidthSubcritical A N) :
    0 < ∫ ω, fixedWidthIncrementProcess A N 0 ω
      ∂fixedWidthGaussianMeasure N := by
  rw [integral_fixedWidthIncrementProcess_zero_eq_neg_logRadialDrift]
  exact neg_pos.mpr hsub

/-- Variance of coordinate zero of the canonical increment process. -/
lemma variance_fixedWidthIncrementProcess_zero_eq_stdDev_sq
    (A : ℝ) (N : ℕ) :
    variance (fixedWidthIncrementProcess A N 0) (fixedWidthGaussianMeasure N) =
      fixedWidthStdDev A N ^ 2 := by
  have hev : MeasurePreserving
      (fun ω : fixedWidthSampleSpace N ↦ ω 0)
      (fixedWidthGaussianMeasure N) (gaussianVec N) := by
    simpa only [fixedWidthGaussianMeasure] using
      (measurePreserving_eval_infinitePi
        (fun _ : ℕ ↦ gaussianVec N) 0)
  have hvar := variance_map
    (μ := fixedWidthGaussianMeasure N)
    (X := logRadialIncrement A N)
    (Y := fun ω : fixedWidthSampleSpace N ↦ ω 0)
    (measurable_logRadialIncrement A N).aemeasurable
    (measurable_pi_apply 0).aemeasurable
  rw [hev.map_eq] at hvar
  change variance
      (fun ω : fixedWidthSampleSpace N ↦ logRadialIncrement A N (ω 0))
      (fixedWidthGaussianMeasure N) = fixedWidthStdDev A N ^ 2
  calc
    _ = variance (logRadialIncrement A N ∘
        fun ω : fixedWidthSampleSpace N ↦ ω 0)
        (fixedWidthGaussianMeasure N) := rfl
    _ = variance (logRadialIncrement A N) (gaussianVec N) := hvar.symm
    _ = fixedWidthStdDev A N ^ 2 :=
      variance_logRadialIncrement_eq_fixedWidthStdDev_sq A N

/-- Strong law for the canonical fixed-width increment process, normalized by
the number of increments. -/
lemma ae_tendsto_fixedWidth_partialSum_div
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N) :
    ∀ᵐ ω ∂fixedWidthGaussianMeasure N,
      Tendsto
        (fun n ↦ partialSum (fixedWidthIncrementProcess A N) n ω / (n : ℝ))
        atTop (nhds (-logRadialDrift A N)) := by
  have hInt : Integrable (fixedWidthIncrementProcess A N 0)
      (fixedWidthGaussianMeasure N) :=
    (memLp_fixedWidthIncrementProcess_zero hA hN).integrable (by norm_num)
  have hslln := ProbabilityTheory.strong_law_ae_real
    (fixedWidthIncrementProcess A N) hInt
    (fun i j hij ↦
      (iIndepFun_fixedWidthIncrementProcess A N).indepFun hij)
    (identDistrib_fixedWidthIncrementProcess A N)
  simpa only [partialSum,
    integral_fixedWidthIncrementProcess_zero_eq_neg_logRadialDrift] using hslln

/-- In the fixed-width subcritical regime, the canonical partial sums are
eventually bounded below by half their positive limiting drift. -/
lemma ae_eventually_fixedWidth_halfDrift_mul_le_partialSum
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∀ᵐ ω ∂fixedWidthGaussianMeasure N, ∀ᶠ n : ℕ in atTop,
      (-logRadialDrift A N / 2) * (n : ℝ) ≤
        partialSum (fixedWidthIncrementProcess A N) n ω := by
  filter_upwards [ae_tendsto_fixedWidth_partialSum_div hA hN] with ω hω
  have hm : 0 < -logRadialDrift A N := neg_pos.mpr hsub
  have hevent := hω.eventually
    (Ioi_mem_nhds (show -logRadialDrift A N / 2 <
      -logRadialDrift A N by linarith))
  filter_upwards [hevent, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  exact le_of_lt ((lt_div_iff₀ hnpos).mp hn)

/-- Corrected post-floor first-passage profile for the canonical fixed-width
Gaussian log-radius increment process. -/
lemma tendsto_measureReal_fixedWidthCorrectedFirstPassageTime_gt_postFloorTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (E : ℕ → fixedWidthSampleSpace N → ℝ)
    (Einf : fixedWidthSampleSpace N → ℝ)
    (hEinf : Measurable Einf)
    (hgood : fixedWidthGaussianMeasure N (correctionGoodEvent E Einf)ᶜ = 0)
    (L Ltilde v : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦ (Ltilde r - L r) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ (fixedWidthGaussianMeasure N).real {ω |
        (postFloorTime
            (∫ x, fixedWidthIncrementProcess A N 0 x
              ∂fixedWidthGaussianMeasure N)
            (fixedWidthStdDev A N) a L v r : WithTop ℕ) <
          correctedFirstPassageTime
            (fixedWidthIncrementProcess A N) E (Ltilde r) ω})
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  exact tendsto_measureReal_correctedFirstPassageTime_gt_postFloorTime
    (P := fixedWidthGaussianMeasure N)
    (P' := ProbabilityTheory.gaussianReal 0 1)
    (fixedWidthIncrementProcess A N) E Einf id HasLaw.id
    (measurable_fixedWidthIncrementProcess A N)
    (memLp_fixedWidthIncrementProcess_zero hA hN)
    (iIndepFun_fixedWidthIncrementProcess A N)
    (identDistrib_fixedWidthIncrementProcess A N)
    (integral_fixedWidthIncrementProcess_zero_pos_of_subcritical hsub)
    (fixedWidthStdDev A N) (fixedWidthStdDev_pos hA hN)
    (variance_fixedWidthIncrementProcess_zero_eq_stdDev_sq A N)
    hEinf hgood L Ltilde v a hL hv hlevel

/-- One-step nonlinear loss in logarithmic radius for a current radius `r` and
standard Gaussian innovation `g`. -/
noncomputable def fixedWidthRadiusLoss (A : ℝ) (N : ℕ) (r : ℝ)
    (g : Fin N → ℝ) : ℝ :=
  etaDefect N ((A / Real.sqrt N) * r) g

lemma measurable_fixedWidthRadiusLoss (A : ℝ) (N : ℕ) :
    Measurable
      (fun p : ℝ × (Fin N → ℝ) => fixedWidthRadiusLoss A N p.1 p.2) := by
  unfold fixedWidthRadiusLoss
  exact (measurable_etaDefect N).comp
    ((measurable_fst.const_mul (A / Real.sqrt N)).prodMk measurable_snd)

/-- The nonlinear radius loss is nonnegative whenever the current radius and
Gaussian innovation are nonzero. -/
lemma fixedWidthRadiusLoss_nonneg
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) {g : Fin N → ℝ} (hg : g ≠ 0) :
    0 ≤ fixedWidthRadiusLoss A N r g := by
  have hscale : 0 < (A / Real.sqrt N) * r :=
    mul_pos (div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))) hr
  apply etaDefect_nonneg N hscale
  apply (gaussianEuclideanNorm_eq_zero_iff N _).not.mpr
  apply (tanhVec_eq_zero_iff N _).not.mpr
  exact smul_ne_zero hscale.ne' hg

/-- Local quadratic control of the scalar logarithmic loss. The explicit
constant is convenient for summing the vector loss once the radius is small. -/
lemma log_abs_div_abs_tanh_le_two_sq
    {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 2) :
    Real.log (|x| / |Real.tanh x|) ≤ 2 * x ^ 2 := by
  have ht0 : Real.tanh x ≠ 0 := by
    intro ht
    apply hx0
    rw [← Real.artanh_tanh x, ht, Real.artanh_zero]
  have htx : |Real.tanh x| ≤ |x| :=
    sq_le_sq.mp (tanh_sq_le_sq x)
  have hty : |Real.tanh x| ≤ 1 / 2 := htx.trans hx
  have hkey := abs_artanh_sub_le hty
  rw [Real.artanh_tanh] at hkey
  have hcub : |Real.tanh x| ^ 3 ≤ |x| ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg _) htx 3
  have hdelta : |x| - |Real.tanh x| ≤ (4 / 3 : ℝ) * |x| ^ 3 :=
    (abs_sub_abs_le_abs_sub x (Real.tanh x)).trans
      (hkey.trans (mul_le_mul_of_nonneg_left hcub (by norm_num)))
  have hsq : |x| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hcube : |x| ^ 3 ≤ (1 / 4 : ℝ) * |x| := by
    nlinarith [abs_nonneg x]
  have hlower : (2 / 3 : ℝ) * |x| ≤ |Real.tanh x| := by
    nlinarith
  have htpos : 0 < |Real.tanh x| := abs_pos.mpr ht0
  have hxpos : 0 < |x| := abs_pos.mpr hx0
  have hmul :
      (4 / 3 : ℝ) * |x| ^ 3 ≤
        2 * |x| ^ 2 * |Real.tanh x| := by
    calc
      (4 / 3 : ℝ) * |x| ^ 3 =
          2 * |x| ^ 2 * ((2 / 3 : ℝ) * |x|) := by ring
      _ ≤ 2 * |x| ^ 2 * |Real.tanh x| :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
  have hratio : |x| / |Real.tanh x| - 1 ≤ 2 * |x| ^ 2 := by
    rw [div_sub_one (abs_ne_zero.mpr ht0)]
    exact (div_le_iff₀ htpos).2 (hdelta.trans hmul)
  calc
    Real.log (|x| / |Real.tanh x|) ≤
        |x| / |Real.tanh x| - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hxpos htpos)
    _ ≤ 2 * |x| ^ 2 := hratio
    _ = 2 * x ^ 2 := by rw [sq_abs]

/-- When a vector lies in the radius-`1/2` ball, its Euclidean norm contracts
under coordinatewise `tanh` by at most an exponential quadratic factor. -/
lemma gaussianEuclideanNorm_le_exp_two_sq_mul_tanhVec
    {N : ℕ} {u : Fin N → ℝ}
    (hu : gaussianEuclideanNorm N u ≤ 1 / 2) :
    gaussianEuclideanNorm N u ≤
      Real.exp (2 * gaussianEuclideanNorm N u ^ 2) *
        gaussianEuclideanNorm N (tanhVec N u) := by
  let S := gaussianSquaredNorm N u
  let T := gaussianSquaredNorm N (tanhVec N u)
  have hS : 0 ≤ S := gaussianSquaredNorm_nonneg N u
  have hnormsq : gaussianEuclideanNorm N u ^ 2 = S := by
    unfold gaussianEuclideanNorm
    rw [Real.sq_sqrt hS]
  have hcoordSq (i : Fin N) : u i ^ 2 ≤ S := by
    dsimp [S, gaussianSquaredNorm]
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  have hcoordNorm (i : Fin N) : |u i| ≤ gaussianEuclideanNorm N u := by
    apply (sq_le_sq₀ (abs_nonneg _)
      (by unfold gaussianEuclideanNorm; positivity)).mp
    rw [sq_abs, hnormsq]
    exact hcoordSq i
  have hcoord (i : Fin N) :
      u i ^ 2 ≤
        (Real.exp (2 * S) * |Real.tanh (u i)|) ^ 2 := by
    by_cases hi : u i = 0
    · simp [hi]
    · have hui : |u i| ≤ 1 / 2 := (hcoordNorm i).trans hu
      have hlog := log_abs_div_abs_tanh_le_two_sq hi hui
      have ht0 : Real.tanh (u i) ≠ 0 := by
        intro ht
        apply hi
        rw [← Real.artanh_tanh (u i), ht, Real.artanh_zero]
      have hratioPos : 0 < |u i| / |Real.tanh (u i)| :=
        div_pos (abs_pos.mpr hi) (abs_pos.mpr ht0)
      have hratio :
          |u i| / |Real.tanh (u i)| ≤ Real.exp (2 * S) := by
        rw [← Real.exp_log hratioPos]
        exact Real.exp_le_exp.mpr
          (hlog.trans (by linarith [hcoordSq i]))
      have habs :
          |u i| ≤ Real.exp (2 * S) * |Real.tanh (u i)| := by
        exact (div_le_iff₀ (abs_pos.mpr ht0)).mp hratio
      have hsq := pow_le_pow_left₀ (abs_nonneg (u i)) habs 2
      simpa only [sq_abs] using hsq
  have hsum : S ≤ Real.exp (2 * S) ^ 2 * T := by
    dsimp [S, T, gaussianSquaredNorm, tanhVec]
    calc
      ∑ i, u i ^ 2 ≤
          ∑ i, (Real.exp (2 * gaussianSquaredNorm N u) *
            |Real.tanh (u i)|) ^ 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = Real.exp (2 * gaussianSquaredNorm N u) ^ 2 *
          ∑ i, Real.tanh (u i) ^ 2 := by
        simp only [mul_pow, sq_abs, Finset.mul_sum]
  have hsquares :
      gaussianEuclideanNorm N u ^ 2 ≤
        (Real.exp (2 * gaussianEuclideanNorm N u ^ 2) *
          gaussianEuclideanNorm N (tanhVec N u)) ^ 2 := by
    rw [mul_pow, hnormsq]
    unfold gaussianEuclideanNorm
    rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N (tanhVec N u))]
    simpa only [S, T] using hsum
  exact (sq_le_sq₀
    (by unfold gaussianEuclideanNorm; positivity)
    (mul_nonneg (Real.exp_pos _).le
      (by unfold gaussianEuclideanNorm; positivity))).mp hsquares

/-- The nonlinear log-radius defect is locally bounded by twice the squared
linearized input norm. -/
lemma etaDefect_le_two_sq
    (N : ℕ) {r : ℝ} (hr : 0 < r) {v : Fin N → ℝ} (hv : v ≠ 0)
    (hsmall : r * gaussianEuclideanNorm N v ≤ 1 / 2) :
    etaDefect N r v ≤ 2 * (r * gaussianEuclideanNorm N v) ^ 2 := by
  have hnormu :
      gaussianEuclideanNorm N (r • v) =
        r * gaussianEuclideanNorm N v := by
    rw [gaussianEuclideanNorm_smul, abs_of_pos hr]
  have huSmall :
      gaussianEuclideanNorm N (r • v) ≤ 1 / 2 := by
    rwa [hnormu]
  have hbound :=
    gaussianEuclideanNorm_le_exp_two_sq_mul_tanhVec huSmall
  have hu0 : r • v ≠ 0 := smul_ne_zero hr.ne' hv
  have huPos : 0 < gaussianEuclideanNorm N (r • v) :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity)
      (Ne.symm ((gaussianEuclideanNorm_eq_zero_iff N _).not.mpr hu0))
  have ht0 : tanhVec N (r • v) ≠ 0 :=
    (tanhVec_eq_zero_iff N _).not.mpr hu0
  have htPos :
      0 < gaussianEuclideanNorm N (tanhVec N (r • v)) :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity)
      (Ne.symm ((gaussianEuclideanNorm_eq_zero_iff N _).not.mpr ht0))
  unfold etaDefect
  rw [← hnormu]
  exact (Real.log_le_iff_le_exp (div_pos huPos htPos)).2
    ((div_le_iff₀ htPos).2 hbound)

/-- Local quadratic upper bound for the fixed-width one-step radius loss. -/
lemma fixedWidthRadiusLoss_le_two_sq
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) {g : Fin N → ℝ} (hg : g ≠ 0)
    (hsmall : ((A / Real.sqrt N) * r) *
      gaussianEuclideanNorm N g ≤ 1 / 2) :
    fixedWidthRadiusLoss A N r g ≤
      2 * (((A / Real.sqrt N) * r) *
        gaussianEuclideanNorm N g) ^ 2 := by
  unfold fixedWidthRadiusLoss
  exact etaDefect_le_two_sq N
    (mul_pos (div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))) hr)
    hg hsmall

/-- One nonlinear radius update splits exactly into the linearized
log-radius increment and the nonlinear loss. -/
lemma neg_log_fixedWidthRadiusStep
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {r : ℝ} (hr : 0 < r) {g : Fin N → ℝ} (hg : g ≠ 0) :
    -Real.log (gaussianEuclideanNorm N
        (tanhVec N (((A / Real.sqrt N) * r) • g))) =
      -Real.log r + logRadialIncrement A N g +
        fixedWidthRadiusLoss A N r g := by
  have hc : 0 < A / Real.sqrt N :=
    div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))
  have hscale : 0 < (A / Real.sqrt N) * r := mul_pos hc hr
  have hgnorm : gaussianEuclideanNorm N g ≠ 0 :=
    (gaussianEuclideanNorm_eq_zero_iff N g).not.mpr hg
  have hnext : gaussianEuclideanNorm N
      (tanhVec N (((A / Real.sqrt N) * r) • g)) ≠ 0 := by
    apply (gaussianEuclideanNorm_eq_zero_iff N _).not.mpr
    apply (tanhVec_eq_zero_iff N _).not.mpr
    exact smul_ne_zero hscale.ne' hg
  unfold logRadialIncrement fixedWidthRadiusLoss etaDefect
  rw [Real.log_div (mul_ne_zero hscale.ne' hgnorm) hnext,
    Real.log_mul hscale.ne' hgnorm,
    Real.log_mul hc.ne' hr.ne', Real.log_mul hc.ne' hgnorm]
  ring

/-- Canonical unrounded radius recursion driven by the product-space Gaussian
innovations. -/
noncomputable def fixedWidthRadiusPath (A : ℝ) (N : ℕ) (R0 : ℝ) :
    ℕ → fixedWidthSampleSpace N → ℝ
  | 0 => fun _ => R0
  | n + 1 => fun ω =>
      gaussianEuclideanNorm N
        (tanhVec N
          (((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) • ω n))

lemma measurable_fixedWidthRadiusPath
    (A : ℝ) (N : ℕ) (R0 : ℝ) (n : ℕ) :
    Measurable (fixedWidthRadiusPath A N R0 n) := by
  induction n with
  | zero =>
      simp only [fixedWidthRadiusPath]
      fun_prop
  | succ n ih =>
      simp only [fixedWidthRadiusPath]
      exact (measurable_gaussianEuclideanNorm N).comp
        ((measurable_tanhVec N).comp
          ((ih.const_mul (A / Real.sqrt N)).smul (measurable_pi_apply n)))

/-- On a path of nonzero innovations, a positive initial radius remains
positive at every finite time. -/
lemma fixedWidthRadiusPath_pos
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {R0 : ℝ} (hR0 : 0 < R0) {ω : fixedWidthSampleSpace N}
    (hω : ∀ n, ω n ≠ 0) (n : ℕ) :
    0 < fixedWidthRadiusPath A N R0 n ω := by
  induction n with
  | zero => simpa only [fixedWidthRadiusPath] using hR0
  | succ n ih =>
      simp only [fixedWidthRadiusPath]
      have hscale :
          0 < (A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω :=
        mul_pos (div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))) ih
      have htanh : tanhVec N
          (((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) • ω n) ≠ 0 :=
        (tanhVec_eq_zero_iff N _).not.mpr
          (smul_ne_zero hscale.ne' (hω n))
      have hnorm : gaussianEuclideanNorm N
          (tanhVec N
            (((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) • ω n)) ≠
          0 :=
        (gaussianEuclideanNorm_eq_zero_iff N _).not.mpr htanh
      exact lt_of_le_of_ne
        (by unfold gaussianEuclideanNorm; positivity) (Ne.symm hnorm)

/-- The nonlinear radius path is dominated by the product of its linearized
multipliers, written as the exponential of the negative increment sum. -/
lemma fixedWidthRadiusPath_le_initial_mul_exp_neg_partialSum
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {R0 : ℝ} (hR0 : 0 < R0) {ω : fixedWidthSampleSpace N}
    (hω : ∀ n, ω n ≠ 0) (n : ℕ) :
    fixedWidthRadiusPath A N R0 n ω ≤
      R0 * Real.exp (-partialSum (fixedWidthIncrementProcess A N) n ω) := by
  induction n with
  | zero =>
      simp [fixedWidthRadiusPath]
  | succ n ih =>
      have hc : 0 < A / Real.sqrt N :=
        div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN))
      have hr := fixedWidthRadiusPath_pos hA hN hR0 hω n
      have hm : 0 < (A / Real.sqrt N) *
          gaussianEuclideanNorm N (ω n) := by
        apply mul_pos hc
        exact lt_of_le_of_ne
          (by unfold gaussianEuclideanNorm; positivity)
          (Ne.symm ((gaussianEuclideanNorm_eq_zero_iff N _).not.mpr (hω n)))
      have hstep : fixedWidthRadiusPath A N R0 (n + 1) ω ≤
          ((A / Real.sqrt N) * gaussianEuclideanNorm N (ω n)) *
            fixedWidthRadiusPath A N R0 n ω := by
        simp only [fixedWidthRadiusPath]
        have htanh := gaussianEuclideanNorm_tanhVec_le N
          (((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) • ω n)
        rw [gaussianEuclideanNorm_smul,
          abs_of_pos (mul_pos hc hr)] at htanh
        nlinarith
      calc
        fixedWidthRadiusPath A N R0 (n + 1) ω ≤
            ((A / Real.sqrt N) * gaussianEuclideanNorm N (ω n)) *
              fixedWidthRadiusPath A N R0 n ω := hstep
        _ ≤ ((A / Real.sqrt N) * gaussianEuclideanNorm N (ω n)) *
              (R0 * Real.exp
                (-partialSum (fixedWidthIncrementProcess A N) n ω)) :=
          mul_le_mul_of_nonneg_left ih hm.le
        _ = R0 * Real.exp
              (-partialSum (fixedWidthIncrementProcess A N) (n + 1) ω) := by
          rw [partialSum_succ]
          unfold fixedWidthIncrementProcess logRadialIncrement
          have hexp :
              -(partialSum (fun j ω ↦
                  -Real.log ((A / Real.sqrt N) *
                    gaussianEuclideanNorm N (ω j))) n ω +
                -Real.log ((A / Real.sqrt N) *
                  gaussianEuclideanNorm N (ω n))) =
                -partialSum (fun j ω ↦
                  -Real.log ((A / Real.sqrt N) *
                    gaussianEuclideanNorm N (ω j))) n ω +
                  Real.log ((A / Real.sqrt N) *
                    gaussianEuclideanNorm N (ω n)) := by
            ring
          rw [hexp, Real.exp_add, Real.exp_log hm]
          ring

/-- The norm of the linearized input at step `n` is controlled by the same
product bound, now through the partial sum at time `n + 1`. -/
lemma fixedWidthLinearizedInput_le_initial_mul_exp_neg_partialSum_succ
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {R0 : ℝ} (hR0 : 0 < R0) {ω : fixedWidthSampleSpace N}
    (hω : ∀ n, ω n ≠ 0) (n : ℕ) :
    ((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) *
        gaussianEuclideanNorm N (ω n) ≤
      R0 * Real.exp
        (-partialSum (fixedWidthIncrementProcess A N) (n + 1) ω) := by
  have hm : 0 < (A / Real.sqrt N) *
      gaussianEuclideanNorm N (ω n) := by
    apply mul_pos (div_pos hA (Real.sqrt_pos.mpr (by exact_mod_cast hN)))
    exact lt_of_le_of_ne
      (by unfold gaussianEuclideanNorm; positivity)
      (Ne.symm ((gaussianEuclideanNorm_eq_zero_iff N _).not.mpr (hω n)))
  calc
    ((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) *
        gaussianEuclideanNorm N (ω n) =
        ((A / Real.sqrt N) * gaussianEuclideanNorm N (ω n)) *
          fixedWidthRadiusPath A N R0 n ω := by ring
    _ ≤ ((A / Real.sqrt N) * gaussianEuclideanNorm N (ω n)) *
          (R0 * Real.exp
            (-partialSum (fixedWidthIncrementProcess A N) n ω)) :=
      mul_le_mul_of_nonneg_left
        (fixedWidthRadiusPath_le_initial_mul_exp_neg_partialSum
          hA hN hR0 hω n) hm.le
    _ = R0 * Real.exp
          (-partialSum (fixedWidthIncrementProcess A N) (n + 1) ω) := by
      rw [partialSum_succ]
      unfold fixedWidthIncrementProcess logRadialIncrement
      have hexp :
          -(partialSum (fun j ω ↦
              -Real.log ((A / Real.sqrt N) *
                gaussianEuclideanNorm N (ω j))) n ω +
            -Real.log ((A / Real.sqrt N) *
              gaussianEuclideanNorm N (ω n))) =
            -partialSum (fun j ω ↦
              -Real.log ((A / Real.sqrt N) *
                gaussianEuclideanNorm N (ω j))) n ω +
              Real.log ((A / Real.sqrt N) *
                gaussianEuclideanNorm N (ω n)) := by
        ring
      rw [hexp, Real.exp_add, Real.exp_log hm]
      ring

/-- Almost surely, the nonlinear one-step losses are eventually bounded by
the deterministic summable geometric envelope. -/
lemma ae_eventually_fixedWidthRadiusLoss_le_majorant
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    {R0 : ℝ} (hR0 : 0 < R0) :
    ∀ᵐ ω ∂fixedWidthGaussianMeasure N, ∀ᶠ n : ℕ in atTop,
      fixedWidthRadiusLoss A N (fixedWidthRadiusPath A N R0 n ω) (ω n) ≤
        fixedWidthLossMajorant A N R0 n := by
  let q := fixedWidthGeometricRate A N
  have hq0 : 0 < q := fixedWidthGeometricRate_pos A N
  have hq1 : q < 1 := fixedWidthGeometricRate_lt_one hsub
  have hgeom : Tendsto (fun n : ℕ ↦ R0 * q ^ (n + 1)) atTop (nhds 0) :=
    by
      simpa only [Function.comp_apply, mul_zero] using
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).comp
          (tendsto_add_atTop_nat 1)).const_mul R0
  have hsmall : ∀ᶠ n : ℕ in atTop, R0 * q ^ (n + 1) < 1 / 2 :=
    hgeom.eventually (Iio_mem_nhds (by norm_num))
  have hnz : ∀ᵐ ω ∂fixedWidthGaussianMeasure N, ∀ n, ω n ≠ 0 := by
    rw [ae_iff]
    have hset :
        {ω : fixedWidthSampleSpace N | ¬ ∀ n, ω n ≠ 0} =
          (fixedWidthNonzeroEvent N)ᶜ := by
      ext ω
      simp only [fixedWidthNonzeroEvent, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [hset]
    exact fixedWidthGaussianMeasure_nonzeroEvent_compl hN
  filter_upwards [hnz,
    ae_eventually_fixedWidth_halfDrift_mul_le_partialSum hA hN hsub]
      with ω hω hhalf
  have hhalfSucc := (tendsto_add_atTop_nat 1).eventually hhalf
  filter_upwards [hhalfSucc, hsmall] with n hS hsmalln
  have hinput :
      ((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) *
          gaussianEuclideanNorm N (ω n) ≤ R0 * q ^ (n + 1) := by
    calc
      ((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) *
          gaussianEuclideanNorm N (ω n) ≤
          R0 * Real.exp
            (-partialSum (fixedWidthIncrementProcess A N) (n + 1) ω) :=
        fixedWidthLinearizedInput_le_initial_mul_exp_neg_partialSum_succ
          hA hN hR0 hω n
      _ ≤ R0 * Real.exp
            (logRadialDrift A N / 2 * ((n + 1 : ℕ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hR0.le
        nlinarith
      _ = R0 * q ^ (n + 1) := by
        unfold q fixedWidthGeometricRate
        rw [← Real.exp_nat_mul]
        congr 2
        ring
  have hinputSmall :
      ((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) *
          gaussianEuclideanNorm N (ω n) ≤ 1 / 2 :=
    hinput.trans hsmalln.le
  have hloss := fixedWidthRadiusLoss_le_two_sq hA hN
    (fixedWidthRadiusPath_pos hA hN hR0 hω n) (hω n) hinputSmall
  have hinputNonneg :
      0 ≤ ((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) *
        gaussianEuclideanNorm N (ω n) :=
    mul_nonneg
      (mul_nonneg
        (div_nonneg hA.le (Real.sqrt_nonneg _))
        (fixedWidthRadiusPath_pos hA hN hR0 hω n).le)
      (by unfold gaussianEuclideanNorm; positivity)
  have hsq :
      (((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) *
          gaussianEuclideanNorm N (ω n)) ^ 2 ≤
        (R0 * q ^ (n + 1)) ^ 2 :=
    pow_le_pow_left₀ hinputNonneg hinput 2
  calc
    fixedWidthRadiusLoss A N (fixedWidthRadiusPath A N R0 n ω) (ω n) ≤
        2 * (((A / Real.sqrt N) * fixedWidthRadiusPath A N R0 n ω) *
          gaussianEuclideanNorm N (ω n)) ^ 2 := hloss
    _ ≤ 2 * (R0 * q ^ (n + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = fixedWidthLossMajorant A N R0 n := by
      rfl

/-- Cumulative nonlinear loss along the canonical radius path. -/
noncomputable def fixedWidthCorrection
    (A : ℝ) (N : ℕ) (R0 : ℝ) :
    ℕ → fixedWidthSampleSpace N → ℝ :=
  fun n ω ↦ ∑ j ∈ Finset.range n,
    fixedWidthRadiusLoss A N (fixedWidthRadiusPath A N R0 j ω) (ω j)

lemma measurable_fixedWidthCorrection
    (A : ℝ) (N : ℕ) (R0 : ℝ) (n : ℕ) :
    Measurable (fixedWidthCorrection A N R0 n) := by
  unfold fixedWidthCorrection
  apply Finset.measurable_sum
  intro j _
  exact (measurable_fixedWidthRadiusLoss A N).comp
    ((measurable_fixedWidthRadiusPath A N R0 j).prodMk
      (measurable_pi_apply j))

lemma fixedWidthCorrection_nonneg
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {R0 : ℝ} (hR0 : 0 < R0) {ω : fixedWidthSampleSpace N}
    (hω : ∀ n, ω n ≠ 0) (n : ℕ) :
    0 ≤ fixedWidthCorrection A N R0 n ω := by
  unfold fixedWidthCorrection
  exact Finset.sum_nonneg fun j _ ↦
    fixedWidthRadiusLoss_nonneg hA hN
      (fixedWidthRadiusPath_pos hA hN hR0 hω j) (hω j)

lemma monotone_fixedWidthCorrection
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {R0 : ℝ} (hR0 : 0 < R0) {ω : fixedWidthSampleSpace N}
    (hω : ∀ n, ω n ≠ 0) :
    Monotone (fun n ↦ fixedWidthCorrection A N R0 n ω) := by
  intro m n hmn
  unfold fixedWidthCorrection
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun j _ _ ↦ fixedWidthRadiusLoss_nonneg hA hN
      (fixedWidthRadiusPath_pos hA hN hR0 hω j) (hω j))

/-- Exact pathwise decomposition of the negative log radius into its initial
value, the linearized partial sum, and the cumulative nonlinear correction. -/
lemma neg_log_fixedWidthRadiusPath_eq
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {R0 : ℝ} (hR0 : 0 < R0) {ω : fixedWidthSampleSpace N}
    (hω : ∀ n, ω n ≠ 0) (n : ℕ) :
    -Real.log (fixedWidthRadiusPath A N R0 n ω) =
      -Real.log R0 + partialSum (fixedWidthIncrementProcess A N) n ω +
        fixedWidthCorrection A N R0 n ω := by
  induction n with
  | zero =>
      simp [fixedWidthRadiusPath, fixedWidthCorrection]
  | succ n ih =>
      calc
        -Real.log (fixedWidthRadiusPath A N R0 (n + 1) ω) =
            -Real.log (fixedWidthRadiusPath A N R0 n ω) +
              fixedWidthIncrementProcess A N n ω +
                fixedWidthRadiusLoss A N
                  (fixedWidthRadiusPath A N R0 n ω) (ω n) := by
          simpa only [fixedWidthRadiusPath, fixedWidthIncrementProcess] using
            neg_log_fixedWidthRadiusStep hA hN
              (fixedWidthRadiusPath_pos hA hN hR0 hω n) (hω n)
        _ = -Real.log R0 +
              partialSum (fixedWidthIncrementProcess A N) (n + 1) ω +
                fixedWidthCorrection A N R0 (n + 1) ω := by
          rw [ih, partialSum_succ]
          simp only [fixedWidthCorrection, Finset.sum_range_succ]
          ring

end AbsorptionCutoff
