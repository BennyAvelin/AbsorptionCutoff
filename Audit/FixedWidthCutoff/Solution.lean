/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.MainTheorems

/-!
# Solution to the fixed-width vanishing-mesh cutoff challenge

This file repeats, verbatim, the statement vocabulary and the theorem of
`Audit/FixedWidthCutoff/Challenge.lean`, and proves the theorem from the
development's public index `AbsorptionCutoff.MainTheorems`.

Each audit definition is a literal copy of its project counterpart, so the bridge
lemmas below all hold by `rfl`; they are stated explicitly rather than left to
unification so that any future drift between the two vocabularies fails loudly
here instead of silently changing what the comparator checks.
-/

namespace AbsorptionCutoff.StatementAudit.FixedWidthCutoff

open Filter MeasureTheory ProbabilityTheory Topology

noncomputable section

/-! ## Total variation -/

/-- Total-variation distance `‖μ − ν‖_TV = sup_B |μ(B) − ν(B)|` over measurable `B`. -/
def tvDist {E : Type*} [MeasurableSpace E] (μ ν : Measure E) : ℝ :=
  ⨆ s : {s : Set E // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|

/-! ## Nearest-grid rounding -/

/-- Scalar nearest-integer rounding on the unit grid, ties broken toward the grid
point of smaller absolute value (round half toward zero). -/
def Q₁ (u : ℝ) : ℤ :=
  if 0 ≤ u then ⌈u - 2⁻¹⌉ else -⌈-u - 2⁻¹⌉

lemma measurable_Q₁ : Measurable Q₁ := by
  unfold Q₁
  apply Measurable.ite (measurableSet_le measurable_const measurable_id)
  · exact Int.measurable_ceil.comp (measurable_id.sub measurable_const)
  · exact (Int.measurable_ceil.comp (measurable_id.neg.sub measurable_const)).neg

/-- Scalar rounding to the grid `ρℤ`. -/
def gridRound (ρ u : ℝ) : ℝ := ρ * (Q₁ (u / ρ) : ℝ)

/-- Coordinatewise vector rounding to `(ρℤ)^N`. -/
def Qρ (ρ : ℝ) {N : ℕ} (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => gridRound ρ (x i)

lemma measurable_Qρ (ρ : ℝ) (N : ℕ) : Measurable (Qρ ρ : (Fin N → ℝ) → Fin N → ℝ) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Qρ gridRound
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  have hdiv : Measurable (fun x : Fin N → ℝ => x i / ρ) :=
    (measurable_pi_apply i).div measurable_const
  exact measurable_const.mul
    (hcast.comp (measurable_Q₁.comp hdiv))

/-! ## The rounded vector chain -/

/-- `tanh` is continuous; built from `sinh / cosh`. -/
lemma continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-- Standard Gaussian measure on `ℝ^N`. -/
def gaussianVec (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (N : ℕ) : IsProbabilityMeasure (gaussianVec N) := by
  unfold gaussianVec; infer_instance

/-- Entry variance `A²/N` of the Gaussian weight matrix. -/
def weightVar (A : ℝ) (N : ℕ) : NNReal := (A ^ 2 / N).toNNReal

/-- The Gaussian weight-matrix law: independent entries `∼ 𝒩(0, A²/N)`. -/
def gaussianMat (A : ℝ) (N : ℕ) : Measure (Fin N → Fin N → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 (weightVar A N)))

instance (A : ℝ) (N : ℕ) : IsProbabilityMeasure (gaussianMat A N) := by
  unfold gaussianMat; infer_instance

/-- The vector step map `tanh(𝖶x)`, applied coordinatewise. -/
def Pstep (N : ℕ) (x : Fin N → ℝ) (W : Fin N → Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.tanh (∑ j, W i j * x j)

lemma measurable_Pstep (N : ℕ) :
    Measurable (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) => Pstep N p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Pstep
  apply continuous_tanh.measurable.comp
  apply Finset.measurable_sum
  intro j _
  fun_prop

/-- The rounded vector step map: take a `tanh(𝖶x)` step, then round to `(ρℤ)^N`. -/
def roundedPstep
    (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) (W : Fin N → Fin N → ℝ) : Fin N → ℝ :=
  Qρ ρ (Pstep N x W)

lemma measurable_roundedPstep (ρ : ℝ) (N : ℕ) :
    Measurable
      (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) =>
        roundedPstep ρ N p.1 p.2) :=
  (measurable_Qρ ρ N).comp (measurable_Pstep N)

/-- The rounded vector transition kernel. The zero grid bin is absorbing. -/
def roundedPkernel
    (A ρ : ℝ) (N : ℕ) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  Kernel.map
    ((Kernel.deterministic id measurable_id).prod (Kernel.const _ (gaussianMat A N)))
    (fun p => roundedPstep ρ N p.1 p.2)

instance (A ρ : ℝ) (N : ℕ) : IsMarkovKernel (roundedPkernel A ρ N) := by
  unfold roundedPkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_roundedPstep ρ N)

/-! ## Log-radial increments -/

/-- Squared Euclidean norm on `Fin N → ℝ` (whose default norm is the sup norm). -/
def gaussianSquaredNorm (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  ∑ i, (g i) ^ 2

/-- Euclidean norm on `Fin N → ℝ`. -/
def gaussianEuclideanNorm (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  Real.sqrt (gaussianSquaredNorm N g)

/-- The log-radial increment `−log((A/√N)‖g‖)`. -/
def logRadialIncrement (A : ℝ) (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  -Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g)

/-- The log-radial drift `E[log((A/√N)‖G‖)]`. -/
def logRadialDrift (A : ℝ) (N : ℕ) : ℝ :=
  ∫ g, Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ∂gaussianVec N

/-- Fixed-width subcriticality: the log-radial drift is negative. -/
def FixedWidthSubcritical (A : ℝ) (N : ℕ) : Prop :=
  logRadialDrift A N < 0

/-! ## The canonical innovation sequence -/

/-- Sample space of the canonical innovation sequence. -/
abbrev fixedWidthSampleSpace (N : ℕ) := ℕ → (Fin N → ℝ)

/-- Countable product law of standard Gaussian vectors. -/
def fixedWidthGaussianMeasure (N : ℕ) :
    Measure (fixedWidthSampleSpace N) :=
  Measure.infinitePi (fun _ : ℕ ↦ gaussianVec N)

instance (N : ℕ) : IsProbabilityMeasure (fixedWidthGaussianMeasure N) := by
  unfold fixedWidthGaussianMeasure
  infer_instance

/-- Standard deviation of the log-radial increment. -/
def fixedWidthStdDev (A : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt (variance (logRadialIncrement A N) (gaussianVec N))

/-- The log-radial increment process on the canonical sample space. -/
def fixedWidthIncrementProcess (A : ℝ) (N : ℕ) :
    ℕ → fixedWidthSampleSpace N → ℝ :=
  fun j ω ↦ logRadialIncrement A N (ω j)

/-! ## The canonical observation time -/

/-- The canonical real observation time `L/μ + (aσ/μ^{3/2})√L + q`. -/
def canonicalTimeArgument
    (μ σ a : ℝ) (L q : ℕ → ℝ) (r : ℕ) : ℝ :=
  L r / μ + (a * σ / (μ * Real.sqrt μ)) * Real.sqrt (L r) + q r

/-- Canonical natural-valued observation time, negative arguments clamped to zero. -/
def canonicalTime
    (μ σ a : ℝ) (L q : ℕ → ℝ) (r : ℕ) : ℕ :=
  ⌊canonicalTimeArgument μ σ a L q r⌋₊

/-- The manuscript's initial-state logarithmic mesh scale `log(R₀ / ρ r)`. -/
def fixedWidthInitialLogMeshScale
    (R₀ : ℝ) (ρ : ℕ → ℝ) (r : ℕ) : ℝ :=
  Real.log (R₀ / ρ r)

/-! ## Bridges to the development

Each audit definition was copied verbatim from its source module, so every bridge
is `rfl`. Stating them makes any future divergence a build error. -/

lemma tvDist_eq {E : Type*} [MeasurableSpace E] (mu nu : Measure E) :
    tvDist mu nu = AbsorptionCutoff.tvDist mu nu := rfl

lemma Q₁_eq : Q₁ = AbsorptionCutoff.Q₁ := rfl

lemma gridRound_eq : gridRound = AbsorptionCutoff.gridRound := rfl

lemma Qρ_eq (ρ : ℝ) (N : ℕ) :
    (Qρ ρ : (Fin N → ℝ) → Fin N → ℝ) = AbsorptionCutoff.Qρ ρ := rfl

lemma gaussianVec_eq (N : ℕ) : gaussianVec N = AbsorptionCutoff.gaussianVec N := rfl

lemma weightVar_eq (A : ℝ) (N : ℕ) : weightVar A N = AbsorptionCutoff.weightVar A N := rfl

lemma gaussianMat_eq (A : ℝ) (N : ℕ) : gaussianMat A N = AbsorptionCutoff.gaussianMat A N := rfl

lemma Pstep_eq (N : ℕ) : Pstep N = AbsorptionCutoff.Pstep N := rfl

lemma roundedPstep_eq (ρ : ℝ) (N : ℕ) :
    roundedPstep ρ N = AbsorptionCutoff.roundedPstep ρ N := rfl

lemma roundedPkernel_eq (A ρ : ℝ) (N : ℕ) :
    roundedPkernel A ρ N = AbsorptionCutoff.roundedPkernel A ρ N := rfl

lemma gaussianSquaredNorm_eq (N : ℕ) :
    gaussianSquaredNorm N = AbsorptionCutoff.gaussianSquaredNorm N := rfl

lemma gaussianEuclideanNorm_eq (N : ℕ) :
    gaussianEuclideanNorm N = AbsorptionCutoff.gaussianEuclideanNorm N := rfl

lemma logRadialIncrement_eq (A : ℝ) (N : ℕ) :
    logRadialIncrement A N = AbsorptionCutoff.logRadialIncrement A N := rfl

lemma logRadialDrift_eq (A : ℝ) (N : ℕ) :
    logRadialDrift A N = AbsorptionCutoff.logRadialDrift A N := rfl

lemma FixedWidthSubcritical_eq (A : ℝ) (N : ℕ) :
    FixedWidthSubcritical A N = AbsorptionCutoff.FixedWidthSubcritical A N := rfl

lemma fixedWidthGaussianMeasure_eq (N : ℕ) :
    fixedWidthGaussianMeasure N = AbsorptionCutoff.fixedWidthGaussianMeasure N := rfl

lemma fixedWidthStdDev_eq (A : ℝ) (N : ℕ) :
    fixedWidthStdDev A N = AbsorptionCutoff.fixedWidthStdDev A N := rfl

lemma fixedWidthIncrementProcess_eq (A : ℝ) (N : ℕ) :
    fixedWidthIncrementProcess A N = AbsorptionCutoff.fixedWidthIncrementProcess A N := rfl

lemma canonicalTimeArgument_eq :
    canonicalTimeArgument = AbsorptionCutoff.canonicalTimeArgument := rfl

lemma canonicalTime_eq : canonicalTime = AbsorptionCutoff.canonicalTime := rfl

lemma fixedWidthInitialLogMeshScale_eq :
    fixedWidthInitialLogMeshScale = AbsorptionCutoff.fixedWidthInitialLogMeshScale := rfl

/-! ## The theorem under audit -/

/-- **Fixed-width vanishing-mesh cutoff** (paper
`thm:rounded-gaussian-nearest-cutoff`). In fixed positive dimension `N` and
subcritical fixed width `A`, started from any `x₀ ≠ 0`, along any positive mesh
sequence `ρ r → 0⁺`, the total-variation distance of the rounded chain from the
absorbing origin at the canonical time with Gaussian offset `a` converges to
`Φ(−a)`. -/
theorem rounded_gaussian_nearest_cutoff
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (ρ : ℕ → ℝ) (hρpos : ∀ r, 0 < ρ r)
    (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0)))
    (a : ℝ) :
    Tendsto
      (fun r ↦
        tvDist
          (((roundedPkernel A (ρ r) N) ^
            (canonicalTime
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N)
              (fixedWidthStdDev A N) a
              (fixedWidthInitialLogMeshScale
                (gaussianEuclideanNorm N x0) ρ) 0 r))
            (Qρ (ρ r) x0))
          (Measure.dirac (0 : Fin N → ℝ)))
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a)))
:=
  AbsorptionCutoff.MainTheorems.rounded_gaussian_nearest_cutoff hA hN hsub x0 hx0 ρ hρpos hρ a

end

end AbsorptionCutoff.StatementAudit.FixedWidthCutoff
