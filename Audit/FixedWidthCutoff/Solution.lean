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

Each audit definition, including the complete cutoff admissibility and limit
conditions, is a literal copy of its project counterpart, so the bridge
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

/-- The two early/late limiting conditions in the windowed cutoff convention. -/
def HasCutoffLimits (d : ℕ → ℕ → ℝ) (tCut w : ℕ → ℝ) : Prop :=
  Tendsto (fun c : ℝ => liminf (fun n => d n ⌊tCut n - c * w n⌋₊) atTop) atTop (nhds 1) ∧
  Tendsto (fun c : ℝ => limsup (fun n => d n ⌊tCut n + c * w n⌋₊) atTop) atTop (nhds 0)

/-- The cutoff center and window are asymptotically admissible. Window positivity is
eventual because cutoff is unchanged by modifying finitely many indices. -/
def IsCutoffWindow (tCut w : ℕ → ℝ) : Prop :=
  Tendsto tCut atTop atTop ∧
  (∀ᶠ n in atTop, 0 < w n) ∧
  Asymptotics.IsLittleO atTop w tCut

/-- Total-variation cutoff at center `tCut` with window `w`, including the
paper's center-divergence, positivity, and little-o requirements. -/
def HasCutoff (d : ℕ → ℕ → ℝ) (tCut w : ℕ → ℝ) : Prop :=
  IsCutoffWindow tCut w ∧ HasCutoffLimits d tCut w

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

/-! ## Canonical path space and absorption time -/

/-- A homogeneous kernel viewed as a history-dependent kernel. -/
def markovHistoryKernel {E : Type*} [MeasurableSpace E]
    (κ : Kernel E E) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → E) E :=
  Kernel.comap κ (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance {E : Type*} [MeasurableSpace E]
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovHistoryKernel κ n) := by
  unfold markovHistoryKernel
  infer_instance

/-- Canonical path-space law for a homogeneous Markov chain. -/
def markovPathMeasure {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) (κ : Kernel E E) [IsMarkovKernel κ] :
    Measure (ℕ → E) :=
  Kernel.trajMeasure μ₀ (markovHistoryKernel κ)

/-- First hitting time of zero, with value `⊤` if zero is never hit. -/
def absorptionTime {Ω β : Type*} [Zero β]
    (X : ℕ → Ω → β) : Ω → WithTop ℕ :=
  hittingAfter X {0} 0

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

/-- Critical width in its equivalent log-drift characterization. -/
def fixedWidthCriticalWidth (N : ℕ) : ℝ :=
  Real.exp (-logRadialDrift 1 N)

/-- `gamma_{A,N} = log (A_c(N) / A)`. -/
def fixedWidthGamma (A : ℝ) (N : ℕ) : ℝ :=
  Real.log (fixedWidthCriticalWidth N / A)

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

/-- `sigma_N = sqrt (Var (log chi_N))`. -/
def fixedWidthSigma (N : ℕ) : ℝ :=
  Real.sqrt
    (variance (fun g : Fin N → ℝ ↦ Real.log (gaussianEuclideanNorm N g))
      (gaussianVec N))

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

/-- Manuscript observation time `t_ρ(a)`. -/
def fixedWidthPaperObservationTime
    (A : ℝ) (N : ℕ) (R₀ : ℝ) (ρ : ℕ → ℝ) (a : ℝ) (r : ℕ) : ℕ :=
  canonicalTime (fixedWidthGamma A N) (fixedWidthSigma N) a
    (fixedWidthInitialLogMeshScale R₀ ρ) 0 r

/-- Cutoff center `L_ρ / gamma_{A,N}`. -/
def fixedWidthPaperCutoffTime
    (A : ℝ) (N : ℕ) (R₀ : ℝ) (ρ : ℕ → ℝ) : ℕ → ℝ :=
  fun r ↦ fixedWidthInitialLogMeshScale R₀ ρ r / fixedWidthGamma A N

/-- Cutoff window `sigma_N gamma_{A,N}^{-3/2} sqrt L_ρ`. -/
def fixedWidthPaperCutoffWindow
    (A : ℝ) (N : ℕ) (R₀ : ℝ) (ρ : ℕ → ℝ) : ℕ → ℝ :=
  fun r ↦ (fixedWidthSigma N /
      (fixedWidthGamma A N * Real.sqrt (fixedWidthGamma A N))) *
    Real.sqrt (fixedWidthInitialLogMeshScale R₀ ρ r)

/-! ## Bridges to the development

Each audit definition was copied verbatim from its source module, so every bridge
is `rfl`. Stating them makes any future divergence a build error. -/

lemma tvDist_eq {E : Type*} [MeasurableSpace E] (mu nu : Measure E) :
    tvDist mu nu = AbsorptionCutoff.tvDist mu nu := rfl

lemma HasCutoffLimits_eq : HasCutoffLimits = AbsorptionCutoff.HasCutoffLimits := rfl

lemma IsCutoffWindow_eq : IsCutoffWindow = AbsorptionCutoff.IsCutoffWindow := rfl

lemma HasCutoff_eq : HasCutoff = AbsorptionCutoff.HasCutoff := rfl

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

lemma markovHistoryKernel_eq {E : Type*} [MeasurableSpace E]
    (κ : Kernel E E) [IsMarkovKernel κ] :
    markovHistoryKernel κ = AbsorptionCutoff.markovHistoryKernel κ := rfl

lemma markovPathMeasure_eq {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) (κ : Kernel E E) [IsMarkovKernel κ] :
    markovPathMeasure μ₀ κ = AbsorptionCutoff.markovPathMeasure μ₀ κ := rfl

lemma absorptionTime_eq {Ω β : Type*} [Zero β] :
    (absorptionTime : (ℕ → Ω → β) → Ω → WithTop ℕ) =
      AbsorptionCutoff.absorptionTime := rfl

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

lemma fixedWidthCriticalWidth_eq :
    fixedWidthCriticalWidth = AbsorptionCutoff.fixedWidthCriticalWidth := rfl

lemma fixedWidthGamma_eq :
    fixedWidthGamma = AbsorptionCutoff.fixedWidthGamma := rfl

lemma fixedWidthGaussianMeasure_eq (N : ℕ) :
    fixedWidthGaussianMeasure N = AbsorptionCutoff.fixedWidthGaussianMeasure N := rfl

lemma fixedWidthStdDev_eq (A : ℝ) (N : ℕ) :
    fixedWidthStdDev A N = AbsorptionCutoff.fixedWidthStdDev A N := rfl

lemma fixedWidthSigma_eq :
    fixedWidthSigma = AbsorptionCutoff.fixedWidthSigma := rfl

lemma fixedWidthIncrementProcess_eq (A : ℝ) (N : ℕ) :
    fixedWidthIncrementProcess A N = AbsorptionCutoff.fixedWidthIncrementProcess A N := rfl

lemma canonicalTimeArgument_eq :
    canonicalTimeArgument = AbsorptionCutoff.canonicalTimeArgument := rfl

lemma canonicalTime_eq : canonicalTime = AbsorptionCutoff.canonicalTime := rfl

lemma fixedWidthInitialLogMeshScale_eq :
    fixedWidthInitialLogMeshScale = AbsorptionCutoff.fixedWidthInitialLogMeshScale := rfl

lemma fixedWidthPaperObservationTime_eq :
    fixedWidthPaperObservationTime =
      AbsorptionCutoff.fixedWidthPaperObservationTime := rfl

lemma fixedWidthPaperCutoffTime_eq :
    fixedWidthPaperCutoffTime =
      AbsorptionCutoff.fixedWidthPaperCutoffTime := rfl

lemma fixedWidthPaperCutoffWindow_eq :
    fixedWidthPaperCutoffWindow =
      AbsorptionCutoff.fixedWidthPaperCutoffWindow := rfl

/-! ## The theorem under audit -/

/-- **Fixed-width vanishing-mesh cutoff** (paper
`thm:rounded-gaussian-nearest-cutoff`). In fixed positive dimension `N` and
subcritical fixed width `A`, started from any `x₀ ≠ 0`, along any positive mesh
sequence `ρ r → 0⁺`, total variation equals absorption survival and has profile
`Φ(−a)` for every fixed `a`; in particular the family has cutoff at the stated
center and window. -/
theorem rounded_gaussian_nearest_cutoff
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hcritical : A < fixedWidthCriticalWidth N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (ρ : ℕ → ℝ) (hρpos : ∀ r, 0 < ρ r)
    (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0))) :
    (∀ a : ℝ,
      (∀ r,
        tvDist
            (((roundedPkernel A (ρ r) N) ^
              (fixedWidthPaperObservationTime A N
                (gaussianEuclideanNorm N x0) ρ a r))
              (Qρ (ρ r) x0))
            (Measure.dirac (0 : Fin N → ℝ)) =
          ((markovPathMeasure (Measure.dirac (Qρ (ρ r) x0))
              (roundedPkernel A (ρ r) N))
            {ω | ((fixedWidthPaperObservationTime A N
                (gaussianEuclideanNorm N x0) ρ a r : ℕ) : WithTop ℕ) <
              absorptionTime
                (fun (s : ℕ) (ω : ℕ → (Fin N → ℝ)) ↦ ω s) ω}).toReal) ∧
      Tendsto
        (fun r ↦
          tvDist
            (((roundedPkernel A (ρ r) N) ^
              (fixedWidthPaperObservationTime A N
                (gaussianEuclideanNorm N x0) ρ a r))
              (Qρ (ρ r) x0))
            (Measure.dirac (0 : Fin N → ℝ)))
        atTop (nhds (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal 0 1) (-a)))) ∧
    HasCutoff
      (fun r t ↦
        tvDist
          (((roundedPkernel A (ρ r) N) ^ t) (Qρ (ρ r) x0))
          (Measure.dirac (0 : Fin N → ℝ)))
      (fixedWidthPaperCutoffTime A N
        (gaussianEuclideanNorm N x0) ρ)
      (fixedWidthPaperCutoffWindow A N
        (gaussianEuclideanNorm N x0) ρ)
:=
  AbsorptionCutoff.MainTheorems.rounded_gaussian_nearest_cutoff
    hA hN hcritical x0 hx0 ρ hρpos hρ

end

end AbsorptionCutoff.StatementAudit.FixedWidthCutoff
