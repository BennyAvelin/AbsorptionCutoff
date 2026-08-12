/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Metastability

/-!
# Solution to the fixed-dimensional absorption challenge

This file repeats, verbatim, the statement vocabulary and the theorem of
`Audit/FixedDimensionAbsorption/Challenge.lean`, and proves the theorem from the
paper-facing source wrapper in `AbsorptionCutoff.Metastability`.

Each audit definition is a literal copy of its project counterpart, so the bridge
lemmas below all hold by `rfl`; they are stated explicitly rather than left to
unification so that any future drift between the two vocabularies fails loudly
here instead of silently changing what the comparator checks.
-/

namespace AbsorptionCutoff.StatementAudit.FixedDimensionAbsorption

open Filter MeasureTheory ProbabilityTheory Topology

noncomputable section

/-! ## Rounding and the metastability threshold -/

/-- Scalar nearest-integer rounding on the unit grid, ties broken toward the grid
point of smaller absolute value (round half toward zero). -/
def Q₁ (u : ℝ) : ℤ :=
  if 0 ≤ u then ⌈u - 2⁻¹⌉ else -⌈-u - 2⁻¹⌉

lemma measurable_Q₁ : Measurable Q₁ := by
  unfold Q₁
  apply Measurable.ite (measurableSet_le measurable_const measurable_id)
  · exact Int.measurable_ceil.comp (measurable_id.sub measurable_const)
  · exact (Int.measurable_ceil.comp (measurable_id.neg.sub measurable_const)).neg

/-- `tanh` is continuous; built from `sinh / cosh`. -/
lemma continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
    funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh
    (fun x => (Real.cosh_pos x).ne')

/-- Scalar rounding to the grid `ρℤ`. -/
def gridRound (ρ u : ℝ) : ℝ := ρ * (Q₁ (u / ρ) : ℝ)

/-- Coordinatewise vector rounding to `(ρℤ)^N`. -/
def Qρ (ρ : ℝ) {N : ℕ} (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => gridRound ρ (x i)

/-- Coordinatewise rounding `Qρ ρ` is measurable. -/
lemma measurable_Qρ (ρ : ℝ) (N : ℕ) :
    Measurable (Qρ ρ : (Fin N → ℝ) → Fin N → ℝ) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Qρ gridRound
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  have hdiv : Measurable (fun x : Fin N → ℝ => x i / ρ) :=
    (measurable_pi_apply i).div measurable_const
  exact measurable_const.mul (hcast.comp (measurable_Q₁.comp hdiv))

/-- The fixed-precision Gaussian profile. -/
def roundedProfile (ρ α : ℝ) : ℝ :=
  ∫ g, ((Q₁ (ρ⁻¹ * Real.tanh (ρ * α * g)) : ℝ)) ^ 2 ∂gaussianReal 0 1

/-- The quotient whose positive-scale infimum is the squared threshold. -/
def roundedThresholdRatio (ρ α : ℝ) : ℝ :=
  α ^ 2 / roundedProfile ρ α

/-- The squared fixed-precision existence threshold. -/
def roundedExistenceThresholdSq (ρ : ℝ) : ℝ :=
  sInf (roundedThresholdRatio ρ '' Set.Ioi 0)

/-- The fixed-precision existence threshold. -/
def roundedExistenceThreshold (ρ : ℝ) : ℝ :=
  Real.sqrt (roundedExistenceThresholdSq ρ)

/-! ## The rounded vector chain -/

/-- Variance `A²/N` of one Gaussian weight. -/
def weightVar (A : ℝ) (N : ℕ) : NNReal := (A ^ 2 / N).toNNReal

/-- Law of the independent Gaussian weight matrix. -/
def gaussianMat (A : ℝ) (N : ℕ) : Measure (Fin N → Fin N → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 (weightVar A N)))

instance (A : ℝ) (N : ℕ) : IsProbabilityMeasure (gaussianMat A N) := by
  unfold gaussianMat; infer_instance

/-- The vector step map `tanh(Wx)`. -/
def Pstep (N : ℕ) (x : Fin N → ℝ)
    (W : Fin N → Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.tanh (∑ j, W i j * x j)

lemma measurable_Pstep (N : ℕ) :
    Measurable
      (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) => Pstep N p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Pstep
  apply continuous_tanh.measurable.comp
  apply Finset.measurable_sum
  intro j _
  fun_prop

/-- Rounded vector step map `Qρ(tanh(Wx))`. -/
def roundedPstep (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ)
    (W : Fin N → Fin N → ℝ) : Fin N → ℝ :=
  Qρ ρ (Pstep N x W)

lemma measurable_roundedPstep (ρ : ℝ) (N : ℕ) :
    Measurable
      (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) =>
        roundedPstep ρ N p.1 p.2) :=
  (measurable_Qρ ρ N).comp (measurable_Pstep N)

/-- Rounded vector transition kernel `P_{ρ,A,N}`. -/
def roundedPkernel
    (A ρ : ℝ) (N : ℕ) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  Kernel.map
    ((Kernel.deterministic id measurable_id).prod
      (Kernel.const _ (gaussianMat A N)))
    (fun p => roundedPstep ρ N p.1 p.2)

instance (A ρ : ℝ) (N : ℕ) : IsMarkovKernel (roundedPkernel A ρ N) := by
  unfold roundedPkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_roundedPstep ρ N)

/-! ## Canonical path space -/

/-- A homogeneous kernel read as a history-dependent kernel that looks only at the
last coordinate of the history. -/
def markovHistoryKernel {E : Type*} [MeasurableSpace E]
    (κ : Kernel E E) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → E) E :=
  Kernel.comap κ (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance instMarkovHistoryKernel {E : Type*} [MeasurableSpace E]
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovHistoryKernel κ n) := by
  unfold markovHistoryKernel
  infer_instance

/-- The path-space law obtained by starting from `μ₀` and iterating `κ`. -/
def markovPathMeasure {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) (κ : Kernel E E) [IsMarkovKernel κ] :
    Measure (ℕ → E) :=
  Kernel.trajMeasure μ₀ (markovHistoryKernel κ)

/-! ## Absorption -/

/-- The first time at or after zero at which a discrete-time process hits `0`,
with value `⊤` if it never does. -/
def absorptionTime {Ω β : Type*} [Zero β]
    (X : ℕ → Ω → β) : Ω → WithTop ℕ :=
  hittingAfter X {0} 0

/-- The paper's finite rounded vector state space
`(ρℤ)^N ∩ [-1-ρ/2, 1+ρ/2]^N`. -/
def roundedStateSpace (ρ : ℝ) (N : ℕ) : Set (Fin N → ℝ) :=
  {y |
    (∀ i, ∃ z : ℤ, y i = ρ * z) ∧
      ∀ i, y i ∈ Set.Icc (-1 - ρ / 2) (1 + ρ / 2)}

/-! ## Bridges to the development

Each audit definition was copied verbatim from its source module, so every bridge
is `rfl`. Stating them makes any future divergence a build error. -/

lemma Q₁_eq : Q₁ = AbsorptionCutoff.Q₁ := rfl

lemma gridRound_eq : gridRound = AbsorptionCutoff.gridRound := rfl

lemma Qρ_eq (ρ : ℝ) (N : ℕ) :
    (Qρ ρ : (Fin N → ℝ) → Fin N → ℝ) = AbsorptionCutoff.Qρ ρ := rfl

lemma roundedProfile_eq : roundedProfile = AbsorptionCutoff.roundedProfile := rfl

lemma roundedThresholdRatio_eq :
    roundedThresholdRatio = AbsorptionCutoff.roundedThresholdRatio := rfl

lemma roundedExistenceThresholdSq_eq :
    roundedExistenceThresholdSq = AbsorptionCutoff.roundedExistenceThresholdSq := rfl

lemma roundedExistenceThreshold_eq :
    roundedExistenceThreshold = AbsorptionCutoff.roundedExistenceThreshold := rfl

lemma weightVar_eq : weightVar = AbsorptionCutoff.weightVar := rfl

lemma gaussianMat_eq (A : ℝ) (N : ℕ) :
    gaussianMat A N = AbsorptionCutoff.gaussianMat A N := rfl

lemma Pstep_eq (N : ℕ) : Pstep N = AbsorptionCutoff.Pstep N := rfl

lemma roundedPstep_eq (ρ : ℝ) (N : ℕ) :
    roundedPstep ρ N = AbsorptionCutoff.roundedPstep ρ N := rfl

lemma roundedPkernel_eq (A ρ : ℝ) (N : ℕ) :
    roundedPkernel A ρ N = AbsorptionCutoff.roundedPkernel A ρ N := rfl

lemma markovHistoryKernel_eq {E : Type*} [MeasurableSpace E] (κ : Kernel E E) (n : ℕ) :
    markovHistoryKernel κ n = AbsorptionCutoff.markovHistoryKernel κ n := rfl

lemma markovPathMeasure_eq {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) (κ : Kernel E E) [IsMarkovKernel κ] :
    markovPathMeasure μ₀ κ = AbsorptionCutoff.markovPathMeasure μ₀ κ := rfl

lemma absorptionTime_eq {Ω β : Type*} [Zero β] (X : ℕ → Ω → β) :
    absorptionTime X = AbsorptionCutoff.absorptionTime X := rfl

lemma roundedStateSpace_eq (ρ : ℝ) (N : ℕ) :
    roundedStateSpace ρ N = AbsorptionCutoff.roundedStateSpace ρ N := rfl

/-! ## The theorem under audit -/

/-- **Fixed-dimensional almost-sure absorption** (paper
`thm:rounded-qualitative-metastability`, second clause). Assume the theorem's
threshold condition `A > A_ex(ρ)`, fix a mesh `ρ ∈ (0,1)` and a dimension
`N ≥ 1`, and let `y` be any deterministic point in the finite rounded state
space. On canonical path space the rounded vector chain started from `y` has
finite absorption time almost surely. -/
theorem rounded_fixed_dimension_absorption
    {A ρ : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hA : roundedExistenceThreshold ρ < A)
    {N : ℕ} (hN : 0 < N)
    (y : Fin N → ℝ) (hy : y ∈ roundedStateSpace ρ N) :
    ∀ᵐ ω ∂markovPathMeasure
        (Measure.dirac y) (roundedPkernel A ρ N),
      absorptionTime
        (fun (s : ℕ) (ω : ℕ → (Fin N → ℝ)) => ω s) ω ≠ ⊤ :=
  AbsorptionCutoff.ae_absorption_roundedPkernel_of_rounded_state
    hρ hρ_lt hA hN y hy

end

end AbsorptionCutoff.StatementAudit.FixedDimensionAbsorption
