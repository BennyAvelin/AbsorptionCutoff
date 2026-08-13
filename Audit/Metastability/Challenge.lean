/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Mathlib-only challenge: rounded qualitative metastability

This file is the comparator challenge surface for the complete paper theorem
`thm:rounded-qualitative-metastability`. It imports only `Mathlib`; every object
in the theorem statement is rebuilt below from Mathlib primitives.

The source correspondences are:

* `Q₁`, `gridRound`, `Qρ`: `AbsorptionCutoff/Rounding.lean`;
* `gaussianVec`, `Hmap`, `Hkernel`: `AbsorptionCutoff/Chains.lean`;
* `weightVar`, `gaussianMat`, `Pstep`: `AbsorptionCutoff/VectorReduction.lean`;
* `roundedPstep`, `roundedPkernel`, `roundedRadiusSq`:
  `AbsorptionCutoff/RoundedVectorReduction.lean`;
* `markovHistoryKernel`, `markovPathMeasure`: `AbsorptionCutoff/MarkovTrajectory.lean`;
* `absorptionTime`: `AbsorptionCutoff/AbsorptionTime.lean`;
* `roundedMeanMap`: `AbsorptionCutoff/Lattice.lean`;
* the threshold, state-space, exit-event, positive-drift objects, and theorem:
  `AbsorptionCutoff/Metastability.lean`.

The only proof omitted in this file is the final theorem's.
-/

namespace AbsorptionCutoff.StatementAudit.Metastability

open Filter MeasureTheory ProbabilityTheory Topology

noncomputable section

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

lemma measurable_Qρ (ρ : ℝ) (N : ℕ) :
    Measurable (Qρ ρ : (Fin N → ℝ) → Fin N → ℝ) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Qρ gridRound
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  have hdiv : Measurable (fun x : Fin N → ℝ => x i / ρ) :=
    (measurable_pi_apply i).div measurable_const
  exact measurable_const.mul
    (hcast.comp (measurable_Q₁.comp hdiv))

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


/-! ## The rounded squared-radius chain -/

/-- Standard Gaussian measure on `ℝ^N`. -/
def gaussianVec (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (N : ℕ) : IsProbabilityMeasure (gaussianVec N) := by
  unfold gaussianVec; infer_instance

/-- `tanh` is continuous; built from `sinh / cosh`. -/
lemma continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')


/-! ## The rounded vector chain -/

/-- Variance `A²/N` of one Gaussian weight. -/
def weightVar (A : ℝ) (N : ℕ) : NNReal := (A ^ 2 / N).toNNReal

/-- Law of the independent Gaussian weight matrix. -/
def gaussianMat (A : ℝ) (N : ℕ) : Measure (Fin N → Fin N → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 (weightVar A N)))

instance (A : ℝ) (N : ℕ) : IsProbabilityMeasure (gaussianMat A N) := by
  unfold gaussianMat
  infer_instance

/-- The vector step map `tanh(Wx)`. -/
def Pstep (N : ℕ) (x : Fin N → ℝ)
    (W : Fin N → Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.tanh (∑ j, W i j * x j)

lemma measurable_Pstep (N : ℕ) :
    Measurable
      (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) =>
        Pstep N p.1 p.2) := by
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

/-- Normalized rounded squared radius
`(Nρ²)⁻¹ ∑ᵢ xᵢ²`. -/
def roundedRadiusSq
    (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  ((N : ℝ) * ρ ^ 2)⁻¹ * ∑ i, (x i) ^ 2


/-- The rounded squared-radius map
`H_{A,ρ,N}(h, g) = N⁻¹ ∑ᵢ Q₁(ρ⁻¹ · tanh(ρ A √h · gᵢ))²`. -/
def Hmap (A ρ : ℝ) (N : ℕ) (h : ℝ) (g : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g i)) : ℤ) : ℝ) ^ 2

lemma measurable_Hmap (A ρ : ℝ) (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => Hmap A ρ N p.1 p.2) := by
  unfold Hmap
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Measurable.pow_const
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  apply hcast.comp
  apply measurable_Q₁.comp
  apply Measurable.const_mul
  exact continuous_tanh.measurable.comp (by fun_prop)

/-- The rounded squared-radius transition kernel on `ℝ`: `H(h, ·)` is the law of
`Hmap A ρ N h G` for a standard Gaussian `G`. The origin is absorbing. -/
def Hkernel (A ρ : ℝ) (N : ℕ) : Kernel ℝ ℝ :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const ℝ (gaussianVec N)))
    (fun p => Hmap A ρ N p.1 p.2)

instance (A ρ : ℝ) (N : ℕ) : IsMarkovKernel (Hkernel A ρ N) := by
  unfold Hkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_Hmap A ρ N)

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

/-- The maximal squared rounded coordinate on `[-ρ⁻¹, ρ⁻¹]`. -/
def roundedRadiusBound (ρ : ℝ) : ℝ :=
  (Q₁ ρ⁻¹ : ℝ) ^ 2


/-- The finite rounded vector state space attained after applying `tanh` and
rounding coordinatewise. -/
def roundedVectorStateSpace (ρ : ℝ) (N : ℕ) : Set (Fin N → ℝ) :=
  {x | ∀ i, ∃ k : ℤ,
    |(k : ℝ)| ≤ |(Q₁ ρ⁻¹ : ℝ)| ∧ x i = ρ * (k : ℝ)}


/-! ## The positive-drift structure -/

/-- The rounded squared-radius mean map. -/
def roundedMeanMap (A ρ h : ℝ) : ℝ :=
  ∫ g, ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) : ℝ)) ^ 2
    ∂(gaussianReal 0 1)

/-- Radii strictly inside the state space at which the rounded mean map has
strictly positive drift. -/
def roundedPositiveDriftSet (A ρ : ℝ) : Set ℝ :=
  {h | h ∈ Set.Ioo 0 (roundedRadiusBound ρ) ∧
    h < roundedMeanMap A ρ h}

/-- The positive-drift component containing a reference radius. -/
def roundedPositiveDriftComponent (A ρ h : ℝ) : Set ℝ :=
  connectedComponentIn (roundedPositiveDriftSet A ρ) h

/-- A positive-drift component is rightmost when every point of the
positive-drift set lies at or to the left of its upper endpoint. -/
def IsRightmostRoundedPositiveDriftComponent (A ρ h : ℝ) : Prop :=
  ∀ u ∈ roundedPositiveDriftSet A ρ,
    u ≤ sSup (roundedPositiveDriftComponent A ρ h)


/-- Paths that exit the closed `η`-neighborhood of `upper` within `T`
steps after time `t₀`. -/
def metastableExitEvent
    (upper η : ℝ) (t₀ T : ℕ) : Set (ℕ → ℝ) :=
  {ω | ∃ s ≤ T, η < |ω (t₀ + s) - upper|}



/-! ## The theorem under audit -/

/-- **Rounded qualitative metastability**, complete paper statement. -/
theorem rounded_qualitative_metastability
    {A ρ : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hA : roundedExistenceThreshold ρ < A) :
    ∃ h : ℝ, h ∈ roundedPositiveDriftSet A ρ ∧
      IsRightmostRoundedPositiveDriftComponent A ρ h ∧
      let Ccomp := roundedPositiveDriftComponent A ρ h
        ∃ η₀ : ℝ, 0 < η₀ ∧
          sInf Ccomp < sSup Ccomp - η₀ ∧
          sSup Ccomp + η₀ < roundedRadiusBound ρ ∧
          (∀ u ∈ Set.Ioc (sSup Ccomp) (sSup Ccomp + η₀),
            roundedMeanMap A ρ u < u) ∧
          ((∀ (B : Set ℝ), IsCompact B →
              B ⊆ Set.Ioc (sInf Ccomp) (sSup Ccomp) →
              ∀ η : ℝ, 0 < η → η < η₀ →
                ∃ Tη : ℕ, ∃ C c₀ c₁ : ℝ,
                  0 < C ∧ 0 < c₀ ∧ 0 < c₁ ∧ c₁ < c₀ ∧
                  (∀ (N : ℕ), 0 < N → ∀ x : Fin N → ℝ,
                    roundedRadiusSq ρ N x ∈ B →
                    (markovPathMeasure
                        (Measure.dirac (roundedRadiusSq ρ N x))
                        (Hkernel A ρ N)).real
                        {ω : ℕ → ℝ |
                          |ω Tη - sSup Ccomp| > η / 2} ≤
                      C * Real.exp (-c₀ * N)) ∧
                  (∀ (N : ℕ), 0 < N → ∀ x : Fin N → ℝ,
                    roundedRadiusSq ρ N x ∈ B → ∀ T : ℕ,
                    (markovPathMeasure
                        (Measure.dirac (roundedRadiusSq ρ N x))
                        (Hkernel A ρ N)).real
                        (metastableExitEvent (sSup Ccomp) η Tη T) ≤
                      C * (1 + T) * Real.exp (-c₀ * N)) ∧
                  (∀ x : ∀ N : ℕ, Fin N → ℝ,
                    (∀ N, 0 < N → roundedRadiusSq ρ N (x N) ∈ B) →
                    Tendsto
                      (fun N : ℕ =>
                        (markovPathMeasure (Measure.dirac (x N))
                            (roundedPkernel A ρ N)).real
                          {ω |
                            ((Tη + ⌊Real.exp (c₁ * N)⌋₊ : ℕ) :
                                WithTop ℕ) <
                              absorptionTime
                                (fun (s : ℕ)
                                  (ω : ℕ → (Fin N → ℝ)) => ω s) ω})
                      atTop (𝓝 1))) ∧
            ∀ (N : ℕ), 0 < N → ∀ x ∈ roundedVectorStateSpace ρ N,
              ∀ᵐ ω ∂markovPathMeasure (Measure.dirac x)
                  (roundedPkernel A ρ N),
                absorptionTime
                  (fun (s : ℕ) (ω : ℕ → (Fin N → ℝ)) => ω s) ω ≠ ⊤) := by
  sorry

end

end AbsorptionCutoff.StatementAudit.Metastability
