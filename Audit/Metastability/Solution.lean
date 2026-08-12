/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.MainTheorems
import Audit.Metastability.Statement

/-!
# Solution to the rounded qualitative metastability challenge

This file repeats, verbatim, the statement vocabulary and the theorem of
`Audit/Metastability/Challenge.lean`, and proves the theorem from the
development's public index `AbsorptionCutoff.MainTheorems`.

Each audit definition is a literal copy of its project counterpart, so the bridge
lemmas below all hold by `rfl`; they are stated explicitly rather than left to
unification so that any future drift between the two vocabularies fails loudly
here instead of silently changing what the comparator checks.
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

/-! ## Bridges to the development

Each audit definition was copied verbatim from its source module, so every bridge
is `rfl`. Stating them makes any future divergence a build error. -/

lemma Q₁_eq : Q₁ = AbsorptionCutoff.Q₁ := rfl

lemma gaussianVec_eq (N : ℕ) : gaussianVec N = AbsorptionCutoff.gaussianVec N := rfl

lemma Hmap_eq (A ρ : ℝ) (N : ℕ) : Hmap A ρ N = AbsorptionCutoff.Hmap A ρ N := rfl

lemma Hkernel_eq (A ρ : ℝ) (N : ℕ) : Hkernel A ρ N = AbsorptionCutoff.Hkernel A ρ N := rfl

lemma markovHistoryKernel_eq {E : Type*} [MeasurableSpace E] (κ : Kernel E E) (n : ℕ) :
    markovHistoryKernel κ n = AbsorptionCutoff.markovHistoryKernel κ n := rfl

lemma markovPathMeasure_eq {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) (κ : Kernel E E) [IsMarkovKernel κ] :
    markovPathMeasure μ₀ κ = AbsorptionCutoff.markovPathMeasure μ₀ κ := rfl

lemma absorptionTime_eq {Ω β : Type*} [Zero β] (X : ℕ → Ω → β) :
    absorptionTime X = AbsorptionCutoff.absorptionTime X := rfl

lemma roundedRadiusBound_eq (ρ : ℝ) :
    roundedRadiusBound ρ = AbsorptionCutoff.roundedRadiusBound ρ := rfl

lemma roundedMeanMap_eq : roundedMeanMap = AbsorptionCutoff.roundedMeanMap := rfl

lemma roundedPositiveDriftSet_eq (A ρ : ℝ) :
    roundedPositiveDriftSet A ρ = AbsorptionCutoff.roundedPositiveDriftSet A ρ := rfl

lemma roundedPositiveDriftComponent_eq (A ρ h : ℝ) :
    roundedPositiveDriftComponent A ρ h =
      AbsorptionCutoff.roundedPositiveDriftComponent A ρ h := rfl

lemma IsRightmostRoundedPositiveDriftComponent_eq (A ρ h : ℝ) :
    IsRightmostRoundedPositiveDriftComponent A ρ h =
      AbsorptionCutoff.IsRightmostRoundedPositiveDriftComponent A ρ h := rfl

/-! ## The theorem under audit -/

/-- **Rounded qualitative metastability**, complete paper statement. -/
theorem rounded_qualitative_metastability :
    RoundedQualitativeMetastabilityStatement :=
  AbsorptionCutoff.MainTheorems.rounded_qualitative_metastability

end

end AbsorptionCutoff.StatementAudit.Metastability
