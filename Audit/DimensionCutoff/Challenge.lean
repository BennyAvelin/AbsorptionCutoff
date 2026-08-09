/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Mathlib-only challenge: fixed-precision dimension cutoff

This file is the comparator challenge surface for the paper's subcritical
fixed-precision dimension cutoff `thm:subcritical-dimension-cutoff`: below the
lattice threshold the rounded vector chain, observed at the deterministic
terminal-scale entrance time, is still far from the absorbing origin one step
early and already absorbed two steps late.

It imports only `Mathlib`. Every object the statement mentions is rebuilt below
from Mathlib primitives. The source correspondences are:

* `Q₁`, `gridRound`, `Qρ`: `AbsorptionCutoff/Rounding.lean`;
* `tvDist`: `AbsorptionCutoff/Cutoff.lean`;
* `weightVar`, `gaussianMat`, `Pstep`: `AbsorptionCutoff/VectorReduction.lean`;
* `roundedPstep`, `roundedPkernel`: `AbsorptionCutoff/RoundedVectorReduction.lean`;
* `latticeProfile`, `latticeThresholdSq`, `latticeThreshold`, `roundedMeanMap`:
  `AbsorptionCutoff/Lattice.lean`;
* `fixedPrecisionScale`, `roundedOrbit`, `roundedOrbitEntrance`:
  `AbsorptionCutoff/OrbitAmplification.lean`;
* `roundedInitialRadius`: `AbsorptionCutoff/RadiusConcentration.lean`;
* `roundedDimensionCutoffTime`: `AbsorptionCutoff/DimensionCutoff.lean`;
* the theorem: `AbsorptionCutoff/RoundedVectorReduction.lean`.

The only proof omitted in this file is the final theorem's.
-/

namespace AbsorptionCutoff.StatementAudit.DimensionCutoff

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

/-! ## The lattice threshold -/

/-- The lattice profile `m(α) = E[Q₁(α G)²]`, `G ∼ 𝒩(0,1)`. -/
def latticeProfile (α : ℝ) : ℝ :=
  ∫ g, ((Q₁ (α * g) : ℝ)) ^ 2 ∂(gaussianReal 0 1)

/-- `inf_{α>0} α² / m(α)`. -/
def latticeThresholdSq : ℝ :=
  ⨅ α : {α : ℝ // 0 < α}, (α : ℝ) ^ 2 / latticeProfile α

/-- The lattice threshold `A_lat`, the nonnegative square root of the above. -/
def latticeThreshold : ℝ :=
  Real.sqrt latticeThresholdSq

/-! ## The deterministic rounded orbit and its entrance time -/

/-- The rounded squared-radius mean map. -/
def roundedMeanMap (A ρ h : ℝ) : ℝ :=
  ∫ g, ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) : ℝ)) ^ 2
    ∂(gaussianReal 0 1)

/-- The deterministic rounded orbit: iterate the rounded mean map from `h₀`. -/
def roundedOrbit (A ρ h₀ : ℝ) (t : ℕ) : ℝ :=
  (roundedMeanMap A ρ)^[t] h₀

/-- The first deterministic time at which the rounded orbit reaches radius `r`,
with the usual `sInf ∅ = 0` convention. -/
def roundedOrbitEntrance (A ρ h₀ r : ℝ) : ℕ :=
  sInf {t : ℕ | roundedOrbit A ρ h₀ t ≤ r}

/-- The terminal fixed-precision scale `(log N)⁻¹`. -/
def fixedPrecisionScale (N : ℕ) : ℝ :=
  (Real.log N)⁻¹

/-- The deterministic rounded initial radius of `x`. -/
def roundedInitialRadius
    (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, ((Q₁ (x i / ρ) : ℤ) : ℝ) ^ 2

/-- The dimension cutoff time: when the deterministic rounded orbit started at the
rounded initial radius first reaches the terminal scale. -/
def roundedDimensionCutoffTime
    (A ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℕ :=
  roundedOrbitEntrance A ρ (roundedInitialRadius ρ N x)
    (fixedPrecisionScale N)

/-! ## The theorem under audit -/

/-- **Fixed-precision dimension cutoff** (paper `thm:subcritical-dimension-cutoff`).
Below the lattice threshold, for meshes `ρ ∈ (0,1)` and starting vectors with
coordinates in `[-1,1]` whose cutoff times diverge, the rounded vector chain
started at `Qρ ρ (x N)` is at total-variation distance tending to `1` from the
absorbing origin one step before the cutoff time, and to `0` two steps after. -/
theorem subcritical_dimension_cutoff
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1)
    (htime :
      Filter.Tendsto
        (fun N : ℕ => roundedDimensionCutoffTime A ρ N (x N))
        Filter.atTop Filter.atTop) :
    Filter.Tendsto
        (fun N : ℕ =>
          tvDist
            (((roundedPkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) - 1))
              (Qρ ρ (x N)))
            (Measure.dirac (0 : Fin N → ℝ)))
        Filter.atTop (𝓝 1) ∧
      Filter.Tendsto
        (fun N : ℕ =>
          tvDist
            (((roundedPkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) + 2))
              (Qρ ρ (x N)))
            (Measure.dirac (0 : Fin N → ℝ)))
        Filter.atTop (𝓝 0) := by
  sorry

end

end AbsorptionCutoff.StatementAudit.DimensionCutoff
