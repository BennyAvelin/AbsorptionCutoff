/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Mathlib-only challenge: supercritical scalar cutoff

This file is the comparator challenge surface for the paper's supercritical
scalar cutoff `thm:gaussian-process-cutoff`: in the supercritical regime the
scalar squared-radius chain exhibits total-variation cutoff, in the dimension
`N`, at `supercriticalCutoffTime` with window `1`, against an eventually unique
family of nonzero invariant laws.

It is the scalar half of the pair whose vector form is audited in
`Audit/VectorCutoff/`; the two statements share most of their vocabulary.

It imports only `Mathlib`. Every object the statement mentions is rebuilt below
from Mathlib primitives. The source correspondences are:

* `tvDist`, `HasCutoff`: `AbsorptionCutoff/Cutoff.lean`;
* `V`: `AbsorptionCutoff/MeanMap/Basic.lean`;
* `gaussianVec`, `Fmap`, `Kchain`: `AbsorptionCutoff/Chains.lean`;
* `radiusSq`: `AbsorptionCutoff/VectorReduction.lean`;
* `koenigsOrbitFactor`, `koenigsOrbitProduct`, `koenigsCoefficient`:
  `AbsorptionCutoff/Supercritical/Deterministic.lean`;
* `supercriticalCutoffTime`: `AbsorptionCutoff/Supercritical/CutoffAssembly.lean`;
* the theorem: `AbsorptionCutoff/Supercritical/CutoffLimitAssembly.lean`.

The only proof omitted in this file is the final theorem's.
-/

namespace AbsorptionCutoff.StatementAudit.ScalarCutoff

open Filter MeasureTheory ProbabilityTheory Topology

noncomputable section

/-! ## Total variation and cutoff -/

/-- Total-variation distance `‖μ − ν‖_TV = sup_B |μ(B) − ν(B)|` over measurable `B`. -/
def tvDist {E : Type*} [MeasurableSpace E] (μ ν : Measure E) : ℝ :=
  ⨆ s : {s : Set E // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|

/-- A family of distance profiles `d n t` has **cutoff** at time `tCut` with window
`w`: rescaling time by `tCut n ± c * w n` drives the profile to `1` and to `0` as
`c → ∞`. -/
def HasCutoff (d : ℕ → ℕ → ℝ) (tCut w : ℕ → ℝ) : Prop :=
  Tendsto (fun c : ℝ => liminf (fun n => d n ⌊tCut n - c * w n⌋₊) atTop) atTop (𝓝 1) ∧
  Tendsto (fun c : ℝ => limsup (fun n => d n ⌊tCut n + c * w n⌋₊) atTop) atTop (𝓝 0)

/-! ## The scalar mean map -/

/-- `tanh` is continuous; built from `sinh / cosh`. -/
lemma continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-- The Gaussian mean map `V_A(q) = E[tanh²(A√q · G)]`, `G ∼ 𝒩(0,1)`. -/
def V (A q : ℝ) : ℝ :=
  ∫ g, Real.tanh (A * Real.sqrt q * g) ^ 2 ∂(gaussianReal 0 1)

/-! ## Gaussian laws, maps, and kernels -/

/-- Standard Gaussian measure on `ℝ^N`. -/
def gaussianVec (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (N : ℕ) : IsProbabilityMeasure (gaussianVec N) := by
  unfold gaussianVec; infer_instance

/-- Normalized squared radius `r_N(x) = N⁻¹ ∑ᵢ xᵢ²`. -/
def radiusSq (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (x i) ^ 2

/-- The squared-radius random map `F_{A,N}(q, g) = N⁻¹ ∑ᵢ tanh²(A√q · gᵢ)`. -/
def Fmap (A : ℝ) (N : ℕ) (q : ℝ) (g : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, Real.tanh (A * Real.sqrt q * g i) ^ 2

lemma measurable_Fmap (A : ℝ) (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => Fmap A N p.1 p.2) := by
  apply Continuous.measurable
  unfold Fmap
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i _
  exact (continuous_tanh.comp (by fun_prop)).pow 2

/-- The scalar squared-radius chain on `ℝ`. -/
def Kchain (A : ℝ) (N : ℕ) : Kernel ℝ ℝ :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const ℝ (gaussianVec N)))
    (fun p => Fmap A N p.1 p.2)

instance (A : ℝ) (N : ℕ) : IsMarkovKernel (Kchain A N) := by
  unfold Kchain
  exact Kernel.IsMarkovKernel.map _ (measurable_Fmap A N)

/-! ## The Koenigs linearization and the cutoff time -/

/-- The `n`-th orbitwise Koenigs factor of `V_A` at the fixed point `qStar`. -/
def koenigsOrbitFactor (A qStar q : ℝ) (n : ℕ) : ℝ :=
  ((V A ((V A)^[n] q) - qStar) / ((V A)^[n] q - qStar)) /
    deriv (V A) qStar

/-- The infinite Koenigs product along the orbit of `q`. -/
def koenigsOrbitProduct (A qStar q : ℝ) : ℝ :=
  ∏' n : ℕ, koenigsOrbitFactor A qStar q n

/-- The Koenigs coefficient of the orbit started at `q`. -/
def koenigsCoefficient (A qStar q : ℝ) : ℝ :=
  (q - qStar) * koenigsOrbitProduct A qStar q

/-- The supercritical cutoff time in dimension `N`. -/
def supercriticalCutoffTime (A qStar q₀ : ℝ) (N : ℕ) : ℝ :=
  ((1 / 2) * Real.log (N : ℝ) +
      Real.log |koenigsCoefficient A qStar q₀|) /
    |Real.log (deriv (V A) qStar)|

/-! ## The theorem under audit -/

/-- **Supercritical scalar cutoff** (paper `thm:gaussian-process-cutoff`). Under
the manuscript's coordinate-box and radius-convergence assumptions, the scalar
squared-radius chain has a unique nonzero invariant law in every sufficiently
large dimension, and the chain started at `radiusSq N (x N)` has
total-variation cutoff relative to those laws at `supercriticalCutoffTime` with
window `1`. -/
theorem gaussian_process_cutoff
    {A qStar q₀ : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hbox :
      ∀ N : ℕ, ∀ i, x N i ∈ Set.Icc (-1 : ℝ) 1)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀)) :
    ∃ ν : ℕ → ProbabilityMeasure ℝ,
      (∀ᶠ N : ℕ in Filter.atTop, ∀ ρ : ProbabilityMeasure ℝ,
        ((ρ : Measure ℝ) ({0} : Set ℝ) = 0 ∧
          Kernel.Invariant (Kchain A N) (ρ : Measure ℝ)) ↔
        ρ = ν N) ∧
      HasCutoff
        (fun N t =>
          tvDist
            (((Kchain A N) ^ t) (radiusSq N (x N)))
            (ν N : Measure ℝ))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  sorry

end

end AbsorptionCutoff.StatementAudit.ScalarCutoff
