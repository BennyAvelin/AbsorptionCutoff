/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Mathlib-only challenge: supercritical vector cutoff

This file is the comparator challenge surface for the paper's supercritical
vector cutoff `cor:gaussian-vector-cutoff`: in the supercritical regime the
unrounded Gaussian vector chain exhibits total-variation cutoff, in the
dimension `N`, at the time `supercriticalCutoffTime` with window `1`.

It imports only `Mathlib`. Every object the statement mentions is rebuilt below
from Mathlib primitives. The source correspondences are:

* `tvDist`, `HasCutoff`: `AbsorptionCutoff/Cutoff.lean`;
* `V`: `AbsorptionCutoff/MeanMap/Basic.lean`;
* `gaussianVec`, `Fmap`, `Kchain`: `AbsorptionCutoff/Chains.lean`;
* `radiusSq`, `Jmap`, `Jkernel`, `weightVar`, `gaussianMat`, `Pstep`, `Pkernel`:
  `AbsorptionCutoff/VectorReduction.lean`;
* `koenigsOrbitFactor`, `koenigsOrbitProduct`, `koenigsCoefficient`:
  `AbsorptionCutoff/Supercritical/Deterministic.lean`;
* `supercriticalCutoffTime`: `AbsorptionCutoff/Supercritical/CutoffAssembly.lean`;
* the theorem: `AbsorptionCutoff/Supercritical/CutoffLimitAssembly.lean`.

The only proof omitted in this file is the final theorem's.
-/

namespace AbsorptionCutoff.StatementAudit.VectorCutoff

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

/-- Entry variance `A²/N` of the Gaussian weight matrix. -/
def weightVar (A : ℝ) (N : ℕ) : NNReal := (A ^ 2 / N).toNNReal

/-- The Gaussian weight-matrix law: independent entries `∼ 𝒩(0, A²/N)`. -/
def gaussianMat (A : ℝ) (N : ℕ) : Measure (Fin N → Fin N → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 (weightVar A N)))

instance (A : ℝ) (N : ℕ) : IsProbabilityMeasure (gaussianMat A N) := by
  unfold gaussianMat; infer_instance

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

/-- The reconstruction map `J_{A,N}(q, g) = (tanh(A√q · gᵢ))ᵢ`. -/
def Jmap (A : ℝ) (N : ℕ) (q : ℝ) (g : Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.tanh (A * Real.sqrt q * g i)

lemma measurable_Jmap (A : ℝ) (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => Jmap A N p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Jmap
  exact continuous_tanh.measurable.comp (by fun_prop)

/-- The reconstruction kernel from a squared radius to a vector. -/
def Jkernel (A : ℝ) (N : ℕ) : Kernel ℝ (Fin N → ℝ) :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const ℝ (gaussianVec N)))
    (fun p => Jmap A N p.1 p.2)

instance (A : ℝ) (N : ℕ) : IsMarkovKernel (Jkernel A N) := by
  unfold Jkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_Jmap A N)

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

/-- The unrounded vector transition kernel: `P(x, ·)` is the law of `tanh(𝖶x)`. -/
def Pkernel (A : ℝ) (N : ℕ) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const _ (gaussianMat A N)))
    (fun p => Pstep N p.1 p.2)

instance (A : ℝ) (N : ℕ) : IsMarkovKernel (Pkernel A N) := by
  unfold Pkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_Pstep N)

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

/-- **Supercritical vector cutoff** (paper `cor:gaussian-vector-cutoff`). Under the
manuscript's coordinate-box and radius-convergence assumptions, there is a constant
`C` and a family `ν` of scalar invariant laws, concentrated on `[0,1]`, away from
the origin, and with `(q − qStar)²`-variance `O(1/N)`, whose reconstructions
`J_{A,N} ∘ ν N` are invariant for the vector chain and away from the origin, such
that the vector chain has total-variation cutoff at `supercriticalCutoffTime`
with window `1`. -/
theorem gaussian_vector_cutoff
    {A qStar q₀ b : ℝ}
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
        Filter.atTop (nhds q₀))
    (hb : 0 < b) :
    ∃ C : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N)
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ∧
          ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
              ({0} : Set (Fin N → ℝ)) = 0) ∧
      HasCutoff
        (fun N t =>
          tvDist (((Pkernel A N) ^ t) (x N))
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  sorry

end

end AbsorptionCutoff.StatementAudit.VectorCutoff
