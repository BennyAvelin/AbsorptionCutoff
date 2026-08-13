/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.MainTheorems

/-!
# Solution to the supercritical vector cutoff challenge

This file repeats, verbatim, the statement vocabulary and the theorem of
`Audit/VectorCutoff/Challenge.lean`, and proves the theorem from the
development's public index `AbsorptionCutoff.MainTheorems`.

Each audit definition, including the complete cutoff admissibility and limit
conditions, is a literal copy of its project counterpart, so the bridge
lemmas below all hold by `rfl`; they are stated explicitly rather than left to
unification so that any future drift between the two vocabularies fails loudly
here instead of silently changing what the comparator checks.
-/

namespace AbsorptionCutoff.StatementAudit.VectorCutoff

open Filter MeasureTheory ProbabilityTheory Topology

noncomputable section

/-! ## Total variation -/

/-- Total-variation distance `‖μ − ν‖_TV = sup_B |μ(B) − ν(B)|` over measurable `B`. -/
def tvDist {E : Type*} [MeasurableSpace E] (μ ν : Measure E) : ℝ :=
  ⨆ s : {s : Set E // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|

/-- The two early/late limiting conditions in the windowed cutoff convention. -/
def HasCutoffLimits (d : ℕ → ℕ → ℝ) (tCut w : ℕ → ℝ) : Prop :=
  Tendsto (fun c : ℝ => liminf (fun n => d n ⌊tCut n - c * w n⌋₊) atTop) atTop (𝓝 1) ∧
  Tendsto (fun c : ℝ => limsup (fun n => d n ⌊tCut n + c * w n⌋₊) atTop) atTop (𝓝 0)

/-- The cutoff center and window are asymptotically admissible. -/
def IsCutoffWindow (tCut w : ℕ → ℝ) : Prop :=
  Tendsto tCut atTop atTop ∧
  (∀ᶠ n in atTop, 0 < w n) ∧
  Asymptotics.IsLittleO atTop w tCut

/-- Full cutoff: admissibility of the center/window and both limiting conditions. -/
def HasCutoff (d : ℕ → ℕ → ℝ) (tCut w : ℕ → ℝ) : Prop :=
  IsCutoffWindow tCut w ∧ HasCutoffLimits d tCut w

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

/-! ## Bridges to the development

Each audit definition was copied verbatim from its source module, so every bridge
is `rfl`. Stating them makes any future divergence a build error. -/

lemma tvDist_eq {E : Type*} [MeasurableSpace E] (mu nu : Measure E) :
    tvDist mu nu = AbsorptionCutoff.tvDist mu nu := rfl

lemma HasCutoffLimits_eq : HasCutoffLimits = AbsorptionCutoff.HasCutoffLimits := rfl

lemma IsCutoffWindow_eq : IsCutoffWindow = AbsorptionCutoff.IsCutoffWindow := rfl

lemma HasCutoff_eq : HasCutoff = AbsorptionCutoff.HasCutoff := rfl

lemma V_eq : V = AbsorptionCutoff.V := rfl

lemma weightVar_eq (A : ℝ) (N : ℕ) : weightVar A N = AbsorptionCutoff.weightVar A N := rfl

lemma gaussianMat_eq (A : ℝ) (N : ℕ) : gaussianMat A N = AbsorptionCutoff.gaussianMat A N := rfl

lemma radiusSq_eq (N : ℕ) : radiusSq N = AbsorptionCutoff.radiusSq N := rfl

lemma Pstep_eq (N : ℕ) : Pstep N = AbsorptionCutoff.Pstep N := rfl

lemma Pkernel_eq (A : ℝ) (N : ℕ) : Pkernel A N = AbsorptionCutoff.Pkernel A N := rfl

lemma koenigsOrbitFactor_eq (A qStar q : ℝ) (n : ℕ) :
    koenigsOrbitFactor A qStar q n = AbsorptionCutoff.koenigsOrbitFactor A qStar q n := rfl

lemma koenigsOrbitProduct_eq (A qStar q : ℝ) :
    koenigsOrbitProduct A qStar q = AbsorptionCutoff.koenigsOrbitProduct A qStar q := rfl

lemma koenigsCoefficient_eq (A qStar q : ℝ) :
    koenigsCoefficient A qStar q = AbsorptionCutoff.koenigsCoefficient A qStar q := rfl

lemma supercriticalCutoffTime_eq' (A qStar q₀ : ℝ) (N : ℕ) :
    supercriticalCutoffTime A qStar q₀ N =
      AbsorptionCutoff.supercriticalCutoffTime A qStar q₀ N := rfl

/-! ## The theorem under audit -/

/-- **Supercritical vector cutoff** (paper `cor:gaussian-vector-cutoff`). Under the
manuscript's coordinate-box and radius-convergence assumptions, the vector chain
has a unique nonzero invariant probability in every sufficiently large dimension
and has total-variation cutoff at `supercriticalCutoffTime` with window `1`
against that family. -/
theorem gaussian_vector_cutoff
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
    ∃ π : (N : ℕ) → ProbabilityMeasure (Fin N → ℝ),
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N) (π N : Measure (Fin N → ℝ)) ∧
          (π N : Measure (Fin N → ℝ))
              ({0} : Set (Fin N → ℝ)) = 0 ∧
          ∀ ρ : ProbabilityMeasure (Fin N → ℝ),
            Kernel.Invariant
                (Pkernel A N) (ρ : Measure (Fin N → ℝ)) →
            (ρ : Measure (Fin N → ℝ))
                ({0} : Set (Fin N → ℝ)) = 0 →
            ρ = π N) ∧
      HasCutoff
        (fun N t =>
          tvDist (((Pkernel A N) ^ t) (x N))
            (π N : Measure (Fin N → ℝ)))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1)
:=
  AbsorptionCutoff.MainTheorems.gaussian_vector_cutoff
    x hA hqStar hfix hq₀ hq₀ne hbox hradius

end

end AbsorptionCutoff.StatementAudit.VectorCutoff
