/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.VectorReduction

/-!
# Invariant-law selection by Cesàro averages

Begins the paper's Krylov--Bogolyubov construction in
`prop:gaussian-compactness-selection`. The first algebraic layer defines the Cesàro
averages of the laws of a Markov chain and records their probability normalization.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace AbsorptionCutoff

variable {E : Type*} [MeasurableSpace E]

/-- The length-`T` Cesàro average `T⁻¹ ∑_{t<T} κ^t(q, ·)` of the laws of a Markov
chain. The definition is meaningful also at `T = 0`; probability normalization is
asserted separately under `0 < T`. -/
noncomputable def cesaroMeasure (κ : Kernel E E) (q : E) (T : ℕ) : Measure E :=
  ((T : ENNReal)⁻¹) • ∑ t ∈ Finset.range T, (κ ^ t) q

/-- A positive-length Cesàro average of Markov-chain laws is a probability measure. -/
theorem cesaroMeasure_isProbabilityMeasure (κ : Kernel E E) [IsMarkovKernel κ]
    (q : E) (T : ℕ) (hT : 0 < T) :
    IsProbabilityMeasure (cesaroMeasure κ q T) := by
  refine ⟨?_⟩
  simp only [cesaroMeasure, Measure.smul_apply, Measure.finsetSum_apply, measure_univ,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, smul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hT.ne') (by simp)

/-- Evolving a Cesàro law by one step shifts every kernel power in its defining
finite sum. This is the pre-telescoping identity in the Krylov--Bogolyubov argument. -/
theorem comp_cesaroMeasure (κ : Kernel E E) [IsMarkovKernel κ]
    (q : E) (T : ℕ) :
    κ ∘ₘ cesaroMeasure κ q T =
      ((T : ENNReal)⁻¹) • ∑ t ∈ Finset.range T, (κ ^ (t + 1)) q := by
  classical
  have hstep (t : ℕ) : κ ∘ₘ ((κ ^ t) q) = (κ ^ (t + 1)) q := by
    ext s hs
    rw [Measure.bind_apply hs κ.aemeasurable,
      ← Kernel.pow_succ_apply_eq_lintegral κ t q hs]
  have hsum (S : Finset ℕ) :
      κ ∘ₘ (∑ t ∈ S, (κ ^ t) q) = ∑ t ∈ S, (κ ^ (t + 1)) q := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert t S ht ih =>
        simp only [Finset.sum_insert ht, Measure.comp_add, hstep, ih]
  rw [cesaroMeasure, Measure.comp_smul, hsum]

/-- Subtraction-free form of the finite Cesàro telescoping identity:
`ν̄_T κ - ν̄_T = T⁻¹(κ^T(q,·) - δ_q)`. -/
theorem comp_cesaroMeasure_add (κ : Kernel E E) [IsMarkovKernel κ]
    (q : E) (T : ℕ) :
    κ ∘ₘ cesaroMeasure κ q T + ((T : ENNReal)⁻¹) • Measure.dirac q =
      cesaroMeasure κ q T + ((T : ENNReal)⁻¹) • (κ ^ T) q := by
  rw [comp_cesaroMeasure, cesaroMeasure, ← smul_add, ← smul_add]
  congr 1
  calc
    (∑ t ∈ Finset.range T, (κ ^ (t + 1)) q) + Measure.dirac q
        = (∑ t ∈ Finset.range T, (κ ^ (t + 1)) q) + (κ ^ 0) q := by
          rw [pow_zero]
          congr 1
    _ = ∑ t ∈ Finset.range (T + 1), (κ ^ t) q :=
      (Finset.sum_range_succ' (fun t => (κ ^ t) q) T).symm
    _ = (∑ t ∈ Finset.range T, (κ ^ t) q) + (κ ^ T) q :=
      Finset.sum_range_succ (fun t => (κ ^ t) q) T

/-- The paper's finite Cesàro telescoping formula, tested against a bounded measurable
real function. -/
theorem integral_comp_cesaroMeasure_sub (κ : Kernel E E) [IsMarkovKernel κ]
    (q : E) (T : ℕ) (hT : 0 < T) (φ : E → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, φ x ∂(κ ∘ₘ cesaroMeasure κ q T)) - ∫ x, φ x ∂cesaroMeasure κ q T =
      ((T : ENNReal)⁻¹).toReal * ((∫ x, φ x ∂((κ ^ T) q)) - φ q) := by
  letI : IsProbabilityMeasure (cesaroMeasure κ q T) :=
    cesaroMeasure_isProbabilityMeasure κ q T hT
  have hint (ξ : Measure E) [IsProbabilityMeasure ξ] : Integrable φ ξ :=
    (integrable_const C).mono' hφ.aestronglyMeasurable
      (Eventually.of_forall hφ_bound)
  have hces : Integrable φ (cesaroMeasure κ q T) := hint _
  have hcomp : Integrable φ (κ ∘ₘ cesaroMeasure κ q T) := hint _
  have hpow : Integrable φ ((κ ^ T) q) := hint _
  have hdir : Integrable φ (Measure.dirac q) := hint _
  have hdir_smul :
      Integrable φ (((T : ENNReal)⁻¹) • Measure.dirac q) :=
    hdir.smul_measure (by simpa using hT.ne')
  have hpow_smul :
      Integrable φ (((T : ENNReal)⁻¹) • (κ ^ T) q) :=
    hpow.smul_measure (by simpa using hT.ne')
  have heq := congrArg (fun ξ : Measure E => ∫ x, φ x ∂ξ)
    (comp_cesaroMeasure_add κ q T)
  rw [integral_add_measure hcomp hdir_smul, integral_add_measure hces hpow_smul,
    integral_smul_measure, integral_smul_measure,
    integral_dirac' φ q hφ.stronglyMeasurable, smul_eq_mul, smul_eq_mul] at heq
  linarith

/-- The Cesàro one-step discrepancy against a test function bounded by `C` is at most
`2C/T`. -/
theorem abs_integral_comp_cesaroMeasure_sub_le (κ : Kernel E E) [IsMarkovKernel κ]
    (q : E) (T : ℕ) (hT : 0 < T) (φ : E → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    |(∫ x, φ x ∂(κ ∘ₘ cesaroMeasure κ q T)) - ∫ x, φ x ∂cesaroMeasure κ q T|
      ≤ ((T : ENNReal)⁻¹).toReal * (2 * C) := by
  rw [integral_comp_cesaroMeasure_sub κ q T hT φ hφ C hφ_bound,
    abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  calc
    |(∫ x, φ x ∂((κ ^ T) q)) - φ q|
        ≤ |∫ x, φ x ∂((κ ^ T) q)| + |φ q| := abs_sub _ _
    _ ≤ C + C := by
      apply add_le_add
      · simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
          (norm_integral_le_of_norm_le_const
            (μ := (κ ^ T) q) (Eventually.of_forall hφ_bound))
      · simpa only [Real.norm_eq_abs] using hφ_bound q
    _ = 2 * C := by ring

/-- The real reciprocal coefficient in the Cesàro averages tends to zero. -/
lemma tendsto_cesaroCoeff :
    Tendsto (fun T : ℕ => ((T : ENNReal)⁻¹).toReal) atTop (𝓝 0) := by
  convert (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    ENNReal.tendsto_inv_nat_nhds_zero using 1
  · rfl
  · rfl

/-- The bounded-test Cesàro one-step discrepancy tends to zero: for any bounded
measurable `φ`, `∫ φ d(κ ∘ₘ ν̄_T) - ∫ φ dν̄_T → 0` as `T → ∞`. This is the smallness
estimate that makes any weak subsequential limit of the Cesàro averages `κ`-invariant. -/
theorem tendsto_integral_comp_cesaroMeasure_sub (κ : Kernel E E) [IsMarkovKernel κ]
    (q : E) (φ : E → ℝ) (hφ : Measurable φ) (C : ℝ) (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    Tendsto (fun T : ℕ =>
      (∫ x, φ x ∂(κ ∘ₘ cesaroMeasure κ q T)) - ∫ x, φ x ∂cesaroMeasure κ q T)
      atTop (𝓝 0) := by
  have hg : Tendsto (fun T : ℕ => ((T : ENNReal)⁻¹).toReal * (2 * C)) atTop (𝓝 0) := by
    simpa using tendsto_cesaroCoeff.mul_const (2 * C)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_gt_atTop 0] with T hT
  simpa using abs_integral_comp_cesaroMeasure_sub_le κ q T hT φ hφ C hφ_bound

/-! ## Feller property of the squared-radius kernel

The Krylov--Bogolyubov step needs the transition kernel `K_{A,N}` to be Feller:
for a continuous bounded test function `φ`, the map `q ↦ K_{A,N}φ(q)` is again
continuous. This is where the continuity of the random map `F_{A,N}` enters. -/

/-- The random map `F_{A,N}(q,g)` is jointly continuous in `(q,g)`. -/
lemma continuous_Fmap (A : ℝ) (N : ℕ) :
    Continuous (fun p : ℝ × (Fin N → ℝ) => Fmap A N p.1 p.2) := by
  unfold Fmap
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i _
  exact (continuous_tanh.comp (by fun_prop)).pow 2

/-- Continuity of the noise slice `g ↦ F_{A,N}(q,g)` at a fixed radius `q`. -/
lemma continuous_Fmap_right (A : ℝ) (N : ℕ) (q : ℝ) :
    Continuous (fun g : Fin N → ℝ => Fmap A N q g) := by
  unfold Fmap
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i _
  exact (continuous_tanh.comp (by fun_prop)).pow 2

/-- Continuity of the radius slice `q ↦ F_{A,N}(q,g)` at a fixed noise `g`. -/
lemma continuous_Fmap_left (A : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    Continuous (fun q : ℝ => Fmap A N q g) := by
  unfold Fmap
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i _
  exact (continuous_tanh.comp (by fun_prop)).pow 2

/-- The action of `K_{A,N}` on a bounded measurable test function `φ` is the Gaussian
average `∫ φ(F_{A,N}(q,g)) 𝒢_N(dg)`. This is the paper's displayed formula for
`K_{A,N}φ(q)`. -/
lemma integral_Kchain (A : ℝ) (N : ℕ) (q : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∫ y, φ y ∂(Kchain A N q) = ∫ g, φ (Fmap A N q g) ∂(gaussianVec N) := by
  rw [Kchain_apply, integral_map]
  · exact (continuous_Fmap_right A N q).aemeasurable
  · exact hφ.aestronglyMeasurable

/-- **Feller property of `K_{A,N}`.** For a continuous, bounded `φ`, the map
`q ↦ K_{A,N}φ(q) = ∫ φ(F_{A,N}(q,g)) 𝒢_N(dg)` is continuous, by continuity of
`F_{A,N}` and dominated convergence. -/
theorem continuous_integral_Kchain (A : ℝ) (N : ℕ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    {C : ℝ} (hφ_bound : ∀ y, ‖φ y‖ ≤ C) :
    Continuous (fun q => ∫ y, φ y ∂(Kchain A N q)) := by
  have hrw : ∀ q, (∫ y, φ y ∂(Kchain A N q)) =
      ∫ g, φ (Fmap A N q g) ∂(gaussianVec N) :=
    fun q => integral_Kchain A N q hφ.measurable
  simp_rw [hrw]
  refine continuous_of_dominated (bound := fun _ => C) (fun q => ?_) (fun q => ?_)
    (integrable_const C) ?_
  · exact (hφ.comp (continuous_Fmap_right A N q)).aestronglyMeasurable
  · exact Eventually.of_forall (fun g => hφ_bound _)
  · exact Eventually.of_forall (fun g => hφ.comp (continuous_Fmap_left A N g))

/-! ## The averaging (Fubini) bridge -/

/-- Bochner form of measure–kernel composition against a bounded measurable test
function: `∫ φ d(κ ∘ₘ μ) = ∫ q, (∫ φ d(κ q)) dμ`, i.e. testing the evolved measure
against `φ` equals testing `μ` against the kernel action `q ↦ ∫ φ d(κ q)`. -/
lemma integral_comp_measure (κ : Kernel E E) [IsMarkovKernel κ] (μ : Measure E)
    [IsProbabilityMeasure μ] {φ : E → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    ∫ y, φ y ∂(κ ∘ₘ μ) = ∫ q, (∫ y, φ y ∂(κ q)) ∂μ := by
  have hint : Integrable φ (κ ∘ₘ μ) :=
    (integrable_const C).mono' hφ.aestronglyMeasurable (Eventually.of_forall hφ_bound)
  rw [Measure.comp_eq_comp_const_apply] at hint ⊢
  rw [Kernel.integral_comp hint, Kernel.const_apply]

/-! ## Abstract Krylov--Bogolyubov invariance of a weak limit -/

/-- **Krylov--Bogolyubov, test-function form.** Suppose the laws `μs n` converge weakly
to `ν`, the Markov kernel `κ` is Feller with bounded-continuous action operator `Kf`
(`Kf f (q) = ∫ f d(κ q)`), and the one-step discrepancy
`∫ f d(κ ∘ₘ μs n) - ∫ f dμs n` vanishes along the sequence. Then every bounded
continuous `f` is `κ`-stationary under `ν`:
`∫ f d(κ ∘ₘ ν) = ∫ f dν`. -/
lemma integral_comp_eq_of_weakLimit {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] (κ : Kernel E E) [IsMarkovKernel κ]
    (μs : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hconv : Tendsto μs atTop (𝓝 ν))
    (Kf : BoundedContinuousFunction E ℝ → BoundedContinuousFunction E ℝ)
    (hKf : ∀ (f : BoundedContinuousFunction E ℝ) (q : E), Kf f q = ∫ y, f y ∂(κ q))
    (hdisc : ∀ f : BoundedContinuousFunction E ℝ,
      Tendsto (fun n => (∫ y, f y ∂(κ ∘ₘ (μs n : Measure E)))
        - ∫ y, f y ∂(μs n : Measure E)) atTop (𝓝 0))
    (f : BoundedContinuousFunction E ℝ) :
    ∫ y, f y ∂(κ ∘ₘ (ν : Measure E)) = ∫ y, f y ∂(ν : Measure E) := by
  -- The Feller action integrates to the evolved-measure test (Fubini bridge).
  have hbridge : ∀ μ : ProbabilityMeasure E,
      (∫ q, Kf f q ∂(μ : Measure E)) = ∫ y, f y ∂(κ ∘ₘ (μ : Measure E)) := by
    intro μ
    rw [integral_comp_measure κ (μ : Measure E) f.continuous.measurable f.norm_coe_le_norm]
    exact integral_congr_ae (Eventually.of_forall fun q => hKf f q)
  -- Weak convergence applied to `f` and to the (bounded continuous) Feller action `Kf f`.
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) f
  have h2 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) (Kf f)
  simp_rw [hbridge] at h2
  -- `∫ f d(κ ∘ₘ μs n) = (∫ f d(κ ∘ₘ μs n) - ∫ f dμs n) + ∫ f dμs n → 0 + ∫ f dν`.
  have hsum : Tendsto (fun n => ∫ y, f y ∂(κ ∘ₘ (μs n : Measure E))) atTop
      (𝓝 (∫ y, f y ∂(ν : Measure E))) := by
    simpa using (hdisc f).add h1
  exact tendsto_nhds_unique h2 hsum

/-- **Krylov--Bogolyubov invariance of a weak limit.** Under the same hypotheses, the
weak limit `ν` is an invariant measure for `κ`. Upgrades the per-test-function
stationarity `integral_comp_eq_of_weakLimit` to measure equality via the fact that
bounded continuous functions separate finite Borel measures. -/
theorem invariant_of_weakLimit {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [HasOuterApproxClosed E] [BorelSpace E] (κ : Kernel E E) [IsMarkovKernel κ]
    (μs : ℕ → ProbabilityMeasure E) (ν : ProbabilityMeasure E)
    (hconv : Tendsto μs atTop (𝓝 ν))
    (Kf : BoundedContinuousFunction E ℝ → BoundedContinuousFunction E ℝ)
    (hKf : ∀ (f : BoundedContinuousFunction E ℝ) (q : E), Kf f q = ∫ y, f y ∂(κ q))
    (hdisc : ∀ f : BoundedContinuousFunction E ℝ,
      Tendsto (fun n => (∫ y, f y ∂(κ ∘ₘ (μs n : Measure E)))
        - ∫ y, f y ∂(μs n : Measure E)) atTop (𝓝 0)) :
    Kernel.Invariant κ (ν : Measure E) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact integral_comp_eq_of_weakLimit κ μs ν hconv Kf hKf hdisc f

/-! ## Feller operator and Cesàro invariance for `K_{A,N}` -/

/-- The Feller action operator of `K_{A,N}` on bounded continuous functions:
`fellerOp A N f (q) = ∫ f(y) K_{A,N}(q, dy)`. Well-defined as a bounded continuous
function by the Feller property `continuous_integral_Kchain` and the probability bound
`‖K_{A,N}f‖ ≤ ‖f‖`. -/
noncomputable def fellerOp (A : ℝ) (N : ℕ) (f : BoundedContinuousFunction ℝ ℝ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q => ∫ y, f y ∂(Kchain A N q))
    (continuous_integral_Kchain A N f.continuous f.norm_coe_le_norm) ‖f‖
    (fun q => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := Kchain A N q) (Eventually.of_forall f.norm_coe_le_norm))

@[simp] lemma fellerOp_apply (A : ℝ) (N : ℕ) (f : BoundedContinuousFunction ℝ ℝ) (q : ℝ) :
    fellerOp A N f q = ∫ y, f y ∂(Kchain A N q) := rfl

/-! ## Support of the Cesàro averages in `[0,1]` (tightness input) -/

/-- One step of `K_{A,N}` from any point lands in `[0,1]`: `K_{A,N}(q, [0,1]ᶜ) = 0`,
because `F_{A,N}(q,g) ∈ [0,1]` for every noise `g` (`0 < N`). -/
lemma Kchain_apply_Icc_compl (A : ℝ) {N : ℕ} (hN : 0 < N) (q : ℝ) :
    Kchain A N q ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  have hpre : (Fmap A N q) ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun g hg => hg ⟨Fmap_nonneg A N q g, (Fmap_lt_one hN q g).le⟩
  rw [Kchain_apply, Measure.map_apply (continuous_Fmap_right A N q).measurable
    measurableSet_Icc.compl, hpre, measure_empty]

/-- Every invariant measure of `K_{A,N}` is carried by `[0,1]`. -/
lemma invariant_Kchain_apply_Icc_compl
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ν : Measure ℝ)
    (hν : Kernel.Invariant (Kchain A N) ν) :
    ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  calc
    ν ((Set.Icc (0 : ℝ) 1)ᶜ) =
        (Kchain A N ∘ₘ ν) ((Set.Icc (0 : ℝ) 1)ᶜ) :=
      congrArg (fun μ : Measure ℝ => μ ((Set.Icc (0 : ℝ) 1)ᶜ)) hν.def.symm
    _ = ∫⁻ q, Kchain A N q ((Set.Icc (0 : ℝ) 1)ᶜ) ∂ν :=
      Measure.bind_apply measurableSet_Icc.compl (Kchain A N).aemeasurable
    _ = 0 := by simp only [Kchain_apply_Icc_compl A hN, lintegral_zero]

/-- Every power `K_{A,N}^t(q, ·)` started from `q ∈ [0,1]` is supported in `[0,1]`. -/
lemma Kchain_pow_apply_Icc_compl (A : ℝ) {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    ((Kchain A N) ^ t) q ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  cases t with
  | zero =>
      rw [pow_zero]
      change Measure.dirac q ((Set.Icc (0 : ℝ) 1)ᶜ) = 0
      rw [Measure.dirac_apply' _ measurableSet_Icc.compl,
        Set.indicator_of_notMem (by simpa using hq)]
  | succ t =>
      have hstep : Kchain A N ∘ₘ ((Kchain A N ^ t) q) = (Kchain A N ^ (t + 1)) q := by
        ext s hs
        rw [Measure.bind_apply hs (Kchain A N).aemeasurable,
          ← Kernel.pow_succ_apply_eq_lintegral (Kchain A N) t q hs]
      rw [← hstep, Measure.bind_apply measurableSet_Icc.compl (Kchain A N).aemeasurable]
      simp [Kchain_apply_Icc_compl A hN]

/-- The Cesàro average of `K_{A,N}` started from `q ∈ [0,1]` is supported in `[0,1]`. -/
lemma cesaroMeasure_Icc_compl (A : ℝ) {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    cesaroMeasure (Kchain A N) q T ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  simp only [cesaroMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Kchain_pow_apply_Icc_compl A hN hq, Finset.sum_const_zero, smul_zero]

/-- **Invariance of Cesàro weak limits** (`prop:gaussian-compactness-selection`,
invariance part). If some scale sequence `T n → ∞` makes the Cesàro averages of
`K_{A,N}` started from `q` converge weakly to `ν`, then `ν` is invariant for `K_{A,N}`. -/
theorem invariant_of_cesaro_weakLimit (A : ℝ) (N : ℕ) (q : ℝ)
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop)
    (μs : ℕ → ProbabilityMeasure ℝ)
    (hμs : ∀ n, (μs n : Measure ℝ) = cesaroMeasure (Kchain A N) q (T n))
    (ν : ProbabilityMeasure ℝ) (hconv : Tendsto μs atTop (𝓝 ν)) :
    Kernel.Invariant (Kchain A N) (ν : Measure ℝ) := by
  refine invariant_of_weakLimit (Kchain A N) μs ν hconv (fellerOp A N)
    (fun f q => fellerOp_apply A N f q) ?_
  intro f
  simp_rw [hμs]
  exact (tendsto_integral_comp_cesaroMeasure_sub (Kchain A N) q (f : ℝ → ℝ)
    f.continuous.measurable ‖f‖ f.norm_coe_le_norm).comp hT

/-! ## Existence of an invariant Cesàro weak limit -/

/-- The `(n+1)`-length Cesàro average of `K_{A,N}` from `q`, packaged as a probability
measure (indexing by `n+1` keeps the length positive). -/
noncomputable def cesaroPM (A : ℝ) (N : ℕ) (q : ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨cesaroMeasure (Kchain A N) q (n + 1),
    cesaroMeasure_isProbabilityMeasure (Kchain A N) q (n + 1) n.succ_pos⟩

@[simp] lemma cesaroPM_toMeasure (A : ℝ) (N : ℕ) (q : ℝ) (n : ℕ) :
    (cesaroPM A N q n : Measure ℝ) = cesaroMeasure (Kchain A N) q (n + 1) := rfl

/-- **Subsequence form of invariant-law existence**
(`prop:gaussian-compactness-selection`, first assertion). For `0 < N` and `q ∈ [0,1]`,
the Cesàro averages of `K_{A,N}` started from `q` have a weakly convergent strict
subsequence whose limit is invariant and supported on `[0,1]`. -/
theorem exists_invariant_of_cesaro_with_subseq (A : ℝ) {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (ν : ProbabilityMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Tendsto (fun n => cesaroPM A N q (φ n)) atTop (𝓝 ν) ∧
      Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
      (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  have htight : IsTightMeasureSet
      {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range (cesaroPM A N q)} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    refine ⟨Set.Icc 0 1, isCompact_Icc, ?_⟩
    rintro μ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [cesaroPM_toMeasure, cesaroMeasure_Icc_compl A hN hq]
    exact zero_le
  obtain ⟨ν, _, φ, hφ, hconv⟩ :=
    (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
      (x := cesaroPM A N q) (fun n => subset_closure ⟨n, rfl⟩)
  have hT : Tendsto (fun n => φ n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (φ n)) hφ.tendsto_atTop
  have hmass (n : ℕ) :
      ((cesaroPM A N q (φ n) : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Icc 0 1) = 1 := by
    have hcompl :
        ((cesaroPM A N q (φ n) : ProbabilityMeasure ℝ) : Measure ℝ)
            ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
      rw [cesaroPM_toMeasure, cesaroMeasure_Icc_compl A hN hq]
    calc
      ((cesaroPM A N q (φ n) : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Icc 0 1) =
          ((cesaroPM A N q (φ n) : ProbabilityMeasure ℝ) : Measure ℝ) Set.univ :=
        measure_of_measure_compl_eq_zero hcompl
      _ = 1 := measure_univ
  have hport :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hconv
      (isClosed_Icc : IsClosed (Set.Icc (0 : ℝ) 1))
  change (atTop.limsup fun n =>
    ((cesaroPM A N q (φ n) : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Icc 0 1)) ≤
      (ν : Measure ℝ) (Set.Icc 0 1) at hport
  rw [show (fun n =>
      ((cesaroPM A N q (φ n) : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Icc 0 1)) =
        fun _ => 1 by funext n; exact hmass n] at hport
  have hIcc : (ν : Measure ℝ) (Set.Icc (0 : ℝ) 1) = 1 :=
    le_antisymm prob_le_one (by simpa only [limsup_const] using hport)
  refine ⟨ν, φ, hφ, hconv,
    invariant_of_cesaro_weakLimit A N q (fun n => φ n + 1) hT
      (fun n => cesaroPM A N q (φ n))
      (fun n => cesaroPM_toMeasure A N q (φ n)) ν hconv, ?_⟩
  rw [measure_compl measurableSet_Icc (by simp), hIcc]
  simp

/-- **Nonemptiness of the invariant-law set** `𝓘_{A,N}(q)`. This is the
existence-only projection of `exists_invariant_of_cesaro_with_subseq`. -/
theorem exists_invariant_of_cesaro (A : ℝ) {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ν : ProbabilityMeasure ℝ, Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
      (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  obtain ⟨ν, _, _, _, hν, hsupp⟩ :=
    exists_invariant_of_cesaro_with_subseq A hN hq
  exact ⟨ν, hν, hsupp⟩

/-- **Stationary equation** `eq:gaussian-q-stationary-equation`. An invariant law `ν`
of `K_{A,N}` satisfies, for every bounded measurable test function `φ`,
`∫ φ(q) ν(dq) = ∫ ∫ φ(F_{A,N}(q,g)) 𝒢_N(dg) ν(dq)`. -/
theorem stationary_equation (A : ℝ) (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν) {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    ∫ q, φ q ∂ν = ∫ q, (∫ g, φ (Fmap A N q g) ∂(gaussianVec N)) ∂ν := by
  have hbridge := integral_comp_measure (Kchain A N) ν hφ hφ_bound
  rw [hν] at hbridge
  rw [hbridge]
  exact integral_congr_ae (Eventually.of_forall fun q => integral_Kchain A N q hφ)

/-! ## Weak stationary equation for the vector chain -/

/-- The action of `P_{A,N}` on a measurable test function `φ` is the Gaussian-matrix
average `∫ φ(Pstep_N(x,𝖶)) gaussianMat_{A,N}(d𝖶)`. -/
lemma integral_Pkernel (A : ℝ) (N : ℕ) (x : Fin N → ℝ)
    {φ : (Fin N → ℝ) → ℝ} (hφ : Measurable φ) :
    ∫ y, φ y ∂(Pkernel A N x) = ∫ W, φ (Pstep N x W) ∂(gaussianMat A N) := by
  rw [Pkernel_apply, integral_map]
  · exact ((measurable_Pstep N).comp
      (by fun_prop : Measurable (Prod.mk x))).aemeasurable
  · exact hφ.aestronglyMeasurable

/-- **Weak vector stationary equation** `eq:gaussian-vector-weak-stationary-equation`.
An invariant law `π` of the unrounded vector kernel satisfies the stationary identity
against every bounded measurable test function. -/
theorem vector_stationary_equation (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ))
    [IsProbabilityMeasure π] (hπ : Kernel.Invariant (Pkernel A N) π)
    {φ : (Fin N → ℝ) → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hφ_bound : ∀ x, ‖φ x‖ ≤ C) :
    ∫ x, φ x ∂π =
      ∫ x, (∫ W, φ (Pstep N x W) ∂(gaussianMat A N)) ∂π := by
  have hbridge := integral_comp_measure (Pkernel A N) π hφ hφ_bound
  rw [hπ] at hbridge
  rw [hbridge]
  exact integral_congr_ae (Eventually.of_forall fun x => integral_Pkernel A N x hφ)

/-! ## Origin absorption for `K_{A,N}` (decomposition input) -/

/-- Splitting a real measure into its atom at the origin and its restriction away from
the origin. -/
lemma measure_eq_atom_zero_add_restrict_compl (ν : Measure ℝ) :
    ν = ν ({0} : Set ℝ) • Measure.dirac 0 + ν.restrict ({0}ᶜ : Set ℝ) := by
  rw [← Measure.restrict_singleton ν 0,
    Measure.restrict_add_restrict_compl (μ := ν) (measurableSet_singleton 0)]

/-- The origin is absorbing for `K_{A,N}`: `K_{A,N}(0, ·) = δ₀`, since `F_{A,N}(0,g) = 0`
for every noise `g`. -/
lemma Kchain_zero (A : ℝ) (N : ℕ) : Kchain A N 0 = Measure.dirac 0 := by
  have hconst : Fmap A N 0 = fun _ : Fin N → ℝ => (0 : ℝ) := by
    funext g
    simp [Fmap, Real.sqrt_zero, Real.tanh_zero]
  rw [Kchain_apply, hconst, Measure.map_const, measure_univ, one_smul]

/-- Evolving the point mass at the absorbing origin through `K_{A,N}` leaves it fixed. -/
lemma Kchain_comp_dirac_zero (A : ℝ) (N : ℕ) :
    Kchain A N ∘ₘ Measure.dirac 0 = Measure.dirac 0 := by
  rw [Measure.dirac_bind (Kernel.measurable _) 0, Kchain_zero]

/-- Kernel evolution respects the decomposition into the origin atom and the law away
from the origin. -/
lemma Kchain_comp_eq_atom_zero_add_restrict_compl (A : ℝ) (N : ℕ) (ν : Measure ℝ) :
    Kchain A N ∘ₘ ν =
      ν ({0} : Set ℝ) • Measure.dirac 0 + Kchain A N ∘ₘ ν.restrict ({0}ᶜ : Set ℝ) := by
  calc
    Kchain A N ∘ₘ ν =
        Kchain A N ∘ₘ
          (ν ({0} : Set ℝ) • Measure.dirac 0 + ν.restrict ({0}ᶜ : Set ℝ)) :=
      congrArg (fun μ : Measure ℝ => Kchain A N ∘ₘ μ)
        (measure_eq_atom_zero_add_restrict_compl ν)
    _ = ν ({0} : Set ℝ) • Measure.dirac 0 +
        Kchain A N ∘ₘ ν.restrict ({0}ᶜ : Set ℝ) := by
      rw [Measure.comp_add, Measure.comp_smul, Kchain_comp_dirac_zero]

/-- If a finite law is invariant for `K_{A,N}`, then its restriction away from the
absorbing origin is itself invariant (as a finite, not necessarily probability, measure). -/
lemma invariant_restrict_compl_zero (A : ℝ) (N : ℕ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν) :
    Kchain A N ∘ₘ ν.restrict ({0}ᶜ : Set ℝ) = ν.restrict ({0}ᶜ : Set ℝ) := by
  have heq :
      ν ({0} : Set ℝ) • Measure.dirac 0 + Kchain A N ∘ₘ ν.restrict ({0}ᶜ : Set ℝ) =
        ν ({0} : Set ℝ) • Measure.dirac 0 + ν.restrict ({0}ᶜ : Set ℝ) :=
    (Kchain_comp_eq_atom_zero_add_restrict_compl A N ν).symm.trans
      (hν.trans (measure_eq_atom_zero_add_restrict_compl ν))
  ext s hs
  have hatom_ne_top : (ν ({0} : Set ℝ) • Measure.dirac 0) s ≠ ⊤ := by
    rw [← Measure.restrict_singleton ν 0]
    exact measure_ne_top (ν.restrict ({0} : Set ℝ)) s
  apply (ENNReal.add_right_inj hatom_ne_top).mp
  simpa only [Measure.add_apply, hs] using congrArg (fun μ : Measure ℝ => μ s) heq

/-- The normalized nonzero component of a probability law:
`ν⁺ = (1 - ν{0})⁻¹ ν|_{{0}ᶜ}`. -/
noncomputable def nonzeroPart (ν : Measure ℝ) : Measure ℝ :=
  (1 - ν ({0} : Set ℝ))⁻¹ • ν.restrict ({0}ᶜ : Set ℝ)

/-- A measure with no atom at the origin is equal to its normalized nonzero
component. -/
lemma nonzeroPart_eq_self_of_apply_singleton_zero (ν : Measure ℝ)
    (hν0 : ν ({0} : Set ℝ) = 0) :
    nonzeroPart ν = ν := by
  have hae : ∀ᵐ x ∂ν, x ∈ ({0}ᶜ : Set ℝ) :=
    compl_mem_ae_iff.mpr hν0
  rw [nonzeroPart, hν0]
  simp [Measure.restrict_eq_self_of_ae_mem hae]

/-- If `ν` is not concentrated at the origin, its normalized nonzero component is a
probability measure. -/
theorem nonzeroPart_isProbabilityMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν0 : ν ({0} : Set ℝ) < 1) :
    IsProbabilityMeasure (nonzeroPart ν) := by
  refine ⟨?_⟩
  rw [nonzeroPart, Measure.smul_apply, Measure.restrict_apply_univ,
    prob_compl_eq_one_sub (measurableSet_singleton 0), smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (tsub_pos_iff_lt.mpr hν0)) (by finiteness)

/-- Normalizing the invariant restriction away from the absorbing origin preserves
invariance. -/
theorem invariant_nonzeroPart (A : ℝ) (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν) :
    Kernel.Invariant (Kchain A N) (nonzeroPart ν) := by
  change Kchain A N ∘ₘ nonzeroPart ν = nonzeroPart ν
  rw [nonzeroPart, Measure.comp_smul, invariant_restrict_compl_zero A N ν hν]

/-- If `ν` is supported on `[0,1]`, then its normalized nonzero component is supported
on `(0,1]`. -/
theorem nonzeroPart_Ioc_compl (ν : Measure ℝ)
    (hν_support : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) :
    nonzeroPart ν ((Set.Ioc (0 : ℝ) 1)ᶜ) = 0 := by
  have hsub :
      (Set.Ioc (0 : ℝ) 1)ᶜ ∩ ({0}ᶜ : Set ℝ) ⊆ (Set.Icc (0 : ℝ) 1)ᶜ := by
    intro x hx hxIcc
    apply hx.1
    exact ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hx.2), hxIcc.2⟩
  rw [nonzeroPart, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc.compl,
    measure_mono_null hsub hν_support, smul_eq_mul, mul_zero]

/-- Reconstructing the normalized nonzero scalar component through `J_{A,N}` gives an
invariant probability law for the unrounded vector chain. -/
theorem invariant_Pkernel_nonzeroPart (A : ℝ) (N : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hν : Kernel.Invariant (Kchain A N) ν)
    (hν0 : ν ({0} : Set ℝ) < 1) :
    IsProbabilityMeasure ((Jkernel A N) ∘ₘ nonzeroPart ν) ∧
      Kernel.Invariant (Pkernel A N) ((Jkernel A N) ∘ₘ nonzeroPart ν) := by
  letI : IsProbabilityMeasure (nonzeroPart ν) := nonzeroPart_isProbabilityMeasure ν hν0
  exact ⟨inferInstance,
    invariant_Pkernel_of_invariant_Kchain A N (nonzeroPart ν)
      (invariant_nonzeroPart A N ν hν)⟩

/-- `K_{A,N}` does not charge the origin from a positive radius: `K_{A,N}(s, {0}) = 0`
for `s > 0` (`A ≠ 0`, `0 < N`), since `F_{A,N}(s,g) = 0` forces every Gaussian coordinate
to vanish, a `𝒢_N`-null event. -/
lemma Kchain_singleton_zero (A : ℝ) {N : ℕ} (hN : 0 < N) (hA : A ≠ 0) {s : ℝ} (hs : 0 < s) :
    Kchain A N s ({(0 : ℝ)}) = 0 := by
  have hAs : A * Real.sqrt s ≠ 0 := mul_ne_zero hA (Real.sqrt_ne_zero'.2 hs)
  have hsub : (Fmap A N s) ⁻¹' {(0 : ℝ)} ⊆ {g : Fin N → ℝ | g ⟨0, hN⟩ = 0} := by
    intro g hg
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fmap] at hg
    have hNe : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.2 hN.ne')
    have hsum : ∑ i, Real.tanh (A * Real.sqrt s * g i) ^ 2 = 0 :=
      (mul_eq_zero.1 hg).resolve_left hNe
    have hterm : Real.tanh (A * Real.sqrt s * g ⟨0, hN⟩) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hsum _ (Finset.mem_univ _)
    have htanh : Real.tanh (A * Real.sqrt s * g ⟨0, hN⟩) = 0 :=
      pow_eq_zero_iff (by norm_num) |>.1 hterm
    have harg : A * Real.sqrt s * g ⟨0, hN⟩ = 0 :=
      Real.tanh_injective (by rw [Real.tanh_zero]; exact htanh)
    simpa using (mul_eq_zero.1 harg).resolve_left hAs
  rw [Kchain_apply, Measure.map_apply (continuous_Fmap_right A N s).measurable
    (measurableSet_singleton 0)]
  refine measure_mono_null hsub ?_
  haveI := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  have hset : {g : Fin N → ℝ | g ⟨0, hN⟩ = 0}
      = Function.eval (⟨0, hN⟩ : Fin N) ⁻¹' {0} := by ext g; simp [Function.eval]
  rw [hset, ← Measure.map_apply
    (measurable_pi_apply (⟨0, hN⟩ : Fin N) : Measurable (Function.eval (⟨0, hN⟩ : Fin N)))
    (measurableSet_singleton 0), gaussianVec, Measure.pi_map_eval]
  simp

/-! ## Existence of an invariant vector law -/

/-- **Existence of an invariant law for the unrounded vector chain**
(`prop:gaussian-compactness-selection`, vector-law existence, via
`prop:gaussian-tv-reduction`). For `0 < N` and `q ∈ [0,1]`, there is a probability
measure `π = ν J_{A,N}` invariant for `P_{A,N}`, obtained from an invariant scalar law
`ν ∈ 𝓘_{A,N}(q)` by reconstruction. -/
theorem exists_invariant_Pkernel_of_cesaro (A : ℝ) {N : ℕ} (hN : 0 < N) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∃ π : Measure (Fin N → ℝ), IsProbabilityMeasure π ∧ Kernel.Invariant (Pkernel A N) π := by
  obtain ⟨ν, hν, _⟩ := exists_invariant_of_cesaro A hN hq
  exact ⟨(Jkernel A N) ∘ₘ (ν : Measure ℝ), inferInstance,
    invariant_Pkernel_of_invariant_Kchain A N (ν : Measure ℝ) hν⟩

end AbsorptionCutoff
