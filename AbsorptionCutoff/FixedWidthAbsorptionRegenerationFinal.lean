/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthAbsorptionRegenerationAssembly

/-!
# Fixed-width finite-grid absorption regeneration final assembly

This continuation module owns the variable-horizon restart estimate,
return-time exponential moment, regeneration contraction, and final
absorption-tail assembly for Chapter 3.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- The deterministic-start entrance horizon appearing in the uniform rounded
entrance estimate, viewed as a function of the starting vector. -/
noncomputable def fixedWidthRoundedGridEntranceHorizon
    (ρ : ℝ) (N : ℕ) (c1 r : ℝ) (y0 : Fin N → ℝ) : ℕ :=
  ⌊c1 * Real.log
    (max 2 (fixedWidthRoundedInitialGridRadius ρ N y0)) + r⌋₊

/-- The rounded entrance horizon is measurable in its starting vector. -/
lemma measurable_fixedWidthRoundedGridEntranceHorizon
    (ρ : ℝ) (N : ℕ) (c1 r : ℝ) :
    Measurable (fixedWidthRoundedGridEntranceHorizon ρ N c1 r) := by
  unfold fixedWidthRoundedGridEntranceHorizon
  apply Measurable.nat_floor
  exact (measurable_const.max
    ((measurable_gaussianEuclideanNorm N).div_const ρ)).log.const_mul c1
      |>.add_const r

/-- Product event that a rounded path, started from its first coordinate,
survives above `Kstar` through the state-dependent entrance horizon. -/
def fixedWidthRoundedGridVariableSurvivalSet
    (ρ : ℝ) (N : ℕ) (Kstar c1 r : ℝ) :
    Set ((Fin N → ℝ) × fixedWidthMatrixSampleSpace N) :=
  {p | ∀ j ≤ fixedWidthRoundedGridEntranceHorizon ρ N c1 r p.1,
    Kstar < fixedWidthRoundedGridRadiusFrom ρ N p.1 j p.2}

/-- Sections of the variable-horizon product event are precisely the rounded
survival sets already controlled by the deterministic-start entrance bound. -/
lemma fixedWidthRoundedGridVariableSurvivalSet_section
    (ρ : ℝ) (N : ℕ) (Kstar c1 r : ℝ) (y0 : Fin N → ℝ) :
    {ω | (y0, ω) ∈
        fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r} =
      fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
        (fixedWidthRoundedGridEntranceHorizon ρ N c1 r y0) := rfl

/-- The rounded variable-horizon survival event is measurable in the product
of the starting vector and fresh matrix driver. -/
lemma measurableSet_fixedWidthRoundedGridVariableSurvivalSet
    (ρ : ℝ) (N : ℕ) (Kstar c1 r : ℝ) :
    MeasurableSet
      (fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r) := by
  have hhorizon : Measurable
      (fun p : (Fin N → ℝ) × fixedWidthMatrixSampleSpace N ↦
        fixedWidthRoundedGridEntranceHorizon ρ N c1 r p.1) :=
    (measurable_fixedWidthRoundedGridEntranceHorizon ρ N c1 r).comp
      measurable_fst
  rw [show fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r =
      ⋂ j : ℕ,
        {p | fixedWidthRoundedGridEntranceHorizon ρ N c1 r p.1 < j} ∪
          {p | Kstar < fixedWidthRoundedGridRadiusFrom ρ N p.1 j p.2} by
    ext p
    simp only [fixedWidthRoundedGridVariableSurvivalSet, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_union]
    constructor
    · intro h j
      exact lt_or_ge
        (fixedWidthRoundedGridEntranceHorizon ρ N c1 r p.1) j |>.elim
          Or.inl (fun hj ↦ Or.inr (h j hj))
    · intro h j hj
      exact (h j).resolve_left (not_lt_of_ge hj)]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_lt hhorizon measurable_const).union
    (measurableSet_lt measurable_const
      (measurable_fixedWidthRoundedGridRadiusFrom_prod ρ N j))

/-- A uniform deterministic-start survival bound passes unchanged to any
probability mixture of starting vectors by product-section integration. -/
lemma measureReal_prod_fixedWidthRoundedGridVariableSurvivalSet_le
    (A ρ : ℝ) (N : ℕ) (ν : Measure (Fin N → ℝ))
    [IsProbabilityMeasure ν] (Kstar c1 c2 c3 r : ℝ) (hc2 : 0 ≤ c2)
    (hbound : ∀ y0 : Fin N → ℝ,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            (fixedWidthRoundedGridEntranceHorizon ρ N c1 r y0)) ≤
        c2 * Real.exp (-c3 * r)) :
    (ν.prod (fixedWidthMatrixGaussianMeasure A N)).real
        (fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r) ≤
      c2 * Real.exp (-c3 * r) := by
  have hrhs : 0 ≤ c2 * Real.exp (-c3 * r) :=
    mul_nonneg hc2 (Real.exp_pos _).le
  have hprod :
      (ν.prod (fixedWidthMatrixGaussianMeasure A N))
          (fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r) ≤
        ENNReal.ofReal (c2 * Real.exp (-c3 * r)) := by
    rw [Measure.prod_apply
      (measurableSet_fixedWidthRoundedGridVariableSurvivalSet
        ρ N Kstar c1 r)]
    apply lintegral_le_const
    filter_upwards [] with y0
    rw [ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top (fixedWidthMatrixGaussianMeasure A N) _) hrhs]
    have hsection :
        Prod.mk y0 ⁻¹'
            fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r =
          fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            (fixedWidthRoundedGridEntranceHorizon ρ N c1 r y0) :=
      fixedWidthRoundedGridVariableSurvivalSet_section
        ρ N Kstar c1 r y0
    rw [hsection]
    exact hbound y0
  exact ENNReal.toReal_le_of_le_ofReal hrhs hprod

/-- Event that the positive rounded return time exceeds one plus the entrance
horizon determined by the time-one state. -/
def fixedWidthRoundedGridReturnExcessSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar c1 r : ℝ) :
    Set (fixedWidthMatrixSampleSpace N) :=
  {ω | ((fixedWidthRoundedGridEntranceHorizon ρ N c1 r
      (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω) + 1 : ℕ) : WithTop ℕ) <
    fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω}

/-- The random return-excess event is the pullback of the product survival
event by the time-one state and shifted future driver. -/
lemma fixedWidthRoundedGridReturnExcessSet_eq_preimage
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar c1 r : ℝ) :
    fixedWidthRoundedGridReturnExcessSet ρ N y0 Kstar c1 r =
      (fun ω : fixedWidthMatrixSampleSpace N ↦
        (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω,
          fixedWidthMatrixShift N 1 ω)) ⁻¹'
        fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r := by
  ext ω
  let n := fixedWidthRoundedGridEntranceHorizon ρ N c1 r
    (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω)
  have hreturn := succ_lt_fixedWidthRoundedGridReturnTimeFrom_iff
    ρ N y0 Kstar ω n
  have hentrance := lt_fixedWidthRoundedGridEntranceTimeFrom_iff
    ρ N (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω) Kstar
      (fixedWidthMatrixShift N 1 ω) n
  change (((n + 1 : ℕ) : WithTop ℕ) <
      fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω) ↔
    ∀ j ≤ n, Kstar < fixedWidthRoundedGridRadiusFrom ρ N
      (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω) j
        (fixedWidthMatrixShift N 1 ω)
  exact hreturn.trans hentrance

/-- The random return-excess event is measurable. -/
lemma measurableSet_fixedWidthRoundedGridReturnExcessSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar c1 r : ℝ) :
    MeasurableSet
      (fixedWidthRoundedGridReturnExcessSet ρ N y0 Kstar c1 r) := by
  rw [fixedWidthRoundedGridReturnExcessSet_eq_preimage]
  exact (measurableSet_fixedWidthRoundedGridVariableSurvivalSet
    ρ N Kstar c1 r).preimage
      ((measurable_fixedWidthRoundedVectorPathFrom ρ N y0 1).prodMk
        (measurable_fixedWidthMatrixShift N 1))

/-- Common entrance constants simultaneously give the max-log entrance tail
and the positive-return excess tail derived from its restart mixture. -/
theorem exists_uniform_fixedWidthRoundedGridEntrance_and_returnExcessSet_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar c1 c2 c3 : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      (∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ, ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            ⌊c1 * Real.log
              (max 2 (fixedWidthRoundedInitialGridRadius ρ N y0)) + r⌋₊) ≤
          c2 * Real.exp (-c3 * r)) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ, ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedGridReturnExcessSet
              ρ N y0 Kstar c1 r) ≤
          c2 * Real.exp (-c3 * r) := by
  obtain ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, hentrance⟩ :=
    exists_uniform_fixedWidthRoundedGridSurvivalSetFrom_max_bound
      hA hN hsub
  refine ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, hentrance, ?_⟩
  intro ρ hρ y0 r
  let μ := fixedWidthMatrixGaussianMeasure A N
  let state : fixedWidthMatrixSampleSpace N → (Fin N → ℝ) :=
    fixedWidthRoundedVectorPathFrom ρ N y0 1
  let ν : Measure (Fin N → ℝ) := Measure.map state μ
  have hstate : Measurable state :=
    measurable_fixedWidthRoundedVectorPathFrom ρ N y0 1
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hstate.aemeasurable
  have hmix :=
    measureReal_prod_fixedWidthRoundedGridVariableSurvivalSet_le
      A ρ N ν Kstar c1 c2 c3 r hc2.le (fun y ↦ by
        simpa only [fixedWidthRoundedGridEntranceHorizon] using
          hentrance ρ hρ y r)
  let restartMap : fixedWidthMatrixSampleSpace N →
      (Fin N → ℝ) × fixedWidthMatrixSampleSpace N :=
    fun ω ↦ (state ω, fixedWidthMatrixShift N 1 ω)
  have hrestart : Measurable restartMap :=
    hstate.prodMk (measurable_fixedWidthMatrixShift N 1)
  have hevent := measurableSet_fixedWidthRoundedGridVariableSurvivalSet
    ρ N Kstar c1 r
  calc
    μ.real (fixedWidthRoundedGridReturnExcessSet
        ρ N y0 Kstar c1 r) =
        μ.real (restartMap ⁻¹'
          fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r) := by
      rw [fixedWidthRoundedGridReturnExcessSet_eq_preimage]
    _ = (Measure.map restartMap μ).real
          (fixedWidthRoundedGridVariableSurvivalSet
            ρ N Kstar c1 r) := by
      change ENNReal.toReal
          (μ (restartMap ⁻¹'
            fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r)) =
        ENNReal.toReal ((Measure.map restartMap μ)
          (fixedWidthRoundedGridVariableSurvivalSet ρ N Kstar c1 r))
      rw [Measure.map_apply hrestart hevent]
    _ = (ν.prod μ).real
          (fixedWidthRoundedGridVariableSurvivalSet
            ρ N Kstar c1 r) := by
      congr 1
      exact map_prod_fixedWidthRoundedVectorPathFrom_shift
        A ρ N y0 1
    _ ≤ c2 * Real.exp (-c3 * r) := hmix

/-- Uniform exponential excess tail for the positive rounded return time,
with the random logarithmic offset determined by the time-one state. -/
theorem exists_uniform_fixedWidthRoundedGridReturnExcessSet_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar c1 c2 c3 : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ, ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedGridReturnExcessSet
              ρ N y0 Kstar c1 r) ≤
          c2 * Real.exp (-c3 * r) := by
  obtain ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, _hentrance, hreturn⟩ :=
    exists_uniform_fixedWidthRoundedGridEntrance_and_returnExcessSet_bound
      hA hN hsub
  exact ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, hreturn⟩

/-- An exponential return-excess tail rules out an infinite positive return
time almost surely. -/
lemma ae_fixedWidthRoundedGridReturnTimeFrom_ne_top_of_excess_bound
    {A ρ : ℝ} {N : ℕ} {y0 : Fin N → ℝ} {Kstar c1 c2 c3 : ℝ}
    (hc3 : 0 < c3)
    (hbound : ∀ r : ℝ,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnExcessSet
            ρ N y0 Kstar c1 r) ≤
        c2 * Real.exp (-c3 * r)) :
    ∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
      fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ≠ ⊤ := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let topSet : Set (fixedWidthMatrixSampleSpace N) :=
    {ω | fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω = ⊤}
  have hle : ∀ n : ℕ,
      μ.real topSet ≤ c2 * Real.exp (-c3 * (n : ℝ)) := by
    intro n
    have hsubset : topSet ⊆
        fixedWidthRoundedGridReturnExcessSet
          ρ N y0 Kstar c1 (n : ℝ) := by
      intro ω hω
      change fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω = ⊤ at hω
      change (((fixedWidthRoundedGridEntranceHorizon ρ N c1 (n : ℝ)
        (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω) + 1 : ℕ) :
          WithTop ℕ) <
        fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω)
      rw [hω]
      simp
    exact (measureReal_mono hsubset).trans (hbound n)
  have hlin : Tendsto (fun n : ℕ ↦ -c3 * (n : ℝ)) atTop atBot := by
    convert
      tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg
        (neg_lt_zero.mpr hc3) using 1
    ext n
    ring
  have hlim : Tendsto
      (fun n : ℕ ↦ c2 * Real.exp (-c3 * (n : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul c2
  have hrealzero : μ.real topSet = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' hlim hle
    · exact measureReal_nonneg
  have hzero : μ topSet = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top μ topSet)).mp hrealzero
  exact measure_eq_zero_iff_ae_notMem.mp hzero

/-- The random logarithmic offset in the positive-return estimate, including
the deterministic first time step. -/
noncomputable def fixedWidthRoundedGridReturnLogOffset
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (c1 : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) : ℝ :=
  1 + c1 * Real.log (max 2
    (fixedWidthRoundedInitialGridRadius ρ N
      (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω)))

/-- Nonnegative positive-return excess beyond the random logarithmic offset.
The arbitrary value of `untopA` at `⊤` is harmless because the return time is
almost surely finite under the exponential excess estimate. -/
noncomputable def fixedWidthRoundedGridReturnExcess
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar c1 : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) : ℝ :=
  max 0
    ((((fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω).untopA : ℕ) : ℝ) -
      fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω)

/-- The random logarithmic return offset is measurable. -/
lemma measurable_fixedWidthRoundedGridReturnLogOffset
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (c1 : ℝ) :
    Measurable (fixedWidthRoundedGridReturnLogOffset ρ N y0 c1) := by
  unfold fixedWidthRoundedGridReturnLogOffset
  exact measurable_const.add
    ((measurable_const.max
      (((measurable_gaussianEuclideanNorm N).comp
        (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 1)).div_const ρ))
      |>.log.const_mul c1)

/-- The nonnegative positive-return excess is measurable. -/
lemma measurable_fixedWidthRoundedGridReturnExcess
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar c1 : ℝ) :
    Measurable (fixedWidthRoundedGridReturnExcess ρ N y0 Kstar c1) := by
  unfold fixedWidthRoundedGridReturnExcess
  have hreturn : Measurable
      (fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar) :=
    (isStoppingTime_fixedWidthRoundedGridReturnTimeFrom
      ρ N y0 Kstar).measurable'
  have hreturnReal : Measurable
      (fun ω ↦ (((fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω).untopA : ℕ) : ℝ)) :=
    MeasurableEmbedding.natCast.measurable.comp hreturn.untopA
  exact measurable_const.max
    (hreturnReal.sub
      (measurable_fixedWidthRoundedGridReturnLogOffset ρ N y0 c1))

/-- The event bound for the `WithTop ℕ`-valued return time transfers to the
nonnegative real return excess used by layer cake. -/
lemma measure_fixedWidthRoundedGridReturnExcess_tail_le_of_bound
    {A ρ : ℝ} {N : ℕ} {y0 : Fin N → ℝ} {Kstar c1 c2 c3 : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hc3 : 0 < c3)
    (hbound : ∀ r : ℝ,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnExcessSet
            ρ N y0 Kstar c1 r) ≤
        c2 * Real.exp (-c3 * r)) :
    ∀ r, 0 < r →
      fixedWidthMatrixGaussianMeasure A N
          {ω | r < fixedWidthRoundedGridReturnExcess
            ρ N y0 Kstar c1 ω} ≤
        ENNReal.ofReal (c2 * Real.exp (-(c3 * r))) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let X := fixedWidthRoundedGridReturnExcess ρ N y0 Kstar c1
  have hfinite : ∀ᵐ ω ∂μ,
      fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ≠ ⊤ :=
    ae_fixedWidthRoundedGridReturnTimeFrom_ne_top_of_excess_bound hc3 hbound
  intro r hr
  have hsubset : {ω | r < X ω} ≤ᵐ[μ]
      fixedWidthRoundedGridReturnExcessSet
        ρ N y0 Kstar c1 r := by
    filter_upwards [hfinite] with ω htop hX
    let τ := fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω
    change τ ≠ ⊤ at htop
    let K1 := fixedWidthRoundedInitialGridRadius ρ N
      (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω)
    let x := c1 * Real.log (max 2 K1) + r
    have hinner : r <
        (((τ.untopA : ℕ) : ℝ) -
          fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω) := by
      change r < max 0
        ((((τ.untopA : ℕ) : ℝ) -
          fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω)) at hX
      exact (lt_max_iff.mp hX).resolve_left (not_lt_of_ge hr.le)
    have hmax : 1 < max 2 K1 :=
      lt_of_lt_of_le (by norm_num) (le_max_left 2 K1)
    have hx : 0 ≤ x := by
      dsimp only [x]
      exact add_nonneg
        (mul_nonneg hc1.le (Real.log_pos hmax).le) hr.le
    have htimeReal : (⌊x⌋₊ : ℝ) + 1 < ((τ.untopA : ℕ) : ℝ) := by
      have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
      unfold fixedWidthRoundedGridReturnLogOffset at hinner
      dsimp only [τ, K1, x] at hfloor ⊢
      linarith
    have htimeNat : ⌊x⌋₊ + 1 < (τ.untopA : ℕ) := by
      exact_mod_cast htimeReal
    change (((fixedWidthRoundedGridEntranceHorizon ρ N c1 r
      (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω) + 1 : ℕ) :
        WithTop ℕ) < τ)
    have hτcoe : (((τ.untopA : ℕ) : WithTop ℕ)) = τ := by
      cases hτval : τ with
      | top => exact (htop hτval).elim
      | coe n => rfl
    rw [← hτcoe]
    exact_mod_cast htimeNat
  calc
    μ {ω | r < X ω} ≤
        μ (fixedWidthRoundedGridReturnExcessSet
          ρ N y0 Kstar c1 r) := measure_mono_ae hsubset
    _ ≤ ENNReal.ofReal (c2 * Real.exp (-(c3 * r))) := by
      rw [ENNReal.le_ofReal_iff_toReal_le
        (measure_ne_top μ _) (mul_nonneg hc2 (Real.exp_pos _).le)]
      simpa only [μ, measureReal_def, neg_mul] using hbound r

/-- The exponential return-excess event bound yields every strictly smaller
positive exponential moment of the nonnegative real return excess. -/
lemma integrable_exp_mul_fixedWidthRoundedGridReturnExcess_of_bound
    {A ρ : ℝ} {N : ℕ} {y0 : Fin N → ℝ} {Kstar c1 c2 c3 s : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hc3 : 0 < c3)
    (hs : 0 < s) (hsc : s < c3)
    (hbound : ∀ r : ℝ,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnExcessSet
            ρ N y0 Kstar c1 r) ≤
        c2 * Real.exp (-c3 * r)) :
    Integrable (fun ω ↦ Real.exp
      (s * fixedWidthRoundedGridReturnExcess
        ρ N y0 Kstar c1 ω))
      (fixedWidthMatrixGaussianMeasure A N) := by
  apply integrable_exp_mul_of_measure_tail_le_exp
    (measurable_fixedWidthRoundedGridReturnExcess
      ρ N y0 Kstar c1).aemeasurable
    (Eventually.of_forall fun ω ↦ by
      unfold fixedWidthRoundedGridReturnExcess
      exact le_max_left _ _)
    hc2 hs hsc
  exact measure_fixedWidthRoundedGridReturnExcess_tail_le_of_bound
    hc1 hc2 hc3 hbound

/-- A sufficiently small exponential moment of the random logarithmic return
offset is integrable for every start in the bounded grid-radius region. -/
lemma integrable_exp_mul_fixedWidthRoundedGridReturnLogOffset
    {A : ℝ} (hA : 0 < A) {ρ : ℝ} (hρ : 0 < ρ)
    {N : ℕ} (hN : 0 < N) (y0 : Fin N → ℝ)
    {Kstar c1 s : ℝ} (hKstar : 0 ≤ Kstar)
    (hstart : fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar)
    (hc1 : 0 < c1) (hs : 0 < s)
    (hp_one : s * c1 ≤ 1) (hpN : s * c1 < N) :
    Integrable (fun ω ↦ Real.exp
      (s * fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω))
      (fixedWidthMatrixGaussianMeasure A N) := by
  let M := fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 0
  let b := Real.sqrt N / 2
  let p := s * c1
  have hp : 0 < p := mul_pos hs hc1
  have henv : Integrable
      (fun ω : fixedWidthMatrixSampleSpace N ↦
        (max 2 (M ω * Kstar + b)) ^ p)
      (fixedWidthMatrixGaussianMeasure A N) := by
    exact integrable_rpow_max_two_mul_add_fixedWidthRoundedRadiusMultiplierFrom
      hA hN ρ y0 0 hKstar (by positivity) hp hp_one hpN
  apply (henv.const_mul (Real.exp s)).mono'
  · exact (Real.continuous_exp.measurable.comp
      ((measurable_fixedWidthRoundedGridReturnLogOffset
        ρ N y0 c1).const_mul s)).aestronglyMeasurable
  · exact Eventually.of_forall fun ω ↦ by
      let K1 := fixedWidthRoundedInitialGridRadius ρ N
        (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω)
      have hK1 : K1 ≤ M ω * Kstar + b := by
        dsimp only [K1, M, b]
        exact fixedWidthRoundedGridRadiusFrom_one_le
          hρ hN y0 Kstar hstart ω
      have hbase : 0 < max 2 K1 :=
        lt_of_lt_of_le (by norm_num) (le_max_left 2 K1)
      have henvbase : 0 ≤ max 2 (M ω * Kstar + b) :=
        le_trans (by norm_num) (le_max_left _ _)
      have hmax : max 2 K1 ≤ max 2 (M ω * Kstar + b) :=
        max_le_max_left 2 hK1
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hoffset :
          Real.exp
              (s * fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω) =
            Real.exp s * (max 2 K1) ^ p := by
        unfold fixedWidthRoundedGridReturnLogOffset
        rw [Real.rpow_def_of_pos hbase]
        rw [← Real.exp_add]
        congr 1
        dsimp only [K1, p]
        ring
      rw [hoffset]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hbase.le hmax hp.le) (Real.exp_pos s).le

/-- The exponential logarithmic-offset moment is bounded by one fixed
reference multiplier integral, uniformly over the mesh and bounded start. -/
lemma integral_exp_mul_fixedWidthRoundedGridReturnLogOffset_le_common
    {A : ℝ} (hA : 0 < A) {ρ : ℝ} (hρ : 0 < ρ)
    {N : ℕ} (hN : 0 < N) (y0 : Fin N → ℝ)
    {Kstar c1 s : ℝ} (hKstar : 0 ≤ Kstar)
    (hstart : fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar)
    (hc1 : 0 < c1) (hs : 0 < s)
    (hp_one : s * c1 ≤ 1) (hpN : s * c1 < N) :
    (∫ ω, Real.exp
        (s * fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω)
        ∂fixedWidthMatrixGaussianMeasure A N) ≤
      Real.exp s *
        ∫ ω,
          (max 2
            (fixedWidthRoundedRadiusMultiplierFrom hN 1
                (0 : Fin N → ℝ) 0 ω * Kstar + Real.sqrt N / 2)) ^
              (s * c1)
          ∂fixedWidthMatrixGaussianMeasure A N := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let M := fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 0
  let Mref := fixedWidthRoundedRadiusMultiplierFrom hN 1
    (0 : Fin N → ℝ) 0
  let b := Real.sqrt N / 2
  let p := s * c1
  let F : ℝ → ℝ := fun z ↦ (max 2 (z * Kstar + b)) ^ p
  have hp : 0 < p := mul_pos hs hc1
  have hFmeas : Measurable F := by
    unfold F
    exact (Real.continuous_rpow_const hp.le).measurable.comp
      (measurable_const.max ((measurable_id.mul_const Kstar).add_const b))
  have hMident : IdentDistrib M Mref μ μ :=
    ⟨(measurable_fixedWidthRoundedRadiusMultiplierFrom
        hN ρ y0 0).aemeasurable,
      (measurable_fixedWidthRoundedRadiusMultiplierFrom
        hN 1 (0 : Fin N → ℝ) 0).aemeasurable,
      (map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ y0 0).trans
        (map_fixedWidthRoundedRadiusMultiplierFrom
          A hN 1 (0 : Fin N → ℝ) 0).symm⟩
  have hFintegral : (∫ ω, F (M ω) ∂μ) = ∫ ω, F (Mref ω) ∂μ :=
    (hMident.comp hFmeas).integral_eq
  have hleft := integrable_exp_mul_fixedWidthRoundedGridReturnLogOffset
    hA hρ hN y0 hKstar hstart hc1 hs hp_one hpN
  have hFint : Integrable (fun ω ↦ F (M ω)) μ := by
    change Integrable
      (fun ω : fixedWidthMatrixSampleSpace N ↦
        (max 2 (M ω * Kstar + b)) ^ p) μ
    exact integrable_rpow_max_two_mul_add_fixedWidthRoundedRadiusMultiplierFrom
      hA hN ρ y0 0 hKstar (by positivity) hp hp_one hpN
  have hpoint : ∀ ω : fixedWidthMatrixSampleSpace N,
      Real.exp (s * fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω) ≤
        Real.exp s * F (M ω) := by
    intro ω
    let K1 := fixedWidthRoundedInitialGridRadius ρ N
      (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω)
    have hK1 : K1 ≤ M ω * Kstar + b := by
      dsimp only [K1, M, b]
      exact fixedWidthRoundedGridRadiusFrom_one_le
        hρ hN y0 Kstar hstart ω
    have hbase : 0 < max 2 K1 :=
      lt_of_lt_of_le (by norm_num) (le_max_left 2 K1)
    have hmax : max 2 K1 ≤ max 2 (M ω * Kstar + b) :=
      max_le_max_left 2 hK1
    have hoffset :
        Real.exp
            (s * fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω) =
          Real.exp s * (max 2 K1) ^ p := by
      unfold fixedWidthRoundedGridReturnLogOffset
      rw [Real.rpow_def_of_pos hbase]
      rw [← Real.exp_add]
      congr 1
      dsimp only [K1, p]
      ring
    rw [hoffset]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hbase.le hmax hp.le) (Real.exp_pos s).le
  calc
    (∫ ω, Real.exp
        (s * fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω) ∂μ) ≤
        ∫ ω, Real.exp s * F (M ω) ∂μ :=
      integral_mono hleft (hFint.const_mul (Real.exp s)) hpoint
    _ = Real.exp s * ∫ ω, F (M ω) ∂μ := by
      rw [integral_const_mul]
    _ = Real.exp s * ∫ ω, F (Mref ω) ∂μ := by rw [hFintegral]

/-- At any exponent satisfying the three common smallness conditions, the
bounded-start positive rounded return time has an exponential moment. -/
lemma integrable_exp_mul_fixedWidthRoundedGridReturnTimeFrom_of_excess_bound
    {A : ℝ} (hA : 0 < A) {ρ : ℝ} (hρ : 0 < ρ)
    {N : ℕ} (hN : 0 < N) (y0 : Fin N → ℝ)
    {Kstar c1 c2 c3 s : ℝ} (hKstar : 0 ≤ Kstar)
    (hstart : fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar)
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hc3 : 0 < c3)
    (hs : 0 < s) (htwo_s_c3 : 2 * s < c3)
    (htwo_s_one : (2 * s) * c1 ≤ 1)
    (htwo_s_N : (2 * s) * c1 < N)
    (hbound : ∀ r : ℝ,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnExcessSet
            ρ N y0 Kstar c1 r) ≤
        c2 * Real.exp (-c3 * r)) :
    Integrable (fun ω ↦ Real.exp
      (s * (((fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω).untopA : ℕ) : ℝ)))
      (fixedWidthMatrixGaussianMeasure A N) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let f := fun ω : fixedWidthMatrixSampleSpace N ↦ Real.exp
    (s * fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω)
  let g := fun ω : fixedWidthMatrixSampleSpace N ↦ Real.exp
    (s * fixedWidthRoundedGridReturnExcess ρ N y0 Kstar c1 ω)
  have hfMeas : AEStronglyMeasurable f μ :=
    (Real.continuous_exp.measurable.comp
      ((measurable_fixedWidthRoundedGridReturnLogOffset
        ρ N y0 c1).const_mul s)).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable g μ :=
    (Real.continuous_exp.measurable.comp
      ((measurable_fixedWidthRoundedGridReturnExcess
        ρ N y0 Kstar c1).const_mul s)).aestronglyMeasurable
  have hfSq : Integrable (fun ω ↦ (f ω) ^ 2) μ := by
    apply (integrable_exp_mul_fixedWidthRoundedGridReturnLogOffset
      hA hρ hN y0 hKstar hstart hc1 (by positivity : 0 < 2 * s)
        htwo_s_one htwo_s_N).congr
    exact Eventually.of_forall fun ω ↦ by
      dsimp only [f]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
  have hgSq : Integrable (fun ω ↦ (g ω) ^ 2) μ := by
    apply (integrable_exp_mul_fixedWidthRoundedGridReturnExcess_of_bound
      hc1 hc2 hc3 (by positivity : 0 < 2 * s) htwo_s_c3 hbound).congr
    exact Eventually.of_forall fun ω ↦ by
      dsimp only [g]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
  have hfLp : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq hfMeas).mpr hfSq
  have hgLp : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq hgMeas).mpr hgSq
  have hprod : Integrable (f * g) μ := hfLp.integrable_mul hgLp
  refine hprod.mono' ?_ ?_
  · have hreturn : Measurable
        (fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar) :=
      (isStoppingTime_fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar).measurable'
    have hreturnReal : Measurable
        (fun ω ↦ (((fixedWidthRoundedGridReturnTimeFrom
          ρ N y0 Kstar ω).untopA : ℕ) : ℝ)) :=
      MeasurableEmbedding.natCast.measurable.comp hreturn.untopA
    exact (Real.continuous_exp.measurable.comp
      (hreturnReal.const_mul s)).aestronglyMeasurable
  · exact Eventually.of_forall fun ω ↦ by
      have hdecomp :
          (((fixedWidthRoundedGridReturnTimeFrom
              ρ N y0 Kstar ω).untopA : ℕ) : ℝ) ≤
            fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω +
              fixedWidthRoundedGridReturnExcess
                ρ N y0 Kstar c1 ω := by
        unfold fixedWidthRoundedGridReturnExcess
        have hmax := le_max_right (0 : ℝ)
          (((((fixedWidthRoundedGridReturnTimeFrom
            ρ N y0 Kstar ω).untopA : ℕ) : ℝ)) -
              fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω)
        linarith
      rw [Pi.mul_apply]
      change ‖Real.exp (s * _)‖ ≤ f ω * g ω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      dsimp only [f, g]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The bounded-start positive rounded return time has a positive exponential
moment whenever its random-offset excess has the uniform exponential tail. -/
lemma exists_pos_integrable_exp_mul_fixedWidthRoundedGridReturnTimeFrom_of_excess_bound
    {A : ℝ} (hA : 0 < A) {ρ : ℝ} (hρ : 0 < ρ)
    {N : ℕ} (hN : 0 < N) (y0 : Fin N → ℝ)
    {Kstar c1 c2 c3 : ℝ} (hKstar : 0 ≤ Kstar)
    (hstart : fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar)
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hc3 : 0 < c3)
    (hbound : ∀ r : ℝ,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnExcessSet
            ρ N y0 Kstar c1 r) ≤
        c2 * Real.exp (-c3 * r)) :
    ∃ s : ℝ, 0 < s ∧
      Integrable (fun ω ↦ Real.exp
        (s * (((fixedWidthRoundedGridReturnTimeFrom
          ρ N y0 Kstar ω).untopA : ℕ) : ℝ)))
        (fixedWidthMatrixGaussianMeasure A N) := by
  let m := min c3 (min (1 / c1) ((N : ℝ) / c1))
  let s := m / 4
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : 0 < m := by
    dsimp only [m]
    exact lt_min hc3 (lt_min (one_div_pos.mpr hc1) (div_pos hNreal hc1))
  have hs : 0 < s := div_pos hm (by norm_num)
  have hm_c3 : m ≤ c3 := min_le_left _ _
  have hm_one : m ≤ 1 / c1 :=
    (min_le_right c3 _).trans (min_le_left _ _)
  have hm_N : m ≤ (N : ℝ) / c1 :=
    (min_le_right c3 _).trans (min_le_right _ _)
  have htwo_s_c3 : 2 * s < c3 := by
    dsimp only [s]
    nlinarith
  have htwo_s_one : (2 * s) * c1 ≤ 1 := by
    have hc1nonneg := hc1.le
    dsimp only [s]
    calc
      (2 * (m / 4)) * c1 ≤ (2 * ((1 / c1) / 4)) * c1 := by
        gcongr
      _ = 1 / 2 := by field_simp [hc1.ne']; norm_num
      _ ≤ 1 := by norm_num
  have htwo_s_N : (2 * s) * c1 < N := by
    have hle : (2 * s) * c1 ≤ (N : ℝ) / 2 := by
      dsimp only [s]
      calc
        (2 * (m / 4)) * c1 ≤
            (2 * (((N : ℝ) / c1) / 4)) * c1 := by
          gcongr
        _ = (N : ℝ) / 2 := by field_simp [hc1.ne']; norm_num
    linarith
  refine ⟨s, hs, ?_⟩
  exact integrable_exp_mul_fixedWidthRoundedGridReturnTimeFrom_of_excess_bound
    hA hρ hN y0 hKstar hstart hc1 hc2 hc3 hs htwo_s_c3
      htwo_s_one htwo_s_N hbound

/-- One bounded radius and one positive exponential-moment parameter work for
the positive rounded return time at every mesh and every bounded start. -/
theorem exists_uniform_pos_integrable_exp_mul_fixedWidthRoundedGridReturnTimeFrom
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar s : ℝ, 0 < Kstar ∧ 0 < s ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ,
        fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar →
          (∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
            fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ≠ ⊤) ∧
          Integrable (fun ω ↦ Real.exp
            (s * (((fixedWidthRoundedGridReturnTimeFrom
              ρ N y0 Kstar ω).untopA : ℕ) : ℝ)))
            (fixedWidthMatrixGaussianMeasure A N) := by
  obtain ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, hreturn⟩ :=
    exists_uniform_fixedWidthRoundedGridReturnExcessSet_bound hA hN hsub
  let m := min c3 (min (1 / c1) ((N : ℝ) / c1))
  let s := m / 4
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : 0 < m := by
    dsimp only [m]
    exact lt_min hc3 (lt_min (one_div_pos.mpr hc1) (div_pos hNreal hc1))
  have hs : 0 < s := div_pos hm (by norm_num)
  have hm_c3 : m ≤ c3 := min_le_left _ _
  have hm_one : m ≤ 1 / c1 :=
    (min_le_right c3 _).trans (min_le_left _ _)
  have hm_N : m ≤ (N : ℝ) / c1 :=
    (min_le_right c3 _).trans (min_le_right _ _)
  have htwo_s_c3 : 2 * s < c3 := by
    dsimp only [s]
    nlinarith
  have htwo_s_one : (2 * s) * c1 ≤ 1 := by
    dsimp only [s]
    calc
      (2 * (m / 4)) * c1 ≤ (2 * ((1 / c1) / 4)) * c1 := by
        gcongr
      _ = 1 / 2 := by field_simp [hc1.ne']; norm_num
      _ ≤ 1 := by norm_num
  have htwo_s_N : (2 * s) * c1 < N := by
    have hle : (2 * s) * c1 ≤ (N : ℝ) / 2 := by
      dsimp only [s]
      calc
        (2 * (m / 4)) * c1 ≤
            (2 * (((N : ℝ) / c1) / 4)) * c1 := by
          gcongr
        _ = (N : ℝ) / 2 := by field_simp [hc1.ne']; norm_num
    linarith
  refine ⟨Kstar, s, hKstar, hs, ?_⟩
  intro ρ hρ y0 hstart
  have htail := hreturn ρ hρ y0
  constructor
  · exact ae_fixedWidthRoundedGridReturnTimeFrom_ne_top_of_excess_bound
      hc3 htail
  · exact integrable_exp_mul_fixedWidthRoundedGridReturnTimeFrom_of_excess_bound
      hA hρ hN y0 hKstar.le hstart hc1 hc2.le hc3 hs htwo_s_c3
        htwo_s_one htwo_s_N htail

/-- Quantitative layer cake: under a probability measure, an exponential tail
gives the explicit smaller exponential-moment bound
`1 + C s / (c - s)`. -/
lemma integral_exp_mul_le_of_measure_tail_le_exp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXmeas : AEMeasurable X μ) (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {C c s : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hsc : s < c)
    (htail : ∀ r, 0 < r →
      μ {ω | r < X ω} ≤ ENNReal.ofReal (C * Real.exp (-(c * r)))) :
    (∫ ω, Real.exp (s * X ω) ∂μ) ≤ 1 + C * s / (c - s) := by
  let g : ℝ → ℝ := fun r ↦ s * Real.exp (s * r)
  have hgcont : Continuous g :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hgint : ∀ r > 0, IntervalIntegrable g volume 0 r :=
    fun r _ ↦ hgcont.intervalIntegrable 0 r
  have hgnonneg : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ g r :=
    Eventually.of_forall fun r ↦ mul_nonneg hs.le (Real.exp_pos _).le
  have hlayer :=
    lintegral_comp_eq_lintegral_meas_lt_mul μ hXnonneg hXmeas hgint hgnonneg
  have hinterval (x : ℝ) :
      (∫ r in (0 : ℝ)..x, g r) = Real.exp (s * x) - 1 := by
    have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt (fun y : ℝ ↦ Real.exp (s * y)) (g r) r := by
      intro r _
      simpa [g, mul_comm] using ((hasDerivAt_id r).const_mul s).exp
    calc
      (∫ r in (0 : ℝ)..x, g r) =
          Real.exp (s * x) - Real.exp (s * 0) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          (hgcont.intervalIntegrable 0 x)
      _ = Real.exp (s * x) - 1 := by rw [mul_zero, Real.exp_zero]
  have htailIntegral :
      (∫⁻ r in Set.Ioi (0 : ℝ),
          μ {ω | r < X ω} * ENNReal.ofReal (g r)) ≤
        ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (C * s * Real.exp (-((c - s) * r))) := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    calc
      μ {ω | r < X ω} * ENNReal.ofReal (g r) ≤
          ENNReal.ofReal (C * Real.exp (-(c * r))) *
            ENNReal.ofReal (g r) := mul_le_mul_left (htail r hr) _
      _ = ENNReal.ofReal
          (C * Real.exp (-(c * r)) * (s * Real.exp (s * r))) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC (Real.exp_pos _).le)]
      _ = ENNReal.ofReal
          (C * s * Real.exp (-((c - s) * r))) := by
        congr 1
        calc
          C * Real.exp (-(c * r)) * (s * Real.exp (s * r)) =
              C * s * (Real.exp (-(c * r)) * Real.exp (s * r)) := by
            ring
          _ = C * s * Real.exp (-((c - s) * r)) := by
            rw [← Real.exp_add]
            congr 2
            ring
  have hdecay : IntegrableOn
      (fun r : ℝ ↦ C * s * Real.exp (-((c - s) * r)))
      (Set.Ioi 0) volume := by
    change Integrable
      (fun r : ℝ ↦ C * s * Real.exp (-((c - s) * r)))
      (volume.restrict (Set.Ioi 0))
    apply ((exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hsc)).const_mul
      (C * s)).congr
    exact Eventually.of_forall fun r ↦ by ring_nf
  have hdecayNonneg : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      0 ≤ C * s * Real.exp (-((c - s) * r)) :=
    Eventually.of_forall fun r ↦
      mul_nonneg (mul_nonneg hC hs.le) (Real.exp_pos _).le
  have hdecayIntegral :
      (∫ r in Set.Ioi (0 : ℝ),
          C * s * Real.exp (-((c - s) * r))) = C * s / (c - s) := by
    have hfun :
        (fun r : ℝ ↦ C * s * Real.exp (-((c - s) * r))) =
          fun r : ℝ ↦ C * s * Real.exp (-(c - s) * r) := by
      funext r
      congr 2
      ring
    rw [hfun]
    rw [integral_const_mul,
      integral_exp_mul_Ioi (neg_lt_zero.mpr (sub_pos.mpr hsc)) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [sub_ne_zero.mpr hsc.ne]
  have hminusLintegral :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω) - 1) ∂μ) ≤
        ENNReal.ofReal (C * s / (c - s)) := by
    calc
      (∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω) - 1) ∂μ) =
          ∫⁻ r in Set.Ioi (0 : ℝ),
            μ {ω | r < X ω} * ENNReal.ofReal (g r) := by
        simpa only [hinterval] using hlayer
      _ ≤ ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (C * s * Real.exp (-((c - s) * r))) :=
        htailIntegral
      _ = ENNReal.ofReal (C * s / (c - s)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hdecay hdecayNonneg,
          hdecayIntegral]
  have hexpInt := integrable_exp_mul_of_measure_tail_le_exp
    hXmeas hXnonneg hC hs hsc htail
  have hminusNonneg : ∀ᵐ ω ∂μ, 0 ≤ Real.exp (s * X ω) - 1 := by
    filter_upwards [hXnonneg] with ω hXω
    exact sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hs.le hXω))
  have hminusInt : Integrable (fun ω ↦ Real.exp (s * X ω) - 1) μ :=
    hexpInt.sub (integrable_const 1)
  have hquotNonneg : 0 ≤ C * s / (c - s) := by positivity
  have hminusIntegral :
      (∫ ω, Real.exp (s * X ω) - 1 ∂μ) ≤ C * s / (c - s) := by
    rw [← ENNReal.ofReal_le_ofReal_iff hquotNonneg,
      ofReal_integral_eq_lintegral_ofReal hminusInt hminusNonneg]
    exact hminusLintegral
  calc
    (∫ ω, Real.exp (s * X ω) ∂μ) =
        ∫ ω, (1 : ℝ) + (Real.exp (s * X ω) - 1) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω ↦ by ring
    _ = (∫ _ω, (1 : ℝ) ∂μ) +
          ∫ ω, Real.exp (s * X ω) - 1 ∂μ := by
      rw [integral_add (integrable_const 1) hminusInt]
    _ = 1 + ∫ ω, Real.exp (s * X ω) - 1 ∂μ := by simp
    _ ≤ 1 + C * s / (c - s) := by
      simpa only [add_comm] using add_le_add_left hminusIntegral 1

/-- The rounded positive-return excess has the explicit exponential-moment
bound supplied by its uniform exponential tail. -/
lemma integral_exp_mul_fixedWidthRoundedGridReturnExcess_le_of_bound
    {A ρ : ℝ} {N : ℕ} {y0 : Fin N → ℝ} {Kstar c1 c2 c3 s : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hc3 : 0 < c3)
    (hs : 0 < s) (hsc : s < c3)
    (hbound : ∀ r : ℝ,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnExcessSet
            ρ N y0 Kstar c1 r) ≤
        c2 * Real.exp (-c3 * r)) :
    (∫ ω, Real.exp
        (s * fixedWidthRoundedGridReturnExcess
          ρ N y0 Kstar c1 ω)
        ∂fixedWidthMatrixGaussianMeasure A N) ≤
      1 + c2 * s / (c3 - s) := by
  apply integral_exp_mul_le_of_measure_tail_le_exp
    (measurable_fixedWidthRoundedGridReturnExcess
      ρ N y0 Kstar c1).aemeasurable
    (Eventually.of_forall fun ω ↦ by
      unfold fixedWidthRoundedGridReturnExcess
      exact le_max_left _ _)
    hc2 hs hsc
  exact measure_fixedWidthRoundedGridReturnExcess_tail_le_of_bound
    hc1 hc2 hc3 hbound

/-- The full rounded positive-return moment is bounded by the arithmetic mean
of the offset and excess second-moment bounds. -/
lemma integral_exp_mul_fixedWidthRoundedGridReturnTimeFrom_le_of_excess_bound
    {A : ℝ} (hA : 0 < A) {ρ : ℝ} (hρ : 0 < ρ)
    {N : ℕ} (hN : 0 < N) (y0 : Fin N → ℝ)
    {Kstar c1 c2 c3 s : ℝ} (hKstar : 0 ≤ Kstar)
    (hstart : fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar)
    (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hc3 : 0 < c3)
    (hs : 0 < s) (htwo_s_c3 : 2 * s < c3)
    (htwo_s_one : (2 * s) * c1 ≤ 1)
    (htwo_s_N : (2 * s) * c1 < N)
    (hbound : ∀ r : ℝ,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnExcessSet
            ρ N y0 Kstar c1 r) ≤
        c2 * Real.exp (-c3 * r)) :
    (∫ ω, Real.exp
        (s * (((fixedWidthRoundedGridReturnTimeFrom
          ρ N y0 Kstar ω).untopA : ℕ) : ℝ))
        ∂fixedWidthMatrixGaussianMeasure A N) ≤
      (Real.exp (2 * s) *
          ∫ ω,
            (max 2
              (fixedWidthRoundedRadiusMultiplierFrom hN 1
                  (0 : Fin N → ℝ) 0 ω * Kstar + Real.sqrt N / 2)) ^
                ((2 * s) * c1)
            ∂fixedWidthMatrixGaussianMeasure A N +
        (1 + c2 * (2 * s) / (c3 - 2 * s))) / 2 := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let τ := fun ω : fixedWidthMatrixSampleSpace N ↦
    (((fixedWidthRoundedGridReturnTimeFrom
      ρ N y0 Kstar ω).untopA : ℕ) : ℝ)
  let f := fun ω : fixedWidthMatrixSampleSpace N ↦ Real.exp
    (s * fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω)
  let g := fun ω : fixedWidthMatrixSampleSpace N ↦ Real.exp
    (s * fixedWidthRoundedGridReturnExcess ρ N y0 Kstar c1 ω)
  have hfSq : Integrable (fun ω ↦ (f ω) ^ 2) μ := by
    apply (integrable_exp_mul_fixedWidthRoundedGridReturnLogOffset
      hA hρ hN y0 hKstar hstart hc1 (by positivity : 0 < 2 * s)
        htwo_s_one htwo_s_N).congr
    exact Eventually.of_forall fun ω ↦ by
      dsimp only [f]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
  have hgSq : Integrable (fun ω ↦ (g ω) ^ 2) μ := by
    apply (integrable_exp_mul_fixedWidthRoundedGridReturnExcess_of_bound
      hc1 hc2 hc3 (by positivity : 0 < 2 * s) htwo_s_c3 hbound).congr
    exact Eventually.of_forall fun ω ↦ by
      dsimp only [g]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
  have hfull : Integrable (fun ω ↦ Real.exp (s * τ ω)) μ := by
    exact integrable_exp_mul_fixedWidthRoundedGridReturnTimeFrom_of_excess_bound
      hA hρ hN y0 hKstar hstart hc1 hc2 hc3 hs htwo_s_c3
        htwo_s_one htwo_s_N hbound
  have hpoint : ∀ ω, Real.exp (s * τ ω) ≤
      ((f ω) ^ 2 + (g ω) ^ 2) / 2 := by
    intro ω
    have hdecomp : τ ω ≤
        fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω +
          fixedWidthRoundedGridReturnExcess ρ N y0 Kstar c1 ω := by
      dsimp only [τ]
      unfold fixedWidthRoundedGridReturnExcess
      have hmax := le_max_right (0 : ℝ)
        (((((fixedWidthRoundedGridReturnTimeFrom
          ρ N y0 Kstar ω).untopA : ℕ) : ℝ)) -
            fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω)
      linarith
    have hprod : Real.exp (s * τ ω) ≤ f ω * g ω := by
      dsimp only [f, g]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hyoung : f ω * g ω ≤ ((f ω) ^ 2 + (g ω) ^ 2) / 2 := by
      nlinarith [sq_nonneg (f ω - g ω)]
    exact hprod.trans hyoung
  have hfBound : (∫ ω, (f ω) ^ 2 ∂μ) ≤
      Real.exp (2 * s) *
        ∫ ω,
          (max 2
            (fixedWidthRoundedRadiusMultiplierFrom hN 1
                (0 : Fin N → ℝ) 0 ω * Kstar + Real.sqrt N / 2)) ^
              ((2 * s) * c1) ∂μ := by
    calc
      (∫ ω, (f ω) ^ 2 ∂μ) =
          ∫ ω, Real.exp
            ((2 * s) *
              fixedWidthRoundedGridReturnLogOffset ρ N y0 c1 ω) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω ↦ by
          dsimp only [f]
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
      _ ≤ _ := integral_exp_mul_fixedWidthRoundedGridReturnLogOffset_le_common
        hA hρ hN y0 hKstar hstart hc1 (by positivity)
          htwo_s_one htwo_s_N
  have hgBound : (∫ ω, (g ω) ^ 2 ∂μ) ≤
      1 + c2 * (2 * s) / (c3 - 2 * s) := by
    calc
      (∫ ω, (g ω) ^ 2 ∂μ) =
          ∫ ω, Real.exp
            ((2 * s) * fixedWidthRoundedGridReturnExcess
              ρ N y0 Kstar c1 ω) ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun ω ↦ by
          dsimp only [g]
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring
      _ ≤ _ :=
        integral_exp_mul_fixedWidthRoundedGridReturnExcess_le_of_bound
          hc1 hc2 hc3 (by positivity) htwo_s_c3 hbound
  calc
    (∫ ω, Real.exp (s * τ ω) ∂μ) ≤
        ∫ ω, ((f ω) ^ 2 + (g ω) ^ 2) / 2 ∂μ :=
      integral_mono hfull ((hfSq.add hgSq).div_const 2) hpoint
    _ = ((∫ ω, (f ω) ^ 2 ∂μ) + (∫ ω, (g ω) ^ 2 ∂μ)) / 2 := by
      rw [integral_div, integral_add hfSq hgSq]
    _ ≤ _ := by
      gcongr

/-- The common entrance constants can be retained while selecting one positive
exponent and one numerical return-moment bound uniformly over bounded starts. -/
theorem exists_uniform_fixedWidthRoundedGridEntrance_and_pos_exp_moment_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar c1 c2 c3 s B : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < s ∧ 0 < B ∧
      (∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ, ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            ⌊c1 * Real.log
              (max 2 (fixedWidthRoundedInitialGridRadius ρ N y0)) + r⌋₊) ≤
          c2 * Real.exp (-c3 * r)) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ,
        fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar →
          (∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
            fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ≠ ⊤) ∧
          Integrable (fun ω ↦ Real.exp
            (s * (((fixedWidthRoundedGridReturnTimeFrom
              ρ N y0 Kstar ω).untopA : ℕ) : ℝ)))
            (fixedWidthMatrixGaussianMeasure A N) ∧
          (∫ ω, Real.exp
              (s * (((fixedWidthRoundedGridReturnTimeFrom
                ρ N y0 Kstar ω).untopA : ℕ) : ℝ))
              ∂fixedWidthMatrixGaussianMeasure A N) ≤ B := by
  obtain ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, hentrance, hreturn⟩ :=
    exists_uniform_fixedWidthRoundedGridEntrance_and_returnExcessSet_bound
      hA hN hsub
  let m := min c3 (min (1 / c1) ((N : ℝ) / c1))
  let s := m / 4
  let B0 :=
    (Real.exp (2 * s) *
          ∫ ω,
            (max 2
              (fixedWidthRoundedRadiusMultiplierFrom hN 1
                  (0 : Fin N → ℝ) 0 ω * Kstar + Real.sqrt N / 2)) ^
                ((2 * s) * c1)
            ∂fixedWidthMatrixGaussianMeasure A N +
        (1 + c2 * (2 * s) / (c3 - 2 * s))) / 2
  let B := 1 + |B0|
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hm : 0 < m := by
    dsimp only [m]
    exact lt_min hc3 (lt_min (one_div_pos.mpr hc1) (div_pos hNreal hc1))
  have hs : 0 < s := div_pos hm (by norm_num)
  have hm_c3 : m ≤ c3 := min_le_left _ _
  have hm_one : m ≤ 1 / c1 :=
    (min_le_right c3 _).trans (min_le_left _ _)
  have hm_N : m ≤ (N : ℝ) / c1 :=
    (min_le_right c3 _).trans (min_le_right _ _)
  have htwo_s_c3 : 2 * s < c3 := by
    dsimp only [s]
    nlinarith
  have htwo_s_one : (2 * s) * c1 ≤ 1 := by
    dsimp only [s]
    calc
      (2 * (m / 4)) * c1 ≤ (2 * ((1 / c1) / 4)) * c1 := by
        gcongr
      _ = 1 / 2 := by field_simp [hc1.ne']; norm_num
      _ ≤ 1 := by norm_num
  have htwo_s_N : (2 * s) * c1 < N := by
    have hle : (2 * s) * c1 ≤ (N : ℝ) / 2 := by
      dsimp only [s]
      calc
        (2 * (m / 4)) * c1 ≤
            (2 * (((N : ℝ) / c1) / 4)) * c1 := by
          gcongr
        _ = (N : ℝ) / 2 := by field_simp [hc1.ne']; norm_num
    linarith
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨Kstar, c1, c2, c3, s, B, hKstar, hc1, hc2, hc3, hs, hB,
    hentrance, ?_⟩
  intro ρ hρ y0 hstart
  have htail := hreturn ρ hρ y0
  refine ⟨ae_fixedWidthRoundedGridReturnTimeFrom_ne_top_of_excess_bound
      hc3 htail, ?_, ?_⟩
  · exact integrable_exp_mul_fixedWidthRoundedGridReturnTimeFrom_of_excess_bound
      hA hρ hN y0 hKstar.le hstart hc1 hc2.le hc3 hs htwo_s_c3
        htwo_s_one htwo_s_N htail
  · apply (integral_exp_mul_fixedWidthRoundedGridReturnTimeFrom_le_of_excess_bound
      hA hρ hN y0 hKstar.le hstart hc1 hc2.le hc3 hs htwo_s_c3
        htwo_s_one htwo_s_N htail).trans
    change B0 ≤ B
    dsimp only [B]
    linarith [le_abs_self B0]

/-- One bounded radius, one positive exponent, and one numerical exponential
return-moment bound work uniformly over every mesh and bounded start. -/
theorem exists_uniform_pos_exp_moment_bound_fixedWidthRoundedGridReturnTimeFrom
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar s B : ℝ, 0 < Kstar ∧ 0 < s ∧ 0 < B ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ,
        fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar →
          (∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
            fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ≠ ⊤) ∧
          Integrable (fun ω ↦ Real.exp
            (s * (((fixedWidthRoundedGridReturnTimeFrom
              ρ N y0 Kstar ω).untopA : ℕ) : ℝ)))
            (fixedWidthMatrixGaussianMeasure A N) ∧
          (∫ ω, Real.exp
              (s * (((fixedWidthRoundedGridReturnTimeFrom
                ρ N y0 Kstar ω).untopA : ℕ) : ℝ))
              ∂fixedWidthMatrixGaussianMeasure A N) ≤ B := by
  obtain ⟨Kstar, _c1, _c2, _c3, s, B, hKstar, _hc1, _hc2, _hc3, hs, hB,
      _hentrance, hreturn⟩ :=
    exists_uniform_fixedWidthRoundedGridEntrance_and_pos_exp_moment_bound
      hA hN hsub
  exact ⟨Kstar, s, B, hKstar, hs, hB, hreturn⟩

/-- The first exact-start rounded-path step has the rounded transition-kernel
law from that deterministic start. -/
lemma map_fixedWidthRoundedVectorPathFrom_one
    (A ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) :
    Measure.map (fixedWidthRoundedVectorPathFrom ρ N y0 1)
        (fixedWidthMatrixGaussianMeasure A N) =
      roundedPkernel A ρ N y0 := by
  rw [show fixedWidthRoundedVectorPathFrom ρ N y0 1 =
      roundedPstep ρ N y0 ∘
        (fun ω : fixedWidthMatrixSampleSpace N ↦ ω 0) from rfl]
  have hstep : Measurable (roundedPstep ρ N y0) :=
    (measurable_Qρ ρ N).comp (measurable_Pstep_right N y0)
  rw [← Measure.map_map hstep (measurable_pi_apply (0 : ℕ))]
  change Measure.map (roundedPstep ρ N y0)
      (Measure.map (Function.eval 0)
        (Measure.infinitePi fun _ : ℕ ↦ gaussianMat A N)) = _
  rw [(measurePreserving_eval_infinitePi
    (fun _ : ℕ ↦ gaussianMat A N) 0).map_eq]
  exact (roundedPkernel_apply A ρ N y0).symm

/-- The bounded-region one-step absorption chance can be chosen before the
mesh, exposing the uniformity already present in its radial small-ball proof. -/
theorem exists_pos_forall_pos_le_measureReal_roundedPkernel_singleton_zero_of_gridRadius_le
    {A : ℝ} (hA : 0 < A) {Kstar : ℝ} (hKstar : 0 < Kstar)
    {N : ℕ} (hN : 0 < N) :
    ∃ p : ℝ, 0 < p ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ x : Fin N → ℝ,
        gaussianEuclideanNorm N x / ρ ≤ Kstar →
          p ≤ (roundedPkernel A ρ N x).real
            ({0} : Set (Fin N → ℝ)) := by
  let t : ℝ := 1 / (2 * Kstar)
  let p : ℝ := (fixedWidthRadialMultiplierLaw A N).real (Set.Iic t)
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hp : 0 < p :=
    measureReal_fixedWidthRadialMultiplierLaw_Iic_pos hA hN ht
  refine ⟨p, hp, ?_⟩
  intro ρ hρ x hx
  let radial : (Fin N → Fin N → ℝ) → ℝ :=
    fun W ↦ gaussianEuclideanNorm N
      (Matrix.mulVec W (fixedWidthUnitDirection hN x))
  have hradial : Measurable radial := by
    apply (measurable_gaussianEuclideanNorm N).comp
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    fun_prop
  have hradialLaw :
      Measure.map radial (gaussianMat A N) =
        fixedWidthRadialMultiplierLaw A N :=
    map_gaussianEuclideanNorm_mulVec_gaussianMat_of_unit A _
      (gaussianEuclideanNorm_fixedWidthUnitDirection hN x)
  have hsmallMeasure :
      (gaussianMat A N).real (radial ⁻¹' Set.Iic t) = p := by
    dsimp only [p]
    rw [← hradialLaw,
      map_measureReal_apply hradial measurableSet_Iic]
  have hsubset :
      radial ⁻¹' Set.Iic t ⊆
        roundedPstep ρ N x ⁻¹' ({0} : Set (Fin N → ℝ)) := by
    intro W hW
    change roundedPstep ρ N x W = 0
    apply roundedPstep_eq_zero_of_radialMultiplier_le
      hρ hKstar hN x W hx
    exact hW
  have hstep : Measurable (roundedPstep ρ N x) :=
    (measurable_Qρ ρ N).comp (measurable_Pstep_right N x)
  rw [roundedPkernel_apply,
    map_measureReal_apply hstep (measurableSet_singleton 0)]
  rw [← hsmallMeasure]
  exact measureReal_mono hsubset

/-- The first-step failure event for a deterministic exact-start rounded path. -/
def fixedWidthRoundedOneStepFailureSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) :
    Set (fixedWidthMatrixSampleSpace N) :=
  {ω | fixedWidthRoundedVectorPathFrom ρ N y0 1 ω ≠ 0}

lemma measurableSet_fixedWidthRoundedOneStepFailureSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) :
    MeasurableSet (fixedWidthRoundedOneStepFailureSet ρ N y0) := by
  change MeasurableSet
    ((fixedWidthRoundedVectorPathFrom ρ N y0 1) ⁻¹'
      ({0} : Set (Fin N → ℝ))ᶜ)
  exact (measurableSet_singleton 0).compl.preimage
    (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 1)

/-- A lower bound on one-step absorption transfers to the complementary
first-step failure probability on the exact-start product path space. -/
lemma measureReal_fixedWidthRoundedOneStepFailureSet_le_one_sub_of_le
    {A ρ p : ℝ} {N : ℕ} {y0 : Fin N → ℝ}
    (hp : p ≤ (roundedPkernel A ρ N y0).real
      ({0} : Set (Fin N → ℝ))) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedOneStepFailureSet ρ N y0) ≤ 1 - p := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let path := fixedWidthRoundedVectorPathFrom ρ N y0 1
  have hpath : Measurable path :=
    measurable_fixedWidthRoundedVectorPathFrom ρ N y0 1
  have hsuccess : μ.real (path ⁻¹' ({0} : Set (Fin N → ℝ))) =
      (roundedPkernel A ρ N y0).real ({0} : Set (Fin N → ℝ)) := by
    rw [← map_measureReal_apply hpath (measurableSet_singleton 0)]
    rw [map_fixedWidthRoundedVectorPathFrom_one]
  change μ.real (path ⁻¹' ({0} : Set (Fin N → ℝ)))ᶜ ≤ 1 - p
  rw [measureReal_compl
    ((measurableSet_singleton 0).preimage hpath), probReal_univ, hsuccess]
  linarith

/-- Weighted interpolation between an event probability and one exponential
moment. This is the failed-cycle Hölder estimate in arithmetic-mean form. -/
lemma integral_indicator_exp_mul_le_weighted
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {E : Set Ω}
    (hE : MeasurableSet E)
    {s θ B : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbase : Integrable (fun ω ↦ Real.exp (s * X ω)) μ)
    (hsmall : Integrable (fun ω ↦ Real.exp ((θ * s) * X ω)) μ)
    (hbaseBound : (∫ ω, Real.exp (s * X ω) ∂μ) ≤ B) :
    (∫ ω, E.indicator
        (fun ω ↦ Real.exp ((θ * s) * X ω)) ω ∂μ) ≤
      (1 - θ) * μ.real E + θ * B := by
  let base := fun ω : Ω ↦ Real.exp (s * X ω)
  let small := fun ω : Ω ↦ Real.exp ((θ * s) * X ω)
  let eventOne := E.indicator (fun _ : Ω ↦ (1 : ℝ))
  have heventOne : Integrable eventOne μ :=
    (integrable_const 1).indicator hE
  have hpoint : ∀ ω, E.indicator small ω ≤
      (1 - θ) * eventOne ω + θ * base ω := by
    intro ω
    by_cases hω : ω ∈ E
    · simp only [eventOne, Set.indicator_of_mem hω]
      have hamgm := Real.geom_mean_le_arith_mean2_weighted
        (sub_nonneg.mpr hθ1) hθ0 (by norm_num : 0 ≤ (1 : ℝ))
        (Real.exp_pos (s * X ω)).le (by ring)
      have hrpow : (Real.exp (s * X ω)) ^ θ = small ω := by
        dsimp only [small]
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
        congr 1
        ring
      simpa only [one_mul, Real.one_rpow, hrpow, base] using hamgm
    · simp only [eventOne, Set.indicator_of_notMem hω,
        mul_zero, zero_add]
      exact mul_nonneg hθ0 (Real.exp_pos _).le
  have heventIntegral : (∫ ω, eventOne ω ∂μ) = μ.real E := by
    dsimp only [eventOne]
    rw [integral_indicator_const (1 : ℝ) hE]
    simp
  calc
    (∫ ω, E.indicator small ω ∂μ) ≤
        ∫ ω, (1 - θ) * eventOne ω + θ * base ω ∂μ :=
      integral_mono (hsmall.indicator hE)
        (heventOne.const_mul (1 - θ) |>.add (hbase.const_mul θ)) hpoint
    _ = (1 - θ) * μ.real E +
          θ * ∫ ω, base ω ∂μ := by
      rw [integral_add (heventOne.const_mul (1 - θ))
        (hbase.const_mul θ), integral_const_mul, integral_const_mul]
      rw [heventIntegral]
    _ ≤ (1 - θ) * μ.real E + θ * B := by
      gcongr

/-- A positive event gap and a finite positive moment bound admit a positive
interpolation weight whose weighted bound is strictly below one. -/
lemma exists_pos_weighted_bound_lt_one
    {p B : ℝ} (hp : 0 < p) (hp_one : p ≤ 1) (hB : 0 < B) :
    ∃ θ q : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 < q ∧ q < 1 ∧
      (1 - θ) * (1 - p) + θ * B ≤ q := by
  let D := B + p + 1
  let θ := p / (2 * D)
  let q := 1 - p / 2
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hθ : 0 < θ := by
    dsimp only [θ]
    positivity
  have hθ_one : θ ≤ 1 := by
    dsimp only [θ]
    apply (div_le_one (by positivity : 0 < 2 * D)).2
    dsimp only [D]
    nlinarith
  have hθBp : θ * (B + p) ≤ p / 2 := by
    dsimp only [θ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * D)).2
    dsimp only [D]
    nlinarith
  have hq : 0 < q := by
    dsimp only [q]
    nlinarith
  have hq_one : q < 1 := by
    dsimp only [q]
    nlinarith
  refine ⟨θ, q, hθ, hθ_one, hq, hq_one, ?_⟩
  calc
    (1 - θ) * (1 - p) + θ * B ≤
        1 - p + θ * (B + p) := by
      nlinarith
    _ ≤ 1 - p + p / 2 := by linarith
    _ = q := by
      dsimp only [q]
      ring

/-- The common entrance constants can be retained through the strict
failed-cycle contraction obtained from minorization and interpolation. -/
theorem exists_uniform_fixedWidthRoundedGridEntrance_and_failedReturn_contraction
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar c1 c2 c3 s q : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      0 < s ∧ 0 < q ∧ q < 1 ∧
      (∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ, ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            ⌊c1 * Real.log
              (max 2 (fixedWidthRoundedInitialGridRadius ρ N y0)) + r⌋₊) ≤
          c2 * Real.exp (-c3 * r)) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ,
        fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar →
          (∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
            fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ≠ ⊤) ∧
          Integrable (fun ω ↦ Real.exp
            (s * (((fixedWidthRoundedGridReturnTimeFrom
              ρ N y0 Kstar ω).untopA : ℕ) : ℝ)))
            (fixedWidthMatrixGaussianMeasure A N) ∧
          Integrable
            ((fixedWidthRoundedOneStepFailureSet ρ N y0).indicator
              (fun ω ↦ Real.exp
                (s * (((fixedWidthRoundedGridReturnTimeFrom
                  ρ N y0 Kstar ω).untopA : ℕ) : ℝ))))
            (fixedWidthMatrixGaussianMeasure A N) ∧
          (∫ ω, (fixedWidthRoundedOneStepFailureSet ρ N y0).indicator
              (fun ω ↦ Real.exp
                (s * (((fixedWidthRoundedGridReturnTimeFrom
                  ρ N y0 Kstar ω).untopA : ℕ) : ℝ))) ω
              ∂fixedWidthMatrixGaussianMeasure A N) ≤ q := by
  obtain ⟨Kstar, c1, c2, c3, s0, B, hKstar, hc1, hc2, hc3, hs0, hB,
      hentrance, hreturn⟩ :=
    exists_uniform_fixedWidthRoundedGridEntrance_and_pos_exp_moment_bound
      hA hN hsub
  obtain ⟨p, hp, hminor⟩ :=
    exists_pos_forall_pos_le_measureReal_roundedPkernel_singleton_zero_of_gridRadius_le
      hA hKstar hN
  have hp_one : p ≤ 1 := by
    have hnorm0 : gaussianEuclideanNorm N (0 : Fin N → ℝ) = 0 :=
      (gaussianEuclideanNorm_eq_zero_iff N 0).2 rfl
    have hpKernel := hminor 1 (by norm_num) (0 : Fin N → ℝ) (by
      rw [hnorm0, zero_div]
      exact hKstar.le)
    exact hpKernel.trans measureReal_le_one
  obtain ⟨θ, q, hθ, hθ_one, hq, hq_one, hweighted⟩ :=
    exists_pos_weighted_bound_lt_one hp hp_one hB
  let s := θ * s0
  have hs : 0 < s := mul_pos hθ hs0
  have hs_le : s ≤ s0 := by
    dsimp only [s]
    nlinarith
  refine ⟨Kstar, c1, c2, c3, s, q, hKstar, hc1, hc2, hc3, hs, hq, hq_one,
    hentrance, ?_⟩
  intro ρ hρ y0 hstart
  obtain ⟨hfinite, hbase, hbaseBound⟩ := hreturn ρ hρ y0 hstart
  let μ := fixedWidthMatrixGaussianMeasure A N
  let τ := fun ω : fixedWidthMatrixSampleSpace N ↦
    (((fixedWidthRoundedGridReturnTimeFrom
      ρ N y0 Kstar ω).untopA : ℕ) : ℝ)
  let E := fixedWidthRoundedOneStepFailureSet ρ N y0
  have hτ : Measurable τ := by
    have hreturnMeas : Measurable
        (fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar) :=
      (isStoppingTime_fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar).measurable'
    exact MeasurableEmbedding.natCast.measurable.comp hreturnMeas.untopA
  have hsmall : Integrable (fun ω ↦ Real.exp (s * τ ω)) μ := by
    apply hbase.mono'
    · exact (Real.continuous_exp.measurable.comp
        (hτ.const_mul s)).aestronglyMeasurable
    · exact Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        change Real.exp (s * τ ω) ≤ Real.exp (s0 * τ ω)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hs_le (Nat.cast_nonneg _)
  have hE : MeasurableSet E :=
    measurableSet_fixedWidthRoundedOneStepFailureSet ρ N y0
  have hfailure : μ.real E ≤ 1 - p :=
    measureReal_fixedWidthRoundedOneStepFailureSet_le_one_sub_of_le
      (hminor ρ hρ y0 hstart)
  have hinterp := integral_indicator_exp_mul_le_weighted
    (μ := μ) (X := τ) (E := E) hE hθ.le hθ_one hbase hsmall hbaseBound
  have hcontract :
      (∫ ω, E.indicator (fun ω ↦ Real.exp (s * τ ω)) ω ∂μ) ≤ q := by
    calc
      (∫ ω, E.indicator (fun ω ↦ Real.exp (s * τ ω)) ω ∂μ) =
          ∫ ω, E.indicator
            (fun ω ↦ Real.exp ((θ * s0) * τ ω)) ω ∂μ := by
        rfl
      _ ≤ (1 - θ) * μ.real E + θ * B := hinterp
      _ ≤ (1 - θ) * (1 - p) + θ * B := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hfailure (sub_nonneg.mpr hθ_one)) le_rfl
      _ ≤ q := hweighted
  refine ⟨hfinite, hsmall, hsmall.indicator hE, ?_⟩
  exact hcontract

/-- Uniform failed-cycle contraction: after shrinking the common return
exponent, the exponential return moment restricted to failure of immediate
absorption is bounded by one common `q < 1`. -/
theorem exists_uniform_fixedWidthRoundedFailedReturn_contraction
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar s q : ℝ,
      0 < Kstar ∧ 0 < s ∧ 0 < q ∧ q < 1 ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ,
        fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar →
          (∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
            fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ≠ ⊤) ∧
          Integrable (fun ω ↦ Real.exp
            (s * (((fixedWidthRoundedGridReturnTimeFrom
              ρ N y0 Kstar ω).untopA : ℕ) : ℝ)))
            (fixedWidthMatrixGaussianMeasure A N) ∧
          Integrable
            ((fixedWidthRoundedOneStepFailureSet ρ N y0).indicator
              (fun ω ↦ Real.exp
                (s * (((fixedWidthRoundedGridReturnTimeFrom
                  ρ N y0 Kstar ω).untopA : ℕ) : ℝ))))
            (fixedWidthMatrixGaussianMeasure A N) ∧
          (∫ ω, (fixedWidthRoundedOneStepFailureSet ρ N y0).indicator
              (fun ω ↦ Real.exp
                (s * (((fixedWidthRoundedGridReturnTimeFrom
                  ρ N y0 Kstar ω).untopA : ℕ) : ℝ))) ω
              ∂fixedWidthMatrixGaussianMeasure A N) ≤ q := by
  obtain ⟨Kstar, _c1, _c2, _c3, s, q, hKstar, _hc1, _hc2, _hc3, hs, hq,
      hqone, _hentrance, hcontract⟩ :=
    exists_uniform_fixedWidthRoundedGridEntrance_and_failedReturn_contraction
      hA hN hsub
  exact ⟨Kstar, s, q, hKstar, hs, hq, hqone, hcontract⟩

/-- The exact-start rounded recursion remains at zero once started there. -/
@[simp] lemma fixedWidthRoundedVectorPathFrom_zero
    (ρ : ℝ) (N n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedVectorPathFrom ρ N 0 n ω = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [fixedWidthRoundedVectorPathFrom, ih]
      exact roundedPstep_zero ρ N (ω n)

/-- Nonabsorption at a later time implies nonabsorption at every earlier
deterministic restart time. -/
lemma fixedWidthRoundedVectorPathFrom_ne_zero_of_add_ne_zero
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (m n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N)
    (h : fixedWidthRoundedVectorPathFrom ρ N y0 (m + n) ω ≠ 0) :
    fixedWidthRoundedVectorPathFrom ρ N y0 m ω ≠ 0 := by
  intro hm
  rw [fixedWidthRoundedVectorPathFrom_add, hm,
    fixedWidthRoundedVectorPathFrom_zero] at h
  exact h rfl

/-- Exact-start survival of the rounded vector chain through one deterministic
time. -/
def fixedWidthRoundedAbsorptionSurvivalSetFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    Set (fixedWidthMatrixSampleSpace N) :=
  {ω | fixedWidthRoundedVectorPathFrom ρ N y0 n ω ≠ 0}

lemma measurableSet_fixedWidthRoundedAbsorptionSurvivalSetFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    MeasurableSet
      (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 n) := by
  change MeasurableSet
    ((fixedWidthRoundedVectorPathFrom ρ N y0 n) ⁻¹'
      ({0} : Set (Fin N → ℝ))ᶜ)
  exact (measurableSet_singleton 0).compl.preimage
    (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n)

/-- Joint variable-start survival event used in deterministic return-slice
restart integrals. -/
def fixedWidthRoundedVariableStartSurvivalSet
    (ρ : ℝ) (N n : ℕ) :
    Set ((Fin N → ℝ) × fixedWidthMatrixSampleSpace N) :=
  {p | fixedWidthRoundedVectorPathFrom ρ N p.1 n p.2 ≠ 0}

lemma measurableSet_fixedWidthRoundedVariableStartSurvivalSet
    (ρ : ℝ) (N n : ℕ) :
    MeasurableSet (fixedWidthRoundedVariableStartSurvivalSet ρ N n) := by
  change MeasurableSet
    ((fun p : (Fin N → ℝ) × fixedWidthMatrixSampleSpace N ↦
      fixedWidthRoundedVectorPathFrom ρ N p.1 n p.2) ⁻¹'
        ({0} : Set (Fin N → ℝ))ᶜ)
  exact (measurableSet_singleton 0).compl.preimage
    (measurable_fixedWidthRoundedVectorPathFrom_prod ρ N n)

lemma fixedWidthRoundedVariableStartSurvivalSet_section
    (ρ : ℝ) (N n : ℕ) (y0 : Fin N → ℝ) :
    Prod.mk y0 ⁻¹' fixedWidthRoundedVariableStartSurvivalSet ρ N n =
      fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 n := by
  rfl

/-- Exact characterization of a finite positive bounded-region return slice. -/
lemma fixedWidthRoundedGridReturnTimeFrom_eq_iff
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) {m : ℕ} (hm : 1 ≤ m) :
    fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω = m ↔
      fixedWidthRoundedGridRadiusFrom ρ N y0 m ω ≤ Kstar ∧
        ∀ j, 1 ≤ j → j < m →
          Kstar < fixedWidthRoundedGridRadiusFrom ρ N y0 j ω := by
  constructor
  · intro heq
    have hne : fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω ≠ ⊤ := by simp [heq]
    have hmem := MeasureTheory.hittingAfter_mem_set_of_ne_top
      (u := fixedWidthRoundedGridRadiusFrom ρ N y0)
      (s := Set.Iic Kstar) (n := 1) hne
    have hvalue :
        (fixedWidthRoundedGridReturnTimeFrom
          ρ N y0 Kstar ω).untopA = m := by
      rw [heq]
      rfl
    change fixedWidthRoundedGridRadiusFrom ρ N y0
      (fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω).untopA ω ≤ Kstar at hmem
    rw [hvalue] at hmem
    refine ⟨hmem, ?_⟩
    intro j h1j hjm
    have hjlt : (j : WithTop ℕ) <
        fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω := by
      rw [heq]
      exact_mod_cast hjm
    have hnotmem := MeasureTheory.notMem_of_lt_hittingAfter hjlt h1j
    change ¬fixedWidthRoundedGridRadiusFrom ρ N y0 j ω ≤ Kstar at hnotmem
    exact lt_of_not_ge hnotmem
  · rintro ⟨hmhit, hbefore⟩
    have hle : fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω ≤ m :=
      MeasureTheory.hittingAfter_le_of_mem hm hmhit
    have hge : (m : WithTop ℕ) ≤
        fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω := by
      rw [← not_lt]
      intro hlt
      obtain ⟨j, hj, hjmem⟩ :=
        (MeasureTheory.hittingAfter_lt_iff
          (u := fixedWidthRoundedGridRadiusFrom ρ N y0)
          (s := Set.Iic Kstar) (n := 1) (i := m) (ω := ω)).mp hlt
      exact (not_lt_of_ge hjmem) (hbefore j hj.1 hj.2)
    exact le_antisymm hle hge

/-- Exact finite positive-return slice on the canonical matrix path space. -/
def fixedWidthRoundedGridReturnSliceSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    Set (fixedWidthMatrixSampleSpace N) :=
  {ω | fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω = m}

lemma measurableSet_fixedWidthRoundedGridReturnSliceSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    MeasurableSet
      (fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m) := by
  exact (measurableSet_singleton (m : WithTop ℕ)).preimage
    ((isStoppingTime_fixedWidthRoundedGridReturnTimeFrom
      ρ N y0 Kstar).measurable')

/-- The same return slice represented on the strict matrix prefix of length
`m`; values of its zero extension at and after `m` are irrelevant. -/
def fixedWidthRoundedGridReturnSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    Set (Fin m → (Fin N → Fin N → ℝ)) :=
  {u | fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar
      (fixedWidthExtendMatrixPrefix N m u) = m}

lemma measurableSet_fixedWidthRoundedGridReturnSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    MeasurableSet
      (fixedWidthRoundedGridReturnSlicePrefixSet ρ N y0 Kstar m) := by
  exact (measurableSet_singleton (m : WithTop ℕ)).preimage
    (((isStoppingTime_fixedWidthRoundedGridReturnTimeFrom
      ρ N y0 Kstar).measurable').comp
        (measurable_fixedWidthExtendMatrixPrefix N m))

lemma fixedWidthRoundedGridReturnSliceSet_eq_preimage_prefix
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    {m : ℕ} (hm : 1 ≤ m) :
    fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m =
      fixedWidthMatrixPrefix N m ⁻¹'
        fixedWidthRoundedGridReturnSlicePrefixSet ρ N y0 Kstar m := by
  ext ω
  let ω' := fixedWidthExtendMatrixPrefix N m
    (fixedWidthMatrixPrefix N m ω)
  have hpath : ∀ j ≤ m,
      fixedWidthRoundedGridRadiusFrom ρ N y0 j ω =
        fixedWidthRoundedGridRadiusFrom ρ N y0 j ω' := by
    intro j hj
    unfold fixedWidthRoundedGridRadiusFrom fixedWidthRoundedVectorRadiusFrom
    apply congrArg (fun x : Fin N → ℝ ↦ gaussianEuclideanNorm N x / ρ)
    apply fixedWidthRoundedVectorPathFrom_eq_of_forall_lt ρ N y0 j
    intro k hk
    dsimp only [ω']
    simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix,
      lt_of_lt_of_le hk hj]
  change (fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω = m) ↔
    fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω' = m
  rw [fixedWidthRoundedGridReturnTimeFrom_eq_iff _ _ _ _ _ hm,
    fixedWidthRoundedGridReturnTimeFrom_eq_iff _ _ _ _ _ hm]
  constructor
  · rintro ⟨hnow, hbefore⟩
    refine ⟨hpath m le_rfl ▸ hnow, ?_⟩
    intro j h1j hjm
    rw [← hpath j hjm.le]
    exact hbefore j h1j hjm
  · rintro ⟨hnow, hbefore⟩
    refine ⟨hpath m le_rfl ▸ hnow, ?_⟩
    intro j h1j hjm
    rw [hpath j hjm.le]
    exact hbefore j h1j hjm

/-- Strict-prefix slice on which the positive return occurs at `m` and the
first absorption attempt failed. -/
def fixedWidthRoundedGridFailedReturnSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    Set (Fin m → (Fin N → Fin N → ℝ)) :=
  fixedWidthRoundedGridReturnSlicePrefixSet ρ N y0 Kstar m ∩
    {u | fixedWidthRoundedVectorPathFrom ρ N y0 1
      (fixedWidthExtendMatrixPrefix N m u) ≠ 0}

lemma measurableSet_fixedWidthRoundedGridFailedReturnSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    MeasurableSet
      (fixedWidthRoundedGridFailedReturnSlicePrefixSet
        ρ N y0 Kstar m) := by
  apply (measurableSet_fixedWidthRoundedGridReturnSlicePrefixSet
    ρ N y0 Kstar m).inter
  change MeasurableSet
    ((fixedWidthRoundedVectorPathFrom ρ N y0 1 ∘
      fixedWidthExtendMatrixPrefix N m) ⁻¹'
        ({0} : Set (Fin N → ℝ))ᶜ)
  exact (measurableSet_singleton 0).compl.preimage
    ((measurable_fixedWidthRoundedVectorPathFrom ρ N y0 1).comp
      (measurable_fixedWidthExtendMatrixPrefix N m))

lemma preimage_fixedWidthRoundedGridFailedReturnSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    {m : ℕ} (hm : 1 ≤ m) :
    fixedWidthMatrixPrefix N m ⁻¹'
        fixedWidthRoundedGridFailedReturnSlicePrefixSet
          ρ N y0 Kstar m =
      fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
        fixedWidthRoundedOneStepFailureSet ρ N y0 := by
  rw [fixedWidthRoundedGridFailedReturnSlicePrefixSet,
    Set.preimage_inter,
    ← fixedWidthRoundedGridReturnSliceSet_eq_preimage_prefix
      ρ N y0 Kstar hm]
  congr 1
  ext ω
  let ω' := fixedWidthExtendMatrixPrefix N m
    (fixedWidthMatrixPrefix N m ω)
  have hpath : fixedWidthRoundedVectorPathFrom ρ N y0 1 ω =
      fixedWidthRoundedVectorPathFrom ρ N y0 1 ω' := by
    apply fixedWidthRoundedVectorPathFrom_eq_of_forall_lt ρ N y0 1
    intro k hk
    dsimp only [ω']
    simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix,
      lt_of_lt_of_le hk hm]
  change (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω' ≠ 0) ↔
    fixedWidthRoundedVectorPathFrom ρ N y0 1 ω ≠ 0
  rw [hpath]

/-- Product-space event consisting of a failed exact return slice in the used
prefix and survival for `n` further steps under the fresh shifted driver. -/
def fixedWidthRoundedReturnSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m n : ℕ) :
    Set ((Fin m → (Fin N → Fin N → ℝ)) ×
      fixedWidthMatrixSampleSpace N) :=
  {p | p.1 ∈ fixedWidthRoundedGridFailedReturnSlicePrefixSet
      ρ N y0 Kstar m ∧
    fixedWidthRoundedVectorPathFrom ρ N
      (fixedWidthRoundedStateFromPrefix ρ N y0 m p.1) n p.2 ≠ 0}

lemma measurableSet_fixedWidthRoundedReturnSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m n : ℕ) :
    MeasurableSet
      (fixedWidthRoundedReturnSliceFutureSurvivalSet
        ρ N y0 Kstar m n) := by
  apply ((measurableSet_fixedWidthRoundedGridFailedReturnSlicePrefixSet
    ρ N y0 Kstar m).preimage measurable_fst).inter
  change MeasurableSet
    ((fun p : (Fin m → (Fin N → Fin N → ℝ)) ×
        fixedWidthMatrixSampleSpace N ↦
      fixedWidthRoundedVectorPathFrom ρ N
        (fixedWidthRoundedStateFromPrefix ρ N y0 m p.1) n p.2) ⁻¹'
          ({0} : Set (Fin N → ℝ))ᶜ)
  apply (measurableSet_singleton 0).compl.preimage
  exact (measurable_fixedWidthRoundedVectorPathFrom_prod ρ N n).comp
    (((measurable_fixedWidthRoundedStateFromPrefix ρ N y0 m).comp
      measurable_fst).prodMk measurable_snd)

/-- Pulling the prefix/fresh-future event back to the canonical driver gives
the failed return slice intersected with survival at the restarted time. -/
lemma preimage_fixedWidthRoundedReturnSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    (fun ω : fixedWidthMatrixSampleSpace N ↦
      (fixedWidthMatrixPrefix N m ω, fixedWidthMatrixShift N m ω)) ⁻¹'
        fixedWidthRoundedReturnSliceFutureSurvivalSet
          ρ N y0 Kstar m n =
      (fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
        fixedWidthRoundedOneStepFailureSet ρ N y0) ∩
          fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (m + n) := by
  ext ω
  change
    (fixedWidthMatrixPrefix N m ω ∈
        fixedWidthRoundedGridFailedReturnSlicePrefixSet
          ρ N y0 Kstar m ∧
      fixedWidthRoundedVectorPathFrom ρ N
        (fixedWidthRoundedStateFromPrefix ρ N y0 m
          (fixedWidthMatrixPrefix N m ω)) n
          (fixedWidthMatrixShift N m ω) ≠ 0) ↔
      ((ω ∈ fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∧
        ω ∈ fixedWidthRoundedOneStepFailureSet ρ N y0) ∧
        ω ∈ fixedWidthRoundedAbsorptionSurvivalSetFrom
          ρ N y0 (m + n))
  rw [fixedWidthRoundedStateFromPrefix_apply,
    ← fixedWidthRoundedVectorPathFrom_add]
  have hprefix := Set.ext_iff.mp
    (preimage_fixedWidthRoundedGridFailedReturnSlicePrefixSet
      ρ N y0 Kstar hm) ω
  exact and_congr hprefix Iff.rfl

/-- The joint law of a strict matrix prefix and the shifted future driver is
the prefix marginal times a fresh canonical driver. -/
lemma map_prod_fixedWidthMatrixPrefix_shift
    (A : ℝ) (N m : ℕ) :
    Measure.map
        (fun ω : fixedWidthMatrixSampleSpace N ↦
          (fixedWidthMatrixPrefix N m ω, fixedWidthMatrixShift N m ω))
        (fixedWidthMatrixGaussianMeasure A N) =
      (Measure.map (fixedWidthMatrixPrefix N m)
          (fixedWidthMatrixGaussianMeasure A N)).prod
        (fixedWidthMatrixGaussianMeasure A N) := by
  have hmap := (indepFun_fixedWidthMatrixPrefix_shift A N m)
    |>.map_prod_eq_prod_map_map
      (measurable_fixedWidthMatrixPrefix N m).aemeasurable
      (measurable_fixedWidthMatrixShift N m).aemeasurable
  rw [map_fixedWidthMatrixShift A N m] at hmap
  exact hmap

/-- A uniform remaining-horizon survival bound multiplies each failed exact
return slice after deterministic prefix/future factorization. -/
lemma measureReal_failedReturnSlice_inter_survival_le_mul
    {A ρ : ℝ} {N : ℕ} (y0 : Fin N → ℝ) {Kstar a : ℝ}
    {m : ℕ} (hm : 1 ≤ m) (n : ℕ) (ha : 0 ≤ a)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ Kstar →
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x n) ≤ a) :
    (fixedWidthMatrixGaussianMeasure A N).real
        ((fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
          fixedWidthRoundedOneStepFailureSet ρ N y0) ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom
              ρ N y0 (m + n)) ≤
      a * (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
          fixedWidthRoundedOneStepFailureSet ρ N y0) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let pref := fixedWidthMatrixPrefix N m
  let shift := fixedWidthMatrixShift N m
  let ν := Measure.map pref μ
  let S := fixedWidthRoundedGridFailedReturnSlicePrefixSet
    ρ N y0 Kstar m
  let E := fixedWidthRoundedReturnSliceFutureSurvivalSet
    ρ N y0 Kstar m n
  have hpref : Measurable pref := measurable_fixedWidthMatrixPrefix N m
  have hshift : Measurable shift := measurable_fixedWidthMatrixShift N m
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hpref.aemeasurable
  have hS : MeasurableSet S :=
    measurableSet_fixedWidthRoundedGridFailedReturnSlicePrefixSet
      ρ N y0 Kstar m
  have hE : MeasurableSet E :=
    measurableSet_fixedWidthRoundedReturnSliceFutureSurvivalSet
      ρ N y0 Kstar m n
  have hsection : ∀ u,
      μ (Prod.mk u ⁻¹' E) ≤ S.indicator (fun _ ↦ ENNReal.ofReal a) u := by
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      change u ∈ fixedWidthRoundedGridFailedReturnSlicePrefixSet
        ρ N y0 Kstar m at hu
      have hstate : fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedStateFromPrefix ρ N y0 m u) ≤ Kstar := by
        have heq := hu.1
        have hhit := (fixedWidthRoundedGridReturnTimeFrom_eq_iff
          ρ N y0 Kstar (fixedWidthExtendMatrixPrefix N m u) hm).1 heq
        change fixedWidthRoundedGridRadiusFrom ρ N y0 m
          (fixedWidthExtendMatrixPrefix N m u) ≤ Kstar
        exact hhit.1
      have hbound := hsurvival
        (fixedWidthRoundedStateFromPrefix ρ N y0 m u) hstate
      have hsecEq : Prod.mk u ⁻¹' E =
          fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N
            (fixedWidthRoundedStateFromPrefix ρ N y0 m u) n := by
        ext v
        change (u ∈ fixedWidthRoundedGridFailedReturnSlicePrefixSet
          ρ N y0 Kstar m ∧
            fixedWidthRoundedVectorPathFrom ρ N
              (fixedWidthRoundedStateFromPrefix ρ N y0 m u) n v ≠ 0) ↔
          fixedWidthRoundedVectorPathFrom ρ N
            (fixedWidthRoundedStateFromPrefix ρ N y0 m u) n v ≠ 0
        simp only [hu, true_and]
      rw [hsecEq]
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) ha]
      exact hbound
    · rw [Set.indicator_of_notMem hu]
      change u ∉ fixedWidthRoundedGridFailedReturnSlicePrefixSet
        ρ N y0 Kstar m at hu
      have hsecEmpty : Prod.mk u ⁻¹' E = ∅ := by
        ext v
        change (u ∈ fixedWidthRoundedGridFailedReturnSlicePrefixSet
          ρ N y0 Kstar m ∧
            fixedWidthRoundedVectorPathFrom ρ N
              (fixedWidthRoundedStateFromPrefix ρ N y0 m u) n v ≠ 0) ↔ False
        simp only [hu, false_and]
      rw [hsecEmpty, measure_empty]
  have hprod : (ν.prod μ) E ≤ ENNReal.ofReal a * ν S := by
    rw [Measure.prod_apply hE]
    calc
      (∫⁻ u, μ (Prod.mk u ⁻¹' E) ∂ν) ≤
          ∫⁻ u, S.indicator (fun _ ↦ ENNReal.ofReal a) u ∂ν :=
        lintegral_mono hsection
      _ = ENNReal.ofReal a * ν S := by
        rw [lintegral_indicator hS]
        simp
  have hprodReal : (ν.prod μ).real E ≤ a * ν.real S := by
    rw [measureReal_def, measureReal_def]
    calc
      ENNReal.toReal ((ν.prod μ) E) ≤
          ENNReal.toReal (ENNReal.ofReal a * ν S) :=
        ENNReal.toReal_mono (by finiteness) hprod
      _ = a * ENNReal.toReal (ν S) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
  have hcoeff : ν.real S = μ.real
      (fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
        fixedWidthRoundedOneStepFailureSet ρ N y0) := by
    dsimp only [ν, pref, S]
    rw [map_measureReal_apply
      (measurable_fixedWidthMatrixPrefix N m)
      (measurableSet_fixedWidthRoundedGridFailedReturnSlicePrefixSet
        ρ N y0 Kstar m)]
    rw [preimage_fixedWidthRoundedGridFailedReturnSlicePrefixSet
      ρ N y0 Kstar hm]
  let restart := fun ω : fixedWidthMatrixSampleSpace N ↦
    (pref ω, shift ω)
  have hrestart : Measurable restart := hpref.prodMk hshift
  calc
    μ.real
        ((fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
          fixedWidthRoundedOneStepFailureSet ρ N y0) ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (m + n)) =
        (Measure.map restart μ).real E := by
      rw [map_measureReal_apply hrestart hE]
      exact congrArg μ.real
        (preimage_fixedWidthRoundedReturnSliceFutureSurvivalSet
          ρ N y0 Kstar hm n).symm
    _ = (ν.prod μ).real E := by
      congr 1
      exact map_prod_fixedWidthMatrixPrefix_shift A N m
    _ ≤ a * ν.real S := hprodReal
    _ = a * μ.real
        (fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
          fixedWidthRoundedOneStepFailureSet ρ N y0) := by
      rw [hcoeff]

/-- Failed first attempt whose subsequent positive bounded-region return is
later than the deterministic horizon `t`. -/
def fixedWidthRoundedGridReturnTailFailureSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (t : ℕ) :
    Set (fixedWidthMatrixSampleSpace N) :=
  {ω | (t : WithTop ℕ) <
      fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω} ∩
    fixedWidthRoundedOneStepFailureSet ρ N y0

lemma measurableSet_fixedWidthRoundedGridReturnTailFailureSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (t : ℕ) :
    MeasurableSet
      (fixedWidthRoundedGridReturnTailFailureSet ρ N y0 Kstar t) := by
  apply (measurableSet_Ioi.preimage
    ((isStoppingTime_fixedWidthRoundedGridReturnTimeFrom
      ρ N y0 Kstar).measurable')).inter
  exact measurableSet_fixedWidthRoundedOneStepFailureSet ρ N y0

/-- Finite renewal partition: survival at `t ≥ 1` lies either before the
positive return or in one exact failed return slice followed by survival. -/
lemma fixedWidthRoundedAbsorptionSurvivalSetFrom_subset_returnTail_union_slices
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    {t : ℕ} (ht : 1 ≤ t) :
    fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t ⊆
      fixedWidthRoundedGridReturnTailFailureSet ρ N y0 Kstar t ∪
        ⋃ m ∈ Finset.Icc 1 t,
          (fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
            fixedWidthRoundedOneStepFailureSet ρ N y0) ∩
              fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t := by
  intro ω hsurvival
  have hfailure : ω ∈ fixedWidthRoundedOneStepFailureSet ρ N y0 := by
    change fixedWidthRoundedVectorPathFrom ρ N y0 1 ω ≠ 0
    obtain ⟨k, hk⟩ : ∃ k, t = 1 + k := ⟨t - 1, by omega⟩
    subst t
    exact fixedWidthRoundedVectorPathFrom_ne_zero_of_add_ne_zero
      ρ N y0 1 k ω hsurvival
  by_cases htail : (t : WithTop ℕ) <
      fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω
  · exact Or.inl ⟨htail, hfailure⟩
  · right
    have hle : fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω ≤ t := le_of_not_gt htail
    have hfinite : fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω ≠ ⊤ := fun htop ↦ by simp [htop] at hle
    let m := (fixedWidthRoundedGridReturnTimeFrom
      ρ N y0 Kstar ω).untopA
    have heq : fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω = m := by
      cases hval : fixedWidthRoundedGridReturnTimeFrom
          ρ N y0 Kstar ω with
      | top => exact (hfinite hval).elim
      | coe k =>
          dsimp only [m]
          rw [hval]
          rfl
    have hmone : 1 ≤ m := by
      have hone := one_le_fixedWidthRoundedGridReturnTimeFrom
        ρ N y0 Kstar ω
      rw [heq] at hone
      exact_mod_cast hone
    have hmt : m ≤ t := by
      rw [heq] at hle
      exact_mod_cast hle
    apply Set.mem_iUnion.mpr ⟨m, ?_⟩
    apply Set.mem_iUnion.mpr ⟨by simpa using Finset.mem_Icc.mpr ⟨hmone, hmt⟩, ?_⟩
    exact ⟨⟨heq, hfailure⟩, hsurvival⟩

/-- Real-measure union bound associated with the finite renewal partition. -/
lemma measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_le_returnTail_add_sum
    (A ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    {t : ℕ} (ht : 1 ≤ t) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnTailFailureSet ρ N y0 Kstar t) +
        ∑ m ∈ Finset.Icc 1 t,
          (fixedWidthMatrixGaussianMeasure A N).real
            ((fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
              fixedWidthRoundedOneStepFailureSet ρ N y0) ∩
                fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let tail := fixedWidthRoundedGridReturnTailFailureSet ρ N y0 Kstar t
  let slice := fun m : ℕ ↦
    (fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
      fixedWidthRoundedOneStepFailureSet ρ N y0) ∩
        fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t
  calc
    μ.real (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
        μ.real (tail ∪ ⋃ m ∈ Finset.Icc 1 t, slice m) :=
      measureReal_mono
        (fixedWidthRoundedAbsorptionSurvivalSetFrom_subset_returnTail_union_slices
          ρ N y0 Kstar ht)
    _ ≤ μ.real tail + μ.real (⋃ m ∈ Finset.Icc 1 t, slice m) :=
      measureReal_union_le tail _
    _ ≤ μ.real tail + ∑ m ∈ Finset.Icc 1 t, μ.real (slice m) := by
      exact add_le_add le_rfl
        (measureReal_biUnion_finset_le (μ := μ) (Finset.Icc 1 t) slice)

/-- The exponentially weighted failed-return tail and all exact finite slices
are jointly dominated by the single failed-return exponential moment. -/
lemma exp_mul_measureReal_returnTail_add_sum_le_integral_failedReturn
    {A ρ s : ℝ} {N : ℕ} (y0 : Fin N → ℝ) (Kstar : ℝ) (t : ℕ)
    (hs : 0 ≤ s)
    (hfinite : ∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
      fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ≠ ⊤)
    (hInt : Integrable
      ((fixedWidthRoundedOneStepFailureSet ρ N y0).indicator
        (fun ω ↦ Real.exp
          (s * (((fixedWidthRoundedGridReturnTimeFrom
            ρ N y0 Kstar ω).untopA : ℕ) : ℝ))))
      (fixedWidthMatrixGaussianMeasure A N)) :
    Real.exp (s * t) *
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridReturnTailFailureSet
            ρ N y0 Kstar t) +
      ∑ m ∈ Finset.Icc 1 t,
        Real.exp (s * m) *
          (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
              fixedWidthRoundedOneStepFailureSet ρ N y0) ≤
      ∫ ω, (fixedWidthRoundedOneStepFailureSet ρ N y0).indicator
        (fun ω ↦ Real.exp
          (s * (((fixedWidthRoundedGridReturnTimeFrom
            ρ N y0 Kstar ω).untopA : ℕ) : ℝ))) ω
        ∂fixedWidthMatrixGaussianMeasure A N := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let τ := fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar
  let F := fixedWidthRoundedOneStepFailureSet ρ N y0
  let tail := fixedWidthRoundedGridReturnTailFailureSet ρ N y0 Kstar t
  let I := Finset.Icc 1 t
  let slice := fun m ↦ fixedWidthRoundedGridReturnSliceSet
    ρ N y0 Kstar m ∩ F
  let w := fun ω : fixedWidthMatrixSampleSpace N ↦
    tail.indicator (fun _ ↦ Real.exp (s * t)) ω +
      ∑ m ∈ I, (slice m).indicator (fun _ ↦ Real.exp (s * m)) ω
  let rhs := F.indicator (fun ω ↦
    Real.exp (s * (((τ ω).untopA : ℕ) : ℝ)))
  have hF : MeasurableSet F :=
    measurableSet_fixedWidthRoundedOneStepFailureSet ρ N y0
  have htail : MeasurableSet tail :=
    measurableSet_fixedWidthRoundedGridReturnTailFailureSet
      ρ N y0 Kstar t
  have hslice : ∀ m, MeasurableSet (slice m) := fun m ↦
    (measurableSet_fixedWidthRoundedGridReturnSliceSet
      ρ N y0 Kstar m).inter hF
  have htailInt : Integrable
      (tail.indicator (fun _ : fixedWidthMatrixSampleSpace N ↦
        Real.exp (s * t))) μ :=
    (integrable_const _).indicator htail
  have hsliceInt : ∀ m, Integrable
      ((slice m).indicator (fun _ : fixedWidthMatrixSampleSpace N ↦
        Real.exp (s * m))) μ := fun m ↦
    (integrable_const _).indicator (hslice m)
  have hsumInt : Integrable (fun ω ↦
      ∑ m ∈ I, (slice m).indicator
        (fun _ ↦ Real.exp (s * m)) ω) μ :=
    integrable_finsetSum I fun m _ ↦ hsliceInt m
  have hwInt : Integrable w μ := htailInt.add hsumInt
  have hpoint : w ≤ᵐ[μ] rhs := by
    filter_upwards [hfinite] with ω hωfinite
    by_cases hωF : ω ∈ F
    · let k := (τ ω).untopA
      have hτeq : τ ω = (k : WithTop ℕ) := by
        cases hval : τ ω with
        | top => exact (hωfinite hval).elim
        | coe j =>
            dsimp only [k]
            rw [hval]
            rfl
      have hkone : 1 ≤ k := by
        have hone := one_le_fixedWidthRoundedGridReturnTimeFrom
          ρ N y0 Kstar ω
        change (1 : WithTop ℕ) ≤ τ ω at hone
        rw [hτeq] at hone
        exact_mod_cast hone
      by_cases hkt : k ≤ t
      · have hkI : k ∈ I := by
          dsimp only [I]
          exact Finset.mem_Icc.mpr ⟨hkone, hkt⟩
        have hnotTail : ω ∉ tail := by
          rintro ⟨hgt, _⟩
          change (t : WithTop ℕ) < τ ω at hgt
          rw [hτeq] at hgt
          exact (not_lt_of_ge hkt) (by exact_mod_cast hgt)
        have hsliceK : ω ∈ slice k := by
          exact ⟨hτeq, hωF⟩
        have hsum : (∑ m ∈ I,
            (slice m).indicator (fun _ ↦ Real.exp (s * m)) ω) =
              Real.exp (s * k) := by
          calc
            (∑ m ∈ I,
                (slice m).indicator (fun _ ↦ Real.exp (s * m)) ω) =
                (slice k).indicator (fun _ ↦ Real.exp (s * k)) ω := by
              apply Finset.sum_eq_single k
              · intro m hmI hmk
                rw [Set.indicator_of_notMem]
                rintro ⟨hmeq, _⟩
                exact hmk (WithTop.coe_eq_coe.mp (hmeq.symm.trans hτeq))
              · exact fun hknot ↦ (hknot hkI).elim
            _ = Real.exp (s * k) := by
              rw [Set.indicator_of_mem hsliceK]
        dsimp only [w, rhs]
        rw [Set.indicator_of_notMem hnotTail, zero_add, hsum,
          Set.indicator_of_mem hωF]
      · have htk : t < k := lt_of_not_ge hkt
        have htailmem : ω ∈ tail := by
          refine ⟨?_, hωF⟩
          change (t : WithTop ℕ) < τ ω
          rw [hτeq]
          exact_mod_cast htk
        have hsumzero : (∑ m ∈ I,
            (slice m).indicator (fun _ ↦ Real.exp (s * m)) ω) = 0 := by
          apply Finset.sum_eq_zero
          intro m hmI
          rw [Set.indicator_of_notMem]
          rintro ⟨hmeq, _⟩
          have hmle : m ≤ t := (Finset.mem_Icc.mp hmI).2
          have hmk : m = k :=
            WithTop.coe_eq_coe.mp (hmeq.symm.trans hτeq)
          omega
        dsimp only [w, rhs]
        rw [Set.indicator_of_mem htailmem, hsumzero, add_zero,
          Set.indicator_of_mem hωF]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast htk.le) hs
    · have hnotTail : ω ∉ tail := fun h ↦ hωF h.2
      have hsumzero : (∑ m ∈ I,
          (slice m).indicator (fun _ ↦ Real.exp (s * m)) ω) = 0 := by
        apply Finset.sum_eq_zero
        intro m _
        rw [Set.indicator_of_notMem]
        exact fun h ↦ hωF h.2
      dsimp only [w, rhs]
      rw [Set.indicator_of_notMem hnotTail, hsumzero, add_zero,
        Set.indicator_of_notMem hωF]
  have hwIntegral : (∫ ω, w ω ∂μ) =
      Real.exp (s * t) * μ.real tail +
        ∑ m ∈ I, Real.exp (s * m) * μ.real (slice m) := by
    dsimp only [w]
    rw [integral_add htailInt hsumInt,
      integral_finsetSum I (fun m _ ↦ hsliceInt m)]
    rw [integral_indicator_const (Real.exp (s * t)) htail]
    congr 1
    · simp [mul_comm]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [integral_indicator_const (Real.exp (s * m)) (hslice m)]
      simp [mul_comm]
  rw [← hwIntegral]
  exact integral_mono_ae hwInt hInt hpoint

/-- A uniform strict failed-return contraction implies an exponential
absorption-survival bound from every start in the bounded grid-radius region. -/
lemma measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_le_exp_neg_mul_of_contraction
    {A ρ s q : ℝ} {N : ℕ} {Kstar : ℝ}
    (hs : 0 < s) (hq : q < 1)
    (hcontract : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ Kstar →
        (∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
          fixedWidthRoundedGridReturnTimeFrom ρ N x Kstar ω ≠ ⊤) ∧
        Integrable
          ((fixedWidthRoundedOneStepFailureSet ρ N x).indicator
            (fun ω ↦ Real.exp
              (s * (((fixedWidthRoundedGridReturnTimeFrom
                ρ N x Kstar ω).untopA : ℕ) : ℝ))))
          (fixedWidthMatrixGaussianMeasure A N) ∧
        (∫ ω, (fixedWidthRoundedOneStepFailureSet ρ N x).indicator
            (fun ω ↦ Real.exp
              (s * (((fixedWidthRoundedGridReturnTimeFrom
                ρ N x Kstar ω).untopA : ℕ) : ℝ))) ω
            ∂fixedWidthMatrixGaussianMeasure A N) ≤ q) :
    ∀ t : ℕ, ∀ y0 : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar →
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
          Real.exp (-s * t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro y0 hstart
      by_cases htzero : t = 0
      · subst t
        calc
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 0) ≤ 1 :=
            measureReal_le_one
          _ = Real.exp (-s * (0 : ℕ)) := by norm_num
      · have ht : 1 ≤ t := by omega
        let μ := fixedWidthMatrixGaussianMeasure A N
        let tail := fixedWidthRoundedGridReturnTailFailureSet
          ρ N y0 Kstar t
        let slice := fun m ↦
          fixedWidthRoundedGridReturnSliceSet ρ N y0 Kstar m ∩
            fixedWidthRoundedOneStepFailureSet ρ N y0
        have hslice (m : ℕ) (hm : m ∈ Finset.Icc 1 t) :
            μ.real (slice m ∩
                fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
              Real.exp (-s * (t - m)) * μ.real (slice m) := by
          have hmBounds := Finset.mem_Icc.mp hm
          have hrem : t - m < t := Nat.sub_lt (by omega) hmBounds.1
          have hremaining : ∀ x : Fin N → ℝ,
              fixedWidthRoundedInitialGridRadius ρ N x ≤ Kstar →
                μ.real
                    (fixedWidthRoundedAbsorptionSurvivalSetFrom
                      ρ N x (t - m)) ≤
                  Real.exp (-s * (t - m)) :=
            fun x hx ↦ by
              simpa only [Nat.cast_sub hmBounds.2] using
                ih (t - m) hrem x hx
          have hrestart :=
            measureReal_failedReturnSlice_inter_survival_le_mul
              (A := A) (ρ := ρ) (N := N) y0
              (Kstar := Kstar) (a := Real.exp (-s * (t - m)))
              hmBounds.1 (t - m) (Real.exp_pos _).le hremaining
          simpa only [slice, Nat.add_sub_of_le hmBounds.2] using hrestart
        have hunion :=
          measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_le_returnTail_add_sum
            A ρ N y0 Kstar ht
        have hrenewal : μ.real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
            μ.real tail +
              ∑ m ∈ Finset.Icc 1 t,
                Real.exp (-s * (t - m)) * μ.real (slice m) := by
          apply hunion.trans
          exact add_le_add le_rfl
            (Finset.sum_le_sum fun m hm ↦ hslice m hm)
        obtain ⟨hfinite, hInt, hIntBound⟩ := hcontract y0 hstart
        have hweighted :=
          (exp_mul_measureReal_returnTail_add_sum_le_integral_failedReturn
            (A := A) (ρ := ρ) (s := s) (N := N) y0 Kstar t
            hs.le hfinite hInt).trans hIntBound
        have hinv : Real.exp (-s * t) * Real.exp (s * t) = 1 := by
          rw [← Real.exp_add]
          have hz : -s * (t : ℝ) + s * t = 0 := by ring
          rw [hz, Real.exp_zero]
        have hfactor (m : ℕ) :
            Real.exp (-s * (t - m)) =
              Real.exp (-s * t) * Real.exp (s * m) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          μ.real (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
              μ.real tail +
                ∑ m ∈ Finset.Icc 1 t,
                  Real.exp (-s * (t - m)) * μ.real (slice m) := hrenewal
          _ = Real.exp (-s * t) *
                (Real.exp (s * t) * μ.real tail +
                  ∑ m ∈ Finset.Icc 1 t,
                    Real.exp (s * m) * μ.real (slice m)) := by
            rw [mul_add, Finset.mul_sum]
            simp_rw [← mul_assoc]
            rw [hinv, one_mul]
            congr 1
            apply Finset.sum_congr rfl
            intro m hm
            rw [hfactor m]
          _ ≤ Real.exp (-s * t) * q :=
            mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
          _ ≤ Real.exp (-s * t) := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hq.le (Real.exp_pos _).le

/-- The common entrance constants can be retained while iterating the strict
failed-cycle contraction into bounded-start exponential survival. -/
theorem exists_uniform_fixedWidthRoundedGridEntrance_and_boundedAbsorptionSurvival_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar c1 c2 c3 s : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < s ∧
      (∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ, ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            ⌊c1 * Real.log
              (max 2 (fixedWidthRoundedInitialGridRadius ρ N y0)) + r⌋₊) ≤
          c2 * Real.exp (-c3 * r)) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ,
        fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar →
          ∀ t : ℕ,
            (fixedWidthMatrixGaussianMeasure A N).real
                (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
              Real.exp (-s * t) := by
  obtain ⟨Kstar, c1, c2, c3, s, q, hKstar, hc1, hc2, hc3, hs, _hq, hqone,
      hentrance, hcontract⟩ :=
    exists_uniform_fixedWidthRoundedGridEntrance_and_failedReturn_contraction
      hA hN hsub
  refine ⟨Kstar, c1, c2, c3, s, hKstar, hc1, hc2, hc3, hs, hentrance, ?_⟩
  intro ρ hρ
  have hcontract' : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ Kstar →
        (∀ᵐ ω ∂fixedWidthMatrixGaussianMeasure A N,
          fixedWidthRoundedGridReturnTimeFrom ρ N x Kstar ω ≠ ⊤) ∧
        Integrable
          ((fixedWidthRoundedOneStepFailureSet ρ N x).indicator
            (fun ω ↦ Real.exp
              (s * (((fixedWidthRoundedGridReturnTimeFrom
                ρ N x Kstar ω).untopA : ℕ) : ℝ))))
          (fixedWidthMatrixGaussianMeasure A N) ∧
        (∫ ω, (fixedWidthRoundedOneStepFailureSet ρ N x).indicator
            (fun ω ↦ Real.exp
              (s * (((fixedWidthRoundedGridReturnTimeFrom
                ρ N x Kstar ω).untopA : ℕ) : ℝ))) ω
            ∂fixedWidthMatrixGaussianMeasure A N) ≤ q := by
    intro x hx
    obtain ⟨hfinite, _hfull, hfailed, hbound⟩ := hcontract ρ hρ x hx
    exact ⟨hfinite, hfailed, hbound⟩
  intro y0 hstart t
  exact measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_le_exp_neg_mul_of_contraction
    hs hqone hcontract' t y0 hstart

/-- Uniform exponential absorption-survival bound from every bounded-region
start, with constants chosen before the mesh and starting vector. -/
theorem exists_uniform_fixedWidthRoundedBoundedAbsorptionSurvival_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar s : ℝ, 0 < Kstar ∧ 0 < s ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ,
        fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar →
          ∀ t : ℕ,
            (fixedWidthMatrixGaussianMeasure A N).real
                (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
              Real.exp (-s * t) := by
  obtain ⟨Kstar, _c1, _c2, _c3, s, hKstar, _hc1, _hc2, _hc3, hs,
      _hentrance, hsurvival⟩ :=
    exists_uniform_fixedWidthRoundedGridEntrance_and_boundedAbsorptionSurvival_bound
      hA hN hsub
  exact ⟨Kstar, s, hKstar, hs, hsurvival⟩

/-- Exact characterization of a finite bounded-region entrance slice. -/
lemma fixedWidthRoundedGridEntranceTimeFrom_eq_iff
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) (m : ℕ) :
    fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω = m ↔
      fixedWidthRoundedGridRadiusFrom ρ N y0 m ω ≤ Kstar ∧
        ∀ j, j < m →
          Kstar < fixedWidthRoundedGridRadiusFrom ρ N y0 j ω := by
  constructor
  · intro heq
    have hne : fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar ω ≠ ⊤ := by simp [heq]
    have hmem := MeasureTheory.hittingAfter_mem_set_of_ne_top
      (u := fixedWidthRoundedGridRadiusFrom ρ N y0)
      (s := Set.Iic Kstar) (n := 0) hne
    have hvalue :
        (fixedWidthRoundedGridEntranceTimeFrom
          ρ N y0 Kstar ω).untopA = m := by
      rw [heq]
      rfl
    change fixedWidthRoundedGridRadiusFrom ρ N y0
      (fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar ω).untopA ω ≤ Kstar at hmem
    rw [hvalue] at hmem
    refine ⟨hmem, ?_⟩
    intro j hjm
    have hjlt : (j : WithTop ℕ) <
        fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω := by
      rw [heq]
      exact_mod_cast hjm
    have hnotmem := MeasureTheory.notMem_of_lt_hittingAfter hjlt (Nat.zero_le j)
    change ¬fixedWidthRoundedGridRadiusFrom ρ N y0 j ω ≤ Kstar at hnotmem
    exact lt_of_not_ge hnotmem
  · rintro ⟨hmhit, hbefore⟩
    have hle : fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar ω ≤ m :=
      MeasureTheory.hittingAfter_le_of_mem (Nat.zero_le m) hmhit
    have hge : (m : WithTop ℕ) ≤
        fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω := by
      rw [← not_lt]
      intro hlt
      obtain ⟨j, hj, hjmem⟩ :=
        (MeasureTheory.hittingAfter_lt_iff
          (u := fixedWidthRoundedGridRadiusFrom ρ N y0)
          (s := Set.Iic Kstar) (n := 0) (i := m) (ω := ω)).mp hlt
      exact (not_lt_of_ge hjmem) (hbefore j hj.2)
    exact le_antisymm hle hge

/-- Exact finite entrance slice represented on the strict matrix prefix. -/
def fixedWidthRoundedGridEntranceSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    Set (Fin m → (Fin N → Fin N → ℝ)) :=
  {u | fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar
      (fixedWidthExtendMatrixPrefix N m u) = m}

lemma measurableSet_fixedWidthRoundedGridEntranceSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    MeasurableSet
      (fixedWidthRoundedGridEntranceSlicePrefixSet ρ N y0 Kstar m) := by
  exact (measurableSet_singleton (m : WithTop ℕ)).preimage
    (((isStoppingTime_fixedWidthRoundedGridEntranceTimeFrom
      ρ N y0 Kstar).measurable').comp
        (measurable_fixedWidthExtendMatrixPrefix N m))

lemma preimage_fixedWidthRoundedGridEntranceSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m : ℕ) :
    fixedWidthMatrixPrefix N m ⁻¹'
        fixedWidthRoundedGridEntranceSlicePrefixSet ρ N y0 Kstar m =
      {ω | fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar ω = m} := by
  ext ω
  let ω' := fixedWidthExtendMatrixPrefix N m
    (fixedWidthMatrixPrefix N m ω)
  have hpath : ∀ j ≤ m,
      fixedWidthRoundedGridRadiusFrom ρ N y0 j ω =
        fixedWidthRoundedGridRadiusFrom ρ N y0 j ω' := by
    intro j hj
    unfold fixedWidthRoundedGridRadiusFrom fixedWidthRoundedVectorRadiusFrom
    apply congrArg (fun x : Fin N → ℝ ↦ gaussianEuclideanNorm N x / ρ)
    apply fixedWidthRoundedVectorPathFrom_eq_of_forall_lt ρ N y0 j
    intro k hk
    dsimp only [ω']
    simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix,
      lt_of_lt_of_le hk hj]
  change (fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω' = m) ↔
    fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω = m
  rw [fixedWidthRoundedGridEntranceTimeFrom_eq_iff,
    fixedWidthRoundedGridEntranceTimeFrom_eq_iff]
  constructor
  · rintro ⟨hnow, hbefore⟩
    refine ⟨hpath m le_rfl ▸ hnow, ?_⟩
    intro j hjm
    rw [hpath j hjm.le]
    exact hbefore j hjm
  · rintro ⟨hnow, hbefore⟩
    refine ⟨hpath m le_rfl ▸ hnow, ?_⟩
    intro j hjm
    rw [← hpath j hjm.le]
    exact hbefore j hjm

/-- Product-space event consisting of an exact entrance slice in the used
prefix and survival for `n` further steps under the fresh shifted driver. -/
def fixedWidthRoundedEntranceSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m n : ℕ) :
    Set ((Fin m → (Fin N → Fin N → ℝ)) ×
      fixedWidthMatrixSampleSpace N) :=
  {p | p.1 ∈ fixedWidthRoundedGridEntranceSlicePrefixSet
      ρ N y0 Kstar m ∧
    fixedWidthRoundedVectorPathFrom ρ N
      (fixedWidthRoundedStateFromPrefix ρ N y0 m p.1) n p.2 ≠ 0}

lemma measurableSet_fixedWidthRoundedEntranceSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (m n : ℕ) :
    MeasurableSet
      (fixedWidthRoundedEntranceSliceFutureSurvivalSet
        ρ N y0 Kstar m n) := by
  apply ((measurableSet_fixedWidthRoundedGridEntranceSlicePrefixSet
    ρ N y0 Kstar m).preimage measurable_fst).inter
  change MeasurableSet
    ((fun p : (Fin m → (Fin N → Fin N → ℝ)) ×
        fixedWidthMatrixSampleSpace N ↦
      fixedWidthRoundedVectorPathFrom ρ N
        (fixedWidthRoundedStateFromPrefix ρ N y0 m p.1) n p.2) ⁻¹'
          ({0} : Set (Fin N → ℝ))ᶜ)
  apply (measurableSet_singleton 0).compl.preimage
  exact (measurable_fixedWidthRoundedVectorPathFrom_prod ρ N n).comp
    (((measurable_fixedWidthRoundedStateFromPrefix ρ N y0 m).comp
      measurable_fst).prodMk measurable_snd)

lemma preimage_fixedWidthRoundedEntranceSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    (m n : ℕ) :
    (fun ω : fixedWidthMatrixSampleSpace N ↦
      (fixedWidthMatrixPrefix N m ω, fixedWidthMatrixShift N m ω)) ⁻¹'
        fixedWidthRoundedEntranceSliceFutureSurvivalSet
          ρ N y0 Kstar m n =
      {ω | fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω = m} ∩
        fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (m + n) := by
  ext ω
  change
    (fixedWidthMatrixPrefix N m ω ∈
        fixedWidthRoundedGridEntranceSlicePrefixSet ρ N y0 Kstar m ∧
      fixedWidthRoundedVectorPathFrom ρ N
        (fixedWidthRoundedStateFromPrefix ρ N y0 m
          (fixedWidthMatrixPrefix N m ω)) n
          (fixedWidthMatrixShift N m ω) ≠ 0) ↔
      (fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω = m ∧
        fixedWidthRoundedVectorPathFrom ρ N y0 (m + n) ω ≠ 0)
  rw [fixedWidthRoundedStateFromPrefix_apply,
    ← fixedWidthRoundedVectorPathFrom_add]
  have hprefix := Set.ext_iff.mp
    (preimage_fixedWidthRoundedGridEntranceSlicePrefixSet
      ρ N y0 Kstar m) ω
  exact and_congr hprefix Iff.rfl

/-- A uniform bounded-start survival estimate multiplies each exact entrance
slice after prefix/fresh-future factorization. -/
lemma measureReal_entranceSlice_inter_survival_le_mul
    {A ρ : ℝ} {N : ℕ} (y0 : Fin N → ℝ) {Kstar a : ℝ}
    (m n : ℕ) (ha : 0 ≤ a)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ Kstar →
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x n) ≤ a) :
    (fixedWidthMatrixGaussianMeasure A N).real
        ({ω | fixedWidthRoundedGridEntranceTimeFrom
            ρ N y0 Kstar ω = m} ∩
          fixedWidthRoundedAbsorptionSurvivalSetFrom
            ρ N y0 (m + n)) ≤
      a * (fixedWidthMatrixGaussianMeasure A N).real
        {ω | fixedWidthRoundedGridEntranceTimeFrom
          ρ N y0 Kstar ω = m} := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let pref := fixedWidthMatrixPrefix N m
  let shift := fixedWidthMatrixShift N m
  let ν := Measure.map pref μ
  let S := fixedWidthRoundedGridEntranceSlicePrefixSet ρ N y0 Kstar m
  let E := fixedWidthRoundedEntranceSliceFutureSurvivalSet
    ρ N y0 Kstar m n
  have hpref : Measurable pref := measurable_fixedWidthMatrixPrefix N m
  have hshift : Measurable shift := measurable_fixedWidthMatrixShift N m
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hpref.aemeasurable
  have hS : MeasurableSet S :=
    measurableSet_fixedWidthRoundedGridEntranceSlicePrefixSet
      ρ N y0 Kstar m
  have hE : MeasurableSet E :=
    measurableSet_fixedWidthRoundedEntranceSliceFutureSurvivalSet
      ρ N y0 Kstar m n
  have hsection : ∀ u,
      μ (Prod.mk u ⁻¹' E) ≤ S.indicator (fun _ ↦ ENNReal.ofReal a) u := by
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      change u ∈ fixedWidthRoundedGridEntranceSlicePrefixSet
        ρ N y0 Kstar m at hu
      have hstate : fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedStateFromPrefix ρ N y0 m u) ≤ Kstar := by
        have hhit := (fixedWidthRoundedGridEntranceTimeFrom_eq_iff
          ρ N y0 Kstar (fixedWidthExtendMatrixPrefix N m u) m).1 hu
        change fixedWidthRoundedGridRadiusFrom ρ N y0 m
          (fixedWidthExtendMatrixPrefix N m u) ≤ Kstar
        exact hhit.1
      have hbound := hsurvival
        (fixedWidthRoundedStateFromPrefix ρ N y0 m u) hstate
      have hsecEq : Prod.mk u ⁻¹' E =
          fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N
            (fixedWidthRoundedStateFromPrefix ρ N y0 m u) n := by
        ext v
        change (u ∈ fixedWidthRoundedGridEntranceSlicePrefixSet
          ρ N y0 Kstar m ∧
            fixedWidthRoundedVectorPathFrom ρ N
              (fixedWidthRoundedStateFromPrefix ρ N y0 m u) n v ≠ 0) ↔
          fixedWidthRoundedVectorPathFrom ρ N
            (fixedWidthRoundedStateFromPrefix ρ N y0 m u) n v ≠ 0
        simp only [hu, true_and]
      rw [hsecEq]
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) ha]
      exact hbound
    · rw [Set.indicator_of_notMem hu]
      change u ∉ fixedWidthRoundedGridEntranceSlicePrefixSet
        ρ N y0 Kstar m at hu
      have hsecEmpty : Prod.mk u ⁻¹' E = ∅ := by
        ext v
        change (u ∈ fixedWidthRoundedGridEntranceSlicePrefixSet
          ρ N y0 Kstar m ∧
            fixedWidthRoundedVectorPathFrom ρ N
              (fixedWidthRoundedStateFromPrefix ρ N y0 m u) n v ≠ 0) ↔ False
        simp only [hu, false_and]
      rw [hsecEmpty, measure_empty]
  have hprod : (ν.prod μ) E ≤ ENNReal.ofReal a * ν S := by
    rw [Measure.prod_apply hE]
    calc
      (∫⁻ u, μ (Prod.mk u ⁻¹' E) ∂ν) ≤
          ∫⁻ u, S.indicator (fun _ ↦ ENNReal.ofReal a) u ∂ν :=
        lintegral_mono hsection
      _ = ENNReal.ofReal a * ν S := by
        rw [lintegral_indicator hS]
        simp
  have hprodReal : (ν.prod μ).real E ≤ a * ν.real S := by
    rw [measureReal_def, measureReal_def]
    calc
      ENNReal.toReal ((ν.prod μ) E) ≤
          ENNReal.toReal (ENNReal.ofReal a * ν S) :=
        ENNReal.toReal_mono (by finiteness) hprod
      _ = a * ENNReal.toReal (ν S) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
  have hcoeff : ν.real S = μ.real
      {ω | fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar ω = m} := by
    dsimp only [ν, pref, S]
    rw [map_measureReal_apply
      (measurable_fixedWidthMatrixPrefix N m)
      (measurableSet_fixedWidthRoundedGridEntranceSlicePrefixSet
        ρ N y0 Kstar m)]
    rw [preimage_fixedWidthRoundedGridEntranceSlicePrefixSet]
  let restart := fun ω : fixedWidthMatrixSampleSpace N ↦
    (pref ω, shift ω)
  have hrestart : Measurable restart := hpref.prodMk hshift
  calc
    μ.real
        ({ω | fixedWidthRoundedGridEntranceTimeFrom
            ρ N y0 Kstar ω = m} ∩
          fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (m + n)) =
        (Measure.map restart μ).real E := by
      rw [map_measureReal_apply hrestart hE]
      exact congrArg μ.real
        (preimage_fixedWidthRoundedEntranceSliceFutureSurvivalSet
          ρ N y0 Kstar m n).symm
    _ = (ν.prod μ).real E := by
      congr 1
      exact map_prod_fixedWidthMatrixPrefix_shift A N m
    _ ≤ a * ν.real S := hprodReal
    _ = a * μ.real
        {ω | fixedWidthRoundedGridEntranceTimeFrom
          ρ N y0 Kstar ω = m} := by
      rw [hcoeff]

/-- Survival at a post-entrance horizon lies either in the late-entrance event
or in one exact finite entrance slice that also survives to that horizon. -/
lemma fixedWidthRoundedAbsorptionSurvivalSetFrom_subset_entranceTail_union_slices
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (H u : ℕ) :
    fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u) ⊆
      fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar H ∪
        ⋃ m ∈ Finset.Icc 0 H,
          {ω | fixedWidthRoundedGridEntranceTimeFrom
              ρ N y0 Kstar ω = m} ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u) := by
  intro ω hsurvival
  by_cases htail : (H : WithTop ℕ) <
      fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω
  · left
    rw [fixedWidthRoundedGridSurvivalSetFrom_eq_lt_entranceTime]
    exact htail
  · right
    have hle : fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar ω ≤ H := le_of_not_gt htail
    have hfinite : fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar ω ≠ ⊤ := fun htop ↦ by simp [htop] at hle
    let m := (fixedWidthRoundedGridEntranceTimeFrom
      ρ N y0 Kstar ω).untopA
    have heq : fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar ω = m := by
      cases hval : fixedWidthRoundedGridEntranceTimeFrom
          ρ N y0 Kstar ω with
      | top => exact (hfinite hval).elim
      | coe k =>
          dsimp only [m]
          rw [hval]
          rfl
    have hmH : m ≤ H := by
      rw [heq] at hle
      exact_mod_cast hle
    apply Set.mem_iUnion.mpr ⟨m, ?_⟩
    apply Set.mem_iUnion.mpr
      ⟨by simpa using Finset.mem_Icc.mpr ⟨Nat.zero_le m, hmH⟩, ?_⟩
    exact ⟨heq, hsurvival⟩

/-- Real-measure union bound for the finite first-entrance decomposition. -/
lemma measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_le_entranceTail_add_sum
    (A ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (H u : ℕ) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u)) ≤
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar H) +
        ∑ m ∈ Finset.Icc 0 H,
          (fixedWidthMatrixGaussianMeasure A N).real
            ({ω | fixedWidthRoundedGridEntranceTimeFrom
                ρ N y0 Kstar ω = m} ∩
              fixedWidthRoundedAbsorptionSurvivalSetFrom
                ρ N y0 (H + u)) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let tail := fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar H
  let slice := fun m : ℕ ↦
    {ω | fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω = m} ∩
      fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u)
  calc
    μ.real (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u)) ≤
        μ.real (tail ∪ ⋃ m ∈ Finset.Icc 0 H, slice m) :=
      measureReal_mono
        (fixedWidthRoundedAbsorptionSurvivalSetFrom_subset_entranceTail_union_slices
          ρ N y0 Kstar H u)
    _ ≤ μ.real tail + μ.real (⋃ m ∈ Finset.Icc 0 H, slice m) :=
      measureReal_union_le tail _
    _ ≤ μ.real tail + ∑ m ∈ Finset.Icc 0 H, μ.real (slice m) := by
      exact add_le_add le_rfl
        (measureReal_biUnion_finset_le (μ := μ) (Finset.Icc 0 H) slice)

/-- The exact entrance-slice contribution after `u` further steps is bounded
by the bounded-start exponential survival profile. -/
lemma sum_measureReal_entranceSlice_inter_survival_le_exp_neg_mul
    {A ρ s : ℝ} {N : ℕ} (y0 : Fin N → ℝ) {Kstar : ℝ}
    (H u : ℕ) (hs : 0 ≤ s)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ Kstar →
        ∀ t : ℕ,
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x t) ≤
            Real.exp (-s * t)) :
    ∑ m ∈ Finset.Icc 0 H,
        (fixedWidthMatrixGaussianMeasure A N).real
          ({ω | fixedWidthRoundedGridEntranceTimeFrom
              ρ N y0 Kstar ω = m} ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom
              ρ N y0 (H + u)) ≤
      Real.exp (-s * u) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let fiber := fun m : ℕ ↦
    {ω | fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω = m}
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hterm : ∀ m ∈ Finset.Icc 0 H,
      μ.real
          (fiber m ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u)) ≤
        Real.exp (-s * u) * μ.real (fiber m) := by
    intro m hm
    have hmH : m ≤ H := (Finset.mem_Icc.mp hm).2
    have hmtotal : m ≤ H + u := hmH.trans (Nat.le_add_right H u)
    have hrestart :=
      measureReal_entranceSlice_inter_survival_le_mul
        (A := A) (ρ := ρ) (N := N) y0
        (Kstar := Kstar)
        (a := Real.exp (-s * ((H + u - m : ℕ) : ℝ)))
        m (H + u - m) (Real.exp_pos _).le
        (fun x hx ↦ hsurvival x hx (H + u - m))
    have htime : u ≤ H + u - m := by omega
    have htimeReal : (u : ℝ) ≤ (H + u - m : ℕ) := by
      exact_mod_cast htime
    have hexp :
        Real.exp (-s * ((H + u - m : ℕ) : ℝ)) ≤ Real.exp (-s * u) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hrestart' :
        μ.real
            (fiber m ∩
              fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u)) ≤
          Real.exp (-s * ((H + u - m : ℕ) : ℝ)) * μ.real (fiber m) := by
      simpa only [μ, fiber, Nat.add_sub_of_le hmtotal] using hrestart
    exact hrestart'.trans
      (mul_le_mul_of_nonneg_right hexp measureReal_nonneg)
  have hmeas : ∀ m ∈ Finset.Icc 0 H, MeasurableSet (fiber m) := by
    intro m _hm
    exact (measurableSet_singleton (m : WithTop ℕ)).preimage
      (isStoppingTime_fixedWidthRoundedGridEntranceTimeFrom
        ρ N y0 Kstar).measurable'
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 0 H)) fiber := by
    intro i _hi j _hj hij
    change Disjoint (fiber i) (fiber j)
    rw [Set.disjoint_left]
    intro ω hiω hjω
    apply hij
    change fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω = i at hiω
    change fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω = j at hjω
    exact_mod_cast hiω.symm.trans hjω
  have hmass : (∑ m ∈ Finset.Icc 0 H, μ.real (fiber m)) ≤ 1 := by
    simpa only [probReal_univ] using
      (sum_measureReal_le_measureReal_univ (μ := μ) hmeas hdisj)
  calc
    ∑ m ∈ Finset.Icc 0 H,
        μ.real
          (fiber m ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u)) ≤
        ∑ m ∈ Finset.Icc 0 H,
          Real.exp (-s * u) * μ.real (fiber m) :=
      Finset.sum_le_sum fun m hm ↦ hterm m hm
    _ = Real.exp (-s * u) *
        ∑ m ∈ Finset.Icc 0 H, μ.real (fiber m) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-s * u) * 1 :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ = Real.exp (-s * u) := mul_one _

/-- After a deterministic entrance horizon `H`, arbitrary-start survival is
bounded by late entrance plus the bounded-start profile for `u` further
steps. -/
lemma measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_le_entranceTail_add_exp
    {A ρ s : ℝ} {N : ℕ} (y0 : Fin N → ℝ) {Kstar : ℝ}
    (H u : ℕ) (hs : 0 ≤ s)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ Kstar →
        ∀ t : ℕ,
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x t) ≤
            Real.exp (-s * t)) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 (H + u)) ≤
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar H) +
        Real.exp (-s * u) := by
  exact
    (measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_le_entranceTail_add_sum
      A ρ N y0 Kstar H u).trans
      (add_le_add le_rfl
        (sum_measureReal_entranceSlice_inter_survival_le_exp_neg_mul
          y0 H u hs hsurvival))

/-- Final finite-grid absorption tail: after the logarithmic entrance horizon,
survival has a uniform exponential tail in the additional time. -/
theorem exists_uniform_fixedWidthRoundedAbsorptionSurvival_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar c1 c2 c3 s : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 0 < s ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ, ∀ r : ℝ, ∀ u : ℕ,
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0
              (⌊c1 * Real.log
                (max 2 (fixedWidthRoundedInitialGridRadius ρ N y0)) + r⌋₊ +
                u)) ≤
          c2 * Real.exp (-c3 * r) + Real.exp (-s * u) := by
  obtain ⟨Kstar, c1, c2, c3, s, hKstar, hc1, hc2, hc3, hs,
      hentrance, hsurvival⟩ :=
    exists_uniform_fixedWidthRoundedGridEntrance_and_boundedAbsorptionSurvival_bound
      hA hN hsub
  refine ⟨Kstar, c1, c2, c3, s, hKstar, hc1, hc2, hc3, hs, ?_⟩
  intro ρ hρ y0 r u
  let H := ⌊c1 * Real.log
    (max 2 (fixedWidthRoundedInitialGridRadius ρ N y0)) + r⌋₊
  have hdecomp :=
    measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_le_entranceTail_add_exp
      y0 H u hs.le (fun x hx t ↦ hsurvival ρ hρ x hx t)
  have htail := hentrance ρ hρ y0 r
  simpa only [H] using hdecomp.trans (add_le_add htail le_rfl)

/-- Paper-facing final finite-grid absorption bound: uniformly over meshes and
starts with grid radius at most `K`, survival beyond `C log K + r` decays
exponentially in `r`. -/
theorem exists_uniform_fixedWidthRoundedAbsorptionSurvival_log_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ K : ℝ, 2 ≤ K → ∀ y0 : Fin N → ℝ,
        fixedWidthRoundedInitialGridRadius ρ N y0 ≤ K →
          ∀ r : ℝ, 0 ≤ r →
            (fixedWidthMatrixGaussianMeasure A N).real
                (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0
                  ⌊C * Real.log K + r⌋₊) ≤
              C * Real.exp (-c * r) := by
  obtain ⟨_Kstar, c1, c2, c3, s, _hKstar, hc1, hc2, hc3, hs, htail⟩ :=
    exists_uniform_fixedWidthRoundedAbsorptionSurvival_bound hA hN hsub
  let c := min c3 s / 2
  let C := max c1 (c2 + Real.exp s)
  have hc : 0 < c := div_pos (lt_min hc3 hs) (by norm_num)
  have hC : 0 < C := by
    dsimp only [C]
    exact lt_of_lt_of_le (add_pos hc2 (Real.exp_pos s))
      (le_max_right _ _)
  refine ⟨c, C, hc, hC, ?_⟩
  intro ρ hρ K hK y0 hstart r hr
  let K0 := fixedWidthRoundedInitialGridRadius ρ N y0
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hmaxpos : 0 < max 2 K0 :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hmaxle : max 2 K0 ≤ K := max_le hK hstart
  have hlogle : Real.log (max 2 K0) ≤ Real.log K :=
    Real.log_le_log hmaxpos hmaxle
  have hlogK : 0 ≤ Real.log K :=
    (Real.log_pos (lt_of_lt_of_le (by norm_num) hK)).le
  let v := c1 * (Real.log K - Real.log (max 2 K0)) + r / 2
  have hrv : r / 2 ≤ v := by
    dsimp only [v]
    nlinarith [hc1.le, hlogle]
  have harg :
      c1 * Real.log (max 2 K0) + v =
        c1 * Real.log K + r / 2 := by
    dsimp only [v]
    ring
  let a := c1 * Real.log K + r / 2
  let b := r / 2
  let tSmall := ⌊a⌋₊ + ⌊b⌋₊
  let tBig := ⌊C * Real.log K + r⌋₊
  have ha : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp only [b]
    positivity
  have htime : tSmall ≤ tBig := by
    dsimp only [tSmall, tBig]
    apply Nat.le_floor
    rw [Nat.cast_add]
    calc
      (⌊a⌋₊ : ℝ) + (⌊b⌋₊ : ℝ) ≤ a + b :=
        add_le_add (Nat.floor_le ha) (Nat.floor_le hb)
      _ = c1 * Real.log K + r := by
        dsimp only [a, b]
        ring
      _ ≤ C * Real.log K + r := by
        have hc1C : c1 ≤ C := by
          dsimp only [C]
          exact le_max_left _ _
        nlinarith
  have hbase := htail ρ hρ y0 v ⌊r / 2⌋₊
  change (fixedWidthMatrixGaussianMeasure A N).real
      (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0
        (⌊c1 * Real.log (max 2 K0) + v⌋₊ + ⌊r / 2⌋₊)) ≤
      c2 * Real.exp (-c3 * v) + Real.exp (-s * ⌊r / 2⌋₊) at hbase
  rw [harg] at hbase
  have hmono :
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 tBig) ≤
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 tSmall) := by
    apply measureReal_mono (h₂ :=
      measure_ne_top (fixedWidthMatrixGaussianMeasure A N) _)
    intro ω hω
    change fixedWidthRoundedVectorPathFrom ρ N y0 tBig ω ≠ 0 at hω
    change fixedWidthRoundedVectorPathFrom ρ N y0 tSmall ω ≠ 0
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le htime
    rw [hd] at hω
    exact fixedWidthRoundedVectorPathFrom_ne_zero_of_add_ne_zero
      ρ N y0 tSmall d ω hω
  have hc_c3 : c ≤ c3 / 2 := by
    dsimp only [c]
    exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hc_s : c ≤ s / 2 := by
    dsimp only [c]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hentryExp : Real.exp (-c3 * v) ≤ Real.exp (-c * r) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hfloorLower : r / 2 - 1 ≤ (⌊r / 2⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one (r / 2)]
  have hfloorExp :
      Real.exp (-s * (⌊r / 2⌋₊ : ℝ)) ≤
        Real.exp s * Real.exp (-c * r) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdecay :
      c2 * Real.exp (-c3 * v) + Real.exp (-s * (⌊r / 2⌋₊ : ℝ)) ≤
        C * Real.exp (-c * r) := by
    calc
      c2 * Real.exp (-c3 * v) + Real.exp (-s * (⌊r / 2⌋₊ : ℝ)) ≤
          c2 * Real.exp (-c * r) + Real.exp s * Real.exp (-c * r) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hentryExp hc2.le) hfloorExp
      _ = (c2 + Real.exp s) * Real.exp (-c * r) := by ring
      _ ≤ C * Real.exp (-c * r) := by
        exact mul_le_mul_of_nonneg_right
          (le_max_right c1 (c2 + Real.exp s)) (Real.exp_pos _).le
  change (fixedWidthMatrixGaussianMeasure A N).real
      (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 tBig) ≤
    C * Real.exp (-c * r)
  exact hmono.trans (hbase.trans hdecay)

/-- Euclidean radius of the unrounded vector path on the common matrix-driver
space used by the synchronous coupling. -/
noncomputable def fixedWidthUnroundedVectorRadius
    (N : ℕ) (x0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → ℝ :=
  fun n ω ↦ gaussianEuclideanNorm N
    (fixedWidthUnroundedVectorPath N x0 n ω)

lemma measurable_fixedWidthUnroundedVectorRadius
    (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthUnroundedVectorRadius N x0 n) :=
  (measurable_gaussianEuclideanNorm N).comp
    (measurable_fixedWidthUnroundedVectorPath N x0 n)

/-- The unrounded vector path is adapted to the canonical matrix-prefix
filtration. -/
lemma measurable_fixedWidthUnroundedVectorPath_piLE
    (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable[Filtration.piLE n]
      (fixedWidthUnroundedVectorPath N x0 n) := by
  induction n with
  | zero =>
      simp only [fixedWidthUnroundedVectorPath]
      exact measurable_const
  | succ n ih =>
      simp only [fixedWidthUnroundedVectorPath]
      have hpath :
          Measurable[Filtration.piLE (n + 1)]
            (fixedWidthUnroundedVectorPath N x0 n) :=
        ih.mono (Filtration.piLE.mono (Nat.le_succ n)) le_rfl
      have hmatrix :
          Measurable[Filtration.piLE (n + 1)]
            (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n) :=
        measurable_fixedWidthMatrixEval_piLE (Nat.le_succ n)
      refine @measurable_pi_lambda
        (fixedWidthMatrixSampleSpace N) (Fin N) (fun _ ↦ ℝ)
        (Filtration.piLE (n + 1)) (fun _ ↦ inferInstance)
        (fun ω ↦ Pstep N
          (fixedWidthUnroundedVectorPath N x0 n ω) (ω n)) ?_
      intro i
      unfold Pstep
      apply continuous_tanh.measurable.comp
      apply Finset.measurable_sum
      intro j _
      exact ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hmatrix)).mul
          ((measurable_pi_apply j).comp hpath)

lemma measurable_fixedWidthUnroundedVectorRadius_piLE
    (N : ℕ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable[Filtration.piLE n]
      (fixedWidthUnroundedVectorRadius N x0 n) :=
  (measurable_gaussianEuclideanNorm N).comp
    (measurable_fixedWidthUnroundedVectorPath_piLE N x0 n)

lemma adapted_fixedWidthUnroundedVectorRadius
    (N : ℕ) (x0 : Fin N → ℝ) :
    Adapted Filtration.piLE (fixedWidthUnroundedVectorRadius N x0) :=
  measurable_fixedWidthUnroundedVectorRadius_piLE N x0

/-- First weak entrance time of the matrix-driven unrounded vector radius into
`(-∞, ε]`. -/
noncomputable def fixedWidthUnroundedVectorEntranceTime
    (N : ℕ) (x0 : Fin N → ℝ) (ε : ℝ) :
    fixedWidthMatrixSampleSpace N → WithTop ℕ :=
  hittingAfter (fixedWidthUnroundedVectorRadius N x0) (Set.Iic ε) 0

/-- The matrix-driven unrounded radius entrance time exceeds `n` exactly when
the radius stays strictly above `ε` through time `n`. -/
lemma lt_fixedWidthUnroundedVectorEntranceTime_iff
    (N : ℕ) (x0 : Fin N → ℝ) (ε : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) (n : ℕ) :
    (n : WithTop ℕ) <
        fixedWidthUnroundedVectorEntranceTime N x0 ε ω ↔
      ∀ j ≤ n, ε < fixedWidthUnroundedVectorRadius N x0 j ω := by
  rw [← not_le]
  change
    (¬hittingAfter (fixedWidthUnroundedVectorRadius N x0)
        (Set.Iic ε) 0 ω ≤ (n : WithTop ℕ)) ↔ _
  have hle :
      hittingAfter (fixedWidthUnroundedVectorRadius N x0)
          (Set.Iic ε) 0 ω ≤ (n : WithTop ℕ) ↔
        ∃ j ≤ n, fixedWidthUnroundedVectorRadius N x0 j ω ≤ ε := by
    simpa [Set.mem_Icc] using
      (MeasureTheory.hittingAfter_le_iff
        (u := fixedWidthUnroundedVectorRadius N x0)
        (s := Set.Iic ε) (n := 0) (i := n) (ω := ω))
  rw [hle]
  simp only [not_exists]
  constructor
  · intro h j hj
    exact lt_of_not_ge fun hle' ↦ h j ⟨hj, hle'⟩
  · intro h j hj
    exact (not_lt_of_ge hj.2) (h j hj.1)

lemma isStoppingTime_fixedWidthUnroundedVectorEntranceTime
    (N : ℕ) (x0 : Fin N → ℝ) (ε : ℝ) :
    IsStoppingTime Filtration.piLE
      (fixedWidthUnroundedVectorEntranceTime N x0 ε) := by
  unfold fixedWidthUnroundedVectorEntranceTime
  exact (adapted_fixedWidthUnroundedVectorRadius N x0)
    |>.isStoppingTime_hittingAfter measurableSet_Iic

/-- The synchronously rounded path is the exact-start rounded path initialized
at the rounded deterministic state. -/
lemma fixedWidthRoundedVectorPath_eq_from
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ)
    (n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedVectorPath ρ N x0 n ω =
      fixedWidthRoundedVectorPathFrom ρ N (Qρ ρ x0) n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [fixedWidthRoundedVectorPath,
        fixedWidthRoundedVectorPathFrom]
      rw [ih]

/-- Off the finite-horizon synchronous-error bad event, failure of the
unrounded path to enter the coupling-radius ball by time `t` forces the rounded
path to survive through `t`. -/
lemma fixedWidthUnroundedNonentrance_diff_couplingErrorBadSet_subset_roundedSurvival
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ)
    (T t : ℕ) (R : ℝ) (ht : t ≤ T) :
    {ω | (t : WithTop ℕ) <
        fixedWidthUnroundedVectorEntranceTime N x0 R ω} \
        fixedWidthCouplingErrorBadSet ρ N x0 T R ⊆
      fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N (Qρ ρ x0) t := by
  intro ω hω
  rcases hω with ⟨hentrance, hgood⟩
  change fixedWidthRoundedVectorPathFrom ρ N (Qρ ρ x0) t ω ≠ 0
  rw [← fixedWidthRoundedVectorPath_eq_from]
  intro hrounded
  have herror : fixedWidthVectorError ρ N x0 t ω ≤ R := by
    apply le_of_not_gt
    intro herr
    apply hgood
    rw [fixedWidthCouplingErrorBadSet]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨t, Finset.mem_range.mpr (Nat.lt_succ_of_le ht), herr⟩
  have hradius : R < fixedWidthUnroundedVectorRadius N x0 t ω :=
    (lt_fixedWidthUnroundedVectorEntranceTime_iff N x0 R ω t).mp
      hentrance t le_rfl
  have heq : fixedWidthVectorError ρ N x0 t ω =
      fixedWidthUnroundedVectorRadius N x0 t ω := by
    simp [fixedWidthVectorError, fixedWidthVectorDiscrepancy,
      fixedWidthUnroundedVectorRadius, hrounded,
      gaussianEuclideanNorm_eq_norm]
  exact (not_lt_of_ge (heq ▸ herror)) hradius

/-- Real-measure lower sandwich: unrounded nonentrance is bounded by rounded
survival plus the finite-horizon synchronous-error probability. -/
lemma measureReal_fixedWidthUnroundedNonentrance_le_roundedSurvival_add_couplingErrorBadSet
    (A ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ)
    (T t : ℕ) (R : ℝ) (ht : t ≤ T) :
    (fixedWidthMatrixGaussianMeasure A N).real
        {ω | (t : WithTop ℕ) <
          fixedWidthUnroundedVectorEntranceTime N x0 R ω} ≤
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedAbsorptionSurvivalSetFrom
            ρ N (Qρ ρ x0) t) +
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet ρ N x0 T R) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let entrance :=
    {ω | (t : WithTop ℕ) <
      fixedWidthUnroundedVectorEntranceTime N x0 R ω}
  let survival :=
    fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N (Qρ ρ x0) t
  let bad := fixedWidthCouplingErrorBadSet ρ N x0 T R
  calc
    μ.real entrance ≤ μ.real (survival ∪ bad) := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      by_cases hbad : ω ∈ bad
      · exact Or.inr hbad
      · exact Or.inl
          (fixedWidthUnroundedNonentrance_diff_couplingErrorBadSet_subset_roundedSurvival
            ρ N x0 T t R ht ⟨hω, hbad⟩)
    _ ≤ μ.real survival + μ.real bad :=
      measureReal_union_le survival bad

/-- Totalized unit direction of the matrix-driven unrounded path, using the
fixed reference direction at the origin. -/
noncomputable def fixedWidthUnroundedVectorDirection
    {N : ℕ} (hN : 0 < N) (x0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → (Fin N → ℝ) :=
  fun n ω ↦ fixedWidthUnitDirection hN
    (fixedWidthUnroundedVectorPath N x0 n ω)

lemma measurable_fixedWidthUnroundedVectorDirection
    {N : ℕ} (hN : 0 < N) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthUnroundedVectorDirection hN x0 n) :=
  (measurable_fixedWidthUnitDirection hN).comp
    (measurable_fixedWidthUnroundedVectorPath N x0 n)

/-- Standardized fresh Gaussian vector obtained by applying the current
matrix innovation to the strict-past unrounded direction. -/
noncomputable def fixedWidthUnroundedVectorInnovation
    {N : ℕ} (hN : 0 < N) (A : ℝ) (x0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → (Fin N → ℝ) :=
  fun n ω ↦ (Real.sqrt N / A) •
    Matrix.mulVec (ω n) (fixedWidthUnroundedVectorDirection hN x0 n ω)

lemma measurable_fixedWidthUnroundedVectorInnovation
    {N : ℕ} (hN : 0 < N) (A : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthUnroundedVectorInnovation hN A x0 n) := by
  unfold fixedWidthUnroundedVectorInnovation
  apply measurable_pi_iff.mpr
  intro i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp (measurable_pi_apply n))).mul
      ((measurable_pi_apply j).comp
        (measurable_fixedWidthUnroundedVectorDirection hN x0 n))

lemma measurable_fixedWidthUnroundedVectorInnovationSequence
    {N : ℕ} (hN : 0 < N) (A : ℝ) (x0 : Fin N → ℝ) :
    Measurable (fun ω n ↦
      fixedWidthUnroundedVectorInnovation hN A x0 n ω) :=
  measurable_pi_lambda _ fun n ↦
    measurable_fixedWidthUnroundedVectorInnovation hN A x0 n

/-- The matrix-driven unrounded radius obeys the canonical scalar radius
recursion when driven by the standardized adapted innovations. -/
lemma fixedWidthUnroundedVectorRadius_succ_eq
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthUnroundedVectorRadius N x0 (n + 1) ω =
      gaussianEuclideanNorm N
        (tanhVec N
          (((A / Real.sqrt N) *
              fixedWidthUnroundedVectorRadius N x0 n ω) •
            fixedWidthUnroundedVectorInnovation hN A x0 n ω)) := by
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  have hA0 : A ≠ 0 := hA.ne'
  have hinput :
      ((A / Real.sqrt N) *
          fixedWidthUnroundedVectorRadius N x0 n ω) •
        fixedWidthUnroundedVectorInnovation hN A x0 n ω =
      Matrix.mulVec (ω n) (fixedWidthUnroundedVectorPath N x0 n ω) := by
    unfold fixedWidthUnroundedVectorInnovation
    rw [smul_smul]
    have hcoeff :
        ((A / Real.sqrt N) *
            fixedWidthUnroundedVectorRadius N x0 n ω) *
          (Real.sqrt N / A) =
        fixedWidthUnroundedVectorRadius N x0 n ω := by
      field_simp
    rw [hcoeff, ← Matrix.mulVec_smul]
    exact congrArg (Matrix.mulVec (ω n))
      (gaussianEuclideanNorm_smul_fixedWidthUnitDirection hN
        (fixedWidthUnroundedVectorPath N x0 n ω))
  rw [hinput]
  rfl

/-- Pathwise identification of the common-matrix unrounded radius with the
canonical scalar-innovation radius path. -/
lemma fixedWidthUnroundedVectorRadius_eq_fixedWidthRadiusPath
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthUnroundedVectorRadius N x0 n ω =
      fixedWidthRadiusPath A N (gaussianEuclideanNorm N x0) n
        (fun k ↦ fixedWidthUnroundedVectorInnovation hN A x0 k ω) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [fixedWidthUnroundedVectorRadius_succ_eq hA hN]
      simp only [fixedWidthRadiusPath]
      rw [ih]

/-- Applying a fixed-width Gaussian matrix to a deterministic unit direction
and undoing the `A / sqrt N` scale produces a standard Gaussian vector. -/
lemma map_standardized_mulVec_gaussianMat_of_unit
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (θ : Fin N → ℝ) (hθ : gaussianEuclideanNorm N θ = 1) :
    Measure.map
        (fun W : Fin N → Fin N → ℝ ↦
          (Real.sqrt N / A) • Matrix.mulVec W θ)
        (gaussianMat A N) =
      gaussianVec N := by
  have hsum : ∑ j, (θ j) ^ 2 = 1 := by
    have hsqrt : Real.sqrt (∑ j, (θ j) ^ 2) = 1 := by
      simpa [gaussianEuclideanNorm, gaussianSquaredNorm] using hθ
    have hnonneg : 0 ≤ ∑ j, (θ j) ^ 2 := by positivity
    nlinarith [Real.sq_sqrt hnonneg]
  have hradius : A ^ 2 * radiusSq N θ = A ^ 2 / N := by
    unfold radiusSq
    rw [hsum]
    simp [div_eq_mul_inv]
  have hrow : Measurable
      (fun W : Fin N → Fin N → ℝ ↦
        fun i ↦ ∑ j, W i j * θ j) := by
    fun_prop
  have hscale : Measurable
      (fun v : Fin N → ℝ ↦ fun i ↦ (Real.sqrt N / A) * v i) := by
    fun_prop
  change Measure.map
      ((fun v : Fin N → ℝ ↦ fun i ↦ (Real.sqrt N / A) * v i) ∘
        (fun W : Fin N → Fin N → ℝ ↦ fun i ↦ ∑ j, W i j * θ j))
      (gaussianMat A N) = gaussianVec N
  rw [← Measure.map_map hscale hrow, map_rowMap_gaussianMat, hradius]
  unfold gaussianVec
  rw [Measure.pi_map_pi (fun _ ↦ (by fun_prop :
    AEMeasurable (fun g : ℝ ↦ (Real.sqrt N / A) * g)
      (gaussianReal 0 ((A ^ 2 / N).toNNReal))))]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal]
  · field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    simp
  · positivity

/-- The time-`n` unrounded direction as an explicit measurable function of
the matrix innovations strictly before time `n`. -/
noncomputable def fixedWidthUnroundedVectorDirectionFromPrefix
    {N : ℕ} (hN : 0 < N) (x0 : Fin N → ℝ) (n : ℕ) :
    (Fin n → (Fin N → Fin N → ℝ)) → (Fin N → ℝ) :=
  fun u ↦ fixedWidthUnroundedVectorDirection hN x0 n
    (fixedWidthExtendMatrixPrefix N n u)

lemma measurable_fixedWidthUnroundedVectorDirectionFromPrefix
    {N : ℕ} (hN : 0 < N) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable
      (fixedWidthUnroundedVectorDirectionFromPrefix hN x0 n) :=
  (measurable_fixedWidthUnroundedVectorDirection hN x0 n).comp
    (measurable_fixedWidthExtendMatrixPrefix N n)

lemma fixedWidthUnroundedVectorDirectionFromPrefix_apply
    {N : ℕ} (hN : 0 < N) (x0 : Fin N → ℝ) (n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthUnroundedVectorDirectionFromPrefix hN x0 n
        (fixedWidthMatrixPrefix N n ω) =
      fixedWidthUnroundedVectorDirection hN x0 n ω := by
  unfold fixedWidthUnroundedVectorDirectionFromPrefix
    fixedWidthUnroundedVectorDirection
  congr 1
  apply fixedWidthUnroundedVectorPath_eq_of_forall_lt
  intro k hk
  simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix, hk]

/-- The strict-past unrounded direction is independent of the fresh matrix
innovation at the current time. -/
lemma indepFun_fixedWidthUnroundedVectorDirection_eval
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (n : ℕ) :
    IndepFun
      (fixedWidthUnroundedVectorDirection hN x0 n)
      (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hcomp := (indepFun_fixedWidthMatrixPrefix_eval A N n).comp
    (measurable_fixedWidthUnroundedVectorDirectionFromPrefix hN x0 n)
    measurable_id
  convert hcomp using 1
  · funext ω
    exact
      (fixedWidthUnroundedVectorDirectionFromPrefix_apply hN x0 n ω).symm
  · rfl

/-- Mixing the standardized Gaussian matrix fibre over any probability law
supported on unit directions still gives the standard product Gaussian law. -/
lemma map_standardized_mulVec_prod_eq_gaussianVec
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ν : Measure (Fin N → ℝ)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ θ ∂ν, gaussianEuclideanNorm N θ = 1) :
    Measure.map
        (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) ↦
          (Real.sqrt N / A) • Matrix.mulVec p.2 p.1)
        (ν.prod (gaussianMat A N)) =
      gaussianVec N := by
  let standardizedMul :
      (Fin N → ℝ) × (Fin N → Fin N → ℝ) → (Fin N → ℝ) :=
    fun p ↦ (Real.sqrt N / A) • Matrix.mulVec p.2 p.1
  have hstandardizedMul : Measurable standardizedMul := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [standardizedMul, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp measurable_fst)
  change Measure.map standardizedMul (ν.prod (gaussianMat A N)) =
    gaussianVec N
  ext s hs
  rw [Measure.map_apply hstandardizedMul hs,
    Measure.prod_apply (hs.preimage hstandardizedMul)]
  have hsections : ∀ᵐ θ ∂ν,
      gaussianMat A N (Prod.mk θ ⁻¹' (standardizedMul ⁻¹' s)) =
        gaussianVec N s := by
    filter_upwards [hν] with θ hθ
    have hfix : Measurable
        (fun W : Fin N → Fin N → ℝ ↦
          (Real.sqrt N / A) • Matrix.mulVec W θ) := by
      apply measurable_pi_iff.mpr
      intro i
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro j _
      fun_prop
    rw [show Prod.mk θ ⁻¹' (standardizedMul ⁻¹' s) =
        (fun W : Fin N → Fin N → ℝ ↦
          (Real.sqrt N / A) • Matrix.mulVec W θ) ⁻¹' s by rfl]
    rw [← Measure.map_apply hfix hs,
      map_standardized_mulVec_gaussianMat_of_unit hA hN θ hθ]
  calc
    ∫⁻ θ, gaussianMat A N
        (Prod.mk θ ⁻¹' (standardizedMul ⁻¹' s)) ∂ν =
        ∫⁻ _θ, gaussianVec N s ∂ν :=
      lintegral_congr_ae hsections
    _ = gaussianVec N s := by simp

/-- Every standardized adapted innovation extracted from the matrix-driven
unrounded path has the common standard Gaussian vector marginal law. -/
lemma map_fixedWidthUnroundedVectorInnovation
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (n : ℕ) :
    Measure.map (fixedWidthUnroundedVectorInnovation hN A x0 n)
        (fixedWidthMatrixGaussianMeasure A N) =
      gaussianVec N := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let direction := fixedWidthUnroundedVectorDirection hN x0 n
  let current : fixedWidthMatrixSampleSpace N → (Fin N → Fin N → ℝ) :=
    fun ω ↦ ω n
  let ν := Measure.map direction μ
  let standardizedMul :
      (Fin N → ℝ) × (Fin N → Fin N → ℝ) → (Fin N → ℝ) :=
    fun p ↦ (Real.sqrt N / A) • Matrix.mulVec p.2 p.1
  have hdirection : Measurable direction :=
    measurable_fixedWidthUnroundedVectorDirection hN x0 n
  have hcurrent : Measurable current := measurable_pi_apply n
  have hstandardizedMul : Measurable standardizedMul := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [standardizedMul, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp measurable_fst)
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hdirection.aemeasurable
  have hν : ∀ᵐ θ ∂ν, gaussianEuclideanNorm N θ = 1 := by
    change ∀ᵐ θ ∂Measure.map direction μ,
      gaussianEuclideanNorm N θ = 1
    exact (ae_map_iff hdirection.aemeasurable
      ((measurableSet_singleton 1).preimage
        (measurable_gaussianEuclideanNorm N))).2
      (Eventually.of_forall fun ω ↦
        gaussianEuclideanNorm_fixedWidthUnitDirection hN
          (fixedWidthUnroundedVectorPath N x0 n ω))
  have hcurrentMap : Measure.map current μ = gaussianMat A N := by
    dsimp [current, μ, fixedWidthMatrixGaussianMeasure]
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ gaussianMat A N) n).map_eq
  have hpair :
      Measure.map (fun ω ↦ (direction ω, current ω)) μ =
        ν.prod (gaussianMat A N) := by
    have hmap :=
      (indepFun_fixedWidthUnroundedVectorDirection_eval A hN x0 n)
        |>.map_prod_eq_prod_map_map
          hdirection.aemeasurable hcurrent.aemeasurable
    change Measure.map (fun ω ↦ (direction ω, current ω)) μ =
      (Measure.map direction μ).prod (Measure.map current μ) at hmap
    rw [hcurrentMap] at hmap
    exact hmap
  change Measure.map
      (standardizedMul ∘ fun ω ↦ (direction ω, current ω)) μ =
    gaussianVec N
  rw [← Measure.map_map hstandardizedMul
    (hdirection.prodMk hcurrent), hpair]
  exact map_standardized_mulVec_prod_eq_gaussianVec hA hN ν hν

/-- Retaining an arbitrary past mark while applying the standardized fresh
Gaussian matrix fibre produces the product of the mark marginal and
`gaussianVec N`. -/
lemma map_mark_standardized_mulVec_prod_eq_prod_gaussianVec
    {E : Type*} [MeasurableSpace E]
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ν : Measure (E × (Fin N → ℝ))) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ p ∂ν, gaussianEuclideanNorm N p.2 = 1) :
    Measure.map
        (fun p : (E × (Fin N → ℝ)) × (Fin N → Fin N → ℝ) ↦
          (p.1.1, (Real.sqrt N / A) • Matrix.mulVec p.2 p.1.2))
        (ν.prod (gaussianMat A N)) =
      (Measure.map Prod.fst ν).prod (gaussianVec N) := by
  classical
  let markStandardizedMul :
      (E × (Fin N → ℝ)) × (Fin N → Fin N → ℝ) →
        E × (Fin N → ℝ) :=
    fun p ↦
      (p.1.1, (Real.sqrt N / A) • Matrix.mulVec p.2 p.1.2)
  have hmulVec : Measurable
      (fun p : (E × (Fin N → ℝ)) × (Fin N → Fin N → ℝ) ↦
        Matrix.mulVec p.2 p.1.2) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp
          (measurable_snd.comp measurable_fst))
  have hmarkStandardizedMul : Measurable markStandardizedMul :=
    (measurable_fst.comp measurable_fst).prodMk
      (hmulVec.const_smul (Real.sqrt N / A))
  change Measure.map markStandardizedMul (ν.prod (gaussianMat A N)) = _
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply hmarkStandardizedMul (hs.prod ht),
    Measure.prod_apply ((hs.prod ht).preimage hmarkStandardizedMul),
    Measure.prod_prod, Measure.map_apply measurable_fst hs]
  have hsections : ∀ᵐ p ∂ν,
      gaussianMat A N
          (Prod.mk p ⁻¹' (markStandardizedMul ⁻¹' (s ×ˢ t))) =
        if p.1 ∈ s then gaussianVec N t else 0 := by
    filter_upwards [hν] with p hp
    have hfix : Measurable
        (fun W : Fin N → Fin N → ℝ ↦
          (Real.sqrt N / A) • Matrix.mulVec W p.2) := by
      apply measurable_pi_iff.mpr
      intro i
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro j _
      fun_prop
    by_cases hps : p.1 ∈ s
    · rw [show Prod.mk p ⁻¹'
          (markStandardizedMul ⁻¹' (s ×ˢ t)) =
          (fun W : Fin N → Fin N → ℝ ↦
            (Real.sqrt N / A) • Matrix.mulVec W p.2) ⁻¹' t by
          ext W
          simp [markStandardizedMul, hps]]
      rw [← Measure.map_apply hfix ht,
        map_standardized_mulVec_gaussianMat_of_unit hA hN p.2 hp,
        if_pos hps]
    · rw [show Prod.mk p ⁻¹'
          (markStandardizedMul ⁻¹' (s ×ˢ t)) = ∅ by
          ext W
          simp [markStandardizedMul, hps]]
      simp [hps]
  calc
    ∫⁻ p, gaussianMat A N
        (Prod.mk p ⁻¹' (markStandardizedMul ⁻¹' (s ×ˢ t))) ∂ν =
        ∫⁻ p, if p.1 ∈ s then gaussianVec N t else 0 ∂ν :=
      lintegral_congr_ae hsections
    _ = ∫⁻ _p in Prod.fst ⁻¹' s, gaussianVec N t ∂ν := by
      rw [← lintegral_indicator (hs.preimage measurable_fst)]
      apply lintegral_congr
      intro p
      simp only [Set.indicator, Set.mem_preimage]
    _ = ν (Prod.fst ⁻¹' s) * gaussianVec N t := by
      rw [setLIntegral_const]
      exact mul_comm _ _

/-- Vector of the first `n` standardized unrounded innovations. -/
noncomputable def fixedWidthUnroundedVectorInnovationPrefix
    {N : ℕ} (hN : 0 < N) (A : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    fixedWidthMatrixSampleSpace N → (Fin n → (Fin N → ℝ)) :=
  fun ω k ↦ fixedWidthUnroundedVectorInnovation hN A x0 k ω

lemma measurable_fixedWidthUnroundedVectorInnovationPrefix
    {N : ℕ} (hN : 0 < N) (A : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable
      (fixedWidthUnroundedVectorInnovationPrefix hN A x0 n) :=
  measurable_pi_lambda _ fun k ↦
    measurable_fixedWidthUnroundedVectorInnovation hN A x0 k

/-- The first `n` innovations as an explicit measurable function of the first
`n` matrix innovations. -/
noncomputable def fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix
    {N : ℕ} (hN : 0 < N) (A : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    (Fin n → (Fin N → Fin N → ℝ)) → (Fin n → (Fin N → ℝ)) :=
  fun u k ↦ fixedWidthUnroundedVectorInnovation hN A x0 k
    (fixedWidthExtendMatrixPrefix N n u)

lemma measurable_fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix
    {N : ℕ} (hN : 0 < N) (A : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    Measurable
      (fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix
        hN A x0 n) :=
  measurable_pi_lambda _ fun k ↦
    (measurable_fixedWidthUnroundedVectorInnovation hN A x0 k).comp
      (measurable_fixedWidthExtendMatrixPrefix N n)

lemma fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix_apply
    {N : ℕ} (hN : 0 < N) (A : ℝ) (x0 : Fin N → ℝ) (n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix
        hN A x0 n (fixedWidthMatrixPrefix N n ω) =
      fixedWidthUnroundedVectorInnovationPrefix hN A x0 n ω := by
  funext k
  have hseq : ∀ j < n,
      fixedWidthExtendMatrixPrefix N n
          (fixedWidthMatrixPrefix N n ω) j = ω j := by
    intro j hj
    simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix, hj]
  unfold fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix
    fixedWidthUnroundedVectorInnovationPrefix
    fixedWidthUnroundedVectorInnovation
  rw [hseq k k.isLt]
  have hdir :
      fixedWidthUnroundedVectorDirection hN x0 k
          (fixedWidthExtendMatrixPrefix N n
            (fixedWidthMatrixPrefix N n ω)) =
        fixedWidthUnroundedVectorDirection hN x0 k ω := by
    unfold fixedWidthUnroundedVectorDirection
    congr 1
    apply fixedWidthUnroundedVectorPath_eq_of_forall_lt
    intro j hj
    exact hseq j (lt_trans hj k.isLt)
  rw [hdir]

/-- The vector of past standardized innovations is independent of the next
standardized innovation. -/
lemma indepFun_fixedWidthUnroundedVectorInnovationPrefix_next
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (n : ℕ) :
    IndepFun
      (fixedWidthUnroundedVectorInnovationPrefix hN A x0 n)
      (fixedWidthUnroundedVectorInnovation hN A x0 n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let past := fixedWidthUnroundedVectorInnovationPrefix hN A x0 n
  let direction := fixedWidthUnroundedVectorDirection hN x0 n
  let current : fixedWidthMatrixSampleSpace N → (Fin N → Fin N → ℝ) :=
    fun ω ↦ ω n
  let pastDirectionFromPrefix :
      (Fin n → (Fin N → Fin N → ℝ)) →
        ((Fin n → (Fin N → ℝ)) × (Fin N → ℝ)) :=
    fun u ↦
      (fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix
        hN A x0 n u,
       fixedWidthUnroundedVectorDirectionFromPrefix hN x0 n u)
  let ν := Measure.map (fun ω ↦ (past ω, direction ω)) μ
  let markStandardizedMul :
      (((Fin n → (Fin N → ℝ)) × (Fin N → ℝ)) ×
          (Fin N → Fin N → ℝ)) →
        ((Fin n → (Fin N → ℝ)) × (Fin N → ℝ)) :=
    fun p ↦
      (p.1.1, (Real.sqrt N / A) • Matrix.mulVec p.2 p.1.2)
  have hpast : Measurable past :=
    measurable_fixedWidthUnroundedVectorInnovationPrefix hN A x0 n
  have hdirection : Measurable direction :=
    measurable_fixedWidthUnroundedVectorDirection hN x0 n
  have hcurrent : Measurable current := measurable_pi_apply n
  have hpastDirectionFromPrefix : Measurable pastDirectionFromPrefix :=
    (measurable_fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix
      hN A x0 n).prodMk
        (measurable_fixedWidthUnroundedVectorDirectionFromPrefix hN x0 n)
  have hpastDirection_apply (ω : fixedWidthMatrixSampleSpace N) :
      pastDirectionFromPrefix (fixedWidthMatrixPrefix N n ω) =
        (past ω, direction ω) := by
    apply Prod.ext
    · exact fixedWidthUnroundedVectorInnovationPrefixFromMatrixPrefix_apply
        hN A x0 n ω
    · exact fixedWidthUnroundedVectorDirectionFromPrefix_apply hN x0 n ω
  have hindCurrent :
      IndepFun (fun ω ↦ (past ω, direction ω)) current μ := by
    have hcomp := (indepFun_fixedWidthMatrixPrefix_eval A N n).comp
      hpastDirectionFromPrefix measurable_id
    convert hcomp using 1
    · funext ω
      exact (hpastDirection_apply ω).symm
    · rfl
  have hcurrentMap : Measure.map current μ = gaussianMat A N := by
    dsimp [current, μ, fixedWidthMatrixGaussianMeasure]
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ gaussianMat A N) n).map_eq
  have hpair :
      Measure.map (fun ω ↦ ((past ω, direction ω), current ω)) μ =
        ν.prod (gaussianMat A N) := by
    have hmap := hindCurrent.map_prod_eq_prod_map_map
      (hpast.prodMk hdirection).aemeasurable hcurrent.aemeasurable
    change Measure.map (fun ω ↦ ((past ω, direction ω), current ω)) μ =
      (Measure.map (fun ω ↦ (past ω, direction ω)) μ).prod
        (Measure.map current μ) at hmap
    rw [hcurrentMap] at hmap
    exact hmap
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map
      (hpast.prodMk hdirection).aemeasurable
  have hν : ∀ᵐ p ∂ν, gaussianEuclideanNorm N p.2 = 1 := by
    change ∀ᵐ p ∂Measure.map (fun ω ↦ (past ω, direction ω)) μ,
      gaussianEuclideanNorm N p.2 = 1
    exact (ae_map_iff (hpast.prodMk hdirection).aemeasurable
      ((measurableSet_singleton 1).preimage
        ((measurable_gaussianEuclideanNorm N).comp measurable_snd))).2
      (Eventually.of_forall fun ω ↦
        gaussianEuclideanNorm_fixedWidthUnitDirection hN
          (fixedWidthUnroundedVectorPath N x0 n ω))
  have hmulVec : Measurable
      (fun p : (((Fin n → (Fin N → ℝ)) × (Fin N → ℝ)) ×
          (Fin N → Fin N → ℝ)) ↦ Matrix.mulVec p.2 p.1.2) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp
          (measurable_snd.comp measurable_fst))
  have hmarkStandardizedMul : Measurable markStandardizedMul :=
    (measurable_fst.comp measurable_fst).prodMk
      (hmulVec.const_smul (Real.sqrt N / A))
  have hjoint :
      Measure.map
          (fun ω ↦
            (past ω, fixedWidthUnroundedVectorInnovation hN A x0 n ω)) μ =
        (Measure.map past μ).prod (gaussianVec N) := by
    have hmarked :=
      map_mark_standardized_mulVec_prod_eq_prod_gaussianVec
        hA hN ν hν
    have hmapped :
        Measure.map markStandardizedMul
            (Measure.map
              (fun ω ↦ ((past ω, direction ω), current ω)) μ) =
          Measure.map markStandardizedMul
            (ν.prod (gaussianMat A N)) := by
      rw [hpair]
    rw [Measure.map_map hmarkStandardizedMul
      ((hpast.prodMk hdirection).prodMk hcurrent)] at hmapped
    have hleft :
        markStandardizedMul ∘
            (fun ω ↦ ((past ω, direction ω), current ω)) =
          fun ω ↦
            (past ω, fixedWidthUnroundedVectorInnovation hN A x0 n ω) := by
      funext ω
      rfl
    rw [hleft, hmarked] at hmapped
    have hfst :
        Measure.map Prod.fst ν = Measure.map past μ := by
      dsimp [ν]
      rw [Measure.map_map measurable_fst (hpast.prodMk hdirection)]
      rfl
    rw [hfst] at hmapped
    exact hmapped
  refine (indepFun_iff_map_prod_eq_prod_map_map
    hpast.aemeasurable
    (measurable_fixedWidthUnroundedVectorInnovation
      hN A x0 n).aemeasurable).2 ?_
  rw [map_fixedWidthUnroundedVectorInnovation hA hN x0 n]
  exact hjoint

/-- The standardized innovations extracted from the unrounded matrix path are
mutually independent. -/
lemma iIndepFun_fixedWidthUnroundedVectorInnovation
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) :
    iIndepFun
      (fixedWidthUnroundedVectorInnovation hN A x0)
      (fixedWidthMatrixGaussianMeasure A N) := by
  apply iIndepFun_of_iIndepFun_fin_prefix
  apply iIndepFun_fin_prefix_of_indepFun_prefix_next
  · exact fun n ↦
      measurable_fixedWidthUnroundedVectorInnovation hN A x0 n
  · intro n
    change IndepFun
      (fixedWidthUnroundedVectorInnovationPrefix hN A x0 n)
      (fixedWidthUnroundedVectorInnovation hN A x0 n)
      (fixedWidthMatrixGaussianMeasure A N)
    exact indepFun_fixedWidthUnroundedVectorInnovationPrefix_next
      hA hN x0 n

/-- The entire standardized innovation sequence has the canonical iid product
Gaussian law used by `fixedWidthRadiusPath`. -/
lemma map_fixedWidthUnroundedVectorInnovationSequence
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) :
    Measure.map
        (fun ω n ↦ fixedWidthUnroundedVectorInnovation hN A x0 n ω)
        (fixedWidthMatrixGaussianMeasure A N) =
      fixedWidthGaussianMeasure N := by
  rw [iIndepFun.map_fun_eq_infinitePi_map
    (fun n ↦
      measurable_fixedWidthUnroundedVectorInnovation hN A x0 n)
    (iIndepFun_fixedWidthUnroundedVectorInnovation hA hN x0)]
  unfold fixedWidthGaussianMeasure
  congr 1
  funext n
  exact map_fixedWidthUnroundedVectorInnovation hA hN x0 n

/-- Under the standardized innovation map, the matrix-driven unrounded
entrance time is exactly the canonical scalar-innovation radius entrance
time. -/
lemma fixedWidthUnroundedVectorEntranceTime_eq_fixedWidthRadiusEntranceTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (ε : ℝ) (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthUnroundedVectorEntranceTime N x0 ε ω =
      fixedWidthRadiusEntranceTime A N (gaussianEuclideanNorm N x0) ε
        (fun n ↦ fixedWidthUnroundedVectorInnovation hN A x0 n ω) := by
  let innovationSequence :
      fixedWidthMatrixSampleSpace N → fixedWidthSampleSpace N :=
    fun ω n ↦ fixedWidthUnroundedVectorInnovation hN A x0 n ω
  change
    hittingAfter (fixedWidthUnroundedVectorRadius N x0) (Set.Iic ε) 0 ω =
      hittingAfter
        (fun n ω ↦ fixedWidthRadiusPath A N
          (gaussianEuclideanNorm N x0) n (innovationSequence ω))
        (Set.Iic ε) 0 ω
  congr 1
  funext n ω'
  exact fixedWidthUnroundedVectorRadius_eq_fixedWidthRadiusPath
    hA hN x0 n ω'

/-- The canonical scalar-innovation radius entrance time exceeds `n` exactly
when the radius remains strictly above the threshold through time `n`. -/
lemma lt_fixedWidthRadiusEntranceTime_iff
    (A : ℝ) (N : ℕ) (R0 ε : ℝ)
    (ω : fixedWidthSampleSpace N) (n : ℕ) :
    (n : WithTop ℕ) < fixedWidthRadiusEntranceTime A N R0 ε ω ↔
      ∀ j ≤ n, ε < fixedWidthRadiusPath A N R0 j ω := by
  rw [← not_le]
  change
    (¬hittingAfter (fixedWidthRadiusPath A N R0)
        (Set.Iic ε) 0 ω ≤ (n : WithTop ℕ)) ↔ _
  have hle :
      hittingAfter (fixedWidthRadiusPath A N R0)
          (Set.Iic ε) 0 ω ≤ (n : WithTop ℕ) ↔
        ∃ j ≤ n, fixedWidthRadiusPath A N R0 j ω ≤ ε := by
    simpa [Set.mem_Icc] using
      (MeasureTheory.hittingAfter_le_iff
        (u := fixedWidthRadiusPath A N R0)
        (s := Set.Iic ε) (n := 0) (i := n) (ω := ω))
  rw [hle]
  simp only [not_exists]
  constructor
  · intro h j hj
    exact lt_of_not_ge fun hle' ↦ h j ⟨hj, hle'⟩
  · intro h j hj
    exact (not_lt_of_ge hj.2) (h j hj.1)

lemma measurableSet_fixedWidthRadiusEntranceTime_gt
    (A : ℝ) (N : ℕ) (R0 ε : ℝ) (n : ℕ) :
    MeasurableSet
      {ω : fixedWidthSampleSpace N |
        (n : WithTop ℕ) < fixedWidthRadiusEntranceTime A N R0 ε ω} := by
  have hset :
      {ω : fixedWidthSampleSpace N |
        (n : WithTop ℕ) < fixedWidthRadiusEntranceTime A N R0 ε ω} =
      ⋂ j ∈ Finset.range (n + 1),
        {ω | ε < fixedWidthRadiusPath A N R0 j ω} := by
    ext ω
    change ((n : WithTop ℕ) <
      fixedWidthRadiusEntranceTime A N R0 ε ω) ↔ _
    rw [lt_fixedWidthRadiusEntranceTime_iff]
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.mem_range,
      Nat.lt_succ_iff]
  rw [hset]
  exact (Finset.range (n + 1)).measurableSet_biInter fun j _ ↦
    measurableSet_lt measurable_const
      (measurable_fixedWidthRadiusPath A N R0 j)

/-- Finite-time survival of the matrix-driven unrounded entrance time has the
same probability as survival of the canonical scalar-innovation radius
entrance time. -/
lemma measureReal_fixedWidthUnroundedVectorEntranceTime_gt_eq_fixedWidthRadiusEntranceTime_gt
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (ε : ℝ) (n : ℕ) :
    (fixedWidthMatrixGaussianMeasure A N).real
        {ω | (n : WithTop ℕ) <
          fixedWidthUnroundedVectorEntranceTime N x0 ε ω} =
      (fixedWidthGaussianMeasure N).real
        {u | (n : WithTop ℕ) <
          fixedWidthRadiusEntranceTime A N
            (gaussianEuclideanNorm N x0) ε u} := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let innovationSequence :
      fixedWidthMatrixSampleSpace N → fixedWidthSampleSpace N :=
    fun ω k ↦ fixedWidthUnroundedVectorInnovation hN A x0 k ω
  let E :=
    {u | (n : WithTop ℕ) <
      fixedWidthRadiusEntranceTime A N
        (gaussianEuclideanNorm N x0) ε u}
  have hinnovationSequence : Measurable innovationSequence :=
    measurable_fixedWidthUnroundedVectorInnovationSequence hN A x0
  have hE : MeasurableSet E :=
    measurableSet_fixedWidthRadiusEntranceTime_gt
      A N (gaussianEuclideanNorm N x0) ε n
  have hpre :
      {ω | (n : WithTop ℕ) <
        fixedWidthUnroundedVectorEntranceTime N x0 ε ω} =
        innovationSequence ⁻¹' E := by
    ext ω
    change ((n : WithTop ℕ) <
      fixedWidthUnroundedVectorEntranceTime N x0 ε ω) ↔ _
    rw [fixedWidthUnroundedVectorEntranceTime_eq_fixedWidthRadiusEntranceTime
      hA hN]
    rfl
  rw [hpre]
  rw [Measure.real_def, Measure.real_def,
    ← Measure.map_apply hinnovationSequence hE]
  rw [show Measure.map innovationSequence μ =
      fixedWidthGaussianMeasure N from
    map_fixedWidthUnroundedVectorInnovationSequence hA hN x0]

/-- The canonical post-floor Gaussian entrance profile transported to the
common matrix-driver unrounded vector path. -/
lemma tendsto_measureReal_fixedWidthUnroundedVectorEntranceTime_gt_postFloorTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (L ε v : ℕ → ℝ) (a : ℝ)
    (hε : ∀ r, 0 < ε r)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    (hlevel : Tendsto
      (fun r ↦
        (Real.log (gaussianEuclideanNorm N x0 / ε r) - L r) /
          Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real {ω |
        (postFloorTime
            (∫ x, fixedWidthIncrementProcess A N 0 x
              ∂fixedWidthGaussianMeasure N)
            (fixedWidthStdDev A N) a L v r : WithTop ℕ) <
          fixedWidthUnroundedVectorEntranceTime N x0 (ε r) ω})
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  have hscalar :=
    tendsto_measureReal_fixedWidthRadiusEntranceTime_gt_postFloorTime
      hA hN hsub hx0 L ε v a hε hL hv hlevel
  refine hscalar.congr' (Eventually.of_forall fun r ↦ ?_)
  exact
    (measureReal_fixedWidthUnroundedVectorEntranceTime_gt_eq_fixedWidthRadiusEntranceTime_gt
      hA hN x0 (ε r)
        (postFloorTime
          (∫ x, fixedWidthIncrementProcess A N 0 x
            ∂fixedWidthGaussianMeasure N)
          (fixedWidthStdDev A N) a L v r)).symm

/-- A fixed polylogarithmic correction is negligible on the square-root
logarithmic scale. -/
lemma tendsto_fixedWidthSubproductLogThreshold_div_sqrt
    (p : ℝ) (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun r ↦ fixedWidthSubproductLogThreshold p (L r) /
        Real.sqrt (L r))
      atTop (nhds 0) := by
  have hbase :
      Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x)
        atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  simpa [fixedWidthSubproductLogThreshold, mul_div_assoc] using
    (hbase.comp hL).const_mul p

/-- The paper's mesh times polylogarithmic threshold has the same normalized
logarithmic entrance level as the bare mesh. -/
lemma tendsto_fixedWidthPolylogEntranceLevel
    (R0 p : ℝ) (hR0 : 0 < R0) (L : ℕ → ℝ)
    (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun r ↦
        (Real.log
            (R0 /
              (Real.exp (-L r) *
                Real.exp (fixedWidthSubproductLogThreshold p (L r)))) -
          L r) /
          Real.sqrt (L r))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun r ↦ Real.sqrt (L r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have hconst :
      Tendsto (fun r ↦ Real.log R0 / Real.sqrt (L r))
        atTop (nhds 0) :=
    hsqrt.const_div_atTop (Real.log R0)
  have hpoly := tendsto_fixedWidthSubproductLogThreshold_div_sqrt p L hL
  have hlim := hconst.sub hpoly
  simp only [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards with r
  rw [Real.log_div hR0.ne'
      (mul_ne_zero (Real.exp_ne_zero _) (Real.exp_ne_zero _)),
    Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp]
  ring

/-- Any linear coupling horizon with coefficient strictly larger than the
inverse drift eventually contains the post-floor cutoff observation time. -/
lemma eventually_postFloorTime_le_fixedWidthCouplingHorizon
    {L v : ℕ → ℝ} {μ σ a C0 : ℝ}
    (hμ : 0 < μ) (hC0 : 1 / μ < C0)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0)) :
    ∀ᶠ r in atTop,
      postFloorTime μ σ a L v r ≤
        fixedWidthCouplingHorizon C0 (L r) := by
  have hC0nonneg : 0 ≤ C0 :=
    (one_div_pos.mpr hμ).trans hC0 |>.le
  have hcanonical :
      Tendsto
        (fun r ↦ (canonicalTime μ σ a L v r : ℝ) / L r)
        atTop (nhds (1 / μ)) :=
    tendsto_canonicalTime_div hμ hL hv
  have hhorizon :
      Tendsto
        (fun r ↦ (fixedWidthCouplingHorizon C0 (L r) : ℝ) / L r)
        atTop (nhds C0) := by
    change Tendsto
      ((fun x : ℝ ↦ (⌊C0 * x⌋₊ : ℝ) / x) ∘ L)
      atTop (nhds C0)
    exact (tendsto_nat_floor_mul_div_atTop hC0nonneg).comp hL
  have hratio := hcanonical.eventually_lt hhorizon hC0
  filter_upwards [
    eventually_postFloorTime_bounds
      (v := v) (σ := σ) (a := a) hμ hL,
    hratio, hL.eventually_gt_atTop 0] with r htime hratioR hLr
  apply htime.1.trans
  have hcast :
      (canonicalTime μ σ a L v r : ℝ) <
        (fixedWidthCouplingHorizon C0 (L r) : ℝ) := by
    exact (div_lt_div_iff_of_pos_right hLr).mp hratioR
  exact Nat.le_of_lt (by exact_mod_cast hcast)

/-- Abstract lower-limit consequence of the synchronous coupling sandwich:
an entrance profile tending to `q` and a vanishing bad-event probability force
rounded survival to be eventually at least `q - δ`. -/
lemma eventually_sub_le_measureReal_fixedWidthRoundedSurvival_of_entrance_coupling
    (A : ℝ) (N : ℕ) (x0 : Fin N → ℝ)
    (ρ R : ℕ → ℝ) (T t : ℕ → ℕ) (q : ℝ)
    (hentry : Tendsto
      (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real
        {ω | (t r : WithTop ℕ) <
          fixedWidthUnroundedVectorEntranceTime N x0 (R r) ω})
      atTop (nhds q))
    (hbad : Tendsto
      (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthCouplingErrorBadSet
          (ρ r) N x0 (T r) (R r)))
      atTop (nhds 0))
    (ht : ∀ᶠ r in atTop, t r ≤ T r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in atTop,
      q - δ ≤
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedAbsorptionSurvivalSetFrom
            (ρ r) N (Qρ (ρ r) x0) (t r)) := by
  have hentryLower :
      ∀ᶠ r in atTop,
        q - δ / 2 <
          (fixedWidthMatrixGaussianMeasure A N).real
            {ω | (t r : WithTop ℕ) <
              fixedWidthUnroundedVectorEntranceTime N x0 (R r) ω} :=
    (tendsto_order.1 hentry).1 (q - δ / 2) (by linarith)
  have hbadUpper :
      ∀ᶠ r in atTop,
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthCouplingErrorBadSet
              (ρ r) N x0 (T r) (R r)) < δ / 2 :=
    (tendsto_order.1 hbad).2 (δ / 2) (by linarith)
  filter_upwards [hentryLower, hbadUpper, ht]
    with r hentryR hbadR htR
  have hsandwich :=
    measureReal_fixedWidthUnroundedNonentrance_le_roundedSurvival_add_couplingErrorBadSet
      A (ρ r) N x0 (T r) (t r) (R r) htR
  linarith

/-- Concrete lower fixed-width cutoff profile on the paper's exponential mesh
scale: rounded survival at the post-floor observation time is eventually at
least the limiting Gaussian tail, up to any positive error. -/
lemma eventually_cdf_sub_le_measureReal_fixedWidthRoundedSurvival_postFloorTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (L v : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in atTop,
      ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal 0 1) (-a) - δ ≤
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedAbsorptionSurvivalSetFrom
            (Real.exp (-L r)) N (Qρ (Real.exp (-L r)) x0)
            (postFloorTime
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N)
              (fixedWidthStdDev A N) a L v r)) := by
  let μ :=
    ∫ x, fixedWidthIncrementProcess A N 0 x
      ∂fixedWidthGaussianMeasure N
  let C0 := 2 / μ
  have hμ : 0 < μ := by
    exact integral_fixedWidthIncrementProcess_zero_pos_of_subcritical hsub
  have hC0pos : 0 < C0 := by
    dsimp [C0]
    positivity
  have hC0 : 1 / μ < C0 := by
    dsimp [C0]
    rw [div_lt_div_iff_of_pos_right hμ]
    norm_num
  obtain ⟨p, _hp, hbadScale⟩ :=
    exists_pos_tendsto_measureReal_fixedWidthCouplingErrorBadSet_zero
      hA hN hsub x0 C0 hC0pos.le
  let R : ℕ → ℝ := fun r ↦
    Real.exp (-L r) *
      Real.exp (fixedWidthSubproductLogThreshold p (L r))
  let T : ℕ → ℕ := fun r ↦ fixedWidthCouplingHorizon C0 (L r)
  let t : ℕ → ℕ := fun r ↦
    postFloorTime μ (fixedWidthStdDev A N) a L v r
  have hentry :
      Tendsto
        (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real
          {ω | (t r : WithTop ℕ) <
            fixedWidthUnroundedVectorEntranceTime N x0 (R r) ω})
        atTop (nhds (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
    exact tendsto_measureReal_fixedWidthUnroundedVectorEntranceTime_gt_postFloorTime
      hA hN hsub x0 hx0 L R v a
      (fun r ↦ mul_pos (Real.exp_pos _) (Real.exp_pos _))
      hL hv
      (tendsto_fixedWidthPolylogEntranceLevel
        (gaussianEuclideanNorm N x0) p hx0 L hL)
  have hbad :
      Tendsto
        (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet
            (Real.exp (-L r)) N x0 (T r) (R r)))
        atTop (nhds 0) := by
    change Tendsto
      ((fun l : ℝ ↦
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet
            (Real.exp (-l)) N x0 (fixedWidthCouplingHorizon C0 l)
            (Real.exp (-l) *
              Real.exp (fixedWidthSubproductLogThreshold p l)))) ∘ L)
      atTop (nhds 0)
    exact hbadScale.comp hL
  have ht : ∀ᶠ r in atTop, t r ≤ T r := by
    exact eventually_postFloorTime_le_fixedWidthCouplingHorizon
      hμ hC0 hL hv
  exact
    eventually_sub_le_measureReal_fixedWidthRoundedSurvival_of_entrance_coupling
      A N x0 (fun r ↦ Real.exp (-L r)) R T t
      (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))
      hentry hbad ht hδ

/-- Exact characterization of a finite matrix-driven unrounded-radius
entrance slice. -/
lemma fixedWidthUnroundedVectorEntranceTime_eq_iff
    (N : ℕ) (x0 : Fin N → ℝ) (ε : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) (m : ℕ) :
    fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ↔
      fixedWidthUnroundedVectorRadius N x0 m ω ≤ ε ∧
        ∀ j, j < m →
          ε < fixedWidthUnroundedVectorRadius N x0 j ω := by
  constructor
  · intro heq
    have hne :
        fixedWidthUnroundedVectorEntranceTime N x0 ε ω ≠ ⊤ := by
      simp [heq]
    have hmem := MeasureTheory.hittingAfter_mem_set_of_ne_top
      (u := fixedWidthUnroundedVectorRadius N x0)
      (s := Set.Iic ε) (n := 0) hne
    have hvalue :
        (fixedWidthUnroundedVectorEntranceTime N x0 ε ω).untopA = m := by
      rw [heq]
      rfl
    change fixedWidthUnroundedVectorRadius N x0
      (fixedWidthUnroundedVectorEntranceTime N x0 ε ω).untopA ω ≤ ε at hmem
    rw [hvalue] at hmem
    refine ⟨hmem, ?_⟩
    intro j hjm
    have hjlt : (j : WithTop ℕ) <
        fixedWidthUnroundedVectorEntranceTime N x0 ε ω := by
      rw [heq]
      exact_mod_cast hjm
    have hnotmem :=
      MeasureTheory.notMem_of_lt_hittingAfter hjlt (Nat.zero_le j)
    change ¬fixedWidthUnroundedVectorRadius N x0 j ω ≤ ε at hnotmem
    exact lt_of_not_ge hnotmem
  · rintro ⟨hmhit, hbefore⟩
    have hle : fixedWidthUnroundedVectorEntranceTime N x0 ε ω ≤ m :=
      MeasureTheory.hittingAfter_le_of_mem (Nat.zero_le m) hmhit
    have hge : (m : WithTop ℕ) ≤
        fixedWidthUnroundedVectorEntranceTime N x0 ε ω := by
      rw [← not_lt]
      intro hlt
      obtain ⟨j, hj, hjmem⟩ :=
        (MeasureTheory.hittingAfter_lt_iff
          (u := fixedWidthUnroundedVectorRadius N x0)
          (s := Set.Iic ε) (n := 0) (i := m) (ω := ω)).mp hlt
      exact (not_lt_of_ge hjmem) (hbefore j hj.2)
    exact le_antisymm hle hge

/-- An exact finite unrounded entrance slice, represented on the strict
matrix prefix that determines it. -/
def fixedWidthUnroundedVectorEntranceSlicePrefixSet
    (N : ℕ) (x0 : Fin N → ℝ) (ε : ℝ) (m : ℕ) :
    Set (Fin m → (Fin N → Fin N → ℝ)) :=
  {u | fixedWidthUnroundedVectorEntranceTime N x0 ε
      (fixedWidthExtendMatrixPrefix N m u) = m}

lemma measurableSet_fixedWidthUnroundedVectorEntranceSlicePrefixSet
    (N : ℕ) (x0 : Fin N → ℝ) (ε : ℝ) (m : ℕ) :
    MeasurableSet
      (fixedWidthUnroundedVectorEntranceSlicePrefixSet N x0 ε m) := by
  exact (measurableSet_singleton (m : WithTop ℕ)).preimage
    (((isStoppingTime_fixedWidthUnroundedVectorEntranceTime
      N x0 ε).measurable').comp
        (measurable_fixedWidthExtendMatrixPrefix N m))

lemma preimage_fixedWidthUnroundedVectorEntranceSlicePrefixSet
    (N : ℕ) (x0 : Fin N → ℝ) (ε : ℝ) (m : ℕ) :
    fixedWidthMatrixPrefix N m ⁻¹'
        fixedWidthUnroundedVectorEntranceSlicePrefixSet N x0 ε m =
      {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m} := by
  ext ω
  let ω' := fixedWidthExtendMatrixPrefix N m
    (fixedWidthMatrixPrefix N m ω)
  have hpath : ∀ j ≤ m,
      fixedWidthUnroundedVectorRadius N x0 j ω =
        fixedWidthUnroundedVectorRadius N x0 j ω' := by
    intro j hj
    unfold fixedWidthUnroundedVectorRadius
    apply congrArg (gaussianEuclideanNorm N)
    apply fixedWidthUnroundedVectorPath_eq_of_forall_lt N x0 j
    intro k hk
    dsimp only [ω']
    simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix,
      lt_of_lt_of_le hk hj]
  change
    (fixedWidthUnroundedVectorEntranceTime N x0 ε ω' = m) ↔
      fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m
  rw [fixedWidthUnroundedVectorEntranceTime_eq_iff,
    fixedWidthUnroundedVectorEntranceTime_eq_iff]
  constructor
  · rintro ⟨hnow, hbefore⟩
    refine ⟨hpath m le_rfl ▸ hnow, ?_⟩
    intro j hjm
    rw [hpath j hjm.le]
    exact hbefore j hjm
  · rintro ⟨hnow, hbefore⟩
    refine ⟨hpath m le_rfl ▸ hnow, ?_⟩
    intro j hjm
    rw [← hpath j hjm.le]
    exact hbefore j hjm

/-- An exact unrounded entrance slice together with the assertion that the
synchronously rounded stopped state lies in a prescribed grid-radius ball. -/
def fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ) (m : ℕ) :
    Set (Fin m → (Fin N → Fin N → ℝ)) :=
  {u | u ∈ fixedWidthUnroundedVectorEntranceSlicePrefixSet N x0 ε m ∧
    fixedWidthRoundedInitialGridRadius ρ N
      (fixedWidthRoundedStateFromPrefix ρ N (Qρ ρ x0) m u) ≤ K}

lemma measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ) (m : ℕ) :
    MeasurableSet
      (fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
        ρ N x0 ε K m) := by
  apply (measurableSet_fixedWidthUnroundedVectorEntranceSlicePrefixSet
    N x0 ε m).inter
  exact measurableSet_le
    (((measurable_gaussianEuclideanNorm N).comp
      (measurable_fixedWidthRoundedStateFromPrefix
        ρ N (Qρ ρ x0) m)).div_const ρ)
    measurable_const

lemma preimage_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ) (m : ℕ) :
    fixedWidthMatrixPrefix N m ⁻¹'
        fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
          ρ N x0 ε K m =
      {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
        fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedVectorPathFrom
            ρ N (Qρ ρ x0) m ω) ≤ K} := by
  ext ω
  change
    (fixedWidthMatrixPrefix N m ω ∈
        fixedWidthUnroundedVectorEntranceSlicePrefixSet N x0 ε m ∧
      fixedWidthRoundedInitialGridRadius ρ N
        (fixedWidthRoundedStateFromPrefix ρ N (Qρ ρ x0) m
          (fixedWidthMatrixPrefix N m ω)) ≤ K) ↔ _
  rw [fixedWidthRoundedStateFromPrefix_apply]
  have hprefix := Set.ext_iff.mp
    (preimage_fixedWidthUnroundedVectorEntranceSlicePrefixSet N x0 ε m) ω
  exact and_congr hprefix Iff.rfl

/-- Product event consisting of a bounded exact unrounded-entrance prefix and
rounded survival for `n` further steps under the fresh shifted driver. -/
def fixedWidthUnroundedEntranceRoundedBoundedSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ)
    (m n : ℕ) :
    Set ((Fin m → (Fin N → Fin N → ℝ)) ×
      fixedWidthMatrixSampleSpace N) :=
  {p | p.1 ∈ fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
      ρ N x0 ε K m ∧
    fixedWidthRoundedVectorPathFrom ρ N
      (fixedWidthRoundedStateFromPrefix ρ N (Qρ ρ x0) m p.1) n p.2 ≠ 0}

lemma measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ)
    (m n : ℕ) :
    MeasurableSet
      (fixedWidthUnroundedEntranceRoundedBoundedSliceFutureSurvivalSet
        ρ N x0 ε K m n) := by
  apply
    ((measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
      ρ N x0 ε K m).preimage measurable_fst).inter
  apply (measurableSet_singleton 0).compl.preimage
  exact (measurable_fixedWidthRoundedVectorPathFrom_prod ρ N n).comp
    (((measurable_fixedWidthRoundedStateFromPrefix
      ρ N (Qρ ρ x0) m).comp measurable_fst).prodMk measurable_snd)

lemma preimage_fixedWidthUnroundedEntranceRoundedBoundedSliceFutureSurvivalSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ)
    (m n : ℕ) :
    (fun ω : fixedWidthMatrixSampleSpace N ↦
      (fixedWidthMatrixPrefix N m ω, fixedWidthMatrixShift N m ω)) ⁻¹'
        fixedWidthUnroundedEntranceRoundedBoundedSliceFutureSurvivalSet
          ρ N x0 ε K m n =
      {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
        fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedVectorPathFrom
            ρ N (Qρ ρ x0) m ω) ≤ K} ∩
        fixedWidthRoundedAbsorptionSurvivalSetFrom
          ρ N (Qρ ρ x0) (m + n) := by
  ext ω
  change
    (fixedWidthMatrixPrefix N m ω ∈
        fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
          ρ N x0 ε K m ∧
      fixedWidthRoundedVectorPathFrom ρ N
        (fixedWidthRoundedStateFromPrefix ρ N (Qρ ρ x0) m
          (fixedWidthMatrixPrefix N m ω)) n
          (fixedWidthMatrixShift N m ω) ≠ 0) ↔
      ((fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
        fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedVectorPathFrom
            ρ N (Qρ ρ x0) m ω) ≤ K) ∧
        fixedWidthRoundedVectorPathFrom
          ρ N (Qρ ρ x0) (m + n) ω ≠ 0)
  rw [fixedWidthRoundedStateFromPrefix_apply,
    ← fixedWidthRoundedVectorPathFrom_add]
  have hprefix := Set.ext_iff.mp
    (preimage_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
      ρ N x0 ε K m) ω
  exact and_congr hprefix Iff.rfl

/-- A uniform bounded-start survival estimate multiplies every exact
unrounded-entrance slice whose synchronously rounded stopped state is bounded. -/
lemma measureReal_unroundedEntrance_boundedSlice_inter_survival_le_mul
    {A ρ : ℝ} {N : ℕ} (x0 : Fin N → ℝ) {ε K a : ℝ}
    (m n : ℕ) (ha : 0 ≤ a)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ K →
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x n) ≤ a) :
    (fixedWidthMatrixGaussianMeasure A N).real
        ({ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
          fixedWidthRoundedInitialGridRadius ρ N
            (fixedWidthRoundedVectorPathFrom
              ρ N (Qρ ρ x0) m ω) ≤ K} ∩
          fixedWidthRoundedAbsorptionSurvivalSetFrom
            ρ N (Qρ ρ x0) (m + n)) ≤
      a * (fixedWidthMatrixGaussianMeasure A N).real
        {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
          fixedWidthRoundedInitialGridRadius ρ N
            (fixedWidthRoundedVectorPathFrom
              ρ N (Qρ ρ x0) m ω) ≤ K} := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let pref := fixedWidthMatrixPrefix N m
  let shift := fixedWidthMatrixShift N m
  let ν := Measure.map pref μ
  let S := fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
    ρ N x0 ε K m
  let E := fixedWidthUnroundedEntranceRoundedBoundedSliceFutureSurvivalSet
    ρ N x0 ε K m n
  have hpref : Measurable pref := measurable_fixedWidthMatrixPrefix N m
  have hshift : Measurable shift := measurable_fixedWidthMatrixShift N m
  haveI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map hpref.aemeasurable
  have hS : MeasurableSet S :=
    measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
      ρ N x0 ε K m
  have hE : MeasurableSet E :=
    measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSliceFutureSurvivalSet
      ρ N x0 ε K m n
  have hsection : ∀ u,
      μ (Prod.mk u ⁻¹' E) ≤
        S.indicator (fun _ ↦ ENNReal.ofReal a) u := by
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      change u ∈ fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
        ρ N x0 ε K m at hu
      have hbound := hsurvival
        (fixedWidthRoundedStateFromPrefix ρ N (Qρ ρ x0) m u) hu.2
      have hsecEq : Prod.mk u ⁻¹' E =
          fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N
            (fixedWidthRoundedStateFromPrefix
              ρ N (Qρ ρ x0) m u) n := by
        ext w
        change
          (u ∈ fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
              ρ N x0 ε K m ∧
            fixedWidthRoundedVectorPathFrom ρ N
              (fixedWidthRoundedStateFromPrefix
                ρ N (Qρ ρ x0) m u) n w ≠ 0) ↔
          fixedWidthRoundedVectorPathFrom ρ N
            (fixedWidthRoundedStateFromPrefix
              ρ N (Qρ ρ x0) m u) n w ≠ 0
        simp only [hu, true_and]
      rw [hsecEq]
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) ha]
      exact hbound
    · rw [Set.indicator_of_notMem hu]
      change u ∉ fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
        ρ N x0 ε K m at hu
      have hsecEmpty : Prod.mk u ⁻¹' E = ∅ := by
        ext w
        change
          (u ∈ fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
              ρ N x0 ε K m ∧
            fixedWidthRoundedVectorPathFrom ρ N
              (fixedWidthRoundedStateFromPrefix
                ρ N (Qρ ρ x0) m u) n w ≠ 0) ↔ False
        simp only [hu, false_and]
      rw [hsecEmpty, measure_empty]
  have hprod : (ν.prod μ) E ≤ ENNReal.ofReal a * ν S := by
    rw [Measure.prod_apply hE]
    calc
      (∫⁻ u, μ (Prod.mk u ⁻¹' E) ∂ν) ≤
          ∫⁻ u, S.indicator (fun _ ↦ ENNReal.ofReal a) u ∂ν :=
        lintegral_mono hsection
      _ = ENNReal.ofReal a * ν S := by
        rw [lintegral_indicator hS]
        simp
  have hprodReal : (ν.prod μ).real E ≤ a * ν.real S := by
    rw [measureReal_def, measureReal_def]
    calc
      ENNReal.toReal ((ν.prod μ) E) ≤
          ENNReal.toReal (ENNReal.ofReal a * ν S) :=
        ENNReal.toReal_mono (by finiteness) hprod
      _ = a * ENNReal.toReal (ν S) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]
  have hcoeff : ν.real S = μ.real
      {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
        fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedVectorPathFrom
            ρ N (Qρ ρ x0) m ω) ≤ K} := by
    dsimp only [ν, pref, S]
    rw [map_measureReal_apply
      (measurable_fixedWidthMatrixPrefix N m)
      (measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
        ρ N x0 ε K m)]
    rw [preimage_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet]
  let restart := fun ω : fixedWidthMatrixSampleSpace N ↦
    (pref ω, shift ω)
  have hrestart : Measurable restart := hpref.prodMk hshift
  calc
    μ.real
        ({ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
          fixedWidthRoundedInitialGridRadius ρ N
            (fixedWidthRoundedVectorPathFrom
              ρ N (Qρ ρ x0) m ω) ≤ K} ∩
          fixedWidthRoundedAbsorptionSurvivalSetFrom
            ρ N (Qρ ρ x0) (m + n)) =
        (Measure.map restart μ).real E := by
      rw [map_measureReal_apply hrestart hE]
      exact congrArg μ.real
        (preimage_fixedWidthUnroundedEntranceRoundedBoundedSliceFutureSurvivalSet
          ρ N x0 ε K m n).symm
    _ = (ν.prod μ).real E := by
      congr 1
      exact map_prod_fixedWidthMatrixPrefix_shift A N m
    _ ≤ a * ν.real S := hprodReal
    _ = a * μ.real
        {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
          fixedWidthRoundedInitialGridRadius ρ N
            (fixedWidthRoundedVectorPathFrom
              ρ N (Qρ ρ x0) m ω) ≤ K} := by
      rw [hcoeff]

/-- Summing the disjoint bounded unrounded-entrance slices preserves the
uniform fresh-future exponential survival bound. -/
lemma sum_measureReal_unroundedEntrance_boundedSlice_inter_survival_le_exp_neg_mul
    {A ρ s : ℝ} {N : ℕ} (x0 : Fin N → ℝ) {ε K : ℝ}
    (H u : ℕ) (hs : 0 ≤ s)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ K →
        ∀ t : ℕ,
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x t) ≤
            Real.exp (-s * t)) :
    ∑ m ∈ Finset.Icc 0 H,
        (fixedWidthMatrixGaussianMeasure A N).real
          ({ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
            fixedWidthRoundedInitialGridRadius ρ N
              (fixedWidthRoundedVectorPathFrom
                ρ N (Qρ ρ x0) m ω) ≤ K} ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom
              ρ N (Qρ ρ x0) (H + u)) ≤
      Real.exp (-s * u) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let fiber := fun m : ℕ ↦
    {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
      fixedWidthRoundedInitialGridRadius ρ N
        (fixedWidthRoundedVectorPathFrom
          ρ N (Qρ ρ x0) m ω) ≤ K}
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hterm : ∀ m ∈ Finset.Icc 0 H,
      μ.real
          (fiber m ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom
              ρ N (Qρ ρ x0) (H + u)) ≤
        Real.exp (-s * u) * μ.real (fiber m) := by
    intro m hm
    have hmH : m ≤ H := (Finset.mem_Icc.mp hm).2
    have hmtotal : m ≤ H + u := hmH.trans (Nat.le_add_right H u)
    have hrestart :=
      measureReal_unroundedEntrance_boundedSlice_inter_survival_le_mul
        (A := A) (ρ := ρ) (N := N) x0
        (ε := ε) (K := K)
        (a := Real.exp (-s * ((H + u - m : ℕ) : ℝ)))
        m (H + u - m) (Real.exp_pos _).le
        (fun x hx ↦ hsurvival x hx (H + u - m))
    have htime : u ≤ H + u - m := by omega
    have htimeReal : (u : ℝ) ≤ (H + u - m : ℕ) := by
      exact_mod_cast htime
    have hexp :
        Real.exp (-s * ((H + u - m : ℕ) : ℝ)) ≤
          Real.exp (-s * u) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hrestart' :
        μ.real
            (fiber m ∩
              fixedWidthRoundedAbsorptionSurvivalSetFrom
                ρ N (Qρ ρ x0) (H + u)) ≤
          Real.exp (-s * ((H + u - m : ℕ) : ℝ)) *
            μ.real (fiber m) := by
      simpa only [μ, fiber, Nat.add_sub_of_le hmtotal] using hrestart
    exact hrestart'.trans
      (mul_le_mul_of_nonneg_right hexp measureReal_nonneg)
  have hmeas : ∀ m ∈ Finset.Icc 0 H, MeasurableSet (fiber m) := by
    intro m _hm
    change MeasurableSet
      {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
        fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedVectorPathFrom
            ρ N (Qρ ρ x0) m ω) ≤ K}
    rw [← preimage_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet]
    exact
      (measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
        ρ N x0 ε K m).preimage
          (measurable_fixedWidthMatrixPrefix N m)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 0 H)) fiber := by
    intro i _hi j _hj hij
    change Disjoint (fiber i) (fiber j)
    rw [Set.disjoint_left]
    intro ω hiω hjω
    apply hij
    change
      (fixedWidthUnroundedVectorEntranceTime N x0 ε ω = i ∧ _) at hiω
    change
      (fixedWidthUnroundedVectorEntranceTime N x0 ε ω = j ∧ _) at hjω
    exact_mod_cast hiω.1.symm.trans hjω.1
  have hmass : (∑ m ∈ Finset.Icc 0 H, μ.real (fiber m)) ≤ 1 := by
    simpa only [probReal_univ] using
      (sum_measureReal_le_measureReal_univ (μ := μ) hmeas hdisj)
  calc
    ∑ m ∈ Finset.Icc 0 H,
        μ.real
          (fiber m ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom
              ρ N (Qρ ρ x0) (H + u)) ≤
        ∑ m ∈ Finset.Icc 0 H,
          Real.exp (-s * u) * μ.real (fiber m) :=
      Finset.sum_le_sum fun m hm ↦ hterm m hm
    _ = Real.exp (-s * u) *
        ∑ m ∈ Finset.Icc 0 H, μ.real (fiber m) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-s * u) * 1 :=
      mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le
    _ = Real.exp (-s * u) := mul_one _

/-- Generic form of the bounded stopped-slice sum: any uniform fresh-start
remainder valid from time `u` onward bounds the whole stopped-entrance sum. -/
lemma sum_measureReal_unroundedEntrance_boundedSlice_inter_survival_le
    {A ρ a : ℝ} {N : ℕ} (x0 : Fin N → ℝ) {ε K : ℝ}
    (H u : ℕ) (ha : 0 ≤ a)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ K →
        ∀ t : ℕ, u ≤ t →
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x t) ≤ a) :
    ∑ m ∈ Finset.Icc 0 H,
        (fixedWidthMatrixGaussianMeasure A N).real
          ({ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
            fixedWidthRoundedInitialGridRadius ρ N
              (fixedWidthRoundedVectorPathFrom
                ρ N (Qρ ρ x0) m ω) ≤ K} ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom
              ρ N (Qρ ρ x0) (H + u)) ≤ a := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let fiber := fun m : ℕ ↦
    {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
      fixedWidthRoundedInitialGridRadius ρ N
        (fixedWidthRoundedVectorPathFrom
          ρ N (Qρ ρ x0) m ω) ≤ K}
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hterm : ∀ m ∈ Finset.Icc 0 H,
      μ.real
          (fiber m ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom
              ρ N (Qρ ρ x0) (H + u)) ≤
        a * μ.real (fiber m) := by
    intro m hm
    have hmH : m ≤ H := (Finset.mem_Icc.mp hm).2
    have hmtotal : m ≤ H + u := hmH.trans (Nat.le_add_right H u)
    have htime : u ≤ H + u - m := by omega
    have hrestart :=
      measureReal_unroundedEntrance_boundedSlice_inter_survival_le_mul
        (A := A) (ρ := ρ) (N := N) x0
        (ε := ε) (K := K) (a := a)
        m (H + u - m) ha
        (fun x hx ↦ hsurvival x hx (H + u - m) htime)
    simpa only [μ, fiber, Nat.add_sub_of_le hmtotal] using hrestart
  have hmeas : ∀ m ∈ Finset.Icc 0 H, MeasurableSet (fiber m) := by
    intro m _hm
    change MeasurableSet
      {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
        fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedVectorPathFrom
            ρ N (Qρ ρ x0) m ω) ≤ K}
    rw [← preimage_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet]
    exact
      (measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
        ρ N x0 ε K m).preimage
          (measurable_fixedWidthMatrixPrefix N m)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 0 H)) fiber := by
    intro i _hi j _hj hij
    change Disjoint (fiber i) (fiber j)
    rw [Set.disjoint_left]
    intro ω hiω hjω
    apply hij
    change
      (fixedWidthUnroundedVectorEntranceTime N x0 ε ω = i ∧ _) at hiω
    change
      (fixedWidthUnroundedVectorEntranceTime N x0 ε ω = j ∧ _) at hjω
    exact_mod_cast hiω.1.symm.trans hjω.1
  have hmass : (∑ m ∈ Finset.Icc 0 H, μ.real (fiber m)) ≤ 1 := by
    simpa only [probReal_univ] using
      (sum_measureReal_le_measureReal_univ (μ := μ) hmeas hdisj)
  calc
    ∑ m ∈ Finset.Icc 0 H,
        μ.real
          (fiber m ∩
            fixedWidthRoundedAbsorptionSurvivalSetFrom
              ρ N (Qρ ρ x0) (H + u)) ≤
        ∑ m ∈ Finset.Icc 0 H, a * μ.real (fiber m) :=
      Finset.sum_le_sum fun m hm ↦ hterm m hm
    _ = a * ∑ m ∈ Finset.Icc 0 H, μ.real (fiber m) := by
      rw [Finset.mul_sum]
    _ ≤ a * 1 := mul_le_mul_of_nonneg_left hmass ha
    _ = a := mul_one a

/-- Event that the unrounded path enters by `H` and that its synchronously
rounded state on the exact entrance slice lies in a prescribed grid ball. -/
def fixedWidthUnroundedEntranceRoundedBoundedSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ) (H : ℕ) :
    Set (fixedWidthMatrixSampleSpace N) :=
  ⋃ m ∈ Finset.Icc 0 H,
    {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
      fixedWidthRoundedInitialGridRadius ρ N
        (fixedWidthRoundedVectorPathFrom ρ N (Qρ ρ x0) m ω) ≤ K}

lemma measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlice
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ) (m : ℕ) :
    MeasurableSet
      {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
        fixedWidthRoundedInitialGridRadius ρ N
          (fixedWidthRoundedVectorPathFrom
            ρ N (Qρ ρ x0) m ω) ≤ K} := by
  rw [← preimage_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet]
  exact
    (measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlicePrefixSet
      ρ N x0 ε K m).preimage (measurable_fixedWidthMatrixPrefix N m)

lemma measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (ε K : ℝ) (H : ℕ) :
    MeasurableSet
      (fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H) := by
  apply Finset.measurableSet_biUnion
  intro m _hm
  exact measurableSet_fixedWidthUnroundedEntranceRoundedBoundedSlice
    ρ N x0 ε K m

/-- On the bounded stopped-entrance event, survival for `u` additional steps
has the same uniform exponential bound as a fresh bounded start. -/
lemma measureReal_unroundedEntranceRoundedBoundedSet_inter_survival_le_exp_neg_mul
    {A ρ s : ℝ} {N : ℕ} (x0 : Fin N → ℝ) {ε K : ℝ}
    (H u : ℕ) (hs : 0 ≤ s)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ K →
        ∀ t : ℕ,
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x t) ≤
            Real.exp (-s * t)) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H ∩
          fixedWidthRoundedAbsorptionSurvivalSetFrom
            ρ N (Qρ ρ x0) (H + u)) ≤
      Real.exp (-s * u) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let fiber := fun m : ℕ ↦
    {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
      fixedWidthRoundedInitialGridRadius ρ N
        (fixedWidthRoundedVectorPathFrom
          ρ N (Qρ ρ x0) m ω) ≤ K}
  let survival :=
    fixedWidthRoundedAbsorptionSurvivalSetFrom
      ρ N (Qρ ρ x0) (H + u)
  have hset :
      fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H ∩
          survival =
        ⋃ m ∈ Finset.Icc 0 H, fiber m ∩ survival := by
    ext ω
    simp only [fixedWidthUnroundedEntranceRoundedBoundedSet,
      Set.mem_inter_iff, Set.mem_iUnion, fiber, survival]
    constructor
    · rintro ⟨⟨m, hm, hωm⟩, hsurvival'⟩
      exact ⟨m, hm, hωm, hsurvival'⟩
    · rintro ⟨m, hm, hωm, hsurvival'⟩
      exact ⟨⟨m, hm, hωm⟩, hsurvival'⟩
  rw [hset]
  exact
    (measureReal_biUnion_finset_le
      (μ := μ) (Finset.Icc 0 H) (fun m ↦ fiber m ∩ survival)).trans
      (by
        simpa only [μ, fiber, survival] using
          sum_measureReal_unroundedEntrance_boundedSlice_inter_survival_le_exp_neg_mul
            (A := A) (ρ := ρ) (s := s) (N := N) x0
            (ε := ε) (K := K) H u hs hsurvival)

/-- Generic bounded stopped-entrance union bound for an arbitrary uniform
fresh-start remainder valid from time `u` onward. -/
lemma measureReal_unroundedEntranceRoundedBoundedSet_inter_survival_le
    {A ρ a : ℝ} {N : ℕ} (x0 : Fin N → ℝ) {ε K : ℝ}
    (H u : ℕ) (ha : 0 ≤ a)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ K →
        ∀ t : ℕ, u ≤ t →
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x t) ≤ a) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H ∩
          fixedWidthRoundedAbsorptionSurvivalSetFrom
            ρ N (Qρ ρ x0) (H + u)) ≤ a := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let fiber := fun m : ℕ ↦
    {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m ∧
      fixedWidthRoundedInitialGridRadius ρ N
        (fixedWidthRoundedVectorPathFrom
          ρ N (Qρ ρ x0) m ω) ≤ K}
  let survival :=
    fixedWidthRoundedAbsorptionSurvivalSetFrom
      ρ N (Qρ ρ x0) (H + u)
  have hset :
      fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H ∩
          survival =
        ⋃ m ∈ Finset.Icc 0 H, fiber m ∩ survival := by
    ext ω
    simp only [fixedWidthUnroundedEntranceRoundedBoundedSet,
      Set.mem_inter_iff, Set.mem_iUnion, fiber, survival]
    constructor
    · rintro ⟨⟨m, hm, hωm⟩, hsurvival'⟩
      exact ⟨m, hm, hωm, hsurvival'⟩
    · rintro ⟨m, hm, hωm, hsurvival'⟩
      exact ⟨⟨m, hm, hωm⟩, hsurvival'⟩
  rw [hset]
  exact
    (measureReal_biUnion_finset_le
      (μ := μ) (Finset.Icc 0 H) (fun m ↦ fiber m ∩ survival)).trans
      (by
        simpa only [μ, fiber, survival] using
          sum_measureReal_unroundedEntrance_boundedSlice_inter_survival_le
            (A := A) (ρ := ρ) (a := a) (N := N) x0
            (ε := ε) (K := K) H u ha hsurvival)

/-- If the unrounded path enters by `H` and the synchronous error stays below
`d` through a larger horizon, then the rounded stopped state belongs to the
bounded entrance event whenever `d + ε ≤ Kρ`. -/
lemma fixedWidthUnroundedEntrance_le_diff_couplingErrorBadSet_subset_boundedSet
    {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) (x0 : Fin N → ℝ)
    (T H : ℕ) (ε d K : ℝ) (hHT : H ≤ T)
    (hthreshold : d + ε ≤ K * ρ) :
    {ω | fixedWidthUnroundedVectorEntranceTime N x0 ε ω ≤
        (H : WithTop ℕ)} \
        fixedWidthCouplingErrorBadSet ρ N x0 T d ⊆
      fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H := by
  intro ω hω
  rcases hω with ⟨hentrance, hgood⟩
  change fixedWidthUnroundedVectorEntranceTime N x0 ε ω ≤
    (H : WithTop ℕ) at hentrance
  have hfinite :
      fixedWidthUnroundedVectorEntranceTime N x0 ε ω ≠ ⊤ := by
    intro htop
    simp [htop] at hentrance
  let m := (fixedWidthUnroundedVectorEntranceTime N x0 ε ω).untopA
  have heq : fixedWidthUnroundedVectorEntranceTime N x0 ε ω = m := by
    cases hval : fixedWidthUnroundedVectorEntranceTime N x0 ε ω with
    | top => exact (hfinite hval).elim
    | coe k =>
        dsimp only [m]
        rw [hval]
        rfl
  have hmH : m ≤ H := by
    rw [heq] at hentrance
    exact_mod_cast hentrance
  have hmT : m ≤ T := hmH.trans hHT
  have herr : fixedWidthVectorError ρ N x0 m ω ≤ d := by
    apply le_of_not_gt
    intro herr'
    apply hgood
    rw [fixedWidthCouplingErrorBadSet]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_of_le hmT), herr'⟩
  have hunrounded :
      fixedWidthUnroundedVectorRadius N x0 m ω ≤ ε :=
    (fixedWidthUnroundedVectorEntranceTime_eq_iff N x0 ε ω m).mp heq |>.1
  have hdecomp :
      fixedWidthRoundedVectorPath ρ N x0 m ω =
        fixedWidthVectorDiscrepancy ρ N x0 m ω +
          fixedWidthUnroundedVectorPath N x0 m ω := by
    ext i
    simp [fixedWidthVectorDiscrepancy]
  have hrounded :
      gaussianEuclideanNorm N (fixedWidthRoundedVectorPath ρ N x0 m ω) ≤
        d + ε := by
    rw [hdecomp]
    exact (gaussianEuclideanNorm_add_le N _ _).trans
      (add_le_add herr hunrounded)
  rw [fixedWidthUnroundedEntranceRoundedBoundedSet]
  apply Set.mem_iUnion.mpr ⟨m, ?_⟩
  apply Set.mem_iUnion.mpr
    ⟨by simpa using Finset.mem_Icc.mpr ⟨Nat.zero_le m, hmH⟩, ?_⟩
  refine ⟨heq, ?_⟩
  rw [← fixedWidthRoundedVectorPath_eq_from]
  unfold fixedWidthRoundedInitialGridRadius
  rw [div_le_iff₀ hρ]
  exact hrounded.trans hthreshold

/-- Rounded survival through `H + u` lies in late unrounded entrance, coupling
failure, or survival after a bounded stopped entrance. -/
lemma fixedWidthRoundedSurvival_subset_unroundedNonentrance_union_bad_union_bounded
    {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) (x0 : Fin N → ℝ)
    (T H u : ℕ) (ε d K : ℝ) (hHT : H ≤ T)
    (hthreshold : d + ε ≤ K * ρ) :
    fixedWidthRoundedAbsorptionSurvivalSetFrom
        ρ N (Qρ ρ x0) (H + u) ⊆
      {ω | (H : WithTop ℕ) <
        fixedWidthUnroundedVectorEntranceTime N x0 ε ω} ∪
      (fixedWidthCouplingErrorBadSet ρ N x0 T d ∪
        (fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H ∩
          fixedWidthRoundedAbsorptionSurvivalSetFrom
            ρ N (Qρ ρ x0) (H + u))) := by
  intro ω hsurvival
  by_cases hlate : (H : WithTop ℕ) <
      fixedWidthUnroundedVectorEntranceTime N x0 ε ω
  · exact Or.inl hlate
  by_cases hbad : ω ∈ fixedWidthCouplingErrorBadSet ρ N x0 T d
  · exact Or.inr (Or.inl hbad)
  · exact Or.inr (Or.inr ⟨
      fixedWidthUnroundedEntrance_le_diff_couplingErrorBadSet_subset_boundedSet
        hρ N x0 T H ε d K hHT hthreshold
        ⟨le_of_not_gt hlate, hbad⟩,
      hsurvival⟩)

/-- Abstract upper probability sandwich: rounded survival is bounded by late
unrounded entrance, coupling failure, and the exponential post-entrance
remainder. -/
lemma measureReal_fixedWidthRoundedSurvival_le_unroundedNonentrance_add_bad_add_exp
    {A ρ s : ℝ} (hρ : 0 < ρ) {N : ℕ} (x0 : Fin N → ℝ)
    (T H u : ℕ) (ε d K : ℝ) (hHT : H ≤ T)
    (hthreshold : d + ε ≤ K * ρ) (hs : 0 ≤ s)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ K →
        ∀ t : ℕ,
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x t) ≤
            Real.exp (-s * t)) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom
          ρ N (Qρ ρ x0) (H + u)) ≤
      (fixedWidthMatrixGaussianMeasure A N).real
          {ω | (H : WithTop ℕ) <
            fixedWidthUnroundedVectorEntranceTime N x0 ε ω} +
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet ρ N x0 T d) +
        Real.exp (-s * u) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let late :=
    {ω | (H : WithTop ℕ) <
      fixedWidthUnroundedVectorEntranceTime N x0 ε ω}
  let bad := fixedWidthCouplingErrorBadSet ρ N x0 T d
  let stopped :=
    fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H ∩
      fixedWidthRoundedAbsorptionSurvivalSetFrom
        ρ N (Qρ ρ x0) (H + u)
  have hinclusion :
      fixedWidthRoundedAbsorptionSurvivalSetFrom
          ρ N (Qρ ρ x0) (H + u) ⊆ late ∪ (bad ∪ stopped) := by
    exact
      fixedWidthRoundedSurvival_subset_unroundedNonentrance_union_bad_union_bounded
        hρ N x0 T H u ε d K hHT hthreshold
  have hstopped : μ.real stopped ≤ Real.exp (-s * u) := by
    exact
      measureReal_unroundedEntranceRoundedBoundedSet_inter_survival_le_exp_neg_mul
        (A := A) (ρ := ρ) (s := s) (N := N) x0
        (ε := ε) (K := K) H u hs hsurvival
  calc
    μ.real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom
          ρ N (Qρ ρ x0) (H + u)) ≤
        μ.real (late ∪ (bad ∪ stopped)) :=
      measureReal_mono hinclusion (measure_ne_top μ _)
    _ ≤ μ.real late + μ.real (bad ∪ stopped) :=
      measureReal_union_le late _
    _ ≤ μ.real late + (μ.real bad + μ.real stopped) := by
      exact add_le_add le_rfl (measureReal_union_le bad stopped)
    _ ≤ μ.real late + μ.real bad + Real.exp (-s * u) := by
      linarith

/-- Generic upper probability sandwich with an arbitrary nonnegative uniform
fresh-start remainder valid from the buffer time onward. -/
lemma measureReal_fixedWidthRoundedSurvival_le_unroundedNonentrance_add_bad_add
    {A ρ a : ℝ} (hρ : 0 < ρ) {N : ℕ} (x0 : Fin N → ℝ)
    (T H u : ℕ) (ε d K : ℝ) (hHT : H ≤ T)
    (hthreshold : d + ε ≤ K * ρ) (ha : 0 ≤ a)
    (hsurvival : ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius ρ N x ≤ K →
        ∀ t : ℕ, u ≤ t →
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N x t) ≤ a) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom
          ρ N (Qρ ρ x0) (H + u)) ≤
      (fixedWidthMatrixGaussianMeasure A N).real
          {ω | (H : WithTop ℕ) <
            fixedWidthUnroundedVectorEntranceTime N x0 ε ω} +
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet ρ N x0 T d) + a := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let late :=
    {ω | (H : WithTop ℕ) <
      fixedWidthUnroundedVectorEntranceTime N x0 ε ω}
  let bad := fixedWidthCouplingErrorBadSet ρ N x0 T d
  let stopped :=
    fixedWidthUnroundedEntranceRoundedBoundedSet ρ N x0 ε K H ∩
      fixedWidthRoundedAbsorptionSurvivalSetFrom
        ρ N (Qρ ρ x0) (H + u)
  have hinclusion :
      fixedWidthRoundedAbsorptionSurvivalSetFrom
          ρ N (Qρ ρ x0) (H + u) ⊆ late ∪ (bad ∪ stopped) :=
    fixedWidthRoundedSurvival_subset_unroundedNonentrance_union_bad_union_bounded
      hρ N x0 T H u ε d K hHT hthreshold
  have hstopped : μ.real stopped ≤ a :=
    measureReal_unroundedEntranceRoundedBoundedSet_inter_survival_le
      (A := A) (ρ := ρ) (a := a) (N := N) x0
      (ε := ε) (K := K) H u ha hsurvival
  calc
    μ.real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom
          ρ N (Qρ ρ x0) (H + u)) ≤
        μ.real (late ∪ (bad ∪ stopped)) :=
      measureReal_mono hinclusion (measure_ne_top μ _)
    _ ≤ μ.real late + μ.real (bad ∪ stopped) :=
      measureReal_union_le late _
    _ ≤ μ.real late + (μ.real bad + μ.real stopped) := by
      exact add_le_add le_rfl (measureReal_union_le bad stopped)
    _ ≤ μ.real late + μ.real bad + a := by
      linarith

/-- Polylogarithmic grid-radius envelope used after the upper comparison
entrance. -/
noncomputable def fixedWidthUpperGridRadius (p L : ℝ) : ℝ :=
  2 * Real.exp ((p + 1) * Real.log L)

/-- Natural absorption buffer obtained from the paper-facing logarithmic-start
absorption bound, with one additional `log L` tail offset. -/
noncomputable def fixedWidthUpperAbsorptionBuffer
    (C p L : ℝ) : ℕ :=
  ⌊C * Real.log (fixedWidthUpperGridRadius p L) + Real.log L⌋₊

lemma two_le_fixedWidthUpperGridRadius
    {p L : ℝ} (hp : -1 ≤ p) (hL : 1 ≤ L) :
    2 ≤ fixedWidthUpperGridRadius p L := by
  unfold fixedWidthUpperGridRadius
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hexp : 1 ≤ Real.exp ((p + 1) * Real.log L) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (by linarith) hlog
  nlinarith

/-- The coupling error threshold plus the enlarged unrounded entrance radius
fits inside the polylogarithmic rounded grid-radius envelope. -/
lemma fixedWidthUpperThreshold_sum_le
    {p L : ℝ} (hL : 1 ≤ L) :
    Real.exp (-L) * Real.exp (p * Real.log L) +
        Real.exp (-L) * Real.exp ((p + 1) * Real.log L) ≤
      fixedWidthUpperGridRadius p L * Real.exp (-L) := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hexp :
      Real.exp (p * Real.log L) ≤
        Real.exp ((p + 1) * Real.log L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold fixedWidthUpperGridRadius
  nlinarith [Real.exp_pos (-L)]

/-- The logarithmic fresh-start absorption delay is negligible on the cutoff
window scale. -/
lemma tendsto_fixedWidthUpperAbsorptionBuffer_div_sqrt
    (C p : ℝ) (hC : 0 ≤ C) (hp : -1 ≤ p)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun r ↦
        (fixedWidthUpperAbsorptionBuffer C p (L r) : ℝ) /
          Real.sqrt (L r))
      atTop (nhds 0) := by
  have hbase :
      Tendsto (fun x : ℝ ↦ Real.log x / Real.sqrt x)
        atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hsqrt : Tendsto (fun r ↦ Real.sqrt (L r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have hlog_grid : ∀ x : ℝ,
      Real.log (fixedWidthUpperGridRadius p x) =
        Real.log 2 + (p + 1) * Real.log x := by
    intro x
    unfold fixedWidthUpperGridRadius
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
  have harg :
      Tendsto
        (fun r ↦
          (C * Real.log (fixedWidthUpperGridRadius p (L r)) +
              Real.log (L r)) /
            Real.sqrt (L r))
        atTop (nhds 0) := by
    have hlim :=
      (hsqrt.const_div_atTop (C * Real.log 2)).add
        ((hbase.comp hL).const_mul (C * (p + 1) + 1))
    have hlim' :
        Tendsto
          (fun r ↦
            C * Real.log 2 / Real.sqrt (L r) +
              (C * (p + 1) + 1) *
                (Real.log (L r) / Real.sqrt (L r)))
          atTop (nhds 0) := by
      simpa only [Function.comp_apply, mul_zero, add_zero] using hlim
    refine hlim'.congr' ?_
    filter_upwards with r
    rw [hlog_grid]
    ring
  have hLone : ∀ᶠ r in atTop, 1 ≤ L r :=
    hL.eventually_ge_atTop 1
  have harg_nonneg : ∀ᶠ r in atTop,
      0 ≤ C * Real.log (fixedWidthUpperGridRadius p (L r)) +
        Real.log (L r) := by
    filter_upwards [hLone] with r hLr
    exact add_nonneg
      (mul_nonneg hC
        (Real.log_nonneg
          (le_trans (by norm_num)
            (two_le_fixedWidthUpperGridRadius hp hLr))))
      (Real.log_nonneg hLr)
  change Tendsto
    (fun r ↦
      (⌊C * Real.log (fixedWidthUpperGridRadius p (L r)) +
        Real.log (L r)⌋₊ : ℝ) / Real.sqrt (L r))
    atTop (nhds 0)
  exact tendsto_natFloor_div harg_nonneg hsqrt harg

/-- The polynomial fresh-start tail produced by the logarithmic absorption
buffer vanishes along every diverging scale. -/
lemma tendsto_fixedWidthUpperAbsorptionRemainder_zero
    (C c : ℝ) (hc : 0 < c)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun r ↦ C * Real.exp (-c * Real.log (L r)))
      atTop (nhds 0) := by
  have hpow := (tendsto_rpow_neg_atTop hc).comp hL
  have hlim := hpow.const_mul C
  simp only [mul_zero] at hlim
  refine hlim.congr' ?_
  have hLpos : ∀ᶠ r in atTop, 0 < L r :=
    hL.eventually_gt_atTop 0
  filter_upwards [hLpos] with r hLr
  change C * (L r) ^ (-c) = C * Real.exp (-c * Real.log (L r))
  rw [Real.rpow_def_of_pos hLr]
  congr 2
  ring

/-- Exact-start rounded survival probabilities decrease with the observation
time. -/
lemma measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_antitone
    {A ρ : ℝ} {N : ℕ} (y0 : Fin N → ℝ) {m n : ℕ}
    (hmn : m ≤ n) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 n) ≤
      (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 m) := by
  apply measureReal_mono (h₂ :=
    measure_ne_top (fixedWidthMatrixGaussianMeasure A N) _)
  intro ω hω
  change fixedWidthRoundedVectorPathFrom ρ N y0 n ω ≠ 0 at hω
  change fixedWidthRoundedVectorPathFrom ρ N y0 m ω ≠ 0
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact fixedWidthRoundedVectorPathFrom_ne_zero_of_add_ne_zero
    ρ N y0 m d ω hω

/-- The paper-facing logarithmic-start absorption theorem, specialized to the
polylogarithmic rounded-state envelope and valid at every time beyond the
natural absorption buffer. -/
theorem exists_uniform_fixedWidthRoundedAbsorptionSurvival_upper_polylog_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) (p : ℝ) (hp : -1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ L : ℝ, 1 ≤ L →
        ∀ y0 : Fin N → ℝ,
          fixedWidthRoundedInitialGridRadius ρ N y0 ≤
              fixedWidthUpperGridRadius p L →
            ∀ t : ℕ, fixedWidthUpperAbsorptionBuffer C p L ≤ t →
              (fixedWidthMatrixGaussianMeasure A N).real
                  (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 t) ≤
                C * Real.exp (-c * Real.log L) := by
  obtain ⟨c, C, hc, hC, hbound⟩ :=
    exists_uniform_fixedWidthRoundedAbsorptionSurvival_log_bound hA hN hsub
  refine ⟨c, C, hc, hC, ?_⟩
  intro ρ hρ L hL y0 hstart t ht
  have hbase :=
    hbound ρ hρ (fixedWidthUpperGridRadius p L)
      (two_le_fixedWidthUpperGridRadius hp hL) y0 hstart
      (Real.log L) (Real.log_nonneg hL)
  have hmono :=
    measureReal_fixedWidthRoundedAbsorptionSurvivalSetFrom_antitone
      (A := A) (ρ := ρ) y0 ht
  exact hmono.trans (by
    simpa only [fixedWidthUpperAbsorptionBuffer] using hbase)

/-- Subtracting a natural buffer inside the post-floor perturbation subtracts
that buffer from the resulting natural observation time. -/
lemma postFloorTime_sub_natCast
    (μ σ a : ℝ) (L v : ℕ → ℝ) (u : ℕ → ℕ) (r : ℕ) :
    postFloorTime μ σ a L (fun s ↦ v s - (u s : ℝ)) r =
      postFloorTime μ σ a L v r - u r := by
  unfold postFloorTime
  rw [show (canonicalTime μ σ a L 0 r : ℝ) +
      (v r - (u r : ℝ)) =
      ((canonicalTime μ σ a L 0 r : ℝ) + v r) - (u r : ℝ) by ring]
  exact Nat.floor_sub_natCast _ _

/-- Subtracting a natural-valued negligible buffer preserves a negligible
real time perturbation. -/
lemma tendsto_perturbation_sub_natCast_div_sqrt
    {L v : ℕ → ℝ} {u : ℕ → ℕ}
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r))
      atTop (nhds 0))
    (hu : Tendsto (fun r ↦ (u r : ℝ) / Real.sqrt (L r))
      atTop (nhds 0)) :
    Tendsto
      (fun r ↦ (v r - (u r : ℝ)) / Real.sqrt (L r))
      atTop (nhds 0) := by
  simpa only [sub_div, sub_zero] using hv.sub hu

/-- Eventually the backward-shifted post-floor time plus its natural buffer
is exactly the original post-floor observation time. -/
lemma eventually_postFloorTime_sub_natCast_add
    {μ σ a : ℝ} (hμ : 0 < μ)
    {L v : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (u : ℕ → ℕ)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r))
      atTop (nhds 0))
    (hu : Tendsto (fun r ↦ (u r : ℝ) / Real.sqrt (L r))
      atTop (nhds 0)) :
    ∀ᶠ r in atTop,
      postFloorTime μ σ a L (fun s ↦ v s - (u s : ℝ)) r + u r =
        postFloorTime μ σ a L v r := by
  have hshift :=
    tendsto_perturbation_sub_natCast_div_sqrt hv hu
  have htop :=
    tendsto_postFloorTime_atTop (σ := σ) (a := a) hμ hL hshift
  filter_upwards [htop.eventually_gt_atTop 0] with r hr
  rw [postFloorTime_sub_natCast] at hr ⊢
  omega

/-- A post-floor entrance horizon shifted backward by a negligible natural
buffer still lies eventually inside every sufficiently large linear coupling
horizon. -/
lemma eventually_postFloorTime_sub_natCast_le_fixedWidthCouplingHorizon
    {L v : ℕ → ℝ} {u : ℕ → ℕ} {μ σ a C0 : ℝ}
    (hμ : 0 < μ) (hC0 : 1 / μ < C0)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r))
      atTop (nhds 0))
    (hu : Tendsto (fun r ↦ (u r : ℝ) / Real.sqrt (L r))
      atTop (nhds 0)) :
    ∀ᶠ r in atTop,
      postFloorTime μ σ a L (fun s ↦ v s - (u s : ℝ)) r ≤
        fixedWidthCouplingHorizon C0 (L r) := by
  exact eventually_postFloorTime_le_fixedWidthCouplingHorizon hμ hC0 hL
    (tendsto_perturbation_sub_natCast_div_sqrt hv hu)

/-- Abstract upper-limit consequence of the restart sandwich: a convergent
unrounded nonentrance profile together with vanishing coupling and fresh-start
remainders forces rounded survival eventually below the profile plus any
positive error. -/
lemma eventually_measureReal_fixedWidthRoundedSurvival_le_add_of_entrance_coupling_absorption
    (A : ℝ) (N : ℕ) (x0 : Fin N → ℝ)
    (ρ ε d K a : ℕ → ℝ) (T H u : ℕ → ℕ) (q : ℝ)
    (hρ : ∀ r, 0 < ρ r)
    (hentry : Tendsto
      (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real
        {ω | (H r : WithTop ℕ) <
          fixedWidthUnroundedVectorEntranceTime N x0 (ε r) ω})
      atTop (nhds q))
    (hbad : Tendsto
      (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthCouplingErrorBadSet
          (ρ r) N x0 (T r) (d r)))
      atTop (nhds 0))
    (hremainder : Tendsto a atTop (nhds 0))
    (hHT : ∀ᶠ r in atTop, H r ≤ T r)
    (hthreshold : ∀ᶠ r in atTop, d r + ε r ≤ K r * ρ r)
    (ha : ∀ᶠ r in atTop, 0 ≤ a r)
    (hsurvival : ∀ᶠ r in atTop, ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius (ρ r) N x ≤ K r →
        ∀ t : ℕ, u r ≤ t →
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom
                (ρ r) N x t) ≤ a r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in atTop,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedAbsorptionSurvivalSetFrom
            (ρ r) N (Qρ (ρ r) x0) (H r + u r)) ≤
        q + δ := by
  have hsum :
      Tendsto
        (fun r ↦
          (fixedWidthMatrixGaussianMeasure A N).real
              {ω | (H r : WithTop ℕ) <
                fixedWidthUnroundedVectorEntranceTime N x0 (ε r) ω} +
            (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthCouplingErrorBadSet
                (ρ r) N x0 (T r) (d r)) +
            a r)
        atTop (nhds q) := by
    simpa using (hentry.add hbad).add hremainder
  have hsumUpper :
      ∀ᶠ r in atTop,
        (fixedWidthMatrixGaussianMeasure A N).real
              {ω | (H r : WithTop ℕ) <
                fixedWidthUnroundedVectorEntranceTime N x0 (ε r) ω} +
            (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthCouplingErrorBadSet
                (ρ r) N x0 (T r) (d r)) +
            a r < q + δ :=
    (tendsto_order.1 hsum).2 (q + δ) (by linarith)
  filter_upwards [hsumUpper, hHT, hthreshold, ha, hsurvival]
    with r hsumR hHTR hthresholdR haR hsurvivalR
  exact
    (measureReal_fixedWidthRoundedSurvival_le_unroundedNonentrance_add_bad_add
      (A := A) (ρ := ρ r) (a := a r) (N := N) (x0 := x0)
      (hρ r) (T r) (H r) (u r) (ε r) (d r) (K r)
      hHTR hthresholdR haR hsurvivalR).trans hsumR.le

/-- Concrete upper fixed-width cutoff profile on the paper's exponential mesh
scale: rounded survival at the post-floor observation time is eventually at
most the limiting Gaussian tail, up to any positive error. -/
lemma eventually_measureReal_fixedWidthRoundedSurvival_postFloorTime_le_cdf_add
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (L v : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ r in atTop,
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedAbsorptionSurvivalSetFrom
            (Real.exp (-L r)) N (Qρ (Real.exp (-L r)) x0)
            (postFloorTime
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N)
              (fixedWidthStdDev A N) a L v r)) ≤
        ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal 0 1) (-a) + δ := by
  let μ :=
    ∫ x, fixedWidthIncrementProcess A N 0 x
      ∂fixedWidthGaussianMeasure N
  let C0 := 2 / μ
  have hμ : 0 < μ := by
    exact integral_fixedWidthIncrementProcess_zero_pos_of_subcritical hsub
  have hC0pos : 0 < C0 := by
    dsimp [C0]
    positivity
  have hC0 : 1 / μ < C0 := by
    dsimp [C0]
    rw [div_lt_div_iff_of_pos_right hμ]
    norm_num
  obtain ⟨p, hp, hbadScale⟩ :=
    exists_pos_tendsto_measureReal_fixedWidthCouplingErrorBadSet_zero
      hA hN hsub x0 C0 hC0pos.le
  have hpneg : -1 ≤ p := by linarith
  obtain ⟨c, C, hc, hC, hsurvivalScale⟩ :=
    exists_uniform_fixedWidthRoundedAbsorptionSurvival_upper_polylog_bound
      hA hN hsub p hpneg
  let ρ : ℕ → ℝ := fun r ↦ Real.exp (-L r)
  let d : ℕ → ℝ := fun r ↦
    Real.exp (-L r) *
      Real.exp (fixedWidthSubproductLogThreshold p (L r))
  let ε : ℕ → ℝ := fun r ↦
    Real.exp (-L r) *
      Real.exp (fixedWidthSubproductLogThreshold (p + 1) (L r))
  let K : ℕ → ℝ := fun r ↦ fixedWidthUpperGridRadius p (L r)
  let u : ℕ → ℕ := fun r ↦ fixedWidthUpperAbsorptionBuffer C p (L r)
  let T : ℕ → ℕ := fun r ↦ fixedWidthCouplingHorizon C0 (L r)
  let H : ℕ → ℕ := fun r ↦
    postFloorTime μ (fixedWidthStdDev A N) a L
      (fun s ↦ v s - (u s : ℝ)) r
  let remainder : ℕ → ℝ := fun r ↦
    C * Real.exp (-c * Real.log (L r))
  have hu :
      Tendsto (fun r ↦ (u r : ℝ) / Real.sqrt (L r))
        atTop (nhds 0) := by
    exact tendsto_fixedWidthUpperAbsorptionBuffer_div_sqrt
      C p hC.le hpneg L hL
  have hshift :
      Tendsto
        (fun r ↦ (v r - (u r : ℝ)) / Real.sqrt (L r))
        atTop (nhds 0) :=
    tendsto_perturbation_sub_natCast_div_sqrt hv hu
  have hentry :
      Tendsto
        (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real
          {ω | (H r : WithTop ℕ) <
            fixedWidthUnroundedVectorEntranceTime N x0 (ε r) ω})
        atTop (nhds (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
    exact tendsto_measureReal_fixedWidthUnroundedVectorEntranceTime_gt_postFloorTime
      hA hN hsub x0 hx0 L ε
      (fun r ↦ v r - (u r : ℝ)) a
      (fun r ↦ mul_pos (Real.exp_pos _) (Real.exp_pos _))
      hL hshift
      (tendsto_fixedWidthPolylogEntranceLevel
        (gaussianEuclideanNorm N x0) (p + 1) hx0 L hL)
  have hbad :
      Tendsto
        (fun r ↦ (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet
            (ρ r) N x0 (T r) (d r)))
        atTop (nhds 0) := by
    change Tendsto
      ((fun l : ℝ ↦
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet
            (Real.exp (-l)) N x0 (fixedWidthCouplingHorizon C0 l)
            (Real.exp (-l) *
              Real.exp (fixedWidthSubproductLogThreshold p l)))) ∘ L)
      atTop (nhds 0)
    exact hbadScale.comp hL
  have hremainder : Tendsto remainder atTop (nhds 0) := by
    exact tendsto_fixedWidthUpperAbsorptionRemainder_zero C c hc L hL
  have hHT : ∀ᶠ r in atTop, H r ≤ T r := by
    exact
      eventually_postFloorTime_sub_natCast_le_fixedWidthCouplingHorizon
        hμ hC0 hL hv hu
  have hthreshold : ∀ᶠ r in atTop, d r + ε r ≤ K r * ρ r := by
    filter_upwards [hL.eventually_ge_atTop 1] with r hLr
    exact fixedWidthUpperThreshold_sum_le hLr
  have ha : ∀ᶠ r in atTop, 0 ≤ remainder r := by
    filter_upwards with r
    positivity
  have hsurvival : ∀ᶠ r in atTop, ∀ x : Fin N → ℝ,
      fixedWidthRoundedInitialGridRadius (ρ r) N x ≤ K r →
        ∀ t : ℕ, u r ≤ t →
          (fixedWidthMatrixGaussianMeasure A N).real
              (fixedWidthRoundedAbsorptionSurvivalSetFrom
                (ρ r) N x t) ≤ remainder r := by
    filter_upwards [hL.eventually_ge_atTop 1] with r hLr
    exact hsurvivalScale (ρ r) (Real.exp_pos _) (L r) hLr
  have hupper :=
    eventually_measureReal_fixedWidthRoundedSurvival_le_add_of_entrance_coupling_absorption
      A N x0 ρ ε d K remainder T H u
      (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) (-a))
      (fun r ↦ Real.exp_pos _) hentry hbad hremainder hHT
      hthreshold ha hsurvival hδ
  have htime :
      ∀ᶠ r in atTop, H r + u r =
        postFloorTime μ (fixedWidthStdDev A N) a L v r := by
    exact eventually_postFloorTime_sub_natCast_add hμ hL u hv hu
  filter_upwards [hupper, htime] with r hupperR htimeR
  simpa only [ρ, μ, htimeR] using hupperR

/-- Exact rounded fixed-width survival profile at the paper's post-floor
cutoff time. -/
theorem tendsto_measureReal_fixedWidthRoundedSurvival_postFloorTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (L v : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0)) :
    Tendsto
      (fun r ↦
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedAbsorptionSurvivalSetFrom
            (Real.exp (-L r)) N (Qρ (Real.exp (-L r)) x0)
            (postFloorTime
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N)
              (fixedWidthStdDev A N) a L v r)))
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    let δ := (ProbabilityTheory.cdf
      (ProbabilityTheory.gaussianReal 0 1) (-a) - b) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hlower :=
      eventually_cdf_sub_le_measureReal_fixedWidthRoundedSurvival_postFloorTime
        hA hN hsub x0 hx0 L v a hL hv hδ
    filter_upwards [hlower] with r hlowerR
    dsimp [δ] at hlowerR
    linarith
  · intro b hb
    let δ := (b - ProbabilityTheory.cdf
      (ProbabilityTheory.gaussianReal 0 1) (-a)) / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    have hupper :=
      eventually_measureReal_fixedWidthRoundedSurvival_postFloorTime_le_cdf_add
        hA hN hsub x0 hx0 L v a hL hv hδ
    filter_upwards [hupper] with r hupperR
    dsimp [δ] at hupperR
    linarith

/-- Updating a probability law with an independent Gaussian matrix is exactly
measure-kernel composition by the rounded transition kernel. -/
lemma map_roundedPstep_prod_eq_comp
    (A ρ : ℝ) (N : ℕ) (ν : Measure (Fin N → ℝ))
    [IsProbabilityMeasure ν] :
    Measure.map (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) ↦
      roundedPstep ρ N p.1 p.2) (ν.prod (gaussianMat A N)) =
      (roundedPkernel A ρ N) ∘ₘ ν := by
  unfold roundedPkernel
  rw [← Measure.map_comp]
  · rw [← Measure.compProd_const, Measure.compProd_eq_comp_prod]
    rfl
  · exact measurable_roundedPstep ρ N

/-- The rounded state at time `n` and the matrix innovation used for the next
step have the product of the state marginal and the Gaussian matrix law. -/
lemma map_prod_fixedWidthRoundedVectorPathFrom_eval
    (A ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measure.map
        (fun ω : fixedWidthMatrixSampleSpace N ↦
          (fixedWidthRoundedVectorPathFrom ρ N y0 n ω, ω n))
        (fixedWidthMatrixGaussianMeasure A N) =
      (Measure.map (fixedWidthRoundedVectorPathFrom ρ N y0 n)
          (fixedWidthMatrixGaussianMeasure A N)).prod
        (gaussianMat A N) := by
  let project :
      (Fin N → ℝ) × fixedWidthMatrixSampleSpace N →
        (Fin N → ℝ) × (Fin N → Fin N → ℝ) :=
    fun p ↦ (p.1, p.2 0)
  have hproject : Measurable project :=
    measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
  have hproject_eq :
      project = Prod.map id (Function.eval 0) := by
    funext p
    rfl
  have hfactor :=
    congrArg (Measure.map project)
      (map_prod_fixedWidthRoundedVectorPathFrom_shift A ρ N y0 n)
  rw [Measure.map_map hproject
      ((measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n).prodMk
        (measurable_fixedWidthMatrixShift N n)),
    hproject_eq,
    ← Measure.map_prod_map _ _
      measurable_id (measurable_pi_apply (0 : ℕ))] at hfactor
  have heval :
      Measure.map (Function.eval 0)
          (fixedWidthMatrixGaussianMeasure A N) =
        gaussianMat A N :=
    (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ gaussianMat A N) 0).map_eq
  rw [heval, Measure.map_id] at hfactor
  have hleft :
      Prod.map id (Function.eval 0) ∘
          (fun a : fixedWidthMatrixSampleSpace N ↦
            (fixedWidthRoundedVectorPathFrom ρ N y0 n a,
              fixedWidthMatrixShift N n a)) =
        fun ω ↦ (fixedWidthRoundedVectorPathFrom ρ N y0 n ω, ω n) := by
    funext ω
    simp [fixedWidthMatrixShift]
  rw [hleft] at hfactor
  exact hfactor

/-- The canonical iid-matrix construction of the exact-start rounded chain has
the same time-`n` law as the `n`th power of its transition kernel. -/
theorem map_fixedWidthRoundedVectorPathFrom
    (A ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measure.map (fixedWidthRoundedVectorPathFrom ρ N y0 n)
        (fixedWidthMatrixGaussianMeasure A N) =
      ((roundedPkernel A ρ N) ^ n) y0 := by
  induction n with
  | zero =>
      rw [pow_zero]
      change Measure.map (fun _ : fixedWidthMatrixSampleSpace N ↦ y0)
        (fixedWidthMatrixGaussianMeasure A N) = Kernel.id y0
      rw [Kernel.id_apply, Measure.map_const]
      simp
  | succ n ih =>
      letI : IsProbabilityMeasure
          (Measure.map (fixedWidthRoundedVectorPathFrom ρ N y0 n)
            (fixedWidthMatrixGaussianMeasure A N)) :=
        Measure.isProbabilityMeasure_map
          (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n).aemeasurable
      rw [pow_succ']
      change Measure.map
          (fixedWidthRoundedVectorPathFrom ρ N y0 (n + 1))
          (fixedWidthMatrixGaussianMeasure A N) =
        ((roundedPkernel A ρ N) ∘ₖ
          ((roundedPkernel A ρ N) ^ n)) y0
      rw [Kernel.comp_apply]
      rw [← ih]
      rw [← map_roundedPstep_prod_eq_comp]
      rw [← map_prod_fixedWidthRoundedVectorPathFrom_eval]
      rw [Measure.map_map]
      · rfl
      · exact measurable_roundedPstep ρ N
      · exact (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n).prodMk
          (measurable_pi_apply n)

/-- The rounded-kernel total-variation distance from the absorbing origin is
exactly the canonical iid-matrix survival probability. -/
lemma tvDist_roundedPkernel_pow_eq_measureReal_fixedWidthRoundedSurvival
    (A ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    tvDist (((roundedPkernel A ρ N) ^ n) y0)
        (Measure.dirac (0 : Fin N → ℝ)) =
      (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 n) := by
  rw [tvDist_roundedPkernel_pow_dirac]
  change ((((roundedPkernel A ρ N) ^ n) y0)
      ({(0 : Fin N → ℝ)}ᶜ)).toReal =
    ((fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthRoundedAbsorptionSurvivalSetFrom ρ N y0 n)).toReal
  congr 1
  rw [← map_fixedWidthRoundedVectorPathFrom A ρ N y0 n,
    Measure.map_apply
      (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n)
      (measurableSet_singleton (0 : Fin N → ℝ)).compl]
  rfl

/-- Paper-facing fixed-width total-variation profile for the rounded vector
chain on the exponential mesh scale. -/
theorem tendsto_tvDist_roundedPkernel_postFloorTime
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (L v : ℕ → ℝ) (a : ℝ)
    (hL : Tendsto L atTop atTop)
    (hv : Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0)) :
    Tendsto
      (fun r ↦
        tvDist
          (((roundedPkernel A (Real.exp (-L r)) N) ^
            (postFloorTime
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N)
              (fixedWidthStdDev A N) a L v r))
            (Qρ (Real.exp (-L r)) x0))
          (Measure.dirac (0 : Fin N → ℝ)))
      atTop (nhds (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  have hsurvival :=
    tendsto_measureReal_fixedWidthRoundedSurvival_postFloorTime
      hA hN hsub x0 hx0 L v a hL hv
  refine hsurvival.congr' ?_
  filter_upwards with r
  exact
    (tvDist_roundedPkernel_pow_eq_measureReal_fixedWidthRoundedSurvival
      A (Real.exp (-L r)) N (Qρ (Real.exp (-L r)) x0)
      (postFloorTime
        (∫ x, fixedWidthIncrementProcess A N 0 x
          ∂fixedWidthGaussianMeasure N)
        (fixedWidthStdDev A N) a L v r)).symm

/-- Center of the fixed-width vanishing-mesh cutoff window. -/
noncomputable def fixedWidthCutoffTime
    (μ : ℝ) (L : ℕ → ℝ) (r : ℕ) : ℝ :=
  L r / μ

/-- Standard-deviation scale of the fixed-width vanishing-mesh cutoff
window. -/
noncomputable def fixedWidthCutoffWindow
    (μ σ : ℝ) (L : ℕ → ℝ) (r : ℕ) : ℝ :=
  (σ / (μ * Real.sqrt μ)) * Real.sqrt (L r)

/-- A positive drift turns every diverging logarithmic level into a diverging
fixed-width cutoff center. -/
lemma tendsto_fixedWidthCutoffTime_atTop
    {μ : ℝ} (hμ : 0 < μ) {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fixedWidthCutoffTime μ L) atTop atTop := by
  change Tendsto (fun r ↦ L r / μ) atTop atTop
  simpa only [div_eq_mul_inv, mul_comm] using
    hL.const_mul_atTop (inv_pos.mpr hμ)

/-- The fixed-width square-root window is positive throughout the asymptotic
regime when its drift and standard deviation are positive. -/
lemma eventually_fixedWidthCutoffWindow_pos
    {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    ∀ᶠ r in atTop, 0 < fixedWidthCutoffWindow μ σ L r := by
  filter_upwards [hL.eventually_gt_atTop 0] with r hr
  unfold fixedWidthCutoffWindow
  exact mul_pos (div_pos hσ (mul_pos hμ (Real.sqrt_pos.2 hμ)))
    (Real.sqrt_pos.2 hr)

/-- The fixed-width square-root window is negligible compared with its linear
cutoff center. -/
lemma isLittleO_fixedWidthCutoffWindow
    {μ σ : ℝ} (hμ : 0 < μ)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Asymptotics.IsLittleO atTop
      (fixedWidthCutoffWindow μ σ L)
      (fixedWidthCutoffTime μ L) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [hL.eventually_gt_atTop 0] with r hr
    intro hzero
    have : L r = 0 := (div_eq_zero_iff.mp hzero).resolve_right hμ.ne'
    exact (ne_of_gt hr this).elim
  · have hsqrt : Tendsto (fun r ↦ Real.sqrt (L r)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hL
    have hratio : Tendsto (fun r ↦ Real.sqrt (L r) / L r)
        atTop (nhds 0) := by
      refine (tendsto_inv_atTop_zero.comp hsqrt).congr' ?_
      filter_upwards [hL.eventually_gt_atTop 0] with r hr
      exact Real.sqrt_div_self.symm
    have hscaled : Tendsto
        (fun r ↦ (σ / (μ * Real.sqrt μ) * μ) *
          (Real.sqrt (L r) / L r)) atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hratio
    refine hscaled.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with r hr
    unfold fixedWidthCutoffWindow fixedWidthCutoffTime
    field_simp [hμ.ne', ne_of_gt hr]

/-- The Gaussian fixed-width center and window satisfy all admissibility
conditions in the paper's cutoff definition. -/
lemma isCutoffWindow_fixedWidth
    {μ σ : ℝ} (hμ : 0 < μ) (hσ : 0 < σ)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    IsCutoffWindow (fixedWidthCutoffTime μ L)
      (fixedWidthCutoffWindow μ σ L) := by
  exact ⟨tendsto_fixedWidthCutoffTime_atTop hμ hL,
    eventually_fixedWidthCutoffWindow_pos hμ hσ hL,
    isLittleO_fixedWidthCutoffWindow hμ hL⟩

/-- The common cutoff API's floored center-plus-window time is exactly the
zero-perturbation post-floor time used by the Gaussian profile. -/
lemma natFloor_fixedWidthCutoffTime_add_mul_window
    (μ σ a : ℝ) (L : ℕ → ℝ) (r : ℕ) :
    ⌊fixedWidthCutoffTime μ L r +
        a * fixedWidthCutoffWindow μ σ L r⌋₊ =
      postFloorTime μ σ a L 0 r := by
  unfold fixedWidthCutoffTime fixedWidthCutoffWindow
  unfold postFloorTime canonicalTime canonicalTimeArgument
  simp only [Pi.zero_apply, add_zero, Nat.floor_natCast]
  congr 1
  ring

/-- The fixed-width rounded vector chains on every diverging exponential mesh
scale exhibit total-variation cutoff at the Gaussian center and window. -/
theorem hasCutoff_roundedPkernel_fixedWidth
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    HasCutoff
      (fun r t ↦
        tvDist
          (((roundedPkernel A (Real.exp (-L r)) N) ^ t)
            (Qρ (Real.exp (-L r)) x0))
          (Measure.dirac (0 : Fin N → ℝ)))
      (fixedWidthCutoffTime
        (∫ x, fixedWidthIncrementProcess A N 0 x
          ∂fixedWidthGaussianMeasure N) L)
      (fixedWidthCutoffWindow
        (∫ x, fixedWidthIncrementProcess A N 0 x
          ∂fixedWidthGaussianMeasure N)
        (fixedWidthStdDev A N) L) := by
  let μ :=
    ∫ x, fixedWidthIncrementProcess A N 0 x
      ∂fixedWidthGaussianMeasure N
  let σ := fixedWidthStdDev A N
  let d : ℕ → ℕ → ℝ := fun r t ↦
    tvDist
      (((roundedPkernel A (Real.exp (-L r)) N) ^ t)
        (Qρ (Real.exp (-L r)) x0))
      (Measure.dirac (0 : Fin N → ℝ))
  change HasCutoff d (fixedWidthCutoffTime μ L)
    (fixedWidthCutoffWindow μ σ L)
  have hμ : 0 < μ :=
    integral_fixedWidthIncrementProcess_zero_pos_of_subcritical hsub
  have hσ : 0 < σ := fixedWidthStdDev_pos hA hN
  rw [HasCutoff, HasCutoffLimits]
  refine ⟨isCutoffWindow_fixedWidth hμ hσ hL, ?_, ?_⟩
  · have hpoint (c : ℝ) :
        Tendsto
          (fun r ↦ d r
            ⌊fixedWidthCutoffTime μ L r -
              c * fixedWidthCutoffWindow μ σ L r⌋₊)
          atTop (nhds (ProbabilityTheory.cdf
            (ProbabilityTheory.gaussianReal 0 1) c)) := by
      have hprofile :=
        tendsto_tvDist_roundedPkernel_postFloorTime
          hA hN hsub x0 hx0 L 0 (-c) hL (by simp)
      simpa only [d, μ, σ, neg_neg,
        show ∀ r, ⌊fixedWidthCutoffTime μ L r -
              c * fixedWidthCutoffWindow μ σ L r⌋₊ =
            postFloorTime μ σ (-c) L 0 r from
          fun r ↦ by
            rw [show fixedWidthCutoffTime μ L r -
                c * fixedWidthCutoffWindow μ σ L r =
              fixedWidthCutoffTime μ L r +
                (-c) * fixedWidthCutoffWindow μ σ L r by ring]
            exact natFloor_fixedWidthCutoffTime_add_mul_window
              μ σ (-c) L r]
        using hprofile
    have hinner :
        (fun c : ℝ ↦ liminf
          (fun r ↦ d r
            ⌊fixedWidthCutoffTime μ L r -
              c * fixedWidthCutoffWindow μ σ L r⌋₊) atTop) =
          ProbabilityTheory.cdf
            (ProbabilityTheory.gaussianReal 0 1) := by
      funext c
      exact (hpoint c).liminf_eq
    rw [hinner]
    exact ProbabilityTheory.tendsto_cdf_atTop _
  · have hpoint (c : ℝ) :
        Tendsto
          (fun r ↦ d r
            ⌊fixedWidthCutoffTime μ L r +
              c * fixedWidthCutoffWindow μ σ L r⌋₊)
          atTop (nhds (ProbabilityTheory.cdf
            (ProbabilityTheory.gaussianReal 0 1) (-c))) := by
      have hprofile :=
        tendsto_tvDist_roundedPkernel_postFloorTime
          hA hN hsub x0 hx0 L 0 c hL (by simp)
      simpa only [d, μ, σ,
        show ∀ r, ⌊fixedWidthCutoffTime μ L r +
              c * fixedWidthCutoffWindow μ σ L r⌋₊ =
            postFloorTime μ σ c L 0 r from
          fun r ↦ natFloor_fixedWidthCutoffTime_add_mul_window μ σ c L r]
        using hprofile
    have hinner :
        (fun c : ℝ ↦ limsup
          (fun r ↦ d r
            ⌊fixedWidthCutoffTime μ L r +
              c * fixedWidthCutoffWindow μ σ L r⌋₊) atTop) =
          fun c ↦ ProbabilityTheory.cdf
            (ProbabilityTheory.gaussianReal 0 1) (-c) := by
      funext c
      exact (hpoint c).limsup_eq
    rw [hinner]
    exact (ProbabilityTheory.tendsto_cdf_atBot _).comp
      tendsto_neg_atTop_atBot

/-- Mixing-time consequence of the fixed-width Gaussian cutoff profile. For
every fixed `ε ∈ (0,1)`, two constant profile offsets eventually bracket the
rounded-vector mixing time, which is the precise `O_ε(window)` form used in
the manuscript. -/
theorem exists_eventually_fixedWidth_mixingTime_bounds
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1) :
    ∃ aLower aUpper : ℝ,
      ∀ᶠ r in atTop,
        ((⌊fixedWidthCutoffTime
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N) L r +
            aLower * fixedWidthCutoffWindow
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N)
              (fixedWidthStdDev A N) L r⌋₊ : ℕ) : ℕ∞) <
          mixingTime
            (dSeq (roundedPkernel A (Real.exp (-L r)) N)
              (Qρ (Real.exp (-L r)) x0)
              (Measure.dirac (0 : Fin N → ℝ)))
            ε ∧
        mixingTime
            (dSeq (roundedPkernel A (Real.exp (-L r)) N)
              (Qρ (Real.exp (-L r)) x0)
              (Measure.dirac (0 : Fin N → ℝ)))
            ε ≤
          ((⌊fixedWidthCutoffTime
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N) L r +
            aUpper * fixedWidthCutoffWindow
              (∫ x, fixedWidthIncrementProcess A N 0 x
                ∂fixedWidthGaussianMeasure N)
              (fixedWidthStdDev A N) L r⌋₊ : ℕ) : ℕ∞) := by
  let μ :=
    ∫ x, fixedWidthIncrementProcess A N 0 x
      ∂fixedWidthGaussianMeasure N
  let σ := fixedWidthStdDev A N
  have hleftLimit :
      Tendsto
        (fun a : ℝ ↦ ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal 0 1) (-a))
        atBot (nhds 1) :=
    (ProbabilityTheory.tendsto_cdf_atTop _).comp
      tendsto_neg_atBot_atTop
  have hrightLimit :
      Tendsto
        (fun a : ℝ ↦ ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal 0 1) (-a))
        atTop (nhds 0) :=
    (ProbabilityTheory.tendsto_cdf_atBot _).comp
      tendsto_neg_atTop_atBot
  obtain ⟨aLower, haLower⟩ :=
    ((tendsto_order.1 hleftLimit).1 ε hε_lt).exists
  obtain ⟨aUpper, haUpper⟩ :=
    ((tendsto_order.1 hrightLimit).2 ε hε).exists
  refine ⟨aLower, aUpper, ?_⟩
  have hlowerProfile :=
    tendsto_tvDist_roundedPkernel_postFloorTime
      hA hN hsub x0 hx0 L 0 aLower hL (by simp)
  have hupperProfile :=
    tendsto_tvDist_roundedPkernel_postFloorTime
      hA hN hsub x0 hx0 L 0 aUpper hL (by simp)
  have hlowerEventually :
      ∀ᶠ r in atTop,
        ε <
          tvDist
            (((roundedPkernel A (Real.exp (-L r)) N) ^
              ⌊fixedWidthCutoffTime μ L r +
                aLower * fixedWidthCutoffWindow μ σ L r⌋₊)
              (Qρ (Real.exp (-L r)) x0))
            (Measure.dirac (0 : Fin N → ℝ)) := by
    have h := (tendsto_order.1 hlowerProfile).1 ε haLower
    simpa only [μ, σ,
      natFloor_fixedWidthCutoffTime_add_mul_window] using h
  have hupperEventually :
      ∀ᶠ r in atTop,
        tvDist
            (((roundedPkernel A (Real.exp (-L r)) N) ^
              ⌊fixedWidthCutoffTime μ L r +
                aUpper * fixedWidthCutoffWindow μ σ L r⌋₊)
              (Qρ (Real.exp (-L r)) x0))
            (Measure.dirac (0 : Fin N → ℝ)) < ε := by
    have h := (tendsto_order.1 hupperProfile).2 ε haUpper
    simpa only [μ, σ,
      natFloor_fixedWidthCutoffTime_add_mul_window] using h
  filter_upwards [hlowerEventually, hupperEventually]
    with r hlowerR hupperR
  let d :=
    dSeq (roundedPkernel A (Real.exp (-L r)) N)
      (Qρ (Real.exp (-L r)) x0)
      (Measure.dirac (0 : Fin N → ℝ))
  let tLower := ⌊fixedWidthCutoffTime μ L r +
    aLower * fixedWidthCutoffWindow μ σ L r⌋₊
  let tUpper := ⌊fixedWidthCutoffTime μ L r +
    aUpper * fixedWidthCutoffWindow μ σ L r⌋₊
  have hlowerD : ε < d tLower := by
    simpa only [d, tLower, dSeq] using hlowerR
  have hupperD : d tUpper ≤ ε := by
    simpa only [d, tUpper, dSeq] using hupperR.le
  change (tLower : ℕ∞) < mixingTime d ε ∧
    mixingTime d ε ≤ (tUpper : ℕ∞)
  constructor
  · rw [mixingTime, lt_sInf_iff]
    refine ⟨((tLower + 1 : ℕ) : ℕ∞), ?_, ?_⟩
    · simpa only [ENat.coe_lt_coe] using Nat.lt_succ_self tLower
    · intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      have htu : tLower < u := by
        by_contra hnot
        have hut : u ≤ tLower := not_lt.mp hnot
        have hmono : d tLower ≤ d u :=
          dSeq_dirac_antitone
            (measurableSet_singleton (0 : Fin N → ℝ))
            (isAbsorbing_roundedPkernel A (Real.exp (-L r)) N)
            (Qρ (Real.exp (-L r)) x0) hut
        exact (not_le_of_gt hlowerD) (hmono.trans hu)
      exact_mod_cast (Nat.succ_le_iff.mpr htu)
  · rw [mixingTime]
    apply sInf_le
    exact ⟨tUpper, hupperD, rfl⟩

/-- Logarithmic scale associated with a positive vanishing mesh sequence. -/
noncomputable def fixedWidthLogMeshScale
    (ρ : ℕ → ℝ) (r : ℕ) : ℝ :=
  -Real.log (ρ r)

/-- Paper's logarithmic scale, including the norm of the initial state. -/
noncomputable def fixedWidthInitialLogMeshScale
    (R₀ : ℝ) (ρ : ℕ → ℝ) (r : ℕ) : ℝ :=
  Real.log (R₀ / ρ r)

/-- The manuscript's floored observation time `t_ρ(a)`, with its critical
width, drift, and `N`-only variance normalization exposed in the type. -/
noncomputable def fixedWidthPaperObservationTime
    (A : ℝ) (N : ℕ) (R₀ : ℝ) (ρ : ℕ → ℝ) (a : ℝ) (r : ℕ) : ℕ :=
  canonicalTime (fixedWidthGamma A N) (fixedWidthSigma N) a
    (fixedWidthInitialLogMeshScale R₀ ρ) 0 r

/-- The paper's cutoff center `L_ρ / gamma_{A,N}`. -/
noncomputable def fixedWidthPaperCutoffTime
    (A : ℝ) (N : ℕ) (R₀ : ℝ) (ρ : ℕ → ℝ) : ℕ → ℝ :=
  fixedWidthCutoffTime (fixedWidthGamma A N)
    (fixedWidthInitialLogMeshScale R₀ ρ)

/-- The paper's cutoff window
`sigma_N * gamma_{A,N}^{-3/2} * sqrt L_ρ`. -/
noncomputable def fixedWidthPaperCutoffWindow
    (A : ℝ) (N : ℕ) (R₀ : ℝ) (ρ : ℕ → ℝ) : ℕ → ℝ :=
  fixedWidthCutoffWindow (fixedWidthGamma A N) (fixedWidthSigma N)
    (fixedWidthInitialLogMeshScale R₀ ρ)

lemma natFloor_fixedWidthCutoffTime_add_mul_window_eq_canonicalTime
    (μ σ a : ℝ) (L : ℕ → ℝ) (r : ℕ) :
    ⌊fixedWidthCutoffTime μ L r +
        a * fixedWidthCutoffWindow μ σ L r⌋₊ =
      canonicalTime μ σ a L 0 r := by
  unfold fixedWidthCutoffTime fixedWidthCutoffWindow
  unfold canonicalTime canonicalTimeArgument
  simp only [Pi.zero_apply, add_zero]
  congr 1
  ring

/-- The paper's initial-state logarithmic scale differs from the bare mesh
scale by the constant `log R₀`. -/
lemma fixedWidthInitialLogMeshScale_eq
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    {ρ : ℕ → ℝ} (hρ : ∀ r, 0 < ρ r) (r : ℕ) :
    fixedWidthInitialLogMeshScale R₀ ρ r =
      fixedWidthLogMeshScale ρ r + Real.log R₀ := by
  rw [fixedWidthInitialLogMeshScale, fixedWidthLogMeshScale,
    Real.log_div hR₀.ne' (hρ r).ne']
  ring

/-- A positive mesh tending to zero has a diverging negative-log scale. -/
lemma tendsto_fixedWidthLogMeshScale_atTop
    {ρ : ℕ → ℝ} (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto (fixedWidthLogMeshScale ρ) atTop atTop := by
  change Tendsto ((fun x : ℝ ↦ -Real.log x) ∘ ρ) atTop atTop
  exact
    (Filter.tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero).comp hρ

/-- Including a fixed positive initial norm preserves divergence of the
negative-log mesh scale. -/
lemma tendsto_fixedWidthInitialLogMeshScale_atTop
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    {ρ : ℕ → ℝ} (hρpos : ∀ r, 0 < ρ r)
    (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto (fixedWidthInitialLogMeshScale R₀ ρ) atTop atTop := by
  have hL : Tendsto (fixedWidthLogMeshScale ρ) atTop atTop :=
    tendsto_fixedWidthLogMeshScale_atTop hρ
  refine (tendsto_atTop_add_const_right atTop (Real.log R₀) hL).congr' ?_
  exact Eventually.of_forall fun r ↦
    (fixedWidthInitialLogMeshScale_eq hR₀ hρpos r).symm

/-- Including the fixed initial norm does not change the logarithmic scale to
first order. -/
lemma tendsto_fixedWidthInitialLogMeshScale_div
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    {ρ : ℕ → ℝ} (hρpos : ∀ r, 0 < ρ r)
    (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
      (fun r ↦ fixedWidthInitialLogMeshScale R₀ ρ r /
        fixedWidthLogMeshScale ρ r)
      atTop (nhds 1) := by
  have hL : Tendsto (fixedWidthLogMeshScale ρ) atTop atTop :=
    tendsto_fixedWidthLogMeshScale_atTop hρ
  have hconst :
      Tendsto (fun r ↦ Real.log R₀ / fixedWidthLogMeshScale ρ r)
        atTop (nhds 0) :=
    hL.const_div_atTop (Real.log R₀)
  have hlim :
      Tendsto
        (fun r ↦ 1 + Real.log R₀ / fixedWidthLogMeshScale ρ r)
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hconst
  refine hlim.congr' ?_
  filter_upwards [hL.eventually_ne_atTop 0] with r hLne
  rw [fixedWidthInitialLogMeshScale_eq hR₀ hρpos]
  field_simp

/-- Including the fixed initial norm does not change the square-root window
scale to first order. -/
lemma tendsto_sqrt_fixedWidthInitialLogMeshScale_div_sqrt
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    {ρ : ℕ → ℝ} (hρpos : ∀ r, 0 < ρ r)
    (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
      (fun r ↦
        Real.sqrt (fixedWidthInitialLogMeshScale R₀ ρ r) /
          Real.sqrt (fixedWidthLogMeshScale ρ r))
      atTop (nhds 1) := by
  have hratio :=
    tendsto_fixedWidthInitialLogMeshScale_div hR₀ hρpos hρ
  have hsqrt :
      Tendsto
        (fun r ↦ Real.sqrt
          (fixedWidthInitialLogMeshScale R₀ ρ r /
            fixedWidthLogMeshScale ρ r))
        atTop (nhds 1) := by
    change Tendsto
      ((fun x : ℝ ↦ Real.sqrt x) ∘
        (fun r ↦ fixedWidthInitialLogMeshScale R₀ ρ r /
          fixedWidthLogMeshScale ρ r))
      atTop (nhds 1)
    simpa only [Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto 1).comp hratio
  have hL : Tendsto (fixedWidthLogMeshScale ρ) atTop atTop :=
    tendsto_fixedWidthLogMeshScale_atTop hρ
  have hLR₀ :
      Tendsto (fixedWidthInitialLogMeshScale R₀ ρ) atTop atTop :=
    tendsto_fixedWidthInitialLogMeshScale_atTop hR₀ hρpos hρ
  refine hsqrt.congr' ?_
  filter_upwards [hL.eventually_ge_atTop 0, hLR₀.eventually_ge_atTop 0]
    with r hLnonneg hLR₀nonneg
  rw [Real.sqrt_div hLR₀nonneg]

/-- Post-floor perturbation that changes the bare mesh-scale observation time
into the manuscript's exact initial-state logarithmic observation time. -/
noncomputable def fixedWidthInitialScalePerturbation
    (μ σ a R₀ : ℝ) (ρ : ℕ → ℝ) (r : ℕ) : ℝ :=
  canonicalTimeArgument μ σ a
      (fixedWidthInitialLogMeshScale R₀ ρ) 0 r -
    (canonicalTime μ σ a (fixedWidthLogMeshScale ρ) 0 r : ℝ)

/-- Adding the initial-scale correction after flooring and flooring again is
exactly the manuscript's natural-floor observation time. -/
lemma postFloorTime_initialScalePerturbation
    (μ σ a R₀ : ℝ) (ρ : ℕ → ℝ) (r : ℕ) :
    postFloorTime μ σ a (fixedWidthLogMeshScale ρ)
        (fixedWidthInitialScalePerturbation μ σ a R₀ ρ) r =
      canonicalTime μ σ a
        (fixedWidthInitialLogMeshScale R₀ ρ) 0 r := by
  unfold postFloorTime fixedWidthInitialScalePerturbation canonicalTime
  congr 1
  ring

/-- The exact correction from the bare mesh scale to the manuscript's
initial-state scale is negligible compared with the square-root window. -/
lemma tendsto_fixedWidthInitialScalePerturbation_div_sqrt
    {μ : ℝ} (hμ : 0 < μ) (σ a : ℝ)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    {ρ : ℕ → ℝ} (hρpos : ∀ r, 0 < ρ r)
    (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto
      (fun r ↦
        fixedWidthInitialScalePerturbation μ σ a R₀ ρ r /
          Real.sqrt (fixedWidthLogMeshScale ρ r))
      atTop (nhds 0) := by
  let L := fixedWidthLogMeshScale ρ
  let L₀ := fixedWidthInitialLogMeshScale R₀ ρ
  have hL : Tendsto L atTop atTop :=
    tendsto_fixedWidthLogMeshScale_atTop hρ
  have hsqrtL : Tendsto (fun r ↦ Real.sqrt (L r)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  have hscale :
      Tendsto (fun r ↦ (L₀ r - L r) / Real.sqrt (L r))
        atTop (nhds 0) := by
    have hconst := hsqrtL.const_div_atTop (Real.log R₀)
    refine hconst.congr' ?_
    exact Eventually.of_forall fun r ↦ by
      change Real.log R₀ / Real.sqrt (L r) =
        (L₀ r - L r) / Real.sqrt (L r)
      rw [show L₀ r = L r + Real.log R₀ by
        exact fixedWidthInitialLogMeshScale_eq hR₀ hρpos r]
      ring
  have hsqrtRatio :
      Tendsto (fun r ↦ Real.sqrt (L₀ r) / Real.sqrt (L r))
        atTop (nhds 1) := by
    exact tendsto_sqrt_fixedWidthInitialLogMeshScale_div_sqrt
      hR₀ hρpos hρ
  have hwindow :
      Tendsto
        (fun r ↦ Real.sqrt (L₀ r) / Real.sqrt (L r) - 1)
        atTop (nhds 0) := by
    simpa using hsqrtRatio.sub_const 1
  have hcomb :
      Tendsto
        (fun r ↦
          (1 / μ) * ((L₀ r - L r) / Real.sqrt (L r)) +
            (a * σ / (μ * Real.sqrt μ)) *
              (Real.sqrt (L₀ r) / Real.sqrt (L r) - 1))
        atTop (nhds 0) := by
    simpa using
      (hscale.const_mul (1 / μ)).add
        (hwindow.const_mul (a * σ / (μ * Real.sqrt μ)))
  have harg :
      Tendsto
        (fun r ↦
          (canonicalTimeArgument μ σ a L₀ 0 r -
            canonicalTimeArgument μ σ a L 0 r) /
              Real.sqrt (L r))
        atTop (nhds 0) := by
    refine hcomb.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with r hLpos
    unfold canonicalTimeArgument
    simp only [Pi.zero_apply, add_zero]
    have hsqrtLne : Real.sqrt (L r) ≠ 0 :=
      (Real.sqrt_pos.2 hLpos).ne'
    have hμne : μ ≠ 0 := hμ.ne'
    field_simp
    ring
  have hq :
      Tendsto (fun r ↦ (0 : ℕ → ℝ) r / Real.sqrt (L r))
        atTop (nhds 0) := by
    simp
  have hargument :=
    tendsto_canonicalTimeArgument_atTop
      (σ := σ) (a := a) hμ hL hq
  have hargument_nonneg :
      ∀ᶠ r in atTop, 0 ≤ canonicalTimeArgument μ σ a L 0 r :=
    (hargument.eventually_gt_atTop 0).mono fun _ h ↦ h.le
  have hfloorNeg :
      Tendsto
        (fun r ↦
          (canonicalTimeArgument μ σ a L 0 r -
            (canonicalTime μ σ a L 0 r : ℝ)) /
              Real.sqrt (L r))
        atTop (nhds 0) := by
    have hfloorRaw :=
      tendsto_natFloor_sub_div hargument_nonneg hsqrtL
    have hfloor :
        Tendsto
          (fun r ↦
            ((canonicalTime μ σ a L 0 r : ℝ) -
              canonicalTimeArgument μ σ a L 0 r) / Real.sqrt (L r))
          atTop (nhds 0) := by
      simpa only [canonicalTime] using hfloorRaw
    have hneg :
        Tendsto
          (fun r ↦
            -(((canonicalTime μ σ a L 0 r : ℝ) -
              canonicalTimeArgument μ σ a L 0 r) / Real.sqrt (L r)))
          atTop (nhds 0) := by
      simpa only [neg_zero] using hfloor.neg
    refine hneg.congr' ?_
    exact Eventually.of_forall fun r ↦ by ring
  have hsum :
      Tendsto
        (fun r ↦
          (canonicalTimeArgument μ σ a L₀ 0 r -
            canonicalTimeArgument μ σ a L 0 r) / Real.sqrt (L r) +
          (canonicalTimeArgument μ σ a L 0 r -
            (canonicalTime μ σ a L 0 r : ℝ)) / Real.sqrt (L r))
        atTop (nhds 0) := by
    simpa only [zero_add] using harg.add hfloorNeg
  refine hsum.congr' ?_
  exact Eventually.of_forall fun r ↦ by
    change
      ((canonicalTimeArgument μ σ a L₀ 0 r -
          canonicalTimeArgument μ σ a L 0 r) / Real.sqrt (L r) +
        (canonicalTimeArgument μ σ a L 0 r -
          (canonicalTime μ σ a L 0 r : ℝ)) / Real.sqrt (L r)) =
        fixedWidthInitialScalePerturbation μ σ a R₀ ρ r /
          Real.sqrt (fixedWidthLogMeshScale ρ r)
    simp only [fixedWidthInitialScalePerturbation, L₀, L]
    ring

/-- Exact paper-facing fixed-width total-variation profile. For every positive
mesh sequence `ρ →0`, the rounded vector chain observed at the manuscript's
natural-floor time with `L_ρ = log (‖x₀‖₂ / ρ)` converges to the standard
Gaussian cutoff profile. -/
theorem tendsto_tvDist_roundedPkernel_fixedWidthMesh
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
        (ProbabilityTheory.gaussianReal 0 1) (-a))) := by
  let μ :=
    ∫ x, fixedWidthIncrementProcess A N 0 x
      ∂fixedWidthGaussianMeasure N
  let σ := fixedWidthStdDev A N
  let L := fixedWidthLogMeshScale ρ
  let v := fixedWidthInitialScalePerturbation
    μ σ a (gaussianEuclideanNorm N x0) ρ
  have hμ : 0 < μ :=
    integral_fixedWidthIncrementProcess_zero_pos_of_subcritical hsub
  have hL : Tendsto L atTop atTop :=
    tendsto_fixedWidthLogMeshScale_atTop hρ
  have hv :
      Tendsto (fun r ↦ v r / Real.sqrt (L r)) atTop (nhds 0) := by
    exact tendsto_fixedWidthInitialScalePerturbation_div_sqrt
      hμ σ a hx0 hρpos hρ
  have hprofile :=
    tendsto_tvDist_roundedPkernel_postFloorTime
      hA hN hsub x0 hx0 L v a hL hv
  refine hprofile.congr' ?_
  filter_upwards with r
  have hmesh : Real.exp (-L r) = ρ r := by
    dsimp [L, fixedWidthLogMeshScale]
    rw [neg_neg, Real.exp_log (hρpos r)]
  have htime :
      postFloorTime μ σ a L v r =
        canonicalTime μ σ a
          (fixedWidthInitialLogMeshScale
            (gaussianEuclideanNorm N x0) ρ) 0 r := by
    exact postFloorTime_initialScalePerturbation
      μ σ a (gaussianEuclideanNorm N x0) ρ r
  simp only [μ, σ, hmesh, htime]

/-- Compatibility wrapper giving cutoff on the same arbitrary positive mesh
sequence and the same initial-state logarithmic scale as the manuscript. -/
theorem hasCutoff_roundedPkernel_fixedWidthMesh
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (ρ : ℕ → ℝ) (hρpos : ∀ r, 0 < ρ r)
    (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0))) :
    HasCutoff
      (fun r t ↦
        tvDist
          (((roundedPkernel A (ρ r) N) ^ t) (Qρ (ρ r) x0))
          (Measure.dirac (0 : Fin N → ℝ)))
      (fixedWidthCutoffTime
        (∫ x, fixedWidthIncrementProcess A N 0 x
          ∂fixedWidthGaussianMeasure N)
        (fixedWidthInitialLogMeshScale
          (gaussianEuclideanNorm N x0) ρ))
      (fixedWidthCutoffWindow
        (∫ x, fixedWidthIncrementProcess A N 0 x
          ∂fixedWidthGaussianMeasure N)
        (fixedWidthStdDev A N)
        (fixedWidthInitialLogMeshScale
          (gaussianEuclideanNorm N x0) ρ)) := by
  let μ :=
    ∫ x, fixedWidthIncrementProcess A N 0 x
      ∂fixedWidthGaussianMeasure N
  let σ := fixedWidthStdDev A N
  let L := fixedWidthInitialLogMeshScale
    (gaussianEuclideanNorm N x0) ρ
  let d : ℕ → ℕ → ℝ := fun r t ↦
    tvDist
      (((roundedPkernel A (ρ r) N) ^ t) (Qρ (ρ r) x0))
      (Measure.dirac (0 : Fin N → ℝ))
  change HasCutoff d (fixedWidthCutoffTime μ L)
    (fixedWidthCutoffWindow μ σ L)
  have hμ : 0 < μ :=
    integral_fixedWidthIncrementProcess_zero_pos_of_subcritical hsub
  have hσ : 0 < σ := fixedWidthStdDev_pos hA hN
  have hLtop : Tendsto L atTop atTop :=
    tendsto_fixedWidthInitialLogMeshScale_atTop hx0 hρpos hρ
  rw [HasCutoff, HasCutoffLimits]
  refine ⟨isCutoffWindow_fixedWidth hμ hσ hLtop, ?_, ?_⟩
  · have hpoint (c : ℝ) :
        Tendsto
          (fun r ↦ d r
            ⌊fixedWidthCutoffTime μ L r -
              c * fixedWidthCutoffWindow μ σ L r⌋₊)
          atTop (nhds (ProbabilityTheory.cdf
            (ProbabilityTheory.gaussianReal 0 1) c)) := by
      have hprofile :=
        tendsto_tvDist_roundedPkernel_fixedWidthMesh
          hA hN hsub x0 hx0 ρ hρpos hρ (-c)
      simpa only [d, μ, σ, L, neg_neg,
        show ∀ r, ⌊fixedWidthCutoffTime μ L r -
              c * fixedWidthCutoffWindow μ σ L r⌋₊ =
            canonicalTime μ σ (-c) L 0 r from
          fun r ↦ by
            rw [show fixedWidthCutoffTime μ L r -
                c * fixedWidthCutoffWindow μ σ L r =
              fixedWidthCutoffTime μ L r +
                (-c) * fixedWidthCutoffWindow μ σ L r by ring]
            exact natFloor_fixedWidthCutoffTime_add_mul_window_eq_canonicalTime
              μ σ (-c) L r]
        using hprofile
    have hinner :
        (fun c : ℝ ↦ liminf
          (fun r ↦ d r
            ⌊fixedWidthCutoffTime μ L r -
              c * fixedWidthCutoffWindow μ σ L r⌋₊) atTop) =
          ProbabilityTheory.cdf
            (ProbabilityTheory.gaussianReal 0 1) := by
      funext c
      exact (hpoint c).liminf_eq
    rw [hinner]
    exact ProbabilityTheory.tendsto_cdf_atTop _
  · have hpoint (c : ℝ) :
        Tendsto
          (fun r ↦ d r
            ⌊fixedWidthCutoffTime μ L r +
              c * fixedWidthCutoffWindow μ σ L r⌋₊)
          atTop (nhds (ProbabilityTheory.cdf
            (ProbabilityTheory.gaussianReal 0 1) (-c))) := by
      have hprofile :=
        tendsto_tvDist_roundedPkernel_fixedWidthMesh
          hA hN hsub x0 hx0 ρ hρpos hρ c
      simpa only [d, μ, σ, L,
        show ∀ r, ⌊fixedWidthCutoffTime μ L r +
              c * fixedWidthCutoffWindow μ σ L r⌋₊ =
            canonicalTime μ σ c L 0 r from
          fun r ↦
            natFloor_fixedWidthCutoffTime_add_mul_window_eq_canonicalTime
              μ σ c L r]
        using hprofile
    have hinner :
        (fun c : ℝ ↦ limsup
          (fun r ↦ d r
            ⌊fixedWidthCutoffTime μ L r +
              c * fixedWidthCutoffWindow μ σ L r⌋₊) atTop) =
          fun c ↦ ProbabilityTheory.cdf
            (ProbabilityTheory.gaussianReal 0 1) (-c) := by
      funext c
      exact (hpoint c).limsup_eq
    rw [hinner]
    exact (ProbabilityTheory.tendsto_cdf_atBot _).comp
      tendsto_neg_atTop_atBot

/-- Full paper theorem `thm:rounded-gaussian-nearest-cutoff`: simultaneously
for every fixed Gaussian offset, total variation at the exact floored
manuscript time equals the canonical absorption-time survival probability and
has the Gaussian profile.  In particular, the same mesh family has cutoff at
the stated center and window. -/
theorem rounded_gaussian_nearest_cutoff_paper
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
        (gaussianEuclideanNorm N x0) ρ) := by
  have hsub : FixedWidthSubcritical A N :=
    (fixedWidthSubcritical_iff_lt_criticalWidth hA hN).2 hcritical
  have hmean :=
    integral_fixedWidthIncrementProcess_zero_eq_fixedWidthGamma hA hN
  have hsigma := fixedWidthStdDev_eq_fixedWidthSigma hA hN
  constructor
  · intro a
    constructor
    · intro r
      exact tvDist_roundedPkernel_pow_eq_survival
        A (ρ r) N (Qρ (ρ r) x0)
        (fixedWidthPaperObservationTime A N
          (gaussianEuclideanNorm N x0) ρ a r)
    · have hprofile := tendsto_tvDist_roundedPkernel_fixedWidthMesh
        hA hN hsub x0 hx0 ρ hρpos hρ a
      simpa only [fixedWidthPaperObservationTime, hmean, hsigma] using hprofile
  · have hcutoff := hasCutoff_roundedPkernel_fixedWidthMesh
      hA hN hsub x0 hx0 ρ hρpos hρ
    simpa only [fixedWidthPaperCutoffTime, fixedWidthPaperCutoffWindow,
      hmean, hsigma] using hcutoff

/-- Compatibility wrapper for the first paper-alignment pass, which exposed
one Gaussian offset at a time and repeated the cutoff conclusion at every
offset. -/
theorem rounded_gaussian_nearest_cutoff_paper_at
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hcritical : A < fixedWidthCriticalWidth N)
    (x0 : Fin N → ℝ) (hx0 : 0 < gaussianEuclideanNorm N x0)
    (ρ : ℕ → ℝ) (hρpos : ∀ r, 0 < ρ r)
    (hρ : Tendsto ρ atTop (nhdsWithin 0 (Set.Ioi 0)))
    (a : ℝ) :
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
        (ProbabilityTheory.gaussianReal 0 1) (-a))) ∧
    HasCutoff
      (fun r t ↦
        tvDist
          (((roundedPkernel A (ρ r) N) ^ t) (Qρ (ρ r) x0))
          (Measure.dirac (0 : Fin N → ℝ)))
      (fixedWidthPaperCutoffTime A N
        (gaussianEuclideanNorm N x0) ρ)
      (fixedWidthPaperCutoffWindow A N
        (gaussianEuclideanNorm N x0) ρ) := by
  rcases rounded_gaussian_nearest_cutoff_paper
      hA hN hcritical x0 hx0 ρ hρpos hρ with ⟨hprofile, hcutoff⟩
  exact ⟨(hprofile a).1, (hprofile a).2, hcutoff⟩

end AbsorptionCutoff
