/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.RadiusConcentration
import AbsorptionCutoff.RoundedAbsorption
import Mathlib.Order.LiminfLimsup

/-!
# Terminal-layer absorption and the fixed-precision dimension cutoff

Assembles the paper's `thm:subcritical-dimension-cutoff`.  This module begins with
the **zero-bin criterion**: one rounded Gaussian step lands in the absorbing zero
bin `H_{A,ρ,N}(h,g) = 0` exactly when every rescaled coordinate stays below the
first admissible rounding threshold `b_{ρ,0} = roundedLayerThreshold ρ 0`.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace AbsorptionCutoff

/-- The deterministic cutoff location in the fixed-precision regime: the first
time at which the rounded mean-map orbit reaches the terminal scale
`a_N = 1 / log N`. -/
noncomputable def roundedDimensionCutoffTime
    (A ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℕ :=
  roundedOrbitEntrance A ρ (roundedInitialRadius ρ N x)
    (fixedPrecisionScale N)

/-- The paper's macroscopic rounded-initial-radius hypothesis
`liminf_{N → ∞} bar h_{0,N} > 0`. -/
noncomputable def macroscopicRoundedInitialRadii
    (ρ : ℝ) (x : ∀ N : ℕ, Fin N → ℝ) : Prop :=
  0 < Filter.liminf
    (fun N : ℕ => roundedInitialRadius ρ N (x N)) Filter.atTop

/-- For boxed initial vectors, the paper's literal positive-`liminf` hypothesis
is equivalent to an eventually uniform positive lower bound. -/
lemma macroscopicRoundedInitialRadii_iff_exists_eventually_lowerBound
    {ρ : ℝ} (hρ : 0 < ρ)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1) :
    macroscopicRoundedInitialRadii ρ x ↔
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          c ≤ roundedInitialRadius ρ N (x N) := by
  let h₀ : ℕ → ℝ := fun N => roundedInitialRadius ρ N (x N)
  have hnonneg : ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ h₀ N :=
    Filter.Eventually.of_forall fun N => roundedInitialRadius_nonneg ρ N (x N)
  have hboundedBelow :
      Filter.atTop.IsBoundedUnder (· ≥ ·) h₀ :=
    Filter.isBoundedUnder_of_eventually_ge hnonneg
  have hboundedAbove :
      ∀ᶠ N : ℕ in Filter.atTop, h₀ N ≤ (ρ⁻¹ + 1 / 2) ^ 2 := by
    filter_upwards [Filter.eventually_gt_atTop 0] with N hN
    exact roundedInitialRadius_le_sq hρ hN (hx N)
  constructor
  · intro hmacro
    let c := Filter.liminf h₀ Filter.atTop / 2
    have hc : 0 < c := by
      dsimp [c]
      exact half_pos hmacro
    refine ⟨c, hc, ?_⟩
    exact (Filter.eventually_lt_of_lt_liminf (by
      dsimp [c]
      exact half_lt_self hmacro) hboundedBelow).mono
      fun _ h => h.le
  · rintro ⟨c, hc, hlower⟩
    exact hc.trans_le
      (Filter.le_liminf_of_le
        (Filter.isCoboundedUnder_ge_of_eventually_le Filter.atTop hboundedAbove) hlower)

/-- The paper's macroscopic rounded initial radii force the deterministic
rounded-map cutoff locations to diverge. -/
theorem tendsto_roundedDimensionCutoffTime_atTop_of_macroscopic
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1)
    (hmacro : macroscopicRoundedInitialRadii ρ x) :
    Filter.Tendsto
      (fun N : ℕ => roundedDimensionCutoffTime A ρ N (x N))
      Filter.atTop Filter.atTop := by
  obtain ⟨c, hc, hlower⟩ :=
    (macroscopicRoundedInitialRadii_iff_exists_eventually_lowerBound hρ x hx).mp hmacro
  refine Filter.tendsto_atTop.2 fun k => ?_
  have horbitPos : 0 < roundedOrbit A ρ c k := by
    induction k with
    | zero => simpa using hc
    | succ k ih =>
        rw [show k + 1 = Nat.succ k from rfl, roundedOrbit_succ]
        exact roundedMeanMap_pos hA hρ hρ_lt ih
  have hscale :
      ∀ᶠ N : ℕ in Filter.atTop,
        fixedPrecisionScale N < roundedOrbit A ρ c k :=
    (tendsto_order.1 tendsto_fixedPrecisionScale_zero).2 _ horbitPos
  filter_upwards [hlower, hscale, Filter.eventually_gt_atTop 1] with N hcN hscaleN hN
  have hh₀ : 0 ≤ roundedInitialRadius ρ N (x N) :=
    roundedInitialRadius_nonneg ρ N (x N)
  have horbitMono :
      roundedOrbit A ρ c k ≤
        roundedOrbit A ρ (roundedInitialRadius ρ N (x N)) k := by
    exact (monotone_roundedMeanMap hA hρ).iterate k hcN
  change k ≤ roundedOrbitEntrance A ρ
    (roundedInitialRadius ρ N (x N)) (fixedPrecisionScale N)
  by_contra hk
  have hentranceLe :
      roundedOrbitEntrance A ρ (roundedInitialRadius ρ N (x N))
          (fixedPrecisionScale N) ≤ k :=
    (Nat.lt_of_not_ge hk).le
  have horbitLe :=
    roundedOrbit_mem_terminal_after_entrance
      hA hA_lt hρ hh₀ (fixedPrecisionScale_pos hN) hentranceLe
  exact (not_le_of_gt (hscaleN.trans_le horbitMono)) horbitLe

/-- The horizon through which radius concentration is used in the cutoff proof,
one step beyond the deterministic terminal-scale entrance. -/
noncomputable def roundedDimensionCutoffHorizon
    (A ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℕ :=
  roundedDimensionCutoffTime A ρ N x + 1

/-- **Zero-bin criterion** (paper §4, terminal-layer absorption).  A single rounded
Gaussian step lands in the absorbing zero bin, `H_{A,ρ,N}(h,g) = 0`, exactly when
every rescaled coordinate `A √h gᵢ` stays within the first admissible rounding
threshold `b_{ρ,0} = roundedLayerThreshold ρ 0`.

The empirical average `H_{A,ρ,N}` is a nonnegative sum of squared rounded
coordinates, so it vanishes iff each summand does; the coordinatewise criterion is
`Q₁(ρ⁻¹ tanh(ρ A √h gᵢ)) = 0`, which by `Q₁_zero_iff` and the layer preimage
`abs_inv_mul_tanh_gt_iff` is exactly `|A √h gᵢ| ≤ b_{ρ,0}`. -/
lemma Hmap_eq_zero_iff {A ρ : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (N : ℕ) (h : ℝ) (g : Fin N → ℝ) :
    Hmap A ρ N h g = 0 ↔
      ∀ i, |A * Real.sqrt h * g i| ≤ roundedLayerThreshold ρ 0 := by
  have hk : ρ * (((0 : ℕ) : ℝ) + 1 / 2) < 1 := by
    simp only [Nat.cast_zero, zero_add]
    nlinarith [hρ, hρ_lt]
  -- Coordinatewise: the rounded value vanishes iff the argument stays within the
  -- first threshold `b_{ρ,0}`.
  have hcoord : ∀ i,
      ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g i)) : ℤ) : ℝ) ^ 2 = 0 ↔
        |A * Real.sqrt h * g i| ≤ roundedLayerThreshold ρ 0 := by
    intro i
    rw [sq_eq_zero_iff, Int.cast_eq_zero, Q₁_zero_iff,
      show ρ * A * Real.sqrt h * g i = ρ * (A * Real.sqrt h * g i) from by ring]
    have knot := (abs_inv_mul_tanh_gt_iff (k := 0) hρ hk (A * Real.sqrt h * g i)).not
    simp only [not_lt, Nat.cast_zero, zero_add, one_div] at knot
    exact knot
  -- The nonnegative empirical average vanishes iff every summand does.
  have hsum_iff : Hmap A ρ N h g = 0 ↔
      ∑ i, ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g i)) : ℤ) : ℝ) ^ 2 = 0 := by
    rw [Hmap]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · rw [mul_eq_zero, or_iff_right (by positivity : (N : ℝ)⁻¹ ≠ 0)]
  rw [hsum_iff, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  constructor
  · intro H i
    exact (hcoord i).mp (H i (Finset.mem_univ i))
  · intro H i _
    exact (hcoord i).mpr (H i)

/-- **Survival criterion** (complement of the zero-bin criterion).  A rounded
Gaussian step escapes the absorbing zero bin, `H_{A,ρ,N}(h,g) ≠ 0`, exactly when some
rescaled coordinate crosses the first admissible rounding threshold `b_{ρ,0}`. -/
lemma Hmap_ne_zero_iff {A ρ : ℝ} (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (N : ℕ) (h : ℝ) (g : Fin N → ℝ) :
    Hmap A ρ N h g ≠ 0 ↔
      ∃ i, roundedLayerThreshold ρ 0 < |A * Real.sqrt h * g i| := by
  rw [ne_eq, Hmap_eq_zero_iff hρ hρ_lt, not_forall]
  simp only [not_le]

/-- Observable form of the zero-bin criterion.  Since `H_{A,ρ,N}` is the nonnegative
empirical average of the one-coordinate observables `U_{A,ρ}(h,·)`, it vanishes iff
every observable does. -/
lemma Hmap_eq_zero_iff_forall_observable (A ρ : ℝ) (N : ℕ) (h : ℝ) (g : Fin N → ℝ) :
    Hmap A ρ N h g = 0 ↔ ∀ i, roundedCoordinateObservable A ρ h (g i) = 0 := by
  rw [Hmap_eq_average_roundedCoordinateObservable]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · rw [mul_eq_zero, or_iff_right (by positivity : (N : ℝ)⁻¹ ≠ 0),
      Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => roundedCoordinateObservable_nonneg A ρ h (g i))]
    simp

/-- Observable form of the survival criterion: `H_{A,ρ,N}(h,g) ≠ 0` iff some
coordinate observable is nonzero. -/
lemma Hmap_ne_zero_iff_exists_observable (A ρ : ℝ) (N : ℕ) (h : ℝ) (g : Fin N → ℝ) :
    Hmap A ρ N h g ≠ 0 ↔ ∃ i, roundedCoordinateObservable A ρ h (g i) ≠ 0 := by
  rw [ne_eq, Hmap_eq_zero_iff_forall_observable, not_forall]

/-- **One-step escape probability.**  From a positive radius `h`, the probability that
one rounded Gaussian step escapes the absorbing zero bin is at most `2N` times the
standard-Gaussian Chernoff factor at the rescaled first threshold `b_{ρ,0}/(A√h)`.
This is the Gaussian union bound over the `N` coordinates, each controlled by the
one-coordinate support estimate `measureReal_roundedCoordinateObservable_ne_zero_le`. -/
lemma measureReal_Hmap_ne_zero_le {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hh : 0 < h) (N : ℕ) :
    (gaussianVec N).real {g | Hmap A ρ N h g ≠ 0} ≤
      2 * N *
        Real.exp (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2) := by
  have hmeasS : MeasurableSet {x : ℝ | roundedCoordinateObservable A ρ h x ≠ 0} := by
    have h0 : MeasurableSet {x : ℝ | roundedCoordinateObservable A ρ h x = 0} :=
      (measurable_roundedCoordinateObservable A ρ h) (measurableSet_singleton 0)
    exact h0.compl
  -- The escape event is the finite union of the coordinatewise support events.
  have hset : {g : Fin N → ℝ | Hmap A ρ N h g ≠ 0} =
      ⋃ i, (Function.eval i) ⁻¹'
        {x : ℝ | roundedCoordinateObservable A ρ h x ≠ 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Function.eval]
    exact Hmap_ne_zero_iff_exists_observable A ρ N h g
  -- Each coordinate marginal of the product Gaussian is the standard Gaussian.
  have hmarg : ∀ i : Fin N,
      (gaussianVec N).real ((Function.eval i) ⁻¹'
        {x : ℝ | roundedCoordinateObservable A ρ h x ≠ 0}) =
        (gaussianReal 0 1).real {x : ℝ | roundedCoordinateObservable A ρ h x ≠ 0} := by
    intro i
    have hpm : (gaussianVec N).map (Function.eval i) = gaussianReal 0 1 := by
      unfold gaussianVec; rw [Measure.pi_map_eval]; simp
    simp only [measureReal_def]
    rw [← Measure.map_apply (f := Function.eval i) (measurable_pi_apply i) hmeasS, hpm]
  rw [hset]
  calc (gaussianVec N).real (⋃ i, (Function.eval i) ⁻¹'
          {x : ℝ | roundedCoordinateObservable A ρ h x ≠ 0})
      ≤ ∑ i : Fin N, (gaussianVec N).real ((Function.eval i) ⁻¹'
          {x : ℝ | roundedCoordinateObservable A ρ h x ≠ 0}) :=
        measureReal_iUnion_fintype_le _
    _ = ∑ _i : Fin N,
          (gaussianReal 0 1).real
            {x : ℝ | roundedCoordinateObservable A ρ h x ≠ 0} :=
        Finset.sum_congr rfl (fun i _ => hmarg i)
    _ = (N : ℝ) *
          (gaussianReal 0 1).real
            {x : ℝ | roundedCoordinateObservable A ρ h x ≠ 0} := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (N : ℝ) *
          (2 * Real.exp
            (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
        exact measureReal_roundedCoordinateObservable_ne_zero_le hA hρ hρ_lt hh
    _ = 2 * N *
          Real.exp (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2) := by
        ring

/-- **Kernel form of the one-step escape bound.**  From a positive radius `h`, the
non-absorption probability of the rounded radius kernel `H_{A,ρ,N}(h,·)` (the mass
away from the absorbing state `0`) is exponentially small. -/
lemma measureReal_Hkernel_compl_singleton_zero_le {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hh : 0 < h) (N : ℕ) :
    (Hkernel A ρ N h).real {(0 : ℝ)}ᶜ ≤
      2 * N *
        Real.exp (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2) := by
  rw [Hkernel_apply, measureReal_def,
    Measure.map_apply (measurable_Hmap_right A ρ N h)
      (measurableSet_singleton (0 : ℝ)).compl]
  have hpre : (Hmap A ρ N h) ⁻¹' {(0 : ℝ)}ᶜ =
      {g : Fin N → ℝ | Hmap A ρ N h g ≠ 0} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
  rw [hpre]
  exact measureReal_Hmap_ne_zero_le hA hρ hρ_lt hh N

/-- The one-step escape estimate is uniform over the terminal interval
`0 ≤ h ≤ η / log N`: its largest value is attained at the upper endpoint.
This is the kernel form used in the final Markov-step split. -/
lemma measureReal_Hkernel_compl_singleton_zero_le_escape_at_eta
    {A ρ η h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hη : 0 < η) {N : ℕ} (hN : 1 < N)
    (hh₀ : 0 ≤ h) (hhle : h ≤ η / Real.log N) :
    (Hkernel A ρ N h).real {(0 : ℝ)}ᶜ ≤
      2 * N *
        Real.exp
          (-((roundedLayerThreshold ρ 0 /
            (A * Real.sqrt (η / Real.log N))) ^ 2) / 2) := by
  by_cases hh : h = 0
  · subst h
    rw [isAbsorbing_Hkernel A ρ N, measureReal_def, Measure.dirac_apply]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false,
      not_false_eq_true, Set.indicator_of_notMem, ENNReal.toReal_zero]
    positivity
  have hhpos : 0 < h := lt_of_le_of_ne hh₀ (Ne.symm hh)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hηlog : 0 < η / Real.log N := div_pos hη hlog
  have hsqrt :
      Real.sqrt h ≤ Real.sqrt (η / Real.log N) :=
    Real.sqrt_le_sqrt hhle
  have hden :
      A * Real.sqrt h ≤ A * Real.sqrt (η / Real.log N) :=
    mul_le_mul_of_nonneg_left hsqrt hA.le
  have hden₀ : 0 < A * Real.sqrt h :=
    mul_pos hA (Real.sqrt_pos.2 hhpos)
  have hdenη : 0 < A * Real.sqrt (η / Real.log N) :=
    mul_pos hA (Real.sqrt_pos.2 hηlog)
  have hb : 0 ≤ roundedLayerThreshold ρ 0 :=
    (roundedLayerThreshold_zero_pos hρ hρ_lt).le
  have hratio :
      roundedLayerThreshold ρ 0 / (A * Real.sqrt (η / Real.log N)) ≤
        roundedLayerThreshold ρ 0 / (A * Real.sqrt h) := by
    rw [div_le_div_iff₀ hdenη hden₀]
    exact mul_le_mul_of_nonneg_left hden hb
  have hsq :
      (roundedLayerThreshold ρ 0 /
          (A * Real.sqrt (η / Real.log N))) ^ 2 ≤
        (roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2 := by
    exact pow_le_pow_left₀ (div_nonneg hb hdenη.le) hratio 2
  calc
    (Hkernel A ρ N h).real {(0 : ℝ)}ᶜ ≤
        2 * N *
          Real.exp
            (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2) :=
      measureReal_Hkernel_compl_singleton_zero_le hA hρ hρ_lt hhpos N
    _ ≤ 2 * N *
          Real.exp
            (-((roundedLayerThreshold ρ 0 /
              (A * Real.sqrt (η / Real.log N))) ^ 2) / 2) := by
      gcongr

/-- **One-step terminal split.**  If the rounded radius chain starts from a
nonnegative state, then survival for one step beyond time `s` is bounded by
the probability that the time-`s` radius exceeds `η / log N`, plus the
uniform terminal escape rate.  This is the kernel-power version of the
paper's final Markov-step decomposition. -/
lemma measureReal_Hkernel_pow_succ_compl_singleton_zero_le
    {A ρ η h₀ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hη : 0 < η) {N : ℕ} (hN : 1 < N)
    (hh₀ : 0 ≤ h₀) (s : ℕ) :
    (((Hkernel A ρ N) ^ (s + 1)) h₀).real {(0 : ℝ)}ᶜ ≤
      (((Hkernel A ρ N) ^ s) h₀).real
          (Set.Ioi (η / Real.log N)) +
        2 * N *
          Real.exp
            (-((roundedLayerThreshold ρ 0 /
              (A * Real.sqrt (η / Real.log N))) ^ 2) / 2) := by
  let ν := ((Hkernel A ρ N) ^ s) h₀
  let E :=
    2 * (N : ℝ) *
      Real.exp
        (-((roundedLayerThreshold ρ 0 /
          (A * Real.sqrt (η / Real.log N))) ^ 2) / 2)
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hnonneg : ∀ᵐ h ∂ν, 0 ≤ h := by
    let μ :=
      markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)
    have hpath :
        ∀ᵐ ω ∂μ, 0 ≤ ω s := by
      dsimp [μ]
      exact markovPathMeasure_dirac_ae_eval_nonneg hh₀ hρ (by omega) s
    have hmap :
        μ.map (fun ω => ω s) = ν := by
      dsimp [μ, ν]
      exact markovPathMeasure_dirac_map_eval h₀ (Hkernel A ρ N) s
    have hmapped :
        ∀ᵐ h ∂μ.map (fun ω => ω s), 0 ≤ h :=
      (MeasureTheory.ae_map_iff
        (measurable_pi_apply s).aemeasurable measurableSet_Ici).2 hpath
    rwa [hmap] at hmapped
  have hpoint :
      ∀ᵐ h ∂ν,
        Hkernel A ρ N h {(0 : ℝ)}ᶜ ≤
          (Set.Ioi (η / Real.log N)).indicator (fun _ : ℝ => (1 : ENNReal)) h +
            ENNReal.ofReal E := by
    filter_upwards [hnonneg] with h hh
    by_cases hlarge : η / Real.log N < h
    · rw [Set.indicator_of_mem
        (show h ∈ Set.Ioi (η / Real.log N) from hlarge)]
      calc
        Hkernel A ρ N h {(0 : ℝ)}ᶜ ≤ Hkernel A ρ N h Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ 1 + ENNReal.ofReal E := le_add_right le_rfl
    · rw [Set.indicator_of_notMem
        (show h ∉ Set.Ioi (η / Real.log N) from hlarge), zero_add]
      have hreal :=
        measureReal_Hkernel_compl_singleton_zero_le_escape_at_eta
          hA hρ hρ_lt hη hN hh (not_lt.mp hlarge)
      calc
        Hkernel A ρ N h {(0 : ℝ)}ᶜ =
            ENNReal.ofReal ((Hkernel A ρ N h).real {(0 : ℝ)}ᶜ) := by
              rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ ENNReal.ofReal E := ENNReal.ofReal_le_ofReal (by simpa [E] using hreal)
  have henn :
      ((Hkernel A ρ N) ^ (s + 1)) h₀ {(0 : ℝ)}ᶜ ≤
        ν (Set.Ioi (η / Real.log N)) + ENNReal.ofReal E := by
    rw [pow_succ',
      show Hkernel A ρ N * (Hkernel A ρ N) ^ s =
          Kernel.comp (Hkernel A ρ N) ((Hkernel A ρ N) ^ s) from by
            change Kernel.comp (Hkernel A ρ N) ((Hkernel A ρ N) ^ s) =
              Kernel.comp (Hkernel A ρ N) ((Hkernel A ρ N) ^ s)
            rfl]
    calc
      (Kernel.comp (Hkernel A ρ N) ((Hkernel A ρ N) ^ s) h₀) {(0 : ℝ)}ᶜ =
          ∫⁻ h, Hkernel A ρ N h {(0 : ℝ)}ᶜ ∂ν := by
        simpa only [ν] using
          Kernel.comp_apply' (Hkernel A ρ N) ((Hkernel A ρ N) ^ s) h₀
            (measurableSet_singleton (0 : ℝ)).compl
      _ ≤
          ∫⁻ h,
            (Set.Ioi (η / Real.log N)).indicator (fun _ : ℝ => (1 : ENNReal)) h +
              ENNReal.ofReal E ∂ν :=
        lintegral_mono_ae hpoint
      _ = (∫⁻ h,
            (Set.Ioi (η / Real.log N)).indicator (fun _ : ℝ => (1 : ENNReal)) h ∂ν) +
            ∫⁻ _h, ENNReal.ofReal E ∂ν := by
          rw [lintegral_add_left]
          exact measurable_const.indicator measurableSet_Ioi
      _ = ν (Set.Ioi (η / Real.log N)) + ENNReal.ofReal E := by
          rw [lintegral_indicator measurableSet_Ioi, lintegral_const]
          simp
  rw [measureReal_def, measureReal_def]
  calc
    (((Hkernel A ρ N) ^ (s + 1)) h₀ {(0 : ℝ)}ᶜ).toReal ≤
        (ν (Set.Ioi (η / Real.log N)) + ENNReal.ofReal E).toReal :=
      ENNReal.toReal_mono (by finiteness) henn
    _ = (ν (Set.Ioi (η / Real.log N))).toReal + E := by
      rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hE]
    _ = ((((Hkernel A ρ N) ^ s) h₀)
          (Set.Ioi (η / Real.log N))).toReal +
        2 * N *
          Real.exp
            (-((roundedLayerThreshold ρ 0 /
              (A * Real.sqrt (η / Real.log N))) ^ 2) / 2) := by
      rfl

/-- The time-`s` kernel mass above `η / log N` is exactly the canonical
path-space probability of the rescaled-radius event `η < H_s log N`.
This is the coordinate-marginal bridge used to feed terminal-radius
convergence into the one-step kernel split. -/
lemma measureReal_Hkernel_pow_Ioi_div_log_eq
    (A ρ η h₀ : ℝ) {N : ℕ} (hN : 1 < N) (s : ℕ) :
    (((Hkernel A ρ N) ^ s) h₀).real
        (Set.Ioi (η / Real.log N)) =
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)).real
        {ω | η < ω s * Real.log N} := by
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hset :
      (fun ω : ℕ → ℝ => ω s) ⁻¹' Set.Ioi (η / Real.log N) =
        {ω | η < ω s * Real.log N} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_setOf_eq]
    exact div_lt_iff₀ hlog
  rw [measureReal_def, measureReal_def,
    ← markovPathMeasure_dirac_map_eval h₀ (Hkernel A ρ N) s,
    Measure.map_apply (measurable_pi_apply s) measurableSet_Ioi, hset]

/-- **Terminal small-radius decay.**  There are constants `c, C > 0` such that, for all
sufficiently large `N`, every radius `h` at or below the terminal scale
`a_N = 1/\log N` already satisfies `V_{A,ρ}(h) ≤ C·N^{-c}`.  This is the deterministic
input behind the paper's terminal-entrance estimate `bar h_{s_N,N} ≤ C N^{-c}`:
compose the small-radius bound `V(h) ≤ C·exp(-c/h)` with `1/h ≥ \log N`. -/
lemma exists_roundedMeanMap_le_rpow_atTop {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ h : ℝ, 0 ≤ h → h ≤ fixedPrecisionScale N →
        roundedMeanMap A ρ h ≤ C * (N : ℝ) ^ (-c) := by
  obtain ⟨c, C, hc, hC, hbound⟩ :=
    exists_roundedMeanMap_small_radius_bounds hA hρ hρ_lt
      (r := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨c, C, hc, hC, ?_⟩
  have hlog : ∀ᶠ N : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  filter_upwards [hlog, Filter.eventually_ge_atTop 2] with N hlogN hN2 h hh0 hhle
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlogN_pos : 0 < Real.log N := lt_of_lt_of_le (by norm_num) hlogN
  have haN_le : fixedPrecisionScale N ≤ 1 / 2 := by
    rw [fixedPrecisionScale, show (1 : ℝ) / 2 = 2⁻¹ from by norm_num]
    exact (inv_le_inv₀ hlogN_pos (by norm_num)).mpr hlogN
  rcases hh0.lt_or_eq with hhpos | h0
  · -- `0 < h`: apply the small-radius bound, then `1/h ≥ log N`.
    have hh_half : h ≤ 1 / 2 := le_trans hhle haN_le
    obtain ⟨hV, -⟩ := hbound h hhpos hh_half
    have hlogN_le : Real.log N ≤ h⁻¹ := by
      have h1 : h ≤ (Real.log N)⁻¹ := by rw [← fixedPrecisionScale]; exact hhle
      have h2 := (inv_le_inv₀ (inv_pos.mpr hlogN_pos) hhpos).mpr h1
      rwa [inv_inv] at h2
    have hexp_arg : -c / h ≤ -c * Real.log N := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonpos_left hlogN_le (by linarith : -c ≤ 0)
    calc roundedMeanMap A ρ h
        ≤ C * Real.exp (-c / h) := hV
      _ ≤ C * Real.exp (-c * Real.log N) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_arg) hC.le
      _ = C * (N : ℝ) ^ (-c) := by
          rw [Real.rpow_def_of_pos hNpos, mul_comm (Real.log N) (-c)]
  · -- `h = 0`: `V(0) = 0`.
    rw [← h0, roundedMeanMap_zero]
    exact le_of_lt (mul_pos hC (Real.rpow_pos_of_pos hNpos _))

/-- **Terminal-entrance limit.**  If a deterministic radius sequence stays (eventually)
nonnegative and below the terminal scale `a_N = 1/\log N`, then applying the rounded
mean map and rescaling by `\log N` vanishes.  With `h_N = bar h_{bar t_N,N} ≤ a_N` the
pre-terminal radius, this is the paper's `bar h_{s_N,N}·\log N → 0`. -/
lemma tendsto_roundedMeanMap_mul_log_of_le_fixedPrecisionScale {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) {h : ℕ → ℝ}
    (hh0 : ∀ᶠ N in Filter.atTop, 0 ≤ h N)
    (hhle : ∀ᶠ N in Filter.atTop, h N ≤ fixedPrecisionScale N) :
    Filter.Tendsto (fun N : ℕ => roundedMeanMap A ρ (h N) * Real.log N)
      Filter.atTop (𝓝 0) := by
  obtain ⟨c, C, hc, hC, hdecay⟩ := exists_roundedMeanMap_le_rpow_atTop hA hρ hρ_lt
  -- The dominating sequence `C·N^{-c}·log N → 0`.
  have hbase : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (-c) * Real.log N)
      Filter.atTop (𝓝 0) := by
    have hdiv : Filter.Tendsto (fun x : ℝ => Real.log x / x ^ c)
        Filter.atTop (𝓝 0) := (isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero
    have hcomp := hdiv.comp tendsto_natCast_atTop_atTop
    have hrw : (fun N : ℕ => (N : ℝ) ^ (-c) * Real.log N) =
        (fun x : ℝ => Real.log x / x ^ c) ∘ (Nat.cast : ℕ → ℝ) := by
      funext N
      simp only [Function.comp_apply]
      rw [Real.rpow_neg (by positivity), div_eq_mul_inv, mul_comm]
    rw [hrw]
    exact hcomp
  have hg : Filter.Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-c) * Real.log N)
      Filter.atTop (𝓝 0) := by
    have h2 : Filter.Tendsto (fun N : ℕ => C * ((N : ℝ) ^ (-c) * Real.log N))
        Filter.atTop (𝓝 0) := by simpa using hbase.const_mul C
    simpa [mul_assoc] using h2
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN1
    exact mul_nonneg (roundedMeanMap_nonneg A ρ (h N))
      (Real.log_nonneg (by exact_mod_cast hN1))
  · filter_upwards [hh0, hhle, hdecay, Filter.eventually_ge_atTop 1]
      with N hh0N hhleN hdecayN hN1
    exact mul_le_mul_of_nonneg_right (hdecayN (h N) hh0N hhleN)
      (Real.log_nonneg (by exact_mod_cast hN1))

/-- The terminal scale exactly cancels the logarithm: `a_N·\log N = 1` for `N ≥ 2`. -/
lemma fixedPrecisionScale_mul_log {N : ℕ} (hN : 1 < N) :
    fixedPrecisionScale N * Real.log N = 1 := by
  have hpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  rw [fixedPrecisionScale, inv_mul_cancel₀ hpos.ne']

/-- **Terminal-entrance normalization.**  Under the same hypotheses as
`tendsto_roundedMeanMap_mul_log_of_le_fixedPrecisionScale`, the normalized denominator
`(V_{A,ρ}(h_N)+a_N)·\log N → 1`, the paper's `(bar h_{s_N,N}+a_N)\log N → 1`. -/
lemma tendsto_add_fixedPrecisionScale_mul_log_of_le {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) {h : ℕ → ℝ}
    (hh0 : ∀ᶠ N in Filter.atTop, 0 ≤ h N)
    (hhle : ∀ᶠ N in Filter.atTop, h N ≤ fixedPrecisionScale N) :
    Filter.Tendsto
      (fun N : ℕ => (roundedMeanMap A ρ (h N) + fixedPrecisionScale N) * Real.log N)
      Filter.atTop (𝓝 1) := by
  have hlim :=
    tendsto_roundedMeanMap_mul_log_of_le_fixedPrecisionScale hA hρ hρ_lt hh0 hhle
  have haN : (fun N : ℕ => fixedPrecisionScale N * Real.log N)
      =ᶠ[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) := by
    filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    exact fixedPrecisionScale_mul_log hN
  have h1 : Filter.Tendsto (fun N : ℕ => fixedPrecisionScale N * Real.log N)
      Filter.atTop (𝓝 1) := tendsto_const_nhds.congr' haN.symm
  have hfun : (fun N : ℕ =>
        (roundedMeanMap A ρ (h N) + fixedPrecisionScale N) * Real.log N) =
      (fun N : ℕ => roundedMeanMap A ρ (h N) * Real.log N
        + fixedPrecisionScale N * Real.log N) := by
    funext N; rw [add_mul]
  rw [hfun]
  simpa using hlim.add h1

/-- **Terminal escape rate vanishes.**  For `0 < η < b_{ρ,0}²/(2A²)`, the one-step escape
bound evaluated at the terminal radius scale `η/\log N` tends to `0`: it equals
`2·N^{1-b_{ρ,0}²/(2A²η)}` and the exponent is negative.  This is the paper's
`2N^{1-b²/(2A²η)} → 0` in the final-absorption step. -/
lemma tendsto_escape_at_eta_atTop {A ρ η : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hη : 0 < η)
    (hη_lt : η < roundedLayerThreshold ρ 0 ^ 2 / (2 * A ^ 2)) :
    Filter.Tendsto (fun N : ℕ => 2 * (N : ℝ) *
      Real.exp (-((roundedLayerThreshold ρ 0 /
        (A * Real.sqrt (η / Real.log N))) ^ 2) / 2)) Filter.atTop (𝓝 0) := by
  set b := roundedLayerThreshold ρ 0 with hbdef
  have hbpos : 0 < b := roundedLayerThreshold_zero_pos hρ hρ_lt
  have h2A2 : (0 : ℝ) < 2 * A ^ 2 := by positivity
  have h2A2η : (0 : ℝ) < 2 * A ^ 2 * η := by positivity
  set β := b ^ 2 / (2 * A ^ 2 * η) with hβdef
  have hβ1 : 1 < β := by
    rw [hβdef, lt_div_iff₀ h2A2η, one_mul]
    rw [lt_div_iff₀ h2A2] at hη_lt
    nlinarith [hη_lt]
  -- The target sequence eventually equals `2·N^{1-β}`.
  have hEq : (fun N : ℕ => 2 * (N : ℝ) *
        Real.exp (-((b / (A * Real.sqrt (η / Real.log N))) ^ 2) / 2))
      =ᶠ[Filter.atTop] (fun N : ℕ => 2 * (N : ℝ) ^ (1 - β)) := by
    filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hsq : Real.sqrt (η / Real.log N) ^ 2 = η / Real.log N :=
      Real.sq_sqrt (by positivity)
    have harg : -((b / (A * Real.sqrt (η / Real.log N))) ^ 2) / 2
        = Real.log N * (-β) := by
      rw [div_pow, mul_pow, hsq, hβdef]
      field_simp
    rw [harg, ← Real.rpow_def_of_pos hNpos,
      show (1 : ℝ) - β = 1 + (-β) from by ring, Real.rpow_add hNpos, Real.rpow_one]
    ring
  rw [Filter.tendsto_congr' hEq]
  have hy : 0 < β - 1 := by linarith
  have hrpow : Filter.Tendsto (fun x : ℝ => x ^ (-(β - 1))) Filter.atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hy
  have hcomp := hrpow.comp tendsto_natCast_atTop_atTop
  have hpow : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - β)) Filter.atTop (𝓝 0) := by
    have hfun : (fun N : ℕ => (N : ℝ) ^ (1 - β)) =
        (fun x : ℝ => x ^ (-(β - 1))) ∘ (Nat.cast : ℕ → ℝ) := by
      funext N
      simp only [Function.comp_apply]
      rw [show (1 : ℝ) - β = -(β - 1) from by ring]
    rw [hfun]; exact hcomp
  simpa using hpow.const_mul 2

/-- **Terminal-entrance limit along the deterministic orbit.**  For a lattice-subcritical
map `A < A_{\mathrm{lat}}` and any nonnegative initial-radius sequence `h₀ N`, the orbit
value one step past the `a_N`-entrance, rescaled by `\log N`, vanishes.  With
`bar t_N = roundedOrbitEntrance A ρ (h₀ N) a_N` and `s_N = bar t_N + 1`, this is exactly
the paper's `bar h_{s_N,N}·\log N → 0`. -/
lemma tendsto_roundedOrbit_terminal_mul_log {A ρ : ℝ} {h₀ : ℕ → ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : ∀ N, 0 ≤ h₀ N) :
    Filter.Tendsto (fun N : ℕ => roundedOrbit A ρ (h₀ N)
        (roundedOrbitEntrance A ρ (h₀ N) (fixedPrecisionScale N) + 1) * Real.log N)
      Filter.atTop (𝓝 0) := by
  have hh0 : ∀ᶠ N in Filter.atTop, 0 ≤
      roundedOrbit A ρ (h₀ N) (roundedOrbitEntrance A ρ (h₀ N) (fixedPrecisionScale N)) :=
    Filter.Eventually.of_forall fun N => roundedOrbit_nonneg (hh₀ N) _
  have hhle : ∀ᶠ N in Filter.atTop,
      roundedOrbit A ρ (h₀ N) (roundedOrbitEntrance A ρ (h₀ N) (fixedPrecisionScale N))
        ≤ fixedPrecisionScale N := by
    filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    exact roundedOrbitEntrance_spec_of_subcritical hA hA_lt hρ (hh₀ N)
      (fixedPrecisionScale_pos hN)
  refine (tendsto_roundedMeanMap_mul_log_of_le_fixedPrecisionScale hA hρ hρ_lt hh0 hhle).congr
    (fun N => ?_)
  rw [roundedOrbit_succ]

/-- **Terminal-entrance normalization along the deterministic orbit.**  Companion to
`tendsto_roundedOrbit_terminal_mul_log`: the normalized denominator
`(bar h_{s_N,N}+a_N)·\log N → 1`. -/
lemma tendsto_roundedOrbit_terminal_add_scale_mul_log {A ρ : ℝ} {h₀ : ℕ → ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : ∀ N, 0 ≤ h₀ N) :
    Filter.Tendsto (fun N : ℕ => (roundedOrbit A ρ (h₀ N)
          (roundedOrbitEntrance A ρ (h₀ N) (fixedPrecisionScale N) + 1)
        + fixedPrecisionScale N) * Real.log N)
      Filter.atTop (𝓝 1) := by
  have hh0 : ∀ᶠ N in Filter.atTop, 0 ≤
      roundedOrbit A ρ (h₀ N) (roundedOrbitEntrance A ρ (h₀ N) (fixedPrecisionScale N)) :=
    Filter.Eventually.of_forall fun N => roundedOrbit_nonneg (hh₀ N) _
  have hhle : ∀ᶠ N in Filter.atTop,
      roundedOrbit A ρ (h₀ N) (roundedOrbitEntrance A ρ (h₀ N) (fixedPrecisionScale N))
        ≤ fixedPrecisionScale N := by
    filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    exact roundedOrbitEntrance_spec_of_subcritical hA hA_lt hρ (hh₀ N)
      (fixedPrecisionScale_pos hN)
  refine (tendsto_add_fixedPrecisionScale_mul_log_of_le hA hρ hρ_lt hh0 hhle).congr
    (fun N => ?_)
  rw [roundedOrbit_succ]

/-- The deterministic cutoff horizon automatically satisfies the
subpolynomial rate hypothesis of fixed-precision radius concentration.  This
packages the paper's deduction
`\bar T_N = \bar t_N + 1 = O(log log N)` and hence
`\bar T_N N⁻¹ exp(C (log log N)²) → 0` for every fixed `C`. -/
lemma roundedDimensionCutoffHorizon_rate
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1) :
    ∀ C : ℝ,
      Filter.Tendsto
        (fun N : ℕ =>
          (roundedDimensionCutoffHorizon A ρ N (x N) : ℝ) / (N : ℝ) *
            Real.exp (C * (Real.log (Real.log N)) ^ 2))
        Filter.atTop (𝓝 0) := by
  let C₀ := (ρ⁻¹ + 1 / 2) ^ 2
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    exact sq_pos_of_pos (add_pos (inv_pos.mpr hρ) (by norm_num))
  obtain ⟨D, hD, N₀, htime⟩ :=
    exists_eventually_uniform_subcritical_tail_length_le_mul_log_log
      hA hA_lt hρ hC₀
  intro C
  have hupper :
      Filter.Tendsto
        (fun N : ℕ =>
          (D + 2) *
            ((N : ℝ)⁻¹ *
              Real.exp ((C + 1) * (Real.log (Real.log N)) ^ 2)))
        Filter.atTop (𝓝 0) :=
    by
      simpa using
        (tendsto_inv_nat_mul_exp_log_log_sq_zero (C + 1)).const_mul (D + 2)
  refine squeeze_zero'
    (g := fun N : ℕ =>
      (D + 2) *
        ((N : ℝ)⁻¹ *
          Real.exp ((C + 1) * (Real.log (Real.log N)) ^ 2)))
    (Filter.Eventually.of_forall fun N => by positivity) ?_ hupper
  obtain ⟨N₁, hN₁⟩ := exists_eventually_le_log_log_nat 1
  filter_upwards [Filter.eventually_ge_atTop (max N₀ (max N₁ 2))] with N hN
  have hN₀ : N₀ ≤ N := (le_max_left N₀ (max N₁ 2)).trans hN
  have hN₁N : N₁ ≤ N :=
    (le_max_left N₁ 2).trans ((le_max_right N₀ (max N₁ 2)).trans hN)
  have hNpos : 0 < N := by
    have : 2 ≤ N :=
      (le_max_right N₁ 2).trans ((le_max_right N₀ (max N₁ 2)).trans hN)
    omega
  let h₀ := roundedInitialRadius ρ N (x N)
  let t := roundedDimensionCutoffTime A ρ N (x N)
  have hh₀ : 0 ≤ h₀ := roundedInitialRadius_nonneg ρ N (x N)
  have hh₀C₀ : h₀ ≤ C₀ := by
    dsimp [h₀, C₀]
    exact roundedInitialRadius_le_sq hρ hNpos (hx N)
  have horbit : ∀ u ∈ Finset.Ico 0 t,
      fixedPrecisionScale N ≤ roundedOrbit A ρ h₀ u := by
    intro u hu
    have hu_lt : u < t := (Finset.mem_Ico.mp hu).2
    exact (roundedOrbit_lt_entrance
      (A := A) (ρ := ρ) (h₀ := h₀) (r := fixedPrecisionScale N)
      hu_lt).le
  have ht :
      (t : ℝ) ≤ (D + 1) * Real.log (Real.log N) := by
    simpa using htime N hN₀ h₀ hh₀ hh₀C₀ 0 t horbit
  have hloglog : 1 ≤ Real.log (Real.log N) := hN₁ N hN₁N
  have htHorizon :
      (roundedDimensionCutoffHorizon A ρ N (x N) : ℝ) ≤
        (D + 2) * Real.log (Real.log N) := by
    rw [roundedDimensionCutoffHorizon]
    change ((t + 1 : ℕ) : ℝ) ≤ _
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hloglog_exp :
      Real.log (Real.log N) ≤
        Real.exp ((Real.log (Real.log N)) ^ 2) := by
    calc
      Real.log (Real.log N) ≤ (Real.log (Real.log N)) ^ 2 := by nlinarith
      _ ≤ 1 + (Real.log (Real.log N)) ^ 2 := by linarith
      _ ≤ Real.exp ((Real.log (Real.log N)) ^ 2) :=
        by simpa [add_comm] using Real.add_one_le_exp ((Real.log (Real.log N)) ^ 2)
  have hD2 : 0 ≤ D + 2 := by linarith
  calc
    (roundedDimensionCutoffHorizon A ρ N (x N) : ℝ) / (N : ℝ) *
          Real.exp (C * (Real.log (Real.log N)) ^ 2)
        ≤ ((D + 2) * Real.log (Real.log N)) / (N : ℝ) *
          Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
            gcongr
    _ ≤ (D + 2) *
          ((N : ℝ)⁻¹ *
            (Real.exp ((Real.log (Real.log N)) ^ 2) *
              Real.exp (C * (Real.log (Real.log N)) ^ 2))) := by
            rw [div_eq_mul_inv]
            calc
              (D + 2) * Real.log (Real.log N) * (N : ℝ)⁻¹ *
                    Real.exp (C * (Real.log (Real.log N)) ^ 2)
                  = (D + 2) * ((N : ℝ)⁻¹ *
                      (Real.log (Real.log N) *
                        Real.exp (C * (Real.log (Real.log N)) ^ 2))) := by ring
              _ ≤ (D + 2) * ((N : ℝ)⁻¹ *
                    (Real.exp ((Real.log (Real.log N)) ^ 2) *
                      Real.exp (C * (Real.log (Real.log N)) ^ 2))) := by
                    gcongr
    _ = (D + 2) *
          ((N : ℝ)⁻¹ *
            Real.exp ((C + 1) * (Real.log (Real.log N)) ^ 2)) := by
            rw [← Real.exp_add]
            congr 3
            ring

/-- At the deterministic terminal horizon, the exact rounded squared radius,
rescaled by `log N`, converges to zero in probability.  This is the
probabilistic terminal-entrance conclusion in the paper: fixed-precision
radius concentration controls the normalized tracking error, while the
deterministic orbit term vanishes and its normalization tends to one. -/
lemma tendsto_measureReal_terminal_radius_mul_log_gt
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    Filter.Tendsto
      (fun N : ℕ =>
        (markovPathMeasure
            (Measure.dirac (roundedInitialRadius ρ N (x N)))
            (Hkernel A ρ N)).real
          {ω |
            η < ω (roundedDimensionCutoffHorizon A ρ N (x N)) *
              Real.log N})
      Filter.atTop (𝓝 0) := by
  let h₀ : ℕ → ℝ := fun N => roundedInitialRadius ρ N (x N)
  let s : ℕ → ℕ := fun N => roundedDimensionCutoffHorizon A ρ N (x N)
  have hh₀ : ∀ N, 0 ≤ h₀ N :=
    fun N => roundedInitialRadius_nonneg ρ N (x N)
  have hbar :
      Filter.Tendsto
        (fun N : ℕ => roundedOrbit A ρ (h₀ N) (s N) * Real.log N)
        Filter.atTop (𝓝 0) := by
    simpa only [h₀, s, roundedDimensionCutoffHorizon,
      roundedDimensionCutoffTime] using
      tendsto_roundedOrbit_terminal_mul_log hA hA_lt hρ hρ_lt hh₀
  have hden :
      Filter.Tendsto
        (fun N : ℕ =>
          (roundedOrbit A ρ (h₀ N) (s N) + fixedPrecisionScale N) *
            Real.log N)
        Filter.atTop (𝓝 1) := by
    simpa only [h₀, s, roundedDimensionCutoffHorizon,
      roundedDimensionCutoffTime] using
      tendsto_roundedOrbit_terminal_add_scale_mul_log
        hA hA_lt hρ hρ_lt hh₀
  have hconc :=
    subcritical_exact_radius_concentration hA hA_lt hρ hρ_lt x hx s
      (by
        simpa only [s] using
          roundedDimensionCutoffHorizon_rate hA hA_lt hρ x hx)
      (η / 4) (by positivity)
  refine squeeze_zero'
    (g := fun N : ℕ =>
      (markovPathMeasure
          (Measure.dirac (roundedInitialRadius ρ N (x N)))
          (Hkernel A ρ N)).real
        {ω | ∃ t ≤ s N,
          η / 4 <
            |normalizedRadiusError A ρ
              (roundedInitialRadius ρ N (x N))
              (fixedPrecisionScale N) t ω|})
    (Filter.Eventually.of_forall fun N => by positivity) ?_ hconc
  have hbar_lt :
      ∀ᶠ N : ℕ in Filter.atTop,
        roundedOrbit A ρ (h₀ N) (s N) * Real.log N < η / 2 :=
    (tendsto_order.1 hbar).2 (η / 2) (by positivity)
  have hden_lt :
      ∀ᶠ N : ℕ in Filter.atTop,
        (roundedOrbit A ρ (h₀ N) (s N) + fixedPrecisionScale N) *
            Real.log N < 2 :=
    (tendsto_order.1 hden).2 2 (by norm_num)
  filter_upwards [hbar_lt, hden_lt, Filter.eventually_gt_atTop 1]
    with N hbarN hdenN hN
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change η < ω (s N) * Real.log N at hω
  refine ⟨s N, le_rfl, ?_⟩
  have ha : 0 < fixedPrecisionScale N := fixedPrecisionScale_pos hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hb : 0 ≤ roundedOrbit A ρ (h₀ N) (s N) :=
    roundedOrbit_nonneg (hh₀ N) _
  have hdenpos :
      0 < (roundedOrbit A ρ (h₀ N) (s N) + fixedPrecisionScale N) *
        Real.log N :=
    mul_pos (add_pos_of_nonneg_of_pos hb ha) hlog
  have hid :
      ω (s N) * Real.log N =
        roundedOrbit A ρ (h₀ N) (s N) * Real.log N +
          normalizedRadiusError A ρ (h₀ N) (fixedPrecisionScale N) (s N) ω *
            ((roundedOrbit A ρ (h₀ N) (s N) + fixedPrecisionScale N) *
              Real.log N) := by
    rw [normalizedRadiusError, radiusTrackingError]
    field_simp
    ring
  have hprod :
      η / 2 <
        normalizedRadiusError A ρ (h₀ N) (fixedPrecisionScale N) (s N) ω *
          ((roundedOrbit A ρ (h₀ N) (s N) + fixedPrecisionScale N) *
            Real.log N) := by
    rw [hid] at hω
    nlinarith
  have hRpos :
      0 < normalizedRadiusError A ρ (h₀ N) (fixedPrecisionScale N) (s N) ω := by
    nlinarith
  rw [abs_of_pos hRpos]
  nlinarith

/-- **Upper half of the fixed-precision dimension cutoff.**  Two steps after
the deterministic terminal-scale entrance, the rounded squared-radius chain
has vanishing mass away from the absorbing origin.  This combines the
terminal-radius convergence in probability, the one-step Markov split, and
the vanishing Gaussian escape rate exactly as in the paper. -/
lemma tendsto_measureReal_Hkernel_pow_cutoff_add_two
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((Hkernel A ρ N) ^
            (roundedDimensionCutoffTime A ρ N (x N) + 2))
          (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}ᶜ)
      Filter.atTop (𝓝 0) := by
  let b := roundedLayerThreshold ρ 0
  let η := b ^ 2 / (4 * A ^ 2)
  have hb : 0 < b := by
    dsimp [b]
    exact roundedLayerThreshold_zero_pos hρ hρ_lt
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hη_lt : η < roundedLayerThreshold ρ 0 ^ 2 / (2 * A ^ 2) := by
    dsimp [η, b]
    have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
    have hb2 : 0 < roundedLayerThreshold ρ 0 ^ 2 :=
      sq_pos_of_pos (roundedLayerThreshold_zero_pos hρ hρ_lt)
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) hA2)
      (mul_pos (by norm_num) hA2)]
    nlinarith
  have hterminal :=
    tendsto_measureReal_terminal_radius_mul_log_gt
      hA hA_lt hρ hρ_lt x hx hη
  have hmass :
      Filter.Tendsto
        (fun N : ℕ =>
          (((Hkernel A ρ N) ^
              (roundedDimensionCutoffHorizon A ρ N (x N)))
            (roundedInitialRadius ρ N (x N))).real
              (Set.Ioi (η / Real.log N)))
        Filter.atTop (𝓝 0) := by
    have heq :
        (fun N : ℕ =>
          (((Hkernel A ρ N) ^
              (roundedDimensionCutoffHorizon A ρ N (x N)))
            (roundedInitialRadius ρ N (x N))).real
              (Set.Ioi (η / Real.log N))) =ᶠ[Filter.atTop]
        (fun N : ℕ =>
          (markovPathMeasure
              (Measure.dirac (roundedInitialRadius ρ N (x N)))
              (Hkernel A ρ N)).real
            {ω |
              η < ω (roundedDimensionCutoffHorizon A ρ N (x N)) *
                Real.log N}) := by
      filter_upwards [Filter.eventually_gt_atTop 1] with N hN
      exact measureReal_Hkernel_pow_Ioi_div_log_eq
        A ρ η (roundedInitialRadius ρ N (x N)) hN
          (roundedDimensionCutoffHorizon A ρ N (x N))
    rw [Filter.tendsto_congr' heq]
    exact hterminal
  have hescape :=
    tendsto_escape_at_eta_atTop hA hρ hρ_lt hη hη_lt
  have hupper :
      Filter.Tendsto
        (fun N : ℕ =>
          (((Hkernel A ρ N) ^
              (roundedDimensionCutoffHorizon A ρ N (x N)))
            (roundedInitialRadius ρ N (x N))).real
              (Set.Ioi (η / Real.log N)) +
            2 * N *
              Real.exp
                (-((roundedLayerThreshold ρ 0 /
                  (A * Real.sqrt (η / Real.log N))) ^ 2) / 2))
        Filter.atTop (𝓝 0) :=
    by simpa using hmass.add hescape
  refine squeeze_zero'
    (g := fun N : ℕ =>
      (((Hkernel A ρ N) ^
          (roundedDimensionCutoffHorizon A ρ N (x N)))
        (roundedInitialRadius ρ N (x N))).real
          (Set.Ioi (η / Real.log N)) +
        2 * N *
          Real.exp
            (-((roundedLayerThreshold ρ 0 /
              (A * Real.sqrt (η / Real.log N))) ^ 2) / 2))
    (Filter.Eventually.of_forall fun N => by positivity) ?_ hupper
  filter_upwards [Filter.eventually_gt_atTop 1] with N hN
  simpa only [roundedDimensionCutoffHorizon, Nat.add_assoc,
    show roundedDimensionCutoffTime A ρ N (x N) + 1 + 1 =
      roundedDimensionCutoffTime A ρ N (x N) + 2 by omega] using
    measureReal_Hkernel_pow_succ_compl_singleton_zero_le
      hA hρ hρ_lt hη hN
      (roundedInitialRadius_nonneg ρ N (x N))
      (roundedDimensionCutoffHorizon A ρ N (x N))

/-- **Lower half of the fixed-precision dimension cutoff.**  If the
deterministic terminal-scale entrance time diverges, then one step before
that entrance the rounded squared-radius chain is still off the absorbing
origin with probability tending to one.  Indeed, the deterministic orbit is
strictly above `a_N` there, so an exact radius equal to zero forces normalized
tracking error greater than `1/2`. -/
lemma tendsto_measureReal_Hkernel_pow_cutoff_sub_one_compl
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
        (((Hkernel A ρ N) ^
            (roundedDimensionCutoffTime A ρ N (x N) - 1))
          (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}ᶜ)
      Filter.atTop (𝓝 1) := by
  let T : ℕ → ℕ :=
    fun N => roundedDimensionCutoffHorizon A ρ N (x N)
  have hconc :=
    subcritical_exact_radius_concentration hA hA_lt hρ hρ_lt x hx T
      (by
        simpa only [T] using
          roundedDimensionCutoffHorizon_rate hA hA_lt hρ x hx)
      (1 / 2) (by norm_num)
  have hzeroPath :
      Filter.Tendsto
        (fun N : ℕ =>
          (markovPathMeasure
              (Measure.dirac (roundedInitialRadius ρ N (x N)))
              (Hkernel A ρ N)).real
            {ω |
              ω (roundedDimensionCutoffTime A ρ N (x N) - 1) = 0})
        Filter.atTop (𝓝 0) := by
    refine squeeze_zero'
      (g := fun N : ℕ =>
        (markovPathMeasure
            (Measure.dirac (roundedInitialRadius ρ N (x N)))
            (Hkernel A ρ N)).real
          {ω | ∃ t ≤ T N,
            1 / 2 <
              |normalizedRadiusError A ρ
                (roundedInitialRadius ρ N (x N))
                (fixedPrecisionScale N) t ω|})
      (Filter.Eventually.of_forall fun N => by positivity) ?_ hconc
    have htime_pos :
        ∀ᶠ N : ℕ in Filter.atTop,
          0 < roundedDimensionCutoffTime A ρ N (x N) :=
      htime.eventually (Filter.eventually_gt_atTop 0)
    filter_upwards [htime_pos, Filter.eventually_gt_atTop 1]
      with N htpos hN
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    let t := roundedDimensionCutoffTime A ρ N (x N) - 1
    let h₀ := roundedInitialRadius ρ N (x N)
    let a := fixedPrecisionScale N
    let hbar := roundedOrbit A ρ h₀ t
    have ht_lt : t < roundedDimensionCutoffTime A ρ N (x N) := by
      dsimp [t]
      omega
    have hbar_gt : a < hbar := by
      dsimp [a, hbar, h₀]
      exact roundedOrbit_lt_entrance
        (A := A) (ρ := ρ)
        (h₀ := roundedInitialRadius ρ N (x N))
        (r := fixedPrecisionScale N)
        (by
          simpa only [roundedDimensionCutoffTime] using ht_lt)
    have ha : 0 < a := by
      dsimp [a]
      exact fixedPrecisionScale_pos hN
    have hbar_nonneg : 0 ≤ hbar := by
      dsimp [hbar, h₀]
      exact roundedOrbit_nonneg
        (roundedInitialRadius_nonneg ρ N (x N)) t
    have hden : 0 < hbar + a := add_pos_of_nonneg_of_pos hbar_nonneg ha
    refine ⟨t, ?_, ?_⟩
    · dsimp [t, T, roundedDimensionCutoffHorizon]
      omega
    · change ω t = 0 at hω
      change 1 / 2 <
        |normalizedRadiusError A ρ h₀ a t ω|
      rw [normalizedRadiusError, radiusTrackingError, hω, zero_sub,
        abs_div, abs_neg, abs_of_nonneg hbar_nonneg, abs_of_pos hden,
        lt_div_iff₀ hden]
      nlinarith
  have hzeroKernel :
      Filter.Tendsto
        (fun N : ℕ =>
          (((Hkernel A ρ N) ^
              (roundedDimensionCutoffTime A ρ N (x N) - 1))
            (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)})
        Filter.atTop (𝓝 0) := by
    have heq :
        (fun N : ℕ =>
          (((Hkernel A ρ N) ^
              (roundedDimensionCutoffTime A ρ N (x N) - 1))
            (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}) =ᶠ[Filter.atTop]
        (fun N : ℕ =>
          (markovPathMeasure
              (Measure.dirac (roundedInitialRadius ρ N (x N)))
              (Hkernel A ρ N)).real
            {ω |
              ω (roundedDimensionCutoffTime A ρ N (x N) - 1) = 0}) := by
      exact Filter.Eventually.of_forall fun N => by
        change
          (((Hkernel A ρ N) ^
              (roundedDimensionCutoffTime A ρ N (x N) - 1))
            (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)} =
          (markovPathMeasure
              (Measure.dirac (roundedInitialRadius ρ N (x N)))
              (Hkernel A ρ N)).real
            {ω |
              ω (roundedDimensionCutoffTime A ρ N (x N) - 1) = 0}
        rw [measureReal_def, measureReal_def,
          ← markovPathMeasure_dirac_map_eval
            (roundedInitialRadius ρ N (x N)) (Hkernel A ρ N)
            (roundedDimensionCutoffTime A ρ N (x N) - 1),
          Measure.map_apply
            (measurable_pi_apply
              (roundedDimensionCutoffTime A ρ N (x N) - 1))
            (measurableSet_singleton (0 : ℝ))]
        congr 2
    rw [Filter.tendsto_congr' heq]
    exact hzeroPath
  have heqCompl :
      (fun N : ℕ =>
        (((Hkernel A ρ N) ^
            (roundedDimensionCutoffTime A ρ N (x N) - 1))
          (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}ᶜ) =
        (fun N : ℕ =>
          1 -
            (((Hkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) - 1))
              (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}) := by
    funext N
    rw [measureReal_compl (measurableSet_singleton (0 : ℝ)), probReal_univ]
  rw [heqCompl]
  simpa using tendsto_const_nhds.sub hzeroKernel

/-- **Fixed-precision subcritical dimension cutoff**
(`thm:subcritical-dimension-cutoff`, scalar-radius/path-space form).  If the
deterministic cutoff location diverges, the rounded squared-radius chain
survives to time `bar t_N - 1` with probability tending to one and survives
to time `bar t_N + 2` with probability tending to zero.  Equivalently, its
total-variation distance from the absorbing point mass has the same two
limits.

The exact rounded-vector counterpart is
`subcritical_dimension_cutoff_roundedVector` in
`AbsorptionCutoff.RoundedVectorReduction`. -/
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
    (Filter.Tendsto
        (fun N : ℕ =>
          (markovPathMeasure
              (Measure.dirac (roundedInitialRadius ρ N (x N)))
              (Hkernel A ρ N)).real
            {ω |
              ((roundedDimensionCutoffTime A ρ N (x N) - 1 : ℕ) :
                  WithTop ℕ) <
                absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω})
        Filter.atTop (𝓝 1) ∧
      Filter.Tendsto
        (fun N : ℕ =>
          (markovPathMeasure
              (Measure.dirac (roundedInitialRadius ρ N (x N)))
              (Hkernel A ρ N)).real
            {ω |
              ((roundedDimensionCutoffTime A ρ N (x N) + 2 : ℕ) :
                  WithTop ℕ) <
                absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω})
        Filter.atTop (𝓝 0)) ∧
    (Filter.Tendsto
        (fun N : ℕ =>
          tvDist
            (((Hkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) - 1))
              (roundedInitialRadius ρ N (x N)))
            (Measure.dirac 0))
        Filter.atTop (𝓝 1) ∧
      Filter.Tendsto
        (fun N : ℕ =>
          tvDist
            (((Hkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) + 2))
              (roundedInitialRadius ρ N (x N)))
            (Measure.dirac 0))
        Filter.atTop (𝓝 0)) := by
  have hlower :=
    tendsto_measureReal_Hkernel_pow_cutoff_sub_one_compl
      hA hA_lt hρ hρ_lt x hx htime
  have hupper :=
    tendsto_measureReal_Hkernel_pow_cutoff_add_two
      hA hA_lt hρ hρ_lt x hx
  have hsurvLowerEq :
      (fun N : ℕ =>
        (markovPathMeasure
            (Measure.dirac (roundedInitialRadius ρ N (x N)))
            (Hkernel A ρ N)).real
          {ω |
            ((roundedDimensionCutoffTime A ρ N (x N) - 1 : ℕ) :
                WithTop ℕ) <
              absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω}) =
      (fun N : ℕ =>
        (((Hkernel A ρ N) ^
            (roundedDimensionCutoffTime A ρ N (x N) - 1))
          (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}ᶜ) := by
    funext N
    rw [measureReal_def,
      measure_roundedAbsorptionTime_gt_eq
        A ρ N (roundedInitialRadius ρ N (x N))
          (roundedDimensionCutoffTime A ρ N (x N) - 1)]
    rfl
  have hsurvUpperEq :
      (fun N : ℕ =>
        (markovPathMeasure
            (Measure.dirac (roundedInitialRadius ρ N (x N)))
            (Hkernel A ρ N)).real
          {ω |
            ((roundedDimensionCutoffTime A ρ N (x N) + 2 : ℕ) :
                WithTop ℕ) <
              absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω}) =
      (fun N : ℕ =>
        (((Hkernel A ρ N) ^
            (roundedDimensionCutoffTime A ρ N (x N) + 2))
          (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}ᶜ) := by
    funext N
    rw [measureReal_def,
      measure_roundedAbsorptionTime_gt_eq
        A ρ N (roundedInitialRadius ρ N (x N))
          (roundedDimensionCutoffTime A ρ N (x N) + 2)]
    rfl
  have htvLowerEq :
      (fun N : ℕ =>
        tvDist
          (((Hkernel A ρ N) ^
              (roundedDimensionCutoffTime A ρ N (x N) - 1))
            (roundedInitialRadius ρ N (x N)))
          (Measure.dirac 0)) =
      (fun N : ℕ =>
        (((Hkernel A ρ N) ^
            (roundedDimensionCutoffTime A ρ N (x N) - 1))
          (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}ᶜ) := by
    funext N
    exact tvDist_Hkernel_pow_dirac
      A ρ N (roundedInitialRadius ρ N (x N))
        (roundedDimensionCutoffTime A ρ N (x N) - 1)
  have htvUpperEq :
      (fun N : ℕ =>
        tvDist
          (((Hkernel A ρ N) ^
              (roundedDimensionCutoffTime A ρ N (x N) + 2))
            (roundedInitialRadius ρ N (x N)))
          (Measure.dirac 0)) =
      (fun N : ℕ =>
        (((Hkernel A ρ N) ^
            (roundedDimensionCutoffTime A ρ N (x N) + 2))
          (roundedInitialRadius ρ N (x N))).real {(0 : ℝ)}ᶜ) := by
    funext N
    exact tvDist_Hkernel_pow_dirac
      A ρ N (roundedInitialRadius ρ N (x N))
        (roundedDimensionCutoffTime A ρ N (x N) + 2)
  rw [hsurvLowerEq, hsurvUpperEq, htvLowerEq, htvUpperEq]
  exact ⟨⟨hlower, hupper⟩, ⟨hlower, hupper⟩⟩

/-- **Mixing-time consequence of the fixed-precision cutoff.**  For every
fixed `ε ∈ (0,1)`, the scalar rounded-radius mixing time is eventually
strictly after `bar t_N - 1` and at most `bar t_N + 2`.  This is the precise
eventual-bound form of the paper's
`t_mix^(N)(ε) = bar t_N + O(1)`. -/
theorem subcritical_dimension_cutoff_mixingTime_bounds
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1)
    (htime :
      Filter.Tendsto
        (fun N : ℕ => roundedDimensionCutoffTime A ρ N (x N))
        Filter.atTop Filter.atTop)
    {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((roundedDimensionCutoffTime A ρ N (x N) - 1 : ℕ) : ℕ∞) <
          mixingTime
            (dSeq (Hkernel A ρ N) (roundedInitialRadius ρ N (x N))
              (Measure.dirac 0))
            ε ∧
        mixingTime
            (dSeq (Hkernel A ρ N) (roundedInitialRadius ρ N (x N))
              (Measure.dirac 0))
            ε ≤
          ((roundedDimensionCutoffTime A ρ N (x N) + 2 : ℕ) : ℕ∞) := by
  have hcut :=
    subcritical_dimension_cutoff hA hA_lt hρ hρ_lt x hx htime
  have hlower := hcut.2.1
  have hupper := hcut.2.2
  have hlowerEventually :
      ∀ᶠ N : ℕ in Filter.atTop,
        ε <
          tvDist
            (((Hkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) - 1))
              (roundedInitialRadius ρ N (x N)))
            (Measure.dirac 0) :=
    (tendsto_order.1 hlower).1 ε hε_lt
  have hupperEventually :
      ∀ᶠ N : ℕ in Filter.atTop,
        tvDist
            (((Hkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) + 2))
              (roundedInitialRadius ρ N (x N)))
            (Measure.dirac 0) < ε :=
    (tendsto_order.1 hupper).2 ε hε
  filter_upwards [hlowerEventually, hupperEventually]
    with N hlowerN hupperN
  let d :=
    dSeq (Hkernel A ρ N) (roundedInitialRadius ρ N (x N))
      (Measure.dirac 0)
  let tLower := roundedDimensionCutoffTime A ρ N (x N) - 1
  let tUpper := roundedDimensionCutoffTime A ρ N (x N) + 2
  have hlowerD : ε < d tLower := by
    simpa only [d, tLower, dSeq] using hlowerN
  have hupperD : d tUpper ≤ ε := by
    exact (by simpa only [d, tUpper, dSeq] using hupperN.le)
  constructor
  · rw [mixingTime, lt_sInf_iff]
    refine ⟨((tLower + 1 : ℕ) : ℕ∞), ?_, ?_⟩
    · simpa only [tLower, ENat.coe_lt_coe] using Nat.lt_succ_self tLower
    · intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      have htu : tLower < u := by
        by_contra hnot
        have hut : u ≤ tLower := not_lt.mp hnot
        have hmono : d tLower ≤ d u :=
          dSeq_Hkernel_dirac_antitone A ρ N
            (roundedInitialRadius ρ N (x N)) hut
        exact (not_le_of_gt hlowerD) (hmono.trans hu)
      exact_mod_cast (Nat.succ_le_iff.mpr htu)
  · rw [mixingTime]
    apply sInf_le
    exact ⟨tUpper, hupperD, rfl⟩

end AbsorptionCutoff
