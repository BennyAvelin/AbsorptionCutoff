/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Logarithmic entrance for affine recursions

Begins the deterministic scaffold for the paper's
`lem:negative-drift-affine-entrance`. Given multipliers `M₁,M₂,…`, additive drift `b`,
and initial value `K`, the pathwise recursion is
`U₀ = K`, `U_{t+1} = M_{t+1} U_t + b`.
-/

open Filter MeasureTheory ProbabilityTheory Topology

namespace AbsorptionCutoff

/-- The pathwise affine recursion `U₀ = K`, `U_{t+1} = M_{t+1}U_t + b`. -/
def affineRecursion (M : ℕ → ℝ) (b K : ℝ) : ℕ → ℝ
  | 0 => K
  | t + 1 => M (t + 1) * affineRecursion M b K t + b

@[simp] lemma affineRecursion_zero (M : ℕ → ℝ) (b K : ℝ) :
    affineRecursion M b K 0 = K := rfl

@[simp] lemma affineRecursion_succ (M : ℕ → ℝ) (b K : ℝ) (t : ℕ) :
    affineRecursion M b K (t + 1) =
      M (t + 1) * affineRecursion M b K t + b := rfl

/-- First entrance time of the affine recursion into `(-∞, Kstar]`, with value `⊤`
if the level is never reached. -/
noncomputable def affineEntranceTime (M : ℕ → ℝ) (b K Kstar : ℝ) : ℕ∞ :=
  sInf ((Nat.cast : ℕ → ℕ∞) '' {t | affineRecursion M b K t ≤ Kstar})

/-- The recursion survives strictly above `Kstar` through time `n` exactly when the
first entrance time into `(-∞, Kstar]` exceeds `n`. -/
lemma lt_affineEntranceTime_iff (M : ℕ → ℝ) (b K Kstar : ℝ) (n : ℕ) :
    (n : ℕ∞) < affineEntranceTime M b K Kstar ↔
      ∀ j ≤ n, Kstar < affineRecursion M b K j := by
  unfold affineEntranceTime
  constructor
  · intro hlt j hj
    by_contra hcon
    have hmem : (j : ℕ∞) ∈
        (Nat.cast : ℕ → ℕ∞) '' {t | affineRecursion M b K t ≤ Kstar} :=
      ⟨j, not_lt.mp hcon, rfl⟩
    have hle : (n : ℕ∞) < (j : ℕ∞) := hlt.trans_le (sInf_le hmem)
    exact absurd (by exact_mod_cast hle : n < j) (Nat.not_lt.mpr hj)
  · intro hall
    refine (ENat.add_one_le_iff (by simp)).mp ?_
    rw [le_sInf_iff]
    rintro x ⟨t, ht, rfl⟩
    have hnt : n < t := by
      by_contra hle
      exact absurd ht (not_le.mpr (hall t (not_lt.mp hle)))
    exact_mod_cast Nat.succ_le_of_lt hnt

/-- The paper's one-step comparison before entrance: if `b ≤ ε Kstar` and the current
state is at least `Kstar`, then the additive recursion is dominated by multiplication
by `M_{t+1}+ε`. -/
lemma affineRecursion_succ_le_mul_add (M : ℕ → ℝ) (b K Kstar ε : ℝ) (t : ℕ)
    (hε : 0 ≤ ε) (hb : b ≤ ε * Kstar)
    (hU : Kstar ≤ affineRecursion M b K t) :
    affineRecursion M b K (t + 1) ≤
      (M (t + 1) + ε) * affineRecursion M b K t := by
  rw [affineRecursion_succ]
  calc
    M (t + 1) * affineRecursion M b K t + b
        ≤ M (t + 1) * affineRecursion M b K t + ε * Kstar :=
      add_le_add le_rfl hb
    _ ≤ M (t + 1) * affineRecursion M b K t +
          ε * affineRecursion M b K t :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hU hε)
    _ = (M (t + 1) + ε) * affineRecursion M b K t := by ring

/-- Iterating the one-step comparison along a path that remains above `Kstar` gives
the product bound `U_n ≤ K ∏_{j<n}(M_{j+1}+ε)`. -/
lemma affineRecursion_le_mul_prod (M : ℕ → ℝ) (b K Kstar ε : ℝ) (n : ℕ)
    (hM : ∀ j, 0 ≤ M j) (hε : 0 ≤ ε) (hb : b ≤ ε * Kstar)
    (hstay : ∀ j < n, Kstar ≤ affineRecursion M b K j) :
    affineRecursion M b K n ≤ K * ∏ j ∈ Finset.range n, (M (j + 1) + ε) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := affineRecursion_succ_le_mul_add M b K Kstar ε n hε hb
        (hstay n (Nat.lt_succ_self n))
      have hprod_nonneg : 0 ≤ M (n + 1) + ε := add_nonneg (hM _) hε
      calc
        affineRecursion M b K (n + 1)
            ≤ (M (n + 1) + ε) * affineRecursion M b K n := hstep
        _ ≤ (M (n + 1) + ε) *
              (K * ∏ j ∈ Finset.range n, (M (j + 1) + ε)) :=
          mul_le_mul_of_nonneg_left
            (ih (fun j hj => hstay j (hj.trans (Nat.lt_succ_self n)))) hprod_nonneg
        _ = K * ∏ j ∈ Finset.range (n + 1), (M (j + 1) + ε) := by
          rw [Finset.prod_range_succ]
          ring

/-- If the recursion is still above `Kstar` at time `n`, the product domination forces
the associated log-increment sum above the paper's threshold `-log(K/Kstar)`. -/
lemma neg_log_div_lt_sum_log_of_affineRecursion (M : ℕ → ℝ) (b K Kstar ε : ℝ) (n : ℕ)
    (hK : 0 < K) (hKstar : 0 < Kstar) (hM : ∀ j, 0 ≤ M j) (hε : 0 ≤ ε)
    (hfac : ∀ j, 0 < M (j + 1) + ε) (hb : b ≤ ε * Kstar)
    (hstay : ∀ j < n, Kstar ≤ affineRecursion M b K j)
    (hUn : Kstar < affineRecursion M b K n) :
    -Real.log (K / Kstar) <
      ∑ j ∈ Finset.range n, Real.log (M (j + 1) + ε) := by
  have hbound := affineRecursion_le_mul_prod M b K Kstar ε n hM hε hb hstay
  have hprod_pos : 0 < ∏ j ∈ Finset.range n, (M (j + 1) + ε) :=
    Finset.prod_pos fun j _ => hfac j
  have hlog :
      Real.log Kstar <
        Real.log (K * ∏ j ∈ Finset.range n, (M (j + 1) + ε)) :=
    Real.log_lt_log hKstar (hUn.trans_le hbound)
  rw [Real.log_mul hK.ne' hprod_pos.ne',
    Real.log_prod (fun j _ => (hfac j).ne')] at hlog
  rw [Real.log_div hK.ne' hKstar.ne']
  linarith

/-- Chernoff's upper-tail bound for a finite sum of independent real random variables,
with the mgf of the sum factored into the product of the individual mgfs. -/
theorem measure_sum_ge_le_exp_mul_prod_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (n : ℕ) (s a : ℝ)
    (hs : 0 ≤ s) (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ)
    (hint : Integrable
      (fun ω => Real.exp (s * (∑ j ∈ Finset.range n, X j ω))) μ) :
    μ.real {ω | a ≤ ∑ j ∈ Finset.range n, X j ω} ≤
      Real.exp (-s * a) * ∏ j ∈ Finset.range n, mgf (X j) μ s := by
  calc
    μ.real {ω | a ≤ ∑ j ∈ Finset.range n, X j ω}
        ≤ Real.exp (-s * a) *
            mgf (fun ω => ∑ j ∈ Finset.range n, X j ω) μ s :=
      measure_ge_le_exp_mul_mgf a hs hint
    _ = Real.exp (-s * a) * ∏ j ∈ Finset.range n, mgf (X j) μ s := by
      have hfun :
          (fun ω => ∑ j ∈ Finset.range n, X j ω) =
            ∑ j ∈ Finset.range n, X j := by
        funext ω
        simp
      rw [hfun, hind.mgf_sum hX]

/-- Iid specialization of `measure_sum_ge_le_exp_mul_prod_mgf`: all individual mgf
factors equal the mgf of `X₀`, so the product is its `n`-th power. -/
theorem measure_sum_ge_le_exp_mul_mgf_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (n : ℕ) (s a : ℝ)
    (hs : 0 ≤ s) (hX : ∀ j, Measurable (X j)) (hind : iIndepFun X μ)
    (hident : ∀ j, IdentDistrib (X j) (X 0) μ μ)
    (hint : Integrable
      (fun ω => Real.exp (s * (∑ j ∈ Finset.range n, X j ω))) μ) :
    μ.real {ω | a ≤ ∑ j ∈ Finset.range n, X j ω} ≤
      Real.exp (-s * a) * mgf (X 0) μ s ^ n := by
  calc
    μ.real {ω | a ≤ ∑ j ∈ Finset.range n, X j ω}
        ≤ Real.exp (-s * a) * ∏ j ∈ Finset.range n, mgf (X j) μ s :=
      measure_sum_ge_le_exp_mul_prod_mgf μ X n s a hs hX hind hint
    _ = Real.exp (-s * a) * mgf (X 0) μ s ^ n := by
      congr 1
      calc
        (∏ j ∈ Finset.range n, mgf (X j) μ s) =
            ∏ _j ∈ Finset.range n, mgf (X 0) μ s := by
          apply Finset.prod_congr rfl
          intro j _
          exact mgf_congr_of_identDistrib (X j) (X 0) (hident j) s
        _ = mgf (X 0) μ s ^ n := by simp

/-- The event that the random affine recursion remains strictly above `Kstar` through
time `n`. -/
def affineSurvivalSet {Ω : Type*} (M : ℕ → Ω → ℝ) (b K Kstar : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j ≤ n, Kstar < affineRecursion (fun k => M k ω) b K j}

/-- The survival event is exactly the event that the pathwise entrance time exceeds `n`,
matching the paper's `\{T > n\}` with `T = inf\{t : U_t ≤ K_*\}`. -/
lemma affineSurvivalSet_eq_lt_affineEntranceTime {Ω : Type*} (M : ℕ → Ω → ℝ)
    (b K Kstar : ℝ) (n : ℕ) :
    affineSurvivalSet M b K Kstar n =
      {ω | (n : ℕ∞) < affineEntranceTime (fun k => M k ω) b K Kstar} := by
  ext ω
  simp only [affineSurvivalSet, Set.mem_setOf_eq, lt_affineEntranceTime_iff]

/-- Survival through time `n` forces the log-increment sum into the upper-tail event
used in the Chernoff estimate. -/
lemma affineSurvivalSet_subset_log_sum {Ω : Type*} (M : ℕ → Ω → ℝ)
    (b K Kstar ε : ℝ) (n : ℕ) (hK : 0 < K) (hKstar : 0 < Kstar)
    (hM : ∀ ω j, 0 ≤ M j ω) (hε : 0 ≤ ε)
    (hfac : ∀ ω j, 0 < M (j + 1) ω + ε) (hb : b ≤ ε * Kstar) :
    affineSurvivalSet M b K Kstar n ⊆
      {ω | -Real.log (K / Kstar) <
        ∑ j ∈ Finset.range n, Real.log (M (j + 1) ω + ε)} := by
  intro ω hsurv
  apply neg_log_div_lt_sum_log_of_affineRecursion
    (fun k => M k ω) b K Kstar ε n hK hKstar (hM ω) hε (hfac ω) hb
  · intro j hj
    exact (hsurv j (Nat.le_of_lt hj)).le
  · exact hsurv n le_rfl

/-- The shifted log-increments `log(M_{j+1}+ε)` used in the affine-entrance random walk. -/
noncomputable def logAffineIncrement {Ω : Type*} (ε : ℝ) (M : ℕ → Ω → ℝ)
    (j : ℕ) (ω : Ω) : ℝ :=
  Real.log (M (j + 1) ω + ε)

/-- The shifted log-increments are measurable when the multipliers are measurable. -/
lemma measurable_logAffineIncrement {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (M : ℕ → Ω → ℝ) (hM : ∀ j, Measurable (M j)) (j : ℕ) :
    Measurable (logAffineIncrement ε M j) := by
  have hlog : Measurable Real.log :=
    measurable_of_continuousOn_compl_singleton 0 Real.continuousOn_log
  exact hlog.comp ((hM (j + 1)).add_const ε)

/-- Independence is preserved when shifting the multiplier sequence and applying
`x ↦ log(x+ε)` coordinatewise. -/
lemma iIndepFun_logAffineIncrement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ℝ) (M : ℕ → Ω → ℝ) (hind : iIndepFun M μ) :
    iIndepFun (logAffineIncrement ε M) μ := by
  have hshift : iIndepFun (fun j => M (j + 1)) μ :=
    hind.precomp Nat.succ_injective
  have htransform : Measurable (fun x : ℝ => Real.log (x + ε)) := by
    have hlog : Measurable Real.log :=
      measurable_of_continuousOn_compl_singleton 0 Real.continuousOn_log
    exact hlog.comp (measurable_id.add_const ε)
  change iIndepFun (fun j ω => Real.log (M (j + 1) ω + ε)) μ
  simpa only [Function.comp_def] using
    hshift.comp (fun _ => fun x : ℝ => Real.log (x + ε)) (fun _ => htransform)

/-- Identical distribution of shifted multipliers transfers to their log-increments. -/
lemma identDistrib_logAffineIncrement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ℝ) (M : ℕ → Ω → ℝ)
    (hident : ∀ j, IdentDistrib (M (j + 1)) (M 1) μ μ) (j : ℕ) :
    IdentDistrib (logAffineIncrement ε M j) (logAffineIncrement ε M 0) μ μ := by
  have htransform : Measurable (fun x : ℝ => Real.log (x + ε)) := by
    have hlog : Measurable Real.log :=
      measurable_of_continuousOn_compl_singleton 0 Real.continuousOn_log
    exact hlog.comp (measurable_id.add_const ε)
  change IdentDistrib (fun ω => Real.log (M (j + 1) ω + ε))
    (fun ω => Real.log (M 1 ω + ε)) μ μ
  simpa only [Function.comp_def] using (hident j).comp htransform

/-- A single exponential moment of `log(M₁+ε)` at parameter `s` propagates, via
independence and identical distribution, to integrability of the finite-sum exponential
`exp(s·∑_{j<n} log(M_{j+1}+ε))` — the integrability hypothesis of the Chernoff bounds. -/
lemma integrable_exp_mul_sum_logAffineIncrement {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ε : ℝ) (M : ℕ → Ω → ℝ) (n : ℕ) (s : ℝ)
    (hM_meas : ∀ j, Measurable (M j))
    (hind : iIndepFun M μ)
    (hident : ∀ j, IdentDistrib (M (j + 1)) (M 1) μ μ)
    (hint0 : Integrable (fun ω => Real.exp (s * logAffineIncrement ε M 0 ω)) μ) :
    Integrable (fun ω => Real.exp
      (s * (∑ j ∈ Finset.range n, logAffineIncrement ε M j ω))) μ := by
  have hexp : Measurable (fun x : ℝ => Real.exp (s * x)) := by fun_prop
  have hfun :
      (fun ω => Real.exp (s * ∑ j ∈ Finset.range n, logAffineIncrement ε M j ω)) =
        (fun ω => Real.exp
          (s * (∑ j ∈ Finset.range n, logAffineIncrement ε M j) ω)) := by
    funext ω; simp
  rw [hfun]
  refine (iIndepFun_logAffineIncrement μ ε M hind).integrable_exp_mul_sum
    (measurable_logAffineIncrement ε M hM_meas) ?_
  intro j _
  have hid := (identDistrib_logAffineIncrement μ ε M hident j).comp hexp
  exact hid.integrable_iff.mpr hint0

/-- The random affine recursion at each fixed time is measurable when all multipliers
are measurable. -/
lemma measurable_affineRecursion {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ → Ω → ℝ) (b K : ℝ) (hM : ∀ j, Measurable (M j)) :
    ∀ n, Measurable (fun ω => affineRecursion (fun k => M k ω) b K n)
  | 0 => measurable_const
  | n + 1 => by
      simp only [affineRecursion_succ]
      exact ((hM (n + 1)).mul (measurable_affineRecursion M b K hM n)).add_const b

/-- The event that the random affine recursion survives above `Kstar` through a fixed
finite time is measurable. -/
lemma measurableSet_affineSurvivalSet {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ → Ω → ℝ) (b K Kstar : ℝ) (n : ℕ) (hM : ∀ j, Measurable (M j)) :
    MeasurableSet (affineSurvivalSet M b K Kstar n) := by
  rw [show affineSurvivalSet M b K Kstar n =
      ⋂ j : ℕ, {ω | j ≤ n → Kstar < affineRecursion (fun k => M k ω) b K j} by
    ext ω
    simp [affineSurvivalSet]]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j ≤ n
  · simp only [hj, true_implies]
    exact measurableSet_lt measurable_const (measurable_affineRecursion M b K hM j)
  · simp [hj]

/-- Finite-time Chernoff bound for survival of the affine recursion above `Kstar`. -/
theorem measureReal_affineSurvivalSet_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (b K Kstar ε : ℝ) (n : ℕ) (s : ℝ)
    (hK : 0 < K) (hKstar : 0 < Kstar) (hM_nonneg : ∀ ω j, 0 ≤ M j ω)
    (hε : 0 ≤ ε) (hfac : ∀ ω j, 0 < M (j + 1) ω + ε)
    (hb : b ≤ ε * Kstar) (hM_meas : ∀ j, Measurable (M j))
    (hind : iIndepFun M μ)
    (hident : ∀ j, IdentDistrib (M (j + 1)) (M 1) μ μ)
    (hs : 0 ≤ s)
    (hint : Integrable
      (fun ω => Real.exp
        (s * (∑ j ∈ Finset.range n, logAffineIncrement ε M j ω))) μ) :
    μ.real (affineSurvivalSet M b K Kstar n) ≤
      Real.exp (s * Real.log (K / Kstar)) *
        mgf (logAffineIncrement ε M 0) μ s ^ n := by
  have hsub :
      affineSurvivalSet M b K Kstar n ⊆
        {ω | -Real.log (K / Kstar) ≤
          ∑ j ∈ Finset.range n, logAffineIncrement ε M j ω} := by
    intro ω hω
    change -Real.log (K / Kstar) ≤
      ∑ j ∈ Finset.range n, logAffineIncrement ε M j ω
    apply le_of_lt
    have htail := affineSurvivalSet_subset_log_sum M b K Kstar ε n hK hKstar
      hM_nonneg hε hfac hb hω
    change -Real.log (K / Kstar) <
      ∑ j ∈ Finset.range n, Real.log (M (j + 1) ω + ε) at htail
    simpa only [logAffineIncrement] using htail
  calc
    μ.real (affineSurvivalSet M b K Kstar n)
        ≤ μ.real {ω | -Real.log (K / Kstar) ≤
            ∑ j ∈ Finset.range n, logAffineIncrement ε M j ω} :=
      measureReal_mono hsub
    _ ≤ Real.exp (-s * (-Real.log (K / Kstar))) *
          mgf (logAffineIncrement ε M 0) μ s ^ n :=
      measure_sum_ge_le_exp_mul_mgf_pow μ (logAffineIncrement ε M) n s
        (-Real.log (K / Kstar)) hs
        (measurable_logAffineIncrement ε M hM_meas)
        (iIndepFun_logAffineIncrement μ ε M hind)
        (identDistrib_logAffineIncrement μ ε M hident) hint
    _ = Real.exp (s * Real.log (K / Kstar)) *
          mgf (logAffineIncrement ε M 0) μ s ^ n := by ring_nf

/-- Exponential-in-time form of the finite survival bound when the log-increment mgf
is at most `exp(-c3)`. -/
theorem measureReal_affineSurvivalSet_le_exp_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (b K Kstar ε : ℝ) (n : ℕ) (s c3 : ℝ)
    (hK : 0 < K) (hKstar : 0 < Kstar) (hM_nonneg : ∀ ω j, 0 ≤ M j ω)
    (hε : 0 ≤ ε) (hfac : ∀ ω j, 0 < M (j + 1) ω + ε)
    (hb : b ≤ ε * Kstar) (hM_meas : ∀ j, Measurable (M j))
    (hind : iIndepFun M μ)
    (hident : ∀ j, IdentDistrib (M (j + 1)) (M 1) μ μ)
    (hs : 0 ≤ s)
    (hint : Integrable
      (fun ω => Real.exp
        (s * (∑ j ∈ Finset.range n, logAffineIncrement ε M j ω))) μ)
    (hmgf : mgf (logAffineIncrement ε M 0) μ s ≤ Real.exp (-c3)) :
    μ.real (affineSurvivalSet M b K Kstar n) ≤
      Real.exp (s * Real.log (K / Kstar) - c3 * n) := by
  calc
    μ.real (affineSurvivalSet M b K Kstar n)
        ≤ Real.exp (s * Real.log (K / Kstar)) *
            mgf (logAffineIncrement ε M 0) μ s ^ n :=
      measureReal_affineSurvivalSet_le μ M b K Kstar ε n s hK hKstar
        hM_nonneg hε hfac hb hM_meas hind hident hs hint
    _ ≤ Real.exp (s * Real.log (K / Kstar)) * Real.exp (-c3) ^ n := by
      gcongr
      exact mgf_nonneg
    _ = Real.exp (s * Real.log (K / Kstar) - c3 * n) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- The exponential survival estimate rewritten at times beyond
`(s / c3) * log K + r - 1`. -/
theorem measureReal_affineSurvivalSet_le_exp_mul_exp_neg {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → Ω → ℝ) (b K Kstar ε : ℝ) (n : ℕ) (s c3 r : ℝ)
    (hK : 0 < K) (hKstar : 0 < Kstar) (hM_nonneg : ∀ ω j, 0 ≤ M j ω)
    (hε : 0 ≤ ε) (hfac : ∀ ω j, 0 < M (j + 1) ω + ε)
    (hb : b ≤ ε * Kstar) (hM_meas : ∀ j, Measurable (M j))
    (hind : iIndepFun M μ)
    (hident : ∀ j, IdentDistrib (M (j + 1)) (M 1) μ μ)
    (hs : 0 ≤ s)
    (hint : Integrable
      (fun ω => Real.exp
        (s * (∑ j ∈ Finset.range n, logAffineIncrement ε M j ω))) μ)
    (hmgf : mgf (logAffineIncrement ε M 0) μ s ≤ Real.exp (-c3))
    (hc3 : 0 < c3)
    (hn : s / c3 * Real.log K + r - 1 < (n : ℝ)) :
    μ.real (affineSurvivalSet M b K Kstar n) ≤
      Real.exp (-s * Real.log Kstar + c3) * Real.exp (-c3 * r) := by
  calc
    μ.real (affineSurvivalSet M b K Kstar n)
        ≤ Real.exp (s * Real.log (K / Kstar) - c3 * n) :=
      measureReal_affineSurvivalSet_le_exp_sub μ M b K Kstar ε n s c3
        hK hKstar hM_nonneg hε hfac hb hM_meas hind hident hs hint hmgf
    _ ≤ Real.exp (-s * Real.log Kstar + c3) * Real.exp (-c3 * r) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [Real.log_div hK.ne' hKstar.ne']
      have htime := mul_lt_mul_of_pos_left hn hc3
      have hc3_ne : c3 ≠ 0 := ne_of_gt hc3
      field_simp [hc3_ne] at htime
      nlinarith

/-- The natural floor of the affine-entrance time parameter satisfies the strict
lower bound required by `measureReal_affineSurvivalSet_le_exp_mul_exp_neg`. -/
lemma affineThreshold_sub_one_lt_floor (s c3 K r : ℝ) :
    s / c3 * Real.log K + r - 1 <
      (⌊s / c3 * Real.log K + r⌋₊ : ℕ) := by
  exact Nat.sub_one_lt_floor _

/-- The affine survival estimate at the paper's floored logarithmic time, with a
prefactor enlarged to be at least one. -/
theorem measureReal_affineSurvivalSet_floor_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (b K Kstar ε : ℝ) (s c3 r : ℝ)
    (hK : 0 < K) (hKstar : 0 < Kstar) (hM_nonneg : ∀ ω j, 0 ≤ M j ω)
    (hε : 0 ≤ ε) (hfac : ∀ ω j, 0 < M (j + 1) ω + ε)
    (hb : b ≤ ε * Kstar) (hM_meas : ∀ j, Measurable (M j))
    (hind : iIndepFun M μ)
    (hident : ∀ j, IdentDistrib (M (j + 1)) (M 1) μ μ)
    (hs : 0 ≤ s)
    (hint : Integrable
      (fun ω => Real.exp
        (s * (∑ j ∈ Finset.range ⌊s / c3 * Real.log K + r⌋₊,
          logAffineIncrement ε M j ω))) μ)
    (hmgf : mgf (logAffineIncrement ε M 0) μ s ≤ Real.exp (-c3))
    (hc3 : 0 < c3) :
    μ.real
        (affineSurvivalSet M b K Kstar ⌊s / c3 * Real.log K + r⌋₊) ≤
      max (Real.exp (-s * Real.log Kstar + c3)) 1 * Real.exp (-c3 * r) := by
  calc
    μ.real
        (affineSurvivalSet M b K Kstar ⌊s / c3 * Real.log K + r⌋₊)
        ≤ Real.exp (-s * Real.log Kstar + c3) * Real.exp (-c3 * r) :=
      measureReal_affineSurvivalSet_le_exp_mul_exp_neg μ M b K Kstar ε
        ⌊s / c3 * Real.log K + r⌋₊ s c3 r hK hKstar hM_nonneg hε hfac hb
        hM_meas hind hident hs hint hmgf hc3
        (affineThreshold_sub_one_lt_floor s c3 K r)
    _ ≤ max (Real.exp (-s * Real.log Kstar + c3)) 1 * Real.exp (-c3 * r) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)

/-- Convergence of shifted-log expectations to a negative log expectation selects
one positive shift whose expectation is still negative. -/
lemma exists_pos_integral_log_add_neg_of_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M : Ω → ℝ)
    (hlim : Tendsto
      (fun n : ℕ => ∫ ω, Real.log (M ω + ((n + 1 : ℕ) : ℝ)⁻¹) ∂μ)
      atTop (𝓝 (∫ ω, Real.log (M ω) ∂μ)))
    (hneg : (∫ ω, Real.log (M ω) ∂μ) < 0) :
    ∃ ε : ℝ, 0 < ε ∧ (∫ ω, Real.log (M ω + ε) ∂μ) < 0 := by
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        (∫ ω, Real.log (M ω + ((n + 1 : ℕ) : ℝ)⁻¹) ∂μ) < 0 :=
    (tendsto_order.1 hlim).2 0 hneg
  obtain ⟨n, hn⟩ := heventually.exists
  refine ⟨((n + 1 : ℕ) : ℝ)⁻¹, ?_, hn⟩
  positivity

/-- Dominated convergence for the shifted logarithms
`log (M + 1 / (n + 1))` when `M` is positive almost everywhere. -/
lemma tendsto_integral_log_add_inv_nat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M bound : Ω → ℝ)
    (hM_meas : AEMeasurable M μ) (hM_pos : ∀ᵐ ω ∂μ, 0 < M ω)
    (hbound_int : Integrable bound μ)
    (hbound : ∀ n : ℕ, ∀ᵐ ω ∂μ,
      ‖Real.log (M ω + ((n + 1 : ℕ) : ℝ)⁻¹)‖ ≤ bound ω) :
    Tendsto
      (fun n : ℕ => ∫ ω, Real.log (M ω + ((n + 1 : ℕ) : ℝ)⁻¹) ∂μ)
      atTop (𝓝 (∫ ω, Real.log (M ω) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence bound ?_ hbound_int hbound ?_
  · intro n
    exact
      (Real.measurable_log.comp_aemeasurable
        (hM_meas.add_const ((n + 1 : ℕ) : ℝ)⁻¹)).aestronglyMeasurable
  · filter_upwards [hM_pos] with ω hω
    apply (Real.continuousAt_log hω.ne').tendsto.comp
    simpa only [one_div, Nat.cast_add, Nat.cast_one, add_zero] using
      ((tendsto_const_nhds (x := M ω)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- A negative expected log and dominated convergence of positive shifts yield a
positive shift whose expected log remains negative. -/
lemma exists_pos_integral_log_add_neg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (M bound : Ω → ℝ)
    (hM_meas : AEMeasurable M μ) (hM_pos : ∀ᵐ ω ∂μ, 0 < M ω)
    (hbound_int : Integrable bound μ)
    (hbound : ∀ n : ℕ, ∀ᵐ ω ∂μ,
      ‖Real.log (M ω + ((n + 1 : ℕ) : ℝ)⁻¹)‖ ≤ bound ω)
    (hneg : (∫ ω, Real.log (M ω) ∂μ) < 0) :
    ∃ ε : ℝ, 0 < ε ∧ (∫ ω, Real.log (M ω + ε) ∂μ) < 0 :=
  exists_pos_integral_log_add_neg_of_tendsto μ M
    (tendsto_integral_log_add_inv_nat μ M bound hM_meas hM_pos hbound_int hbound)
    hneg

/-- A function with value one and negative derivative at zero is strictly below
one at some positive argument. -/
lemma exists_pos_lt_one_of_hasDerivAt_neg (f : ℝ → ℝ) (μ : ℝ)
    (hf0 : f 0 = 1) (hderiv : HasDerivAt f μ 0) (hμ : μ < 0) :
    ∃ s : ℝ, 0 < s ∧ f s < 1 := by
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hu0 : Tendsto u atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hupos : ∀ n, 0 < u n := fun n => by
    dsimp [u]
    positivity
  have huWithin : Tendsto u atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hu0, Eventually.of_forall (fun n => hupos n)⟩
  have hslope :
      Tendsto (fun n => slope f 0 (u n)) atTop (𝓝 μ) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).2.comp huWithin
  have heventually : ∀ᶠ n : ℕ in atTop, slope f 0 (u n) < 0 :=
    (tendsto_order.1 hslope).2 0 hμ
  obtain ⟨n, hn⟩ := heventually.exists
  refine ⟨u n, hupos n, ?_⟩
  rw [slope_def_field, sub_zero, hf0] at hn
  have hnum : f (u n) - 1 < 0 := by
    have := (div_lt_iff₀ (hupos n)).mp hn
    simpa using this
  linarith

/-- Strengthened selection: a function with value one and negative derivative at zero is
strictly below one at some positive argument that additionally lies in any prescribed
neighborhood `U` of zero. -/
lemma exists_pos_mem_lt_one_of_hasDerivAt_neg (f : ℝ → ℝ) (μ : ℝ) {U : Set ℝ}
    (hU : U ∈ 𝓝 0) (hf0 : f 0 = 1) (hderiv : HasDerivAt f μ 0) (hμ : μ < 0) :
    ∃ s : ℝ, 0 < s ∧ s ∈ U ∧ f s < 1 := by
  let u : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hu0 : Tendsto u atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hupos : ∀ n, 0 < u n := fun n => by
    dsimp [u]
    positivity
  have huWithin : Tendsto u atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hu0, Eventually.of_forall (fun n => hupos n)⟩
  have hslope :
      Tendsto (fun n => slope f 0 (u n)) atTop (𝓝 μ) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hderiv).2.comp huWithin
  have heventually : ∀ᶠ n : ℕ in atTop, slope f 0 (u n) < 0 :=
    (tendsto_order.1 hslope).2 0 hμ
  have hmem : ∀ᶠ n : ℕ in atTop, u n ∈ U := hu0.eventually hU
  obtain ⟨n, hn, hnU⟩ := (heventually.and hmem).exists
  refine ⟨u n, hupos n, hnU, ?_⟩
  rw [slope_def_field, sub_zero, hf0] at hn
  have hnum : f (u n) - 1 < 0 := by
    have := (div_lt_iff₀ (hupos n)).mp hn
    simpa using this
  linarith

/-- At zero, the derivative of the mgf is the expectation whenever zero lies in
the interior of the exponential-integrability set. -/
lemma hasDerivAt_mgf_zero_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ)
    (hX : 0 ∈ interior (integrableExpSet X μ)) :
    HasDerivAt (mgf X μ) (∫ ω, X ω ∂μ) 0 := by
  simpa using hasDerivAt_mgf hX

/-- A negative expectation and exponential integrability around zero give a
positive parameter at which the mgf is strictly below one. -/
lemma exists_pos_mgf_lt_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : 0 ∈ interior (integrableExpSet X μ))
    (hneg : (∫ ω, X ω ∂μ) < 0) :
    ∃ s : ℝ, 0 < s ∧ mgf X μ s < 1 :=
  exists_pos_lt_one_of_hasDerivAt_neg (mgf X μ) (∫ ω, X ω ∂μ)
    mgf_zero (hasDerivAt_mgf_zero_integral μ X hX) hneg

/-- Strengthened mgf selection: the positive parameter can be taken inside the interior of
the exponential-integrability set, so that `exp(s·X)` is genuinely integrable alongside
`mgf X μ s < 1`. (The bare `mgf < 1` does not force integrability: a non-integrable
`exp(s·X)` gives the Bochner value `mgf = 0 < 1`.) -/
lemma exists_pos_integrable_mgf_lt_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : 0 ∈ interior (integrableExpSet X μ))
    (hneg : (∫ ω, X ω ∂μ) < 0) :
    ∃ s : ℝ, 0 < s ∧ Integrable (fun ω => Real.exp (s * X ω)) μ ∧ mgf X μ s < 1 := by
  obtain ⟨s, hs_pos, hs_mem, hs_lt⟩ :=
    exists_pos_mem_lt_one_of_hasDerivAt_neg (mgf X μ) (∫ ω, X ω ∂μ)
      (isOpen_interior.mem_nhds hX) mgf_zero
      (hasDerivAt_mgf_zero_integral μ X hX) hneg
  have hs_in : s ∈ integrableExpSet X μ := interior_subset hs_mem
  exact ⟨s, hs_pos, hs_in, hs_lt⟩

/-- A nonnegative number strictly below one is bounded by `exp (-c)` for some
positive `c`, including the endpoint value zero. -/
lemma exists_pos_exp_neg_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∃ c : ℝ, 0 < c ∧ a ≤ Real.exp (-c) := by
  rcases eq_or_lt_of_le ha0 with rfl | ha
  · exact ⟨1, by norm_num, (Real.exp_pos (-1)).le⟩
  · refine ⟨-Real.log a, neg_pos.mpr (Real.log_neg ha ha1), ?_⟩
    rw [neg_neg, Real.exp_log ha]

/-- A negative expectation and exponential integrability around zero yield a
positive parameter `s` together with a positive rate `c₃` such that
`mgf X μ s ≤ exp (-c₃)`. This packages the mgf-decay input to the affine
entrance survival bound. -/
lemma exists_pos_mgf_le_exp_neg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : 0 ∈ interior (integrableExpSet X μ))
    (hneg : (∫ ω, X ω ∂μ) < 0) :
    ∃ s : ℝ, 0 < s ∧ ∃ c3 : ℝ, 0 < c3 ∧ mgf X μ s ≤ Real.exp (-c3) := by
  obtain ⟨s, hs_pos, hs_lt⟩ := exists_pos_mgf_lt_one μ X hX hneg
  obtain ⟨c3, hc3_pos, hc3⟩ := exists_pos_exp_neg_ge (a := mgf X μ s) mgf_nonneg hs_lt
  exact ⟨s, hs_pos, c3, hc3_pos, hc3⟩

/-- Integrable-aware mgf-decay package: a positive parameter `s` with `exp(s·X)` integrable
and a positive rate `c₃` with `mgf X μ s ≤ exp(-c₃)`. The integrability clause is what lets
the finite-sum-exponential hypothesis of the survival bound be discharged
(`integrable_exp_mul_sum_logAffineIncrement`). -/
lemma exists_pos_integrable_mgf_le_exp_neg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : 0 ∈ interior (integrableExpSet X μ))
    (hneg : (∫ ω, X ω ∂μ) < 0) :
    ∃ s : ℝ, 0 < s ∧ Integrable (fun ω => Real.exp (s * X ω)) μ ∧
      ∃ c3 : ℝ, 0 < c3 ∧ mgf X μ s ≤ Real.exp (-c3) := by
  obtain ⟨s, hs_pos, hs_int, hs_lt⟩ := exists_pos_integrable_mgf_lt_one μ X hX hneg
  obtain ⟨c3, hc3_pos, hc3⟩ := exists_pos_exp_neg_ge (a := mgf X μ s) mgf_nonneg hs_lt
  exact ⟨s, hs_pos, hs_int, c3, hc3_pos, hc3⟩

/-- Parametrized logarithmic-entrance bound (`lem:negative-drift-affine-entrance`, with the
shift `ε` already fixed so that `𝔼 log(M₁+ε)<0` and `log(M₁+ε)` has an exponential moment
about the origin). There exist `c₁,c₂,c₃>0` with
`ℙ(inf\{t:U_t≤K_*\} > ⌊c₁ log K + r⌋) ≤ c₂ e^{-c₃ r}` for the affine recursion started at `K`. -/
theorem measureReal_affineEntranceTime_gt_floor_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ) (b K Kstar ε r : ℝ)
    (hK : 0 < K) (hKstar : 0 < Kstar) (hb : b ≤ ε * Kstar) (hε : 0 < ε)
    (hM_nonneg : ∀ ω j, 0 ≤ M j ω) (hM_meas : ∀ j, Measurable (M j))
    (hind : iIndepFun M μ) (hident : ∀ j, IdentDistrib (M (j + 1)) (M 1) μ μ)
    (hExp : 0 ∈ interior (integrableExpSet (logAffineIncrement ε M 0) μ))
    (hneg : (∫ ω, logAffineIncrement ε M 0 ω ∂μ) < 0) :
    ∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      μ.real {ω | (⌊c1 * Real.log K + r⌋₊ : ℕ∞) <
          affineEntranceTime (fun k => M k ω) b K Kstar} ≤ c2 * Real.exp (-c3 * r) := by
  obtain ⟨s, hs_pos, hs_int, c3, hc3_pos, hmgf⟩ :=
    exists_pos_integrable_mgf_le_exp_neg μ (logAffineIncrement ε M 0) hExp hneg
  refine ⟨s / c3, max (Real.exp (-s * Real.log Kstar + c3)) 1, c3,
    div_pos hs_pos hc3_pos, lt_of_lt_of_le one_pos (le_max_right _ _), hc3_pos, ?_⟩
  have hfac : ∀ ω j, 0 < M (j + 1) ω + ε := fun ω j =>
    add_pos_of_nonneg_of_pos (hM_nonneg ω (j + 1)) hε
  have hint : Integrable (fun ω => Real.exp
      (s * (∑ j ∈ Finset.range ⌊s / c3 * Real.log K + r⌋₊,
        logAffineIncrement ε M j ω))) μ :=
    integrable_exp_mul_sum_logAffineIncrement μ ε M ⌊s / c3 * Real.log K + r⌋₊ s
      hM_meas hind hident hs_int
  have hbound := measureReal_affineSurvivalSet_floor_le μ M b K Kstar ε s c3 r
    hK hKstar hM_nonneg hε.le hfac hb hM_meas hind hident hs_pos.le hint hmgf hc3_pos
  rwa [affineSurvivalSet_eq_lt_affineEntranceTime] at hbound

/-- Logarithmic entrance for contractive affine recursions
(`lem:negative-drift-affine-entrance`), fully internal form. For iid nonnegative multipliers
with `𝔼 log M₁ < 0` and `log(M₁+ε)` exponentially integrable near the origin for every
`ε>0`, there exist `K_*, c₁, c₂, c₃ > 0` — depending only on `b` and the law of `M₁`, uniform
in the start `K` and the excess `r` — with
`ℙ(inf\{t:U_t≤K_*\} > ⌊c₁ log K + r⌋) ≤ c₂ e^{-c₃ r}`. The shift `ε` (and hence `K_*`) is
selected internally via `exists_pos_integral_log_add_neg` from `𝔼 log M₁ < 0`. -/
theorem exists_affineEntrance_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ) (b : ℝ) (bound : Ω → ℝ)
    (hM_nonneg : ∀ ω j, 0 ≤ M j ω) (hM_meas : ∀ j, Measurable (M j))
    (hind : iIndepFun M μ) (hident : ∀ j, IdentDistrib (M (j + 1)) (M 1) μ μ)
    (hElog : (∫ ω, Real.log (M 1 ω) ∂μ) < 0)
    (hExp : ∀ ε : ℝ, 0 < ε →
      0 ∈ interior (integrableExpSet (logAffineIncrement ε M 0) μ))
    (hM_pos : ∀ᵐ ω ∂μ, 0 < M 1 ω) (hbound_int : Integrable bound μ)
    (hbound : ∀ n : ℕ, ∀ᵐ ω ∂μ,
      ‖Real.log (M 1 ω + ((n + 1 : ℕ) : ℝ)⁻¹)‖ ≤ bound ω) :
    ∃ Kstar c1 c2 c3 : ℝ, 0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ K : ℝ, 0 < K → ∀ r : ℝ,
        μ.real {ω | (⌊c1 * Real.log K + r⌋₊ : ℕ∞) <
            affineEntranceTime (fun k => M k ω) b K Kstar} ≤
          c2 * Real.exp (-c3 * r) := by
  obtain ⟨ε, hε_pos, hneg⟩ :=
    exists_pos_integral_log_add_neg μ (M 1) bound (hM_meas 1).aemeasurable
      hM_pos hbound_int hbound hElog
  obtain ⟨s, hs_pos, hs_int, c3, hc3_pos, hmgf⟩ :=
    exists_pos_integrable_mgf_le_exp_neg μ (logAffineIncrement ε M 0) (hExp ε hε_pos) hneg
  set Kstar := max (b / ε) 1 with hKstar_def
  have hKstar_pos : 0 < Kstar := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hb : b ≤ ε * Kstar := by
    rw [mul_comm]
    exact (div_le_iff₀ hε_pos).mp (le_max_left _ _)
  have hfac : ∀ ω j, 0 < M (j + 1) ω + ε := fun ω j =>
    add_pos_of_nonneg_of_pos (hM_nonneg ω (j + 1)) hε_pos
  refine ⟨Kstar, s / c3, max (Real.exp (-s * Real.log Kstar + c3)) 1, c3,
    hKstar_pos, div_pos hs_pos hc3_pos,
    lt_of_lt_of_le one_pos (le_max_right _ _), hc3_pos, ?_⟩
  intro K hK r
  have hint : Integrable (fun ω => Real.exp
      (s * (∑ j ∈ Finset.range ⌊s / c3 * Real.log K + r⌋₊,
        logAffineIncrement ε M j ω))) μ :=
    integrable_exp_mul_sum_logAffineIncrement μ ε M ⌊s / c3 * Real.log K + r⌋₊ s
      hM_meas hind hident hs_int
  have hbnd := measureReal_affineSurvivalSet_floor_le μ M b K Kstar ε s c3 r
    hK hKstar_pos hM_nonneg hε_pos.le hfac hb hM_meas hind hident hs_pos.le hint hmgf hc3_pos
  rwa [affineSurvivalSet_eq_lt_affineEntranceTime] at hbnd

end AbsorptionCutoff
