/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib
import AbsorptionCutoff.Estimates

/-!
# Stopped second-moment estimate (abstract stochastic wrapper)

Formalizes the stochastic wrapper of the paper's `lem:common-stopped-orbit-tracking`
(§`app:common-stopped-orbit-tracking`), the abstract route: a general filtered probability
space carrying an adapted process `R`, an `𝓕_t`-measurable multiplier `A` with
`|A_t| ≤ α_t`, martingale-difference noise `η` (`𝔼[η_{t+1}|𝓕_t] = 0`,
`𝔼[η_{t+1}²|𝓕_t] ≤ Cσ_t²/N`), and a stopping time `τ`. The deterministic engines feeding
this file are already proved in `Estimates.lean` (`geom_recursion_bound`, `backWeight`).

## Plan (paper's proof order)
1. Killed one-step **pointwise** bound `1_{τ>t+1} R_{t+1}² ≤ 1_{τ>t}(A_t R_t+η_{t+1})²`
   (this file, `killed_step_pointwise`) — recursion only, no conditioning.
2. Killed one-step **conditional** bound
   `𝔼[1_{τ>t+1} R_{t+1}²|𝓕_t] ≤ 1_{τ>t}(α_t² R_t²+Cσ_t²/N)` (condExp, cross term = 0).
3. Killed **integral** recursion `m_{t+1} ≤ α_t² m_t + Cσ_t²/N`, then `geom_recursion_bound`.
4. Stopped weighted one-step bound + telescoping with `backWeight` ⇒ `𝔼R̄_T²` bound.
5. Exit probability via Chebyshev.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace AbsorptionCutoff

/-- **Pointwise killed one-step bound** (step 1): on `{τ > t+1} ⊆ {τ > t}` the recursion
`R_{t+1} = A_t R_t + η_{t+1}` applies, so the two sides agree there; off `{τ > t+1}` the
left side vanishes and the right side is nonnegative. Uses only the recursion (which holds
on `{t < τ}`), no conditioning. -/
lemma killed_step_pointwise {Ω : Type*} {R A η : ℕ → Ω → ℝ} {τ : Ω → ℕ} {t : ℕ}
    (hrec : ∀ ω, t < τ ω → R (t + 1) ω = A t ω * R t ω + η (t + 1) ω) (ω : Ω) :
    {ω | t + 1 < τ ω}.indicator (fun _ => (1 : ℝ)) ω * R (t + 1) ω ^ 2
      ≤ {ω | t < τ ω}.indicator (fun _ => (1 : ℝ)) ω
          * (A t ω * R t ω + η (t + 1) ω) ^ 2 := by
  by_cases h1 : t + 1 < τ ω
  · have h0 : t < τ ω := lt_trans (Nat.lt_succ_self t) h1
    rw [Set.indicator_of_mem (show ω ∈ {ω | t + 1 < τ ω} from h1),
        Set.indicator_of_mem (show ω ∈ {ω | t < τ ω} from h0), one_mul, one_mul]
    exact le_of_eq (by rw [hrec ω h0])
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | t + 1 < τ ω} from h1), zero_mul]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω) (sq_nonneg _)

/-- **Core conditional one-step bound** (step 2 core, abstract). For an `m`-measurable
`a`, a martingale-difference `e` (`𝔼[e|m]=0`, `𝔼[e²|m]≤c`), and a bound `a² ≤ b` a.e.,
the conditional second moment of `a + e` is controlled: `𝔼[(a+e)²|m] ≤ b + c` a.e. The
cross term `2ae` drops out because `𝔼[e|m]=0` (pull the `m`-measurable factor `2a` out via
`condExp_mul_of_aestronglyMeasurable_left`); `𝔼[a²|m]=a²≤b` and `𝔼[e²|m]≤c`. -/
lemma condExp_add_sq_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {a e b : Ω → ℝ} {c : ℝ}
    (ha_meas : StronglyMeasurable[m] a)
    (hbound : ∀ᵐ ω ∂μ, a ω ^ 2 ≤ b ω)
    (he1 : μ[e | m] =ᵐ[μ] 0)
    (he2 : μ[fun ω => e ω ^ 2 | m] ≤ᵐ[μ] fun _ => c)
    (hint_a2 : Integrable (fun ω => a ω ^ 2) μ)
    (hint_ae : Integrable (fun ω => a ω * e ω) μ)
    (hint_e2 : Integrable (fun ω => e ω ^ 2) μ)
    (hint_e : Integrable e μ) :
    μ[fun ω => (a ω + e ω) ^ 2 | m] ≤ᵐ[μ] fun ω => b ω + c := by
  have hint_2ae : Integrable (fun ω => 2 * a ω * e ω) μ := by
    have h := hint_ae.const_mul 2
    simpa [mul_assoc] using h
  have hexp : (fun ω => (a ω + e ω) ^ 2)
      = (fun ω => a ω ^ 2 + 2 * a ω * e ω) + (fun ω => e ω ^ 2) := by
    ext ω; simp only [Pi.add_apply]; ring
  rw [hexp]
  have hIntsum : Integrable (fun ω => a ω ^ 2 + 2 * a ω * e ω) μ := hint_a2.add hint_2ae
  have hca2 : μ[fun ω => a ω ^ 2 | m] = fun ω => a ω ^ 2 :=
    condExp_of_stronglyMeasurable hm (ha_meas.pow 2) hint_a2
  have hcae : μ[fun ω => 2 * a ω * e ω | m] =ᵐ[μ] 0 := by
    have hf2a : StronglyMeasurable[m] (fun ω => 2 * a ω) := ha_meas.const_mul 2
    have hrw : (fun ω => 2 * a ω * e ω) = (fun ω => 2 * a ω) * e := by
      ext ω; simp only [Pi.mul_apply]
    rw [hrw]
    refine (condExp_mul_of_aestronglyMeasurable_left hf2a.aestronglyMeasurable
      (by rw [← hrw]; exact hint_2ae) hint_e).trans ?_
    filter_upwards [he1] with ω hω
    simp only [Pi.mul_apply, Pi.zero_apply] at hω ⊢
    rw [hω, mul_zero]
  have h_eq : μ[(fun ω => a ω ^ 2 + 2 * a ω * e ω) + (fun ω => e ω ^ 2) | m]
      =ᵐ[μ] (fun ω => a ω ^ 2) + μ[fun ω => e ω ^ 2 | m] := by
    refine (condExp_add hIntsum hint_e2 m).trans ?_
    have hleft : μ[fun ω => a ω ^ 2 + 2 * a ω * e ω | m] =ᵐ[μ] fun ω => a ω ^ 2 := by
      refine (condExp_add hint_a2 hint_2ae m).trans ?_
      rw [hca2]
      filter_upwards [hcae] with ω hω
      simp only [Pi.add_apply, Pi.zero_apply] at hω ⊢
      rw [hω, add_zero]
    exact hleft.add EventuallyEq.rfl
  refine h_eq.trans_le ?_
  filter_upwards [hbound, he2] with ω hb he
  have he' : μ[fun ω => e ω ^ 2 | m] ω ≤ c := he
  simp only [Pi.add_apply]
  linarith

/-- **Killed one-step conditional bound** (step 2). Combines the pointwise bound
`killed_step_pointwise` with the core `condExp_add_sq_le`: take `𝔼[·|𝓕_t]` (monotone),
pull the `𝓕_t`-measurable indicator `1_{τ>t}` out (`condExp_indicator`), and apply the core
bound inside. Gives `𝔼[1_{τ>t+1}R_{t+1}²|𝓕_t] ≤ 1_{τ>t}(α_t²R_t²+Cσ_t²/N)` a.e. The only
stopping-time input is `{τ>t} ∈ 𝓕_t` (hypothesis `hτ`). -/
lemma killed_condExp_step {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {R A η : ℕ → Ω → ℝ} {τ : Ω → ℕ} {α σ : ℕ → ℝ} {C N : ℝ} {t : ℕ}
    (hτ : MeasurableSet[ℱ t] {ω | t < τ ω})
    (hrec : ∀ ω, t < τ ω → R (t + 1) ω = A t ω * R t ω + η (t + 1) ω)
    (ha_meas : StronglyMeasurable[ℱ t] (fun ω => A t ω * R t ω))
    (hAsq : ∀ ω, A t ω ^ 2 ≤ α t ^ 2)
    (hη1 : μ[η (t + 1) | ℱ t] =ᵐ[μ] 0)
    (hη2 : μ[fun ω => η (t + 1) ω ^ 2 | ℱ t] ≤ᵐ[μ] fun _ => C * σ t ^ 2 / N)
    (hint_a2 : Integrable (fun ω => (A t ω * R t ω) ^ 2) μ)
    (hint_ae : Integrable (fun ω => A t ω * R t ω * η (t + 1) ω) μ)
    (hint_e2 : Integrable (fun ω => η (t + 1) ω ^ 2) μ)
    (hint_e : Integrable (η (t + 1)) μ)
    (hint_L : Integrable
      (fun ω => {ω | t + 1 < τ ω}.indicator (fun _ => (1 : ℝ)) ω * R (t + 1) ω ^ 2) μ)
    (hint_sq : Integrable (fun ω => (A t ω * R t ω + η (t + 1) ω) ^ 2) μ) :
    μ[fun ω => {ω | t + 1 < τ ω}.indicator (fun _ => (1 : ℝ)) ω * R (t + 1) ω ^ 2 | ℱ t]
      ≤ᵐ[μ] fun ω => {ω | t < τ ω}.indicator (fun _ => (1 : ℝ)) ω
          * (α t ^ 2 * R t ω ^ 2 + C * σ t ^ 2 / N) := by
  have hbound : ∀ᵐ ω ∂μ, (A t ω * R t ω) ^ 2 ≤ α t ^ 2 * R t ω ^ 2 := by
    refine ae_of_all μ (fun ω => ?_)
    calc (A t ω * R t ω) ^ 2 = A t ω ^ 2 * R t ω ^ 2 := by ring
      _ ≤ α t ^ 2 * R t ω ^ 2 := mul_le_mul_of_nonneg_right (hAsq ω) (sq_nonneg _)
  have hcore : μ[fun ω => (A t ω * R t ω + η (t + 1) ω) ^ 2 | ℱ t]
      ≤ᵐ[μ] fun ω => α t ^ 2 * R t ω ^ 2 + C * σ t ^ 2 / N :=
    condExp_add_sq_le (a := fun ω => A t ω * R t ω) (e := η (t + 1))
      (b := fun ω => α t ^ 2 * R t ω ^ 2) (c := C * σ t ^ 2 / N)
      (ℱ.le t) ha_meas hbound hη1 hη2 hint_a2 hint_ae hint_e2 hint_e
  have hpw := killed_step_pointwise hrec
  have hM_eq : (fun ω => {ω | t < τ ω}.indicator (fun _ => (1 : ℝ)) ω
        * (A t ω * R t ω + η (t + 1) ω) ^ 2)
      = {ω | t < τ ω}.indicator (fun ω => (A t ω * R t ω + η (t + 1) ω) ^ 2) := by
    ext ω; by_cases h : ω ∈ {ω | t < τ ω} <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hint_M : Integrable (fun ω => {ω | t < τ ω}.indicator (fun _ => (1 : ℝ)) ω
      * (A t ω * R t ω + η (t + 1) ω) ^ 2) μ := by
    rw [hM_eq]; exact hint_sq.indicator ((ℱ.le t) _ hτ)
  refine (condExp_mono (m := ℱ t) hint_L hint_M (ae_of_all μ hpw)).trans ?_
  rw [hM_eq]
  refine (condExp_indicator hint_sq hτ).trans_le ?_
  have hRHS : (fun ω => {ω | t < τ ω}.indicator (fun _ => (1 : ℝ)) ω
        * (α t ^ 2 * R t ω ^ 2 + C * σ t ^ 2 / N))
      = {ω | t < τ ω}.indicator (fun ω => α t ^ 2 * R t ω ^ 2 + C * σ t ^ 2 / N) := by
    ext ω; by_cases h : ω ∈ {ω | t < τ ω} <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  rw [hRHS]
  filter_upwards [hcore] with ω hω
  by_cases h : ω ∈ {ω | t < τ ω}
  · simp only [Set.indicator_of_mem h]; exact hω
  · simp [Set.indicator_of_notMem h]

/-- The **killed second moment** `m_t = 𝔼[R_t² 1_{τ>t}] = ∫ 1_{τ>t} R_t² dμ`. -/
noncomputable def killedMoment {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (R : ℕ → Ω → ℝ) (τ : Ω → ℕ) (s : ℕ) : ℝ :=
  ∫ ω, {ω | s < τ ω}.indicator (fun _ => (1 : ℝ)) ω * R s ω ^ 2 ∂μ

/-- Integrating an a.e. conditional bound `𝔼[G|m] ≤ 1_{S₀}(k·R²+d)` (`d ≥ 0`) over a
probability space: `∫ G ≤ k·∫ 1_{S₀}R² + d`, using `∫ 𝔼[G|m] = ∫ G` and `ℙ(S₀) ≤ 1`. This
turns the killed conditional bound into the scalar recursion. -/
lemma integral_le_of_condExp_le {Ω : Type*} {m0 m : MeasurableSpace Ω} (hm : m ≤ m0)
    {μ : @Measure Ω m0} [IsProbabilityMeasure μ] {S0 : Set Ω} {R G : Ω → ℝ} {k d : ℝ}
    (hd : 0 ≤ d) (hS0 : MeasurableSet[m0] S0)
    (hcond : μ[G | m] ≤ᵐ[μ] fun ω => S0.indicator (fun _ => (1 : ℝ)) ω * (k * R ω ^ 2 + d))
    (hintH : Integrable (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω * (k * R ω ^ 2 + d)) μ)
    (hint_SR : Integrable (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω * R ω ^ 2) μ) :
    ∫ ω, G ω ∂μ ≤ k * (∫ ω, S0.indicator (fun _ => (1 : ℝ)) ω * R ω ^ 2 ∂μ) + d := by
  have hIC : ∫ ω, G ω ∂μ = ∫ ω, (μ[G | m]) ω ∂μ := (integral_condExp hm).symm
  have hmono : ∫ ω, (μ[G | m]) ω ∂μ
      ≤ ∫ ω, S0.indicator (fun _ => (1 : ℝ)) ω * (k * R ω ^ 2 + d) ∂μ :=
    integral_mono_ae integrable_condExp hintH hcond
  have hint1 : Integrable (fun ω => k * (S0.indicator (fun _ => (1 : ℝ)) ω * R ω ^ 2)) μ :=
    hint_SR.const_mul k
  have hint2 : Integrable (fun ω => d * S0.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hS0).const_mul d
  have hHint : ∫ ω, S0.indicator (fun _ => (1 : ℝ)) ω * (k * R ω ^ 2 + d) ∂μ
      = k * (∫ ω, S0.indicator (fun _ => (1 : ℝ)) ω * R ω ^ 2 ∂μ) + d * μ.real S0 := by
    have hHsplit : (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω * (k * R ω ^ 2 + d))
        = (fun ω => k * (S0.indicator (fun _ => (1 : ℝ)) ω * R ω ^ 2)
            + d * S0.indicator (fun _ => (1 : ℝ)) ω) := by ext ω; ring
    rw [hHsplit, integral_add hint1 hint2, integral_const_mul, integral_const_mul,
        integral_indicator_const (1 : ℝ) hS0, smul_eq_mul, mul_one]
  have hle1 : μ.real S0 ≤ 1 := by
    change (μ S0).toReal ≤ 1
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  calc ∫ ω, G ω ∂μ = ∫ ω, (μ[G | m]) ω ∂μ := hIC
    _ ≤ ∫ ω, S0.indicator (fun _ => (1 : ℝ)) ω * (k * R ω ^ 2 + d) ∂μ := hmono
    _ = k * (∫ ω, S0.indicator (fun _ => (1 : ℝ)) ω * R ω ^ 2 ∂μ) + d * μ.real S0 := hHint
    _ ≤ k * (∫ ω, S0.indicator (fun _ => (1 : ℝ)) ω * R ω ^ 2 ∂μ) + d := by nlinarith [hle1, hd]

/-- **Killed second-moment recursion** (step 3). Integrating `killed_condExp_step` over the
probability space gives the scalar recursion `m_{t+1} ≤ α_t² m_t + Cσ_t²/N`, the input to
`geom_recursion_bound` (paper `eq:common-killed-orbit-tracking`). -/
lemma killed_moment_recursion {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {R A η : ℕ → Ω → ℝ} {τ : Ω → ℕ} {α σ : ℕ → ℝ} {C N : ℝ} {t : ℕ}
    (hd : 0 ≤ C * σ t ^ 2 / N)
    (hτ : MeasurableSet[ℱ t] {ω | t < τ ω})
    (hrec : ∀ ω, t < τ ω → R (t + 1) ω = A t ω * R t ω + η (t + 1) ω)
    (ha_meas : StronglyMeasurable[ℱ t] (fun ω => A t ω * R t ω))
    (hAsq : ∀ ω, A t ω ^ 2 ≤ α t ^ 2)
    (hη1 : μ[η (t + 1) | ℱ t] =ᵐ[μ] 0)
    (hη2 : μ[fun ω => η (t + 1) ω ^ 2 | ℱ t] ≤ᵐ[μ] fun _ => C * σ t ^ 2 / N)
    (hint_a2 : Integrable (fun ω => (A t ω * R t ω) ^ 2) μ)
    (hint_ae : Integrable (fun ω => A t ω * R t ω * η (t + 1) ω) μ)
    (hint_e2 : Integrable (fun ω => η (t + 1) ω ^ 2) μ)
    (hint_e : Integrable (η (t + 1)) μ)
    (hint_L : Integrable
      (fun ω => {ω | t + 1 < τ ω}.indicator (fun _ => (1 : ℝ)) ω * R (t + 1) ω ^ 2) μ)
    (hint_sq : Integrable (fun ω => (A t ω * R t ω + η (t + 1) ω) ^ 2) μ)
    (hint_H : Integrable (fun ω => {ω | t < τ ω}.indicator (fun _ => (1 : ℝ)) ω
      * (α t ^ 2 * R t ω ^ 2 + C * σ t ^ 2 / N)) μ)
    (hint_SR : Integrable
      (fun ω => {ω | t < τ ω}.indicator (fun _ => (1 : ℝ)) ω * R t ω ^ 2) μ) :
    killedMoment μ R τ (t + 1) ≤ α t ^ 2 * killedMoment μ R τ t + C * σ t ^ 2 / N := by
  have hcond := killed_condExp_step hτ hrec ha_meas hAsq hη1 hη2 hint_a2 hint_ae hint_e2
    hint_e hint_L hint_sq
  exact integral_le_of_condExp_le (R := R t) (k := α t ^ 2) (d := C * σ t ^ 2 / N)
    (ℱ.le t) hd ((ℱ.le t) _ hτ) hcond hint_H hint_SR

/-- **Closed-form killed second-moment bound** (paper `eq:common-killed-orbit-tracking`).
Feeding the per-step recursion `m_{t+1} ≤ α_t² m_t + Cσ_t²/N` (`killed_moment_recursion`,
supplied here for all `t` as `hrec_all`) into the deterministic engine `geom_recursion_bound`
gives the explicit product/sum bound. -/
lemma killed_moment_closed_form {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {α σ : ℕ → ℝ} {C N : ℝ}
    (hrec_all : ∀ t, killedMoment μ R τ (t + 1)
      ≤ α t ^ 2 * killedMoment μ R τ t + C * σ t ^ 2 / N) (t : ℕ) :
    killedMoment μ R τ t
      ≤ (∏ u ∈ Finset.range t, α u ^ 2) * killedMoment μ R τ 0
        + ∑ s ∈ Finset.range t, (∏ u ∈ Finset.Ico (s + 1) t, α u ^ 2) * (C * σ s ^ 2 / N) :=
  geom_recursion_bound (fun u => sq_nonneg (α u)) hrec_all t

/-! ### Stopped second moment -/

/-- The process stopped at `τ`: `R̄_t = R_{t ∧ τ}`. -/
def stoppedValue {Ω : Type*} (R : ℕ → Ω → ℝ) (τ : Ω → ℕ) (t : ℕ) (ω : Ω) : ℝ :=
  R (min t (τ ω)) ω

/-- The local finite-valued stopped process agrees with Mathlib's
`WithTop ℕ`-valued stopped process after coercing the stopping time. -/
lemma stoppedValue_eq_stoppedProcess_coe
    {Ω : Type*} (R : ℕ → Ω → ℝ) (τ : Ω → ℕ) (t : ℕ) :
    stoppedValue R τ t =
      MeasureTheory.stoppedProcess R
        (fun ω => (τ ω : WithTop ℕ)) t := by
  funext ω
  simp only [stoppedValue, MeasureTheory.stoppedProcess]
  have hcoe (n : ℕ) : (n : WithTop ℕ).untopA = n := by
    apply le_antisymm
    · exact (WithTop.untopA_le_iff WithTop.coe_ne_top).mpr le_rfl
    · exact (WithTop.le_untopA_iff WithTop.coe_ne_top).mpr le_rfl
  by_cases hle : t ≤ τ ω
  · rw [min_eq_left hle]
    have hmin :
        min (t : WithTop ℕ) (τ ω : WithTop ℕ) = (t : WithTop ℕ) :=
      min_eq_left (WithTop.coe_le_coe.mpr hle)
    have hidx :
        (min (t : WithTop ℕ) (τ ω : WithTop ℕ)).untopA = t := by
      rw [hmin]
      exact hcoe t
    exact congrArg (fun u : ℕ => R u ω) hidx.symm
  · have hge : τ ω ≤ t := (not_le.mp hle).le
    rw [min_eq_right hge]
    have hmin :
        min (t : WithTop ℕ) (τ ω : WithTop ℕ) = (τ ω : WithTop ℕ) :=
      min_eq_right (WithTop.coe_le_coe.mpr hge)
    have hidx :
        (min (t : WithTop ℕ) (τ ω : WithTop ℕ)).untopA = τ ω := by
      rw [hmin]
      exact hcoe _
    exact congrArg (fun u : ℕ => R u ω) hidx.symm

/-- **Stopped one-step decomposition** (step 4, pointwise). On `{τ ≤ t}` the stopped
process is constant, while on `{t < τ}` the original recursion applies:
`R̄_{t+1} = 1_{τ≤t} R̄_t + 1_{t<τ}(A_t R_t + η_{t+1})`. The two indicator events are
disjoint and exhaustive. -/
lemma stoppedValue_succ_decomposition {Ω : Type*} {R A η : ℕ → Ω → ℝ}
    {τ : Ω → ℕ} {t : ℕ}
    (hrec : ∀ ω, t < τ ω → R (t + 1) ω = A t ω * R t ω + η (t + 1) ω)
    (ω : Ω) :
    stoppedValue R τ (t + 1) ω
      = {ω | τ ω ≤ t}.indicator (stoppedValue R τ t) ω
        + {ω | t < τ ω}.indicator (fun ω => A t ω * R t ω + η (t + 1) ω) ω := by
  by_cases h : τ ω ≤ t
  · have hnot : ¬t < τ ω := Nat.not_lt_of_ge h
    rw [Set.indicator_of_mem (show ω ∈ {ω | τ ω ≤ t} from h),
      Set.indicator_of_notMem (show ω ∉ {ω | t < τ ω} from hnot), add_zero]
    simp only [stoppedValue]
    rw [Nat.min_eq_right h, Nat.min_eq_right (le_trans h (Nat.le_succ t))]
  · have hlt : t < τ ω := Nat.lt_of_not_ge h
    rw [Set.indicator_of_notMem (show ω ∉ {ω | τ ω ≤ t} from h),
      Set.indicator_of_mem (show ω ∈ {ω | t < τ ω} from hlt), zero_add]
    simp only [stoppedValue]
    rw [Nat.min_eq_left (Nat.succ_le_of_lt hlt), hrec ω hlt]

/-- Squared and deterministically weighted form of `stoppedValue_succ_decomposition`.
Disjointness of `{τ ≤ t}` and `{t < τ}` removes the cross term pointwise. -/
lemma stoppedValue_succ_sq_decomposition {Ω : Type*} {R A η : ℕ → Ω → ℝ}
    {τ : Ω → ℕ} {t : ℕ} {W : ℝ}
    (hrec : ∀ ω, t < τ ω → R (t + 1) ω = A t ω * R t ω + η (t + 1) ω)
    (ω : Ω) :
    W * stoppedValue R τ (t + 1) ω ^ 2
      = {ω | τ ω ≤ t}.indicator (fun ω => W * stoppedValue R τ t ω ^ 2) ω
        + {ω | t < τ ω}.indicator
            (fun ω => W * (A t ω * R t ω + η (t + 1) ω) ^ 2) ω := by
  rw [stoppedValue_succ_decomposition hrec ω]
  by_cases h : τ ω ≤ t
  · have hnot : ¬t < τ ω := Nat.not_lt_of_ge h
    simp [h, hnot]
  · have hlt : t < τ ω := Nat.lt_of_not_ge h
    simp [h, hlt]

/-- Event-localized form of `condExp_add_sq_le`. If `S` is visible in the conditioning
σ-algebra, the same conditional square bound holds after restricting both sides to `S`. -/
lemma condExp_indicator_add_sq_le {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    {S : Set Ω} {a e b : Ω → ℝ} {c : ℝ}
    (hS : MeasurableSet[m] S)
    (ha_meas : StronglyMeasurable[m] a)
    (hbound : ∀ᵐ ω ∂μ, a ω ^ 2 ≤ b ω)
    (he1 : μ[e | m] =ᵐ[μ] 0)
    (he2 : μ[fun ω => e ω ^ 2 | m] ≤ᵐ[μ] fun _ => c)
    (hint_a2 : Integrable (fun ω => a ω ^ 2) μ)
    (hint_ae : Integrable (fun ω => a ω * e ω) μ)
    (hint_e2 : Integrable (fun ω => e ω ^ 2) μ)
    (hint_e : Integrable e μ)
    (hint_sq : Integrable (fun ω => (a ω + e ω) ^ 2) μ) :
    μ[S.indicator (fun ω => (a ω + e ω) ^ 2) | m]
      ≤ᵐ[μ] S.indicator (fun ω => b ω + c) := by
  refine (condExp_indicator hint_sq hS).trans_le ?_
  have hcore := condExp_add_sq_le hm ha_meas hbound he1 he2 hint_a2 hint_ae hint_e2 hint_e
  filter_upwards [hcore] with ω hω
  by_cases h : ω ∈ S
  · simpa [Set.indicator_of_mem h] using hω
  · simp [Set.indicator_of_notMem h]

/-- **Weighted stopped one-step conditional bound** (step 4). The branch
`{τ ≤ t}` is already stopped and is pulled unchanged through the conditional
expectation. On `{t < τ}`, `condExp_indicator_add_sq_le` removes the cross term.
The backward-weight inequalities then absorb both deterministic square terms into
`W₀ R̄_t²`; the noise contribution is bounded by `W₁ c`. -/
lemma stopped_condExp_step {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {R A η : ℕ → Ω → ℝ} {τ : Ω → ℕ} {α W₀ W₁ c : ℝ} {t : ℕ}
    (hτ : MeasurableSet[ℱ t] {ω | t < τ ω})
    (hrec : ∀ ω, t < τ ω → R (t + 1) ω = A t ω * R t ω + η (t + 1) ω)
    (hbar_meas : StronglyMeasurable[ℱ t] (stoppedValue R τ t))
    (ha_meas : StronglyMeasurable[ℱ t] (fun ω => A t ω * R t ω))
    (hAsq : ∀ᵐ ω ∂μ, A t ω ^ 2 ≤ α ^ 2)
    (hη1 : μ[η (t + 1) | ℱ t] =ᵐ[μ] 0)
    (hη2 : μ[fun ω => η (t + 1) ω ^ 2 | ℱ t] ≤ᵐ[μ] fun _ => c)
    (hc : 0 ≤ c) (hW₁ : 0 ≤ W₁) (hWle : W₁ ≤ W₀)
    (hαWle : α ^ 2 * W₁ ≤ W₀)
    (hint_a2 : Integrable (fun ω => (A t ω * R t ω) ^ 2) μ)
    (hint_ae : Integrable (fun ω => A t ω * R t ω * η (t + 1) ω) μ)
    (hint_e2 : Integrable (fun ω => η (t + 1) ω ^ 2) μ)
    (hint_e : Integrable (η (t + 1)) μ)
    (hint_sq : Integrable (fun ω => (A t ω * R t ω + η (t + 1) ω) ^ 2) μ)
    (hint_bar : Integrable (fun ω => W₁ * stoppedValue R τ t ω ^ 2) μ) :
    μ[fun ω => W₁ * stoppedValue R τ (t + 1) ω ^ 2 | ℱ t]
      ≤ᵐ[μ] fun ω => W₀ * stoppedValue R τ t ω ^ 2 + W₁ * c := by
  let S₀ : Set Ω := {ω | τ ω ≤ t}
  let S₁ : Set Ω := {ω | t < τ ω}
  have hS₁ : MeasurableSet[ℱ t] S₁ := hτ
  have hS₀ : MeasurableSet[ℱ t] S₀ := by
    have heq : S₀ = S₁ᶜ := by
      ext ω
      simp [S₀, S₁]
    rw [heq]
    exact hS₁.compl
  have hbound : ∀ᵐ ω ∂μ, (A t ω * R t ω) ^ 2 ≤ α ^ 2 * R t ω ^ 2 := by
    filter_upwards [hAsq] with ω hω
    calc
      (A t ω * R t ω) ^ 2 = A t ω ^ 2 * R t ω ^ 2 := by ring
      _ ≤ α ^ 2 * R t ω ^ 2 := mul_le_mul_of_nonneg_right hω (sq_nonneg _)
  have hactive := condExp_indicator_add_sq_le (S := S₁)
    (a := fun ω => A t ω * R t ω) (e := η (t + 1))
    (b := fun ω => α ^ 2 * R t ω ^ 2) (c := c)
    (ℱ.le t) hS₁ ha_meas hbound hη1 hη2 hint_a2 hint_ae hint_e2 hint_e hint_sq
  have hint₀ : Integrable (S₀.indicator
      (fun ω => W₁ * stoppedValue R τ t ω ^ 2)) μ :=
    hint_bar.indicator ((ℱ.le t) _ hS₀)
  have hint₁ : Integrable (S₁.indicator
      (fun ω => W₁ * (A t ω * R t ω + η (t + 1) ω) ^ 2)) μ :=
    (hint_sq.const_mul W₁).indicator ((ℱ.le t) _ hS₁)
  have hdec : (fun ω => W₁ * stoppedValue R τ (t + 1) ω ^ 2)
      = S₀.indicator (fun ω => W₁ * stoppedValue R τ t ω ^ 2)
        + S₁.indicator (fun ω => W₁ * (A t ω * R t ω + η (t + 1) ω) ^ 2) := by
    ext ω
    exact stoppedValue_succ_sq_decomposition hrec ω
  rw [hdec]
  refine (condExp_add hint₀ hint₁ (ℱ t)).trans_le ?_
  have hstop : μ[S₀.indicator
      (fun ω => W₁ * stoppedValue R τ t ω ^ 2) | ℱ t]
      = S₀.indicator (fun ω => W₁ * stoppedValue R τ t ω ^ 2) := by
    exact condExp_of_stronglyMeasurable (ℱ.le t)
      ((hbar_meas.pow 2).const_mul W₁ |>.indicator hS₀) hint₀
  have hactiveW : μ[S₁.indicator
      (fun ω => W₁ * (A t ω * R t ω + η (t + 1) ω) ^ 2) | ℱ t]
      ≤ᵐ[μ] S₁.indicator (fun ω => W₁ * (α ^ 2 * R t ω ^ 2 + c)) := by
    have hfun : S₁.indicator
        (fun ω => W₁ * (A t ω * R t ω + η (t + 1) ω) ^ 2)
        = fun ω => W₁ * S₁.indicator
            (fun ω => (A t ω * R t ω + η (t + 1) ω) ^ 2) ω := by
      ext ω
      by_cases h : ω ∈ S₁ <;> simp [h]
    rw [hfun]
    refine (condExp_smul W₁
      (S₁.indicator (fun ω => (A t ω * R t ω + η (t + 1) ω) ^ 2))
      (ℱ t)).trans_le ?_
    filter_upwards [hactive] with ω hω
    simpa [smul_eq_mul, Set.indicator_apply] using mul_le_mul_of_nonneg_left hω hW₁
  rw [hstop]
  filter_upwards [hactiveW] with ω hω
  refine (add_le_add_right hω _).trans ?_
  by_cases h : ω ∈ S₀
  · have hn : ω ∉ S₁ := by
      simpa [S₀, S₁, Nat.not_lt] using h
    simp only [Set.indicator_of_mem h, Set.indicator_of_notMem hn]
    have hs : W₁ * stoppedValue R τ t ω ^ 2
        ≤ W₀ * stoppedValue R τ t ω ^ 2 :=
      mul_le_mul_of_nonneg_right hWle (sq_nonneg _)
    linarith [mul_nonneg hW₁ hc]
  · have ha : ω ∈ S₁ := by
      simpa [S₀, S₁, Nat.not_lt] using h
    have hbar : stoppedValue R τ t ω = R t ω := by
      simp only [stoppedValue]
      rw [Nat.min_eq_left (Nat.le_of_lt ha)]
    simp only [Set.indicator_of_notMem h, Set.indicator_of_mem ha, zero_add]
    rw [hbar]
    have hs : W₁ * (α ^ 2 * R t ω ^ 2)
        ≤ W₀ * R t ω ^ 2 := by
      nlinarith [sq_nonneg (R t ω)]
    nlinarith

/-- Integrate a conditional bound with an additive deterministic error over a probability
space. This is the scalar bridge used to turn `stopped_condExp_step` into the weighted
moment recursion. -/
lemma integral_le_of_condExp_add_const {Ω : Type*} {m0 m : MeasurableSpace Ω}
    (hm : m ≤ m0) {μ : @Measure Ω m0} [IsProbabilityMeasure μ]
    {G H : Ω → ℝ} {d : ℝ}
    (hcond : μ[G | m] ≤ᵐ[μ] fun ω => H ω + d)
    (hintH : Integrable H μ) :
    ∫ ω, G ω ∂μ ≤ (∫ ω, H ω ∂μ) + d := by
  calc
    ∫ ω, G ω ∂μ = ∫ ω, (μ[G | m]) ω ∂μ := (integral_condExp hm).symm
    _ ≤ ∫ ω, (H ω + d) ∂μ :=
      integral_mono_ae integrable_condExp (hintH.add (integrable_const d)) hcond
    _ = (∫ ω, H ω ∂μ) + ∫ _ω, d ∂μ :=
      integral_add hintH (integrable_const d)
    _ = (∫ ω, H ω ∂μ) + d := by simp

/-- **Scalar weighted stopped-moment recursion.** Integrating the output of
`stopped_condExp_step` gives the one-step inequality used in the telescoping argument. -/
lemma stopped_moment_recursion {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {W₀ W₁ c : ℝ} {t : ℕ}
    (hcond :
      μ[fun ω => W₁ * stoppedValue R τ (t + 1) ω ^ 2 | ℱ t]
        ≤ᵐ[μ] fun ω => W₀ * stoppedValue R τ t ω ^ 2 + W₁ * c)
    (hint_bar : Integrable (fun ω => W₀ * stoppedValue R τ t ω ^ 2) μ) :
    ∫ ω, W₁ * stoppedValue R τ (t + 1) ω ^ 2 ∂μ
      ≤ (∫ ω, W₀ * stoppedValue R τ t ω ^ 2 ∂μ) + W₁ * c :=
  integral_le_of_condExp_add_const (ℱ.le t) hcond hint_bar

/-- Finite telescoping of an additive one-step recursion:
`M_{t+1} ≤ M_t + d_t` implies `M_T ≤ M_0 + ∑_{t<T} d_t`. -/
lemma sum_recursion_bound {M d : ℕ → ℝ} {T : ℕ}
    (hstep : ∀ t, t < T → M (t + 1) ≤ M t + d t) :
    M T ≤ M 0 + ∑ t ∈ Finset.range T, d t := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hlast := hstep T (Nat.lt_succ_self T)
      have hprev : ∀ t, t < T → M (t + 1) ≤ M t + d t :=
        fun t ht => hstep t (lt_trans ht (Nat.lt_succ_self T))
      calc
        M (T + 1) ≤ M T + d T := hlast
        _ ≤ (M 0 + ∑ t ∈ Finset.range T, d t) + d T :=
          add_le_add_left (ih hprev) _
        _ = M 0 + ∑ t ∈ Finset.range (T + 1), d t := by
          rw [Finset.sum_range_succ]
          ring

/-- Telescope the scalar weighted stopped-moment recursion over a finite horizon. -/
lemma stopped_moment_telescope {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {W c : ℕ → ℝ} {T : ℕ}
    (hstep : ∀ t, t < T →
      (∫ ω, W (t + 1) * stoppedValue R τ (t + 1) ω ^ 2 ∂μ)
        ≤ (∫ ω, W t * stoppedValue R τ t ω ^ 2 ∂μ) + W (t + 1) * c t) :
    (∫ ω, W T * stoppedValue R τ T ω ^ 2 ∂μ)
      ≤ (∫ ω, W 0 * stoppedValue R τ 0 ω ^ 2 ∂μ)
        + ∑ t ∈ Finset.range T, W (t + 1) * c t :=
  sum_recursion_bound
    (M := fun s => ∫ ω, W s * stoppedValue R τ s ω ^ 2 ∂μ)
    (d := fun s => W (s + 1) * c s) (T := T) hstep

/-- A uniform per-step bound controls the accumulated weighted noise over a finite horizon. -/
lemma sum_weighted_noise_le {W c : ℕ → ℝ} {T : ℕ} {D : ℝ}
    (hbound : ∀ t, t < T → W (t + 1) * c t ≤ D) :
    ∑ t ∈ Finset.range T, W (t + 1) * c t ≤ T * D := by
  calc
    ∑ t ∈ Finset.range T, W (t + 1) * c t
        ≤ ∑ _t ∈ Finset.range T, D := by
          exact Finset.sum_le_sum fun t ht => hbound t (Finset.mem_range.mp ht)
    _ = T * D := by simp

/-- The paper's amplification bound turns each backward-weighted variance term into the
uniform error `C K² / N`. -/
lemma backWeight_noise_le {α σ : ℕ → ℝ} {T t : ℕ} {C N K : ℝ}
    (hCN : 0 ≤ C / N)
    (hamp : backWeight α T (t + 1) * σ t ^ 2 ≤ K ^ 2) :
    backWeight α T (t + 1) * (C * σ t ^ 2 / N) ≤ C * K ^ 2 / N := by
  calc
    backWeight α T (t + 1) * (C * σ t ^ 2 / N)
        = (C / N) * (backWeight α T (t + 1) * σ t ^ 2) := by ring
    _ ≤ (C / N) * K ^ 2 := mul_le_mul_of_nonneg_left hamp hCN
    _ = C * K ^ 2 / N := by ring

/-- Telescope the weighted stopped-moment recursion when every weighted noise term has the
same deterministic upper bound. -/
lemma stopped_moment_uniform_bound {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {W c : ℕ → ℝ} {T : ℕ} {D : ℝ}
    (hstep : ∀ t, t < T →
      (∫ ω, W (t + 1) * stoppedValue R τ (t + 1) ω ^ 2 ∂μ)
        ≤ (∫ ω, W t * stoppedValue R τ t ω ^ 2 ∂μ) + W (t + 1) * c t)
    (hbound : ∀ t, t < T → W (t + 1) * c t ≤ D) :
    (∫ ω, W T * stoppedValue R τ T ω ^ 2 ∂μ)
      ≤ (∫ ω, W 0 * stoppedValue R τ 0 ω ^ 2 ∂μ) + T * D := by
  exact (stopped_moment_telescope hstep).trans
    (add_le_add_right (sum_weighted_noise_le hbound) _)

/-- The stopped-moment telescope specialized to the paper's backward weights and variance
scale. -/
lemma stopped_moment_backWeight_bound {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {α σ : ℕ → ℝ}
    {T : ℕ} {C N K : ℝ}
    (hstep : ∀ t, t < T →
      (∫ ω, backWeight α T (t + 1) * stoppedValue R τ (t + 1) ω ^ 2 ∂μ)
        ≤ (∫ ω, backWeight α T t * stoppedValue R τ t ω ^ 2 ∂μ)
          + backWeight α T (t + 1) * (C * σ t ^ 2 / N))
    (hCN : 0 ≤ C / N)
    (hamp : ∀ t, t < T → backWeight α T (t + 1) * σ t ^ 2 ≤ K ^ 2) :
    (∫ ω, backWeight α T T * stoppedValue R τ T ω ^ 2 ∂μ)
      ≤ (∫ ω, backWeight α T 0 * stoppedValue R τ 0 ω ^ 2 ∂μ)
        + T * (C * K ^ 2 / N) := by
  exact stopped_moment_uniform_bound hstep fun t ht =>
    backWeight_noise_le hCN (hamp t ht)

/-- Endpoint-normalized form of `stopped_moment_backWeight_bound`: `W_T = 1` and the
time-zero stopped value is the original initial value. -/
lemma stopped_moment_backWeight_endpoints {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {α σ : ℕ → ℝ}
    {T : ℕ} {C N K : ℝ}
    (hstep : ∀ t, t < T →
      (∫ ω, backWeight α T (t + 1) * stoppedValue R τ (t + 1) ω ^ 2 ∂μ)
        ≤ (∫ ω, backWeight α T t * stoppedValue R τ t ω ^ 2 ∂μ)
          + backWeight α T (t + 1) * (C * σ t ^ 2 / N))
    (hCN : 0 ≤ C / N)
    (hamp : ∀ t, t < T → backWeight α T (t + 1) * σ t ^ 2 ≤ K ^ 2) :
    (∫ ω, stoppedValue R τ T ω ^ 2 ∂μ)
      ≤ backWeight α T 0 * (∫ ω, R 0 ω ^ 2 ∂μ) + T * (C * K ^ 2 / N) := by
  simpa [stoppedValue, integral_const_mul] using
    (stopped_moment_backWeight_bound hstep hCN hamp)

/-- **Stopped second-moment tracking bound** (paper
`eq:common-stopped-orbit-tracking`). The variance constant is normalized to `C ≥ 1`,
as permitted by enlarging it, so the initial and accumulated-noise terms share one
prefactor. -/
lemma stopped_moment_tracking_bound {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {α σ : ℕ → ℝ}
    {T : ℕ} {C N : ℝ}
    (hstep : ∀ t, t < T →
      (∫ ω, backWeight α T (t + 1) * stoppedValue R τ (t + 1) ω ^ 2 ∂μ)
        ≤ (∫ ω, backWeight α T t * stoppedValue R τ t ω ^ 2 ∂μ)
          + backWeight α T (t + 1) * (C * σ t ^ 2 / N))
    (hCN : 0 ≤ C / N) (hC : 1 ≤ C)
    (hα : ∀ u, u < T → 0 ≤ α u)
    (hσ : ∀ t, t < T → 0 ≤ σ t) :
    (∫ ω, stoppedValue R τ T ω ^ 2 ∂μ)
      ≤ C * trackingAmplification α σ T ^ 2
        * ((∫ ω, R 0 ω ^ 2 ∂μ) + T / N) := by
  let K := trackingAmplification α σ T
  have hbase := stopped_moment_backWeight_endpoints (K := K) hstep hCN
    (fun t ht => backWeight_mul_sigma_sq_le_trackingAmplification_sq hα ht (hσ t ht))
  have hW : backWeight α T 0 ≤ K ^ 2 :=
    backWeight_zero_le_trackingAmplification_sq hα
  have hm0 : 0 ≤ ∫ ω, R 0 ω ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg (R 0 ω)
  have hWK : backWeight α T 0 ≤ C * K ^ 2 := by
    calc
      backWeight α T 0 ≤ K ^ 2 := hW
      _ ≤ C * K ^ 2 := by nlinarith [sq_nonneg K]
  have hinit :
      backWeight α T 0 * (∫ ω, R 0 ω ^ 2 ∂μ)
        ≤ C * K ^ 2 * (∫ ω, R 0 ω ^ 2 ∂μ) :=
    mul_le_mul_of_nonneg_right hWK hm0
  calc
    (∫ ω, stoppedValue R τ T ω ^ 2 ∂μ)
        ≤ backWeight α T 0 * (∫ ω, R 0 ω ^ 2 ∂μ)
          + T * (C * K ^ 2 / N) := hbase
    _ ≤ C * K ^ 2 * (∫ ω, R 0 ω ^ 2 ∂μ) + T * (C * K ^ 2 / N) :=
      add_le_add_left hinit _
    _ = C * K ^ 2 * ((∫ ω, R 0 ω ^ 2 ∂μ) + T / N) := by ring

/-! ### Exit probability -/

/-- Pointwise Chebyshev input for a first-exit time: on `{τ ≤ T}`, the stopped process
at time `T` equals the process at the exit time and hence has magnitude greater than
the exit threshold. -/
lemma exit_indicator_sq_le_stopped {Ω : Type*} {R : ℕ → Ω → ℝ} {τ : Ω → ℕ}
    {T : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hexit : ∀ ω, τ ω ≤ T → δ < |R (τ ω) ω|) (ω : Ω) :
    {ω | τ ω ≤ T}.indicator (fun _ => (1 : ℝ)) ω * δ ^ 2
      ≤ stoppedValue R τ T ω ^ 2 := by
  by_cases hτ : τ ω ≤ T
  · rw [Set.indicator_of_mem (show ω ∈ {ω | τ ω ≤ T} from hτ), one_mul]
    simp only [stoppedValue]
    rw [Nat.min_eq_right hτ]
    have hsquare : δ ^ 2 ≤ |R (τ ω) ω| ^ 2 :=
      (sq_le_sq₀ hδ (abs_nonneg _)).mpr (le_of_lt (hexit ω hτ))
    simpa only [sq_abs] using hsquare
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | τ ω ≤ T} from hτ), zero_mul]
    exact sq_nonneg _

/-- Integrating `exit_indicator_sq_le_stopped` gives the Chebyshev numerator bound
`δ² μ{τ≤T} ≤ 𝔼[R̄_T²]`. -/
lemma exit_prob_mul_sq_le_stopped_moment {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {T : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hS : MeasurableSet {ω | τ ω ≤ T})
    (hexit : ∀ ω, τ ω ≤ T → δ < |R (τ ω) ω|)
    (hint : Integrable (fun ω => stoppedValue R τ T ω ^ 2) μ) :
    δ ^ 2 * μ.real {ω | τ ω ≤ T}
      ≤ ∫ ω, stoppedValue R τ T ω ^ 2 ∂μ := by
  let S : Set Ω := {ω | τ ω ≤ T}
  have hleft : Integrable (S.indicator (fun _ => δ ^ 2)) μ :=
    (integrable_const (δ ^ 2)).indicator hS
  have hpw : ∀ ω, S.indicator (fun _ => δ ^ 2) ω
      ≤ stoppedValue R τ T ω ^ 2 := by
    intro ω
    have h := exit_indicator_sq_le_stopped hδ hexit ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      simpa [S, Set.indicator_of_mem hω] using h
    · rw [Set.indicator_of_notMem hω]
      exact sq_nonneg _
  calc
    δ ^ 2 * μ.real {ω | τ ω ≤ T}
        = ∫ ω, S.indicator (fun _ => δ ^ 2) ω ∂μ := by
          rw [integral_indicator_const (δ ^ 2) hS, smul_eq_mul]
          ring
    _ ≤ ∫ ω, stoppedValue R τ T ω ^ 2 ∂μ :=
      integral_mono hleft hint hpw

/-- Chebyshev form of `exit_prob_mul_sq_le_stopped_moment`, after division by a
positive threshold squared. -/
lemma exit_prob_le_stopped_moment_div {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {T : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hS : MeasurableSet {ω | τ ω ≤ T})
    (hexit : ∀ ω, τ ω ≤ T → δ < |R (τ ω) ω|)
    (hint : Integrable (fun ω => stoppedValue R τ T ω ^ 2) μ) :
    μ.real {ω | τ ω ≤ T}
      ≤ (∫ ω, stoppedValue R τ T ω ^ 2 ∂μ) / δ ^ 2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hδ)]
  have h := exit_prob_mul_sq_le_stopped_moment hδ.le hS hexit hint
  simpa [mul_comm] using h

/-- Chebyshev's stopped-process bound when the moment is evaluated at a later
time than the exit-event horizon. -/
lemma exit_prob_le_stopped_moment_div_of_le
    {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {T S : ℕ} {δ : ℝ}
    (hTS : T ≤ S) (hδ : 0 < δ)
    (hE : MeasurableSet {ω | τ ω ≤ T})
    (hexit : ∀ ω, τ ω ≤ T → δ < |R (τ ω) ω|)
    (hint : Integrable (fun ω => stoppedValue R τ S ω ^ 2) μ) :
    μ.real {ω | τ ω ≤ T}
      ≤ (∫ ω, stoppedValue R τ S ω ^ 2 ∂μ) / δ ^ 2 := by
  let E : Set Ω := {ω | τ ω ≤ T}
  have hleft : Integrable (E.indicator (fun _ => δ ^ 2)) μ :=
    (integrable_const (δ ^ 2)).indicator hE
  have hpw : ∀ ω, E.indicator (fun _ => δ ^ 2) ω
      ≤ stoppedValue R τ S ω ^ 2 := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      have hτS : τ ω ≤ S := (show τ ω ≤ T from hω).trans hTS
      have hsquare : δ ^ 2 ≤ |R (τ ω) ω| ^ 2 :=
        (sq_le_sq₀ hδ.le (abs_nonneg _)).mpr
          (le_of_lt (hexit ω hω))
      simp only [stoppedValue]
      rw [Nat.min_eq_right hτS]
      simpa only [sq_abs] using hsquare
    · rw [Set.indicator_of_notMem hω]
      exact sq_nonneg _
  have hmul :
      δ ^ 2 * μ.real {ω | τ ω ≤ T}
        ≤ ∫ ω, stoppedValue R τ S ω ^ 2 ∂μ := by
    calc
      δ ^ 2 * μ.real {ω | τ ω ≤ T}
          = ∫ ω, E.indicator (fun _ => δ ^ 2) ω ∂μ := by
            rw [integral_indicator_const (δ ^ 2) hE, smul_eq_mul]
            ring
      _ ≤ ∫ ω, stoppedValue R τ S ω ^ 2 ∂μ :=
        integral_mono hleft hint hpw
  rw [le_div_iff₀ (sq_pos_of_pos hδ)]
  simpa [mul_comm] using hmul

/-- **Orbit exit-probability bound** (paper `eq:common-orbit-exit-bound`). Chebyshev's
inequality for the stopped process, combined with `stopped_moment_tracking_bound`. -/
lemma orbit_exit_prob_bound {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {R : ℕ → Ω → ℝ} {τ : Ω → ℕ} {α σ : ℕ → ℝ}
    {T : ℕ} {C N δ : ℝ}
    (hstep : ∀ t, t < T →
      (∫ ω, backWeight α T (t + 1) * stoppedValue R τ (t + 1) ω ^ 2 ∂μ)
        ≤ (∫ ω, backWeight α T t * stoppedValue R τ t ω ^ 2 ∂μ)
          + backWeight α T (t + 1) * (C * σ t ^ 2 / N))
    (hCN : 0 ≤ C / N) (hC : 1 ≤ C)
    (hα : ∀ u, u < T → 0 ≤ α u)
    (hσ : ∀ t, t < T → 0 ≤ σ t)
    (hδ : 0 < δ) (hS : MeasurableSet {ω | τ ω ≤ T})
    (hexit : ∀ ω, τ ω ≤ T → δ < |R (τ ω) ω|)
    (hint : Integrable (fun ω => stoppedValue R τ T ω ^ 2) μ) :
    μ.real {ω | τ ω ≤ T}
      ≤ (C * trackingAmplification α σ T ^ 2 / δ ^ 2)
        * ((∫ ω, R 0 ω ^ 2 ∂μ) + T / N) := by
  have hcheb := exit_prob_le_stopped_moment_div hδ hS hexit hint
  have hmoment := stopped_moment_tracking_bound hstep hCN hC hα hσ
  calc
    μ.real {ω | τ ω ≤ T}
        ≤ (∫ ω, stoppedValue R τ T ω ^ 2 ∂μ) / δ ^ 2 := hcheb
    _ ≤ (C * trackingAmplification α σ T ^ 2
          * ((∫ ω, R 0 ω ^ 2 ∂μ) + T / N)) / δ ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hδ)).mpr hmoment
    _ = (C * trackingAmplification α σ T ^ 2 / δ ^ 2)
          * ((∫ ω, R 0 ω ^ 2 ∂μ) + T / N) := by ring

end AbsorptionCutoff
