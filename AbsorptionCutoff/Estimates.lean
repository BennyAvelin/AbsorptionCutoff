/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Common scalar estimates

Reusable estimates from the paper's §2 / Appendix A. This file starts with the
deterministic engine behind the killed second-moment bound
(`lem:common-stopped-orbit-tracking`, eq. `eq:common-killed-orbit-tracking`): the
closed form obtained by iterating a geometric-type recursion.

In the paper's application, `m t = 𝔼[𝓡_t² 1_{τ>t}]`, `a u = α_{u}²` (squared
amplification bounds), and `b s = C σ_s² / N`; the one-step probabilistic bound
`m (t+1) ≤ α_t² m t + C σ_t²/N` (martingale-difference orthogonality of the noise)
feeds into `geom_recursion_bound` to give the explicit killed-moment estimate.

## Main results
* `AbsorptionCutoff.geom_recursion_bound` — iterating `m (t+1) ≤ a t · m t + b t`
  (`a ≥ 0`) into the explicit product/sum bound.
* `AbsorptionCutoff.geom_recursion_bound_const` — the uniform simplification
  `m t ≤ αᵗ · m 0 + t · αᵗ · β` under `a u ≤ α` (`α ≥ 1`), `b s ≤ β`.
* `AbsorptionCutoff.backWeight` — the backward weights `W_t = ∏_{u=t}^{T-1} (1 ∨ α_u²)`
  for the stopped-moment telescoping, with `W_T = 1`, `1 ≤ W_t`, `W_{t+1} ≤ W_t`,
  and `α_t² · W_{t+1} ≤ W_t`.

## Downstream use
`AbsorptionCutoff.StoppedMoment` supplies the filtration and stopped-moment wrappers.
`AbsorptionCutoff.RadiusConcentration` applies those wrappers and the backward weights
below to the paper's tracking and exit-probability estimates.
-/

open Finset MeasureTheory
open scoped ENNReal

namespace AbsorptionCutoff

/-- Hölder interpolation bounds a fractional moment on a measurable set by the
full first moment and the measure of the set. -/
theorem integrableOn_rpow_and_setIntegral_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f)
    {s : Set Ω} (hs : MeasurableSet s) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    IntegrableOn (fun ω => f ω ^ θ) s μ ∧
      (∫ ω in s, f ω ^ θ ∂μ) ≤
        (∫ ω, f ω ∂μ) ^ θ * (μ.real s) ^ (1 - θ) := by
  have hf_norm : Integrable (fun ω => ‖f ω‖ ^ (1 : ℝ)) μ :=
    hf.congr (hf0.mono fun ω hω => by simp [Real.norm_of_nonneg hω])
  have hθ_norm : Integrable (fun ω => ‖f ω‖ ^ θ) μ :=
    integrable_norm_rpow_of_le hf.aestronglyMeasurable hθ0.le zero_le_one hθ1.le hf_norm
  have hθ : Integrable (fun ω => f ω ^ θ) μ :=
    hθ_norm.congr (hf0.mono fun ω hω => by simp [Real.norm_of_nonneg hω])
  refine ⟨hθ.integrableOn, ?_⟩
  let F : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (f ω)
  let G : Ω → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hF : AEMeasurable F μ :=
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hG : AEMeasurable G μ :=
    (measurable_const.indicator hs).aemeasurable
  have hholder := ENNReal.lintegral_mul_norm_pow_le hF hG hθ0.le
    (sub_nonneg.mpr hθ1.le) (by ring : θ + (1 - θ) = 1)
  have hFint : (∫⁻ ω, F ω ∂μ) = ENNReal.ofReal (∫ ω, f ω ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hf hf0).symm
  have hGint : (∫⁻ ω, G ω ∂μ) = μ s := by
    rw [show G = s.indicator (fun _ => 1) from rfl, lintegral_indicator hs]
    simp
  have hf0s : 0 ≤ᵐ[μ.restrict s] f := ae_restrict_of_ae hf0
  have hleft :
      ENNReal.ofReal (∫ ω in s, f ω ^ θ ∂μ) =
        ∫⁻ ω, F ω ^ θ * G ω ^ (1 - θ) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hθ.integrableOn
      (hf0s.mono fun ω hω => Real.rpow_nonneg hω θ)]
    rw [← lintegral_indicator hs]
    apply lintegral_congr_ae
    filter_upwards [hf0] with ω hω
    by_cases hωs : ω ∈ s
    · simp [F, G, hωs, ENNReal.ofReal_rpow_of_nonneg hω hθ0.le]
    · simp [G, hωs, sub_pos.mpr hθ1]
  have hENN :
      ENNReal.ofReal (∫ ω in s, f ω ^ θ ∂μ) ≤
        ENNReal.ofReal (∫ ω, f ω ∂μ) ^ θ * (μ s) ^ (1 - θ) := by
    rw [hleft]
    simpa [hFint, hGint] using hholder
  have hfi_nonneg : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg_of_ae hf0
  have hθi_nonneg : 0 ≤ ∫ ω in s, f ω ^ θ ∂μ :=
    integral_nonneg_of_ae (hf0s.mono fun ω hω => Real.rpow_nonneg hω θ)
  have hreal := ENNReal.toReal_mono (by finiteness) hENN
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hθi_nonneg, ENNReal.toReal_ofReal hfi_nonneg] at hreal
  exact hreal

/-- Hölder interpolation for negative powers: a smaller negative moment on a
measurable set is controlled by a larger full negative moment and the measure
of the set. -/
theorem integrableOn_neg_rpow_and_setIntegral_neg_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    {N α γ : ℝ} (hN : 0 < N) (hγ : 0 < γ) (hγα : γ < α)
    (hαmom : Integrable (fun ω => X ω ^ (-α * N)) μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    IntegrableOn (fun ω => X ω ^ (-γ * N)) s μ ∧
      (∫ ω in s, X ω ^ (-γ * N) ∂μ) ≤
        (∫ ω, X ω ^ (-α * N) ∂μ) ^ (γ / α) *
          (μ.real s) ^ (1 - γ / α) := by
  have hα : 0 < α := hγ.trans hγα
  have hholder :=
    integrableOn_rpow_and_setIntegral_rpow_le hαmom
      (hXpos.mono fun ω hω => Real.rpow_nonneg hω.le _)
      hs (div_pos hγ hα) ((div_lt_one hα).2 hγα)
  have hrpow :
      (fun ω => (X ω ^ (-α * N)) ^ (γ / α)) =ᵐ[μ]
        (fun ω => X ω ^ (-γ * N)) := by
    filter_upwards [hXpos] with ω hω
    rw [← Real.rpow_mul hω.le]
    congr 1
    field_simp [hα.ne']
  have hrpow_restrict := ae_restrict_of_ae (s := s) hrpow
  refine ⟨hholder.1.congr hrpow_restrict, ?_⟩
  calc
    (∫ ω in s, X ω ^ (-γ * N) ∂μ) =
        ∫ ω in s, (X ω ^ (-α * N)) ^ (γ / α) ∂μ :=
      (integral_congr_ae hrpow_restrict).symm
    _ ≤ (∫ ω, X ω ^ (-α * N) ∂μ) ^ (γ / α) *
          (μ.real s) ^ (1 - γ / α) := hholder.2

/-- A strict multiplicative gap remains strict after small positive losses in
both factors. -/
lemma exists_eps_delta_of_one_lt_mul {a μ : ℝ}
    (ha : 0 < a) (h : 1 < a * μ) :
    ∃ ε δ : ℝ, ε ∈ Set.Ioo 0 1 ∧ 0 < δ ∧
      1 < (1 - ε) * a * (μ - δ) := by
  let δ : ℝ := (a * μ - 1) / (2 * a)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact div_pos (sub_pos.mpr h) (mul_pos (by norm_num) ha)
  have hremain : 1 < a * (μ - δ) := by
    dsimp only [δ]
    field_simp [ha.ne']
    nlinarith
  let b : ℝ := a * (μ - δ)
  have hb : 1 < b := by simpa only [b] using hremain
  let ε : ℝ := (b - 1) / (2 * b)
  have hεpos : 0 < ε := by
    dsimp only [ε]
    exact div_pos (sub_pos.mpr hb)
      (mul_pos (by norm_num) (zero_lt_one.trans hb))
  have hεone : ε < 1 := by
    dsimp only [ε]
    rw [div_lt_one (mul_pos (by norm_num) (zero_lt_one.trans hb))]
    linarith
  refine ⟨ε, δ, ⟨hεpos, hεone⟩, hδ, ?_⟩
  rw [mul_assoc]
  change 1 < (1 - ε) * b
  dsimp only [ε]
  field_simp [(zero_lt_one.trans hb).ne']
  nlinarith

/-- Iterating a geometric-type recursion `m (t+1) ≤ a t · m t + b t` with nonnegative
multipliers gives the explicit killed-moment bound (paper `eq:common-killed-orbit-tracking`):
`m t ≤ (∏_{u<t} a u) · m 0 + ∑_{s<t} (∏_{s<u<t} a u) · b s`. -/
lemma geom_recursion_bound {m a b : ℕ → ℝ} (ha : ∀ u, 0 ≤ a u)
    (hrec : ∀ t, m (t + 1) ≤ a t * m t + b t) (t : ℕ) :
    m t ≤ (∏ u ∈ range t, a u) * m 0
      + ∑ s ∈ range t, (∏ u ∈ Ico (s + 1) t, a u) * b s := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hsum : ∑ s ∈ range t, (∏ u ∈ Ico (s + 1) (t + 1), a u) * b s
        = a t * ∑ s ∈ range t, (∏ u ∈ Ico (s + 1) t, a u) * b s := by
      rw [mul_sum]
      apply sum_congr rfl
      intro s hs
      rw [mem_range] at hs
      rw [prod_Ico_succ_top (by omega : s + 1 ≤ t)]
      ring
    have hstep : a t * ((∏ u ∈ range t, a u) * m 0
        + ∑ s ∈ range t, (∏ u ∈ Ico (s + 1) t, a u) * b s) + b t
        = (∏ u ∈ range (t + 1), a u) * m 0
          + ∑ s ∈ range (t + 1), (∏ u ∈ Ico (s + 1) (t + 1), a u) * b s := by
      rw [prod_range_succ, sum_range_succ, Ico_self, prod_empty, one_mul, hsum]
      ring
    calc m (t + 1) ≤ a t * m t + b t := hrec t
      _ ≤ a t * ((∏ u ∈ range t, a u) * m 0
            + ∑ s ∈ range t, (∏ u ∈ Ico (s + 1) t, a u) * b s) + b t := by
          have := mul_le_mul_of_nonneg_left ih (ha t); linarith
      _ = _ := hstep

/-- A scalar affine recursion with contraction factor `0 ≤ a < 1` stays below the
larger of its initial value and the fixed point `B / (1 - a)`. No sign assumption on
`B` or on the sequence is needed. -/
lemma geom_recursion_bound_contraction {m : ℕ → ℝ} {a B : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hrec : ∀ t, m (t + 1) ≤ a * m t + B) (t : ℕ) :
    m t ≤ max (m 0) (B / (1 - a)) := by
  let M := max (m 0) (B / (1 - a))
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  have hfixed : B / (1 - a) ≤ M := le_max_right _ _
  have hBM : B ≤ M * (1 - a) := (div_le_iff₀ hden).mp hfixed
  change m t ≤ M
  induction t with
  | zero =>
      exact le_max_left _ _
  | succ t ih =>
      calc
        m (t + 1) ≤ a * m t + B := hrec t
        _ ≤ a * M + B := add_le_add (mul_le_mul_of_nonneg_left ih ha0) le_rfl
        _ ≤ a * M + M * (1 - a) := add_le_add le_rfl hBM
        _ = M := by ring

/-- Finite-horizon version of `geom_recursion_bound_contraction`: the same
fixed-point bound at time `t` only needs the affine recursion before `t`. -/
lemma geom_recursion_bound_contraction_of_lt
    {m : ℕ → ℝ} {a B : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) {t : ℕ}
    (hrec : ∀ s < t, m (s + 1) ≤ a * m s + B) :
    m t ≤ max (m 0) (B / (1 - a)) := by
  let M := max (m 0) (B / (1 - a))
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  have hfixed : B / (1 - a) ≤ M := le_max_right _ _
  have hBM : B ≤ M * (1 - a) := (div_le_iff₀ hden).mp hfixed
  change m t ≤ M
  induction t with
  | zero =>
      exact le_max_left _ _
  | succ t ih =>
      have ih' : m t ≤ M :=
        ih (fun s hs => hrec s (hs.trans (Nat.lt_succ_self t)))
      calc
        m (t + 1) ≤ a * m t + B := hrec t (Nat.lt_succ_self t)
        _ ≤ a * M + B :=
          add_le_add (mul_le_mul_of_nonneg_left ih' ha0) le_rfl
        _ ≤ a * M + M * (1 - a) := add_le_add le_rfl hBM
        _ = M := by ring

/-- Finite iteration of a contractive affine recursion while retaining the
geometric decay of the initial value. -/
lemma geom_recursion_bound_contraction_pow_of_lt
    {m : ℕ → ℝ} {a B : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hB : 0 ≤ B) {t : ℕ}
    (hrec : ∀ s < t, m (s + 1) ≤ a * m s + B) :
    m t ≤ a ^ t * m 0 + B / (1 - a) := by
  have hden : 0 < 1 - a := sub_pos.mpr ha1
  induction t with
  | zero =>
      simp only [pow_zero, one_mul]
      exact le_add_of_nonneg_right (div_nonneg hB hden.le)
  | succ t ih =>
      have iht : m t ≤ a ^ t * m 0 + B / (1 - a) :=
        ih (fun s hs => hrec s (hs.trans (Nat.lt_succ_self t)))
      calc
        m (t + 1) ≤ a * m t + B := hrec t (Nat.lt_succ_self t)
        _ ≤ a * (a ^ t * m 0 + B / (1 - a)) + B :=
          add_le_add (mul_le_mul_of_nonneg_left iht ha0) le_rfl
        _ = a ^ (t + 1) * m 0 + B / (1 - a) := by
          field_simp [hden.ne']
          ring

/-- Every positive exponential rate eventually absorbs one natural factor
and leaves an inverse-natural bound. -/
lemma eventually_nat_mul_exp_neg_le_inv_nat
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N : ℝ) * Real.exp (-c * (N : ℝ)) ≤ 1 / (N : ℝ) := by
  have hscale :
      Filter.Tendsto (fun N : ℕ => c * (N : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hlim :
      Filter.Tendsto
        (fun N : ℕ =>
          (c * (N : ℝ)) ^ 2 * Real.exp (-(c * (N : ℝ))))
        Filter.atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hscale
  have hsmall :
      ∀ᶠ N : ℕ in Filter.atTop,
        (c * (N : ℝ)) ^ 2 * Real.exp (-(c * (N : ℝ))) ≤ c ^ 2 :=
    hlim.eventually_le_const (sq_pos_of_pos hc)
  filter_upwards [hsmall, Filter.eventually_ge_atTop (1 : ℕ)] with
      N hNbound hN
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hsq :
      (N : ℝ) ^ 2 * Real.exp (-c * (N : ℝ)) ≤ 1 := by
    calc
      (N : ℝ) ^ 2 * Real.exp (-c * (N : ℝ)) =
          ((c * (N : ℝ)) ^ 2 *
            Real.exp (-(c * (N : ℝ)))) / c ^ 2 := by
        field_simp [hc.ne']
      _ ≤ c ^ 2 / c ^ 2 :=
        div_le_div_of_nonneg_right hNbound (sq_nonneg c)
      _ = 1 := by field_simp [hc.ne']
  rw [le_div_iff₀ hNreal]
  calc
    (N : ℝ) * Real.exp (-c * (N : ℝ)) * (N : ℝ) =
        (N : ℝ) ^ 2 * Real.exp (-c * (N : ℝ)) := by ring
    _ ≤ 1 := hsq

/-- A varying natural horizon bounded by `C N` can be absorbed into the same
inverse-dimension envelope. -/
lemma eventually_two_nat_horizon_mul_exp_neg_le_mul_inv_nat
    {T : ℕ → ℕ} {C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      2 * (T N : ℝ) * Real.exp (-c * (N : ℝ)) ≤
        2 * C / (N : ℝ) := by
  filter_upwards
      [hT, eventually_nat_mul_exp_neg_le_inv_nat hc] with
      N hTN hdecay
  calc
    2 * (T N : ℝ) * Real.exp (-c * (N : ℝ)) ≤
        2 * (C * (N : ℝ)) * Real.exp (-c * (N : ℝ)) := by
      gcongr
    _ = 2 * C *
        ((N : ℝ) * Real.exp (-c * (N : ℝ))) := by ring
    _ ≤ 2 * C * (1 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg (by norm_num) hC)
    _ = 2 * C / (N : ℝ) := by ring

/-- Uniform version: with `a u ≤ α` (`α ≥ 1`) and `b s ≤ β`, the killed-moment bound
simplifies to `m t ≤ αᵗ · m 0 + t · αᵗ · β` — the form applied with the amplification
bound `K_N` in the paper. -/
lemma geom_recursion_bound_const {m a b : ℕ → ℝ} {α β : ℝ}
    (hα : 1 ≤ α) (hm0 : 0 ≤ m 0) (ha0 : ∀ u, 0 ≤ a u) (haα : ∀ u, a u ≤ α)
    (hb0 : ∀ s, 0 ≤ b s) (hbβ : ∀ s, b s ≤ β)
    (hrec : ∀ t, m (t + 1) ≤ a t * m t + b t) (t : ℕ) :
    m t ≤ α ^ t * m 0 + (t : ℝ) * α ^ t * β := by
  have hαt : (0 : ℝ) ≤ α ^ t := by positivity
  have hp1 : (∏ u ∈ range t, a u) ≤ α ^ t := by
    calc ∏ u ∈ range t, a u ≤ ∏ _u ∈ range t, α :=
          Finset.prod_le_prod (fun i _ => ha0 i) (fun i _ => haα i)
      _ = α ^ t := by rw [Finset.prod_const, Finset.card_range]
  have hterm1 : (∏ u ∈ range t, a u) * m 0 ≤ α ^ t * m 0 :=
    mul_le_mul_of_nonneg_right hp1 hm0
  have hsumbound : ∑ s ∈ range t, (∏ u ∈ Ico (s + 1) t, a u) * b s ≤ (t : ℝ) * α ^ t * β := by
    have hterm : ∀ s ∈ range t, (∏ u ∈ Ico (s + 1) t, a u) * b s ≤ α ^ t * β := by
      intro s _
      have hps : (∏ u ∈ Ico (s + 1) t, a u) ≤ α ^ t :=
        calc ∏ u ∈ Ico (s + 1) t, a u ≤ ∏ _u ∈ Ico (s + 1) t, α :=
              Finset.prod_le_prod (fun i _ => ha0 i) (fun i _ => haα i)
          _ = α ^ (t - (s + 1)) := by rw [Finset.prod_const, Nat.card_Ico]
          _ ≤ α ^ t := pow_le_pow_right₀ hα (by omega)
      calc (∏ u ∈ Ico (s + 1) t, a u) * b s ≤ α ^ t * b s :=
            mul_le_mul_of_nonneg_right hps (hb0 s)
        _ ≤ α ^ t * β := mul_le_mul_of_nonneg_left (hbβ s) hαt
    calc ∑ s ∈ range t, (∏ u ∈ Ico (s + 1) t, a u) * b s
        ≤ ∑ _s ∈ range t, α ^ t * β := Finset.sum_le_sum hterm
      _ = (t : ℝ) * α ^ t * β := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  linarith [geom_recursion_bound ha0 hrec t, hterm1, hsumbound]

/-! ### Backward weights for the stopped second-moment telescoping

Deterministic engine for the *stopped-moment* half of `lem:common-stopped-orbit-tracking`
(paper `eq:common-stopped-orbit-tracking`): the backward weights
`W_t = ∏_{u=t}^{T-1} (1 ∨ α_u²)`. Each factor is `≥ 1`, so the weights are `≥ 1`,
nonincreasing in `t`, satisfy `W_T = 1`, and dominate the forward multiplier via
`α_t² · W_{t+1} ≤ W_t`. These are exactly the algebraic facts used when telescoping
`𝔼[W_{t+1} R̄_{t+1}²] - 𝔼[W_t R̄_t²] ≤ C K_N²/N` in the stopped-moment estimate. -/

/-- Backward weights `W_t = ∏_{u=t}^{T-1} (1 ⊔ α_u²)` for the stopped-moment telescoping. -/
def backWeight (α : ℕ → ℝ) (T t : ℕ) : ℝ := ∏ u ∈ Ico t T, ((1 : ℝ) ⊔ α u ^ 2)

@[simp] lemma backWeight_self (α : ℕ → ℝ) (T : ℕ) : backWeight α T T = 1 := by
  simp [backWeight]

/-- Each backward weight is `≥ 1` (every factor `1 ⊔ α_u² ≥ 1`). -/
lemma one_le_backWeight (α : ℕ → ℝ) (T t : ℕ) : (1 : ℝ) ≤ backWeight α T t := by
  rw [backWeight]
  calc (1 : ℝ) = ∏ _u ∈ Ico t T, (1 : ℝ) := (Finset.prod_const_one).symm
    _ ≤ ∏ u ∈ Ico t T, (1 ⊔ α u ^ 2) :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) (fun u _ => le_max_left _ _)

lemma backWeight_nonneg (α : ℕ → ℝ) (T t : ℕ) : 0 ≤ backWeight α T t :=
  le_trans zero_le_one (one_le_backWeight α T t)

/-- Peel the bottom factor: `W_t = (1 ⊔ α_t²) · W_{t+1}` for `t < T`. -/
lemma backWeight_eq_mul_succ {α : ℕ → ℝ} {T t : ℕ} (ht : t < T) :
    backWeight α T t = (1 ⊔ α t ^ 2) * backWeight α T (t + 1) := by
  unfold backWeight
  rw [Finset.prod_eq_prod_Ico_succ_bot ht]

/-- The backward weights are nonincreasing: `W_{t+1} ≤ W_t` for `t < T`. -/
lemma backWeight_succ_le {α : ℕ → ℝ} {T t : ℕ} (ht : t < T) :
    backWeight α T (t + 1) ≤ backWeight α T t := by
  rw [backWeight_eq_mul_succ ht]
  exact le_mul_of_one_le_left (backWeight_nonneg α T (t + 1)) (le_max_left _ _)

/-- The weights dominate the forward multiplier: `α_t² · W_{t+1} ≤ W_t` for `t < T`. -/
lemma sq_mul_backWeight_succ_le {α : ℕ → ℝ} {T t : ℕ} (ht : t < T) :
    α t ^ 2 * backWeight α T (t + 1) ≤ backWeight α T t := by
  rw [backWeight_eq_mul_succ ht]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (backWeight_nonneg α T (t + 1))

/-! ### Finite-horizon tracking amplification -/

/-- The amplification scalar from `eq:common-tracking-amplification`: the maximum of `1`,
the multiplier products, and the noise-amplification products over `0 ≤ s < t ≤ T`. -/
def trackingAmplification (α σ : ℕ → ℝ) (T : ℕ) : ℝ :=
  (Finset.range T).fold max 1 fun s =>
    (Finset.Icc (s + 1) T).fold max 1 fun t =>
      (∏ u ∈ Finset.Ico s t, (1 ⊔ α u))
        ⊔ (σ s * ∏ u ∈ Finset.Ico (s + 1) t, (1 ⊔ α u))

/-- The tracking amplification scalar includes `1` among its defining candidates. -/
lemma one_le_trackingAmplification (α σ : ℕ → ℝ) (T : ℕ) :
    1 ≤ trackingAmplification α σ T := by
  unfold trackingAmplification
  rw [Finset.le_fold_max]
  exact Or.inl le_rfl

/-- A uniform bound on the sum of the multiplier and noise-amplification products
bounds the tracking amplification scalar. -/
lemma trackingAmplification_le_of_combination_le
    {α σ : ℕ → ℝ} {T : ℕ} {K : ℝ}
    (hK : 1 ≤ K)
    (hσ : ∀ s, s < T → 0 ≤ σ s)
    (hcomb : ∀ s t, s < t → t ≤ T →
      (∏ u ∈ Finset.Ico s t, (1 ⊔ α u))
        + σ s * ∏ u ∈ Finset.Ico (s + 1) t, (1 ⊔ α u) ≤ K) :
    trackingAmplification α σ T ≤ K := by
  unfold trackingAmplification
  rw [Finset.fold_max_le]
  refine ⟨hK, ?_⟩
  intro s hs
  rw [Finset.fold_max_le]
  refine ⟨hK, ?_⟩
  intro t ht
  rw [max_le_iff]
  have hst : s < t := Nat.succ_le_iff.mp (Finset.mem_Icc.mp ht).1
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  have hsT : s < T := lt_of_lt_of_le hst htT
  have hp0 : 0 ≤ ∏ u ∈ Finset.Ico s t, (1 ⊔ α u) :=
    Finset.prod_nonneg fun _ _ => le_trans zero_le_one (le_max_left _ _)
  have hnoise0 :
      0 ≤ σ s * ∏ u ∈ Finset.Ico (s + 1) t, (1 ⊔ α u) :=
    mul_nonneg (hσ s hsT)
      (Finset.prod_nonneg fun _ _ => le_trans zero_le_one (le_max_left _ _))
  have hsum := hcomb s t hst htT
  exact ⟨(le_add_of_nonneg_right hnoise0).trans hsum,
    (le_add_of_nonneg_left hp0).trans hsum⟩

/-- Every multiplier product in the defining finite horizon is bounded by the tracking
amplification scalar. -/
lemma tracking_product_le {α σ : ℕ → ℝ} {T s t : ℕ} (hst : s < t) (ht : t ≤ T) :
    (∏ u ∈ Finset.Ico s t, (1 ⊔ α u)) ≤ trackingAmplification α σ T := by
  have hsT : s < T := lt_of_lt_of_le hst ht
  have hinner :
      (∏ u ∈ Finset.Ico s t, (1 ⊔ α u))
        ≤ (Finset.Icc (s + 1) T).fold max 1 (fun t =>
          (∏ u ∈ Finset.Ico s t, (1 ⊔ α u))
            ⊔ (σ s * ∏ u ∈ Finset.Ico (s + 1) t, (1 ⊔ α u))) := by
    rw [Finset.le_fold_max]
    exact Or.inr ⟨t, Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hst, ht⟩,
      le_max_left _ _⟩
  unfold trackingAmplification
  rw [Finset.le_fold_max]
  exact Or.inr ⟨s, Finset.mem_range.mpr hsT, hinner⟩

/-- Every noise-amplification product in the defining finite horizon is bounded by the
tracking amplification scalar. -/
lemma tracking_noise_product_le {α σ : ℕ → ℝ} {T s t : ℕ} (hst : s < t) (ht : t ≤ T) :
    σ s * (∏ u ∈ Finset.Ico (s + 1) t, (1 ⊔ α u))
      ≤ trackingAmplification α σ T := by
  have hsT : s < T := lt_of_lt_of_le hst ht
  have hinner :
      σ s * (∏ u ∈ Finset.Ico (s + 1) t, (1 ⊔ α u))
        ≤ (Finset.Icc (s + 1) T).fold max 1 (fun t =>
          (∏ u ∈ Finset.Ico s t, (1 ⊔ α u))
            ⊔ (σ s * ∏ u ∈ Finset.Ico (s + 1) t, (1 ⊔ α u))) := by
    rw [Finset.le_fold_max]
    exact Or.inr ⟨t, Finset.mem_Icc.mpr ⟨Nat.succ_le_iff.mpr hst, ht⟩,
      le_max_right _ _⟩
  unfold trackingAmplification
  rw [Finset.le_fold_max]
  exact Or.inr ⟨s, Finset.mem_range.mpr hsT, hinner⟩

/-- For nonnegative multipliers, every backward weight is the square of its corresponding
unsquared suffix product. -/
lemma backWeight_eq_tracking_product_sq {α : ℕ → ℝ} {T s : ℕ}
    (hα : ∀ u, u < T → 0 ≤ α u) :
    backWeight α T s = (∏ u ∈ Finset.Ico s T, (1 ⊔ α u)) ^ 2 := by
  unfold backWeight
  have hfactor : ∀ u ∈ Finset.Ico s T, (1 ⊔ α u ^ 2) = (1 ⊔ α u) ^ 2 := by
    intro u hu
    have ha : 0 ≤ α u := hα u (Finset.mem_Ico.mp hu).2
    by_cases h : α u ≤ 1
    · have hs : α u ^ 2 ≤ 1 := by nlinarith
      rw [max_eq_left hs, max_eq_left h]
      norm_num
    · have h1 : 1 ≤ α u := le_of_not_ge h
      have hs : 1 ≤ α u ^ 2 := by nlinarith
      rw [max_eq_right hs, max_eq_right h1]
  rw [Finset.prod_congr rfl hfactor, ← Finset.prod_pow]

/-- Zero-start specialization of `backWeight_eq_tracking_product_sq`. -/
lemma backWeight_zero_eq_tracking_product_sq {α : ℕ → ℝ} {T : ℕ}
    (hα : ∀ u, u < T → 0 ≤ α u) :
    backWeight α T 0 = (∏ u ∈ Finset.Ico 0 T, (1 ⊔ α u)) ^ 2 :=
  backWeight_eq_tracking_product_sq hα

/-- The initial backward weight is bounded by the square of the tracking amplification
scalar. -/
lemma backWeight_zero_le_trackingAmplification_sq {α σ : ℕ → ℝ} {T : ℕ}
    (hα : ∀ u, u < T → 0 ≤ α u) :
    backWeight α T 0 ≤ trackingAmplification α σ T ^ 2 := by
  rw [backWeight_zero_eq_tracking_product_sq hα]
  have hK : 0 ≤ trackingAmplification α σ T :=
    le_trans zero_le_one (one_le_trackingAmplification α σ T)
  by_cases hT : T = 0
  · subst T
    simp only [Finset.Ico_self, Finset.prod_empty, one_pow]
    simpa using (sq_le_sq₀ zero_le_one hK).mpr (one_le_trackingAmplification α σ 0)
  · have hTpos : 0 < T := Nat.pos_of_ne_zero hT
    have hp : (∏ u ∈ Finset.Ico 0 T, (1 ⊔ α u))
        ≤ trackingAmplification α σ T :=
      tracking_product_le hTpos le_rfl
    have hp0 : 0 ≤ ∏ u ∈ Finset.Ico 0 T, (1 ⊔ α u) :=
      Finset.prod_nonneg fun _ _ => le_trans zero_le_one (le_max_left _ _)
    exact (sq_le_sq₀ hp0 hK).mpr hp

/-- Each backward-weighted noise scale is bounded by the square of the tracking
amplification scalar. -/
lemma backWeight_mul_sigma_sq_le_trackingAmplification_sq
    {α σ : ℕ → ℝ} {T t : ℕ}
    (hα : ∀ u, u < T → 0 ≤ α u) (ht : t < T) (hσ : 0 ≤ σ t) :
    backWeight α T (t + 1) * σ t ^ 2 ≤ trackingAmplification α σ T ^ 2 := by
  rw [backWeight_eq_tracking_product_sq hα]
  have hp0 : 0 ≤ ∏ u ∈ Finset.Ico (t + 1) T, (1 ⊔ α u) :=
    Finset.prod_nonneg fun _ _ => le_trans zero_le_one (le_max_left _ _)
  have hnoise0 : 0 ≤ σ t * ∏ u ∈ Finset.Ico (t + 1) T, (1 ⊔ α u) :=
    mul_nonneg hσ hp0
  have hK : 0 ≤ trackingAmplification α σ T :=
    le_trans zero_le_one (one_le_trackingAmplification α σ T)
  calc
    (∏ u ∈ Finset.Ico (t + 1) T, (1 ⊔ α u)) ^ 2 * σ t ^ 2
        = (σ t * ∏ u ∈ Finset.Ico (t + 1) T, (1 ⊔ α u)) ^ 2 := by ring
    _ ≤ trackingAmplification α σ T ^ 2 :=
      (sq_le_sq₀ hnoise0 hK).mpr (tracking_noise_product_le ht le_rfl)

end AbsorptionCutoff
