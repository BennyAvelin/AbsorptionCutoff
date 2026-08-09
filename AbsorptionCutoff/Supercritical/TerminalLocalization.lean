/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.TerminalContraction

/-!
# Terminal localization for the supercritical cutoff

This module continues the supercritical cutoff proof after the varying
terminal contraction and centered-moment estimates established in
`TerminalContraction.lean`. Keeping the shrinking-radius localization and
subsequent terminal assembly here avoids re-elaborating that completed module
for each small unit.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The deterministic orbit center at the terminal block start is eventually
inside half of the shrinking terminal radius. -/
lemma
    eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_half_terminalRadius
    {A qStar q₀ b : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      |(V A)^[
          supercriticalTerminalBlockStart A qStar q₀ c b N] (q N) -
          qStar| ≤
        supercriticalTerminalRadius N / 2 := by
  obtain ⟨D, hD, hcenter⟩ :=
    exists_eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_mul_rpow_div_sqrt
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hscale :=
    tendsto_mul_rpow_sub_terminalBlockLength_div_sqrt_div_terminalRadius_zero
      (μ := deriv (V A) qStar) (b := b) (D := D) (c := c)
      hμ.1 hμ.2 hb hD.le
  have hsmall :
      ∀ᶠ N : ℕ in Filter.atTop,
        D *
                deriv (V A) qStar ^
                  (c - (supercriticalTerminalBlockLength b N : ℝ)) /
              Real.sqrt (N : ℝ) /
            supercriticalTerminalRadius N <
          1 / 2 :=
    hscale (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards
      [hcenter, hsmall, Filter.eventually_ge_atTop (2 : ℕ)] with
      N hcenterN hsmallN hN
  have hradius :
      0 < supercriticalTerminalRadius N :=
    supercriticalTerminalRadius_pos (show 1 < N by omega)
  have hscaleN :
      D *
              deriv (V A) qStar ^
                (c - (supercriticalTerminalBlockLength b N : ℝ)) /
            Real.sqrt (N : ℝ) <
        supercriticalTerminalRadius N / 2 := by
    have hbound := (div_lt_iff₀ hradius).1 hsmallN
    nlinarith
  exact hcenterN.trans hscaleN.le

/-- A point starting inside half of a stable interval remains there under
every iterate of a strict local contraction fixing the interval center. -/
lemma forall_abs_V_iterate_sub_fixed_le_half_radius
    {A qStar R κ x : ℝ}
    (hA : A ≠ 0) (hfix : V A qStar = qStar)
    (hR : 0 < R) (hRq : R < qStar)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hx : |x - qStar| ≤ R / 2) :
    ∀ u : ℕ, |(V A)^[u] x - qStar| ≤ R / 2 := by
  intro u
  induction u with
  | zero =>
      simpa using hx
  | succ u ih =>
      have huI :
          (V A)^[u] x ∈ Set.Icc (qStar - R) (qStar + R) := by
        rw [abs_le] at ih
        constructor <;> linarith
      have hqI :
          qStar ∈ Set.Icc (qStar - R) (qStar + R) := by
        constructor <;> linarith
      have hcontract :=
        abs_V_sub_le_mul_abs_sub_of_mem_stableInterval
          hA hRq hderiv huI hqI
      rw [hfix] at hcontract
      rw [Function.iterate_succ_apply']
      calc
        |V A ((V A)^[u] x) - qStar| ≤
            κ * |(V A)^[u] x - qStar| :=
          hcontract
        _ ≤ κ * (R / 2) :=
          mul_le_mul_of_nonneg_left ih hκ0
        _ ≤ R / 2 := by
          nlinarith

/-- For the paper's convergent initial sequences, every deterministic center
through the terminal block remains inside half of the shrinking radius. -/
lemma
    eventually_forall_abs_V_iterate_terminalBlockStart_add_sub_fixed_le_half_terminalRadius
    {A qStar q₀ b : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ u : ℕ,
      |(V A)^[
          supercriticalTerminalBlockStart A qStar q₀ c b N + u] (q N) -
          qStar| ≤
        supercriticalTerminalRadius N / 2 := by
  have hstart :=
    eventually_abs_V_iterate_terminalBlockStart_sub_fixed_le_half_terminalRadius
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  obtain ⟨L, hL, hdata⟩ :=
    exists_eventually_supercriticalTerminal_contraction_data
      hA hqStar hfix
  filter_upwards [hstart, hdata] with N hstartN hdataN
  obtain ⟨hradius, hradiusBound, hκ0, hκ1, hderiv⟩ :=
    hdataN
  have hRq :
      supercriticalTerminalRadius N < qStar := by
    have hhalf :
        supercriticalTerminalRadius N ≤ qStar / 2 :=
      hradiusBound.trans (min_le_left _ _)
    linarith [hqStar.1]
  intro u
  have hiter :=
    forall_abs_V_iterate_sub_fixed_le_half_radius
      (ne_of_gt (zero_lt_one.trans hA)) hfix
      hradius hRq hκ0 hκ1 hderiv hstartN u
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact hiter

/-- The dynamic orbit moment and deterministic center bounds give uniform
shrinking-radius localization on the restarted terminal block. -/
lemma eventually_forall_shifted_eval_not_mem_terminalInterval_le_of_cutoff
    {A qStar q₀ b R κ η δ C : ℝ}
    (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (c : ℝ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (T : ℕ → ℕ)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ t ≤ T N,
          |(V A)^[t] (q N) - qStar| ≤ R - η)
    (hblock :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalBlockStart A qStar q₀ c b N +
            supercriticalTerminalBlockLength b N ≤
          T N) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ u < supercriticalTerminalBlockLength b N,
        (markovPathMeasure
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
              (fun ω =>
                ω (supercriticalTerminalBlockStart
                  A qStar q₀ c b N)))
            (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω u ∉ Set.Icc
                (qStar - supercriticalTerminalRadius N)
                (qStar + supercriticalTerminalRadius N)} ≤
          (4 * ((1 / 4) / (1 - κ ^ 2) + 2 * C) /
              supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) := by
  have hqIcc :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1 :=
    hqmem.mono fun _ hqN => ⟨hqN.1.le, hqN.2⟩
  have hmoment :=
    eventually_forall_integral_sq_eval_blockStart_add_le_inv_nat
      (ne_of_gt (zero_lt_one.trans hA))
      hκ0 hκ1 hη0 hδ hC hRinterior hderiv hbuffer
      q T
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      (supercriticalTerminalBlockLength b)
      hqIcc hT horbit hblock
  have hcenter :=
    eventually_forall_abs_V_iterate_terminalBlockStart_add_sub_fixed_le_half_terminalRadius
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  have hcenter' :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u < supercriticalTerminalBlockLength b N,
          |(V A)^[
              supercriticalTerminalBlockStart A qStar q₀ c b N + u] (q N) -
              qStar| ≤
            supercriticalTerminalRadius N / 2 :=
    hcenter.mono fun _ hcenterN u _ => hcenterN u
  exact
    eventually_forall_shifted_eval_not_mem_terminalInterval_le_of_center
      q
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      (supercriticalTerminalBlockLength b)
      hqIcc hcenter' hmoment

/-- Invariant fixed-point moments give stationary shrinking-radius
localization uniformly over every path time. -/
lemma eventually_forall_stationary_eval_not_mem_terminalInterval_le_inv_nat
    {A qStar C : ℝ}
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ))
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ u : ℕ,
      (markovPathMeasure (ν N : Measure ℝ) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc
              (qStar - supercriticalTerminalRadius N)
              (qStar + supercriticalTerminalRadius N)} ≤
        (C / supercriticalTerminalRadius N ^ 2) / (N : ℝ) := by
  filter_upwards
      [hνinv, hνsq, hνbound,
        Filter.eventually_ge_atTop (2 : ℕ)] with
      N hνinvN hνsqN hνboundN hN
  intro u
  have hstationary :=
    markovPathMeasure_measureReal_abs_eval_sub_gt_le_div_sq_div_nat
      (ν N : Measure ℝ) hνinvN
      (supercriticalTerminalRadius_pos (show 1 < N by omega))
      hνsqN hνboundN u
  have hset :
      {ω : ℕ → ℝ |
          ω u ∉ Set.Icc
            (qStar - supercriticalTerminalRadius N)
            (qStar + supercriticalTerminalRadius N)} =
        {ω : ℕ → ℝ |
          supercriticalTerminalRadius N < |ω u - qStar|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le]
    rw [lt_abs]
    constructor
    · intro h
      rcases h with h | h
      · right
        linarith
      · left
        linarith
    · intro h
      rcases h with h | h
      · right
        linarith
      · left
        linarith
  rw [hset]
  exact hstationary

lemma eventually_integral_abs_fst_sub_snd_eval_blockStart_le_terminalContraction_pow_mul_add
    {A qStar L C₁ C₂ : ℝ}
    (hA : A ≠ 0) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (q : ℕ → ℝ) (s ℓ : ℕ → ℕ)
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hcontraction :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalRadius N < qStar ∧
        0 ≤ supercriticalTerminalContraction A qStar L N ∧
        supercriticalTerminalContraction A qStar L N < 1 ∧
        ∀ z : ℝ,
          |z - qStar| ≤ supercriticalTerminalRadius N →
          |deriv (V A) z| ≤
            supercriticalTerminalContraction A qStar L N)
    (hq :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1)
    (hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hbad₁ :
      ∀ᶠ N : ℕ in Filter.atTop, ∀ u < ℓ N,
        (markovPathMeasure
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
              (fun ω => ω (s N)))
            (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω u ∉ Set.Icc
                (qStar - supercriticalTerminalRadius N)
                (qStar + supercriticalTerminalRadius N)} ≤
          (C₁ / supercriticalTerminalRadius N ^ 2) / (N : ℝ))
    (hbad₂ :
      ∀ᶠ N : ℕ in Filter.atTop, ∀ u < ℓ N,
        (markovPathMeasure (ν N : Measure ℝ) (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω u ∉ Set.Icc
                (qStar - supercriticalTerminalRadius N)
                (qStar + supercriticalTerminalRadius N)} ≤
          (C₂ / supercriticalTerminalRadius N ^ 2) / (N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∫ ω, |(ω (ℓ N)).1 - (ω (ℓ N)).2|
          ∂(markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω => ω (s N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)) ≤
        supercriticalTerminalContraction A qStar L N ^ ℓ N *
            (∫ p, |p.1 - p.2|
              ∂((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω => ω (s N))).prod (ν N : Measure ℝ)) +
          (((C₁ + C₂) / supercriticalTerminalRadius N ^ 2) /
              (N : ℝ)) /
            (1 - supercriticalTerminalContraction A qStar L N) := by
  filter_upwards
      [hcontraction, hq, hνsupport, hbad₁, hbad₂,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hcontractionN hqN hνsupportN hbad₁N hbad₂N hN
  obtain ⟨hRq, hκ0, hκ1, hderiv⟩ := hcontractionN
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hB₁ :
      0 ≤ (C₁ / supercriticalTerminalRadius N ^ 2) / (N : ℝ) :=
    div_nonneg (div_nonneg hC₁ (sq_nonneg _)) (Nat.cast_nonneg N)
  have hB₂ :
      0 ≤ (C₂ / supercriticalTerminalRadius N ^ 2) / (N : ℝ) :=
    div_nonneg (div_nonneg hC₂ (sq_nonneg _)) (Nat.cast_nonneg N)
  have hterminal :=
    integral_abs_fst_sub_snd_eval_blockStart_prod_le_terminalContraction_pow_mul_add_of_localization
      hA hRq hκ0 hκ1 hB₁ hB₂ hderiv hNpos hqN
      (ν N : Measure ℝ) hνsupportN hbad₁N hbad₂N
  have hnormalize :
      (C₁ / supercriticalTerminalRadius N ^ 2) / (N : ℝ) +
          (C₂ / supercriticalTerminalRadius N ^ 2) / (N : ℝ) =
        ((C₁ + C₂) / supercriticalTerminalRadius N ^ 2) /
          (N : ℝ) := by
    ring
  rw [hnormalize] at hterminal
  exact hterminal

/-- The shrinking contraction and the evolving and stationary terminal
localizations assemble into the paper's varying terminal recursion. -/
lemma
    exists_eventually_integral_abs_fst_sub_snd_eval_terminalBlock_le_terminalContraction_pow_mul_add
    {A qStar q₀ b R κ η δ C C₂ : ℝ}
    (q : ℕ → ℝ)
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (c : ℝ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (T : ℕ → ℕ)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ t ≤ T N,
          |(V A)^[t] (q N) - qStar| ≤ R - η)
    (hblock :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalBlockStart A qStar q₀ c b N +
            supercriticalTerminalBlockLength b N ≤
          T N)
    (hC₂ : 0 ≤ C₂)
    (hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ))
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∫ ω,
            |(ω (supercriticalTerminalBlockLength b N)).1 -
              (ω (supercriticalTerminalBlockLength b N)).2|
            ∂(markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)) ≤
          supercriticalTerminalContraction A qStar L N ^
                supercriticalTerminalBlockLength b N *
              (∫ p, |p.1 - p.2|
                ∂((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ)) +
            (((4 * ((1 / 4) / (1 - κ ^ 2) + 2 * C) + C₂) /
                supercriticalTerminalRadius N ^ 2) /
              (N : ℝ)) /
              (1 - supercriticalTerminalContraction A qStar L N) := by
  obtain ⟨L, hL, hcontractionData⟩ :=
    exists_eventually_supercriticalTerminal_contraction_data
      hA hqStar hfix
  refine ⟨L, hL, ?_⟩
  have hcontraction :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalRadius N < qStar ∧
        0 ≤ supercriticalTerminalContraction A qStar L N ∧
        supercriticalTerminalContraction A qStar L N < 1 ∧
        ∀ z : ℝ,
          |z - qStar| ≤ supercriticalTerminalRadius N →
          |deriv (V A) z| ≤
            supercriticalTerminalContraction A qStar L N :=
    hcontractionData.mono fun N hN => by
      obtain ⟨_, hRbound, ha0, ha1, hderivN⟩ := hN
      have hRhalf :
          supercriticalTerminalRadius N ≤ qStar / 2 :=
        hRbound.trans (min_le_left _ _)
      exact ⟨by linarith [hqStar.1], ha0, ha1, hderivN⟩
  have hqIcc :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1 :=
    hqmem.mono fun _ hqN => ⟨hqN.1.le, hqN.2⟩
  have hbad₁ :=
    eventually_forall_shifted_eval_not_mem_terminalInterval_le_of_cutoff
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hκ0 hκ1 hη0 hδ hC hRinterior hderiv hbuffer
      T hT horbit hblock
  have hbad₂all :=
    eventually_forall_stationary_eval_not_mem_terminalInterval_le_inv_nat
      ν hνinv hνsq hνbound
  have hbad₂ :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u < supercriticalTerminalBlockLength b N,
          (markovPathMeasure (ν N : Measure ℝ) (Kchain A N)).real
              {ω : ℕ → ℝ |
                ω u ∉ Set.Icc
                  (qStar - supercriticalTerminalRadius N)
                  (qStar + supercriticalTerminalRadius N)} ≤
            (C₂ / supercriticalTerminalRadius N ^ 2) / (N : ℝ) :=
    hbad₂all.mono fun _ hN u _ => hN u
  have hdenpos : 0 < 1 - κ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hκ1)
      (show 0 < 1 + κ by linarith)]
  have hCdyn :
      0 ≤ 4 * ((1 / 4) / (1 - κ ^ 2) + 2 * C) := by
    positivity
  exact
    eventually_integral_abs_fst_sub_snd_eval_blockStart_le_terminalContraction_pow_mul_add
      (ne_of_gt (zero_lt_one.trans hA)) hCdyn hC₂ q
      (supercriticalTerminalBlockStart A qStar q₀ c b)
      (supercriticalTerminalBlockLength b) ν
      hcontraction hqIcc hνsupport hbad₁ hbad₂

/-- The varying terminal recursion inherits the inverse-square-root
block-start product-distance estimate. -/
lemma
    exists_eventually_terminalBlock_distance_le_terminalContraction_pow_mul_inv_sqrt_add
    {A qStar q₀ b R κ η δ C C₀ C₂ : ℝ}
    (q : ℕ → ℝ)
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (c : ℝ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (T : ℕ → ℕ)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ t ≤ T N,
          |(V A)^[t] (q N) - qStar| ≤ R - η)
    (hblock :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalBlockStart A qStar q₀ c b N +
            supercriticalTerminalBlockLength b N ≤
          T N)
    (hC₂ : 0 ≤ C₂)
    (hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ))
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ))
    (hcenters :
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[
            supercriticalTerminalBlockStart A qStar q₀ c b N] (q N) -
            qStar| ≤
          C₀ / Real.sqrt (N : ℝ)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∫ ω,
            |(ω (supercriticalTerminalBlockLength b N)).1 -
              (ω (supercriticalTerminalBlockLength b N)).2|
            ∂(markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)) ≤
          supercriticalTerminalContraction A qStar L N ^
                supercriticalTerminalBlockLength b N *
              ((Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
                  C₀ + Real.sqrt C₂) /
                Real.sqrt (N : ℝ)) +
            (((4 * ((1 / 4) / (1 - κ ^ 2) + 2 * C) + C₂) /
                supercriticalTerminalRadius N ^ 2) /
              (N : ℝ)) /
              (1 - supercriticalTerminalContraction A qStar L N) := by
  obtain ⟨L, hL, hterminal⟩ :=
    exists_eventually_integral_abs_fst_sub_snd_eval_terminalBlock_le_terminalContraction_pow_mul_add
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hκ0 hκ1 hη0 hδ hC hRinterior hderiv hbuffer
      T hT horbit hblock hC₂ hνsupport hνinv hνsq hνbound
  refine ⟨L, hL, ?_⟩
  have hqIcc :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1 :=
    hqmem.mono fun _ hqN => ⟨hqN.1.le, hqN.2⟩
  have hstart :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalBlockStart A qStar q₀ c b N ≤ T N :=
    hblock.mono fun _ hN => (Nat.le_add_right _ _).trans hN
  have hproduct :=
    eventually_integral_abs_fst_sub_snd_blockStart_prod_le_inv_sqrt_nat
      (ne_of_gt (zero_lt_one.trans hA))
      hκ0 hκ1 hη0 hδ hC hC₂ hRinterior hderiv hbuffer
      q (supercriticalTerminalBlockStart A qStar q₀ c b) T
      hqIcc hstart hT horbit ν hνsq hνbound hcenters
  filter_upwards [hterminal, hproduct] with N hterminalN hproductN
  calc
    ∫ ω,
          |(ω (supercriticalTerminalBlockLength b N)).1 -
            (ω (supercriticalTerminalBlockLength b N)).2|
          ∂(markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)) ≤
        supercriticalTerminalContraction A qStar L N ^
              supercriticalTerminalBlockLength b N *
            (∫ p, |p.1 - p.2|
              ∂((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ)) +
          (((4 * ((1 / 4) / (1 - κ ^ 2) + 2 * C) + C₂) /
              supercriticalTerminalRadius N ^ 2) /
            (N : ℝ)) /
            (1 - supercriticalTerminalContraction A qStar L N) :=
      hterminalN
    _ ≤
        supercriticalTerminalContraction A qStar L N ^
              supercriticalTerminalBlockLength b N *
            ((Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
                C₀ + Real.sqrt C₂) /
              Real.sqrt (N : ℝ)) +
          (((4 * ((1 / 4) / (1 - κ ^ 2) + 2 * C) + C₂) /
              supercriticalTerminalRadius N ^ 2) /
            (N : ℝ)) /
            (1 - supercriticalTerminalContraction A qStar L N) := by
      gcongr
      exact pow_nonneg
        (supercriticalTerminalContraction_nonneg
          hA hqStar hfix hL N) _

/-- Up to an arbitrary fixed factor above one, the terminal contraction power
can be replaced by the corresponding fixed-point multiplier power. -/
lemma
    exists_eventually_terminalBlock_distance_le_multiplier_pow_mul_inv_sqrt_add
    {A qStar q₀ b R κ η δ C C₀ C₂ : ℝ}
    (q : ℕ → ℝ)
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (c : ℝ)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (T : ℕ → ℕ)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ t ≤ T N,
          |(V A)^[t] (q N) - qStar| ≤ R - η)
    (hblock :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalBlockStart A qStar q₀ c b N +
            supercriticalTerminalBlockLength b N ≤
          T N)
    (hC₀ : 0 ≤ C₀) (hC₂ : 0 ≤ C₂)
    (hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ))
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ))
    (hcenters :
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[
            supercriticalTerminalBlockStart A qStar q₀ c b N] (q N) -
            qStar| ≤
          C₀ / Real.sqrt (N : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∫ ω,
            |(ω (supercriticalTerminalBlockLength b N)).1 -
              (ω (supercriticalTerminalBlockLength b N)).2|
            ∂(markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)) ≤
          (1 + ε) *
              deriv (V A) qStar ^
                supercriticalTerminalBlockLength b N *
              ((Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
                  C₀ + Real.sqrt C₂) /
                Real.sqrt (N : ℝ)) +
            (((4 * ((1 / 4) / (1 - κ ^ 2) + 2 * C) + C₂) /
                supercriticalTerminalRadius N ^ 2) /
              (N : ℝ)) /
              (1 - supercriticalTerminalContraction A qStar L N) := by
  obtain ⟨L, hL, hterminal⟩ :=
    exists_eventually_terminalBlock_distance_le_terminalContraction_pow_mul_inv_sqrt_add
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hκ0 hκ1 hη0 hδ hC hRinterior hderiv hbuffer
      T hT horbit hblock hC₂ hνsupport hνinv hνsq hνbound hcenters
  refine ⟨L, hL, ?_⟩
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hratio :=
    tendsto_supercriticalTerminalContraction_div_multiplier_pow_blockLength_one
      hA hqStar hfix hL hb
  have hratioUpper :
      ∀ᶠ N : ℕ in Filter.atTop,
        (supercriticalTerminalContraction A qStar L N /
            deriv (V A) qStar) ^
            supercriticalTerminalBlockLength b N <
          1 + ε :=
    hratio (eventually_lt_nhds (by linarith))
  filter_upwards [hterminal, hratioUpper] with
      N hterminalN hratioN
  have hpow :
      supercriticalTerminalContraction A qStar L N ^
          supercriticalTerminalBlockLength b N =
        (supercriticalTerminalContraction A qStar L N /
            deriv (V A) qStar) ^
              supercriticalTerminalBlockLength b N *
          deriv (V A) qStar ^
            supercriticalTerminalBlockLength b N := by
    rw [div_pow]
    field_simp [hμ.1.ne']
  have hpowBound :
      supercriticalTerminalContraction A qStar L N ^
          supercriticalTerminalBlockLength b N ≤
        (1 + ε) *
          deriv (V A) qStar ^
            supercriticalTerminalBlockLength b N := by
    rw [hpow]
    exact mul_le_mul_of_nonneg_right hratioN.le
      (pow_nonneg hμ.1.le _)
  have hBnonneg :
      0 ≤
        (Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
            C₀ + Real.sqrt C₂) /
          Real.sqrt (N : ℝ) :=
    div_nonneg
      (add_nonneg
        (add_nonneg (Real.sqrt_nonneg _) hC₀)
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hscaled :=
    mul_le_mul_of_nonneg_right hpowBound hBnonneg
  linarith

end AbsorptionCutoff
