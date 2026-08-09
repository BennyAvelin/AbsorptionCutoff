/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.TerminalEntrance

/-!
# Terminal entrance assembly for the supercritical cutoff

This module continues the supercritical cutoff proof after the arbitrary-law
killed-moment and stable-exit estimates established in
`TerminalEntrance.lean`. The remaining finite-entrance concentration and
paper-facing cutoff assembly belong here.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The paper's stopped argument after a random entrance: the full dynamic
second moment consists of damped entrance variance, the local noise floor,
initial entrance failure, and finite-horizon transition noise. -/
lemma integral_sq_eval_sub_V_iterate_le_initial_add_inv_add_exp_of_measure
    {A q qStar R κ δ : ℝ} {N T t : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hR0 : 0 ≤ R)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hδ : 0 < δ)
    (hRinterior : R < min qStar (1 - qStar))
    (hfix : V A qStar = qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * R ≤ R)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (horbit :
      ∀ s ≤ T, (V A)^[s] q ∈ Set.Icc (qStar - R) (qStar + R))
    (htT : t ≤ T) :
    ∫ ω, (ω t - (V A)^[t] q) ^ 2
        ∂(markovPathMeasure μ₀ (Kchain A N)) ≤
      (κ ^ 2) ^ t * ∫ x, (x - q) ^ 2 ∂μ₀ +
        (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
        μ₀.real {x : ℝ | R < |x - qStar|} +
        2 * T * Real.exp (-2 * N * δ ^ 2) := by
  have hRq : R < qStar :=
    hRinterior.trans_le (min_le_left _ _)
  have hRone : R < 1 - qStar :=
    hRinterior.trans_le (min_le_right _ _)
  have horbit01 :
      (V A)^[t] q ∈ Set.Icc (0 : ℝ) 1 := by
    have ht := horbit t htT
    exact
      ⟨by linarith [ht.1, hRq],
        by linarith [ht.2, hRone]⟩
  calc
    ∫ ω, (ω t - (V A)^[t] q) ^ 2
        ∂(markovPathMeasure μ₀ (Kchain A N)) ≤
        stableIntervalKilledErrorMomentOfMeasure
            A N μ₀ q qStar R T t +
          (markovPathMeasure μ₀ (Kchain A N)).real
            {ω : ℕ → ℝ |
              stableIntervalExitTime qStar R T ω ≤ T} :=
      integral_sq_eval_sub_V_iterate_le_killed_add_exit_of_measure
        hN μ₀ hμ₀ htT horbit01
    _ ≤
        ((κ ^ 2) ^ t * ∫ x, (x - q) ^ 2 ∂μ₀ +
          (1 / (4 * (N : ℝ))) / (1 - κ ^ 2)) +
          (markovPathMeasure μ₀ (Kchain A N)).real
            {ω : ℕ → ℝ |
              stableIntervalExitTime qStar R T ω ≤ T} :=
      add_le_add
        (stableIntervalKilledErrorMomentOfMeasure_le
          hA hN hκ0 hκ1 hRq μ₀ hμ₀ hderiv htT
          (fun s hs => horbit s (hs.trans htT)))
        le_rfl
    _ ≤
        ((κ ^ 2) ^ t * ∫ x, (x - q) ^ 2 ∂μ₀ +
          (1 / (4 * (N : ℝ))) / (1 - κ ^ 2)) +
          (μ₀.real {x : ℝ | R < |x - qStar|} +
            2 * T * Real.exp (-2 * N * δ ^ 2)) :=
      add_le_add le_rfl
        (markovPathMeasure_measureReal_stableIntervalExitTime_le_of_measure
          hA hN hR0 hκ0 hδ hRq hfix hderiv hbuffer μ₀)
    _ =
        (κ ^ 2) ^ t * ∫ x, (x - q) ^ 2 ∂μ₀ +
          (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
          μ₀.real {x : ℝ | R < |x - qStar|} +
          2 * T * Real.exp (-2 * N * δ ^ 2) := by
      ring

/-- Applying the random-entrance estimate to a fixed-time marginal rewrites
all four terms on the original Dirac-start path. -/
lemma integral_sq_eval_add_sub_V_iterate_le_initial_add_inv_add_exp
    {A q qStar R κ δ : ℝ} {N m T t : ℕ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hA : A ≠ 0) (hN : 0 < N) (hR0 : 0 ≤ R)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hδ : 0 < δ)
    (hRinterior : R < min qStar (1 - qStar))
    (hfix : V A qStar = qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * R ≤ R)
    (horbit :
      ∀ s ≤ T,
        (V A)^[s] ((V A)^[m] q) ∈
          Set.Icc (qStar - R) (qStar + R))
    (htT : t ≤ T) :
    ∫ ω, (ω (m + t) - (V A)^[m + t] q) ^ 2
        ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) ≤
      (κ ^ 2) ^ t *
          ∫ ω, (ω m - (V A)^[m] q) ^ 2
            ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) +
        (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
        (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
          {ω : ℕ → ℝ | R < |ω m - qStar|} +
        2 * T * Real.exp (-2 * N * δ ^ 2) := by
  let μ := markovPathMeasure (Measure.dirac q) (Kchain A N)
  let μm := μ.map (fun ω => ω m)
  haveI : IsProbabilityMeasure μm := by
    dsimp only [μm]
    exact
      Measure.isProbabilityMeasure_map
        (measurable_pi_apply m).aemeasurable
  have hμm :
      μm ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    simpa only [μ, μm] using
      markovPathMeasure_dirac_map_eval_apply_compl_Icc_eq_zero
        hq hN m
  have hfull :=
    integral_sq_eval_sub_V_iterate_le_initial_add_inv_add_exp_of_measure
      hA hN hR0 hκ0 hκ1 hδ hRinterior hfix hderiv hbuffer
      μm hμm horbit htT
  have hcenter :
      (V A)^[t] ((V A)^[m] q) = (V A)^[m + t] q := by
    rw [Nat.add_comm, Function.iterate_add_apply]
  have hinit :
      (∫ x, (x - (V A)^[m] q) ^ 2 ∂μm) =
        ∫ ω, (ω m - (V A)^[m] q) ^ 2 ∂μ := by
    dsimp only [μm]
    rw [integral_map
      (μ := μ)
      (φ := fun ω : ℕ → ℝ => ω m)
      (f := fun x : ℝ => (x - (V A)^[m] q) ^ 2)
      (measurable_pi_apply m).aemeasurable
      (((measurable_id.sub measurable_const).pow_const 2)
        |>.aestronglyMeasurable)]
  have hbad :
      μm.real {x : ℝ | R < |x - qStar|} =
        μ.real {ω : ℕ → ℝ | R < |ω m - qStar|} := by
    have hmeas :
        MeasurableSet {x : ℝ | R < |x - qStar|} :=
      measurableSet_lt measurable_const
        ((measurable_id.sub measurable_const).abs)
    dsimp only [μm]
    change
      (μ.map (fun ω : ℕ → ℝ => ω m)).real
          {x : ℝ | R < |x - qStar|} =
        μ.real ((fun ω : ℕ → ℝ => ω m) ⁻¹'
          {x : ℝ | R < |x - qStar|})
    exact
      map_measureReal_apply
        (μ := μ) (measurable_pi_apply m) hmeas
  have hshift :
      (markovPathMeasure μm (Kchain A N)).map
          (fun ω => ω t) =
        μ.map (fun ω => ω (m + t)) := by
    simpa only [μ, μm] using
      markovPathMeasure_map_eval_of_map_eval
        (Measure.dirac q) (Kchain A N) m t
  let f : ℝ → ℝ :=
    fun x => (x - (V A)^[t] ((V A)^[m] q)) ^ 2
  have hf : StronglyMeasurable f := by
    dsimp only [f]
    exact
      ((measurable_id.sub measurable_const).pow_const 2)
        |>.stronglyMeasurable
  have hlhs :
      (∫ ω, f (ω t)
          ∂(markovPathMeasure μm (Kchain A N))) =
        ∫ ω, f (ω (m + t)) ∂μ := by
    calc
      ∫ ω, f (ω t)
          ∂(markovPathMeasure μm (Kchain A N)) =
          ∫ x, f x
            ∂((markovPathMeasure μm (Kchain A N)).map
              (fun ω => ω t)) :=
        (integral_map
          (μ := markovPathMeasure μm (Kchain A N))
          (φ := fun ω : ℕ → ℝ => ω t)
          (f := f)
          (measurable_pi_apply t).aemeasurable
          hf.aestronglyMeasurable).symm
      _ = ∫ x, f x ∂(μ.map (fun ω => ω (m + t))) := by
        rw [hshift]
      _ = ∫ ω, f (ω (m + t)) ∂μ :=
        integral_map
          (μ := μ)
          (φ := fun ω : ℕ → ℝ => ω (m + t))
          (f := f)
          (measurable_pi_apply (m + t)).aemeasurable
          hf.aestronglyMeasurable
  rw [hinit, hbad] at hfull
  calc
    ∫ ω, (ω (m + t) - (V A)^[m + t] q) ^ 2 ∂μ =
        ∫ ω, (ω t - (V A)^[t] ((V A)^[m] q)) ^ 2
          ∂(markovPathMeasure μm (Kchain A N)) := by
      rw [← hcenter]
      simpa only [f] using hlhs.symm
    _ ≤
        (κ ^ 2) ^ t *
            ∫ ω, (ω m - (V A)^[m] q) ^ 2 ∂μ +
          (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
          μ.real {ω : ℕ → ℝ | R < |ω m - qStar|} +
          2 * T * Real.exp (-2 * N * δ ^ 2) :=
      hfull

/-- The deterministic stable margin and stochastic fixed-time entrance tail
can be selected with the same compact-uniform parameters. -/
theorem exists_uniform_markovPathMeasure_stable_entrance_exp_bound_with_margin
    {A qStar r : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hr : r ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ κ R η : ℝ, ∃ m : ℕ, ∃ C c : ℝ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C ∧ 0 < c ∧
      (∀ x : ℝ,
        |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      (∀ q ∈ Set.Icc r 1,
        |(V A)^[m] q - qStar| ≤ R - η) ∧
      ∀ N : ℕ, 0 < N → ∀ q ∈ Set.Icc r 1,
        (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
            {ω : ℕ → ℝ | R < |ω m - qStar|} ≤
          C * Real.exp (-(c * (N : ℝ))) := by
  obtain ⟨κ, R, η, m, hκ0, hκ1, hη0, hηR, hRinterior,
      hderiv, _hcontract, hentry⟩ :=
    exists_uniform_V_iterate_stable_margin hA hqStar hfix hr
  obtain ⟨δ, hδ, htrack⟩ :=
    exists_pos_markovPathMeasure_measureReal_abs_sub_iterate_V_ge_le
      A m hη0
  let C : ℝ := 2 * ((m : ℝ) + 1)
  let c : ℝ := 2 * δ ^ 2
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine
    ⟨κ, R, η, m, C, c, hκ0, hκ1, hη0, hηR,
      hRinterior, hC, hc, hderiv, hentry, ?_⟩
  intro N hN q hq
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hr.1.le.trans hq.1, hq.2⟩
  have hsubset :
      {ω : ℕ → ℝ | R < |ω m - qStar|} ⊆
        {ω : ℕ → ℝ | η ≤ |ω m - (V A)^[m] q|} := by
    intro ω hfail
    change R < |ω m - qStar| at hfail
    change η ≤ |ω m - (V A)^[m] q|
    have htriangle :
        |ω m - qStar| ≤
          |ω m - (V A)^[m] q| +
            |(V A)^[m] q - qStar| := by
      calc
        |ω m - qStar| =
            |(ω m - (V A)^[m] q) +
              ((V A)^[m] q - qStar)| := by
          congr 1
          ring
        _ ≤ _ := abs_add_le _ _
    linarith [hentry q hq]
  calc
    (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
          {ω : ℕ → ℝ | R < |ω m - qStar|} ≤
        (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
          {ω : ℕ → ℝ | η ≤ |ω m - (V A)^[m] q|} :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ 2 * m * Real.exp (-2 * N * δ ^ 2) :=
      htrack N hN q hqIcc
    _ ≤ C * Real.exp (-(c * (N : ℝ))) := by
      dsimp only [C, c]
      rw [show -(2 * δ ^ 2 * (N : ℝ)) =
          -2 * (N : ℝ) * δ ^ 2 by ring]
      gcongr
      norm_num

/-- The synchronized deterministic margin and stochastic entrance tail apply
eventually to every sequence converging to a positive initial radius. -/
theorem
    exists_eventually_markovPathMeasure_stable_entrance_exp_bound_with_margin_of_tendsto
    {A qStar q₀ : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ κ R η : ℝ, ∃ m : ℕ, ∃ C c : ℝ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C ∧ 0 < c ∧
      (∀ x : ℝ,
        |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[m] (q N) - qStar| ≤ R - η ∧
        (markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).real
            {ω : ℕ → ℝ | R < |ω m - qStar|} ≤
          C * Real.exp (-(c * (N : ℝ))) := by
  let r : ℝ := q₀ / 2
  have hr : r ∈ Set.Ioc (0 : ℝ) 1 := by
    dsimp only [r]
    constructor <;> linarith [hq₀.1, hq₀.2]
  obtain ⟨κ, R, η, m, C, c, hκ0, hκ1, hη0, hηR,
      hRinterior, hC, hc, hderiv, hmargin, hentrance⟩ :=
    exists_uniform_markovPathMeasure_stable_entrance_exp_bound_with_margin
      hA hqStar hfix hr
  refine
    ⟨κ, R, η, m, C, c, hκ0, hκ1, hη0, hηR,
      hRinterior, hC, hc, hderiv, ?_⟩
  have hqLower :
      ∀ᶠ N : ℕ in Filter.atTop, r < q N :=
    hq (eventually_gt_nhds (by
      dsimp only [r]
      linarith [hq₀.1]))
  filter_upwards
      [hqLower, hqmem, Filter.eventually_ge_atTop (1 : ℕ)] with
      N hqLowerN hqN hN
  have hqIcc : q N ∈ Set.Icc r 1 :=
    ⟨hqLowerN.le, hqN.2⟩
  exact
    ⟨hmargin (q N) hqIcc,
      hentrance N (Nat.zero_lt_of_lt hN) (q N) hqIcc⟩

/-- After a fixed stochastic entrance, every positive convergent initial
sequence has a uniform inverse-dimension dynamic moment bound through any
linearly bounded varying horizon. -/
theorem
    exists_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_of_tendsto
    {A qStar q₀ Cₜ : ℝ} (q : ℕ → ℝ) (T : ℕ → ℕ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Ioc (0 : ℝ) 1)
    (hCₜ : 0 ≤ Cₜ)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ Cₜ * (N : ℝ)) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in Filter.atTop, ∀ t : ℕ,
        m ≤ t → t ≤ T N →
        ∫ ω, (ω t - (V A)^[t] (q N)) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)) ≤
          C / (N : ℝ) := by
  have hA0 : A ≠ 0 :=
    ne_of_gt (zero_lt_one.trans hA)
  obtain ⟨κ, R, η, m, Cₑ, cₑ, hκ0, hκ1, hη0, hηR,
      hRinterior, hCₑ, hcₑ, hderiv, hentry⟩ :=
    exists_eventually_markovPathMeasure_stable_entrance_exp_bound_with_margin_of_tendsto
      q hA hqStar hfix hq₀ hq hqmem
  obtain ⟨C₀, hC₀, hinitial⟩ :=
    exists_nonneg_integral_sq_eval_sub_V_iterate_le_div_nat
      hA0 m
  let δ : ℝ := (1 - κ) * R / 2
  have hR : 0 < R :=
    hη0.trans hηR
  have hR0 : 0 ≤ R :=
    hR.le
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hbuffer : δ + κ * R ≤ R := by
    dsimp only [δ]
    nlinarith
  have hκsq : κ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hκ0 zero_le_one).2 hκ1
  have hden : 0 < 1 - κ ^ 2 :=
    sub_pos.mpr hκsq
  have hentryDecay :=
    eventually_nat_mul_exp_neg_le_inv_nat hcₑ
  have hhorizonDecay :=
    eventually_two_nat_horizon_mul_exp_neg_le_mul_inv_nat
      (T := T) (C := Cₜ) (c := 2 * δ ^ 2)
      hCₜ
      (mul_pos (by norm_num) (sq_pos_of_pos hδ))
      hT
  let C : ℝ :=
    C₀ + (1 / 4) / (1 - κ ^ 2) + Cₑ + 2 * Cₜ
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨m, C, hC, ?_⟩
  filter_upwards
      [hentry, hqmem, hentryDecay, hhorizonDecay,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hentryN hqN hentryDecayN hhorizonDecayN hN
  intro t hmt htT
  have hNpos : 0 < N :=
    Nat.zero_lt_of_lt hN
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hNpos
  have hqIcc : q N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hqN.1.le, hqN.2⟩
  have hRq : R < qStar :=
    hRinterior.trans_le (min_le_left _ _)
  have horbitAbs :
      ∀ s : ℕ,
        |(V A)^[s] ((V A)^[m] (q N)) - qStar| ≤ R := by
    intro s
    induction s with
    | zero =>
        simpa only [Function.iterate_zero_apply] using
          hentryN.1.trans (sub_le_self R hη0.le)
    | succ s ih =>
        have hsIcc :
            (V A)^[s] ((V A)^[m] (q N)) ∈
              Set.Icc (qStar - R) (qStar + R) := by
          rw [abs_le] at ih
          constructor <;> linarith
        have hqStarIcc :
            qStar ∈ Set.Icc (qStar - R) (qStar + R) := by
          constructor <;> linarith
        have hcontract :=
          abs_V_sub_le_mul_abs_sub_of_mem_stableInterval
            hA0 hRq hderiv hsIcc hqStarIcc
        rw [hfix] at hcontract
        rw [Function.iterate_succ_apply']
        calc
          |V A ((V A)^[s] ((V A)^[m] (q N))) - qStar| ≤
              κ * |(V A)^[s] ((V A)^[m] (q N)) - qStar| :=
            hcontract
          _ ≤ κ * R :=
            mul_le_mul_of_nonneg_left ih hκ0
          _ ≤ 1 * R :=
            mul_le_mul_of_nonneg_right hκ1.le hR0
          _ = R := one_mul R
  have horbit :
      ∀ s ≤ T N,
        (V A)^[s] ((V A)^[m] (q N)) ∈
          Set.Icc (qStar - R) (qStar + R) := by
    intro s _hs
    have hs := horbitAbs s
    rw [abs_le] at hs
    constructor <;> linarith
  have hlocalTime : t - m ≤ T N :=
    (Nat.sub_le t m).trans htT
  have hfull :=
    integral_sq_eval_add_sub_V_iterate_le_initial_add_inv_add_exp
      hqIcc hA0 hNpos hR0 hκ0 hκ1 hδ hRinterior hfix
      hderiv hbuffer horbit hlocalTime
  have hdamped :
      (κ ^ 2) ^ (t - m) *
          ∫ ω, (ω m - (V A)^[m] (q N)) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)) ≤
        C₀ / (N : ℝ) := by
    calc
      (κ ^ 2) ^ (t - m) *
            ∫ ω, (ω m - (V A)^[m] (q N)) ^ 2
              ∂(markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)) ≤
          (κ ^ 2) ^ (t - m) * (C₀ / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (hinitial hqIcc hNpos)
          (pow_nonneg (sq_nonneg κ) _)
      _ ≤ 1 * (C₀ / (N : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (pow_le_one₀ (sq_nonneg κ) hκsq.le)
          (div_nonneg hC₀ hNreal.le)
      _ = C₀ / (N : ℝ) := one_mul _
  have hentryDecayN' :
      (N : ℝ) * Real.exp (-(cₑ * (N : ℝ))) ≤
        1 / (N : ℝ) := by
    rw [show -(cₑ * (N : ℝ)) =
        -cₑ * (N : ℝ) by ring]
    exact hentryDecayN
  have hentrance :
      (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).real
          {ω : ℕ → ℝ | R < |ω m - qStar|} ≤
        Cₑ / (N : ℝ) := by
    calc
      (markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).real
            {ω : ℕ → ℝ | R < |ω m - qStar|} ≤
          Cₑ * Real.exp (-(cₑ * (N : ℝ))) :=
        hentryN.2
      _ ≤ Cₑ *
          ((N : ℝ) * Real.exp (-(cₑ * (N : ℝ)))) := by
        gcongr
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ N by exact_mod_cast hN)
            (Real.exp_nonneg _))
      _ ≤ Cₑ * (1 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hentryDecayN' hCₑ.le
      _ = Cₑ / (N : ℝ) := by ring
  have hhorizon :
      2 * (T N : ℝ) * Real.exp (-2 * N * δ ^ 2) ≤
        2 * Cₜ / (N : ℝ) := by
    rw [show -2 * (N : ℝ) * δ ^ 2 =
        -(2 * δ ^ 2) * (N : ℝ) by ring]
    exact hhorizonDecayN
  have htDecomp : m + (t - m) = t := by
    omega
  calc
    ∫ ω, (ω t - (V A)^[t] (q N)) ^ 2
        ∂(markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)) ≤
        (κ ^ 2) ^ (t - m) *
            ∫ ω, (ω m - (V A)^[m] (q N)) ^ 2
              ∂(markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)) +
          (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
          (markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).real
            {ω : ℕ → ℝ | R < |ω m - qStar|} +
          2 * (T N : ℝ) * Real.exp (-2 * N * δ ^ 2) := by
      simpa only [htDecomp] using hfull
    _ ≤ C₀ / (N : ℝ) +
          (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
          Cₑ / (N : ℝ) +
          2 * Cₜ / (N : ℝ) :=
      add_le_add (add_le_add (add_le_add hdamped le_rfl) hentrance)
        hhorizon
    _ = C / (N : ℝ) := by
      dsimp only [C]
      field_simp [hNreal.ne', hden.ne']

end AbsorptionCutoff
