/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.TerminalLocalization

/-!
# Terminal entrance for the supercritical cutoff

This module continues the supercritical cutoff proof after the shrinking
terminal localization and contraction assembly established in
`TerminalLocalization.lean`. The remaining finite stochastic entrance and
paper-facing cutoff assembly belong here.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- On the full squared-radius state interval, the Gaussian mean map has the
paper's finite global Lipschitz constant `A²`. -/
lemma abs_V_sub_le_sq_mul_abs_sub_of_mem_Icc
    {A x y : ℝ} (hA : A ≠ 0)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |V A x - V A y| ≤ A ^ 2 * |x - y| := by
  have hderivBound :
      ∀ z : ℝ, 0 < z → |deriv (V A) z| ≤ A ^ 2 := by
    intro z hz
    rw [(hasDerivAt_V hA hz).deriv]
    change ‖∫ g, dV A z g ∂(gaussianReal 0 1)‖ ≤ A ^ 2
    calc
      ‖∫ g, dV A z g ∂(gaussianReal 0 1)‖ ≤
          ∫ g, A ^ 2 * g ^ 2 ∂(gaussianReal 0 1) :=
        norm_integral_le_of_norm_le
          (integrable_sq_gaussian.const_mul (A ^ 2))
          (Filter.Eventually.of_forall fun g => by
            rw [Real.norm_eq_abs, abs_of_nonneg (dV_nonneg A z g)]
            calc
              dV A z g ≤ (A * g) ^ 2 := dV_le A z g
              _ = A ^ 2 * g ^ 2 := by ring)
      _ = A ^ 2 := by
        rw [integral_const_mul, integral_sq_gaussian, mul_one]
  have hordered :
      ∀ {a b : ℝ},
        a ∈ Set.Icc (0 : ℝ) 1 →
        b ∈ Set.Icc (0 : ℝ) 1 →
        a < b →
        |V A a - V A b| ≤ A ^ 2 * |a - b| := by
    intro a b ha hb hab
    have hdiff :
        DifferentiableOn ℝ (V A) (Set.Ioo a b) := by
      intro z hz
      exact
        (hasDerivAt_V hA (ha.1.trans_lt hz.1)).differentiableAt
          |>.differentiableWithinAt
    obtain ⟨z, hz, hzderiv⟩ :=
      exists_deriv_eq_slope (f := V A) hab
        (V_continuous A).continuousOn hdiff
    have hba : 0 < b - a := sub_pos.mpr hab
    have heq :
        V A b - V A a = deriv (V A) z * (b - a) := by
      rw [hzderiv]
      field_simp [hba.ne']
    calc
      |V A a - V A b| = |V A b - V A a| := abs_sub_comm _ _
      _ = |deriv (V A) z| * |b - a| := by rw [heq, abs_mul]
      _ ≤ A ^ 2 * |b - a| :=
        mul_le_mul_of_nonneg_right
          (hderivBound z (ha.1.trans_lt hz.1)) (abs_nonneg _)
      _ = A ^ 2 * |a - b| := by rw [abs_sub_comm b a]
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact hordered hx hy hxy
  · subst y
    simp
  · simpa only [abs_sub_comm] using hordered hy hx hyx

/-- Before deterministic entrance, global Lipschitz control gives one
finite-prefix second-moment recursion step. -/
lemma integral_sq_eval_succ_sub_V_iterate_le_global
    {A q : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hN : 0 < N) (t : ℕ) :
    ∫ ω, (ω (t + 1) - (V A)^[t + 1] q) ^ 2
        ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) ≤
      (A ^ 2) ^ 2 *
          ∫ ω, (ω t - (V A)^[t] q) ^ 2
            ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) +
        1 / (4 * (N : ℝ)) := by
  have hiterate :
      ∀ s : ℕ, (V A)^[s] q ∈ Set.Icc (0 : ℝ) 1 := by
    intro s
    induction s with
    | zero =>
        simpa only [Function.iterate_zero_apply] using hq
    | succ s _ =>
        rw [Function.iterate_succ_apply']
        exact ⟨V_nonneg _ _, (V_lt_one _ _).le⟩
  have hpath :
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
        ω t ∈ Set.Icc (0 : ℝ) 1 :=
    markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc hq hN t
  have hcontract :
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
        |V A (ω t) - V A ((V A)^[t] q)| ≤
          A ^ 2 * |ω t - (V A)^[t] q| :=
    hpath.mono fun ω hω =>
      abs_V_sub_le_sq_mul_abs_sub_of_mem_Icc
        hA hω (hiterate t)
  simpa only [Function.iterate_succ_apply'] using
    (integral_sq_eval_succ_sub_V_le_of_abs_V_sub_le
      (A := A) (r := (V A)^[t] q)
      hq hN (sq_nonneg A) t hcontract)

/-- At every fixed time, the global finite-prefix recursion gives a
dimension-free constant multiplying `N⁻¹`, uniformly over starts in
`[0,1]`. -/
theorem exists_nonneg_integral_sq_eval_sub_V_iterate_le_div_nat
    {A : ℝ} (hA : A ≠ 0) (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {q : ℝ}, q ∈ Set.Icc (0 : ℝ) 1 →
        ∀ {N : ℕ}, 0 < N →
          (∫ ω, (ω t - (V A)^[t] q) ^ 2
              ∂(markovPathMeasure (Measure.dirac q) (Kchain A N))) ≤
            C / (N : ℝ) := by
  induction t with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro q hq N hN
      let μ := markovPathMeasure (Measure.dirac q) (Kchain A N)
      have hω0 :
          ∀ᵐ ω ∂μ, ω 0 = q := by
        change
          ∀ᵐ ω
              ∂(markovPathMeasure
                (Measure.dirac q) (Kchain A N)),
            ω 0 = q
        rw [ae_iff]
        have hset :
            {ω : ℕ → ℝ | ω 0 ≠ q} =
              (fun ω : ℕ → ℝ => ω 0) ⁻¹' ({q} : Set ℝ)ᶜ := by
          ext ω
          simp
        rw [show {ω : ℕ → ℝ | ¬ω 0 = q} =
              {ω : ℕ → ℝ | ω 0 ≠ q} by rfl,
          hset, ← Measure.map_apply (measurable_pi_apply 0)
            (measurableSet_singleton q).compl,
          markovPathMeasure_map_zero]
        simp
      rw [zero_div]
      apply le_of_eq
      apply integral_eq_zero_of_ae
      filter_upwards [hω0] with ω hω
      simp [hω]
  | succ t ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine
        ⟨(A ^ 2) ^ 2 * C + 1 / 4,
          add_nonneg
            (mul_nonneg (sq_nonneg (A ^ 2)) hC)
            (by norm_num),
          ?_⟩
      intro q hq N hN
      have hstep :=
        integral_sq_eval_succ_sub_V_iterate_le_global
          hA hq hN t
      have ht := hbound hq hN
      calc
        ∫ ω, (ω (t + 1) - (V A)^[t + 1] q) ^ 2
            ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) ≤
            (A ^ 2) ^ 2 *
                ∫ ω, (ω t - (V A)^[t] q) ^ 2
                  ∂(markovPathMeasure
                    (Measure.dirac q) (Kchain A N)) +
              1 / (4 * (N : ℝ)) :=
          hstep
        _ ≤ (A ^ 2) ^ 2 * (C / (N : ℝ)) +
              1 / (4 * (N : ℝ)) := by
          gcongr
        _ = ((A ^ 2) ^ 2 * C + 1 / 4) / (N : ℝ) := by
          have hNcast : (N : ℝ) ≠ 0 := by
            exact_mod_cast hN.ne'
          field_simp [hNcast]

/-- The uniform fixed-time stable-entrance estimate applies eventually to
every sequence converging to a positive initial radius. -/
theorem
    exists_eventually_markovPathMeasure_stable_entrance_exp_bound_of_tendsto
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
        (markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).real
            {ω : ℕ → ℝ | R < |ω m - qStar|} ≤
          C * Real.exp (-(c * (N : ℝ))) := by
  let r : ℝ := q₀ / 2
  have hr : r ∈ Set.Ioc (0 : ℝ) 1 := by
    dsimp only [r]
    constructor <;> linarith [hq₀.1, hq₀.2]
  obtain ⟨κ, R, η, m, C, c, hκ0, hκ1, hη0, hηR,
      hRinterior, hC, hc, hderiv, hentrance⟩ :=
    exists_uniform_markovPathMeasure_stable_entrance_exp_bound
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
  exact
    hentrance N (Nat.zero_lt_of_lt hN) (q N)
      ⟨hqLowerN.le, hqN.2⟩

/-- A scalar path whose arbitrary initial law is supported on `[0,1]`
remains there at every fixed time almost surely. -/
lemma markovPathMeasure_ae_eval_mem_Kchain_Icc_of_measure
    {A : ℝ} {N : ℕ} (hN : 0 < N)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure μ (Kchain A N)),
      ω t ∈ Set.Icc (0 : ℝ) 1 := by
  cases t with
  | zero =>
      rw [ae_iff]
      have hset :
          {ω : ℕ → ℝ | ¬ω 0 ∈ Set.Icc (0 : ℝ) 1} =
            (fun ω : ℕ → ℝ => ω 0) ⁻¹'
              (Set.Icc (0 : ℝ) 1)ᶜ := rfl
      rw [hset]
      calc
        (markovPathMeasure μ (Kchain A N))
              ((fun ω : ℕ → ℝ => ω 0) ⁻¹'
                (Set.Icc (0 : ℝ) 1)ᶜ) =
            ((markovPathMeasure μ (Kchain A N)).map
              (fun ω => ω 0)) ((Set.Icc (0 : ℝ) 1)ᶜ) :=
          (Measure.map_apply
            (μ := markovPathMeasure μ (Kchain A N))
            (measurable_pi_apply 0)
            measurableSet_Icc.compl).symm
        _ = μ ((Set.Icc (0 : ℝ) 1)ᶜ) := by
          rw [markovPathMeasure_map_zero]
        _ = 0 := hμ
  | succ t =>
      exact markovPathMeasure_ae_eval_succ_mem_Kchain_Icc
        hN μ t

/-- Integrating the scalar conditional recursion works from every probability
initial law supported on `[0,1]`. -/
lemma integral_sq_eval_succ_sub_V_le_of_abs_V_sub_le_of_measure
    {A r κ : ℝ} {N : ℕ}
    (hN : 0 < N) (hκ : 0 ≤ κ)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (t : ℕ)
    (hcontract :
      ∀ᵐ ω ∂(markovPathMeasure μ₀ (Kchain A N)),
        |V A (ω t) - V A r| ≤ κ * |ω t - r|) :
    ∫ ω, (ω (t + 1) - V A r) ^ 2
        ∂(markovPathMeasure μ₀ (Kchain A N)) ≤
      κ ^ 2 *
          ∫ ω, (ω t - r) ^ 2
            ∂(markovPathMeasure μ₀ (Kchain A N)) +
        1 / (4 * (N : ℝ)) := by
  let μ := markovPathMeasure μ₀ (Kchain A N)
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp (s : ℕ) :
      ∀ᵐ ω ∂μ, ω s ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_ae_eval_mem_Kchain_Icc_of_measure
        hN μ₀ hμ₀ s
  have hInt (s : ℕ) (a : ℝ) :
      Integrable (fun ω : ℕ → ℝ => (ω s - a) ^ 2) μ := by
    apply integrable_sq_sub_of_ae_mem_Icc
      μ (fun ω : ℕ → ℝ => ω s) a
    · have hm : Measurable (fun ω : ℕ → ℝ => ω s) :=
        measurable_pi_apply s
      exact
        ((hm.sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact hsupp s
  have hcond :
      μ[fun ω => (ω (t + 1) - V A r) ^ 2 | Filtration.piLE t]
        ≤ᵐ[μ]
          fun ω =>
            κ ^ 2 * (ω t - r) ^ 2 +
              1 / (4 * (N : ℝ)) := by
    simpa only [μ] using
      condExp_sq_eval_succ_sub_V_le_of_abs_V_sub_le
        hN hκ μ₀ t hcontract
  have hright :
      Integrable
        (fun ω : ℕ → ℝ =>
          κ ^ 2 * (ω t - r) ^ 2 +
            1 / (4 * (N : ℝ))) μ :=
    ((hInt t r).const_mul (κ ^ 2)).add
      (integrable_const _)
  change
    (∫ ω, (ω (t + 1) - V A r) ^ 2 ∂μ) ≤
      κ ^ 2 * ∫ ω, (ω t - r) ^ 2 ∂μ +
        1 / (4 * (N : ℝ))
  calc
    ∫ ω, (ω (t + 1) - V A r) ^ 2 ∂μ =
        ∫ ω,
          μ[fun ω =>
              (ω (t + 1) - V A r) ^ 2 |
            Filtration.piLE t] ω ∂μ :=
      (integral_condExp (Filtration.piLE.le t)).symm
    _ ≤
        ∫ ω,
          (κ ^ 2 * (ω t - r) ^ 2 +
            1 / (4 * (N : ℝ))) ∂μ :=
      integral_mono_ae integrable_condExp hright hcond
    _ =
        κ ^ 2 * ∫ ω, (ω t - r) ^ 2 ∂μ +
          1 / (4 * (N : ℝ)) := by
      rw [integral_add
          ((hInt t r).const_mul (κ ^ 2))
          (integrable_const _),
        integral_const_mul, integral_const,
        probReal_univ, one_smul]

/-- The local conditional recursion on survival is independent of the
initial law of the canonical path. -/
lemma
    condExp_sq_eval_succ_sub_V_iterate_le_on_lt_stableIntervalExitTime_of_measure
    {A q qStar R κ : ℝ} {N T t : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hκ : 0 ≤ κ) (hRq : R < qStar)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t + 1 ≤ T)
    (horbit :
      (V A)^[t] q ∈ Set.Icc (qStar - R) (qStar + R)) :
    ∀ᵐ ω ∂(markovPathMeasure μ₀ (Kchain A N)),
      t < stableIntervalExitTime qStar R T ω →
        (markovPathMeasure μ₀ (Kchain A N))[
            fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2 |
              Filtration.piLE t] ω ≤
          κ ^ 2 * (ω t - (V A)^[t] q) ^ 2 +
            1 / (4 * (N : ℝ)) := by
  have heq :=
    condExp_sq_eval_succ_sub_eq_integral_Kchain
      (A := A) (r := V A ((V A)^[t] q)) hN μ₀ t
  rw [show
    (fun ω : ℕ → ℝ => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) =
      (fun ω : ℕ → ℝ =>
        (ω (t + 1) - V A ((V A)^[t] q)) ^ 2) by
      funext ω
      rw [Function.iterate_succ_apply']]
  filter_upwards [heq] with ω hω
  intro hsurvive
  have htT' : t ≤ T := by omega
  have hcontract :=
    abs_V_eval_sub_V_iterate_le_of_lt_stableIntervalExitTime
      hA hRq hderiv htT' horbit hsurvive
  rw [hω]
  exact integral_sq_sub_V_Kchain_le_of_abs_V_sub_le
    hN hκ hcontract

/-- The killed local conditional recursion also holds after restarting from
an arbitrary supported probability law. -/
lemma condExp_indicator_sq_eval_succ_sub_V_iterate_le_of_measure
    {A q qStar R κ : ℝ} {N T t : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hκ : 0 ≤ κ) (hRq : R < qStar)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t + 1 ≤ T)
    (horbit :
      (V A)^[t] q ∈ Set.Icc (qStar - R) (qStar + R)) :
    (markovPathMeasure μ₀ (Kchain A N))[
        fun ω =>
          {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω |
          Filtration.piLE t] ≤ᵐ[
      markovPathMeasure μ₀ (Kchain A N)]
        fun ω =>
          {ω | t < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => κ ^ 2 * (ω t - (V A)^[t] q) ^ 2 +
              1 / (4 * (N : ℝ))) ω := by
  let μ := markovPathMeasure μ₀ (Kchain A N)
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp :
      ∀ᵐ ω ∂μ, ω (t + 1) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_ae_eval_mem_Kchain_Icc_of_measure
        hN μ₀ hμ₀ (t + 1)
  have hint_sq :
      Integrable
        (fun ω : ℕ → ℝ =>
          (ω (t + 1) - (V A)^[t + 1] q) ^ 2) μ := by
    apply integrable_sq_sub_of_ae_mem_Icc μ
      (fun ω : ℕ → ℝ => ω (t + 1)) ((V A)^[t + 1] q)
    · exact
        (((measurable_pi_apply (t + 1)).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact hsupp
  have htT' : t ≤ T := by omega
  have hS0 :
      MeasurableSet[Filtration.piLE t]
        {ω : ℕ → ℝ | t < stableIntervalExitTime qStar R T ω} :=
    measurableSet_lt_stableIntervalExitTime htT'
  have hS1 :
      MeasurableSet
        {ω : ℕ → ℝ | t + 1 < stableIntervalExitTime qStar R T ω} :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le (t + 1) _
      (measurableSet_lt_stableIntervalExitTime htT)
  have hS0ambient :
      MeasurableSet
        {ω : ℕ → ℝ | t < stableIntervalExitTime qStar R T ω} :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le t _ hS0
  have hint_L := hint_sq.indicator hS1
  have hint_M := hint_sq.indicator hS0ambient
  have hpoint :
      ∀ ω : ℕ → ℝ,
        {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω ≤
          {ω | t < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω :=
    indicator_sq_succ_lt_stableIntervalExitTime_le _
  have hmono :=
    condExp_mono (m := Filtration.piLE t)
      hint_L hint_M (ae_of_all μ hpoint)
  have hcore :=
    condExp_sq_eval_succ_sub_V_iterate_le_on_lt_stableIntervalExitTime_of_measure
      hA hN hκ hRq μ₀ hderiv htT horbit
  change
    μ[fun ω =>
        {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
          (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω |
      Filtration.piLE t] ≤ᵐ[μ] _
  refine hmono.trans ?_
  refine (condExp_indicator hint_sq hS0).trans_le ?_
  filter_upwards [hcore] with ω hω
  by_cases h : ω ∈
      {ω | t < stableIntervalExitTime qStar R T ω}
  · simp only [Set.indicator_of_mem h]
    exact hω h
  · simp [Set.indicator_of_notMem h]

/-- The squared error from an arbitrary initial law, killed upon leaving the
stable interval around a deterministic reference orbit. -/
noncomputable def stableIntervalKilledErrorMomentOfMeasure
    (A : ℝ) (N : ℕ) (μ₀ : Measure ℝ)
    (q qStar R : ℝ) (T t : ℕ) : ℝ :=
  ∫ ω,
    {ω | t < stableIntervalExitTime qStar R T ω}.indicator
      (fun ω => (ω t - (V A)^[t] q) ^ 2) ω
    ∂(markovPathMeasure μ₀ (Kchain A N))

/-- Integrating the arbitrary-law killed conditional estimate gives the
one-step affine recursion for its stopped orbit-error moment. -/
lemma stableIntervalKilledErrorMomentOfMeasure_succ_le
    {A q qStar R κ : ℝ} {N T t : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hκ : 0 ≤ κ) (hRq : R < qStar)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t + 1 ≤ T)
    (horbit :
      (V A)^[t] q ∈ Set.Icc (qStar - R) (qStar + R)) :
    stableIntervalKilledErrorMomentOfMeasure
        A N μ₀ q qStar R T (t + 1) ≤
      κ ^ 2 *
          stableIntervalKilledErrorMomentOfMeasure
            A N μ₀ q qStar R T t +
        1 / (4 * (N : ℝ)) := by
  let μ := markovPathMeasure μ₀ (Kchain A N)
  let S0 : Set (ℕ → ℝ) :=
    {ω | t < stableIntervalExitTime qStar R T ω}
  let E : (ℕ → ℝ) → ℝ :=
    fun ω => ω t - (V A)^[t] q
  let d : ℝ := 1 / (4 * (N : ℝ))
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp :
      ∀ᵐ ω ∂μ, ω t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_ae_eval_mem_Kchain_Icc_of_measure
        hN μ₀ hμ₀ t
  have hint_Esq : Integrable (fun ω => E ω ^ 2) μ := by
    apply integrable_sq_sub_of_ae_mem_Icc μ
      (fun ω : ℕ → ℝ => ω t) ((V A)^[t] q)
    · exact
        (((measurable_pi_apply t).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact hsupp
  have htT' : t ≤ T := by omega
  have hS0filtration : MeasurableSet[Filtration.piLE t] S0 := by
    simpa only [S0] using
      (measurableSet_lt_stableIntervalExitTime htT')
  have hS0 : MeasurableSet S0 :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le t _ hS0filtration
  have hEqSR :
      (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω * E ω ^ 2) =
        S0.indicator (fun ω => E ω ^ 2) := by
    ext ω
    by_cases h : ω ∈ S0 <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hint_SR :
      Integrable
        (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω * E ω ^ 2) μ := by
    rw [hEqSR]
    exact hint_Esq.indicator hS0
  have hEqH :
      (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω *
        (κ ^ 2 * E ω ^ 2 + d)) =
        S0.indicator (fun ω => κ ^ 2 * E ω ^ 2 + d) := by
    ext ω
    by_cases h : ω ∈ S0 <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hint_H :
      Integrable
        (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω *
          (κ ^ 2 * E ω ^ 2 + d)) μ := by
    rw [hEqH]
    exact
      ((hint_Esq.const_mul (κ ^ 2)).add (integrable_const d)).indicator hS0
  have hcond0 :
      μ[fun ω =>
          {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω |
        Filtration.piLE t] ≤ᵐ[μ]
        fun ω => S0.indicator
          (fun ω => κ ^ 2 * E ω ^ 2 + d) ω := by
    simpa only [μ, S0, E, d] using
      (condExp_indicator_sq_eval_succ_sub_V_iterate_le_of_measure
        hA hN hκ hRq μ₀ hμ₀ hderiv htT horbit)
  have hcond :
      μ[fun ω =>
          {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω |
        Filtration.piLE t] ≤ᵐ[μ]
        fun ω => S0.indicator (fun _ => (1 : ℝ)) ω *
          (κ ^ 2 * E ω ^ 2 + d) := by
    filter_upwards [hcond0] with ω hω
    by_cases h : ω ∈ S0
    · simpa [Set.indicator_of_mem h] using hω
    · simpa [Set.indicator_of_notMem h] using hω
  have hrec :=
    integral_le_of_condExp_le
      (μ := μ) (m := Filtration.piLE t) (S0 := S0) (R := E)
      (G := fun ω =>
        {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
          (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω)
      (k := κ ^ 2) (d := d)
      (Filtration.piLE.le t) (by dsimp only [d]; positivity)
      hS0 hcond hint_H hint_SR
  rw [hEqSR] at hrec
  simpa only [stableIntervalKilledErrorMomentOfMeasure, μ, S0, E, d] using hrec

/-- Through a finite stable horizon, the killed moment retains the
geometrically damped initial second moment and accumulates only the uniform
`N⁻¹` noise floor. -/
lemma stableIntervalKilledErrorMomentOfMeasure_le
    {A q qStar R κ : ℝ} {N T t : ℕ}
    (hA : A ≠ 0) (hN : 0 < N)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hRq : R < qStar)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t ≤ T)
    (horbit :
      ∀ s ≤ t, (V A)^[s] q ∈ Set.Icc (qStar - R) (qStar + R)) :
    stableIntervalKilledErrorMomentOfMeasure A N μ₀ q qStar R T t ≤
      (κ ^ 2) ^ t * ∫ x, (x - q) ^ 2 ∂μ₀ +
        (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) := by
  let m : ℕ → ℝ :=
    fun s =>
      stableIntervalKilledErrorMomentOfMeasure
        A N μ₀ q qStar R T s
  have hrec :
      ∀ s < t, m (s + 1) ≤
        κ ^ 2 * m s + 1 / (4 * (N : ℝ)) := by
    intro s hst
    apply stableIntervalKilledErrorMomentOfMeasure_succ_le
      hA hN hκ0 hRq μ₀ hμ₀ hderiv
    · exact (Nat.succ_le_of_lt hst).trans htT
    · exact horbit s hst.le
  have hκsq : κ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hκ0 zero_le_one).2 hκ1
  have hgeom :
      m t ≤ (κ ^ 2) ^ t * m 0 +
        (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) :=
    geom_recursion_bound_contraction_pow_of_lt
      (sq_nonneg κ) hκsq (by positivity) hrec
  let μ := markovPathMeasure μ₀ (Kchain A N)
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp :
      ∀ᵐ ω ∂μ, ω 0 ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_ae_eval_mem_Kchain_Icc_of_measure
        hN μ₀ hμ₀ 0
  have hint :
      Integrable (fun ω : ℕ → ℝ => (ω 0 - q) ^ 2) μ := by
    apply integrable_sq_sub_of_ae_mem_Icc
      μ (fun ω : ℕ → ℝ => ω 0) q
    · exact
        (((measurable_pi_apply 0).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact hsupp
  have hSfiltration :
      MeasurableSet[Filtration.piLE 0]
        {ω : ℕ → ℝ | 0 < stableIntervalExitTime qStar R T ω} :=
    measurableSet_lt_stableIntervalExitTime (Nat.zero_le T)
  have hS :
      MeasurableSet
        {ω : ℕ → ℝ | 0 < stableIntervalExitTime qStar R T ω} :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le 0 _ hSfiltration
  have hm0path :
      m 0 ≤ ∫ ω, (ω 0 - q) ^ 2 ∂μ := by
    dsimp only [m, stableIntervalKilledErrorMomentOfMeasure]
    change
      (∫ ω,
          {ω | 0 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω 0 - q) ^ 2) ω ∂μ) ≤
        ∫ ω, (ω 0 - q) ^ 2 ∂μ
    apply integral_mono_ae (hint.indicator hS) hint
    filter_upwards with ω
    by_cases h :
        0 < stableIntervalExitTime qStar R T ω
    · rw [Set.indicator_of_mem
        (show ω ∈
          {ω | 0 < stableIntervalExitTime qStar R T ω} from h)]
    · rw [Set.indicator_of_notMem
        (show ω ∉
          {ω | 0 < stableIntervalExitTime qStar R T ω} from h)]
      exact sq_nonneg _
  have hmap :
      (∫ ω, (ω 0 - q) ^ 2 ∂μ) =
        ∫ x, (x - q) ^ 2 ∂μ₀ := by
    rw [← integral_map
      (μ := μ)
      (φ := fun ω : ℕ → ℝ => ω 0)
      (f := fun x : ℝ => (x - q) ^ 2)
      (measurable_pi_apply 0).aemeasurable
      (((measurable_id.sub measurable_const).pow_const 2)
        |>.aestronglyMeasurable),
      show μ.map (fun ω : ℕ → ℝ => ω 0) = μ₀ by
        simpa only [μ] using
          (markovPathMeasure_map_zero
            (μ₀ := μ₀) (κ := Kchain A N))]
  have hm0 :
      m 0 ≤ ∫ x, (x - q) ^ 2 ∂μ₀ := by
    rw [← hmap]
    exact hm0path
  change m t ≤ _
  exact hgeom.trans
    (add_le_add
      (mul_le_mul_of_nonneg_left hm0 (pow_nonneg (sq_nonneg κ) t))
      le_rfl)

/-- The path-space one-step Hoeffding bound is uniform over the initial
probability law. -/
lemma markovPathMeasure_measureReal_abs_next_sub_V_gt_le_of_measure
    {A ε : ℝ} {N : ℕ} (hN : 0 < N) (hε : 0 < ε)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    (markovPathMeasure μ₀ (Kchain A N)).real
        {ω : ℕ → ℝ | |ω (t + 1) - V A (ω t)| > ε} ≤
      2 * Real.exp (-2 * N * ε ^ 2) := by
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure μ₀ (Kchain A N)
  let current : ((i : Finset.Iic t) → ℝ) → ℝ :=
    fun p => p ⟨t, Finset.mem_Iic.mpr le_rfl⟩
  let D : Set ((((i : Finset.Iic t) → ℝ) × ℝ)) :=
    {p | ε < |p.2 - V A (current p.1)|}
  let ψ : ((((i : Finset.Iic t) → ℝ) × ℝ) → ℝ) :=
    D.indicator fun _ => 1
  let E : Set (ℕ → ℝ) :=
    {ω | ε < |ω (t + 1) - V A (ω t)|}
  have hcurrent : Measurable current :=
    measurable_pi_apply
      (⟨t, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic t)
  have hD : MeasurableSet D := by
    apply measurableSet_lt measurable_const
    exact (measurable_snd.sub
      ((V_continuous A).measurable.comp
        (hcurrent.comp measurable_fst))).abs
  have hψ : StronglyMeasurable ψ :=
    measurable_const.indicator hD |>.stronglyMeasurable
  have hE : MeasurableSet E := by
    apply measurableSet_lt measurable_const
    exact ((measurable_pi_apply (t + 1)).sub
      ((V_continuous A).measurable.comp
        (measurable_pi_apply t))).abs
  have hpath :
      (fun ω : ℕ → ℝ =>
        ψ (Preorder.frestrictLe t ω, ω (t + 1))) =
        fun ω => E.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp only [ψ, D, E, current, Set.indicator_apply,
      Set.mem_setOf_eq, Preorder.frestrictLe_apply]
    rfl
  have hψint :
      Integrable (fun ω : ℕ → ℝ =>
        ψ (Preorder.frestrictLe t ω, ω (t + 1))) μ := by
    rw [hpath]
    exact (integrable_const (1 : ℝ)).indicator hE
  have hcondEq :=
    condExp_markovPathMeasure_prefix_eval_succ_piLE
      μ₀ (Kchain A N) t hψ hψint
  have hcond :
      μ[fun ω =>
          E.indicator (fun _ => (1 : ℝ)) ω |
        Filtration.piLE t] ≤ᵐ[μ]
          fun _ => 2 * Real.exp (-2 * N * ε ^ 2) := by
    filter_upwards [hcondEq] with ω hω
    rw [show
      (fun ω =>
        E.indicator (fun _ => (1 : ℝ)) ω) =
          (fun ω =>
            ψ (Preorder.frestrictLe t ω, ω (t + 1))) by
              exact hpath.symm, hω]
    have hstep :=
      Kchain_measureReal_abs_sub_V_gt_le
        (A := A) (q := ω t) hN hε
    have hnext :
        (∫ y, ψ (Preorder.frestrictLe t ω, y)
            ∂(Kchain A N (ω t))) =
          (Kchain A N (ω t)).real
            {y : ℝ | |y - V A (ω t)| > ε} := by
      rw [show
        (fun y =>
          ψ (Preorder.frestrictLe t ω, y)) =
            {y : ℝ | |y - V A (ω t)| > ε}.indicator
              (fun _ => (1 : ℝ)) by
                funext y
                simp only [ψ, D, current, Set.indicator_apply,
                  Set.mem_setOf_eq, Preorder.frestrictLe_apply]
                rfl,
        integral_indicator_const, smul_eq_mul, mul_one]
      exact measurableSet_lt measurable_const
        ((measurable_id.sub measurable_const).abs)
    rw [hnext]
    exact hstep
  have hGint :
      Integrable (fun ω =>
        E.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hE
  calc
    μ.real E =
        ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
      rw [integral_indicator_const, smul_eq_mul, mul_one]
      exact hE
    _ = ∫ ω,
          μ[fun ω =>
              E.indicator (fun _ => (1 : ℝ)) ω |
            Filtration.piLE t] ω ∂μ :=
      (integral_condExp (Filtration.piLE.le t)).symm
    _ ≤ ∫ _ω, 2 * Real.exp (-2 * N * ε ^ 2) ∂μ :=
      integral_mono_ae integrable_condExp (integrable_const _) hcond
    _ = 2 * Real.exp (-2 * N * ε ^ 2) := by
      rw [integral_const, probReal_univ, one_smul]

/-- A finite union bound makes the arbitrary-law path deviation estimate
uniform through the whole horizon. -/
lemma
    markovPathMeasure_measureReal_finiteHorizonKchainStepDeviationEvent_le_of_measure
    {A ε : ℝ} {N T : ℕ} (hN : 0 < N) (hε : 0 < ε)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] :
    (markovPathMeasure μ₀ (Kchain A N)).real
        (finiteHorizonKchainStepDeviationEvent A ε T) ≤
      2 * T * Real.exp (-2 * N * ε ^ 2) := by
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure μ₀ (Kchain A N)
  let b : ℝ := 2 * Real.exp (-2 * N * ε ^ 2)
  rw [finiteHorizonKchainStepDeviationEvent]
  calc
    μ.real
        (⋃ s ∈ Finset.range T,
          {ω : ℕ → ℝ | |ω (s + 1) - V A (ω s)| > ε}) ≤
      ∑ s ∈ Finset.range T,
        μ.real {ω : ℕ → ℝ | |ω (s + 1) - V A (ω s)| > ε} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _s ∈ Finset.range T, b := by
      apply Finset.sum_le_sum
      intro s _hs
      exact
        markovPathMeasure_measureReal_abs_next_sub_V_gt_le_of_measure
          hN hε μ₀ s
    _ = 2 * T * Real.exp (-2 * N * ε ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, b]
      ring

/-- Starting anywhere in the stable interval, contraction toward the fixed
point and uniformly small step deviations prevent exit through the horizon. -/
lemma stableIntervalExitTime_eq_sentinel_of_initial_mem_of_step_deviation_le
    {A qStar R κ δ : ℝ} {T : ℕ} {ω : ℕ → ℝ}
    (hA : A ≠ 0) (hR0 : 0 ≤ R) (hκ0 : 0 ≤ κ) (hRq : R < qStar)
    (hfix : V A qStar = qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * R ≤ R)
    (hω0 : ω 0 ∈ Set.Icc (qStar - R) (qStar + R))
    (hstep :
      ∀ s < T, |ω (s + 1) - V A (ω s)| ≤ δ) :
    stableIntervalExitTime qStar R T ω = T + 1 := by
  have hqStarMem :
      qStar ∈ Set.Icc (qStar - R) (qStar + R) := by
    constructor <;> linarith
  have hmem :
      ∀ s ≤ T, ω s ∈ Set.Icc (qStar - R) (qStar + R) := by
    intro s hsT
    induction s with
    | zero =>
        exact hω0
    | succ s ih =>
        have hsT' : s ≤ T := (Nat.le_succ s).trans hsT
        have hslt : s < T := Nat.lt_of_succ_le hsT
        have hsMem := ih hsT'
        have hcontract :=
          abs_V_sub_le_mul_abs_sub_of_mem_stableInterval
            hA hRq hderiv hsMem hqStarMem
        have hmean :
            |V A (ω s) - qStar| ≤
              κ * |ω s - qStar| := by
          simpa only [hfix] using hcontract
        have hsAbs : |ω s - qStar| ≤ R := by
          rw [abs_le]
          constructor <;> linarith [hsMem.1, hsMem.2]
        have hnextAbs : |ω (s + 1) - qStar| ≤ R := by
          calc
            |ω (s + 1) - qStar| ≤
                |ω (s + 1) - V A (ω s)| +
                  |V A (ω s) - qStar| :=
              abs_sub_le _ _ _
            _ ≤ δ + κ * |ω s - qStar| :=
              add_le_add (hstep s hslt) hmean
            _ ≤ δ + κ * R :=
              add_le_add le_rfl
                (mul_le_mul_of_nonneg_left hsAbs hκ0)
            _ ≤ R := hbuffer
        rw [abs_le] at hnextAbs
        exact
          ⟨by linarith [hnextAbs.1],
            by linarith [hnextAbs.2]⟩
  have hsurvive :
      T < stableIntervalExitTime qStar R T ω :=
    (lt_stableIntervalExitTime_iff le_rfl).2 hmem
  have hsentinel :=
    stableIntervalExitTime_le_sentinel qStar R T ω
  omega

/-- From an arbitrary initial law, stable-interval exit can only come from
initial entrance failure or a later large one-step deviation. -/
lemma markovPathMeasure_measureReal_stableIntervalExitTime_le_of_measure
    {A qStar R κ δ : ℝ} {N T : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hR0 : 0 ≤ R)
    (hκ0 : 0 ≤ κ) (hδ : 0 < δ) (hRq : R < qStar)
    (hfix : V A qStar = qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * R ≤ R)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] :
    (markovPathMeasure μ₀ (Kchain A N)).real
        {ω : ℕ → ℝ |
          stableIntervalExitTime qStar R T ω ≤ T} ≤
      μ₀.real {x : ℝ | R < |x - qStar|} +
        2 * T * Real.exp (-2 * N * δ ^ 2) := by
  let μ := markovPathMeasure μ₀ (Kchain A N)
  let Eexit : Set (ℕ → ℝ) :=
    {ω | stableIntervalExitTime qStar R T ω ≤ T}
  let E0 : Set (ℕ → ℝ) :=
    {ω | R < |ω 0 - qStar|}
  let Edev : Set (ℕ → ℝ) :=
    finiteHorizonKchainStepDeviationEvent A δ T
  have hsubset : Eexit ⊆ E0 ∪ Edev := by
    intro ω hexit
    by_cases hω0 :
        ω 0 ∈ Set.Icc (qStar - R) (qStar + R)
    · right
      by_contra hnotdev
      have hstep :
          ∀ s < T, |ω (s + 1) - V A (ω s)| ≤ δ := by
        intro s hsT
        apply le_of_not_gt
        intro hgt
        apply hnotdev
        dsimp only [Edev, finiteHorizonKchainStepDeviationEvent]
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨s, ⟨Finset.mem_range.mpr hsT, hgt⟩⟩
      have hsentinel :=
        stableIntervalExitTime_eq_sentinel_of_initial_mem_of_step_deviation_le
          hA hR0 hκ0 hRq hfix hderiv hbuffer hω0 hstep
      change stableIntervalExitTime qStar R T ω ≤ T at hexit
      rw [hsentinel] at hexit
      omega
    · left
      change R < |ω 0 - qStar|
      apply lt_of_not_ge
      intro habs
      rw [abs_le] at habs
      apply hω0
      exact
        ⟨by linarith [habs.1],
          by linarith [habs.2]⟩
  have hE0 :
      μ.real E0 =
        μ₀.real {x : ℝ | R < |x - qStar|} := by
    have hmeas :
        MeasurableSet {x : ℝ | R < |x - qStar|} :=
      measurableSet_lt measurable_const
        ((measurable_id.sub measurable_const).abs)
    calc
      μ.real E0 =
          (μ.map (fun ω : ℕ → ℝ => ω 0)).real
            {x : ℝ | R < |x - qStar|} := by
        dsimp only [E0]
        exact
          (map_measureReal_apply
            (μ := μ) (measurable_pi_apply 0) hmeas).symm
      _ = μ₀.real {x : ℝ | R < |x - qStar|} := by
        rw [show μ.map (fun ω : ℕ → ℝ => ω 0) = μ₀ by
          simpa only [μ] using
            (markovPathMeasure_map_zero
              (μ₀ := μ₀) (κ := Kchain A N))]
  calc
    μ.real Eexit ≤ μ.real (E0 ∪ Edev) :=
      measureReal_mono hsubset (measure_ne_top μ (E0 ∪ Edev))
    _ ≤ μ.real E0 + μ.real Edev :=
      measureReal_union_le E0 Edev
    _ = μ₀.real {x : ℝ | R < |x - qStar|} +
        μ.real Edev := by rw [hE0]
    _ ≤ μ₀.real {x : ℝ | R < |x - qStar|} +
        2 * T * Real.exp (-2 * N * δ ^ 2) :=
      add_le_add le_rfl
        (by
          simpa only [μ, Edev] using
            (markovPathMeasure_measureReal_finiteHorizonKchainStepDeviationEvent_le_of_measure
              hN hδ μ₀))

/-- Splitting over survival and exit removes the arbitrary-law stopping:
the full orbit-error moment is the killed moment plus the exit probability. -/
lemma integral_sq_eval_sub_V_iterate_le_killed_add_exit_of_measure
    {A q qStar R : ℝ} {N T t : ℕ}
    (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (hμ₀ : μ₀ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (htT : t ≤ T)
    (horbit01 : (V A)^[t] q ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, (ω t - (V A)^[t] q) ^ 2
        ∂(markovPathMeasure μ₀ (Kchain A N)) ≤
      stableIntervalKilledErrorMomentOfMeasure
          A N μ₀ q qStar R T t +
        (markovPathMeasure μ₀ (Kchain A N)).real
          {ω : ℕ → ℝ |
            stableIntervalExitTime qStar R T ω ≤ T} := by
  let μ := markovPathMeasure μ₀ (Kchain A N)
  let S : Set (ℕ → ℝ) :=
    {ω | t < stableIntervalExitTime qStar R T ω}
  let B : Set (ℕ → ℝ) :=
    {ω | stableIntervalExitTime qStar R T ω ≤ t}
  let BT : Set (ℕ → ℝ) :=
    {ω | stableIntervalExitTime qStar R T ω ≤ T}
  let E : (ℕ → ℝ) → ℝ :=
    fun ω => (ω t - (V A)^[t] q) ^ 2
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp :
      ∀ᵐ ω ∂μ, ω t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_ae_eval_mem_Kchain_Icc_of_measure
        hN μ₀ hμ₀ t
  have hint_E : Integrable E μ := by
    apply integrable_sq_sub_of_ae_mem_Icc μ
      (fun ω : ℕ → ℝ => ω t) ((V A)^[t] q)
    · exact
        (((measurable_pi_apply t).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact hsupp
  have hSfiltration : MeasurableSet[Filtration.piLE t] S := by
    simpa only [S] using
      measurableSet_lt_stableIntervalExitTime htT
  have hS : MeasurableSet S :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le t _ hSfiltration
  have hB : MeasurableSet B := by
    rw [show B = Sᶜ by
      ext ω
      simp [B, S]]
    exact hS.compl
  have hBT : MeasurableSet BT := by
    simpa only [BT] using
      measurableSet_stableIntervalExitTime_le qStar R T
  have hsplit : E = S.indicator E + B.indicator E := by
    funext ω
    simp only [Pi.add_apply]
    by_cases h : t < stableIntervalExitTime qStar R T ω
    · have hn :
          ¬stableIntervalExitTime qStar R T ω ≤ t :=
        Nat.not_le_of_lt h
      rw [Set.indicator_of_mem (show ω ∈ S from h),
        Set.indicator_of_notMem (show ω ∉ B from hn), add_zero]
    · have hb :
          stableIntervalExitTime qStar R T ω ≤ t :=
        Nat.le_of_not_gt h
      rw [Set.indicator_of_notMem (show ω ∉ S from h),
        Set.indicator_of_mem (show ω ∈ B from hb), zero_add]
  have hEle : ∀ᵐ ω ∂μ, E ω ≤ 1 := by
    filter_upwards [hsupp] with ω hω
    dsimp only [E]
    have hlower : -1 ≤ ω t - (V A)^[t] q := by
      linarith [hω.1, horbit01.2]
    have hupper : ω t - (V A)^[t] q ≤ 1 := by
      linarith [hω.2, horbit01.1]
    nlinarith [sq_nonneg (ω t - (V A)^[t] q)]
  have hbad :
      ∫ ω, B.indicator E ω ∂μ ≤ μ.real BT := by
    have hright :
        Integrable (BT.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hBT
    calc
      ∫ ω, B.indicator E ω ∂μ ≤
          ∫ ω, BT.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        apply integral_mono_ae (hint_E.indicator hB) hright
        filter_upwards [hEle] with ω hω
        by_cases hb : ω ∈ B
        · have hbT : ω ∈ BT := by
            change stableIntervalExitTime qStar R T ω ≤ t at hb
            change stableIntervalExitTime qStar R T ω ≤ T
            exact hb.trans htT
          simp only [Set.indicator_of_mem hb,
            Set.indicator_of_mem hbT]
          exact hω
        · rw [Set.indicator_of_notMem hb]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      _ = μ.real BT := by
        rw [integral_indicator_const, smul_eq_mul, mul_one]
        exact hBT
  change
    (∫ ω, E ω ∂μ) ≤
      (∫ ω, S.indicator E ω ∂μ) + μ.real BT
  calc
    ∫ ω, E ω ∂μ =
        ∫ ω, (S.indicator E + B.indicator E) ω ∂μ :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun ω => congrFun hsplit ω)
    _ = (∫ ω, S.indicator E ω ∂μ) +
        ∫ ω, B.indicator E ω ∂μ :=
      integral_add (hint_E.indicator hS) (hint_E.indicator hB)
    _ ≤ (∫ ω, S.indicator E ω ∂μ) + μ.real BT :=
      add_le_add le_rfl hbad

end AbsorptionCutoff
