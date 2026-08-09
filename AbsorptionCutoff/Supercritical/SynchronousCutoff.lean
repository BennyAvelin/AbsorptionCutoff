/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.CutoffDynamics

/-!
# Synchronous coupling estimates for the supercritical cutoff

This module continues the synchronous squared-radius coupling package after
the dynamic concentration and foundational coupling estimates established in
`CutoffDynamics.lean`. Keeping subsequent terminal-block estimates here avoids
re-elaborating the large dynamic-concentration module for each small coupling
unit.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- Separate scalar delocalization bounds on the two coordinates control
delocalization of the synchronous pair from the common stable interval. -/
lemma markovPathMeasure_measureReal_eval_not_mem_stableInterval_prod_le_add
    {A qStar R B₁ B₂ : ℝ} {N : ℕ} {q : ℝ × ℝ} {t : ℕ}
    (h₁ :
      (markovPathMeasure (Measure.dirac q.1) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω t ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₁)
    (h₂ :
      (markovPathMeasure (Measure.dirac q.2) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω t ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₂) :
    (markovPathMeasure (Measure.dirac q) (synchronousKchain A N)).real
        {ω : ℕ → ℝ × ℝ |
          ω t ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
            Set.Icc (qStar - R) (qStar + R)} ≤
      B₁ + B₂ := by
  exact
    (markovPathMeasure_measureReal_eval_not_mem_prod_le
      A N q t (Set.Icc (qStar - R) (qStar + R)) measurableSet_Icc).trans
        (add_le_add h₁ h₂)

/-- Uniform scalar localization of both marginals through a terminal block
gives synchronous contraction with the sum of their localization errors. -/
lemma integral_abs_fst_sub_snd_eval_le_pow_mul_add_of_scalar_localization
    {A qStar R κ B₁ B₂ : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) {q : ℝ × ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) {t : ℕ}
    (hbad₁ : ∀ s < t,
      (markovPathMeasure (Measure.dirac q.1) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω s ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₁)
    (hbad₂ : ∀ s < t,
      (markovPathMeasure (Measure.dirac q.2) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω s ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₂) :
    ∫ ω, |(ω t).1 - (ω t).2|
        ∂(markovPathMeasure (Measure.dirac q) (synchronousKchain A N)) ≤
      κ ^ t * |q.1 - q.2| + (B₁ + B₂) / (1 - κ) := by
  apply integral_abs_fst_sub_snd_eval_le_pow_mul_add
    hA hRq hκ0 hκ1 (add_nonneg hB₁ hB₂) hderiv hN hq
  intro s hs
  exact
    markovPathMeasure_measureReal_eval_not_mem_stableInterval_prod_le_add
      (hbad₁ s hs) (hbad₂ s hs)

/-- At each fixed time, the first-coordinate marginal of a synchronous path
with an arbitrary initial pair law is the scalar path started from the
first-coordinate marginal of that law. -/
lemma markovPathMeasure_map_eval_synchronousKchain_map_fst_of_measure
    (A : ℝ) (N : ℕ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (t : ℕ) :
    ((markovPathMeasure μ (synchronousKchain A N)).map
        (fun ω => ω t)).map Prod.fst =
      (markovPathMeasure (μ.map Prod.fst) (Kchain A N)).map
        (fun ω => ω t) := by
  letI : IsProbabilityMeasure (μ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  induction t with
  | zero =>
      rw [markovPathMeasure_map_zero, markovPathMeasure_map_zero]
  | succ t ih =>
      rw [markovPathMeasure_map_eval_succ,
        markovPathMeasure_map_eval_succ]
      ext s hs
      rw [Measure.map_apply measurable_fst hs,
        Measure.bind_apply (measurable_fst hs)
          (synchronousKchain A N).aemeasurable,
        Measure.bind_apply hs (Kchain A N).aemeasurable]
      have hkernel (p : ℝ × ℝ) :
          synchronousKchain A N p (Prod.fst ⁻¹' s) =
            Kchain A N p.1 s := by
        have hm := congrArg (fun ν : Measure ℝ => ν s)
          (synchronousKchain_map_fst A N p)
        rw [Measure.map_apply measurable_fst hs] at hm
        exact hm
      simp_rw [hkernel]
      rw [← ih, lintegral_map
        ((Kchain A N).measurable_coe hs) measurable_fst]

/-- At each fixed time, the second-coordinate marginal of a synchronous path
with an arbitrary initial pair law is the scalar path started from the
second-coordinate marginal of that law. -/
lemma markovPathMeasure_map_eval_synchronousKchain_map_snd_of_measure
    (A : ℝ) (N : ℕ) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (t : ℕ) :
    ((markovPathMeasure μ (synchronousKchain A N)).map
        (fun ω => ω t)).map Prod.snd =
      (markovPathMeasure (μ.map Prod.snd) (Kchain A N)).map
        (fun ω => ω t) := by
  letI : IsProbabilityMeasure (μ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  induction t with
  | zero =>
      rw [markovPathMeasure_map_zero, markovPathMeasure_map_zero]
  | succ t ih =>
      rw [markovPathMeasure_map_eval_succ,
        markovPathMeasure_map_eval_succ]
      ext s hs
      rw [Measure.map_apply measurable_snd hs,
        Measure.bind_apply (measurable_snd hs)
          (synchronousKchain A N).aemeasurable,
        Measure.bind_apply hs (Kchain A N).aemeasurable]
      have hkernel (p : ℝ × ℝ) :
          synchronousKchain A N p (Prod.snd ⁻¹' s) =
            Kchain A N p.2 s := by
        have hm := congrArg (fun ν : Measure ℝ => ν s)
          (synchronousKchain_map_snd A N p)
        rw [Measure.map_apply measurable_snd hs] at hm
        exact hm
      simp_rw [hkernel]
      rw [← ih, lintegral_map
        ((Kchain A N).measurable_coe hs) measurable_snd]

/-- For an arbitrary initial pair law, the probability of leaving `J × J`
at a fixed time is at most the sum of the two scalar marginal
delocalization probabilities. -/
lemma markovPathMeasure_measureReal_eval_not_mem_prod_le_of_measure
    (A : ℝ) (N : ℕ) (ξ : Measure (ℝ × ℝ)) [IsProbabilityMeasure ξ]
    (t : ℕ) (J : Set ℝ) (hJ : MeasurableSet J) :
    (markovPathMeasure ξ (synchronousKchain A N)).real
        {ω : ℕ → ℝ × ℝ | ω t ∉ J ×ˢ J} ≤
      (markovPathMeasure (ξ.map Prod.fst) (Kchain A N)).real
          {ω : ℕ → ℝ | ω t ∉ J} +
        (markovPathMeasure (ξ.map Prod.snd) (Kchain A N)).real
          {ω : ℕ → ℝ | ω t ∉ J} := by
  letI : IsProbabilityMeasure (ξ.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (ξ.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let μ := markovPathMeasure ξ (synchronousKchain A N)
  let μ₁ := markovPathMeasure (ξ.map Prod.fst) (Kchain A N)
  let μ₂ := markovPathMeasure (ξ.map Prod.snd) (Kchain A N)
  let B₁ : Set (ℕ → ℝ × ℝ) :=
    (fun ω => ω t) ⁻¹' (Prod.fst ⁻¹' Jᶜ)
  let B₂ : Set (ℕ → ℝ × ℝ) :=
    (fun ω => ω t) ⁻¹' (Prod.snd ⁻¹' Jᶜ)
  have hunion :
      {ω : ℕ → ℝ × ℝ | ω t ∉ J ×ˢ J} = B₁ ∪ B₂ := by
    ext ω
    simp only [B₁, B₂, Set.mem_union, Set.mem_setOf_eq, Set.mem_prod]
    tauto
  have hfst : μ.real B₁ =
      μ₁.real {ω : ℕ → ℝ | ω t ∉ J} := by
    change μ.real ((fun ω => ω t) ⁻¹' (Prod.fst ⁻¹' Jᶜ)) =
      μ₁.real ((fun ω => ω t) ⁻¹' Jᶜ)
    calc
      μ.real ((fun ω => ω t) ⁻¹' (Prod.fst ⁻¹' Jᶜ)) =
          (μ.map (fun ω => ω t)).real (Prod.fst ⁻¹' Jᶜ) :=
        (map_measureReal_apply (μ := μ) (measurable_pi_apply t)
          (hJ.compl.preimage measurable_fst)).symm
      _ = ((μ.map (fun ω => ω t)).map Prod.fst).real Jᶜ := by
        symm
        exact map_measureReal_apply measurable_fst hJ.compl
      _ = (μ₁.map (fun ω => ω t)).real Jᶜ := by
        rw [markovPathMeasure_map_eval_synchronousKchain_map_fst_of_measure]
      _ = μ₁.real ((fun ω => ω t) ⁻¹' Jᶜ) :=
        map_measureReal_apply (measurable_pi_apply t) hJ.compl
  have hsnd : μ.real B₂ =
      μ₂.real {ω : ℕ → ℝ | ω t ∉ J} := by
    change μ.real ((fun ω => ω t) ⁻¹' (Prod.snd ⁻¹' Jᶜ)) =
      μ₂.real ((fun ω => ω t) ⁻¹' Jᶜ)
    calc
      μ.real ((fun ω => ω t) ⁻¹' (Prod.snd ⁻¹' Jᶜ)) =
          (μ.map (fun ω => ω t)).real (Prod.snd ⁻¹' Jᶜ) :=
        (map_measureReal_apply (μ := μ) (measurable_pi_apply t)
          (hJ.compl.preimage measurable_snd)).symm
      _ = ((μ.map (fun ω => ω t)).map Prod.snd).real Jᶜ := by
        symm
        exact map_measureReal_apply measurable_snd hJ.compl
      _ = (μ₂.map (fun ω => ω t)).real Jᶜ := by
        rw [markovPathMeasure_map_eval_synchronousKchain_map_snd_of_measure]
      _ = μ₂.real ((fun ω => ω t) ⁻¹' Jᶜ) :=
        map_measureReal_apply (measurable_pi_apply t) hJ.compl
  rw [hunion]
  exact (measureReal_union_le B₁ B₂).trans_eq
    (congrArg₂ (· + ·) hfst hsnd)

/-- Separate scalar stable-interval bounds from the two initial marginals
control delocalization of a synchronous path with an arbitrary initial pair
law. -/
lemma
    markovPathMeasure_measureReal_eval_not_mem_stableInterval_prod_le_add_of_measure
    {A qStar R B₁ B₂ : ℝ} {N : ℕ}
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] {t : ℕ}
    (h₁ :
      (markovPathMeasure (μ.map Prod.fst) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω t ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₁)
    (h₂ :
      (markovPathMeasure (μ.map Prod.snd) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω t ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₂) :
    (markovPathMeasure μ (synchronousKchain A N)).real
        {ω : ℕ → ℝ × ℝ |
          ω t ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
            Set.Icc (qStar - R) (qStar + R)} ≤
      B₁ + B₂ := by
  exact
    (markovPathMeasure_measureReal_eval_not_mem_prod_le_of_measure
      A N μ t (Set.Icc (qStar - R) (qStar + R)) measurableSet_Icc).trans
        (add_le_add h₁ h₂)

/-- A synchronous path whose arbitrary initial pair law is supported on
`[0,1]²` remains there at every fixed time almost surely. -/
lemma markovPathMeasure_ae_eval_mem_synchronousKchain_prod_Icc_of_measure
    {A : ℝ} {N : ℕ} (hN : 0 < N)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ :
      μ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure μ (synchronousKchain A N)),
      ω t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  cases t with
  | zero =>
      rw [ae_iff]
      have hset :
          {ω : ℕ → ℝ × ℝ |
              ¬ω 0 ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1} =
            (fun ω : ℕ → ℝ × ℝ => ω 0) ⁻¹'
              (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ := rfl
      rw [hset]
      calc
        (markovPathMeasure μ (synchronousKchain A N))
              ((fun ω : ℕ → ℝ × ℝ => ω 0) ⁻¹'
                (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) =
            ((markovPathMeasure μ (synchronousKchain A N)).map
              (fun ω => ω 0))
                ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) :=
          (Measure.map_apply (μ :=
            markovPathMeasure μ (synchronousKchain A N))
            (measurable_pi_apply 0)
            (measurableSet_Icc.prod measurableSet_Icc).compl).symm
        _ = μ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) := by
          rw [markovPathMeasure_map_zero]
        _ = 0 := hμ
  | succ t =>
      exact markovPathMeasure_ae_eval_succ_mem_synchronousKchain_prod_Icc
        hN μ t

/-- Coordinate distance at every fixed time is integrable along a synchronous
path with an arbitrary probability initial pair law supported on `[0,1]²`. -/
lemma integrable_abs_fst_sub_snd_eval_synchronousKchain_of_measure
    {A : ℝ} {N : ℕ} (hN : 0 < N)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ :
      μ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (t : ℕ) :
    Integrable (fun ω : ℕ → ℝ × ℝ => |(ω t).1 - (ω t).2|)
      (markovPathMeasure μ (synchronousKchain A N)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_pi_apply t).fst.sub
      (measurable_pi_apply t).snd).abs.aestronglyMeasurable) ?_
  filter_upwards [
    markovPathMeasure_ae_eval_mem_synchronousKchain_prod_Icc_of_measure
      hN μ hμ t] with ω hω
  simp only [Real.norm_eq_abs, abs_abs]
  exact abs_le.mpr ⟨by linarith [hω.1.1, hω.2.2],
    by linarith [hω.2.1, hω.1.2]⟩

/-- Along a synchronous path with an arbitrary supported probability initial
pair law, the conditional expected next coordinate distance is the distance
between the current mean-map images. -/
lemma condExp_abs_fst_sub_snd_eval_succ_eq_abs_V_sub_of_measure
    {A : ℝ} {N : ℕ} (hN : 0 < N)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ :
      μ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (t : ℕ) :
    (markovPathMeasure μ (synchronousKchain A N))[
        fun ω => |(ω (t + 1)).1 - (ω (t + 1)).2| | Filtration.piLE t]
      =ᵐ[markovPathMeasure μ (synchronousKchain A N)]
        fun ω => |V A (ω t).1 - V A (ω t).2| := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  let φ : ℝ × ℝ → ℝ := fun p => |p.1 - p.2|
  have hφ : StronglyMeasurable φ := by
    exact (measurable_fst.sub measurable_snd).abs.stronglyMeasurable
  have hφint :
      Integrable (fun ω : ℕ → ℝ × ℝ => φ (ω (t + 1)))
        (markovPathMeasure μ (synchronousKchain A N)) := by
    simpa only [φ] using
      integrable_abs_fst_sub_snd_eval_synchronousKchain_of_measure
        hN μ hμ (t + 1)
  have heq :=
    condExp_markovPathMeasure_eval_succ
      μ (synchronousKchain A N) t hφ hφint
  have hsupp :=
    markovPathMeasure_ae_eval_mem_synchronousKchain_prod_Icc_of_measure
      (A := A) hN μ hμ t
  filter_upwards [heq, hsupp] with ω hω hωsupp
  rw [hω]
  exact integral_abs_fst_sub_snd_synchronousKchain
    hN.ne' hωsupp.1.1 hωsupp.2.1

/-- The synchronous conditional distance for an arbitrary supported initial
pair law contracts on a common stable interval; outside that interval, the
global `[0,1]²` support pays one bad-event indicator. -/
lemma
    condExp_abs_fst_sub_snd_eval_succ_le_mul_add_indicator_of_measure
    {A qStar R κ : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar) (hκ : 0 ≤ κ)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ :
      μ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (t : ℕ) :
    (markovPathMeasure μ (synchronousKchain A N))[
        fun ω => |(ω (t + 1)).1 - (ω (t + 1)).2| | Filtration.piLE t]
      ≤ᵐ[markovPathMeasure μ (synchronousKchain A N)]
        fun ω =>
          κ * |(ω t).1 - (ω t).2| +
            {ω : ℕ → ℝ × ℝ |
              ω t ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
                Set.Icc (qStar - R) (qStar + R)}.indicator
              (fun _ => (1 : ℝ)) ω := by
  have heq :=
    condExp_abs_fst_sub_snd_eval_succ_eq_abs_V_sub_of_measure
      (A := A) hN μ hμ t
  have hsupp :=
    markovPathMeasure_ae_eval_mem_synchronousKchain_prod_Icc_of_measure
      (A := A) hN μ hμ t
  filter_upwards [heq, hsupp] with ω hω hωsupp
  rw [hω]
  by_cases hlocal :
      ω t ∈ Set.Icc (qStar - R) (qStar + R) ×ˢ
        Set.Icc (qStar - R) (qStar + R)
  · rw [Set.indicator_of_notMem (by simpa using hlocal), add_zero]
    exact abs_V_sub_le_mul_abs_sub_of_mem_stableInterval
      hA hRq hderiv hlocal.1 hlocal.2
  · rw [Set.indicator_of_mem (by simpa using hlocal)]
    have hV : |V A (ω t).1 - V A (ω t).2| ≤ 1 := by
      rw [abs_le]
      exact ⟨by
          linarith [V_nonneg A (ω t).1, (V_lt_one A (ω t).2).le],
        by linarith [V_nonneg A (ω t).2, (V_lt_one A (ω t).1).le]⟩
    calc
      |V A (ω t).1 - V A (ω t).2| ≤ 1 := hV
      _ ≤ κ * |(ω t).1 - (ω t).2| + 1 := by
        linarith [mul_nonneg hκ (abs_nonneg ((ω t).1 - (ω t).2))]

/-- Integrating the arbitrary-law localized conditional estimate gives the
synchronous distance recursion with the current bad-localization probability
as its additive error. -/
lemma
    integral_abs_fst_sub_snd_eval_succ_le_mul_add_measureReal_of_measure
    {A qStar R κ : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar) (hκ : 0 ≤ κ)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) (μ₀ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ₀]
    (hμ₀ :
      μ₀ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (t : ℕ) :
    ∫ ω, |(ω (t + 1)).1 - (ω (t + 1)).2|
        ∂(markovPathMeasure μ₀ (synchronousKchain A N)) ≤
      κ * ∫ ω, |(ω t).1 - (ω t).2|
        ∂(markovPathMeasure μ₀ (synchronousKchain A N)) +
      (markovPathMeasure μ₀ (synchronousKchain A N)).real
        {ω : ℕ → ℝ × ℝ |
          ω t ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
            Set.Icc (qStar - R) (qStar + R)} := by
  let μ := markovPathMeasure μ₀ (synchronousKchain A N)
  let B : Set (ℕ → ℝ × ℝ) :=
    {ω | ω t ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
      Set.Icc (qStar - R) (qStar + R)}
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hB : MeasurableSet B := by
    dsimp only [B]
    exact ((measurable_pi_apply t)
      (measurableSet_Icc.prod measurableSet_Icc)).compl
  have hdistInt (s : ℕ) :
      Integrable (fun ω : ℕ → ℝ × ℝ => |(ω s).1 - (ω s).2|) μ := by
    simpa only [μ] using
      integrable_abs_fst_sub_snd_eval_synchronousKchain_of_measure
        hN μ₀ hμ₀ s
  have hindInt :
      Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hright :
      Integrable (fun ω : ℕ → ℝ × ℝ =>
        κ * |(ω t).1 - (ω t).2| +
          B.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((hdistInt t).const_mul κ).add hindInt
  have hcond :
      μ[fun ω => |(ω (t + 1)).1 - (ω (t + 1)).2| |
          Filtration.piLE t]
        ≤ᵐ[μ] fun ω =>
          κ * |(ω t).1 - (ω t).2| +
            B.indicator (fun _ => (1 : ℝ)) ω := by
    simpa only [μ, B] using
      condExp_abs_fst_sub_snd_eval_succ_le_mul_add_indicator_of_measure
        hA hRq hκ hderiv hN μ₀ hμ₀ t
  change
    (∫ ω, |(ω (t + 1)).1 - (ω (t + 1)).2| ∂μ) ≤
      κ * ∫ ω, |(ω t).1 - (ω t).2| ∂μ + μ.real B
  calc
    ∫ ω, |(ω (t + 1)).1 - (ω (t + 1)).2| ∂μ =
        ∫ ω, μ[fun ω => |(ω (t + 1)).1 - (ω (t + 1)).2| |
          Filtration.piLE t] ω ∂μ :=
      (integral_condExp (Filtration.piLE.le t)).symm
    _ ≤ ∫ ω, (κ * |(ω t).1 - (ω t).2| +
        B.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
      integral_mono_ae integrable_condExp hright hcond
    _ = κ * ∫ ω, |(ω t).1 - (ω t).2| ∂μ + μ.real B := by
      rw [integral_add ((hdistInt t).const_mul κ) hindInt,
        integral_const_mul, integral_indicator_const, smul_eq_mul, mul_one]
      exact hB

/-- A uniform bad-localization bound through time `t` iterates the
arbitrary-law synchronous recursion while retaining geometric decay of the
initial expected distance. -/
lemma integral_abs_fst_sub_snd_eval_le_pow_mul_add_of_measure
    {A qStar R κ B : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hB : 0 ≤ B)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) (μ₀ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ₀]
    (hμ₀ :
      μ₀ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    {t : ℕ}
    (hbad : ∀ s < t,
      (markovPathMeasure μ₀ (synchronousKchain A N)).real
        {ω : ℕ → ℝ × ℝ |
          ω s ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
            Set.Icc (qStar - R) (qStar + R)} ≤ B) :
    ∫ ω, |(ω t).1 - (ω t).2|
        ∂(markovPathMeasure μ₀ (synchronousKchain A N)) ≤
      κ ^ t * (∫ p, |p.1 - p.2| ∂μ₀) + B / (1 - κ) := by
  let μ := markovPathMeasure μ₀ (synchronousKchain A N)
  let m : ℕ → ℝ :=
    fun s => ∫ ω, |(ω s).1 - (ω s).2| ∂μ
  have hrec : ∀ s < t, m (s + 1) ≤ κ * m s + B := by
    intro s hs
    have hstep :=
      integral_abs_fst_sub_snd_eval_succ_le_mul_add_measureReal_of_measure
        hA hRq hκ0 hderiv hN μ₀ hμ₀ s
    have hstep' : m (s + 1) ≤ κ * m s +
        (markovPathMeasure μ₀ (synchronousKchain A N)).real
          {ω : ℕ → ℝ × ℝ |
            ω s ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
              Set.Icc (qStar - R) (qStar + R)} := by
      simpa only [m, μ] using hstep
    exact hstep'.trans (add_le_add_right (hbad s hs) _)
  have hiter :=
    geom_recursion_bound_contraction_pow_of_lt
      hκ0 hκ1 hB hrec
  have hm0 : m 0 = ∫ p, |p.1 - p.2| ∂μ₀ := by
    dsimp only [m, μ]
    rw [← integral_map
      (μ := markovPathMeasure μ₀ (synchronousKchain A N))
      (φ := fun ω : ℕ → ℝ × ℝ => ω 0)
      (f := fun p : ℝ × ℝ => |p.1 - p.2|)
      (measurable_pi_apply 0).aemeasurable
      (measurable_fst.sub measurable_snd).abs.aestronglyMeasurable,
      markovPathMeasure_map_zero]
  rw [hm0] at hiter
  exact hiter

/-- Uniform scalar localization of both random-start marginals through a
terminal block gives synchronous contraction with the sum of their
localization errors. -/
lemma
    integral_abs_fst_sub_snd_eval_le_pow_mul_add_of_measure_of_scalar_localization
    {A qStar R κ B₁ B₂ : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) (μ₀ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ₀]
    (hμ₀ :
      μ₀ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    {t : ℕ}
    (hbad₁ : ∀ s < t,
      (markovPathMeasure (μ₀.map Prod.fst) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω s ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₁)
    (hbad₂ : ∀ s < t,
      (markovPathMeasure (μ₀.map Prod.snd) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω s ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₂) :
    ∫ ω, |(ω t).1 - (ω t).2|
        ∂(markovPathMeasure μ₀ (synchronousKchain A N)) ≤
      κ ^ t * (∫ p, |p.1 - p.2| ∂μ₀) +
        (B₁ + B₂) / (1 - κ) := by
  apply integral_abs_fst_sub_snd_eval_le_pow_mul_add_of_measure
    hA hRq hκ0 hκ1 (add_nonneg hB₁ hB₂) hderiv hN μ₀ hμ₀
  intro s hs
  exact
    markovPathMeasure_measureReal_eval_not_mem_stableInterval_prod_le_add_of_measure
      μ₀ (hbad₁ s hs) (hbad₂ s hs)

/-- The product of two probability measures supported on `[0,1]` is
supported on `[0,1]²`. -/
lemma Measure.prod_apply_compl_prod_Icc_eq_zero
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hν : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) :
    (μ.prod ν)
      ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  let S := Set.Icc (0 : ℝ) 1
  have hsubset :
      (S ×ˢ S)ᶜ ⊆
        (Sᶜ ×ˢ Set.univ) ∪ (Set.univ ×ˢ Sᶜ) := by
    intro p hp
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff,
      Set.mem_univ, and_true, true_and]
    simp only [Set.mem_compl_iff, Set.mem_prod] at hp
    tauto
  have hleft : (μ.prod ν) (Sᶜ ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, hμ, zero_mul]
  have hright : (μ.prod ν) (Set.univ ×ˢ Sᶜ) = 0 := by
    rw [Measure.prod_prod, hν, mul_zero]
  exact measure_mono_null hsubset (measure_union_null hleft hright)

/-- On a probability space, a centered first absolute moment is bounded by
the square root of the corresponding second moment. -/
lemma integral_abs_sub_le_sqrt_integral_sq
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (qStar : ℝ)
    (hsq : Integrable (fun q => (q - qStar) ^ 2) μ) :
    ∫ q, |q - qStar| ∂μ ≤
      Real.sqrt (∫ q, (q - qStar) ^ 2 ∂μ) := by
  have hmem :
      MemLp (fun q : ℝ => q - qStar) 2 μ :=
    (memLp_two_iff_integrable_sq
      (measurable_id.sub measurable_const).aestronglyMeasurable).2 hsq
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hmemReal :
      MemLp (fun q : ℝ => q - qStar)
        (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hmem
  have hcs := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) hholder hmemReal (memLp_const (1 : ℝ))
  simpa only [Real.norm_eq_abs, abs_one, mul_one, ENNReal.ofReal_ofNat,
    Real.rpow_two, sq_abs, integral_const, probReal_univ, one_smul,
    one_pow, Real.one_rpow, Real.sqrt_eq_rpow] using hcs

/-- Under an independent product law, the expected distance between the
two coordinates is bounded by their centered root second moments. -/
lemma integral_abs_fst_sub_snd_prod_le_add_sqrt_integral_sq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (qStar : ℝ)
    (hμsq : Integrable (fun q => (q - qStar) ^ 2) μ)
    (hνsq : Integrable (fun q => (q - qStar) ^ 2) ν) :
    ∫ p, |p.1 - p.2| ∂(μ.prod ν) ≤
      Real.sqrt (∫ q, (q - qStar) ^ 2 ∂μ) +
        Real.sqrt (∫ q, (q - qStar) ^ 2 ∂ν) := by
  have hμmem :
      MemLp (fun q : ℝ => q - qStar) 2 μ :=
    (memLp_two_iff_integrable_sq
      (measurable_id.sub measurable_const).aestronglyMeasurable).2 hμsq
  have hνmem :
      MemLp (fun q : ℝ => q - qStar) 2 ν :=
    (memLp_two_iff_integrable_sq
      (measurable_id.sub measurable_const).aestronglyMeasurable).2 hνsq
  have hμabs : Integrable (fun q : ℝ => |q - qStar|) μ :=
    (hμmem.integrable (by norm_num)).abs
  have hνabs : Integrable (fun q : ℝ => |q - qStar|) ν :=
    (hνmem.integrable (by norm_num)).abs
  have hfst :
      Integrable (fun p : ℝ × ℝ => |p.1 - qStar|) (μ.prod ν) :=
    hμabs.comp_fst ν
  have hsnd :
      Integrable (fun p : ℝ × ℝ => |p.2 - qStar|) (μ.prod ν) :=
    hνabs.comp_snd μ
  have hsum :
      Integrable
        (fun p : ℝ × ℝ => |p.1 - qStar| + |p.2 - qStar|)
        (μ.prod ν) :=
    hfst.add hsnd
  have hpoint (p : ℝ × ℝ) :
      |p.1 - p.2| ≤ |p.1 - qStar| + |p.2 - qStar| := by
    calc
      |p.1 - p.2| =
          |(p.1 - qStar) + (qStar - p.2)| := by
        congr 1
        ring
      _ ≤ |p.1 - qStar| + |qStar - p.2| := abs_add_le _ _
      _ = |p.1 - qStar| + |p.2 - qStar| := by
        rw [abs_sub_comm qStar p.2]
  have hdist :
      Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) (μ.prod ν) := by
    refine hsum.mono'
      (measurable_fst.sub measurable_snd).abs.aestronglyMeasurable ?_
    filter_upwards with p
    simpa only [Real.norm_eq_abs, abs_abs,
      abs_of_nonneg
        (add_nonneg (abs_nonneg (p.1 - qStar))
          (abs_nonneg (p.2 - qStar)))] using
      hpoint p
  calc
    ∫ p, |p.1 - p.2| ∂(μ.prod ν) ≤
        ∫ p, (|p.1 - qStar| + |p.2 - qStar|) ∂(μ.prod ν) :=
      integral_mono_ae hdist hsum (Filter.Eventually.of_forall hpoint)
    _ = (∫ q, |q - qStar| ∂μ) + ∫ q, |q - qStar| ∂ν := by
      rw [integral_add hfst hsnd]
      have hleft := integral_fun_fst
        (μ := μ) (ν := ν) (fun q : ℝ => |q - qStar|)
      have hright := integral_fun_snd
        (μ := μ) (ν := ν) (fun q : ℝ => |q - qStar|)
      rw [hleft, hright]
      simp only [probReal_univ, one_smul]
    _ ≤ Real.sqrt (∫ q, (q - qStar) ^ 2 ∂μ) +
        Real.sqrt (∫ q, (q - qStar) ^ 2 ∂ν) :=
      add_le_add
        (integral_abs_sub_le_sqrt_integral_sq μ qStar hμsq)
        (integral_abs_sub_le_sqrt_integral_sq ν qStar hνsq)

/-- Explicit inverse-dimension second-moment envelopes give an
inverse-square-root bound on the initial product-law distance. -/
lemma integral_abs_fst_sub_snd_prod_le_add_sqrt_div_sqrt_nat
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (qStar : ℝ) {C₁ C₂ : ℝ} {N : ℕ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμsq : Integrable (fun q => (q - qStar) ^ 2) μ)
    (hνsq : Integrable (fun q => (q - qStar) ^ 2) ν)
    (hμbound :
      (∫ q, (q - qStar) ^ 2 ∂μ) ≤ C₁ / (N : ℝ))
    (hνbound :
      (∫ q, (q - qStar) ^ 2 ∂ν) ≤ C₂ / (N : ℝ)) :
    ∫ p, |p.1 - p.2| ∂(μ.prod ν) ≤
      (Real.sqrt C₁ + Real.sqrt C₂) / Real.sqrt (N : ℝ) := by
  calc
    ∫ p, |p.1 - p.2| ∂(μ.prod ν) ≤
        Real.sqrt (∫ q, (q - qStar) ^ 2 ∂μ) +
          Real.sqrt (∫ q, (q - qStar) ^ 2 ∂ν) :=
      integral_abs_fst_sub_snd_prod_le_add_sqrt_integral_sq
        μ ν qStar hμsq hνsq
    _ ≤ Real.sqrt (C₁ / (N : ℝ)) +
        Real.sqrt (C₂ / (N : ℝ)) :=
      add_le_add (Real.sqrt_le_sqrt hμbound) (Real.sqrt_le_sqrt hνbound)
    _ = (Real.sqrt C₁ + Real.sqrt C₂) / Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_div hC₁, Real.sqrt_div hC₂, add_div]

/-- Product-law distance can be estimated around two different centers,
paying the deterministic distance between those centers. -/
lemma integral_abs_fst_sub_snd_prod_le_sqrt_add_abs_add_sqrt
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b : ℝ)
    (hμsq : Integrable (fun q => (q - a) ^ 2) μ)
    (hνsq : Integrable (fun q => (q - b) ^ 2) ν) :
    ∫ p, |p.1 - p.2| ∂(μ.prod ν) ≤
      Real.sqrt (∫ q, (q - a) ^ 2 ∂μ) + |a - b| +
        Real.sqrt (∫ q, (q - b) ^ 2 ∂ν) := by
  have hμmem :
      MemLp (fun q : ℝ => q - a) 2 μ :=
    (memLp_two_iff_integrable_sq
      (measurable_id.sub measurable_const).aestronglyMeasurable).2 hμsq
  have hνmem :
      MemLp (fun q : ℝ => q - b) 2 ν :=
    (memLp_two_iff_integrable_sq
      (measurable_id.sub measurable_const).aestronglyMeasurable).2 hνsq
  have hμabs : Integrable (fun q : ℝ => |q - a|) μ :=
    (hμmem.integrable (by norm_num)).abs
  have hνabs : Integrable (fun q : ℝ => |q - b|) ν :=
    (hνmem.integrable (by norm_num)).abs
  have hfst :
      Integrable (fun p : ℝ × ℝ => |p.1 - a|) (μ.prod ν) :=
    hμabs.comp_fst ν
  have hsnd :
      Integrable (fun p : ℝ × ℝ => |p.2 - b|) (μ.prod ν) :=
    hνabs.comp_snd μ
  have hconst :
      Integrable (fun _ : ℝ × ℝ => |a - b|) (μ.prod ν) :=
    integrable_const _
  have hmajor :
      Integrable
        (fun p : ℝ × ℝ => |p.1 - a| + |a - b| + |p.2 - b|)
        (μ.prod ν) :=
    (hfst.add hconst).add hsnd
  have hpoint (p : ℝ × ℝ) :
      |p.1 - p.2| ≤ |p.1 - a| + |a - b| + |p.2 - b| := by
    calc
      |p.1 - p.2| =
          |(p.1 - a) + (a - b) + (b - p.2)| := by
        congr 1
        ring
      _ ≤ |(p.1 - a) + (a - b)| + |b - p.2| := abs_add_le _ _
      _ ≤ |p.1 - a| + |a - b| + |b - p.2| := by
        gcongr
        exact abs_add_le _ _
      _ = |p.1 - a| + |a - b| + |p.2 - b| := by
        rw [abs_sub_comm b p.2]
  have hdist :
      Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) (μ.prod ν) := by
    refine hmajor.mono'
      (measurable_fst.sub measurable_snd).abs.aestronglyMeasurable ?_
    filter_upwards with p
    simpa only [Real.norm_eq_abs, abs_abs,
      abs_of_nonneg
        (add_nonneg
          (add_nonneg (abs_nonneg (p.1 - a)) (abs_nonneg (a - b)))
          (abs_nonneg (p.2 - b)))] using hpoint p
  calc
    ∫ p, |p.1 - p.2| ∂(μ.prod ν) ≤
        ∫ p, (|p.1 - a| + |a - b| + |p.2 - b|) ∂(μ.prod ν) :=
      integral_mono_ae hdist hmajor (Filter.Eventually.of_forall hpoint)
    _ = (∫ q, |q - a| ∂μ) + |a - b| + ∫ q, |q - b| ∂ν := by
      have houter :
          (∫ p, (|p.1 - a| + |a - b| + |p.2 - b|) ∂(μ.prod ν)) =
            (∫ p, (|p.1 - a| + |a - b|) ∂(μ.prod ν)) +
              ∫ p, |p.2 - b| ∂(μ.prod ν) :=
        integral_add (hfst.add hconst) hsnd
      have hinner :
          (∫ p, (|p.1 - a| + |a - b|) ∂(μ.prod ν)) =
            (∫ p, |p.1 - a| ∂(μ.prod ν)) +
              ∫ _p : ℝ × ℝ, |a - b| ∂(μ.prod ν) :=
        integral_add hfst hconst
      rw [houter, hinner]
      have hleft := integral_fun_fst
        (μ := μ) (ν := ν) (fun q : ℝ => |q - a|)
      have hright := integral_fun_snd
        (μ := μ) (ν := ν) (fun q : ℝ => |q - b|)
      rw [hleft, hright]
      simp only [integral_const, probReal_univ, one_smul]
    _ ≤ Real.sqrt (∫ q, (q - a) ^ 2 ∂μ) + |a - b| +
        Real.sqrt (∫ q, (q - b) ^ 2 ∂ν) := by
      gcongr
      · exact integral_abs_sub_le_sqrt_integral_sq μ a hμsq
      · exact integral_abs_sub_le_sqrt_integral_sq ν b hνsq

/-- Inverse-dimension moment bounds at two centers, together with an
inverse-square-root bound between the centers, control product-law distance
at the same inverse-square-root scale. -/
lemma
    integral_abs_fst_sub_snd_prod_le_sqrt_add_const_add_sqrt_div_sqrt_nat
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b : ℝ) {C₀ C₁ C₂ : ℝ} {N : ℕ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hμsq : Integrable (fun q => (q - a) ^ 2) μ)
    (hνsq : Integrable (fun q => (q - b) ^ 2) ν)
    (hμbound :
      (∫ q, (q - a) ^ 2 ∂μ) ≤ C₁ / (N : ℝ))
    (hνbound :
      (∫ q, (q - b) ^ 2 ∂ν) ≤ C₂ / (N : ℝ))
    (hcenters : |a - b| ≤ C₀ / Real.sqrt (N : ℝ)) :
    ∫ p, |p.1 - p.2| ∂(μ.prod ν) ≤
      (Real.sqrt C₁ + C₀ + Real.sqrt C₂) /
        Real.sqrt (N : ℝ) := by
  calc
    ∫ p, |p.1 - p.2| ∂(μ.prod ν) ≤
        Real.sqrt (∫ q, (q - a) ^ 2 ∂μ) + |a - b| +
          Real.sqrt (∫ q, (q - b) ^ 2 ∂ν) :=
      integral_abs_fst_sub_snd_prod_le_sqrt_add_abs_add_sqrt
        μ ν a b hμsq hνsq
    _ ≤ Real.sqrt (C₁ / (N : ℝ)) +
        C₀ / Real.sqrt (N : ℝ) +
          Real.sqrt (C₂ / (N : ℝ)) :=
      add_le_add
        (add_le_add (Real.sqrt_le_sqrt hμbound) hcenters)
        (Real.sqrt_le_sqrt hνbound)
    _ = (Real.sqrt C₁ + C₀ + Real.sqrt C₂) /
        Real.sqrt (N : ℝ) := by
      rw [Real.sqrt_div hC₁, Real.sqrt_div hC₂]
      ring

/-- A path-law second moment transfers to its fixed-time marginal before
forming the independent product with a second probability law. -/
lemma
    integral_abs_fst_sub_snd_map_eval_prod_le_sqrt_add_const_add_sqrt_div_sqrt_nat
    (ρ : Measure (ℕ → ℝ)) [IsProbabilityMeasure ρ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (t : ℕ) (a b : ℝ) {C₀ C₁ C₂ : ℝ} {N : ℕ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hρsq : Integrable (fun ω => (ω t - a) ^ 2) ρ)
    (hνsq : Integrable (fun q => (q - b) ^ 2) ν)
    (hρbound :
      (∫ ω, (ω t - a) ^ 2 ∂ρ) ≤ C₁ / (N : ℝ))
    (hνbound :
      (∫ q, (q - b) ^ 2 ∂ν) ≤ C₂ / (N : ℝ))
    (hcenters : |a - b| ≤ C₀ / Real.sqrt (N : ℝ)) :
    ∫ p, |p.1 - p.2|
        ∂((ρ.map (fun ω => ω t)).prod ν) ≤
      (Real.sqrt C₁ + C₀ + Real.sqrt C₂) /
        Real.sqrt (N : ℝ) := by
  let μ : Measure ℝ := ρ.map (fun ω => ω t)
  have heval : AEMeasurable (fun ω : ℕ → ℝ => ω t) ρ :=
    (measurable_pi_apply t).aemeasurable
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    exact Measure.isProbabilityMeasure_map heval
  have hμmeas :
      AEStronglyMeasurable (fun q : ℝ => (q - a) ^ 2) μ :=
    ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable
  have hμsq :
      Integrable (fun q : ℝ => (q - a) ^ 2) μ := by
    apply (integrable_map_measure hμmeas heval).2
    change Integrable (fun ω => (ω t - a) ^ 2) ρ
    exact hρsq
  have hμeq :
      (∫ q, (q - a) ^ 2 ∂μ) =
        ∫ ω, (ω t - a) ^ 2 ∂ρ := by
    dsimp only [μ]
    exact integral_map heval hμmeas
  have hμbound :
      (∫ q, (q - a) ^ 2 ∂μ) ≤ C₁ / (N : ℝ) := by
    rw [hμeq]
    exact hρbound
  simpa only [μ] using
    integral_abs_fst_sub_snd_prod_le_sqrt_add_const_add_sqrt_div_sqrt_nat
      μ ν a b hC₁ hC₂ hμsq hνsq hμbound hνbound hcenters

/-- The eventual dynamic orbit-moment estimate controls the evolving
fixed-time marginal's contribution to the independent block-start distance.
The stationary moment and deterministic center separation remain explicit
inputs for the subsequent invariant-law specialization. -/
lemma eventually_integral_abs_fst_sub_snd_blockStart_prod_le_inv_sqrt_nat
    {A qStar R κ η δ C C₀ C₂ : ℝ}
    (hA : A ≠ 0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hC₂ : 0 ≤ C₂)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (q : ℕ → ℝ) (t T : ℕ → ℕ)
    (hq :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1)
    (htT :
      ∀ᶠ N : ℕ in Filter.atTop,
        t N ≤ T N)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ s ≤ T N,
          |(V A)^[s] (q N) - qStar| ≤ R - η)
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ))
    (hcenters :
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[t N] (q N) - qStar| ≤
          C₀ / Real.sqrt (N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∫ p, |p.1 - p.2|
          ∂((markovPathMeasure (Measure.dirac (q N)) (Kchain A N)).map
              (fun ω => ω (t N))).prod (ν N : Measure ℝ) ≤
        (Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
            C₀ + Real.sqrt C₂) /
          Real.sqrt (N : ℝ) := by
  have hκsq : κ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hκ0 zero_le_one).2 hκ1
  have hCdynamic :
      0 ≤ (1 / 4) / (1 - κ ^ 2) + 2 * C :=
    add_nonneg
      (div_nonneg (by norm_num) (sub_nonneg.mpr hκsq.le))
      (mul_nonneg (by norm_num) hC)
  have hdynamic :=
    eventually_integral_sq_eval_sub_V_iterate_le_inv_nat
      hA hκ0 hκ1 hη0 hδ hC hRinterior hderiv hbuffer
      q t T hq htT hT horbit
  filter_upwards
      [hdynamic, hνsq, hνbound, hcenters, hq,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hdynamicN hνsqN hνboundN hcentersN hqN hN
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  let ρ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac (q N)) (Kchain A N)
  haveI : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    infer_instance
  have hρsq :
      Integrable
        (fun ω : ℕ → ℝ =>
          (ω (t N) - (V A)^[t N] (q N)) ^ 2) ρ := by
    apply integrable_sq_sub_of_ae_mem_Icc ρ
      (fun ω : ℕ → ℝ => ω (t N)) ((V A)^[t N] (q N))
    · exact
        (((measurable_pi_apply (t N)).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · simpa only [ρ] using
        markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
          hqN hNpos (t N)
  simpa only [ρ] using
    integral_abs_fst_sub_snd_map_eval_prod_le_sqrt_add_const_add_sqrt_div_sqrt_nat
      ρ (ν N : Measure ℝ) (t N) ((V A)^[t N] (q N)) qStar
      hCdynamic hC₂ hρsq hνsqN hdynamicN hνboundN hcentersN

/-- The per-dimension invariant measures with inverse-dimension fixed-point
moment can be selected as one family carrying the full eventual package. -/
theorem
    exists_eventually_invariant_Kchain_family_integral_sq_sub_fixed_le_inv_nat
    {A qStar : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ R η C : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ) := by
  obtain ⟨κ, R, η, C, N₀, hκ0, hκ1, hη0, hηR,
      hRinterior, hC, hderiv, hselect⟩ :=
    exists_eventually_invariant_Kchain_integral_sq_sub_fixed_le_inv_nat
      hA hqStar hfix
  let ν : ℕ → ProbabilityMeasure ℝ := fun N =>
    if hN : N₀ ≤ N then
      Classical.choose (hselect N hN)
    else
      diracProba qStar
  have hνspec (N : ℕ) (hN : N₀ ≤ N) :
      Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
      (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
      (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
      (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
        C / (N : ℝ) := by
    dsimp only [ν]
    rw [dif_pos hN]
    exact Classical.choose_spec (hselect N hN)
  refine ⟨κ, R, η, C, ν, hκ0, hκ1, hη0, hηR,
    hRinterior, hC, hderiv, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
  obtain ⟨hν, hνsupport, hνzero, hνbound⟩ := hνspec N hN
  refine ⟨hν, hνsupport, hνzero, ?_, hνbound⟩
  apply integrable_sq_sub_of_ae_mem_Icc
    (ν N : Measure ℝ) (fun q : ℝ => q) qStar
  · exact
      ((measurable_id.sub measurable_const).pow_const 2)
        |>.aestronglyMeasurable
  · rw [ae_iff]
    change (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0
    exact hνsupport

/-- The selected stationary family can be inserted directly into the
dynamic block-start estimate, with only the deterministic orbit hypotheses
left to be supplied by the cutoff-time choice. -/
theorem
    exists_stationary_family_eventually_blockStart_prod_le_inv_sqrt_nat
    {A qStar : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ R η C₂ : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C₂ ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ)) ∧
      ∀ {δ C C₀ : ℝ},
        0 < δ →
        0 ≤ C →
        δ + κ * η ≤ η →
        ∀ (q : ℕ → ℝ) (t T : ℕ → ℕ),
          (∀ᶠ N : ℕ in Filter.atTop,
            q N ∈ Set.Icc (0 : ℝ) 1) →
          (∀ᶠ N : ℕ in Filter.atTop, t N ≤ T N) →
          (∀ᶠ N : ℕ in Filter.atTop,
            (T N : ℝ) ≤ C * (N : ℝ)) →
          (∀ᶠ N : ℕ in Filter.atTop,
            ∀ s ≤ T N,
              |(V A)^[s] (q N) - qStar| ≤ R - η) →
          (∀ᶠ N : ℕ in Filter.atTop,
            |(V A)^[t N] (q N) - qStar| ≤
              C₀ / Real.sqrt (N : ℝ)) →
          ∀ᶠ N : ℕ in Filter.atTop,
            ∫ p, |p.1 - p.2|
                ∂((markovPathMeasure
                    (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω => ω (t N))).prod (ν N : Measure ℝ) ≤
              (Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
                  C₀ + Real.sqrt C₂) /
                Real.sqrt (N : ℝ) := by
  obtain ⟨κ, R, η, C₂, ν, hκ0, hκ1, hη0, hηR,
      hRinterior, hC₂, hderiv, hν⟩ :=
    exists_eventually_invariant_Kchain_family_integral_sq_sub_fixed_le_inv_nat
      hA hqStar hfix
  refine ⟨κ, R, η, C₂, ν, hκ0, hκ1, hη0, hηR,
    hRinterior, hC₂, hderiv, hν, ?_⟩
  intro δ C C₀ hδ hC hbuffer q t T hq htT hT horbit hcenters
  have hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) := by
    filter_upwards [hν] with N hνN
    exact hνN.2.2.2.1
  have hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ) := by
    filter_upwards [hν] with N hνN
    exact hνN.2.2.2.2
  exact
    eventually_integral_abs_fst_sub_snd_blockStart_prod_le_inv_sqrt_nat
      (ne_of_gt (zero_lt_one.trans hA)) hκ0 hκ1 hη0.le hδ hC hC₂.le
      hRinterior hderiv hbuffer q t T hq htT hT horbit
      ν hνsq hνbound hcenters

/-- A centered second moment controls the probability of leaving the
corresponding interval. -/
lemma measureReal_abs_sub_gt_le_integral_sq_div
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (qStar : ℝ) {R : ℝ}
    (hR : 0 < R)
    (hsq : Integrable (fun q => (q - qStar) ^ 2) μ) :
    μ.real {q : ℝ | R < |q - qStar|} ≤
      (∫ q, (q - qStar) ^ 2 ∂μ) / R ^ 2 := by
  have hnonneg :
      0 ≤ᵐ[μ] fun q : ℝ => (q - qStar) ^ 2 :=
    Filter.Eventually.of_forall fun q => sq_nonneg (q - qStar)
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg hnonneg hsq (R ^ 2)
  have hsubset :
      {q : ℝ | R < |q - qStar|} ⊆
        {q : ℝ | R ^ 2 ≤ (q - qStar) ^ 2} := by
    intro q hq
    change R ^ 2 ≤ (q - qStar) ^ 2
    simpa only [sq_abs] using
      ((sq_lt_sq₀ hR.le (abs_nonneg (q - qStar))).2 hq).le
  have hmul :
      R ^ 2 * μ.real {q : ℝ | R < |q - qStar|} ≤
        ∫ q, (q - qStar) ^ 2 ∂μ :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
      (sq_nonneg R)).trans hmarkov
  calc
    μ.real {q : ℝ | R < |q - qStar|} =
        (R ^ 2 * μ.real {q : ℝ | R < |q - qStar|}) / R ^ 2 := by
      field_simp [hR.ne']
    _ ≤ (∫ q, (q - qStar) ^ 2 ∂μ) / R ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 hmul

/-- An inverse-dimension centered second-moment envelope gives an
inverse-dimension stable-interval escape bound. -/
lemma measureReal_abs_sub_gt_le_div_sq_div_nat
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (qStar : ℝ) {R C : ℝ}
    {N : ℕ} (hR : 0 < R)
    (hsq : Integrable (fun q => (q - qStar) ^ 2) μ)
    (hbound :
      (∫ q, (q - qStar) ^ 2 ∂μ) ≤ C / (N : ℝ)) :
    μ.real {q : ℝ | R < |q - qStar|} ≤
      (C / R ^ 2) / (N : ℝ) := by
  calc
    μ.real {q : ℝ | R < |q - qStar|} ≤
        (∫ q, (q - qStar) ^ 2 ∂μ) / R ^ 2 :=
      measureReal_abs_sub_gt_le_integral_sq_div μ qStar hR hsq
    _ ≤ (C / (N : ℝ)) / R ^ 2 :=
      div_le_div_of_nonneg_right hbound (sq_nonneg R)
    _ = (C / R ^ 2) / (N : ℝ) := by ring

/-- A canonical Markov path started from an invariant probability measure
has that same measure as every fixed-time marginal. -/
lemma markovPathMeasure_map_eval_eq_of_invariant
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (κ : Kernel E E) [IsMarkovKernel κ]
    (hν : Kernel.Invariant κ ν) (t : ℕ) :
    (markovPathMeasure ν κ).map (fun ω => ω t) = ν := by
  induction t with
  | zero =>
      exact markovPathMeasure_map_zero ν κ
  | succ t ih =>
      rw [markovPathMeasure_map_eval_succ, ih, hν.def]

/-- The probability of any measurable fixed-time event under an
invariant-start path equals its probability under the invariant law. -/
lemma markovPathMeasure_measureReal_eval_mem_eq_of_invariant
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (κ : Kernel E E) [IsMarkovKernel κ]
    (hν : Kernel.Invariant κ ν) (t : ℕ)
    (S : Set E) (hS : MeasurableSet S) :
    (markovPathMeasure ν κ).real {ω : ℕ → E | ω t ∈ S} =
      ν.real S := by
  change
    (markovPathMeasure ν κ).real ((fun ω : ℕ → E => ω t) ⁻¹' S) =
      ν.real S
  calc
    (markovPathMeasure ν κ).real ((fun ω : ℕ → E => ω t) ⁻¹' S) =
        ((markovPathMeasure ν κ).map (fun ω => ω t)).real S :=
      (map_measureReal_apply (measurable_pi_apply t) hS).symm
    _ = ν.real S := by
      rw [markovPathMeasure_map_eval_eq_of_invariant ν κ hν t]

/-- An invariant centered-moment bound localizes every fixed-time
coordinate of the stationary canonical path with the same constant. -/
lemma
    markovPathMeasure_measureReal_abs_eval_sub_gt_le_div_sq_div_nat
    {A qStar R C : ℝ} {N : ℕ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν)
    (hR : 0 < R)
    (hsq : Integrable (fun q => (q - qStar) ^ 2) ν)
    (hbound :
      (∫ q, (q - qStar) ^ 2 ∂ν) ≤ C / (N : ℝ))
    (t : ℕ) :
    (markovPathMeasure ν (Kchain A N)).real
        {ω : ℕ → ℝ | R < |ω t - qStar|} ≤
      (C / R ^ 2) / (N : ℝ) := by
  let S : Set ℝ := {q : ℝ | R < |q - qStar|}
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_lt measurable_const
      ((measurable_id.sub measurable_const).abs)
  calc
    (markovPathMeasure ν (Kchain A N)).real
          {ω : ℕ → ℝ | R < |ω t - qStar|} =
        ν.real S := by
      change
        (markovPathMeasure ν (Kchain A N)).real
            {ω : ℕ → ℝ | ω t ∈ S} = ν.real S
      exact markovPathMeasure_measureReal_eval_mem_eq_of_invariant
        ν (Kchain A N) hν t S hS
    _ ≤ (C / R ^ 2) / (N : ℝ) :=
      measureReal_abs_sub_gt_le_div_sq_div_nat
        ν qStar hR hsq hbound

/-- Eventual invariant moment control for a dimension-indexed family gives
a localization estimate uniform over every stationary path time. -/
lemma
    eventually_forall_markovPathMeasure_measureReal_abs_eval_sub_gt_le_div_sq_div_nat
    {A qStar R C : ℝ} (hR : 0 < R)
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
    ∀ᶠ N : ℕ in Filter.atTop, ∀ t : ℕ,
      (markovPathMeasure (ν N : Measure ℝ) (Kchain A N)).real
          {ω : ℕ → ℝ | R < |ω t - qStar|} ≤
        (C / R ^ 2) / (N : ℝ) := by
  filter_upwards [hνinv, hνsq, hνbound] with
      N hνinvN hνsqN hνboundN
  intro t
  exact
    markovPathMeasure_measureReal_abs_eval_sub_gt_le_div_sq_div_nat
      (ν N : Measure ℝ) hνinvN hR hνsqN hνboundN t

/-- Restarting a canonical Markov path from its time-`s` marginal and
running for `t` further steps gives the original time-`s+t` marginal. -/
lemma markovPathMeasure_map_eval_of_map_eval
    {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (κ : Kernel E E) [IsMarkovKernel κ] (s t : ℕ) :
    (markovPathMeasure
        ((markovPathMeasure μ κ).map (fun ω => ω s)) κ).map
        (fun ω => ω t) =
      (markovPathMeasure μ κ).map (fun ω => ω (s + t)) := by
  haveI :
      IsProbabilityMeasure
        ((markovPathMeasure μ κ).map (fun ω => ω s)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply s).aemeasurable
  induction t with
  | zero =>
      simpa using
        markovPathMeasure_map_zero
          ((markovPathMeasure μ κ).map (fun ω => ω s)) κ
  | succ t ih =>
      rw [markovPathMeasure_map_eval_succ, ih]
      simpa only [Nat.add_assoc] using
        (markovPathMeasure_map_eval_succ μ κ (s + t)).symm

/-- The measurable fixed-time events of a path restarted at time `s`
coincide with the corresponding original-path events at time `s+t`. -/
lemma markovPathMeasure_measureReal_eval_mem_of_map_eval
    {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (κ : Kernel E E) [IsMarkovKernel κ] (s t : ℕ)
    (S : Set E) (hS : MeasurableSet S) :
    (markovPathMeasure
        ((markovPathMeasure μ κ).map (fun ω => ω s)) κ).real
        {ω : ℕ → E | ω t ∈ S} =
      (markovPathMeasure μ κ).real
        {ω : ℕ → E | ω (s + t) ∈ S} := by
  haveI :
      IsProbabilityMeasure
        ((markovPathMeasure μ κ).map (fun ω => ω s)) :=
    Measure.isProbabilityMeasure_map (measurable_pi_apply s).aemeasurable
  change
    (markovPathMeasure
        ((markovPathMeasure μ κ).map (fun ω => ω s)) κ).real
        ((fun ω : ℕ → E => ω t) ⁻¹' S) =
      (markovPathMeasure μ κ).real
        ((fun ω : ℕ → E => ω (s + t)) ⁻¹' S)
  calc
    (markovPathMeasure
        ((markovPathMeasure μ κ).map (fun ω => ω s)) κ).real
          ((fun ω : ℕ → E => ω t) ⁻¹' S) =
        ((markovPathMeasure
          ((markovPathMeasure μ κ).map (fun ω => ω s)) κ).map
            (fun ω => ω t)).real S :=
      (map_measureReal_apply (measurable_pi_apply t) hS).symm
    _ = ((markovPathMeasure μ κ).map
          (fun ω => ω (s + t))).real S := by
      rw [markovPathMeasure_map_eval_of_map_eval μ κ s t]
    _ = (markovPathMeasure μ κ).real
        ((fun ω : ℕ → E => ω (s + t)) ⁻¹' S) :=
      map_measureReal_apply (measurable_pi_apply (s + t)) hS

/-- The fixed-time probability of leaving the stable interval is bounded by
the existing finite-horizon exit estimate. -/
lemma markovPathMeasure_measureReal_eval_not_mem_stableInterval_le_exp
    {A q qStar R κ η δ : ℝ} {N T t : ℕ}
    (hA : A ≠ 0) (hN : 0 < N)
    (hκ0 : 0 ≤ κ) (hη0 : 0 ≤ η) (hδ : 0 < δ) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (horbit :
      ∀ s ≤ T, |(V A)^[s] q - qStar| ≤ R - η)
    (htT : t ≤ T) :
    (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
        {ω : ℕ → ℝ |
          ω t ∉ Set.Icc (qStar - R) (qStar + R)} ≤
      2 * T * Real.exp (-2 * N * δ ^ 2) := by
  have hsubset :
      {ω : ℕ → ℝ |
          ω t ∉ Set.Icc (qStar - R) (qStar + R)} ⊆
        {ω : ℕ → ℝ |
          stableIntervalExitTime qStar R T ω ≤ T} := by
    intro ω hbad
    change stableIntervalExitTime qStar R T ω ≤ T
    by_contra hnot
    have hTlt :
        T < stableIntervalExitTime qStar R T ω :=
      Nat.lt_of_not_ge hnot
    have htlt :
        t < stableIntervalExitTime qStar R T ω :=
      htT.trans_lt hTlt
    exact hbad
      (eval_mem_stableInterval_of_lt_stableIntervalExitTime htT htlt)
  exact
    (measureReal_mono hsubset).trans
      (markovPathMeasure_measureReal_stableIntervalExitTime_le
        hA hN hκ0 hη0 hδ hRq hderiv hbuffer horbit)

/-- For linearly bounded varying horizons, dynamic stable-interval
localization is eventually uniform in time at inverse-dimension scale. -/
lemma
    eventually_forall_markovPathMeasure_measureReal_eval_not_mem_stableInterval_le_inv_nat
    {A qStar R κ η δ C : ℝ}
    (hA : A ≠ 0)
    (hκ0 : 0 ≤ κ) (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (q : ℕ → ℝ) (T : ℕ → ℕ)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ s ≤ T N,
          |(V A)^[s] (q N) - qStar| ≤ R - η) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ t ≤ T N,
      (markovPathMeasure (Measure.dirac (q N)) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω t ∉ Set.Icc (qStar - R) (qStar + R)} ≤
        2 * C / (N : ℝ) := by
  have hc : 0 < 2 * δ ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hδ)
  have hdecay :=
    eventually_two_nat_horizon_mul_exp_neg_le_mul_inv_nat
      hC hc hT
  filter_upwards
      [hdecay, horbit, Filter.eventually_ge_atTop (1 : ℕ)] with
      N hdecayN horbitN hN
  intro t htT
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  calc
    (markovPathMeasure (Measure.dirac (q N)) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω t ∉ Set.Icc (qStar - R) (qStar + R)} ≤
        2 * (T N : ℝ) * Real.exp (-2 * N * δ ^ 2) :=
      markovPathMeasure_measureReal_eval_not_mem_stableInterval_le_exp
        hA hNpos hκ0 hη0 hδ hRq hderiv hbuffer horbitN htT
    _ = 2 * (T N : ℝ) *
        Real.exp (-(2 * δ ^ 2) * (N : ℝ)) := by
      congr 2
      ring
    _ ≤ 2 * C / (N : ℝ) := hdecayN

/-- Uniform dynamic localization transfers to a fresh terminal-block path
started from the original path's block-start marginal. -/
lemma
    eventually_forall_markovPathMeasure_shifted_measureReal_eval_not_mem_stableInterval_le_inv_nat
    {A qStar R κ η δ C : ℝ}
    (hA : A ≠ 0)
    (hκ0 : 0 ≤ κ) (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (q : ℕ → ℝ) (T s ℓ : ℕ → ℕ)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u ≤ T N,
          |(V A)^[u] (q N) - qStar| ≤ R - η)
    (hblock :
      ∀ᶠ N : ℕ in Filter.atTop,
        s N + ℓ N ≤ T N) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ u < ℓ N,
      (markovPathMeasure
          ((markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω => ω (s N)))
          (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc (qStar - R) (qStar + R)} ≤
        2 * C / (N : ℝ) := by
  have hdynamic :=
    eventually_forall_markovPathMeasure_measureReal_eval_not_mem_stableInterval_le_inv_nat
      hA hκ0 hη0 hδ hC hRq hderiv hbuffer q T hT horbit
  filter_upwards [hdynamic, hblock] with N hdynamicN hblockN
  intro u hu
  have htime : s N + u ≤ T N := by omega
  let J : Set ℝ := Set.Icc (qStar - R) (qStar + R)
  have hshift :=
    markovPathMeasure_measureReal_eval_mem_of_map_eval
      (Measure.dirac (q N)) (Kchain A N) (s N) u Jᶜ
      measurableSet_Icc.compl
  calc
    (markovPathMeasure
          ((markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω => ω (s N)))
          (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc (qStar - R) (qStar + R)} =
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω (s N + u) ∉ Set.Icc (qStar - R) (qStar + R)} := by
      simpa only [J, Set.mem_compl_iff] using hshift
    _ ≤ 2 * C / (N : ℝ) := hdynamicN (s N + u) htime

/-- Every fixed-time marginal of a supported Dirac-start scalar path is
supported on `[0,1]`. -/
lemma markovPathMeasure_dirac_map_eval_apply_compl_Icc_eq_zero
    {A q : ℝ} {N : ℕ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hN : 0 < N) (t : ℕ) :
    ((markovPathMeasure (Measure.dirac q) (Kchain A N)).map
        (fun ω => ω t)) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  rw [Measure.map_apply (measurable_pi_apply t) measurableSet_Icc.compl]
  have hsupp :=
    markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc (A := A) hq hN t
  rw [ae_iff] at hsupp
  exact hsupp

/-- An evolving fixed-time marginal paired independently with a supported
stationary law satisfies the arbitrary-law terminal contraction estimate as
soon as the two scalar path localizations are available. -/
lemma
    integral_abs_fst_sub_snd_eval_blockStart_prod_le_pow_mul_add_of_localization
    {A q qStar R κ B₁ B₂ : ℝ} {N s ℓ : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνsupport : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hbad₁ : ∀ u < ℓ,
      (markovPathMeasure
          ((markovPathMeasure
            (Measure.dirac q) (Kchain A N)).map (fun ω => ω s))
          (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₁)
    (hbad₂ : ∀ u < ℓ,
      (markovPathMeasure ν (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₂) :
    ∫ ω, |(ω ℓ).1 - (ω ℓ).2|
        ∂(markovPathMeasure
          (((markovPathMeasure
              (Measure.dirac q) (Kchain A N)).map (fun ω => ω s)).prod ν)
          (synchronousKchain A N)) ≤
      κ ^ ℓ *
          (∫ p, |p.1 - p.2|
            ∂((markovPathMeasure
              (Measure.dirac q) (Kchain A N)).map
                (fun ω => ω s)).prod ν) +
        (B₁ + B₂) / (1 - κ) := by
  let μ : Measure ℝ :=
    (markovPathMeasure
      (Measure.dirac q) (Kchain A N)).map (fun ω => ω s)
  let μ₀ : Measure (ℝ × ℝ) := μ.prod ν
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_apply s).aemeasurable
  haveI : IsProbabilityMeasure μ₀ := by
    dsimp only [μ₀]
    infer_instance
  have hμsupport : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    simpa only [μ] using
      markovPathMeasure_dirac_map_eval_apply_compl_Icc_eq_zero
        (A := A) hq hN s
  have hμ₀support :
      μ₀ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    dsimp only [μ₀]
    exact Measure.prod_apply_compl_prod_Icc_eq_zero
      μ ν hμsupport hνsupport
  have hfst : μ₀.map Prod.fst = μ := by
    dsimp only [μ₀]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : μ₀.map Prod.snd = ν := by
    dsimp only [μ₀]
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
  have hbad₁' : ∀ u < ℓ,
      (markovPathMeasure (μ₀.map Prod.fst) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₁ := by
    intro u hu
    rw [hfst]
    simpa only [μ] using hbad₁ u hu
  have hbad₂' : ∀ u < ℓ,
      (markovPathMeasure (μ₀.map Prod.snd) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc (qStar - R) (qStar + R)} ≤ B₂ := by
    intro u hu
    rw [hsnd]
    exact hbad₂ u hu
  simpa only [μ₀, μ] using
    integral_abs_fst_sub_snd_eval_le_pow_mul_add_of_measure_of_scalar_localization
      hA hRq hκ0 hκ1 hB₁ hB₂ hderiv hN μ₀ hμ₀support
      hbad₁' hbad₂'

/-- Eventual dynamic and stationary localization bounds insert directly into
the terminal product-law recursion, while retaining the block-start expected
distance. -/
lemma
    eventually_integral_abs_fst_sub_snd_eval_blockStart_prod_le_pow_mul_add_inv_nat
    {A qStar R κ η δ C C₂ : ℝ}
    (hA : A ≠ 0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hR : 0 < R) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (q : ℕ → ℝ) (T s ℓ : ℕ → ℕ)
    (hq :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u ≤ T N,
          |(V A)^[u] (q N) - qStar| ≤ R - η)
    (hblock :
      ∀ᶠ N : ℕ in Filter.atTop,
        s N + ℓ N ≤ T N)
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ))
    (hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∫ ω, |(ω (ℓ N)).1 - (ω (ℓ N)).2|
          ∂(markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω => ω (s N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)) ≤
        κ ^ ℓ N *
            (∫ p, |p.1 - p.2|
              ∂((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω => ω (s N))).prod (ν N : Measure ℝ)) +
          ((2 * C + C₂ / R ^ 2) / (N : ℝ)) / (1 - κ) := by
  have hdynamic :=
    eventually_forall_markovPathMeasure_shifted_measureReal_eval_not_mem_stableInterval_le_inv_nat
      hA hκ0 hη0 hδ hC hRq hderiv hbuffer q T s ℓ hT horbit hblock
  have hstationary :=
    eventually_forall_markovPathMeasure_measureReal_abs_eval_sub_gt_le_div_sq_div_nat
      hR ν hνinv hνsq hνbound
  filter_upwards
      [hdynamic, hstationary, hq, hνsupport,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hdynamicN hstationaryN hqN hνsupportN hN
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hB₁ : 0 ≤ 2 * C / (N : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hC) (Nat.cast_nonneg N)
  have hB₂ : 0 ≤ (C₂ / R ^ 2) / (N : ℝ) :=
    div_nonneg (div_nonneg hC₂ (sq_nonneg R)) (Nat.cast_nonneg N)
  have hbad₂ : ∀ u < ℓ N,
      (markovPathMeasure (ν N : Measure ℝ) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω u ∉ Set.Icc (qStar - R) (qStar + R)} ≤
        (C₂ / R ^ 2) / (N : ℝ) := by
    intro u _
    have hset :
        {ω : ℕ → ℝ |
            ω u ∉ Set.Icc (qStar - R) (qStar + R)} =
          {ω : ℕ → ℝ | R < |ω u - qStar|} := by
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
    exact hstationaryN u
  have hterminal :=
    integral_abs_fst_sub_snd_eval_blockStart_prod_le_pow_mul_add_of_localization
      hA hRq hκ0 hκ1 hB₁ hB₂ hderiv hNpos hqN
      (ν N : Measure ℝ) hνsupportN hdynamicN hbad₂
  have hnormalize :
      2 * C / (N : ℝ) + (C₂ / R ^ 2) / (N : ℝ) =
        (2 * C + C₂ / R ^ 2) / (N : ℝ) := by
    ring
  rw [hnormalize] at hterminal
  exact hterminal

/-- The inverse-square-root block-start product estimate closes the initial
term in the eventual terminal recursion. -/
lemma
    eventually_integral_abs_fst_sub_snd_eval_blockStart_prod_le_pow_mul_inv_sqrt_add_inv_nat
    {A qStar R κ η δ C C₀ C₂ : ℝ}
    (hA : A ≠ 0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C) (hC₂ : 0 ≤ C₂)
    (hR : 0 < R)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (q : ℕ → ℝ) (T s ℓ : ℕ → ℕ)
    (hq :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ u ≤ T N,
          |(V A)^[u] (q N) - qStar| ≤ R - η)
    (hblock :
      ∀ᶠ N : ℕ in Filter.atTop,
        s N + ℓ N ≤ T N)
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ))
    (hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C₂ / (N : ℝ))
    (hcenters :
      ∀ᶠ N : ℕ in Filter.atTop,
        |(V A)^[s N] (q N) - qStar| ≤
          C₀ / Real.sqrt (N : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∫ ω, |(ω (ℓ N)).1 - (ω (ℓ N)).2|
          ∂(markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω => ω (s N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)) ≤
        κ ^ ℓ N *
            ((Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
                C₀ + Real.sqrt C₂) /
              Real.sqrt (N : ℝ)) +
          ((2 * C + C₂ / R ^ 2) / (N : ℝ)) / (1 - κ) := by
  have hRq : R < qStar :=
    hRinterior.trans_le (min_le_left qStar (1 - qStar))
  have hterminal :=
    eventually_integral_abs_fst_sub_snd_eval_blockStart_prod_le_pow_mul_add_inv_nat
      hA hκ0 hκ1 hη0 hδ hC hC₂ hR hRq hderiv hbuffer
      q T s ℓ hq hT horbit hblock ν hνinv hνsupport hνsq hνbound
  have hsT :
      ∀ᶠ N : ℕ in Filter.atTop,
        s N ≤ T N := by
    filter_upwards [hblock] with N hblockN
    omega
  have hinitial :=
    eventually_integral_abs_fst_sub_snd_blockStart_prod_le_inv_sqrt_nat
      hA hκ0 hκ1 hη0 hδ hC hC₂ hRinterior hderiv hbuffer
      q s T hq hsT hT horbit ν hνsq hνbound hcenters
  filter_upwards [hterminal, hinitial] with N hterminalN hinitialN
  calc
    _ ≤ κ ^ ℓ N *
          (∫ p, |p.1 - p.2|
            ∂((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω => ω (s N))).prod (ν N : Measure ℝ)) +
        ((2 * C + C₂ / R ^ 2) / (N : ℝ)) / (1 - κ) :=
      hterminalN
    _ ≤ κ ^ ℓ N *
          ((Real.sqrt ((1 / 4) / (1 - κ ^ 2) + 2 * C) +
              C₀ + Real.sqrt C₂) /
            Real.sqrt (N : ℝ)) +
        ((2 * C + C₂ / R ^ 2) / (N : ℝ)) / (1 - κ) := by
      gcongr

end AbsorptionCutoff
