/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.ScalarCutoff

/-!
# Scalar cutoff marginal assembly for the supercritical chain

This module continues the scalar cutoff proof after the terminal
score-smoothing profile established in `ScalarCutoff.lean`. It identifies the
two smoothed terminal marginals with the evolving cutoff-time law and the
invariant law.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The first smoothed terminal marginal is the evolving scalar law at the
integer cutoff time. -/
lemma eventually_terminalBlock_smoothed_fst_eq_cutoff_marginal
    {A qStar q₀ b : ℝ} (q : ℕ → ℝ)
    (ν : ℕ → ProbabilityMeasure ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hb : 0 < b) (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Kchain A N ∘ₘ
          ((markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)).map
              (fun ω =>
                ω (supercriticalTerminalBlockLength b N))).map Prod.fst =
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω =>
              ω (supercriticalIntegerCutoffTime A qStar q₀ N c)) := by
  have hend :=
    eventually_supercriticalTerminalBlockStart_add_length_eq_integerCutoffTime_sub_one
      (q₀ := q₀) hA hqStar hfix hb c
  have hcutoffPos :
      ∀ᶠ N : ℕ in Filter.atTop,
        1 ≤ supercriticalIntegerCutoffTime A qStar q₀ N c :=
    (tendsto_supercriticalIntegerCutoffTime_atTop
      (q₀ := q₀) hA hqStar hfix c).eventually
        (Filter.eventually_ge_atTop 1)
  filter_upwards [hend, hcutoffPos] with N hendN hcutoffPosN
  let ρ : Measure ℝ :=
    (markovPathMeasure
      (Measure.dirac (q N)) (Kchain A N)).map
        (fun ω =>
          ω (supercriticalTerminalBlockStart A qStar q₀ c b N))
  let ξ : Measure (ℝ × ℝ) := ρ.prod (ν N : Measure ℝ)
  haveI : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_apply
        (supercriticalTerminalBlockStart A qStar q₀ c b N)).aemeasurable
  haveI : IsProbabilityMeasure ξ := by
    dsimp only [ξ]
    infer_instance
  have hfst : ξ.map Prod.fst = ρ := by
    dsimp only [ξ]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hsync :=
    markovPathMeasure_map_eval_synchronousKchain_map_fst_of_measure
      A N ξ (supercriticalTerminalBlockLength b N)
  calc
    Kchain A N ∘ₘ
          ((markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)).map
              (fun ω =>
                ω (supercriticalTerminalBlockLength b N))).map Prod.fst =
        Kchain A N ∘ₘ
          (markovPathMeasure ρ (Kchain A N)).map
            (fun ω =>
              ω (supercriticalTerminalBlockLength b N)) := by
      simpa only [ξ, ρ, hfst] using congrArg (Kchain A N ∘ₘ ·) hsync
    _ =
        Kchain A N ∘ₘ
          (markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).map
              (fun ω =>
                ω (supercriticalTerminalBlockStart A qStar q₀ c b N +
                  supercriticalTerminalBlockLength b N)) := by
      rw [markovPathMeasure_map_eval_of_map_eval]
    _ =
        Kchain A N ∘ₘ
          (markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).map
              (fun ω =>
                ω (supercriticalIntegerCutoffTime A qStar q₀ N c - 1)) := by
      rw [hendN]
    _ =
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω =>
              ω ((supercriticalIntegerCutoffTime A qStar q₀ N c - 1) + 1)) := by
      symm
      exact
        markovPathMeasure_map_eval_succ
          (Measure.dirac (q N)) (Kchain A N)
            (supercriticalIntegerCutoffTime A qStar q₀ N c - 1)
    _ =
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω =>
              ω (supercriticalIntegerCutoffTime A qStar q₀ N c)) := by
      rw [Nat.sub_add_cancel hcutoffPosN]

/-- The second endpoint marginal of a synchronous path started from a product
with an invariant law remains invariant after the smoothing step. -/
lemma terminalBlock_smoothed_snd_eq_of_invariant
    (A : ℝ) (N : ℕ)
    (ρ ν : Measure ℝ) [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν) (t : ℕ) :
    Kchain A N ∘ₘ
        ((markovPathMeasure (ρ.prod ν) (synchronousKchain A N)).map
          (fun ω => ω t)).map Prod.snd =
      ν := by
  have hsync :=
    markovPathMeasure_map_eval_synchronousKchain_map_snd_of_measure
      A N (ρ.prod ν) t
  have hsnd : (ρ.prod ν).map Prod.snd = ν := by
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
  rw [hsnd] at hsync
  rw [hsync, markovPathMeasure_map_eval_eq_of_invariant ν (Kchain A N) hν t,
    hν.def]

/-- The evolving scalar law at the integer cutoff time satisfies the
paper-facing upper cutoff profile against an invariant family. -/
theorem
    exists_eventually_tvDist_cutoff_marginal_invariant_le_rpow_add_of_tendsto
    {A qStar q₀ b C₂ : ℝ} (q : ℕ → ℝ)
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
    ∃ D : ℝ, 0 < D ∧ ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ N : ℕ in Filter.atTop,
        tvDist
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalIntegerCutoffTime A qStar q₀ N c)))
            (ν N : Measure ℝ) ≤
          D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨D, hD, hsmooth⟩ :=
    exists_eventually_terminalBlock_smoothed_tvDist_le_rpow_add_of_tendsto
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hC₂ hνsupport hνinv hνsq hνbound
  have hfst :=
    eventually_terminalBlock_smoothed_fst_eq_cutoff_marginal
      (q₀ := q₀) q ν hA hqStar hfix hb c
  refine ⟨D, hD, ?_⟩
  intro ζ hζ
  have hsmoothSlack := hsmooth ζ hζ
  filter_upwards [hsmoothSlack, hfst, hνinv] with
      N hsmoothN hfstN hνinvN
  let ρ : Measure ℝ :=
    (markovPathMeasure
      (Measure.dirac (q N)) (Kchain A N)).map
        (fun ω =>
          ω (supercriticalTerminalBlockStart A qStar q₀ c b N))
  haveI : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_apply
        (supercriticalTerminalBlockStart A qStar q₀ c b N)).aemeasurable
  have hsnd :=
    terminalBlock_smoothed_snd_eq_of_invariant
      A N ρ (ν N : Measure ℝ) hνinvN
        (supercriticalTerminalBlockLength b N)
  have hsnd' :
      Kchain A N ∘ₘ
          ((markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)).map
              (fun ω =>
                ω (supercriticalTerminalBlockLength b N))).map Prod.snd =
        (ν N : Measure ℝ) := by
    simpa only [ρ] using hsnd
  rw [hfstN, hsnd'] at hsmoothN
  exact hsmoothN

/-- One stationary scalar family can be selected together with the complete
paper-facing upper cutoff profile. -/
theorem
    exists_stationary_family_eventually_tvDist_cutoff_marginal_le_rpow_add_of_tendsto
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
    ∃ C D : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < D ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      ∀ ζ : ℝ, 0 < ζ →
        ∀ᶠ N : ℕ in Filter.atTop,
          tvDist
              ((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalIntegerCutoffTime A qStar q₀ N c)))
              (ν N : Measure ℝ) ≤
            D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨κ, R, η, C, ν, hκ0, hκ1, hη0, hηR,
      hRinterior, hC, hderiv, hν⟩ :=
    exists_eventually_invariant_Kchain_family_integral_sq_sub_fixed_le_inv_nat
      hA hqStar hfix
  have hνinv :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) :=
    hν.mono fun _ hνN => hνN.1
  have hνsupport :
      ∀ᶠ N : ℕ in Filter.atTop,
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
    hν.mono fun _ hνN => hνN.2.1
  have hνsq :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) :=
    hν.mono fun _ hνN => hνN.2.2.2.1
  have hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ) :=
    hν.mono fun _ hνN => hνN.2.2.2.2
  obtain ⟨D, hD, hupper⟩ :=
    exists_eventually_tvDist_cutoff_marginal_invariant_le_rpow_add_of_tendsto
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
      hC.le hνsupport hνinv hνsq hνbound
  exact ⟨C, D, ν, hC, hD, hν, hupper⟩

/-- The vector-chain upper TV bracket can be written against the canonical
scalar path marginal at the preceding time. -/
lemma tvDist_Pkernel_pow_succ_le_markovPathMeasure_radius_marginal
    (A : ℝ) (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x : Fin N → ℝ) (t : ℕ) :
    tvDist
        (((Pkernel A N) ^ (t + 1)) x)
        ((Jkernel A N) ∘ₘ ν) ≤
      tvDist
        ((markovPathMeasure
          (Measure.dirac (radiusSq N x)) (Kchain A N)).map
            (fun ω => ω t))
        ν := by
  calc
    tvDist
          (((Pkernel A N) ^ (t + 1)) x)
          ((Jkernel A N) ∘ₘ ν) ≤
        tvDist (((Kchain A N) ^ t) (radiusSq N x)) ν :=
      tvDist_Pkernel_pow_succ_le_Kchain_pow A N ν x t
    _ =
        tvDist
          ((markovPathMeasure
            (Measure.dirac (radiusSq N x)) (Kchain A N)).map
              (fun ω => ω t))
          ν := by
      rw [markovPathMeasure_dirac_map_eval]

/-- A convergent sequence of vector radii admits a reconstructed invariant
vector family with the successor-time upper cutoff profile. -/
theorem
    exists_reconstructed_invariant_vector_family_eventually_tvDist_cutoff_succ_le_rpow_add
    {A qStar q₀ b : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀))
    (hradiusMem :
      ∀ᶠ N : ℕ in Filter.atTop,
        radiusSq N (x N) ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (c : ℝ) :
    ∃ C D : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < D ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N)
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ∧
          ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
              ({0} : Set (Fin N → ℝ)) = 0) ∧
      ∀ ζ : ℝ, 0 < ζ →
        ∀ᶠ N : ℕ in Filter.atTop,
          tvDist
              (((Pkernel A N) ^
                (supercriticalIntegerCutoffTime A qStar q₀ N c + 1))
                (x N))
              ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ≤
            D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨C, D, ν, hC, hD, hν, hscalar⟩ :=
    exists_stationary_family_eventually_tvDist_cutoff_marginal_le_rpow_add_of_tendsto
      (fun N : ℕ => radiusSq N (x N))
      hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb c
  have hvector :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N)
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ∧
          ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
              ({0} : Set (Fin N → ℝ)) = 0 := by
    filter_upwards
        [hν, Filter.eventually_ge_atTop (1 : ℕ)] with
        N hνN hN
    refine ⟨invariant_Pkernel_of_invariant_Kchain
      A N (ν N : Measure ℝ) hνN.1, ?_⟩
    rw [← map_radiusSq_apply_singleton_zero
      (show 0 < N by omega)
      ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))]
    rw [radiusSq_map_Jkernel_comp, hνN.1.def, hνN.2.2.1]
  refine ⟨C, D, ν, hC, hD, hν, hvector, ?_⟩
  intro ζ hζ
  have hscalarSlack := hscalar ζ hζ
  filter_upwards [hscalarSlack] with N hscalarN
  exact
    (tvDist_Pkernel_pow_succ_le_markovPathMeasure_radius_marginal
      A N (ν N : Measure ℝ) (x N)
        (supercriticalIntegerCutoffTime A qStar q₀ N c)).trans hscalarN

/-- The locally uniform Koenigs asymptotic remains valid when both the
initial state and the iteration time vary, provided the initial states
converge inside the supercritical state space and the times tend to infinity.
-/
theorem tendsto_normalized_V_orbit_sub_fixed_of_tendsto
    {A qStar q₀ : ℝ} (q : ℕ → ℝ) (T : ℕ → ℕ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop, q N ∈ Set.Ioc (0 : ℝ) 1)
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun N : ℕ =>
        ((V A)^[T N] (q N) - qStar) *
          (deriv (V A) qStar)⁻¹ ^ T N)
      Filter.atTop
      (nhds (koenigsCoefficient A qStar q₀)) := by
  obtain ⟨r, hr, hq₀K, hKD, huniform⟩ :=
    exists_tendstoUniformlyOn_normalized_V_orbit_sub_fixed
      hA hqStar hfix hq₀ hq₀ne
  let K : Set ℝ := Set.Icc (q₀ - r) (min (q₀ + r) 1)
  have hqclose :
      ∀ᶠ N : ℕ in Filter.atTop,
        dist (q N) q₀ < r :=
    hq (Metric.ball_mem_nhds q₀ hr)
  have hqK :
      ∀ᶠ N : ℕ in Filter.atTop, q N ∈ K := by
    filter_upwards [hqclose, hqmem] with N hclose hqN
    rw [Real.dist_eq, abs_lt] at hclose
    change q₀ - r ≤ q N ∧ q N ≤ min (q₀ + r) 1
    exact ⟨by linarith, le_min (by linarith) hqN.2⟩
  have hqWithin :
      Filter.Tendsto q Filter.atTop (nhdsWithin q₀ K) :=
    tendsto_nhdsWithin_iff.mpr ⟨hq, hqK⟩
  have hcoeff :
      Filter.Tendsto
        (fun N : ℕ => koenigsCoefficient A qStar (q N))
        Filter.atTop
        (nhds (koenigsCoefficient A qStar q₀)) := by
    exact Filter.Tendsto.comp
      ((continuousOn_koenigsCoefficient hA hqStar hfix).mono hKD
        q₀ hq₀K) hqWithin
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  have herror :
      Filter.Tendsto
        (fun N : ℕ =>
          ((V A)^[T N] (q N) - qStar) *
              (deriv (V A) qStar)⁻¹ ^ T N -
            koenigsCoefficient A qStar (q N))
        Filter.atTop
        (nhds 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    have heventually :
        ∀ᶠ N : ℕ in Filter.atTop,
          dist
              (((V A)^[T N] (q N) - qStar) *
                  (deriv (V A) qStar)⁻¹ ^ T N -
                koenigsCoefficient A qStar (q N))
              0 < ε := by
      filter_upwards [hT (huniform ε hε), hqK] with N hTN hqKN
      have hdist := hTN (q N) hqKN
      simpa only [Real.dist_eq, sub_zero, abs_sub_comm] using hdist
    exact Filter.eventually_atTop.1 heventually
  simpa only [sub_add_cancel, zero_add] using herror.add hcoeff

/-- At the integer cutoff time, every convergent nonstationary initial
sequence retains a fixed positive multiple of the paper's deterministic
`N⁻¹ᐟ² μ^c` separation scale. -/
theorem
    exists_eventually_rpow_le_sqrt_nat_mul_abs_V_iterate_integerCutoffTime_sub_fixed
    {A qStar q₀ : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop, q N ∈ Set.Ioc (0 : ℝ) 1)
    (c : ℝ) :
    ∃ d : ℝ, 0 < d ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        d * deriv (V A) qStar ^ c ≤
          Real.sqrt (N : ℝ) *
            |(V A)^[
                supercriticalIntegerCutoffTime A qStar q₀ N c] (q N) -
              qStar| := by
  let μ := deriv (V A) qStar
  let C := koenigsCoefficient A qStar q₀
  let T : ℕ → ℕ :=
    fun N => supercriticalIntegerCutoffTime A qStar q₀ N c
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hCne : C ≠ 0 := by
    exact koenigsCoefficient_ne_zero hA hqStar hfix hq₀ hq₀ne
  have hCpos : 0 < |C| :=
    abs_pos.mpr hCne
  have hT :
      Filter.Tendsto T Filter.atTop Filter.atTop := by
    exact
      tendsto_supercriticalIntegerCutoffTime_atTop
        (q₀ := q₀) hA hqStar hfix c
  have hnormalized :=
    tendsto_normalized_V_orbit_sub_fixed_of_tendsto
      q T hA hqStar hfix hq₀ hq₀ne hq hqmem hT
  have hnormalizedLower :
      ∀ᶠ N : ℕ in Filter.atTop,
        |C| / 2 ≤
          |((V A)^[T N] (q N) - qStar) * μ⁻¹ ^ T N| := by
    have habs :
        Filter.Tendsto
          (fun N : ℕ =>
            |((V A)^[T N] (q N) - qStar) * μ⁻¹ ^ T N|)
          Filter.atTop
          (nhds |C|) := by
      simpa only [μ, C] using hnormalized.abs
    have hlower :=
      habs (eventually_gt_nhds (by linarith : |C| / 2 < |C|))
    filter_upwards [hlower] with N hN
    exact hN.le
  have hshiftAtTop :
      Filter.Tendsto
        (fun N : ℕ =>
          supercriticalCutoffTime A qStar q₀ N + c)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop c
      (tendsto_supercriticalCutoffTime_atTop
        (q₀ := q₀) hA hqStar hfix)
  have hnonneg :
      ∀ᶠ N : ℕ in Filter.atTop,
        0 ≤ supercriticalCutoffTime A qStar q₀ N + c :=
    hshiftAtTop.eventually (Filter.eventually_ge_atTop 0)
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards
      [hnormalizedLower, hnonneg,
       Filter.eventually_ge_atTop (1 : ℕ)] with
      N hnormalizedN hnonnegN hN
  let t := supercriticalCutoffTime A qStar q₀ N
  let n := T N
  let x := (V A)^[n] (q N) - qStar
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 hNreal
  have hfloor :
      (n : ℝ) ≤ t + c := by
    dsimp only [n, T, t]
    exact Nat.floor_le hnonnegN
  have hpowLower :
      μ ^ (t + c) ≤ μ ^ n := by
    rw [← Real.rpow_natCast]
    exact
      Real.rpow_le_rpow_of_exponent_ge hμ.1 hμ.2.le hfloor
  have hxLower :
      |C| / 2 * μ ^ n ≤ |x| := by
    change |C| / 2 ≤ |x * μ⁻¹ ^ n| at hnormalizedN
    have hμpowpos : 0 < μ ^ n :=
      pow_pos hμ.1 n
    calc
      |C| / 2 * μ ^ n ≤
          |x * μ⁻¹ ^ n| * μ ^ n :=
        mul_le_mul_of_nonneg_right hnormalizedN hμpowpos.le
      _ = |x| := by
        rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr hμ.1),
          mul_assoc, ← mul_pow, inv_mul_cancel₀ hμ.1.ne',
          one_pow, mul_one]
  have hnormalize :
      μ ^ t =
        1 / (Real.sqrt (N : ℝ) * |C|) := by
    simpa only [μ, C, t] using
      rpow_supercriticalCutoffTime_eq_inv_sqrt_mul_abs_koenigsCoefficient
        hA hqStar hfix hq₀ hq₀ne hNpos
  have hscale :
      Real.sqrt (N : ℝ) *
          (|C| / 2 * μ ^ (t + c)) =
        1 / 2 * μ ^ c := by
    rw [Real.rpow_add hμ.1, hnormalize]
    field_simp [hsqrtpos.ne', hCne]
    ring
  change
    1 / 2 * μ ^ c ≤ Real.sqrt (N : ℝ) * |x|
  calc
    1 / 2 * μ ^ c =
        Real.sqrt (N : ℝ) *
          (|C| / 2 * μ ^ (t + c)) := hscale.symm
    _ ≤
        Real.sqrt (N : ℝ) *
          (|C| / 2 * μ ^ n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpowLower
          (div_nonneg (abs_nonneg C) (by norm_num)))
        hsqrtpos.le
    _ ≤ Real.sqrt (N : ℝ) * |x| :=
      mul_le_mul_of_nonneg_left hxLower hsqrtpos.le

/-- Two probability measures with small centered second moments are separated
in total variation when their centers are far apart.  The test event is the
open half-radius interval about the first center. -/
lemma one_sub_four_mul_add_div_sq_le_tvDist_of_integral_sq
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b Mμ Mν : ℝ)
    (hab : a ≠ b)
    (hμint : Integrable (fun x : ℝ => (x - a) ^ 2) μ)
    (hνint : Integrable (fun x : ℝ => (x - b) ^ 2) ν)
    (hμbound : (∫ x : ℝ, (x - a) ^ 2 ∂μ) ≤ Mμ)
    (hνbound : (∫ x : ℝ, (x - b) ^ 2 ∂ν) ≤ Mν) :
    1 - 4 * (Mμ + Mν) / |a - b| ^ 2 ≤ tvDist μ ν := by
  let R : ℝ := |a - b| / 2
  let E : Set ℝ := {x : ℝ | |x - a| < R}
  have hδpos : 0 < |a - b| :=
    abs_pos.mpr (sub_ne_zero.mpr hab)
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact measurableSet_lt (measurable_id.sub_const a).abs measurable_const
  have hμnonneg :
      0 ≤ᵐ[μ] fun x : ℝ => (x - a) ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg (x - a)
  have hμmarkov :=
    mul_meas_ge_le_integral_of_nonneg hμnonneg hμint (R ^ 2)
  have hμsubset :
      Eᶜ ⊆ {x : ℝ | R ^ 2 ≤ (x - a) ^ 2} := by
    intro x hx
    have hxR : R ≤ |x - a| := by
      simpa only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] using hx
    change R ^ 2 ≤ (x - a) ^ 2
    simpa only [sq_abs] using
      (sq_le_sq₀ hR.le (abs_nonneg (x - a))).2 hxR
  have hμcompl :
      μ.real Eᶜ ≤ Mμ / R ^ 2 := by
    have hmul :
        R ^ 2 * μ.real Eᶜ ≤ Mμ :=
      (mul_le_mul_of_nonneg_left
          (measureReal_mono hμsubset) (sq_nonneg R)).trans
        (hμmarkov.trans hμbound)
    calc
      μ.real Eᶜ =
          (R ^ 2 * μ.real Eᶜ) / R ^ 2 := by
        field_simp [hR.ne']
      _ ≤ Mμ / R ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hR)).2 hmul
  have hνsubset :
      E ⊆ {x : ℝ | R < |x - b|} := by
    intro x hx
    have hxR : |x - a| < R := hx
    have htriangle : |a - b| ≤ |x - a| + |x - b| := by
      simpa only [abs_sub_comm a x] using abs_sub_le a x b
    have htwoR : |a - b| = R + R := by
      dsimp only [R]
      ring
    rw [htwoR] at htriangle
    change R < |x - b|
    linarith
  have hνE :
      ν.real E ≤ Mν / R ^ 2 := by
    calc
      ν.real E ≤ ν.real {x : ℝ | R < |x - b|} :=
        measureReal_mono hνsubset
      _ ≤ (∫ x : ℝ, (x - b) ^ 2 ∂ν) / R ^ 2 :=
        measureReal_abs_sub_gt_le_integral_sq_div ν b hR hνint
      _ ≤ Mν / R ^ 2 :=
        div_le_div_of_nonneg_right hνbound (sq_nonneg R)
  have hμsum := measureReal_add_measureReal_compl (μ := μ) hE
  rw [probReal_univ] at hμsum
  have hμE :
      1 - Mμ / R ^ 2 ≤ μ.real E := by
    linarith
  have hdisc :
      μ.real E - ν.real E ≤ tvDist μ ν :=
    (le_abs_self _).trans
      (abs_measure_toReal_sub_le_tvDist μ ν E hE)
  have hbasic :
      1 - (Mμ / R ^ 2 + Mν / R ^ 2) ≤ tvDist μ ν := by
    linarith
  convert hbasic using 1
  dsimp only [R]
  field_simp [hδpos.ne']
  ring

/-- The fixed-measure separating-event estimate at the cutoff scale.  Two
`N⁻¹` moment envelopes and a center separation of order
`N⁻¹ᐟ² μ^c` give an `N`-independent lower total-variation profile. -/
lemma
    eventually_one_sub_four_mul_add_div_sq_rpow_le_tvDist_of_inv_nat_moments
    (ρ ν : ℕ → ProbabilityMeasure ℝ) (a : ℕ → ℝ)
    (b Cρ Cν d μ c : ℝ)
    (hCρ : 0 ≤ Cρ) (hCν : 0 ≤ Cν)
    (hd : 0 < d) (hμ : 0 < μ)
    (hρint :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x : ℝ => (x - a N) ^ 2)
          (ρ N : Measure ℝ))
    (hνint :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x : ℝ => (x - b) ^ 2)
          (ν N : Measure ℝ))
    (hρbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x : ℝ, (x - a N) ^ 2 ∂(ρ N : Measure ℝ)) ≤
          Cρ / (N : ℝ))
    (hνbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x : ℝ, (x - b) ^ 2 ∂(ν N : Measure ℝ)) ≤
          Cν / (N : ℝ))
    (hseparation :
      ∀ᶠ N : ℕ in Filter.atTop,
        d * μ ^ c ≤
          Real.sqrt (N : ℝ) * |a N - b|) :
    ∀ᶠ N : ℕ in Filter.atTop,
      1 - 4 * (Cρ + Cν) / (d ^ 2 * μ ^ (2 * c)) ≤
        tvDist (ρ N : Measure ℝ) (ν N : Measure ℝ) := by
  filter_upwards
      [hρint, hνint, hρbound, hνbound, hseparation,
       Filter.eventually_ge_atTop (1 : ℕ)] with
      N hρintN hνintN hρboundN hνboundN hseparationN hN
  have hNpos : 0 < N :=
    Nat.zero_lt_of_lt hN
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  have hμc : 0 < μ ^ c :=
    Real.rpow_pos_of_pos hμ c
  have hcenter : a N ≠ b := by
    intro hab
    rw [hab, sub_self, abs_zero, mul_zero] at hseparationN
    exact (not_le_of_gt (mul_pos hd hμc)) hseparationN
  have hδpos : 0 < |a N - b| :=
    abs_pos.mpr (sub_ne_zero.mpr hcenter)
  have hden :
      d ^ 2 * μ ^ (2 * c) ≤
        (N : ℝ) * |a N - b| ^ 2 := by
    calc
      d ^ 2 * μ ^ (2 * c) =
          (d * μ ^ c) ^ 2 := by
        rw [show (2 : ℝ) * c = c * (2 : ℕ) by norm_num [mul_comm],
          Real.rpow_mul_natCast hμ.le]
        ring
      _ ≤
          (Real.sqrt (N : ℝ) * |a N - b|) ^ 2 :=
        (sq_le_sq₀ (mul_nonneg hd.le hμc.le)
          (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).2
            hseparationN
      _ = (N : ℝ) * |a N - b| ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hNreal.le]
  have hfixed :=
    one_sub_four_mul_add_div_sq_le_tvDist_of_integral_sq
      (ρ N : Measure ℝ) (ν N : Measure ℝ)
      (a N) b (Cρ / (N : ℝ)) (Cν / (N : ℝ))
      hcenter hρintN hνintN hρboundN hνboundN
  have hnum : 0 ≤ 4 * (Cρ + Cν) := by
    positivity
  have hdencutoff : 0 < d ^ 2 * μ ^ (2 * c) := by
    positivity
  have hratio :
      4 * (Cρ + Cν) /
            ((N : ℝ) * |a N - b| ^ 2) ≤
        4 * (Cρ + Cν) / (d ^ 2 * μ ^ (2 * c)) :=
    div_le_div_of_nonneg_left hnum hdencutoff hden
  have hscaled :
      4 * (Cρ / (N : ℝ) + Cν / (N : ℝ)) /
          |a N - b| ^ 2 ≤
        4 * (Cρ + Cν) / (d ^ 2 * μ ^ (2 * c)) := by
    calc
      4 * (Cρ / (N : ℝ) + Cν / (N : ℝ)) /
          |a N - b| ^ 2 =
          4 * (Cρ + Cν) /
            ((N : ℝ) * |a N - b| ^ 2) := by
        field_simp [hNreal.ne', hδpos.ne']
      _ ≤ 4 * (Cρ + Cν) / (d ^ 2 * μ ^ (2 * c)) :=
        hratio
  exact (sub_le_sub_left hscaled 1).trans hfixed

/-- A positive convergent scalar initial sequence has the paper's lower
cutoff profile against one selected origin-free invariant family. -/
theorem
    exists_stationary_family_eventually_one_sub_mul_rpow_le_tvDist_cutoff_marginal
    {A qStar q₀ : ℝ} (q : ℕ → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hq : Filter.Tendsto q Filter.atTop (nhds q₀))
    (hqmem :
      ∀ᶠ N : ℕ in Filter.atTop, q N ∈ Set.Ioc (0 : ℝ) 1)
    (c : ℝ) :
    ∃ C D : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < D ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        1 - D * deriv (V A) qStar ^ (-(2 * c)) ≤
          tvDist
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalIntegerCutoffTime
                    A qStar q₀ N c)))
            (ν N : Measure ℝ)) := by
  let μ := deriv (V A) qStar
  let T : ℕ → ℕ :=
    fun N => supercriticalIntegerCutoffTime A qStar q₀ N c
  let a : ℕ → ℝ :=
    fun N => (V A)^[T N] (q N)
  obtain ⟨κ, R, η, Cν, ν, hκ0, hκ1, hη0, hηR,
      hRinterior, hCν, hderiv, hν⟩ :=
    exists_eventually_invariant_Kchain_family_integral_sq_sub_fixed_le_inv_nat
      hA hqStar hfix
  obtain ⟨Cₜ, hCₜ, hTlinear, _hblock⟩ :=
    exists_eventually_supercriticalCutoff_block_horizon
      (q₀ := q₀) (b := (1 : ℝ))
      hA hqStar hfix zero_lt_one c
  obtain ⟨m, Cρ, hCρ, hdynamic⟩ :=
    exists_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_of_tendsto
      q T hA hqStar hfix hq₀ hq hqmem hCₜ.le hTlinear
  have hTatTop :
      Filter.Tendsto T Filter.atTop Filter.atTop := by
    exact
      tendsto_supercriticalIntegerCutoffTime_atTop
        (q₀ := q₀) hA hqStar hfix c
  have hmT :
      ∀ᶠ N : ℕ in Filter.atTop, m ≤ T N :=
    hTatTop.eventually (Filter.eventually_ge_atTop m)
  have hpathBound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ ω, (ω (T N) - a N) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N))) ≤
          Cρ / (N : ℝ) := by
    filter_upwards [hdynamic, hmT] with N hdynamicN hmTN
    exact hdynamicN (T N) hmTN le_rfl
  have hpathInt :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable
          (fun ω : ℕ → ℝ => (ω (T N) - a N) ^ 2)
          (markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)) := by
    filter_upwards
        [hqmem, Filter.eventually_ge_atTop (1 : ℕ)] with
        N hqN hN
    apply integrable_sq_sub_of_ae_mem_Icc
      (markovPathMeasure
        (Measure.dirac (q N)) (Kchain A N))
      (fun ω : ℕ → ℝ => ω (T N)) (a N)
    · exact
        (((measurable_pi_apply (T N)).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact
        markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
          ⟨hqN.1.le, hqN.2⟩ (Nat.zero_lt_of_lt hN) (T N)
  let ρ : ℕ → ProbabilityMeasure ℝ :=
    fun N =>
      ⟨(markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).map
            (fun ω => ω (T N)),
        Measure.isProbabilityMeasure_map
          (measurable_pi_apply (T N)).aemeasurable⟩
  have hρInt :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x : ℝ => (x - a N) ^ 2)
          (ρ N : Measure ℝ) := by
    filter_upwards [hpathInt] with N hpathIntN
    let f : ℝ → ℝ := fun x => (x - a N) ^ 2
    have hf :
        AEStronglyMeasurable f (ρ N : Measure ℝ) := by
      dsimp only [f]
      exact
        ((measurable_id.sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    apply
      (integrable_map_measure hf
        (measurable_pi_apply (T N)).aemeasurable).2
    change
      Integrable
        (fun ω : ℕ → ℝ => (ω (T N) - a N) ^ 2)
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N))
    exact hpathIntN
  have hρBound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x : ℝ, (x - a N) ^ 2 ∂(ρ N : Measure ℝ)) ≤
          Cρ / (N : ℝ) := by
    filter_upwards [hpathBound] with N hpathBoundN
    have hf :
        AEStronglyMeasurable
          (fun x : ℝ => (x - a N) ^ 2)
          (ρ N : Measure ℝ) :=
      ((measurable_id.sub measurable_const).pow_const 2)
        |>.aestronglyMeasurable
    rw [show
      (∫ x : ℝ, (x - a N) ^ 2 ∂(ρ N : Measure ℝ)) =
          ∫ ω, (ω (T N) - a N) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)) by
        dsimp only [ρ]
        exact
          integral_map
            (measurable_pi_apply (T N)).aemeasurable hf]
    exact hpathBoundN
  have hνInt :
      ∀ᶠ N : ℕ in Filter.atTop,
        Integrable (fun x : ℝ => (x - qStar) ^ 2)
          (ν N : Measure ℝ) :=
    hν.mono fun _ hνN => hνN.2.2.2.1
  have hνBound :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ x : ℝ, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          Cν / (N : ℝ) :=
    hν.mono fun _ hνN => hνN.2.2.2.2
  obtain ⟨d, hd, hseparation⟩ :=
    exists_eventually_rpow_le_sqrt_nat_mul_abs_V_iterate_integerCutoffTime_sub_fixed
      q hA hqStar hfix hq₀ hq₀ne hq hqmem c
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hlower :=
    eventually_one_sub_four_mul_add_div_sq_rpow_le_tvDist_of_inv_nat_moments
      ρ ν a qStar Cρ Cν d μ c hCρ hCν.le hd hμ.1
      hρInt hνInt hρBound hνBound hseparation
  let D : ℝ := 4 * (Cρ + Cν) / d ^ 2
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hprofile :
      D * μ ^ (-(2 * c)) =
        4 * (Cρ + Cν) / (d ^ 2 * μ ^ (2 * c)) := by
    dsimp only [D, μ]
    rw [Real.rpow_neg hμ.1.le]
    field_simp [hd.ne']
  refine ⟨Cν, D, ν, hCν, hD, hν, ?_⟩
  filter_upwards [hlower] with N hlowerN
  change
    1 - D * μ ^ (-(2 * c)) ≤
      tvDist (ρ N : Measure ℝ) (ν N : Measure ℝ)
  rw [hprofile]
  exact hlowerN

/-- A convergent sequence of positive vector radii admits a reconstructed
origin-free invariant vector family with the paper's lower cutoff profile. -/
theorem
    exists_reconstructed_invariant_vector_family_eventually_one_sub_mul_rpow_le_tvDist_cutoff
    {A qStar q₀ : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀))
    (hradiusMem :
      ∀ᶠ N : ℕ in Filter.atTop,
        radiusSq N (x N) ∈ Set.Ioc (0 : ℝ) 1)
    (c : ℝ) :
    ∃ C D : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < D ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N)
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ∧
          ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
              ({0} : Set (Fin N → ℝ)) = 0) ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        1 - D * deriv (V A) qStar ^ (-(2 * c)) ≤
          tvDist
            (((Pkernel A N) ^
              supercriticalIntegerCutoffTime A qStar q₀ N c)
                (x N))
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) := by
  obtain ⟨C, D, ν, hC, hD, hν, hlower⟩ :=
    exists_stationary_family_eventually_one_sub_mul_rpow_le_tvDist_cutoff_marginal
      (fun N : ℕ => radiusSq N (x N))
      hA hqStar hfix hq₀ hq₀ne hradius hradiusMem c
  have hvector :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N)
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ∧
          ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
              ({0} : Set (Fin N → ℝ)) = 0 := by
    filter_upwards
        [hν, Filter.eventually_ge_atTop (1 : ℕ)] with
        N hνN hN
    refine ⟨invariant_Pkernel_of_invariant_Kchain
      A N (ν N : Measure ℝ) hνN.1, ?_⟩
    rw [← map_radiusSq_apply_singleton_zero
      (show 0 < N by omega)
      ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))]
    rw [radiusSq_map_Jkernel_comp, hνN.1.def, hνN.2.2.1]
  refine ⟨C, D, ν, hC, hD, hν, hvector, ?_⟩
  filter_upwards [hlower, hν] with N hlowerN hνN
  rw [markovPathMeasure_dirac_map_eval] at hlowerN
  exact hlowerN.trans
    (tvDist_Kchain_pow_le_Pkernel_pow
      A N (ν N : Measure ℝ) hνN.1 (x N)
        (supercriticalIntegerCutoffTime A qStar q₀ N c))

end AbsorptionCutoff
