/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.CutoffProfileAssembly

/-!
# Cutoff limit assembly for the supercritical chain

This module continues the supercritical cutoff proof after the shift-uniform
scalar, vector, and terminal-coupling profiles established in
`CutoffProfileAssembly.lean`. The remaining scaled bounds and paper-facing
iterated limits belong here.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- The paper's constant-one supercritical window is admissible: the cutoff
center diverges, the window is positive, and it is negligible relative to the
center. -/
lemma isCutoffWindow_supercriticalCutoffTime_one
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    IsCutoffWindow
      (supercriticalCutoffTime A qStar q₀)
      (fun _ => 1) := by
  have hcenter :=
    tendsto_supercriticalCutoffTime_atTop
      (q₀ := q₀) hA hqStar hfix
  refine ⟨hcenter, Filter.Eventually.of_forall (fun _ => zero_lt_one), ?_⟩
  rw [Asymptotics.isLittleO_const_left]
  exact Or.inr (tendsto_norm_atTop_atTop.comp hcenter)

/-- The terminal synchronous distance has one inverse-square-root cutoff
profile constant for every fixed shift. -/
theorem
    exists_forall_eventually_sqrt_nat_mul_terminalBlock_distance_le_rpow_add
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
    (hb : 0 < b)
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
    ∃ Dprofile : ℝ, 0 < Dprofile ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        Real.sqrt (N : ℝ) *
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
          Dprofile * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨L, C₁, C₀, D, hL, hC₁, hC₀, hD, hterminal⟩ :=
    exists_forall_eventually_terminalBlock_distance_le_multiplier_pow_mul_rpow_add
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb
      hC₂ hνsupport hνinv hνsq hνbound
  let Dprofile : ℝ := 2 * D
  have hDprofile : 0 < Dprofile := by
    dsimp only [Dprofile]
    positivity
  refine ⟨Dprofile, hDprofile, ?_⟩
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hfluct :
      Filter.Tendsto
        (fun N : ℕ =>
          deriv (V A) qStar ^
              supercriticalTerminalBlockLength b N *
            (Real.sqrt C₀ + Real.sqrt C₂))
        Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_supercriticalTerminalBlockLength_zero
        hμ.1.le hμ.2 hb).mul_const (Real.sqrt C₀ + Real.sqrt C₂)
  have hlocalization :=
    tendsto_sqrt_nat_mul_terminalLocalizationError_zero
      (L := L) (C := 4 * C₁ + C₂) hA hqStar hfix
  intro ζ hζ c
  have hupper :
      Filter.Tendsto
        (fun N : ℕ =>
          (1 + (1 : ℝ)) *
              (deriv (V A) qStar ^
                    supercriticalTerminalBlockLength b N *
                  (Real.sqrt C₀ + Real.sqrt C₂) +
                D * deriv (V A) qStar ^ c) +
            Real.sqrt (N : ℝ) *
              ((((4 * C₁ + C₂) /
                    supercriticalTerminalRadius N ^ 2) /
                  (N : ℝ)) /
                (1 -
                  supercriticalTerminalContraction A qStar L N)))
        Filter.atTop
          (nhds (Dprofile * deriv (V A) qStar ^ c)) := by
    have hbase :=
      ((hfluct.add_const
        (D * deriv (V A) qStar ^ c)).const_mul
          (1 + (1 : ℝ))).add hlocalization
    simpa only [Dprofile, zero_add, add_zero, one_add_one_eq_two,
      mul_assoc] using hbase
  have hupperEventually :
      ∀ᶠ N : ℕ in Filter.atTop,
        (1 + (1 : ℝ)) *
              (deriv (V A) qStar ^
                    supercriticalTerminalBlockLength b N *
                  (Real.sqrt C₀ + Real.sqrt C₂) +
                D * deriv (V A) qStar ^ c) +
            Real.sqrt (N : ℝ) *
              ((((4 * C₁ + C₂) /
                    supercriticalTerminalRadius N ^ 2) /
                  (N : ℝ)) /
                (1 -
                  supercriticalTerminalContraction A qStar L N)) <
          Dprofile * deriv (V A) qStar ^ c + ζ :=
    hupper (eventually_lt_nhds (by linarith))
  filter_upwards
      [hterminal 1 zero_lt_one c, hupperEventually,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hterminalN hupperN hN
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hsqrt : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 hNpos
  have hscaled :=
    mul_le_mul_of_nonneg_left hterminalN hsqrt.le
  calc
    Real.sqrt (N : ℝ) *
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
        Real.sqrt (N : ℝ) *
          ((1 + (1 : ℝ)) *
              deriv (V A) qStar ^
                supercriticalTerminalBlockLength b N *
              ((Real.sqrt C₀ +
                  D * deriv (V A) qStar ^
                    (c -
                      (supercriticalTerminalBlockLength b N : ℝ)) +
                  Real.sqrt C₂) /
                Real.sqrt (N : ℝ)) +
            ((((4 * C₁ + C₂) /
                supercriticalTerminalRadius N ^ 2) /
              (N : ℝ)) /
              (1 -
                supercriticalTerminalContraction A qStar L N))) :=
      hscaled
    _ =
        (1 + (1 : ℝ)) *
              (deriv (V A) qStar ^
                    supercriticalTerminalBlockLength b N *
                  (Real.sqrt C₀ + Real.sqrt C₂) +
                D * deriv (V A) qStar ^ c) +
            Real.sqrt (N : ℝ) *
              ((((4 * C₁ + C₂) /
                    supercriticalTerminalRadius N ^ 2) /
                  (N : ℝ)) /
                (1 -
                  supercriticalTerminalContraction A qStar L N)) := by
      have hcancel :=
        pow_mul_rpow_sub_natCast hμ.1
          (supercriticalTerminalBlockLength b N) c
      have halgebra :
          deriv (V A) qStar ^
                supercriticalTerminalBlockLength b N *
              (Real.sqrt C₀ +
                D * deriv (V A) qStar ^
                  (c -
                    (supercriticalTerminalBlockLength b N : ℝ)) +
                Real.sqrt C₂) =
            deriv (V A) qStar ^
                  supercriticalTerminalBlockLength b N *
                (Real.sqrt C₀ + Real.sqrt C₂) +
              D * deriv (V A) qStar ^ c := by
        calc
          _ =
              deriv (V A) qStar ^
                    supercriticalTerminalBlockLength b N *
                  (Real.sqrt C₀ + Real.sqrt C₂) +
                D *
                  (deriv (V A) qStar ^
                      supercriticalTerminalBlockLength b N *
                    deriv (V A) qStar ^
                      (c -
                        (supercriticalTerminalBlockLength b N : ℝ))) := by
            ring
          _ = _ := by rw [hcancel]
      rw [mul_add]
      field_simp [hsqrt.ne']
      linear_combination
        (1 + (1 : ℝ)) * (N : ℝ) * halgebra
    _ ≤ Dprofile * deriv (V A) qStar ^ c + ζ :=
      hupperN.le

/-- One centered moment envelope localizes the evolving coordinate at the
endpoint of every fixed-shift terminal block. -/
theorem
    exists_forall_eventually_shifted_eval_terminalBlockLength_not_mem_terminalInterval_le
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
    (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        (markovPathMeasure
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockStart
                    A qStar q₀ c b N)))
            (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉
                Set.Icc
                  (qStar - supercriticalTerminalRadius N)
                  (qStar + supercriticalTerminalRadius N)} ≤
          (4 * C / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) := by
  obtain ⟨m, C, hC, hmoment⟩ :=
    exists_forall_eventually_forall_integral_sq_eval_sub_V_iterate_le_inv_nat_cutoff
      q hA hqStar hfix hq₀ hq hqmem
  refine ⟨C, hC, ?_⟩
  intro c
  have hblock :=
    eventually_supercriticalTerminalBlockStart_add_length_eq_integerCutoffTime_sub_one
      (q₀ := q₀) hA hqStar hfix hb c
  have hentranceBefore :
      ∀ᶠ N : ℕ in Filter.atTop,
        m ≤ supercriticalTerminalBlockStart A qStar q₀ c b N :=
    (tendsto_supercriticalTerminalBlockStart_atTop
      (q₀ := q₀) hA hqStar hfix hb c).eventually
        (Filter.eventually_ge_atTop m)
  have hmomentEndpoint :
      ∀ᶠ N : ℕ in Filter.atTop,
        (∫ ω,
          (ω (supercriticalTerminalBlockStart
                A qStar q₀ c b N +
              supercriticalTerminalBlockLength b N) -
            (V A)^[
              supercriticalTerminalBlockStart
                  A qStar q₀ c b N +
                supercriticalTerminalBlockLength b N] (q N)) ^ 2
            ∂(markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N))) ≤
          C / (N : ℝ) := by
    filter_upwards
        [hmoment c, hentranceBefore, hblock] with
        N hmomentN hentranceBeforeN hblockN
    exact
      hmomentN
        (supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N)
        (by omega) (by omega)
  have hcenter :=
    eventually_forall_abs_V_iterate_terminalBlockStart_add_sub_fixed_le_half_terminalRadius
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb c
  have hqIcc :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1 :=
    hqmem.mono fun _ hqN => ⟨hqN.1.le, hqN.2⟩
  filter_upwards
      [hmomentEndpoint, hcenter, hqIcc,
        Filter.eventually_ge_atTop (2 : ℕ)] with
      N hmomentN hcenterN hqN hN
  have hNpos : 0 < N := by omega
  have hsq :
      Integrable
        (fun ω : ℕ → ℝ =>
          (ω (supercriticalTerminalBlockStart
                A qStar q₀ c b N +
              supercriticalTerminalBlockLength b N) -
            (V A)^[
              supercriticalTerminalBlockStart
                  A qStar q₀ c b N +
                supercriticalTerminalBlockLength b N] (q N)) ^ 2)
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)) := by
    apply integrable_sq_sub_of_ae_mem_Icc
      (markovPathMeasure
        (Measure.dirac (q N)) (Kchain A N))
      (fun ω : ℕ → ℝ =>
        ω (supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N))
      ((V A)^[
        supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N] (q N))
    · exact
        (((measurable_pi_apply
          (supercriticalTerminalBlockStart A qStar q₀ c b N +
            supercriticalTerminalBlockLength b N)).sub
              measurable_const).pow_const 2).aestronglyMeasurable
    · exact
        markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
          hqN hNpos
            (supercriticalTerminalBlockStart A qStar q₀ c b N +
              supercriticalTerminalBlockLength b N)
  have hlocal :=
    markovPathMeasure_measureReal_eval_not_mem_stableInterval_le_four_mul_div_sq_div_nat_of_center
      (Measure.dirac (q N)) (Kchain A N)
      (supercriticalTerminalBlockStart A qStar q₀ c b N +
        supercriticalTerminalBlockLength b N)
      ((V A)^[
        supercriticalTerminalBlockStart A qStar q₀ c b N +
          supercriticalTerminalBlockLength b N] (q N))
      qStar
      (supercriticalTerminalRadius_pos (show 1 < N by omega))
      (hcenterN (supercriticalTerminalBlockLength b N))
      hsq hmomentN
  let J : Set ℝ :=
    Set.Icc
      (qStar - supercriticalTerminalRadius N)
      (qStar + supercriticalTerminalRadius N)
  have hshift :=
    markovPathMeasure_measureReal_eval_mem_of_map_eval
      (Measure.dirac (q N)) (Kchain A N)
      (supercriticalTerminalBlockStart A qStar q₀ c b N)
      (supercriticalTerminalBlockLength b N) Jᶜ
      measurableSet_Icc.compl
  calc
    (markovPathMeasure
          ((markovPathMeasure
            (Measure.dirac (q N)) (Kchain A N)).map
              (fun ω =>
                ω (supercriticalTerminalBlockStart
                  A qStar q₀ c b N)))
          (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω (supercriticalTerminalBlockLength b N) ∉
              Set.Icc
                (qStar - supercriticalTerminalRadius N)
                (qStar + supercriticalTerminalRadius N)} =
        (markovPathMeasure
          (Measure.dirac (q N)) (Kchain A N)).real
          {ω : ℕ → ℝ |
            ω (supercriticalTerminalBlockStart A qStar q₀ c b N +
                supercriticalTerminalBlockLength b N) ∉
              Set.Icc
                (qStar - supercriticalTerminalRadius N)
                (qStar + supercriticalTerminalRadius N)} := by
      simpa only [J, Set.mem_compl_iff] using hshift
    _ ≤ (4 * C / supercriticalTerminalRadius N ^ 2) /
        (N : ℝ) := hlocal

/-- One endpoint-localization constant controls the terminal synchronous pair
for every fixed shift. -/
theorem
    exists_forall_eventually_terminalBlock_endpoint_not_mem_prod_le
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
    (hb : 0 < b)
    (_hC₂ : 0 ≤ C₂)
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
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        (markovPathMeasure
            (((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockStart
                      A qStar q₀ c b N))).prod (ν N : Measure ℝ))
            (synchronousKchain A N)).real
            {ω : ℕ → ℝ × ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉
                Set.Icc
                    (qStar - supercriticalTerminalRadius N)
                    (qStar + supercriticalTerminalRadius N) ×ˢ
                  Set.Icc
                    (qStar - supercriticalTerminalRadius N)
                    (qStar + supercriticalTerminalRadius N)} ≤
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) := by
  obtain ⟨C, hC, hbad₁⟩ :=
    exists_forall_eventually_shifted_eval_terminalBlockLength_not_mem_terminalInterval_le
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb
  have hbad₂all :=
    eventually_forall_stationary_eval_not_mem_terminalInterval_le_inv_nat
      ν hνinv hνsq hνbound
  refine ⟨C, hC, ?_⟩
  intro c
  filter_upwards [hbad₁ c, hbad₂all] with N hbad₁N hbad₂N
  let ρ : Measure ℝ :=
    (markovPathMeasure
      (Measure.dirac (q N)) (Kchain A N)).map
        (fun ω =>
          ω (supercriticalTerminalBlockStart A qStar q₀ c b N))
  let ξ : Measure (ℝ × ℝ) := ρ.prod (ν N : Measure ℝ)
  let J : Set ℝ :=
    Set.Icc
      (qStar - supercriticalTerminalRadius N)
      (qStar + supercriticalTerminalRadius N)
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
  have hsnd : ξ.map Prod.snd = (ν N : Measure ℝ) := by
    dsimp only [ξ]
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
  have hpair :=
    markovPathMeasure_measureReal_eval_not_mem_prod_le_of_measure
      A N ξ (supercriticalTerminalBlockLength b N) J measurableSet_Icc
  rw [hfst, hsnd] at hpair
  calc
    (markovPathMeasure
          (((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockStart
                    A qStar q₀ c b N))).prod (ν N : Measure ℝ))
          (synchronousKchain A N)).real
          {ω : ℕ → ℝ × ℝ |
            ω (supercriticalTerminalBlockLength b N) ∉
              Set.Icc
                  (qStar - supercriticalTerminalRadius N)
                  (qStar + supercriticalTerminalRadius N) ×ˢ
                Set.Icc
                  (qStar - supercriticalTerminalRadius N)
                  (qStar + supercriticalTerminalRadius N)} ≤
        (markovPathMeasure ρ (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉ J} +
          (markovPathMeasure (ν N : Measure ℝ) (Kchain A N)).real
            {ω : ℕ → ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉ J} := by
      simpa only [ξ, ρ, J] using hpair
    _ ≤
        (4 * C / supercriticalTerminalRadius N ^ 2) / (N : ℝ) +
          (C₂ / supercriticalTerminalRadius N ^ 2) / (N : ℝ) := by
      exact add_le_add hbad₁N
        (hbad₂N (supercriticalTerminalBlockLength b N))
    _ = ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
        (N : ℝ) := by ring

/-- One-step score smoothing gives one terminal TV profile constant for every
fixed shift. -/
theorem
    exists_forall_eventually_terminalBlock_smoothed_tvDist_le_rpow_add_of_tendsto
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
    (hb : 0 < b)
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
    ∃ D : ℝ, 0 < D ∧ ∀ ζ : ℝ, 0 < ζ → ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        tvDist
            (Kchain A N ∘ₘ
              ((markovPathMeasure
                (((markovPathMeasure
                    (Measure.dirac (q N)) (Kchain A N)).map
                      (fun ω =>
                        ω (supercriticalTerminalBlockStart
                          A qStar q₀ c b N))).prod (ν N : Measure ℝ))
                (synchronousKchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockLength b N))).map Prod.fst)
            (Kchain A N ∘ₘ
              ((markovPathMeasure
                (((markovPathMeasure
                    (Measure.dirac (q N)) (Kchain A N)).map
                      (fun ω =>
                        ω (supercriticalTerminalBlockStart
                          A qStar q₀ c b N))).prod (ν N : Measure ℝ))
                (synchronousKchain A N)).map
                  (fun ω =>
                    ω (supercriticalTerminalBlockLength b N))).map Prod.snd) ≤
          D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨D₀, hD₀, hdistance⟩ :=
    exists_forall_eventually_sqrt_nat_mul_terminalBlock_distance_le_rpow_add
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb
      hC₂ hνsupport hνinv hνsq hνbound
  obtain ⟨C, hC, hbad⟩ :=
    exists_forall_eventually_terminalBlock_endpoint_not_mem_prod_le
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb
      hC₂ hνinv hνsq hνbound
  let B : ℝ := 1 / (Real.sqrt 2 * qStar)
  have hB : 0 < B := by
    dsimp only [B]
    exact one_div_pos.mpr
      (mul_pos (Real.sqrt_pos.2 (by norm_num)) hqStar.1)
  have hbadLimit :
      Filter.Tendsto
        (fun N : ℕ =>
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ))
        Filter.atTop (nhds 0) := by
    have hlimit :=
      tendsto_inv_nat_div_supercriticalTerminalRadius_sq_zero.const_mul
        (4 * C + C₂)
    convert hlimit using 1
    · funext N
      ring
    · simp
  have hradiusUpper :
      ∀ᶠ N : ℕ in Filter.atTop,
        supercriticalTerminalRadius N < qStar / 2 :=
    tendsto_supercriticalTerminalRadius_zero
      (eventually_lt_nhds (by linarith [hqStar.1]))
  refine ⟨B * D₀, mul_pos hB hD₀, ?_⟩
  intro ζ hζ c
  have hslack : 0 < ζ / (2 * B) := by positivity
  have hdistanceSlack :=
    hdistance (ζ / (2 * B)) hslack c
  have hbadSmall :
      ∀ᶠ N : ℕ in Filter.atTop,
        ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) ≤
          ζ / 2 :=
    Filter.Eventually.mono
      (hbadLimit (eventually_lt_nhds (by linarith)))
      fun _ hN => hN.le
  filter_upwards
      [hdistanceSlack, hbad c, hbadSmall, hradiusUpper,
        hqmem, hνsupport, Filter.eventually_ge_atTop (2 : ℕ)] with
      N hdistanceN hbadN hbadSmallN hradiusUpperN
        hqN hνsupportN hN
  have hNpos : 0 < N := by omega
  have hradiusPos : 0 < supercriticalTerminalRadius N :=
    supercriticalTerminalRadius_pos (show 1 < N by omega)
  have hradiusQ : supercriticalTerminalRadius N < qStar := by
    linarith [hqStar.1]
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
  have hρsupport :
      ρ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    dsimp only [ρ]
    exact
      markovPathMeasure_dirac_map_eval_apply_compl_Icc_eq_zero
        (A := A) ⟨hqN.1.le, hqN.2⟩ hNpos
          (supercriticalTerminalBlockStart A qStar q₀ c b N)
  have hξsupport :
      ξ ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
    dsimp only [ξ]
    exact Measure.prod_apply_compl_prod_Icc_eq_zero
      ρ (ν N : Measure ℝ) hρsupport hνsupportN
  have hdistInt :
      Integrable
        (fun ω : ℕ → ℝ × ℝ =>
          |(ω (supercriticalTerminalBlockLength b N)).1 -
            (ω (supercriticalTerminalBlockLength b N)).2|)
        (markovPathMeasure ξ (synchronousKchain A N)) :=
    integrable_abs_fst_sub_snd_eval_synchronousKchain_of_measure
      hNpos ξ hξsupport (supercriticalTerminalBlockLength b N)
  have hscore :=
    tvDist_Kchain_comp_map_eval_fst_snd_le_integral_add_stableInterval
      (qStar := qStar) (R := supercriticalTerminalRadius N)
      (zero_lt_one.trans hA) hradiusPos hradiusQ N ξ
      (supercriticalTerminalBlockLength b N) hdistInt
  have hgap :
      qStar / 2 ≤ qStar - supercriticalTerminalRadius N := by
    linarith
  have hden :
      Real.sqrt 2 * qStar ≤
        2 * Real.sqrt 2 *
          (qStar - supercriticalTerminalRadius N) := by
    calc
      Real.sqrt 2 * qStar =
          (2 * Real.sqrt 2) * (qStar / 2) := by ring
      _ ≤ (2 * Real.sqrt 2) *
          (qStar - supercriticalTerminalRadius N) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
  have hcoef :
      1 /
          (2 * Real.sqrt 2 *
            (qStar - supercriticalTerminalRadius N)) ≤
        B := by
    dsimp only [B]
    exact one_div_le_one_div_of_le
      (mul_pos (Real.sqrt_pos.2 (by norm_num)) hqStar.1) hden
  have hscaledNonneg :
      0 ≤
        Real.sqrt (N : ℝ) *
          ∫ ω,
            |(ω (supercriticalTerminalBlockLength b N)).1 -
              (ω (supercriticalTerminalBlockLength b N)).2|
            ∂(markovPathMeasure ξ (synchronousKchain A N)) := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _)
  calc
    tvDist
          (Kchain A N ∘ₘ
            ((markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockLength b N))).map Prod.fst)
          (Kchain A N ∘ₘ
            ((markovPathMeasure
              (((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalTerminalBlockStart
                        A qStar q₀ c b N))).prod (ν N : Measure ℝ))
              (synchronousKchain A N)).map
                (fun ω =>
                  ω (supercriticalTerminalBlockLength b N))).map Prod.snd) ≤
        Real.sqrt (N : ℝ) /
              (2 * Real.sqrt 2 *
                (qStar - supercriticalTerminalRadius N)) *
            ∫ ω,
              |(ω (supercriticalTerminalBlockLength b N)).1 -
                (ω (supercriticalTerminalBlockLength b N)).2|
              ∂(markovPathMeasure ξ (synchronousKchain A N)) +
          (markovPathMeasure ξ (synchronousKchain A N)).real
            {ω : ℕ → ℝ × ℝ |
              ω (supercriticalTerminalBlockLength b N) ∉
                Set.Icc
                    (qStar - supercriticalTerminalRadius N)
                    (qStar + supercriticalTerminalRadius N) ×ˢ
                  Set.Icc
                    (qStar - supercriticalTerminalRadius N)
                    (qStar + supercriticalTerminalRadius N)} := by
      simpa only [ξ, ρ] using hscore
    _ ≤
        (1 /
              (2 * Real.sqrt 2 *
                (qStar - supercriticalTerminalRadius N))) *
            (Real.sqrt (N : ℝ) *
              ∫ ω,
                |(ω (supercriticalTerminalBlockLength b N)).1 -
                  (ω (supercriticalTerminalBlockLength b N)).2|
                ∂(markovPathMeasure ξ (synchronousKchain A N))) +
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) := by
      convert add_le_add_left hbadN
        (1 /
          (2 * Real.sqrt 2 *
            (qStar - supercriticalTerminalRadius N)) *
          (Real.sqrt (N : ℝ) *
            ∫ ω,
              |(ω (supercriticalTerminalBlockLength b N)).1 -
                (ω (supercriticalTerminalBlockLength b N)).2|
              ∂(markovPathMeasure ξ (synchronousKchain A N)))) using 1 <;>
        ring
    _ ≤
        B *
            (Real.sqrt (N : ℝ) *
              ∫ ω,
                |(ω (supercriticalTerminalBlockLength b N)).1 -
                  (ω (supercriticalTerminalBlockLength b N)).2|
                ∂(markovPathMeasure ξ (synchronousKchain A N))) +
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hcoef hscaledNonneg) le_rfl
    _ ≤
        B * (D₀ * deriv (V A) qStar ^ c + ζ / (2 * B)) +
          ((4 * C + C₂) / supercriticalTerminalRadius N ^ 2) /
            (N : ℝ) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hB.le
        simpa only [ξ, ρ] using hdistanceN
      · exact le_rfl
    _ ≤
        B * (D₀ * deriv (V A) qStar ^ c + ζ / (2 * B)) +
          ζ / 2 :=
      add_le_add le_rfl hbadSmallN
    _ = (B * D₀) * deriv (V A) qStar ^ c + ζ := by
      field_simp [hB.ne']
      ring

/-- The evolving scalar law has one upper cutoff profile constant against the
invariant family for every fixed shift. -/
theorem
    exists_forall_eventually_tvDist_cutoff_marginal_invariant_le_rpow_add_of_tendsto
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
    (hb : 0 < b)
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
    ∃ D : ℝ, 0 < D ∧ ∀ ζ : ℝ, 0 < ζ → ∀ c : ℝ,
      ∀ᶠ N : ℕ in Filter.atTop,
        tvDist
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalIntegerCutoffTime A qStar q₀ N c)))
            (ν N : Measure ℝ) ≤
          D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨D, hD, hsmooth⟩ :=
    exists_forall_eventually_terminalBlock_smoothed_tvDist_le_rpow_add_of_tendsto
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb
      hC₂ hνsupport hνinv hνsq hνbound
  refine ⟨D, hD, ?_⟩
  intro ζ hζ c
  have hsmoothSlack := hsmooth ζ hζ c
  have hfst :=
    eventually_terminalBlock_smoothed_fst_eq_cutoff_marginal
      (q₀ := q₀) q ν hA hqStar hfix hb c
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

/-- One stationary scalar family and one pair of constants carry the upper
cutoff profile for every fixed shift. -/
theorem
    exists_stationary_family_forall_eventually_tvDist_cutoff_marginal_le_rpow_add_of_tendsto
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
    (hb : 0 < b) :
    ∃ C D : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < D ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ c : ℝ,
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
    exists_forall_eventually_tvDist_cutoff_marginal_invariant_le_rpow_add_of_tendsto
      q ν hA hqStar hfix hq₀ hq₀ne hq hqmem hb
      hC.le hνsupport hνinv hνsq hνbound
  exact ⟨C, D, ν, hC, hD, hν, hupper⟩

/-- The reconstructed invariant vector family has one successor-time upper
cutoff profile constant for every fixed shift. -/
theorem
    exists_reconstructed_invariant_vector_family_forall_eventually_tvDist_cutoff_succ_le_rpow_add
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
    (hb : 0 < b) :
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
      ∀ ζ : ℝ, 0 < ζ → ∀ c : ℝ,
        ∀ᶠ N : ℕ in Filter.atTop,
          tvDist
              (((Pkernel A N) ^
                (supercriticalIntegerCutoffTime A qStar q₀ N c + 1))
                (x N))
              ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ≤
            D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨C, D, ν, hC, hD, hν, hscalar⟩ :=
    exists_stationary_family_forall_eventually_tvDist_cutoff_marginal_le_rpow_add_of_tendsto
      (fun N : ℕ => radiusSq N (x N))
      hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb
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
  intro ζ hζ c
  filter_upwards [hscalar ζ hζ c] with N hscalarN
  exact
    (tvDist_Pkernel_pow_succ_le_markovPathMeasure_radius_marginal
      A N (ν N : Measure ℝ) (x N)
        (supercriticalIntegerCutoffTime A qStar q₀ N c)).trans hscalarN

/-- Shifting the real cutoff parameter down by one removes the successor in
the vector upper bound once the translated cutoff center is nonnegative. -/
lemma
    eventually_supercriticalIntegerCutoffTime_sub_one_add_one_eq
    {A qStar q₀ : ℝ}
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (c : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      supercriticalIntegerCutoffTime A qStar q₀ N (c - 1) + 1 =
        supercriticalIntegerCutoffTime A qStar q₀ N c := by
  have htranslated :
      Filter.Tendsto
        (fun N : ℕ =>
          supercriticalCutoffTime A qStar q₀ N + (c - 1))
        Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop (c - 1)
      (tendsto_supercriticalCutoffTime_atTop
        (q₀ := q₀) hA hqStar hfix)
  have hnonneg :
      ∀ᶠ N : ℕ in Filter.atTop,
        0 ≤ supercriticalCutoffTime A qStar q₀ N + (c - 1) :=
    htranslated.eventually (Filter.eventually_ge_atTop 0)
  filter_upwards [hnonneg] with N hnonnegN
  change
    ⌊supercriticalCutoffTime A qStar q₀ N + (c - 1)⌋₊ + 1 =
      ⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊
  calc
    ⌊supercriticalCutoffTime A qStar q₀ N + (c - 1)⌋₊ + 1 =
        ⌊(supercriticalCutoffTime A qStar q₀ N + (c - 1)) + 1⌋₊ :=
      (Nat.floor_add_one hnonnegN).symm
    _ = ⌊supercriticalCutoffTime A qStar q₀ N + c⌋₊ := by
      congr 1
      ring

/-- The reconstructed invariant vector family has one upper cutoff profile
constant at the integer cutoff time itself for every fixed shift. -/
theorem
    exists_reconstructed_invariant_vector_family_forall_eventually_tvDist_cutoff_le_rpow_add
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
    (hb : 0 < b) :
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
      ∀ ζ : ℝ, 0 < ζ → ∀ c : ℝ,
        ∀ᶠ N : ℕ in Filter.atTop,
          tvDist
              (((Pkernel A N) ^
                supercriticalIntegerCutoffTime A qStar q₀ N c)
                (x N))
              ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ≤
            D * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨C, D, ν, hC, hD, hν, hvector, hupper⟩ :=
    exists_reconstructed_invariant_vector_family_forall_eventually_tvDist_cutoff_succ_le_rpow_add
      x hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  let Dprofile : ℝ := D / deriv (V A) qStar
  have hDprofile : 0 < Dprofile := by
    dsimp only [Dprofile]
    exact div_pos hD hμ.1
  refine ⟨C, Dprofile, ν, hC, hDprofile, hν, hvector, ?_⟩
  intro ζ hζ c
  have hupperShift := hupper ζ hζ (c - 1)
  have htime :=
    eventually_supercriticalIntegerCutoffTime_sub_one_add_one_eq
      (q₀ := q₀) hA hqStar hfix c
  filter_upwards [hupperShift, htime] with N hupperN htimeN
  rw [htimeN] at hupperN
  calc
    tvDist
          (((Pkernel A N) ^
            supercriticalIntegerCutoffTime A qStar q₀ N c)
            (x N))
          ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ≤
        D * deriv (V A) qStar ^ (c - 1) + ζ :=
      hupperN
    _ = Dprofile * deriv (V A) qStar ^ c + ζ := by
      dsimp only [Dprofile]
      rw [Real.rpow_sub hμ.1, Real.rpow_one]
      field_simp [hμ.1.ne']

/-- Two eventually invariant scalar probability families supported on
`[0,1]` and carrying no mass at the origin are eventually equal. -/
lemma eventually_eq_of_invariant_Kchain_family_apply_singleton_zero
    {A : ℝ} (ν ρ : ℕ → ProbabilityMeasure ℝ)
    (hA : 0 < A)
    (hν :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0)
    (hρ :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ρ N : Measure ℝ) ∧
        (ρ N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ρ N : Measure ℝ) ({0} : Set ℝ) = 0) :
    ∀ᶠ N : ℕ in Filter.atTop, ν N = ρ N := by
  filter_upwards
      [hν, hρ, Filter.eventually_ge_atTop (1 : ℕ)] with
      N hνN hρN hN
  apply ProbabilityMeasure.toMeasure_injective
  have hν0lt : (ν N : Measure ℝ) ({0} : Set ℝ) < 1 := by
    rw [hνN.2.2]
    exact zero_lt_one
  have hρ0lt : (ρ N : Measure ℝ) ({0} : Set ℝ) < 1 := by
    rw [hρN.2.2]
    exact zero_lt_one
  have hparts :=
    nonzeroPart_eq_of_invariant_Kchain hA
      (show 0 < N by omega)
      (ν N : Measure ℝ) (ρ N : Measure ℝ)
      hνN.1 hρN.1 hνN.2.1 hρN.2.1 hν0lt hρ0lt
  rw [nonzeroPart_eq_self_of_apply_singleton_zero _ hνN.2.2,
    nonzeroPart_eq_self_of_apply_singleton_zero _ hρN.2.2] at hparts
  exact hparts

/-- One reconstructed invariant vector family carries both fixed-shift
cutoff profiles, with every constant selected before the shift. -/
theorem
    exists_reconstructed_invariant_vector_family_forall_eventually_two_sided_tvDist_cutoff_profile
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
    (hb : 0 < b) :
    ∃ C Dlower Dupper : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < Dlower ∧ 0 < Dupper ∧
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
      (∀ c : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
        1 - Dlower * deriv (V A) qStar ^ (-(2 * c)) ≤
          tvDist
            (((Pkernel A N) ^
              supercriticalIntegerCutoffTime A qStar q₀ N c)
                (x N))
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))) ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ c : ℝ,
        ∀ᶠ N : ℕ in Filter.atTop,
          tvDist
              (((Pkernel A N) ^
                supercriticalIntegerCutoffTime A qStar q₀ N c)
                (x N))
              ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)) ≤
            Dupper * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨Clower, Dlower, νlower, hClower, hDlower,
      hνlower, hvectorLower, hlower⟩ :=
    exists_reconstructed_invariant_vector_family_forall_eventually_one_sub_mul_rpow_le_tvDist_cutoff
      x hA hqStar hfix hq₀ hq₀ne hradius hradiusMem
  obtain ⟨Cupper, Dupper, νupper, hCupper, hDupper,
      hνupper, hvectorUpper, hupper⟩ :=
    exists_reconstructed_invariant_vector_family_forall_eventually_tvDist_cutoff_le_rpow_add
      x hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb
  have hνlowerCore :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (νlower N : Measure ℝ) ∧
        (νlower N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (νlower N : Measure ℝ) ({0} : Set ℝ) = 0 :=
    hνlower.mono fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.1⟩
  have hνupperCore :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (νupper N : Measure ℝ) ∧
        (νupper N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (νupper N : Measure ℝ) ({0} : Set ℝ) = 0 :=
    hνupper.mono fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.1⟩
  have heq :
      ∀ᶠ N : ℕ in Filter.atTop, νlower N = νupper N :=
    eventually_eq_of_invariant_Kchain_family_apply_singleton_zero
      νlower νupper (zero_lt_one.trans hA)
      hνlowerCore hνupperCore
  have hlowerUpper :
      ∀ c : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
        1 - Dlower * deriv (V A) qStar ^ (-(2 * c)) ≤
          tvDist
            (((Pkernel A N) ^
              supercriticalIntegerCutoffTime A qStar q₀ N c)
                (x N))
            ((Jkernel A N) ∘ₘ (νupper N : Measure ℝ)) := by
    intro c
    filter_upwards [hlower c, heq] with N hlowerN heqN
    rw [heqN] at hlowerN
    exact hlowerN
  exact
    ⟨Cupper, Dlower, Dupper, νupper,
      hCupper, hDlower, hDupper,
      hνupper, hvectorUpper, hlowerUpper, hupper⟩

/-- The two-sided eventual profile gives fixed-shift inner liminf and limsup
bounds against the same reconstructed invariant family. -/
theorem
    exists_reconstructed_invariant_vector_family_forall_liminf_limsup_tvDist_cutoff_profile
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
    (hb : 0 < b) :
    ∃ C Dlower Dupper : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < Dlower ∧ 0 < Dupper ∧
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
      (∀ c : ℝ,
        1 - Dlower * deriv (V A) qStar ^ (-(2 * c)) ≤
          Filter.liminf
            (fun N : ℕ =>
              tvDist
                (((Pkernel A N) ^
                  supercriticalIntegerCutoffTime A qStar q₀ N c)
                    (x N))
                ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)))
            Filter.atTop) ∧
      ∀ c : ℝ,
        Filter.limsup
            (fun N : ℕ =>
              tvDist
                (((Pkernel A N) ^
                  supercriticalIntegerCutoffTime A qStar q₀ N c)
                    (x N))
                ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)))
            Filter.atTop ≤
          Dupper * deriv (V A) qStar ^ c := by
  obtain ⟨C, Dlower, Dupper, ν, hC, hDlower, hDupper,
      hν, hvector, hlower, hupper⟩ :=
    exists_reconstructed_invariant_vector_family_forall_eventually_two_sided_tvDist_cutoff_profile
      x hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb
  let d : ℝ → ℕ → ℝ := fun c N =>
    tvDist
      (((Pkernel A N) ^
        supercriticalIntegerCutoffTime A qStar q₀ N c) (x N))
      ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
  have hdNonneg (c : ℝ) :
      ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ d c N :=
    Filter.Eventually.of_forall fun N => by
      dsimp only [d]
      exact tvDist_nonneg _ _
  have hdLeOne (c : ℝ) :
      ∀ᶠ N : ℕ in Filter.atTop, d c N ≤ 1 :=
    Filter.Eventually.of_forall fun N => by
      dsimp only [d]
      exact tvDist_le_one _ _
  have hlowerLimit :
      ∀ c : ℝ,
        1 - Dlower * deriv (V A) qStar ^ (-(2 * c)) ≤
          Filter.liminf (d c) Filter.atTop := by
    intro c
    exact Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_eventually_le
        Filter.atTop (hdLeOne c))
      (hlower c)
  have hupperLimit :
      ∀ c : ℝ,
        Filter.limsup (d c) Filter.atTop ≤
          Dupper * deriv (V A) qStar ^ c := by
    intro c
    apply le_of_forall_pos_le_add
    intro ζ hζ
    exact Filter.limsup_le_of_le
      (Filter.isCoboundedUnder_le_of_eventually_le
        Filter.atTop (hdNonneg c))
      (hupper ζ hζ c)
  exact
    ⟨C, Dlower, Dupper, ν, hC, hDlower, hDupper,
      hν, hvector, hlowerLimit, hupperLimit⟩

/-- The inner cutoff profiles converge to one on the early side and zero on
the late side of the cutoff window. -/
theorem
    exists_reconstructed_invariant_vector_family_tendsto_outer_tvDist_cutoff_profile
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
    (hb : 0 < b) :
    ∃ C Dlower Dupper : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < Dlower ∧ 0 < Dupper ∧
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
      Filter.Tendsto
        (fun c : ℝ =>
          Filter.liminf
            (fun N : ℕ =>
              tvDist
                (((Pkernel A N) ^
                  supercriticalIntegerCutoffTime A qStar q₀ N (-c))
                    (x N))
                ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)))
            Filter.atTop)
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun c : ℝ =>
          Filter.limsup
            (fun N : ℕ =>
              tvDist
                (((Pkernel A N) ^
                  supercriticalIntegerCutoffTime A qStar q₀ N c)
                    (x N))
                ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)))
            Filter.atTop)
        Filter.atTop (nhds 0) := by
  obtain ⟨C, Dlower, Dupper, ν, hC, hDlower, hDupper,
      hν, hvector, hlower, hupper⟩ :=
    exists_reconstructed_invariant_vector_family_forall_liminf_limsup_tvDist_cutoff_profile
      x hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb
  let d : ℝ → ℕ → ℝ := fun c N =>
    tvDist
      (((Pkernel A N) ^
        supercriticalIntegerCutoffTime A qStar q₀ N c) (x N))
      ((Jkernel A N) ∘ₘ (ν N : Measure ℝ))
  have hdNonneg (c : ℝ) :
      ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ d c N :=
    Filter.Eventually.of_forall fun N => by
      dsimp only [d]
      exact tvDist_nonneg _ _
  have hdLeOne (c : ℝ) :
      ∀ᶠ N : ℕ in Filter.atTop, d c N ≤ 1 :=
    Filter.Eventually.of_forall fun N => by
      dsimp only [d]
      exact tvDist_le_one _ _
  have hliminfLeOne (c : ℝ) :
      Filter.liminf (d c) Filter.atTop ≤ 1 :=
    Filter.liminf_le_of_frequently_le
      (hdLeOne c).frequently ⟨0, hdNonneg c⟩
  have hlimsupNonneg (c : ℝ) :
      0 ≤ Filter.limsup (d c) Filter.atTop :=
    Filter.le_limsup_of_frequently_le
      (hdNonneg c).frequently ⟨1, hdLeOne c⟩
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hμPow :
      Filter.Tendsto
        (fun c : ℝ => deriv (V A) qStar ^ c)
        Filter.atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one
      (deriv (V A) qStar) (by linarith [hμ.1]) hμ.2
  have htwice :
      Filter.Tendsto (fun c : ℝ => 2 * c)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have hμPowTwice :
      Filter.Tendsto
        (fun c : ℝ => deriv (V A) qStar ^ (2 * c))
        Filter.atTop (nhds 0) :=
    hμPow.comp htwice
  have hlowerEnvelope :
      Filter.Tendsto
        (fun c : ℝ =>
          1 - Dlower * deriv (V A) qStar ^ (2 * c))
        Filter.atTop (nhds 1) := by
    simpa only [mul_zero, sub_zero] using
      tendsto_const_nhds.sub (hμPowTwice.const_mul Dlower)
  have hlowerBound (c : ℝ) :
      1 - Dlower * deriv (V A) qStar ^ (2 * c) ≤
        Filter.liminf (d (-c)) Filter.atTop := by
    simpa only [mul_neg, neg_neg] using hlower (-c)
  have hlowerOuter :
      Filter.Tendsto
        (fun c : ℝ => Filter.liminf (d (-c)) Filter.atTop)
        Filter.atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlowerEnvelope tendsto_const_nhds
      (Filter.Eventually.of_forall hlowerBound)
      (Filter.Eventually.of_forall fun c => hliminfLeOne (-c))
  have hupperOuter :
      Filter.Tendsto
        (fun c : ℝ => Filter.limsup (d c) Filter.atTop)
        Filter.atTop (nhds 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall hlimsupNonneg)
      (Filter.Eventually.of_forall hupper)
      (by simpa only [mul_zero] using hμPow.const_mul Dupper)
  exact
    ⟨C, Dlower, Dupper, ν, hC, hDlower, hDupper,
      hν, hvector, hlowerOuter, hupperOuter⟩

/-- The reconstructed invariant vector family exhibits total-variation
cutoff at the supercritical center with constant window one. -/
theorem
    exists_reconstructed_invariant_vector_family_hasCutoff
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
    (hb : 0 < b) :
    ∃ C : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧
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
      HasCutoff
        (fun N t =>
          tvDist (((Pkernel A N) ^ t) (x N))
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  obtain ⟨C, Dlower, Dupper, ν, hC, hDlower, hDupper,
      hν, hvector, hearly, hlate⟩ :=
    exists_reconstructed_invariant_vector_family_tendsto_outer_tvDist_cutoff_profile
      x hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb
  refine ⟨C, ν, hC, hν, hvector, ?_⟩
  refine ⟨isCutoffWindow_supercriticalCutoffTime_one hA hqStar hfix, ?_⟩
  simpa only [HasCutoffLimits, supercriticalIntegerCutoffTime_eq,
    mul_one, sub_eq_add_neg] using And.intro hearly hlate

/-- A vector whose coordinates lie in `[-1,1]` has normalized squared radius
at most one. -/
lemma radiusSq_le_one_of_forall_mem_Icc
    {N : ℕ} (x : Fin N → ℝ)
    (hx : ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) :
    radiusSq N x ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp [radiusSq]
  have hsum :
      ∑ i, (x i) ^ 2 ≤ (N : ℝ) := by
    calc
      ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _hi
        nlinarith [(hx i).1, (hx i).2]
      _ = (N : ℝ) := by simp
  calc
    radiusSq N x =
        (N : ℝ)⁻¹ * ∑ i, (x i) ^ 2 := rfl
    _ ≤ (N : ℝ)⁻¹ * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN)

/-- Radius convergence to a positive limit and an eventual coordinate-box
bound imply the eventual scalar state-space hypothesis. -/
lemma eventually_radiusSq_mem_Ioc_of_tendsto_of_forall_mem_Icc
    {q₀ : ℝ} (x : (N : ℕ) → Fin N → ℝ)
    (hq₀ : 0 < q₀)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀))
    (hbox :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ i, x N i ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      radiusSq N (x N) ∈ Set.Ioc (0 : ℝ) 1 := by
  have hpositive :
      ∀ᶠ N : ℕ in Filter.atTop, 0 < radiusSq N (x N) :=
    hradius (Ioi_mem_nhds hq₀)
  filter_upwards [hpositive, hbox] with N hpositiveN hboxN
  exact ⟨hpositiveN, radiusSq_le_one_of_forall_mem_Icc (x N) hboxN⟩

/-- Under the manuscript's coordinate-box and radius-convergence assumptions,
the vector chain has supercritical total-variation cutoff with window one. -/
theorem
    exists_reconstructed_invariant_vector_family_hasCutoff_of_forall_mem_Icc
    {A qStar q₀ b : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hbox :
      ∀ N : ℕ, ∀ i, x N i ∈ Set.Icc (-1 : ℝ) 1)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀))
    (hb : 0 < b) :
    ∃ C : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧
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
      HasCutoff
        (fun N t =>
          tvDist (((Pkernel A N) ^ t) (x N))
            ((Jkernel A N) ∘ₘ (ν N : Measure ℝ)))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  have hradiusMem :
      ∀ᶠ N : ℕ in Filter.atTop,
        radiusSq N (x N) ∈ Set.Ioc (0 : ℝ) 1 :=
    eventually_radiusSq_mem_Ioc_of_tendsto_of_forall_mem_Icc
      x hq₀.1 hradius
        (Filter.Eventually.of_forall fun N => hbox N)
  exact
    exists_reconstructed_invariant_vector_family_hasCutoff
      x hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb

/-- Under the manuscript's coordinate-box and radius-convergence assumptions,
the vector chain has a unique nonzero invariant probability in every sufficiently
large dimension and has supercritical total-variation cutoff with window one
against that family. -/
theorem
    exists_unique_nonzero_invariant_vector_family_cutoff_of_forall_mem_Icc
    {A qStar q₀ : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hbox :
      ∀ N : ℕ, ∀ i, x N i ∈ Set.Icc (-1 : ℝ) 1)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀)) :
    ∃ π : (N : ℕ) → ProbabilityMeasure (Fin N → ℝ),
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant
            (Pkernel A N) (π N : Measure (Fin N → ℝ)) ∧
          (π N : Measure (Fin N → ℝ))
              ({0} : Set (Fin N → ℝ)) = 0 ∧
          ∀ ρ : ProbabilityMeasure (Fin N → ℝ),
            Kernel.Invariant
                (Pkernel A N) (ρ : Measure (Fin N → ℝ)) →
            (ρ : Measure (Fin N → ℝ))
                ({0} : Set (Fin N → ℝ)) = 0 →
            ρ = π N) ∧
      HasCutoff
        (fun N t =>
          tvDist (((Pkernel A N) ^ t) (x N))
            (π N : Measure (Fin N → ℝ)))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  obtain ⟨C, ν, hC, hν, hvector, hcutoff⟩ :=
    exists_reconstructed_invariant_vector_family_hasCutoff_of_forall_mem_Icc
      (b := 1) x hA hqStar hfix hq₀ hq₀ne hbox hradius (by norm_num)
  let π : (N : ℕ) → ProbabilityMeasure (Fin N → ℝ) := fun N =>
    ⟨(Jkernel A N) ∘ₘ (ν N : Measure ℝ), inferInstance⟩
  refine ⟨π, ?_, ?_⟩
  · filter_upwards [hvector, Filter.eventually_atTop.2 ⟨1, fun _ hN => hN⟩]
      with N hvectorN hN
    refine ⟨hvectorN.1, hvectorN.2, ?_⟩
    intro ρ hρ hρ0
    apply ProbabilityMeasure.toMeasure_injective
    exact invariant_probability_unique_Pkernel_of_apply_singleton_zero
      (zero_lt_one.trans hA) (Nat.zero_lt_of_lt hN)
      (ρ : Measure (Fin N → ℝ)) (π N : Measure (Fin N → ℝ))
      hρ hvectorN.1 hρ0 hvectorN.2
  · simpa [π] using hcutoff

/-- One origin-free invariant scalar family carries both fixed-shift cutoff
profiles, with every constant selected before the shift. -/
theorem
    exists_stationary_family_forall_eventually_two_sided_tvDist_cutoff_profile
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
    (hb : 0 < b) :
    ∃ C Dlower Dupper : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < Dlower ∧ 0 < Dupper ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      (∀ c : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
        1 - Dlower * deriv (V A) qStar ^ (-(2 * c)) ≤
          tvDist
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalIntegerCutoffTime A qStar q₀ N c)))
            (ν N : Measure ℝ)) ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ c : ℝ,
        ∀ᶠ N : ℕ in Filter.atTop,
          tvDist
              ((markovPathMeasure
                (Measure.dirac (q N)) (Kchain A N)).map
                  (fun ω =>
                    ω (supercriticalIntegerCutoffTime A qStar q₀ N c)))
              (ν N : Measure ℝ) ≤
            Dupper * deriv (V A) qStar ^ c + ζ := by
  obtain ⟨Clower, Dlower, νlower, hClower, hDlower,
      hνlower, hlower⟩ :=
    exists_stationary_family_forall_eventually_one_sub_mul_rpow_le_tvDist_cutoff_marginal
      q hA hqStar hfix hq₀ hq₀ne hq hqmem
  obtain ⟨Cupper, Dupper, νupper, hCupper, hDupper,
      hνupper, hupper⟩ :=
    exists_stationary_family_forall_eventually_tvDist_cutoff_marginal_le_rpow_add_of_tendsto
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb
  have hνlowerCore :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (νlower N : Measure ℝ) ∧
        (νlower N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (νlower N : Measure ℝ) ({0} : Set ℝ) = 0 :=
    hνlower.mono fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.1⟩
  have hνupperCore :
      ∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (νupper N : Measure ℝ) ∧
        (νupper N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (νupper N : Measure ℝ) ({0} : Set ℝ) = 0 :=
    hνupper.mono fun _ hN => ⟨hN.1, hN.2.1, hN.2.2.1⟩
  have heq :
      ∀ᶠ N : ℕ in Filter.atTop, νlower N = νupper N :=
    eventually_eq_of_invariant_Kchain_family_apply_singleton_zero
      νlower νupper (zero_lt_one.trans hA)
      hνlowerCore hνupperCore
  have hlowerUpper :
      ∀ c : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
        1 - Dlower * deriv (V A) qStar ^ (-(2 * c)) ≤
          tvDist
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalIntegerCutoffTime A qStar q₀ N c)))
            (νupper N : Measure ℝ) := by
    intro c
    filter_upwards [hlower c, heq] with N hlowerN heqN
    rw [heqN] at hlowerN
    exact hlowerN
  exact
    ⟨Cupper, Dlower, Dupper, νupper,
      hCupper, hDlower, hDupper, hνupper, hlowerUpper, hupper⟩

/-- The scalar inner cutoff profiles converge to one on the early side and
zero on the late side of the cutoff window. -/
theorem
    exists_stationary_family_tendsto_outer_tvDist_cutoff_profile
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
    (hb : 0 < b) :
    ∃ C Dlower Dupper : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧ 0 < Dlower ∧ 0 < Dupper ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      Filter.Tendsto
        (fun c : ℝ =>
          Filter.liminf
            (fun N : ℕ =>
              tvDist
                ((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalIntegerCutoffTime
                        A qStar q₀ N (-c))))
                (ν N : Measure ℝ))
            Filter.atTop)
        Filter.atTop (nhds 1) ∧
      Filter.Tendsto
        (fun c : ℝ =>
          Filter.limsup
            (fun N : ℕ =>
              tvDist
                ((markovPathMeasure
                  (Measure.dirac (q N)) (Kchain A N)).map
                    (fun ω =>
                      ω (supercriticalIntegerCutoffTime
                        A qStar q₀ N c)))
                (ν N : Measure ℝ))
            Filter.atTop)
        Filter.atTop (nhds 0) := by
  obtain ⟨C, Dlower, Dupper, ν, hC, hDlower, hDupper,
      hν, hlower, hupper⟩ :=
    exists_stationary_family_forall_eventually_two_sided_tvDist_cutoff_profile
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb
  let d : ℝ → ℕ → ℝ := fun c N =>
    tvDist
      ((markovPathMeasure
        (Measure.dirac (q N)) (Kchain A N)).map
          (fun ω =>
            ω (supercriticalIntegerCutoffTime A qStar q₀ N c)))
      (ν N : Measure ℝ)
  have hdNonneg (c : ℝ) :
      ∀ᶠ N : ℕ in Filter.atTop, 0 ≤ d c N :=
    Filter.Eventually.of_forall fun N => by
      dsimp only [d]
      exact tvDist_nonneg _ _
  have hdLeOne (c : ℝ) :
      ∀ᶠ N : ℕ in Filter.atTop, d c N ≤ 1 :=
    Filter.Eventually.of_forall fun N => by
      letI :
          IsProbabilityMeasure
            ((markovPathMeasure
              (Measure.dirac (q N)) (Kchain A N)).map
                (fun ω =>
                  ω (supercriticalIntegerCutoffTime
                    A qStar q₀ N c))) :=
        Measure.isProbabilityMeasure_map
          (measurable_pi_apply
            (supercriticalIntegerCutoffTime
              A qStar q₀ N c)).aemeasurable
      dsimp only [d]
      exact tvDist_le_one _ _
  have hlowerLimit :
      ∀ c : ℝ,
        1 - Dlower * deriv (V A) qStar ^ (-(2 * c)) ≤
          Filter.liminf (d c) Filter.atTop := by
    intro c
    exact Filter.le_liminf_of_le
      (Filter.isCoboundedUnder_ge_of_eventually_le
        Filter.atTop (hdLeOne c))
      (hlower c)
  have hupperLimit :
      ∀ c : ℝ,
        Filter.limsup (d c) Filter.atTop ≤
          Dupper * deriv (V A) qStar ^ c := by
    intro c
    apply le_of_forall_pos_le_add
    intro ζ hζ
    exact Filter.limsup_le_of_le
      (Filter.isCoboundedUnder_le_of_eventually_le
        Filter.atTop (hdNonneg c))
      (hupper ζ hζ c)
  have hliminfLeOne (c : ℝ) :
      Filter.liminf (d c) Filter.atTop ≤ 1 :=
    Filter.liminf_le_of_frequently_le
      (hdLeOne c).frequently ⟨0, hdNonneg c⟩
  have hlimsupNonneg (c : ℝ) :
      0 ≤ Filter.limsup (d c) Filter.atTop :=
    Filter.le_limsup_of_frequently_le
      (hdNonneg c).frequently ⟨1, hdLeOne c⟩
  have hμ :=
    V_multiplier_mem_Ioo
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix
  have hμPow :
      Filter.Tendsto
        (fun c : ℝ => deriv (V A) qStar ^ c)
        Filter.atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one
      (deriv (V A) qStar) (by linarith [hμ.1]) hμ.2
  have htwice :
      Filter.Tendsto (fun c : ℝ => 2 * c)
        Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have hμPowTwice :
      Filter.Tendsto
        (fun c : ℝ => deriv (V A) qStar ^ (2 * c))
        Filter.atTop (nhds 0) :=
    hμPow.comp htwice
  have hlowerEnvelope :
      Filter.Tendsto
        (fun c : ℝ =>
          1 - Dlower * deriv (V A) qStar ^ (2 * c))
        Filter.atTop (nhds 1) := by
    simpa only [mul_zero, sub_zero] using
      tendsto_const_nhds.sub (hμPowTwice.const_mul Dlower)
  have hlowerBound (c : ℝ) :
      1 - Dlower * deriv (V A) qStar ^ (2 * c) ≤
        Filter.liminf (d (-c)) Filter.atTop := by
    simpa only [mul_neg, neg_neg] using hlowerLimit (-c)
  have hlowerOuter :
      Filter.Tendsto
        (fun c : ℝ => Filter.liminf (d (-c)) Filter.atTop)
        Filter.atTop (nhds 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlowerEnvelope tendsto_const_nhds
      (Filter.Eventually.of_forall hlowerBound)
      (Filter.Eventually.of_forall fun c => hliminfLeOne (-c))
  have hupperOuter :
      Filter.Tendsto
        (fun c : ℝ => Filter.limsup (d c) Filter.atTop)
        Filter.atTop (nhds 0) :=
    squeeze_zero'
      (Filter.Eventually.of_forall hlimsupNonneg)
      (Filter.Eventually.of_forall hupperLimit)
      (by simpa only [mul_zero] using hμPow.const_mul Dupper)
  exact
    ⟨C, Dlower, Dupper, ν, hC, hDlower, hDupper,
      hν, hlowerOuter, hupperOuter⟩

/-- The origin-free invariant scalar family exhibits total-variation cutoff
at the supercritical center with constant window one. -/
theorem
    exists_stationary_family_hasCutoff
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
    (hb : 0 < b) :
    ∃ C : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun x => (x - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ x, (x - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      HasCutoff
        (fun N t =>
          tvDist (((Kchain A N) ^ t) (q N))
            (ν N : Measure ℝ))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  obtain ⟨C, Dlower, Dupper, ν, hC, hDlower, hDupper,
      hν, hearly, hlate⟩ :=
    exists_stationary_family_tendsto_outer_tvDist_cutoff_profile
      q hA hqStar hfix hq₀ hq₀ne hq hqmem hb
  refine ⟨C, ν, hC, hν, ?_⟩
  refine ⟨isCutoffWindow_supercriticalCutoffTime_one hA hqStar hfix, ?_⟩
  simpa only [HasCutoffLimits, supercriticalIntegerCutoffTime_eq,
    mul_one, sub_eq_add_neg, markovPathMeasure_dirac_map_eval] using
    And.intro hearly hlate

/-- Under the manuscript's coordinate-box and radius-convergence assumptions,
the scalar squared-radius chain has supercritical total-variation cutoff with
window one. -/
theorem
    exists_stationary_family_hasCutoff_of_forall_mem_Icc
    {A qStar q₀ b : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hbox :
      ∀ N : ℕ, ∀ i, x N i ∈ Set.Icc (-1 : ℝ) 1)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀))
    (hb : 0 < b) :
    ∃ C : ℝ, ∃ ν : ℕ → ProbabilityMeasure ℝ,
      0 < C ∧
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun q => (q - qStar) ^ 2) (ν N : Measure ℝ) ∧
        (∫ q, (q - qStar) ^ 2 ∂(ν N : Measure ℝ)) ≤
          C / (N : ℝ)) ∧
      HasCutoff
        (fun N t =>
          tvDist
            (((Kchain A N) ^ t) (radiusSq N (x N)))
            (ν N : Measure ℝ))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  have hradiusMem :
      ∀ᶠ N : ℕ in Filter.atTop,
        radiusSq N (x N) ∈ Set.Ioc (0 : ℝ) 1 :=
    eventually_radiusSq_mem_Ioc_of_tendsto_of_forall_mem_Icc
      x hq₀.1 hradius
        (Filter.Eventually.of_forall fun N => hbox N)
  exact
    exists_stationary_family_hasCutoff
      (fun N => radiusSq N (x N))
      hA hqStar hfix hq₀ hq₀ne hradius hradiusMem hb

/-- Under the manuscript's coordinate-box and radius-convergence assumptions,
the scalar squared-radius chain has a unique origin-free invariant law in every
sufficiently large dimension, and cutoff relative to those laws. This is the
paper-facing form of `exists_stationary_family_hasCutoff_of_forall_mem_Icc`;
the latter additionally records support and variance estimates used in its
proof. -/
theorem
    exists_eventually_unique_nonzero_invariant_family_hasCutoff_of_forall_mem_Icc
    {A qStar q₀ : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hbox :
      ∀ N : ℕ, ∀ i, x N i ∈ Set.Icc (-1 : ℝ) 1)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀)) :
    ∃ ν : ℕ → ProbabilityMeasure ℝ,
      (∀ᶠ N : ℕ in Filter.atTop,
        Kernel.Invariant (Kchain A N) (ν N : Measure ℝ) ∧
        (ν N : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        ∀ ρ : ProbabilityMeasure ℝ,
          Kernel.Invariant (Kchain A N) (ρ : Measure ℝ) →
          (ρ : Measure ℝ) ({0} : Set ℝ) = 0 →
          ρ = ν N) ∧
      HasCutoff
        (fun N t =>
          tvDist
            (((Kchain A N) ^ t) (radiusSq N (x N)))
            (ν N : Measure ℝ))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  obtain ⟨C, ν, hC, hν, hcutoff⟩ :=
    exists_stationary_family_hasCutoff_of_forall_mem_Icc
      (b := 1) x hA hqStar hfix hq₀ hq₀ne hbox hradius zero_lt_one
  refine ⟨ν, ?_, hcutoff⟩
  filter_upwards [hν, Filter.eventually_gt_atTop 0] with N hνN hN
  refine ⟨hνN.1, hνN.2.2.1, ?_⟩
  intro ρ hρ hρ0
  exact invariant_probability_unique_Kchain_of_apply_singleton_zero
    (zero_lt_one.trans hA) hN ρ (ν N) hρ hνN.1 hρ0 hνN.2.2.1

/-- Paper-facing scalar cutoff theorem. In every sufficiently large dimension,
`ν N` is characterized as the unique probability law that is both nonzero and
invariant for `Kchain A N`; cutoff holds relative to this same family. -/
theorem
    exists_unique_nonzero_invariant_family_hasCutoff_of_forall_mem_Icc
    {A qStar q₀ : ℝ}
    (x : (N : ℕ) → Fin N → ℝ)
    (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar)
    (hbox :
      ∀ N : ℕ, ∀ i, x N i ∈ Set.Icc (-1 : ℝ) 1)
    (hradius :
      Filter.Tendsto
        (fun N : ℕ => radiusSq N (x N))
        Filter.atTop (nhds q₀)) :
    ∃ ν : ℕ → ProbabilityMeasure ℝ,
      (∀ᶠ N : ℕ in Filter.atTop, ∀ ρ : ProbabilityMeasure ℝ,
        ((ρ : Measure ℝ) ({0} : Set ℝ) = 0 ∧
          Kernel.Invariant (Kchain A N) (ρ : Measure ℝ)) ↔
        ρ = ν N) ∧
      HasCutoff
        (fun N t =>
          tvDist
            (((Kchain A N) ^ t) (radiusSq N (x N)))
            (ν N : Measure ℝ))
        (supercriticalCutoffTime A qStar q₀)
        (fun _ => 1) := by
  obtain ⟨ν, hν, hcutoff⟩ :=
    exists_eventually_unique_nonzero_invariant_family_hasCutoff_of_forall_mem_Icc
      x hA hqStar hfix hq₀ hq₀ne hbox hradius
  refine ⟨ν, ?_, hcutoff⟩
  filter_upwards [hν] with N hνN
  intro ρ
  constructor
  · rintro ⟨hρ0, hρ⟩
    exact hνN.2.2 ρ hρ hρ0
  · rintro rfl
    exact ⟨hνN.2.1, hνN.1⟩

end AbsorptionCutoff
