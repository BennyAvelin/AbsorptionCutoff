/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Chains
import AbsorptionCutoff.OrbitAmplification
import AbsorptionCutoff.MarkovTrajectory
import AbsorptionCutoff.StoppedMoment

/-!
# Fixed-precision radius concentration

Begins the paper's `prop:subcritical-exact-radius-concentration`.  The scalar
observable below is one coordinate's contribution to the rounded squared-radius
transition.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace AbsorptionCutoff

/-- The paper's one-coordinate rounded squared-radius observable
`U_{A,ρ}(h,g) = Q₁(ρ⁻¹ tanh(ρ A √h g))²`. -/
noncomputable def roundedCoordinateObservable
    (A ρ h g : ℝ) : ℝ :=
  ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) : ℤ) : ℝ) ^ 2

/-- The squared radius of a deterministic vector after rescaling by the grid
width and rounding to the unit lattice. -/
noncomputable def roundedInitialRadius
    (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, ((Q₁ (x i / ρ) : ℤ) : ℝ) ^ 2

/-- The deterministic rounded initial radius is nonnegative. -/
lemma roundedInitialRadius_nonneg (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    0 ≤ roundedInitialRadius ρ N x := by
  unfold roundedInitialRadius
  positivity

/-- The paper's deterministic initial-radius bound for vectors with coordinates
in `[-1,1]`. -/
lemma roundedInitialRadius_le_sq
    {ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N)
    {x : Fin N → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    roundedInitialRadius ρ N x ≤ (ρ⁻¹ + 1 / 2) ^ 2 := by
  have hρinv : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρ.le
  have hcoord : ∀ i : Fin N,
      |((Q₁ (x i / ρ) : ℤ) : ℝ)| ≤ ρ⁻¹ + 1 / 2 := by
    intro i
    calc
      |((Q₁ (x i / ρ) : ℤ) : ℝ)| ≤ |x i / ρ| + 1 / 2 :=
        by
          convert abs_Q₁_le (x i / ρ) using 1
          norm_num
      _ = |x i| * ρ⁻¹ + 1 / 2 := by
        rw [abs_div, abs_of_pos hρ]
        field_simp
      _ ≤ ρ⁻¹ + 1 / 2 := by
        have hmul : |x i| * ρ⁻¹ ≤ ρ⁻¹ := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (hx i) hρinv
        linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hNinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hNreal.le
  unfold roundedInitialRadius
  calc
    (N : ℝ)⁻¹ * ∑ i, ((Q₁ (x i / ρ) : ℤ) : ℝ) ^ 2 ≤
      (N : ℝ)⁻¹ * ∑ _i : Fin N, (ρ⁻¹ + 1 / 2) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hNinv
      apply Finset.sum_le_sum
      intro i hi
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
    _ = (ρ⁻¹ + 1 / 2) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hNreal.ne']

/-- The deterministic initial-radius bound in the exact form displayed in the
paper. -/
lemma roundedInitialRadius_le_paper
    {ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N)
    {x : Fin N → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    roundedInitialRadius ρ N x ≤ (1 + ρ / 2) ^ 2 / ρ ^ 2 := by
  calc
    roundedInitialRadius ρ N x ≤ (ρ⁻¹ + 1 / 2) ^ 2 :=
      roundedInitialRadius_le_sq hρ hN hx
    _ = (1 + ρ / 2) ^ 2 / ρ ^ 2 := by
      field_simp [hρ.ne']

/-- The error between the canonical stochastic radius and its deterministic
rounded-mean-map orbit. -/
noncomputable def radiusTrackingError
    (A ρ h₀ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ω t - roundedOrbit A ρ h₀ t

/-- The centered one-step innovation of the canonical rounded radius chain. -/
noncomputable def radiusNoise
    (A ρ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ω (t + 1) - roundedMeanMap A ρ (ω t)

/-- The radius-tracking error normalized by the deterministic orbit and a
positive terminal scale. -/
noncomputable def normalizedRadiusError
    (A ρ h₀ a : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  radiusTrackingError A ρ h₀ t ω / (roundedOrbit A ρ h₀ t + a)

/-- The paper's difference quotient for the rounded mean map, with the
derivative used when the stochastic and deterministic radii coincide. -/
noncomputable def radiusDifferenceQuotient
    (A ρ h₀ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  if radiusTrackingError A ρ h₀ t ω ≠ 0 then
    (roundedMeanMap A ρ (ω t) -
      roundedMeanMap A ρ (roundedOrbit A ρ h₀ t)) /
      radiusTrackingError A ρ h₀ t ω
  else
    deriv (roundedMeanMap A ρ) (roundedOrbit A ρ h₀ t)

/-- The one-step innovation normalized at the current deterministic orbit
scale. -/
noncomputable def normalizedRadiusNoise
    (A ρ h₀ a : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  radiusNoise A ρ t ω / (roundedOrbit A ρ h₀ t + a)

/-- The normalized multiplier obtained from the rounded-map difference
quotient and the deterministic one-step radius ratio. -/
noncomputable def radiusNormalizedMultiplier
    (A ρ h₀ a : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  radiusDifferenceQuotient A ρ h₀ t ω *
    roundedBeta A ρ a (roundedOrbit A ρ h₀ t)

/-- The event that the stochastic radius tracks its deterministic orbit at a
given time within relative tolerance `δ`. -/
def radiusTrackingGood
    (A ρ h₀ a δ : ℝ) (t : ℕ) (ω : ℕ → ℝ) : Prop :=
  |radiusTrackingError A ρ h₀ t ω| ≤
    δ * (roundedOrbit A ρ h₀ t + a)

/-- The first bad tracking index through horizon `T`, capped by the sentinel
`T+1` when no bad index occurs. -/
noncomputable def radiusTrackingExitTime
    (A ρ h₀ a δ : ℝ) (T : ℕ) (ω : ℕ → ℝ) : ℕ :=
  sInf ({t : ℕ | t ≤ T ∧ ¬radiusTrackingGood A ρ h₀ a δ t ω} ∪ {T + 1})

/-- The capped tracking exit time never exceeds its sentinel value. -/
lemma radiusTrackingExitTime_le_sentinel
    (A ρ h₀ a δ : ℝ) (T : ℕ) (ω : ℕ → ℝ) :
    radiusTrackingExitTime A ρ h₀ a δ T ω ≤ T + 1 := by
  unfold radiusTrackingExitTime
  exact Nat.sInf_le
    (Set.mem_union_right _ (Set.mem_singleton (T + 1)))

/-- The paper's normalized multiplier, stopped on survival before the capped
tracking exit. -/
noncomputable def stoppedRadiusMultiplier
    (A ρ h₀ a δ : ℝ) (T t : ℕ) : (ℕ → ℝ) → ℝ :=
  {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}.indicator
    (radiusNormalizedMultiplier A ρ h₀ a t)

/-- The paper's normalized one-step noise, stopped on survival before the
capped tracking exit and indexed by its arrival time. -/
noncomputable def stoppedNormalizedRadiusNoise
    (A ρ h₀ a δ : ℝ) (T : ℕ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | t + 1, ω =>
      {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}.indicator
        (fun ω =>
          roundedBeta A ρ a (roundedOrbit A ρ h₀ t) *
            normalizedRadiusNoise A ρ h₀ a t ω) ω

/-- Successor-index form of the stopped normalized noise. -/
@[simp] lemma stoppedNormalizedRadiusNoise_succ
    (A ρ h₀ a δ : ℝ) (T t : ℕ) (ω : ℕ → ℝ) :
    stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω =
      {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}.indicator
        (fun ω =>
          roundedBeta A ρ a (roundedOrbit A ρ h₀ t) *
            normalizedRadiusNoise A ρ h₀ a t ω) ω := rfl

/-- Before the capped exit time, every radius up to the current index lies in
the tracking window; conversely, tracking through `t≤T` keeps the exit time
strictly beyond `t`. -/
lemma lt_radiusTrackingExitTime_iff
    {A ρ h₀ a δ : ℝ} {T t : ℕ} {ω : ℕ → ℝ} (htT : t ≤ T) :
    t < radiusTrackingExitTime A ρ h₀ a δ T ω ↔
      ∀ u ≤ t, radiusTrackingGood A ρ h₀ a δ u ω := by
  let S : Set ℕ :=
    {u : ℕ | u ≤ T ∧ ¬radiusTrackingGood A ρ h₀ a δ u ω} ∪ {T + 1}
  have hSne : S.Nonempty := ⟨T + 1, Set.mem_union_right _ (Set.mem_singleton _)⟩
  change t < sInf S ↔ _
  constructor
  · intro ht u hut
    by_contra hubad
    have huS : u ∈ S :=
      Set.mem_union_left _ ⟨hut.trans htT, hubad⟩
    exact (not_le_of_gt ht) ((Nat.sInf_le huS).trans hut)
  · intro hall
    have hmin : sInf S ∈ S := Nat.sInf_mem hSne
    by_contra hnot
    have hmint : sInf S ≤ t := not_lt.mp hnot
    rcases hmin with hbad | hsentinel
    · exact hbad.2 (hall (sInf S) hmint)
    · have heq : sInf S = T + 1 := Set.mem_singleton_iff.mp hsentinel
      omega

/-- Tracking-good is exactly the assertion that the normalized radius error
does not exceed the tolerance. -/
lemma radiusTrackingGood_iff_abs_normalizedRadiusError_le
    {A ρ h₀ a δ : ℝ} {t : ℕ} {ω : ℕ → ℝ}
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) :
    radiusTrackingGood A ρ h₀ a δ t ω ↔
      |normalizedRadiusError A ρ h₀ a t ω| ≤ δ := by
  have hden : 0 < roundedOrbit A ρ h₀ t + a :=
    add_pos_of_nonneg_of_pos (roundedOrbit_nonneg hh₀ t) ha
  unfold radiusTrackingGood normalizedRadiusError
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]

/-- Exit through the capped horizon is exactly an exceedance of the normalized
radius-tracking tolerance at some time up to that horizon. -/
lemma radiusTrackingExitTime_le_iff_exists_abs_normalizedRadiusError_gt
    {A ρ h₀ a δ : ℝ} {T : ℕ} {ω : ℕ → ℝ}
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) :
    radiusTrackingExitTime A ρ h₀ a δ T ω ≤ T ↔
      ∃ t ≤ T, δ < |normalizedRadiusError A ρ h₀ a t ω| := by
  constructor
  · intro hexit
    have hnotall :
        ¬ ∀ t ≤ T, radiusTrackingGood A ρ h₀ a δ t ω := by
      intro hall
      have hlt := (lt_radiusTrackingExitTime_iff le_rfl).2 hall
      omega
    push Not at hnotall
    obtain ⟨t, htT, htbad⟩ := hnotall
    refine ⟨t, htT, ?_⟩
    rw [radiusTrackingGood_iff_abs_normalizedRadiusError_le hh₀ ha] at htbad
    exact lt_of_not_ge htbad
  · rintro ⟨t, htT, htbad⟩
    by_contra hnot
    have hlt : T < radiusTrackingExitTime A ρ h₀ a δ T ω := by omega
    have hgood :=
      (lt_radiusTrackingExitTime_iff le_rfl).mp hlt t htT
    rw [radiusTrackingGood_iff_abs_normalizedRadiusError_le hh₀ ha] at hgood
    exact (not_le_of_gt htbad) hgood

/-- Strictly before the capped exit time, the current index satisfies the
tracking-good inequality. -/
lemma radiusTrackingGood_of_lt_exit
    {A ρ h₀ a δ : ℝ} {T t : ℕ} {ω : ℕ → ℝ}
    (htT : t ≤ T)
    (hlt : t < radiusTrackingExitTime A ρ h₀ a δ T ω) :
    radiusTrackingGood A ρ h₀ a δ t ω :=
  (lt_radiusTrackingExitTime_iff htT).mp hlt t le_rfl

/-- Exiting through the tracked horizon forces the normalized tracking error
at the exit index strictly above the tolerance. -/
lemma delta_lt_abs_normalizedRadiusError_at_exit
    {A ρ h₀ a δ : ℝ} (hh₀ : 0 ≤ h₀) (ha : 0 < a)
    {T : ℕ} {ω : ℕ → ℝ}
    (hexit : radiusTrackingExitTime A ρ h₀ a δ T ω ≤ T) :
    δ < |normalizedRadiusError A ρ h₀ a
      (radiusTrackingExitTime A ρ h₀ a δ T ω) ω| := by
  let τ := radiusTrackingExitTime A ρ h₀ a δ T ω
  let S : Set ℕ :=
    {u : ℕ | u ≤ T ∧ ¬radiusTrackingGood A ρ h₀ a δ u ω} ∪ {T + 1}
  have hSne : S.Nonempty :=
    ⟨T + 1, Set.mem_union_right _ (Set.mem_singleton _)⟩
  have hτS : τ ∈ S := by
    change sInf S ∈ S
    exact Nat.sInf_mem hSne
  have hbad : ¬radiusTrackingGood A ρ h₀ a δ τ ω := by
    rcases hτS with hτbad | hsentinel
    · exact hτbad.2
    · have hτeq : τ = T + 1 := Set.mem_singleton_iff.mp hsentinel
      dsimp [τ] at hτeq
      omega
  have horbit : 0 ≤ roundedOrbit A ρ h₀ τ :=
    roundedOrbit_nonneg hh₀ τ
  have hdenom : 0 < roundedOrbit A ρ h₀ τ + a :=
    add_pos_of_nonneg_of_pos horbit ha
  have hstrict :
      δ * (roundedOrbit A ρ h₀ τ + a) <
        |radiusTrackingError A ρ h₀ τ ω| := by
    exact not_le.mp (by
      simpa only [radiusTrackingGood] using hbad)
  rw [normalizedRadiusError, abs_div, abs_of_pos hdenom]
  exact (lt_div_iff₀ hdenom).2 hstrict

/-- Before the capped exit time, a nonnegative stochastic radius belongs to
the local orbit window used in the deterministic amplification bound. -/
lemma eval_mem_roundedOrbitWindow_of_lt_exit
    {A ρ h₀ a δ : ℝ} {T t : ℕ} {ω : ℕ → ℝ}
    (htT : t ≤ T) (hω : 0 ≤ ω t)
    (hlt : t < radiusTrackingExitTime A ρ h₀ a δ T ω) :
    ω t ∈ roundedOrbitWindow δ a (roundedOrbit A ρ h₀ t) := by
  refine ⟨hω, ?_⟩
  simpa [radiusTrackingGood, radiusTrackingError] using
    radiusTrackingGood_of_lt_exit htT hlt

/-- The rounded mean map has nonnegative derivative throughout the
nonnegative radius axis. -/
lemma deriv_roundedMeanMap_nonneg_of_nonneg
    {A ρ h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : 0 ≤ h) :
    0 ≤ deriv (roundedMeanMap A ρ) h := by
  rcases hh.eq_or_lt with rfl | hh
  · rw [deriv_roundedMeanMap_zero hA hρ hρ_lt]
  · rw [deriv_roundedMeanMap_eq hA hρ hh]
    unfold roundedMeanMapDerivative
    apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg
    · positivity
    apply mul_nonneg
    · exact div_nonneg (roundedLayerThreshold_pos hρ hk).le
        (mul_nonneg hA.le (Real.rpow_nonneg hh.le _))
    · exact gaussianPDFReal_nonneg 0 1 _

/-- The rounded mean-map derivative has a finite upper bound on every compact
nonnegative radius interval, including the flat endpoint at the origin. -/
lemma exists_deriv_roundedMeanMap_le_on_Icc_zero
    {A ρ R : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hR : 0 ≤ R) :
    ∃ L : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) R,
      deriv (roundedMeanMap A ρ) u ≤ L := by
  rcases hR.eq_or_lt with rfl | hR
  · refine ⟨1, ?_⟩
    intro u hu
    have hu : u = 0 := le_antisymm hu.2 hu.1
    subst u
    rw [deriv_roundedMeanMap_zero hA hρ hρ_lt]
    norm_num
  · let r : ℝ := min (R / 2) (1 / 4)
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min (by linarith) (by norm_num)
    have hrR : r ≤ R := by
      calc
        r ≤ R / 2 := min_le_left _ _
        _ ≤ R := by linarith
    have hr_one : r < 1 :=
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    obtain ⟨c, C, hc, hC, hsmall⟩ :=
      exists_roundedMeanMap_small_radius_bounds hA hρ hρ_lt hr hr_one
    obtain ⟨D, hD, hglue⟩ :=
      exists_pos_inv_sq_mul_expNegInvGlue_bound c r
    obtain ⟨L, hL, hcompact⟩ :=
      exists_pos_deriv_roundedMeanMap_le_on_Icc hA hρ hr hrR
    refine ⟨max ((C / c ^ 2) * D) L, ?_⟩
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      rw [deriv_roundedMeanMap_zero hA hρ hρ_lt]
      exact le_trans (by positivity) (le_max_left _ _)
    · have hu_pos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      by_cases hur : u ≤ r
      · have huglue : u ∈ Set.Icc (0 : ℝ) (2 * r) := by
          exact ⟨hu.1, hur.trans (by linarith)⟩
        calc
          deriv (roundedMeanMap A ρ) u ≤
              C * u ^ (-2 : ℝ) * Real.exp (-c / u) :=
            (hsmall u hu_pos hur).2
          _ = (C / c ^ 2) *
                (((fun x : ℝ =>
                    (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
                  fun v : ℝ => v / c) u) :=
            mul_rpow_neg_two_exp_eq_rescaled_glue hc hu_pos
          _ ≤ (C / c ^ 2) * D := by
            exact mul_le_mul_of_nonneg_left (hglue u huglue) (by positivity)
          _ ≤ max ((C / c ^ 2) * D) L := le_max_left _ _
      · exact (hcompact u ⟨not_le.mp hur |>.le, hu.2⟩).trans
          (le_max_right _ _)

/-- The derivative image of every nonnegative local orbit window is bounded
above. -/
lemma bddAbove_deriv_roundedMeanMap_image_roundedOrbitWindow
    {A ρ δ a h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : 0 ≤ h) (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    BddAbove
      (deriv (roundedMeanMap A ρ) '' roundedOrbitWindow δ a h) := by
  have hR : 0 ≤ h + δ * (h + a) := by positivity
  obtain ⟨L, hL⟩ :=
    exists_deriv_roundedMeanMap_le_on_Icc_zero hA hρ hρ_lt hR
  refine ⟨L, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hL u (roundedOrbitWindow_subset_Icc hu)

/-- The normalized one-step radius ratio is nonnegative at every
nonnegative orbit radius and terminal scale. -/
lemma roundedBeta_nonneg
    {A ρ a h : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a) :
    0 ≤ roundedBeta A ρ a h := by
  rw [roundedBeta]
  exact div_nonneg (add_nonneg hh ha)
    (add_nonneg (roundedMeanMap_nonneg A ρ h) ha)

/-- The deterministic tracking amplification at the fixed-precision terminal
scale is subpolynomial, uniformly over every finite horizon. -/
lemma exists_eventually_trackingAmplification_le_exp_sq
    {A ρ h₀ C₀ r : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → ∀ T : ℕ,
        trackingAmplification
            (fun u => roundedAlpha A ρ δ (fixedPrecisionScale N)
              (roundedOrbit A ρ h₀ u))
            (fun u => roundedBeta A ρ (fixedPrecisionScale N)
              (roundedOrbit A ρ h₀ u)) T ≤
          Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨C, hC, N₀, hcomb⟩ :=
    exists_eventually_roundedAmplificationCombination_le_exp_sq
      hA hA_lt hρ hρ_lt hh₀ hh₀C₀ hC₀ hr hr_half hrC₀
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN δ hδ hδ_quarter T
  have ha : 0 ≤ fixedPrecisionScale N := by
    by_cases hNtwo : 1 < N
    · exact (fixedPrecisionScale_pos hNtwo).le
    · interval_cases N <;> simp [fixedPrecisionScale]
  apply trackingAmplification_le_of_combination_le
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hC.le (sq_nonneg _))
  · intro s _
    exact roundedBeta_nonneg (roundedOrbit_nonneg hh₀ s) ha
  · intro s t hst _
    simpa only [roundedAmplificationCombination, roundedAmplificationProduct] using
      hcomb N hN δ hδ hδ_quarter s t hst

/-- The deterministic tracking amplification is uniformly subpolynomial over
every initial radius in `[0,C₀]` and every finite horizon. -/
lemma exists_eventually_uniform_trackingAmplification_le_exp_sq
    {A ρ r C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h₀ : ℝ, 0 ≤ h₀ → h₀ ≤ C₀ →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 → ∀ T : ℕ,
          trackingAmplification
              (fun u => roundedAlpha A ρ δ (fixedPrecisionScale N)
                (roundedOrbit A ρ h₀ u))
              (fun u => roundedBeta A ρ (fixedPrecisionScale N)
                (roundedOrbit A ρ h₀ u)) T ≤
            Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨C, hC, Nbase, hcomb⟩ :=
    exists_eventually_uniform_roundedAmplificationCombination_le_exp_sq
      hA hA_lt hρ hρ_lt hC₀ hr hr_half hrC₀
  refine ⟨C, hC, max Nbase 2, ?_⟩
  intro N hN h₀ hh₀ hh₀C₀ δ hδ hδ_quarter T
  have hNbase : Nbase ≤ N := (le_max_left Nbase 2).trans hN
  have hNtwo : 2 ≤ N := (le_max_right Nbase 2).trans hN
  have ha : 0 ≤ fixedPrecisionScale N :=
    (fixedPrecisionScale_pos (by omega)).le
  apply trackingAmplification_le_of_combination_le
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hC.le (sq_nonneg _))
  · intro s _
    exact roundedBeta_nonneg (roundedOrbit_nonneg hh₀ s) ha
  · intro s t hst _
    simpa only [roundedAmplificationCombination, roundedAmplificationProduct] using
      hcomb N hNbase h₀ hh₀ hh₀C₀ δ hδ hδ_quarter s t hst

/-- The paper's deterministic normalized amplification factor is
nonnegative on every nonnegative local orbit window. -/
lemma roundedAlpha_nonneg
    {A ρ δ a h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh : 0 ≤ h) (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    0 ≤ roundedAlpha A ρ δ a h := by
  have hsup : 0 ≤ roundedLocalDerivativeSup A ρ δ a h := by
    calc
      0 ≤ deriv (roundedMeanMap A ρ) h :=
        deriv_roundedMeanMap_nonneg_of_nonneg hA hρ hρ_lt hh
      _ ≤ roundedLocalDerivativeSup A ρ δ a h := by
        rw [roundedLocalDerivativeSup]
        exact le_csSup
          (bddAbove_deriv_roundedMeanMap_image_roundedOrbitWindow
            hA hρ hρ_lt hh ha hδ)
          ⟨h, mem_roundedOrbitWindow_self hδ ha hh, rfl⟩
  rw [roundedAlpha]
  exact mul_nonneg hsup (roundedBeta_nonneg hh ha)

/-- The whole segment between a local-window point and its nonnegative center
remains inside the same local orbit window. -/
lemma uIcc_subset_roundedOrbitWindow_of_mem
    {δ a h x : ℝ} (hh : 0 ≤ h)
    (hx : x ∈ roundedOrbitWindow δ a h) :
    Set.uIcc x h ⊆ roundedOrbitWindow δ a h := by
  intro c hc
  rcases hx with ⟨hx_nonneg, hx_local⟩
  by_cases hxh : x ≤ h
  · rw [Set.uIcc_of_le hxh] at hc
    rcases hc with ⟨hxc, hch⟩
    refine ⟨hx_nonneg.trans hxc, ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hxh)] at hx_local
    rw [abs_of_nonpos (sub_nonpos.mpr hch)]
    linarith
  · have hhx : h ≤ x := not_le.mp hxh |>.le
    rw [Set.uIcc_comm, Set.uIcc_of_le hhx] at hc
    rcases hc with ⟨hhc, hcx⟩
    refine ⟨hh.trans hhc, ?_⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hhx)] at hx_local
    rw [abs_of_nonneg (sub_nonneg.mpr hhc)]
    linarith

/-- The rounded-map secant quotient between two distinct nonnegative radii is
an actual derivative at an intermediate radius. -/
lemma exists_deriv_eq_secant_roundedMeanMap
    {A ρ x h : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hx : 0 ≤ x) (hh : 0 ≤ h) (hne : x ≠ h) :
    ∃ c ∈ Set.uIcc x h,
      deriv (roundedMeanMap A ρ) c =
        (roundedMeanMap A ρ x - roundedMeanMap A ρ h) / (x - h) := by
  rcases lt_or_gt_of_ne hne with hxh | hhx
  · obtain ⟨c, hc, hderiv⟩ :=
      exists_deriv_eq_slope (roundedMeanMap A ρ) hxh
        (continuous_roundedMeanMap hA hρ hρ_lt).continuousOn
        (fun u hu =>
          (hasDerivAt_roundedMeanMap hA hρ (hx.trans_lt hu.1)
            ).differentiableAt.differentiableWithinAt)
    refine ⟨c, ?_, ?_⟩
    · rw [Set.uIcc_of_le hxh.le]
      exact ⟨hc.1.le, hc.2.le⟩
    · calc
        deriv (roundedMeanMap A ρ) c =
            (roundedMeanMap A ρ h - roundedMeanMap A ρ x) / (h - x) :=
          hderiv
        _ = (roundedMeanMap A ρ x - roundedMeanMap A ρ h) / (x - h) := by
          field_simp [sub_ne_zero.mpr hne, sub_ne_zero.mpr hne.symm]
          ring
  · obtain ⟨c, hc, hderiv⟩ :=
      exists_deriv_eq_slope (roundedMeanMap A ρ) hhx
        (continuous_roundedMeanMap hA hρ hρ_lt).continuousOn
        (fun u hu =>
          (hasDerivAt_roundedMeanMap hA hρ (hh.trans_lt hu.1)
            ).differentiableAt.differentiableWithinAt)
    refine ⟨c, ?_, hderiv⟩
    rw [Set.uIcc_comm, Set.uIcc_of_le hhx.le]
    exact ⟨hc.1.le, hc.2.le⟩

/-- The pathwise difference quotient is the rounded-map derivative at some
point of the current local orbit window. -/
lemma exists_mem_roundedOrbitWindow_deriv_eq_radiusDifferenceQuotient
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {t : ℕ} {ω : ℕ → ℝ}
    (hh : 0 ≤ roundedOrbit A ρ h₀ t) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hω : ω t ∈
      roundedOrbitWindow δ a (roundedOrbit A ρ h₀ t)) :
    ∃ c ∈ roundedOrbitWindow δ a (roundedOrbit A ρ h₀ t),
      deriv (roundedMeanMap A ρ) c =
        radiusDifferenceQuotient A ρ h₀ t ω := by
  by_cases he : radiusTrackingError A ρ h₀ t ω = 0
  · refine ⟨roundedOrbit A ρ h₀ t,
      mem_roundedOrbitWindow_self hδ ha hh, ?_⟩
    simp [radiusDifferenceQuotient, he]
  · have hne : ω t ≠ roundedOrbit A ρ h₀ t := by
      intro heq
      apply he
      simp [radiusTrackingError, heq]
    obtain ⟨c, hc, hderiv⟩ :=
      exists_deriv_eq_secant_roundedMeanMap
        hA hρ hρ_lt hω.1 hh hne
    refine ⟨c, uIcc_subset_roundedOrbitWindow_of_mem hh hω hc, ?_⟩
    rw [radiusDifferenceQuotient, if_pos he, radiusTrackingError]
    exact hderiv

/-- Once the local derivative image is bounded above, the pathwise difference
quotient is controlled by the paper's local derivative supremum. -/
lemma radiusDifferenceQuotient_le_roundedLocalDerivativeSup_of_bddAbove
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {t : ℕ} {ω : ℕ → ℝ}
    (hh : 0 ≤ roundedOrbit A ρ h₀ t) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hω : ω t ∈ roundedOrbitWindow δ a (roundedOrbit A ρ h₀ t))
    (hbdd : BddAbove
      (deriv (roundedMeanMap A ρ) ''
        roundedOrbitWindow δ a (roundedOrbit A ρ h₀ t))) :
    radiusDifferenceQuotient A ρ h₀ t ω ≤
      roundedLocalDerivativeSup A ρ δ a (roundedOrbit A ρ h₀ t) := by
  obtain ⟨c, hc, hderiv⟩ :=
    exists_mem_roundedOrbitWindow_deriv_eq_radiusDifferenceQuotient
      hA hρ hρ_lt hh ha hδ hω
  rw [← hderiv, roundedLocalDerivativeSup]
  exact le_csSup hbdd ⟨c, hc, rfl⟩

/-- The pathwise difference quotient is controlled by the paper's local
derivative supremum throughout every nonnegative local orbit window. -/
lemma radiusDifferenceQuotient_le_roundedLocalDerivativeSup
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {t : ℕ} {ω : ℕ → ℝ}
    (hh : 0 ≤ roundedOrbit A ρ h₀ t) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hω : ω t ∈ roundedOrbitWindow δ a (roundedOrbit A ρ h₀ t)) :
    radiusDifferenceQuotient A ρ h₀ t ω ≤
      roundedLocalDerivativeSup A ρ δ a (roundedOrbit A ρ h₀ t) := by
  exact radiusDifferenceQuotient_le_roundedLocalDerivativeSup_of_bddAbove
    hA hρ hρ_lt hh ha hδ hω
    (bddAbove_deriv_roundedMeanMap_image_roundedOrbitWindow
      hA hρ hρ_lt hh ha hδ)

/-- Inside the local tracking window, the normalized difference-quotient
coefficient is bounded by the paper's deterministic amplification factor. -/
lemma abs_radiusNormalizedMultiplier_le_roundedAlpha_of_mem
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {t : ℕ} {ω : ℕ → ℝ}
    (hh : 0 ≤ roundedOrbit A ρ h₀ t) (ha : 0 < a) (hδ : 0 ≤ δ)
    (hω : ω t ∈ roundedOrbitWindow δ a (roundedOrbit A ρ h₀ t)) :
    |radiusNormalizedMultiplier A ρ h₀ a t ω| ≤
      roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ t) := by
  obtain ⟨c, hc, hderiv⟩ :=
    exists_mem_roundedOrbitWindow_deriv_eq_radiusDifferenceQuotient
      hA hρ hρ_lt hh ha.le hδ hω
  have hquot_nonneg :
      0 ≤ radiusDifferenceQuotient A ρ h₀ t ω := by
    rw [← hderiv]
    exact deriv_roundedMeanMap_nonneg_of_nonneg hA hρ hρ_lt hc.1
  have hbeta_nonneg :
      0 ≤ roundedBeta A ρ a (roundedOrbit A ρ h₀ t) := by
    rw [roundedBeta]
    exact div_nonneg (add_nonneg hh ha.le)
      (add_nonneg (roundedMeanMap_nonneg A ρ _) ha.le)
  rw [radiusNormalizedMultiplier, roundedAlpha,
    abs_of_nonneg (mul_nonneg hquot_nonneg hbeta_nonneg)]
  exact mul_le_mul_of_nonneg_right
    (radiusDifferenceQuotient_le_roundedLocalDerivativeSup
      hA hρ hρ_lt hh ha.le hδ hω)
    hbeta_nonneg

/-- Strictly before the capped tracking exit, the normalized multiplier obeys
the deterministic amplification bound whenever the current state is
nonnegative. -/
lemma abs_radiusNormalizedMultiplier_le_roundedAlpha_of_lt_exit
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {T t : ℕ} {ω : ℕ → ℝ} (htT : t ≤ T) (hω : 0 ≤ ω t)
    (hlt : t < radiusTrackingExitTime A ρ h₀ a δ T ω) :
    |radiusNormalizedMultiplier A ρ h₀ a t ω| ≤
      roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ t) := by
  have hh := roundedOrbit_nonneg (A := A) (ρ := ρ) hh₀ t
  exact abs_radiusNormalizedMultiplier_le_roundedAlpha_of_mem
    hA hρ hρ_lt hh ha hδ
    (eval_mem_roundedOrbitWindow_of_lt_exit htT hω hlt)

/-- The time-`t` coordinate is measurable with respect to the canonical
coordinate-prefix filtration at time `t`. -/
lemma measurable_piLE_eval (t : ℕ) :
    Measurable[Filtration.piLE t] (fun ω : ℕ → ℝ => ω t) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hrestrict :
      Measurable[MeasurableSpace.comap (Preorder.frestrictLe t) inferInstance]
        (Preorder.frestrictLe t : (ℕ → ℝ) → ((i : Finset.Iic t) → ℝ)) :=
    comap_measurable _
  exact (measurable_pi_apply ⟨t, Finset.mem_Iic.mpr le_rfl⟩).comp hrestrict

/-- The tracking error at time `t` is measurable with respect to the
coordinate-prefix filtration. -/
lemma measurable_radiusTrackingError
    (A ρ h₀ : ℝ) (t : ℕ) :
    Measurable[Filtration.piLE t] (radiusTrackingError A ρ h₀ t) := by
  have hconst : Measurable[Filtration.piLE t]
      (fun _ : ℕ → ℝ => roundedOrbit A ρ h₀ t) :=
    measurable_const
  exact (measurable_piLE_eval t).sub hconst

/-- The normalized tracking error is measurable with respect to the
coordinate-prefix filtration at its current time. -/
lemma measurable_normalizedRadiusError
    (A ρ h₀ a : ℝ) (t : ℕ) :
    Measurable[Filtration.piLE t]
      (normalizedRadiusError A ρ h₀ a t) := by
  unfold normalizedRadiusError
  exact (measurable_radiusTrackingError A ρ h₀ t).div measurable_const

/-- The paper's case-defined difference quotient is measurable at the current
time. -/
lemma measurable_radiusDifferenceQuotient
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (h₀ : ℝ) (t : ℕ) :
    Measurable[Filtration.piLE t]
      (radiusDifferenceQuotient A ρ h₀ t) := by
  have herr := measurable_radiusTrackingError A ρ h₀ t
  have hVcurrent : Measurable[Filtration.piLE t]
      (fun ω : ℕ → ℝ => roundedMeanMap A ρ (ω t)) :=
    (continuous_roundedMeanMap hA hρ hρ_lt).measurable.comp
      (measurable_piLE_eval t)
  have hVorbit : Measurable[Filtration.piLE t]
      (fun _ : ℕ → ℝ =>
        roundedMeanMap A ρ (roundedOrbit A ρ h₀ t)) :=
    measurable_const
  have hbranch : MeasurableSet[Filtration.piLE t]
      {ω : ℕ → ℝ | radiusTrackingError A ρ h₀ t ω ≠ 0} :=
    ((measurableSet_singleton (0 : ℝ)).preimage herr).compl
  have hderiv : Measurable[Filtration.piLE t]
      (fun _ : ℕ → ℝ =>
        deriv (roundedMeanMap A ρ) (roundedOrbit A ρ h₀ t)) :=
    measurable_const
  unfold radiusDifferenceQuotient
  exact Measurable.ite hbranch
    ((hVcurrent.sub hVorbit).div herr) hderiv

/-- The normalized tracking multiplier is measurable at the current time. -/
lemma measurable_radiusNormalizedMultiplier
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (h₀ a : ℝ) (t : ℕ) :
    Measurable[Filtration.piLE t]
      (radiusNormalizedMultiplier A ρ h₀ a t) := by
  have hbeta : Measurable[Filtration.piLE t]
      (fun _ : ℕ → ℝ =>
        roundedBeta A ρ a (roundedOrbit A ρ h₀ t)) :=
    measurable_const
  exact (measurable_radiusDifferenceQuotient hA hρ hρ_lt h₀ t).mul hbeta

/-- The tracking-good event at time `t` belongs to the canonical filtration
at time `t`. -/
lemma measurableSet_radiusTrackingGood
    (A ρ h₀ a δ : ℝ) (t : ℕ) :
    MeasurableSet[Filtration.piLE t]
      {ω : ℕ → ℝ | radiusTrackingGood A ρ h₀ a δ t ω} := by
  change MeasurableSet[Filtration.piLE t]
    {ω : ℕ → ℝ |
      |ω t - roundedOrbit A ρ h₀ t| ≤
        δ * (roundedOrbit A ρ h₀ t + a)}
  have hleft : Measurable[Filtration.piLE t]
      (fun ω : ℕ → ℝ => |ω t - roundedOrbit A ρ h₀ t|) := by
    have hconst : Measurable[Filtration.piLE t]
        (fun _ : ℕ → ℝ => roundedOrbit A ρ h₀ t) :=
      measurable_const
    exact continuous_abs.measurable.comp
      ((measurable_piLE_eval t).sub hconst)
  have hright : Measurable[Filtration.piLE t]
      (fun _ : ℕ → ℝ => δ * (roundedOrbit A ρ h₀ t + a)) :=
    measurable_const
  exact measurableSet_le hleft hright

/-- Through the fixed horizon, survival of the capped tracking exit time is
measurable in the canonical coordinate-prefix filtration. -/
lemma measurableSet_lt_radiusTrackingExitTime
    {A ρ h₀ a δ : ℝ} {T t : ℕ} (htT : t ≤ T) :
    MeasurableSet[Filtration.piLE t]
      {ω : ℕ → ℝ | t < radiusTrackingExitTime A ρ h₀ a δ T ω} := by
  rw [show {ω : ℕ → ℝ |
      t < radiusTrackingExitTime A ρ h₀ a δ T ω} =
      ⋂ u : ℕ, {ω | u ≤ t → radiusTrackingGood A ρ h₀ a δ u ω} by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq,
      lt_radiusTrackingExitTime_iff htT]]
  apply MeasurableSet.iInter
  intro u
  by_cases hut : u ≤ t
  · simp only [hut, true_implies]
    exact (Filtration.piLE (X := fun _ : ℕ => ℝ)).mono hut _
      (measurableSet_radiusTrackingGood A ρ h₀ a δ u)
  · simp [hut]

/-- The event that the capped tracking exit occurs through the tracked horizon
is measurable in the ambient path sigma-algebra. -/
lemma measurableSet_radiusTrackingExitTime_le
    (A ρ h₀ a δ : ℝ) (T : ℕ) :
    MeasurableSet
      {ω : ℕ → ℝ | radiusTrackingExitTime A ρ h₀ a δ T ω ≤ T} := by
  rw [show
    {ω : ℕ → ℝ | radiusTrackingExitTime A ρ h₀ a δ T ω ≤ T} =
      {ω | T < radiusTrackingExitTime A ρ h₀ a δ T ω}ᶜ by
        ext ω
        simp]
  exact ((Filtration.piLE (X := fun _ : ℕ => ℝ)).le T _
    (measurableSet_lt_radiusTrackingExitTime le_rfl)).compl

/-- The capped tracking exit time, viewed as a `WithTop ℕ`-valued random time, is a
stopping time for the canonical coordinate-prefix filtration. -/
lemma isStoppingTime_radiusTrackingExitTime
    (A ρ h₀ a δ : ℝ) (T : ℕ) :
    IsStoppingTime (Filtration.piLE : Filtration ℕ _)
      (fun ω : ℕ → ℝ =>
        (radiusTrackingExitTime A ρ h₀ a δ T ω : WithTop ℕ)) := by
  intro t
  change MeasurableSet[Filtration.piLE t]
    {ω : ℕ → ℝ |
      (radiusTrackingExitTime A ρ h₀ a δ T ω : WithTop ℕ) ≤ t}
  by_cases htT : t ≤ T
  · rw [show
      {ω : ℕ → ℝ |
        (radiusTrackingExitTime A ρ h₀ a δ T ω : WithTop ℕ) ≤ t} =
        {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}ᶜ by
      ext ω
      simp]
    exact (measurableSet_lt_radiusTrackingExitTime htT).compl
  · have hTt : T + 1 ≤ t := by omega
    rw [show
      {ω : ℕ → ℝ |
        (radiusTrackingExitTime A ρ h₀ a δ T ω : WithTop ℕ) ≤ t} =
        Set.univ by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact_mod_cast
        (radiusTrackingExitTime_le_sentinel A ρ h₀ a δ T ω).trans hTt]
    exact MeasurableSet.univ

/-- The normalized tracking error stopped at the capped exit time is strongly
measurable at its current time. -/
lemma stronglyMeasurable_stoppedNormalizedRadiusError
    (A ρ h₀ a δ : ℝ) (T t : ℕ) :
    StronglyMeasurable[Filtration.piLE t]
      (stoppedValue (normalizedRadiusError A ρ h₀ a)
        (radiusTrackingExitTime A ρ h₀ a δ T) t) := by
  have hR : StronglyAdapted
      (Filtration.piLE : Filtration ℕ _)
      (normalizedRadiusError A ρ h₀ a) :=
    fun u =>
      (measurable_normalizedRadiusError A ρ h₀ a u).stronglyMeasurable
  have hτ : IsStoppingTime
      (Filtration.piLE : Filtration ℕ _)
      (fun ω : ℕ → ℝ =>
        (radiusTrackingExitTime A ρ h₀ a δ T ω : WithTop ℕ)) :=
    isStoppingTime_radiusTrackingExitTime A ρ h₀ a δ T
  rw [stoppedValue_eq_stoppedProcess_coe]
  exact (hR.stoppedProcess_of_discrete hτ) t

/-- The stopped normalized multiplier is adapted to the canonical
coordinate-prefix filtration. -/
lemma measurable_stoppedRadiusMultiplier
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (h₀ a δ : ℝ) {T t : ℕ} (htT : t ≤ T) :
    Measurable[Filtration.piLE t]
      (stoppedRadiusMultiplier A ρ h₀ a δ T t) := by
  exact (measurable_radiusNormalizedMultiplier hA hρ hρ_lt h₀ a t).indicator
    (measurableSet_lt_radiusTrackingExitTime htT)

/-- The stopped normalized drift term is strongly measurable with respect to
the current coordinate-prefix filtration. -/
lemma stronglyMeasurable_stoppedRadiusMultiplier_mul_normalizedRadiusError
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (h₀ a δ : ℝ) {T t : ℕ} (htT : t ≤ T) :
    StronglyMeasurable[Filtration.piLE t]
      (fun ω =>
        stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
          normalizedRadiusError A ρ h₀ a t ω) := by
  exact ((measurable_stoppedRadiusMultiplier
    hA hρ hρ_lt h₀ a δ htT).mul
      (measurable_normalizedRadiusError A ρ h₀ a t)).stronglyMeasurable

/-- The difference quotient exactly factors the rounded-map increment. -/
lemma radiusDifferenceQuotient_mul_trackingError
    (A ρ h₀ : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    radiusDifferenceQuotient A ρ h₀ t ω *
        radiusTrackingError A ρ h₀ t ω =
      roundedMeanMap A ρ (ω t) -
        roundedMeanMap A ρ (roundedOrbit A ρ h₀ t) := by
  by_cases he : radiusTrackingError A ρ h₀ t ω = 0
  · have hx : ω t = roundedOrbit A ρ h₀ t := by
      simpa [radiusTrackingError, sub_eq_zero] using he
    simp [radiusDifferenceQuotient, he, hx]
  · rw [radiusDifferenceQuotient, if_pos he, div_mul_cancel₀ _ he]

/-- The tracking error starts from zero when the stochastic and deterministic
initial radii agree. -/
lemma radiusTrackingError_zero_of_eval_zero_eq
    {A ρ h₀ : ℝ} {ω : ℕ → ℝ} (hω : ω 0 = h₀) :
    radiusTrackingError A ρ h₀ 0 ω = 0 := by
  simp [radiusTrackingError, hω]

/-- Exact unnormalized error recursion along the deterministic rounded orbit. -/
lemma radiusTrackingError_succ (A ρ h₀ : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    radiusTrackingError A ρ h₀ (t + 1) ω =
      (roundedMeanMap A ρ (ω t) -
        roundedMeanMap A ρ (roundedOrbit A ρ h₀ t)) +
      radiusNoise A ρ t ω := by
  rw [radiusTrackingError, radiusNoise, roundedOrbit_succ]
  ring

/-- Multiplicative form of the exact tracking-error recursion. -/
lemma radiusTrackingError_succ_eq_mul_add
    (A ρ h₀ : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    radiusTrackingError A ρ h₀ (t + 1) ω =
      radiusDifferenceQuotient A ρ h₀ t ω *
        radiusTrackingError A ρ h₀ t ω +
      radiusNoise A ρ t ω := by
  rw [radiusTrackingError_succ,
    radiusDifferenceQuotient_mul_trackingError]

/-- Exact normalized tracking recursion from the paper. -/
lemma normalizedRadiusError_succ
    {A ρ h₀ a : ℝ} (hh₀ : 0 ≤ h₀) (ha : 0 < a)
    (t : ℕ) (ω : ℕ → ℝ) :
    normalizedRadiusError A ρ h₀ a (t + 1) ω =
      radiusNormalizedMultiplier A ρ h₀ a t ω *
        normalizedRadiusError A ρ h₀ a t ω +
      roundedBeta A ρ a (roundedOrbit A ρ h₀ t) *
        normalizedRadiusNoise A ρ h₀ a t ω := by
  have horbit : 0 ≤ roundedOrbit A ρ h₀ t :=
    roundedOrbit_nonneg hh₀ t
  have hdenom :
      roundedOrbit A ρ h₀ t + a ≠ 0 := by
    exact (add_pos_of_nonneg_of_pos horbit ha).ne'
  have hnext :
      roundedMeanMap A ρ (roundedOrbit A ρ h₀ t) + a ≠ 0 := by
    have hV := roundedMeanMap_nonneg A ρ (roundedOrbit A ρ h₀ t)
    exact (add_pos_of_nonneg_of_pos hV ha).ne'
  simp only [normalizedRadiusError, radiusNormalizedMultiplier,
    normalizedRadiusNoise]
  rw [radiusTrackingError_succ_eq_mul_add, roundedOrbit_succ, roundedBeta]
  field_simp [hdenom, hnext]

/-- Before the capped tracking exit, the normalized error obeys the paper's
recursion with the stopped multiplier and stopped noise. -/
lemma normalizedRadiusError_succ_eq_stopped_of_lt_exit
    {A ρ h₀ a δ : ℝ} (hh₀ : 0 ≤ h₀) (ha : 0 < a)
    {T t : ℕ} {ω : ℕ → ℝ}
    (hlt : t < radiusTrackingExitTime A ρ h₀ a δ T ω) :
    normalizedRadiusError A ρ h₀ a (t + 1) ω =
      stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
        normalizedRadiusError A ρ h₀ a t ω +
      stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω := by
  rw [stoppedRadiusMultiplier, Set.indicator_of_mem
      (show ω ∈ {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω} from hlt),
    stoppedNormalizedRadiusNoise_succ, Set.indicator_of_mem
      (show ω ∈ {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω} from hlt)]
  exact normalizedRadiusError_succ hh₀ ha t ω

/-- On the radius-tracking event, the stochastic radius is bounded by the
corresponding deterministic radius and terminal scale. -/
lemma state_le_of_abs_sub_le_mul_add
    {x h a δ : ℝ} (hlocal : |x - h| ≤ δ * (h + a)) :
    x ≤ (1 + δ) * h + δ * a := by
  have hdiff : x - h ≤ |x - h| := le_abs_self (x - h)
  nlinarith

/-- Squared form of the state localization estimate used in the conditional
noise bound. -/
lemma state_sq_le_of_abs_sub_le_mul_add
    {x h a δ : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hlocal : |x - h| ≤ δ * (h + a)) :
    x ^ 2 ≤ (1 + δ) ^ 2 * (h + a) ^ 2 := by
  have hx_le : x ≤ (1 + δ) * (h + a) := by
    calc
      x ≤ (1 + δ) * h + δ * a :=
        state_le_of_abs_sub_le_mul_add hlocal
      _ ≤ (1 + δ) * (h + a) := by nlinarith
  have hupper : 0 ≤ (1 + δ) * (h + a) := mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg (x - (1 + δ) * (h + a))]

/-- The rounded coordinate observable is nonnegative. -/
lemma roundedCoordinateObservable_nonneg (A ρ h g : ℝ) :
    0 ≤ roundedCoordinateObservable A ρ h g := by
  unfold roundedCoordinateObservable
  positivity

/-- The rounded coordinate observable is measurable in the Gaussian input. -/
lemma measurable_roundedCoordinateObservable (A ρ h : ℝ) :
    Measurable (roundedCoordinateObservable A ρ h) := by
  unfold roundedCoordinateObservable
  apply Measurable.pow_const
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  apply hcast.comp
  apply measurable_Q₁.comp
  apply Measurable.const_mul
  exact continuous_tanh.measurable.comp (by fun_prop)

/-- The finite-dimensional radius transition is the empirical average of the
one-coordinate observables. -/
lemma Hmap_eq_average_roundedCoordinateObservable
    (A ρ : ℝ) (N : ℕ) (h : ℝ) (g : Fin N → ℝ) :
    Hmap A ρ N h g =
      (N : ℝ)⁻¹ * ∑ i, roundedCoordinateObservable A ρ h (g i) := by
  rfl

/-- The standard-Gaussian mean of one rounded coordinate is exactly the rounded
mean map. -/
lemma integral_roundedCoordinateObservable (A ρ h : ℝ) :
    ∫ g, roundedCoordinateObservable A ρ h g ∂(gaussianReal 0 1) =
      roundedMeanMap A ρ h := by
  rfl

/-- Uniformly in the radius and Gaussian input, the rounded coordinate
observable is bounded by the largest possible rounded value. -/
lemma roundedCoordinateObservable_le_sq
    {A ρ h g : ℝ} (hρ : 0 < ρ) :
    roundedCoordinateObservable A ρ h g ≤ (ρ⁻¹ + 1 / 2) ^ 2 := by
  have hinv : 0 ≤ ρ⁻¹ := inv_nonneg.mpr hρ.le
  have harg :
      |ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)| ≤ ρ⁻¹ := by
    rw [abs_mul, abs_of_nonneg hinv]
    exact mul_le_of_le_one_right hinv (Real.abs_tanh_lt_one _).le
  have hQ :
      |((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) : ℤ) : ℝ)| ≤
        ρ⁻¹ + 1 / 2 := by
    exact (abs_Q₁_le _).trans (by
      simpa using add_le_add_left harg (1 / 2))
  rw [roundedCoordinateObservable, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hQ 2

/-- Every fixed power of the rounded coordinate observable is integrable under
the standard Gaussian law. -/
lemma integrable_pow_roundedCoordinateObservable
    {A ρ h : ℝ} (hρ : 0 < ρ) (p : ℕ) :
    Integrable (fun g =>
      (roundedCoordinateObservable A ρ h g) ^ p) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_const ((ρ⁻¹ + 1 / 2) ^ (2 * p)))
    ((measurable_roundedCoordinateObservable A ρ h).pow_const p
      |>.aestronglyMeasurable) ?_
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_nonneg
    (pow_nonneg (roundedCoordinateObservable_nonneg A ρ h g) p)]
  calc
    roundedCoordinateObservable A ρ h g ^ p ≤
        ((ρ⁻¹ + 1 / 2) ^ 2) ^ p :=
      pow_le_pow_left₀ (roundedCoordinateObservable_nonneg A ρ h g)
        (roundedCoordinateObservable_le_sq hρ) p
    _ = (ρ⁻¹ + 1 / 2) ^ (2 * p) := by rw [pow_mul]

/-- The one-step rounded radius has mean equal to the rounded mean map. -/
lemma integral_Hmap_eq_roundedMeanMap
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : N ≠ 0) :
    ∫ g, Hmap A ρ N h g ∂(gaussianVec N) = roundedMeanMap A ρ h := by
  have hInt : ∀ i : Fin N, Integrable
      (fun g : Fin N → ℝ => roundedCoordinateObservable A ρ h (g i))
      (gaussianVec N) := by
    intro i
    refine Integrable.mono' (integrable_const ((ρ⁻¹ + 1 / 2) ^ 2))
      ((measurable_roundedCoordinateObservable A ρ h).comp
        (measurable_pi_apply i) |>.aestronglyMeasurable) ?_
    filter_upwards with g
    rw [Real.norm_eq_abs,
      abs_of_nonneg (roundedCoordinateObservable_nonneg A ρ h (g i))]
    exact roundedCoordinateObservable_le_sq hρ
  have hmarg : ∀ i : Fin N,
      ∫ g, roundedCoordinateObservable A ρ h (g i) ∂(gaussianVec N) =
        roundedMeanMap A ρ h := by
    intro i
    have hpm : (gaussianVec N).map (Function.eval i) = gaussianReal 0 1 := by
      unfold gaussianVec
      rw [Measure.pi_map_eval]
      simp
    have hf : AEStronglyMeasurable (roundedCoordinateObservable A ρ h)
        ((gaussianVec N).map (Function.eval i)) :=
      (measurable_roundedCoordinateObservable A ρ h).aestronglyMeasurable
    have hφ : AEMeasurable (Function.eval i) (gaussianVec N) :=
      (measurable_pi_apply i).aemeasurable
    have hmap := integral_map hφ hf
    rw [hpm] at hmap
    exact hmap.symm.trans (integral_roundedCoordinateObservable A ρ h)
  unfold Hmap
  rw [integral_const_mul]
  change (N : ℝ)⁻¹ *
      ∫ g, ∑ i, roundedCoordinateObservable A ρ h (g i) ∂(gaussianVec N) =
    roundedMeanMap A ρ h
  rw [integral_finsetSum _ (fun i _ => hInt i)]
  simp_rw [hmarg]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The rounded mean map inherits the uniform coordinate bound. -/
lemma roundedMeanMap_le_sq {A ρ h : ℝ} (hρ : 0 < ρ) :
    roundedMeanMap A ρ h ≤ (ρ⁻¹ + 1 / 2) ^ 2 := by
  rw [← integral_roundedCoordinateObservable]
  have hint : Integrable (roundedCoordinateObservable A ρ h)
      (gaussianReal 0 1) := by
    simpa using integrable_pow_roundedCoordinateObservable
      (A := A) (h := h) hρ 1
  calc
    ∫ g, roundedCoordinateObservable A ρ h g ∂(gaussianReal 0 1) ≤
        ∫ _g : ℝ, (ρ⁻¹ + 1 / 2) ^ 2 ∂(gaussianReal 0 1) :=
      integral_mono hint (integrable_const _) fun g =>
        roundedCoordinateObservable_le_sq hρ
    _ = (ρ⁻¹ + 1 / 2) ^ 2 := by simp

/-- Every realization of the rounded radius step obeys the same uniform
coordinate bound. -/
lemma Hmap_le_sq {A ρ h : ℝ} {N : ℕ}
    (hρ : 0 < ρ) (hN : 0 < N) (g : Fin N → ℝ) :
    Hmap A ρ N h g ≤ (ρ⁻¹ + 1 / 2) ^ 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Hmap_eq_average_roundedCoordinateObservable]
  calc
    (N : ℝ)⁻¹ *
        ∑ i, roundedCoordinateObservable A ρ h (g i) ≤
      (N : ℝ)⁻¹ *
        ∑ _i : Fin N, (ρ⁻¹ + 1 / 2) ^ 2 := by
      gcongr with i
      exact roundedCoordinateObservable_le_sq hρ
    _ = (ρ⁻¹ + 1 / 2) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hNreal.ne']

/-- Measurability of the rounded radius step as a function of the Gaussian
input, with the current radius fixed. -/
lemma measurable_Hmap_right (A ρ : ℝ) (N : ℕ) (h : ℝ) :
    Measurable (Hmap A ρ N h) := by
  unfold Hmap
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_roundedCoordinateObservable A ρ h).comp
    (measurable_pi_apply i)

/-- The uniformly bounded rounded radius step is integrable. -/
lemma integrable_Hmap {A ρ h : ℝ} {N : ℕ}
    (hρ : 0 < ρ) (hN : 0 < N) :
    Integrable (Hmap A ρ N h) (gaussianVec N) := by
  refine Integrable.mono' (integrable_const ((ρ⁻¹ + 1 / 2) ^ 2))
    (measurable_Hmap_right A ρ N h |>.aestronglyMeasurable) ?_
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_nonneg (Hmap_nonneg A ρ N h g)]
  exact Hmap_le_sq hρ hN g

/-- The rounded radius kernel at `h` is the pushforward of the standard
Gaussian vector under `Hmap`. -/
lemma Hkernel_apply (A ρ : ℝ) (N : ℕ) (h : ℝ) :
    Hkernel A ρ N h = (gaussianVec N).map (Hmap A ρ N h) := by
  unfold Hkernel
  rw [Kernel.map_apply _ (measurable_Hmap A ρ N), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, id_eq, Measure.dirac_prod,
    Measure.map_map (measurable_Hmap A ρ N)
      (by fun_prop : Measurable (Prod.mk h))]
  rfl

/-- The one-step innovation is centered under the rounded radius kernel. -/
lemma integral_Hkernel_sub_roundedMeanMap_eq_zero
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N) :
    ∫ y, y - roundedMeanMap A ρ h ∂(Hkernel A ρ N h) = 0 := by
  rw [Hkernel_apply, integral_map]
  · rw [integral_sub (integrable_Hmap hρ hN) (integrable_const _),
      integral_Hmap_eq_roundedMeanMap hρ hN.ne', integral_const]
    simp
  · exact (measurable_Hmap_right A ρ N h).aemeasurable
  · fun_prop

/-- Every rounded-radius transition is supported in the deterministic compact
interval supplied by the coordinate bound. -/
lemma Hkernel_apply_Icc_compl
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N) :
    Hkernel A ρ N h
        (Set.Icc 0 ((ρ⁻¹ + 1 / 2) ^ 2))ᶜ = 0 := by
  have hHmeas : Measurable (Hmap A ρ N h) := by
    unfold Hmap
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_roundedCoordinateObservable A ρ h).comp
      (measurable_pi_apply i)
  rw [Hkernel_apply, Measure.map_apply hHmeas
    (measurableSet_Icc.compl)]
  have hempty :
      Hmap A ρ N h ⁻¹' (Set.Icc 0 ((ρ⁻¹ + 1 / 2) ^ 2))ᶜ = ∅ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false]
    intro hg
    exact hg ⟨Hmap_nonneg A ρ N h g, Hmap_le_sq hρ hN g⟩
  rw [hempty, measure_empty]

/-- A canonical Markov path started from a Dirac mass has its prescribed
initial state at time zero almost surely. -/
lemma markovPathMeasure_dirac_ae_eval_zero_eq
    (h₀ : ℝ) (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac h₀) κ), ω 0 = h₀ := by
  rw [ae_iff]
  have hset :
      {ω : ℕ → ℝ | ω 0 ≠ h₀} =
        (fun ω : ℕ → ℝ => ω 0) ⁻¹' ({h₀} : Set ℝ)ᶜ := by
    ext ω
    simp
  rw [show {ω : ℕ → ℝ | ¬ω 0 = h₀} = {ω : ℕ → ℝ | ω 0 ≠ h₀} by rfl,
    hset, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton h₀).compl,
    markovPathMeasure_map_zero]
  simp

/-- Every positive-time coordinate of the canonical rounded-radius path lies
in the deterministic compact support interval almost surely. -/
lemma markovPathMeasure_ae_eval_succ_mem_Icc
    {A ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure μ₀ (Hkernel A ρ N)),
      ω (t + 1) ∈ Set.Icc 0 ((ρ⁻¹ + 1 / 2) ^ 2) := by
  have hzero : ∀ a : ℝ,
      Hkernel A ρ N a
        (Set.Icc 0 ((ρ⁻¹ + 1 / 2) ^ 2))ᶜ = 0 :=
    fun _ => Hkernel_apply_Icc_compl hρ hN
  rw [ae_iff]
  have hset :
      {ω : ℕ → ℝ |
        ω (t + 1) ∉ Set.Icc 0 ((ρ⁻¹ + 1 / 2) ^ 2)} =
      (fun ω : ℕ → ℝ => ω (t + 1)) ⁻¹'
        (Set.Icc 0 ((ρ⁻¹ + 1 / 2) ^ 2))ᶜ := rfl
  rw [show {ω : ℕ → ℝ |
      ¬ω (t + 1) ∈ Set.Icc 0 ((ρ⁻¹ + 1 / 2) ^ 2)} =
      {ω : ℕ → ℝ |
        ω (t + 1) ∉ Set.Icc 0 ((ρ⁻¹ + 1 / 2) ^ 2)} by rfl,
    hset, ← Measure.map_apply (measurable_pi_apply (t + 1))
      measurableSet_Icc.compl,
    markovPathMeasure_map_eval_succ,
    Measure.bind_apply measurableSet_Icc.compl
      (Hkernel A ρ N).aemeasurable]
  simp only [hzero, lintegral_zero]

/-- Every coordinate of the canonical rounded-radius path started from a
nonnegative Dirac state is nonnegative almost surely. -/
lemma markovPathMeasure_dirac_ae_eval_nonneg
    {A ρ h₀ : ℝ} {N : ℕ} (hh₀ : 0 ≤ h₀) (hρ : 0 < ρ) (hN : 0 < N)
    (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)),
      0 ≤ ω t := by
  cases t with
  | zero =>
      filter_upwards [
        markovPathMeasure_dirac_ae_eval_zero_eq h₀ (Hkernel A ρ N)] with ω hω
      simpa only [hω] using hh₀
  | succ t =>
      filter_upwards [
        markovPathMeasure_ae_eval_succ_mem_Icc hρ hN (Measure.dirac h₀) t] with ω hω
      exact hω.1

/-- At every fixed time, the squared normalized tracking error is integrable
under the canonical Dirac-started rounded-radius path law. -/
lemma integrable_sq_normalizedRadiusError
    {A ρ h₀ a : ℝ} (hh₀ : 0 ≤ h₀) (ha : 0 < a)
    (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) (t : ℕ) :
    Integrable (fun ω =>
      normalizedRadiusError A ρ h₀ a t ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
  have hmeasFull : Measurable
      (normalizedRadiusError A ρ h₀ a t) :=
    (measurable_normalizedRadiusError A ρ h₀ a t).mono
      ((Filtration.piLE (X := fun _ : ℕ => ℝ)).le t) le_rfl
  have hmeas : AEStronglyMeasurable
      (fun ω => normalizedRadiusError A ρ h₀ a t ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    (hmeasFull.pow_const 2).aestronglyMeasurable
  cases t with
  | zero =>
      refine Integrable.mono' (integrable_const (0 : ℝ)) hmeas ?_
      filter_upwards [
        markovPathMeasure_dirac_ae_eval_zero_eq
          h₀ (Hkernel A ρ N)] with ω hω
      simp [normalizedRadiusError, radiusTrackingError, hω]
  | succ t =>
      let B : ℝ := (ρ⁻¹ + 1 / 2) ^ 2
      have hB : 0 ≤ B := by
        dsimp [B]
        positivity
      have horbit : 0 ≤ roundedOrbit A ρ h₀ (t + 1) :=
        roundedOrbit_nonneg hh₀ (t + 1)
      have hdenom :
          0 < roundedOrbit A ρ h₀ (t + 1) + a :=
        add_pos_of_nonneg_of_pos horbit ha
      let K : ℝ :=
        (B + |roundedOrbit A ρ h₀ (t + 1)|) /
          (roundedOrbit A ρ h₀ (t + 1) + a)
      have hK : 0 ≤ K := by
        exact div_nonneg (add_nonneg hB (abs_nonneg _)) hdenom.le
      refine Integrable.mono' (integrable_const (K ^ 2)) hmeas ?_
      filter_upwards [
        markovPathMeasure_ae_eval_succ_mem_Icc
          hρ hN (Measure.dirac h₀) t] with ω hω
      have habsError :
          |ω (t + 1) - roundedOrbit A ρ h₀ (t + 1)| ≤
            B + |roundedOrbit A ρ h₀ (t + 1)| := by
        calc
          |ω (t + 1) - roundedOrbit A ρ h₀ (t + 1)| ≤
              |ω (t + 1)| +
                |roundedOrbit A ρ h₀ (t + 1)| :=
            abs_sub _ _
          _ = ω (t + 1) +
                |roundedOrbit A ρ h₀ (t + 1)| := by
            rw [abs_of_nonneg hω.1]
          _ ≤ B + |roundedOrbit A ρ h₀ (t + 1)| := by
            gcongr
            simpa [B] using hω.2
      have habsNormalized :
          |normalizedRadiusError A ρ h₀ a (t + 1) ω| ≤ K := by
        rw [normalizedRadiusError, abs_div,
          abs_of_pos hdenom]
        exact div_le_div_of_nonneg_right habsError hdenom.le
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habsNormalized 2

/-- The squared normalized tracking error stopped at the capped exit time is
integrable under the canonical Dirac-started rounded-radius path law. -/
lemma integrable_sq_stoppedNormalizedRadiusError
    {A ρ h₀ a δ : ℝ} (hh₀ : 0 ≤ h₀) (ha : 0 < a)
    (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) (T t : ℕ) :
    Integrable (fun ω =>
      stoppedValue (normalizedRadiusError A ρ h₀ a)
        (radiusTrackingExitTime A ρ h₀ a δ T) t ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
  let R : ℕ → (ℕ → ℝ) → ℝ :=
    fun n ω => normalizedRadiusError A ρ h₀ a n ω ^ 2
  let τ : (ℕ → ℝ) → ℕ :=
    radiusTrackingExitTime A ρ h₀ a δ T
  have hτ : IsStoppingTime
      (Filtration.piLE : Filtration ℕ _)
      (fun ω : ℕ → ℝ => (τ ω : WithTop ℕ)) :=
    isStoppingTime_radiusTrackingExitTime A ρ h₀ a δ T
  have hR : ∀ n : ℕ, Integrable (R n)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    fun n => integrable_sq_normalizedRadiusError hh₀ ha hρ hN n
  have hstop : Integrable
      (MeasureTheory.stoppedProcess R
        (fun ω => (τ ω : WithTop ℕ)) t)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    MeasureTheory.integrable_stoppedProcess hτ hR t
  rw [← stoppedValue_eq_stoppedProcess_coe] at hstop
  change Integrable (fun ω =>
    normalizedRadiusError A ρ h₀ a
      (min t (radiusTrackingExitTime A ρ h₀ a δ T ω)) ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) at hstop
  change Integrable (fun ω =>
    normalizedRadiusError A ρ h₀ a
      (min t (radiusTrackingExitTime A ρ h₀ a δ T ω)) ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))
  exact hstop

/-- A deterministic weight preserves integrability of the stopped normalized
tracking-error square. -/
lemma integrable_weighted_sq_stoppedNormalizedRadiusError
    {A ρ h₀ a δ : ℝ} (hh₀ : 0 ≤ h₀) (ha : 0 < a)
    (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N) (T t : ℕ) (W : ℝ) :
    Integrable (fun ω =>
      W * stoppedValue (normalizedRadiusError A ρ h₀ a)
        (radiusTrackingExitTime A ρ h₀ a δ T) t ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
  (integrable_sq_stoppedNormalizedRadiusError
    (δ := δ) hh₀ ha hρ hN T t).const_mul W

/-- Under the canonical Dirac-started path law, the normalized multiplier
obeys its deterministic amplification bound almost surely before the capped
tracking exit. -/
lemma abs_radiusNormalizedMultiplier_le_roundedAlpha_of_lt_exit_ae
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)),
      t < radiusTrackingExitTime A ρ h₀ a δ T ω →
        |radiusNormalizedMultiplier A ρ h₀ a t ω| ≤
          roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ t) := by
  filter_upwards [
    markovPathMeasure_dirac_ae_eval_nonneg hh₀ hρ hN t] with ω hω
  intro hlt
  exact abs_radiusNormalizedMultiplier_le_roundedAlpha_of_lt_exit
    hA hρ hρ_lt hh₀ ha hδ htT hω hlt

/-- The paper's stopped normalized coefficient obeys the deterministic
amplification bound almost surely. -/
lemma abs_stoppedRadiusMultiplier_le_roundedAlpha_ae
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)),
      |stoppedRadiusMultiplier A ρ h₀ a δ T t ω| ≤
        roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ t) := by
  have halpha :
      0 ≤ roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ t) :=
    roundedAlpha_nonneg hA hρ hρ_lt (roundedOrbit_nonneg hh₀ t) ha.le hδ
  filter_upwards [
    abs_radiusNormalizedMultiplier_le_roundedAlpha_of_lt_exit_ae
      hA hρ hρ_lt hh₀ ha hδ hN htT] with ω hω
  by_cases hlt : t < radiusTrackingExitTime A ρ h₀ a δ T ω
  · rw [stoppedRadiusMultiplier, Set.indicator_of_mem
      (show ω ∈ {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω} from hlt)]
    exact hω hlt
  · rw [stoppedRadiusMultiplier, Set.indicator_of_notMem
      (show ω ∉ {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω} from hlt),
      abs_zero]
    exact halpha

/-- Squared form of the stopped normalized coefficient bound, matching the
hypothesis used by the common stopped-moment estimate. -/
lemma sq_stoppedRadiusMultiplier_le_roundedAlpha_sq_ae
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)),
      stoppedRadiusMultiplier A ρ h₀ a δ T t ω ^ 2 ≤
        roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ t) ^ 2 := by
  filter_upwards [
    abs_stoppedRadiusMultiplier_le_roundedAlpha_ae
      hA hρ hρ_lt hh₀ ha hδ hN htT] with ω hω
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hω 2

/-- The squared stopped normalized drift term is integrable under the
canonical Dirac-started rounded-radius path law. -/
lemma integrable_sq_stoppedRadiusMultiplier_mul_normalizedRadiusError
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    Integrable (fun ω =>
      (stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
        normalizedRadiusError A ρ h₀ a t ω) ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
  let α : ℝ := roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ t)
  have hdom : Integrable (fun ω =>
      α ^ 2 * normalizedRadiusError A ρ h₀ a t ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    (integrable_sq_normalizedRadiusError hh₀ ha hρ hN t).const_mul (α ^ 2)
  have hmeasFull : Measurable (fun ω =>
      stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
        normalizedRadiusError A ρ h₀ a t ω) :=
    ((measurable_stoppedRadiusMultiplier hA hρ hρ_lt h₀ a δ htT).mul
      (measurable_normalizedRadiusError A ρ h₀ a t)).mono
        ((Filtration.piLE (X := fun _ : ℕ => ℝ)).le t) le_rfl
  refine Integrable.mono' hdom (hmeasFull.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [
    sq_stoppedRadiusMultiplier_le_roundedAlpha_sq_ae
      hA hρ hρ_lt hh₀ ha hδ hN htT] with ω hω
  have hω' :
      stoppedRadiusMultiplier A ρ h₀ a δ T t ω ^ 2 ≤ α ^ 2 := by
    simpa [α] using hω
  calc
    ‖(stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
        normalizedRadiusError A ρ h₀ a t ω) ^ 2‖ =
        (stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
          normalizedRadiusError A ρ h₀ a t ω) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ = stoppedRadiusMultiplier A ρ h₀ a δ T t ω ^ 2 *
          normalizedRadiusError A ρ h₀ a t ω ^ 2 := by ring
    _ ≤ α ^ 2 * normalizedRadiusError A ρ h₀ a t ω ^ 2 :=
      mul_le_mul_of_nonneg_right hω' (sq_nonneg _)

/-- Centered-square integration against the rounded radius kernel is exactly
the corresponding Gaussian-vector integral. -/
lemma integral_sq_Hkernel_sub_roundedMeanMap
    (A ρ : ℝ) (N : ℕ) (h : ℝ) :
    ∫ y, (y - roundedMeanMap A ρ h) ^ 2 ∂(Hkernel A ρ N h) =
      ∫ g, (Hmap A ρ N h g - roundedMeanMap A ρ h) ^ 2
        ∂(gaussianVec N) := by
  rw [Hkernel_apply, integral_map]
  · apply Measurable.aemeasurable
    unfold Hmap
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_roundedCoordinateObservable A ρ h).comp
      (measurable_pi_apply i)
  · fun_prop

/-- On the canonical rounded-radius path space, the conditional centered
square of the next step is the corresponding Gaussian-vector integral. -/
lemma condExp_sq_next_sub_roundedMeanMap
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (N : ℕ) (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ)
    (hint : Integrable (fun ω : ℕ → ℝ =>
      (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2)
      (markovPathMeasure μ₀ (Hkernel A ρ N))) :
    (markovPathMeasure μ₀ (Hkernel A ρ N))[
        fun ω => (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2 |
        Filtration.piLE t]
      =ᵐ[markovPathMeasure μ₀ (Hkernel A ρ N)]
        fun ω =>
          ∫ g, (Hmap A ρ N (ω t) g - roundedMeanMap A ρ (ω t)) ^ 2
            ∂(gaussianVec N) := by
  let ψ : ((((i : Finset.Iic t) → ℝ) × ℝ) → ℝ) :=
    fun p => (p.2 -
      roundedMeanMap A ρ (p.1 ⟨t, Finset.mem_Iic.mpr le_rfl⟩)) ^ 2
  have hψ : StronglyMeasurable ψ := by
    apply Continuous.stronglyMeasurable
    dsimp [ψ]
    have hcurrent : Continuous (fun p :
        (((i : Finset.Iic t) → ℝ) × ℝ) =>
          roundedMeanMap A ρ
            (p.1 ⟨t, Finset.mem_Iic.mpr le_rfl⟩)) :=
      (continuous_roundedMeanMap hA hρ hρ_lt).comp
        ((continuous_apply _).comp continuous_fst)
    exact (continuous_snd.sub hcurrent).pow 2
  have hcond :=
    condExp_markovPathMeasure_prefix_eval_succ_piLE
      μ₀ (Hkernel A ρ N) t hψ hint
  refine hcond.trans ?_
  filter_upwards with ω
  exact integral_sq_Hkernel_sub_roundedMeanMap A ρ N (ω t)

/-- The centered next-step square on the canonical rounded-radius path is
automatically integrable. -/
lemma integrable_sq_next_sub_roundedMeanMap
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    Integrable (fun ω : ℕ → ℝ =>
      (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2)
      (markovPathMeasure μ₀ (Hkernel A ρ N)) := by
  let B : ℝ := (ρ⁻¹ + 1 / 2) ^ 2
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hmeas : AEStronglyMeasurable (fun ω : ℕ → ℝ =>
      (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2)
      (markovPathMeasure μ₀ (Hkernel A ρ N)) := by
    apply Measurable.aestronglyMeasurable
    exact ((measurable_pi_apply (t + 1)).sub
      ((continuous_roundedMeanMap hA hρ hρ_lt).measurable.comp
        (measurable_pi_apply t))).pow_const 2
  refine Integrable.mono' (integrable_const (B ^ 2)) hmeas ?_
  filter_upwards [markovPathMeasure_ae_eval_succ_mem_Icc hρ hN μ₀ t] with ω hω
  have hVnonneg : 0 ≤ roundedMeanMap A ρ (ω t) :=
    roundedMeanMap_nonneg A ρ (ω t)
  have hVle : roundedMeanMap A ρ (ω t) ≤ B := by
    exact roundedMeanMap_le_sq hρ
  have hXle : ω (t + 1) ≤ B := by
    simpa [B] using hω.2
  have habs :
      |ω (t + 1) - roundedMeanMap A ρ (ω t)| ≤ B := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hω.1, hXle]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) habs 2

/-- The centered next-step innovation is integrable on the canonical path
space. -/
lemma integrable_next_sub_roundedMeanMap
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    Integrable (fun ω : ℕ → ℝ =>
      ω (t + 1) - roundedMeanMap A ρ (ω t))
      (markovPathMeasure μ₀ (Hkernel A ρ N)) := by
  have hmeas : AEStronglyMeasurable (fun ω : ℕ → ℝ =>
      ω (t + 1) - roundedMeanMap A ρ (ω t))
      (markovPathMeasure μ₀ (Hkernel A ρ N)) := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_pi_apply (t + 1)).sub
      ((continuous_roundedMeanMap hA hρ hρ_lt).measurable.comp
        (measurable_pi_apply t))
  exact ((memLp_two_iff_integrable_sq hmeas).2
    (integrable_sq_next_sub_roundedMeanMap hA hρ hρ_lt hN μ₀ t)).integrable
      (by norm_num)

/-- The stopped normalized noise is integrable under the canonical
Dirac-started rounded-radius path law. -/
lemma integrable_stoppedNormalizedRadiusNoise_succ
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    Integrable
      (stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1))
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
  change Integrable
    ({ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}.indicator
      (fun ω =>
        roundedBeta A ρ a (roundedOrbit A ρ h₀ t) *
          normalizedRadiusNoise A ρ h₀ a t ω))
    (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))
  have hscaled : Integrable
      (fun ω : ℕ → ℝ =>
        roundedBeta A ρ a (roundedOrbit A ρ h₀ t) *
          normalizedRadiusNoise A ρ h₀ a t ω)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
    unfold normalizedRadiusNoise radiusNoise
    exact
      ((integrable_next_sub_roundedMeanMap
          hA hρ hρ_lt hN (Measure.dirac h₀) t).div_const
        (roundedOrbit A ρ h₀ t + a)).const_mul
        (roundedBeta A ρ a (roundedOrbit A ρ h₀ t))
  exact hscaled.indicator
    ((Filtration.piLE (X := fun _ : ℕ => ℝ)).le t _
      (measurableSet_lt_radiusTrackingExitTime htT))

/-- The square of the stopped normalized successor noise is integrable under
the canonical Dirac-started rounded-radius path law. -/
lemma integrable_sq_stoppedNormalizedRadiusNoise_succ
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    Integrable
      (fun ω =>
        stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
  let S : Set (ℕ → ℝ) :=
    {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}
  let e : (ℕ → ℝ) → ℝ :=
    fun ω =>
      roundedBeta A ρ a (roundedOrbit A ρ h₀ t) *
        normalizedRadiusNoise A ρ h₀ a t ω
  have he_sq : Integrable (fun ω => e ω ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
    have hraw :=
      (integrable_sq_next_sub_roundedMeanMap
        hA hρ hρ_lt hN (Measure.dirac h₀) t).div_const
          ((roundedOrbit A ρ h₀ t + a) ^ 2) |>.const_mul
            (roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2)
    convert hraw using 1
    funext ω
    simp only [e, normalizedRadiusNoise, radiusNoise, mul_pow, div_pow]
  have hsquare :
      (fun ω =>
        stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2) =
        S.indicator (fun ω => e ω ^ 2) := by
    funext ω
    by_cases hω : ω ∈ S
    · rw [stoppedNormalizedRadiusNoise_succ,
        Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    · rw [stoppedNormalizedRadiusNoise_succ,
        Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]
      simp
  rw [hsquare]
  exact he_sq.indicator
    ((Filtration.piLE (X := fun _ : ℕ => ℝ)).le t _
      (measurableSet_lt_radiusTrackingExitTime htT))

/-- The product of the stopped normalized drift and successor noise is
integrable under the canonical Dirac-started rounded-radius path law. -/
lemma integrable_stoppedRadiusDrift_mul_stoppedNormalizedRadiusNoise_succ
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    Integrable (fun ω =>
      stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
        normalizedRadiusError A ρ h₀ a t ω *
          stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
  have hdrift_meas : AEStronglyMeasurable (fun ω =>
      stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
        normalizedRadiusError A ρ h₀ a t ω)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    ((stronglyMeasurable_stoppedRadiusMultiplier_mul_normalizedRadiusError
      hA hρ hρ_lt h₀ a δ htT).mono
        ((Filtration.piLE (X := fun _ : ℕ => ℝ)).le t)).aestronglyMeasurable
  have hdrift : MemLp (fun ω =>
      stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
        normalizedRadiusError A ρ h₀ a t ω) 2
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    (memLp_two_iff_integrable_sq hdrift_meas).2
      (integrable_sq_stoppedRadiusMultiplier_mul_normalizedRadiusError
        hA hρ hρ_lt hh₀ ha hδ hN htT)
  have hnoise_int : Integrable
      (stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1))
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    integrable_stoppedNormalizedRadiusNoise_succ
      (h₀ := h₀) (a := a) (δ := δ) hA hρ hρ_lt hN htT
  have hnoise : MemLp
      (stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1)) 2
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    (memLp_two_iff_integrable_sq hnoise_int.aestronglyMeasurable).2
      (integrable_sq_stoppedNormalizedRadiusNoise_succ
        (h₀ := h₀) (a := a) (δ := δ) hA hρ hρ_lt hN htT)
  change Integrable
    ((fun ω =>
      stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
        normalizedRadiusError A ρ h₀ a t ω) *
      stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1))
    (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))
  exact hdrift.integrable_mul hnoise

/-- The squared sum of the stopped normalized drift and successor noise is
integrable under the canonical Dirac-started rounded-radius path law. -/
lemma integrable_sq_stoppedRadiusDrift_add_stoppedNormalizedRadiusNoise_succ
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    Integrable (fun ω =>
      (stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
          normalizedRadiusError A ρ h₀ a t ω +
        stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω) ^ 2)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
  have hdrift :=
    integrable_sq_stoppedRadiusMultiplier_mul_normalizedRadiusError
      hA hρ hρ_lt hh₀ ha hδ hN htT
  have hcross :=
    integrable_stoppedRadiusDrift_mul_stoppedNormalizedRadiusNoise_succ
      hA hρ hρ_lt hh₀ ha hδ hN htT
  have hnoise :=
    integrable_sq_stoppedNormalizedRadiusNoise_succ
      (h₀ := h₀) (a := a) (δ := δ) hA hρ hρ_lt hN htT
  have hexpand := hdrift.add ((hcross.const_mul 2).add hnoise)
  have hfun :
      (fun ω =>
        (stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
            normalizedRadiusError A ρ h₀ a t ω +
          stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω) ^ 2) =
        ((fun ω =>
          (stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
            normalizedRadiusError A ρ h₀ a t ω) ^ 2) +
          ((fun ω =>
            2 * (stoppedRadiusMultiplier A ρ h₀ a δ T t ω *
              normalizedRadiusError A ρ h₀ a t ω *
                stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω)) +
            fun ω =>
              stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2)) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  rw [hfun]
  exact hexpand

/-- The exact conditional centered-square identity with its integrability
hypothesis discharged from compact support. -/
lemma condExp_sq_next_sub_roundedMeanMap_eq
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    (markovPathMeasure μ₀ (Hkernel A ρ N))[
        fun ω => (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2 |
        Filtration.piLE t]
      =ᵐ[markovPathMeasure μ₀ (Hkernel A ρ N)]
        fun ω =>
          ∫ g, (Hmap A ρ N (ω t) g - roundedMeanMap A ρ (ω t)) ^ 2
            ∂(gaussianVec N) :=
  condExp_sq_next_sub_roundedMeanMap hA hρ hρ_lt N μ₀ t
    (integrable_sq_next_sub_roundedMeanMap hA hρ hρ_lt hN μ₀ t)

/-- The canonical next-step innovation is conditionally centered with respect
to the coordinate-prefix filtration. -/
lemma condExp_next_sub_roundedMeanMap_eq_zero
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    (markovPathMeasure μ₀ (Hkernel A ρ N))[
        fun ω => ω (t + 1) - roundedMeanMap A ρ (ω t) |
        Filtration.piLE t]
      =ᵐ[markovPathMeasure μ₀ (Hkernel A ρ N)] 0 := by
  let ψ : ((((i : Finset.Iic t) → ℝ) × ℝ) → ℝ) :=
    fun p => p.2 -
      roundedMeanMap A ρ (p.1 ⟨t, Finset.mem_Iic.mpr le_rfl⟩)
  have hψ : StronglyMeasurable ψ := by
    apply Continuous.stronglyMeasurable
    dsimp [ψ]
    exact continuous_snd.sub
      ((continuous_roundedMeanMap hA hρ hρ_lt).comp
        ((continuous_apply _).comp continuous_fst))
  have hcond :=
    condExp_markovPathMeasure_prefix_eval_succ_piLE
      μ₀ (Hkernel A ρ N) t hψ
      (integrable_next_sub_roundedMeanMap hA hρ hρ_lt hN μ₀ t)
  refine hcond.trans ?_
  filter_upwards with ω
  exact integral_Hkernel_sub_roundedMeanMap_eq_zero hρ hN

/-- The stopped normalized successor noise is conditionally centered under
the canonical Dirac-started rounded-radius path law. -/
lemma condExp_stoppedNormalizedRadiusNoise_succ_eq_zero
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
        stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) |
        Filtration.piLE t]
      =ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)] 0 := by
  let S : Set (ℕ → ℝ) :=
    {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}
  let c : ℝ :=
    roundedBeta A ρ a (roundedOrbit A ρ h₀ t) /
      (roundedOrbit A ρ h₀ t + a)
  let f : (ℕ → ℝ) → ℝ := S.indicator (fun _ => c)
  let ξ : (ℕ → ℝ) → ℝ :=
    fun ω => ω (t + 1) - roundedMeanMap A ρ (ω t)
  have hS : MeasurableSet[Filtration.piLE t] S := by
    exact measurableSet_lt_radiusTrackingExitTime htT
  have hf : StronglyMeasurable[Filtration.piLE t] f := by
    exact (measurable_const.indicator hS).stronglyMeasurable
  have hprod :
      f * ξ =
        stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) := by
    funext ω
    by_cases hω : ω ∈ S
    · simp only [Pi.mul_apply, f, Set.indicator_of_mem hω, ξ, c]
      rw [stoppedNormalizedRadiusNoise_succ, Set.indicator_of_mem]
      · simp only [normalizedRadiusNoise, radiusNoise]
        ring
      · exact hω
    · simp only [Pi.mul_apply, f, Set.indicator_of_notMem hω, zero_mul]
      rw [stoppedNormalizedRadiusNoise_succ, Set.indicator_of_notMem]
      exact hω
  have hξ : Integrable ξ
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
    exact integrable_next_sub_roundedMeanMap
      hA hρ hρ_lt hN (Measure.dirac h₀) t
  have hprod_int : Integrable (f * ξ)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
    rw [hprod]
    exact integrable_stoppedNormalizedRadiusNoise_succ
      hA hρ hρ_lt hN htT
  rw [← hprod]
  refine (condExp_mul_of_aestronglyMeasurable_left
    hf.aestronglyMeasurable hprod_int hξ).trans ?_
  filter_upwards [
    condExp_next_sub_roundedMeanMap_eq_zero
      hA hρ hρ_lt hN (Measure.dirac h₀) t] with ω hω
  have hξω :
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
          ξ | Filtration.piLE t] ω = 0 := by
    simpa only [ξ, Pi.zero_apply] using hω
  rw [Pi.mul_apply, hξω, mul_zero]
  rfl

/-- Exact conditional second-moment identity for the stopped normalized
successor noise under the canonical Dirac-started path law. -/
lemma condExp_sq_stoppedNormalizedRadiusNoise_succ
    {A ρ h₀ a δ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T) :
    (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
        fun ω =>
          stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2 |
        Filtration.piLE t]
      =ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
        fun ω =>
          {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}.indicator
              (fun _ =>
                (roundedBeta A ρ a (roundedOrbit A ρ h₀ t) /
                  (roundedOrbit A ρ h₀ t + a)) ^ 2) ω *
            (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
              fun ω =>
                (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2 |
              Filtration.piLE t] ω := by
  let S : Set (ℕ → ℝ) :=
    {ω | t < radiusTrackingExitTime A ρ h₀ a δ T ω}
  let c : ℝ :=
    (roundedBeta A ρ a (roundedOrbit A ρ h₀ t) /
      (roundedOrbit A ρ h₀ t + a)) ^ 2
  let f : (ℕ → ℝ) → ℝ := S.indicator (fun _ => c)
  let ξ : (ℕ → ℝ) → ℝ :=
    fun ω => (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2
  have hS : MeasurableSet[Filtration.piLE t] S :=
    measurableSet_lt_radiusTrackingExitTime htT
  have hf : StronglyMeasurable[Filtration.piLE t] f :=
    (measurable_const.indicator hS).stronglyMeasurable
  have hprod :
      f * ξ = fun ω =>
        stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2 := by
    funext ω
    by_cases hω : ω ∈ S
    · simp only [Pi.mul_apply, f, Set.indicator_of_mem hω, c, ξ]
      rw [stoppedNormalizedRadiusNoise_succ, Set.indicator_of_mem]
      · simp only [normalizedRadiusNoise, radiusNoise, mul_pow, div_pow]
        ring
      · exact hω
    · simp only [Pi.mul_apply, f, Set.indicator_of_notMem hω, zero_mul]
      rw [stoppedNormalizedRadiusNoise_succ, Set.indicator_of_notMem]
      · simp
      · exact hω
  have hξ : Integrable ξ
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) :=
    integrable_sq_next_sub_roundedMeanMap
      hA hρ hρ_lt hN (Measure.dirac h₀) t
  have hprod_int : Integrable (f * ξ)
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) := by
    rw [hprod]
    exact integrable_sq_stoppedNormalizedRadiusNoise_succ
      hA hρ hρ_lt hN htT
  rw [← hprod]
  refine (condExp_mul_of_aestronglyMeasurable_left
    hf.aestronglyMeasurable hprod_int hξ).trans ?_
  filter_upwards with ω
  rfl

/-- The centered one-step rounded radius has the `N⁻¹` second-moment bound
coming from its independent Gaussian coordinates. -/
lemma integral_sq_Hmap_sub_roundedMeanMap_le
    {A ρ h : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : 0 < N) :
    ∫ g, (Hmap A ρ N h g - roundedMeanMap A ρ h) ^ 2
        ∂(gaussianVec N) ≤
      (N : ℝ)⁻¹ *
        ∫ g, (roundedCoordinateObservable A ρ h g) ^ 2
          ∂(gaussianReal 0 1) := by
  let U : ℝ → ℝ := roundedCoordinateObservable A ρ h
  have hUmeas : AEStronglyMeasurable U (gaussianReal 0 1) :=
    (measurable_roundedCoordinateObservable A ρ h).aestronglyMeasurable
  have hUmem : MemLp U 2 (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq hUmeas).2
      (integrable_pow_roundedCoordinateObservable hρ 2)
  have hvarSum :
      variance (fun g : Fin N → ℝ => ∑ i, U (g i)) (gaussianVec N) =
        ∑ _i : Fin N, variance U (gaussianReal 0 1) := by
    unfold gaussianVec
    rw [show (fun g : Fin N → ℝ => ∑ i, U (g i)) =
        ∑ i, fun g : Fin N → ℝ => U (g i) by
      funext g
      simp]
    exact variance_sum_pi (X := fun _ : Fin N => U) fun _ => hUmem
  have hHmeas : AEMeasurable (Hmap A ρ N h) (gaussianVec N) := by
    apply Measurable.aemeasurable
    unfold Hmap
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_roundedCoordinateObservable A ρ h).comp
      (measurable_pi_apply i)
  rw [← integral_Hmap_eq_roundedMeanMap hρ hN.ne', ← variance_eq_integral hHmeas]
  have hvarH :
      variance (Hmap A ρ N h) (gaussianVec N) =
        (N : ℝ)⁻¹ ^ 2 *
          ((N : ℝ) * variance U (gaussianReal 0 1)) := by
    unfold Hmap
    rw [variance_const_mul]
    change (N : ℝ)⁻¹ ^ 2 *
        variance (fun g : Fin N → ℝ => ∑ i, U (g i)) (gaussianVec N) =
      _
    rw [hvarSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hvarH]
  have hvar_le :
      variance U (gaussianReal 0 1) ≤
        ∫ g, U g ^ 2 ∂(gaussianReal 0 1) := by
    rw [variance_eq_sub hUmem]
    exact sub_le_self _ (sq_nonneg _)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (N : ℝ)⁻¹ ^ 2 *
        ((N : ℝ) * variance U (gaussianReal 0 1)) ≤
      (N : ℝ)⁻¹ ^ 2 *
        ((N : ℝ) * ∫ g, U g ^ 2 ∂(gaussianReal 0 1)) := by
      gcongr
    _ = (N : ℝ)⁻¹ *
        ∫ g, (roundedCoordinateObservable A ρ h g) ^ 2
          ∂(gaussianReal 0 1) := by
      dsimp [U]
      field_simp [hNreal.ne']

/-- A nonzero rounded coordinate must cross the first admissible rounding
threshold. -/
lemma roundedLayerThreshold_zero_lt_of_observable_ne_zero
    {A ρ h g : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hne : roundedCoordinateObservable A ρ h g ≠ 0) :
    roundedLayerThreshold ρ 0 < A * Real.sqrt h * |g| := by
  have hQ :
      Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) ≠ 0 := by
    intro hzero
    apply hne
    simp [roundedCoordinateObservable, hzero]
  have hcross :
      1 / 2 < |ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)| := by
    have hnot :
        ¬ |ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)| ≤ 2⁻¹ := by
      intro hle
      exact hQ ((Q₁_zero_iff _).mpr hle)
    norm_num at hnot ⊢
    exact hnot
  have hadmissible : ρ * (((0 : ℕ) : ℝ) + 1 / 2) < 1 := by
    norm_num
    linarith
  have hthreshold :=
    (abs_inv_mul_tanh_gt_iff hρ hadmissible
      (A * Real.sqrt h * g)).mp (by
        simpa only [Nat.cast_zero, zero_add, mul_assoc] using hcross)
  simpa [abs_mul, abs_of_pos hA, abs_of_nonneg (Real.sqrt_nonneg h)] using
    hthreshold

/-- Near the origin, nonzero rounded output has exponentially small Gaussian
probability. -/
lemma measureReal_roundedCoordinateObservable_ne_zero_le
    {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hh : 0 < h) :
    (gaussianReal 0 1).real
        {g : ℝ | roundedCoordinateObservable A ρ h g ≠ 0} ≤
      2 * Real.exp
        (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2) := by
  let b := roundedLayerThreshold ρ 0
  have hb : 0 ≤ b := (roundedLayerThreshold_zero_pos hρ hρ_lt).le
  have hsubset :
      {g : ℝ | roundedCoordinateObservable A ρ h g ≠ 0} ⊆
        {g : ℝ | b < |A * Real.sqrt h * g|} := by
    intro g hg
    have hthreshold :=
      roundedLayerThreshold_zero_lt_of_observable_ne_zero
        hA hρ hρ_lt hg
    simpa [b, abs_mul, abs_of_pos hA,
      abs_of_nonneg (Real.sqrt_nonneg h)] using hthreshold
  calc
    (gaussianReal 0 1).real
        {g : ℝ | roundedCoordinateObservable A ρ h g ≠ 0} ≤
        (gaussianReal 0 1).real
          {g : ℝ | b < |A * Real.sqrt h * g|} :=
      measureReal_mono hsubset
    _ = 2 * gaussianUpperTail (b / (A * Real.sqrt h)) :=
      gaussianReal_abs_scale_gt hA hh hb
    _ ≤ 2 * Real.exp (-((b / (A * Real.sqrt h)) ^ 2) / 2) :=
      mul_le_mul_of_nonneg_left
        (gaussianUpperTail_le_exp_neg_sq_div_two
          (div_nonneg hb (mul_nonneg hA.le (Real.sqrt_nonneg h))))
        (by norm_num)
    _ = 2 * Real.exp
        (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2) := rfl

/-- Fixed moments inherit the exponentially small support probability near the
origin. -/
lemma integral_pow_roundedCoordinateObservable_le_exp
    {A ρ h : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hh : 0 < h)
    (p : ℕ) (hp : 1 ≤ p) :
    ∫ g, (roundedCoordinateObservable A ρ h g) ^ p
        ∂(gaussianReal 0 1) ≤
      2 * (ρ⁻¹ + 1 / 2) ^ (2 * p) *
        Real.exp
          (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2) := by
  let S : Set ℝ := {g | roundedCoordinateObservable A ρ h g ≠ 0}
  let B : ℝ := (ρ⁻¹ + 1 / 2) ^ (2 * p)
  have hS : MeasurableSet S := by
    change MeasurableSet
      ((roundedCoordinateObservable A ρ h) ⁻¹' ({0} : Set ℝ)ᶜ)
    exact measurable_roundedCoordinateObservable A ρ h
      (measurableSet_singleton (0 : ℝ)).compl
  have hB : 0 ≤ B := by
    exact pow_nonneg (by positivity) _
  have hf :
      Integrable (fun g => (roundedCoordinateObservable A ρ h g) ^ p)
        (gaussianReal 0 1) :=
    integrable_pow_roundedCoordinateObservable hρ p
  have hind : Integrable (S.indicator fun _ : ℝ => B) (gaussianReal 0 1) :=
    (integrable_const B).indicator hS
  have hpoint :
      ∀ g : ℝ, (roundedCoordinateObservable A ρ h g) ^ p ≤
        S.indicator (fun _ : ℝ => B) g := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      exact (pow_le_pow_left₀
        (roundedCoordinateObservable_nonneg A ρ h g)
        (roundedCoordinateObservable_le_sq hρ) p).trans_eq (by
          rw [show B = ((ρ⁻¹ + 1 / 2) ^ 2) ^ p by
            simp [B, pow_mul]])
    · rw [Set.indicator_of_notMem hg]
      have hzero : roundedCoordinateObservable A ρ h g = 0 := by
        simpa [S] using hg
      simp [hzero, Nat.ne_of_gt hp]
  calc
    ∫ g, (roundedCoordinateObservable A ρ h g) ^ p
        ∂(gaussianReal 0 1) ≤
        ∫ g, S.indicator (fun _ : ℝ => B) g ∂(gaussianReal 0 1) :=
      integral_mono_ae hf hind (Filter.Eventually.of_forall hpoint)
    _ = B * (gaussianReal 0 1).real S := by
      rw [integral_indicator_const B hS, smul_eq_mul]
      ring
    _ ≤ B * (2 * Real.exp
        (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2)) :=
      mul_le_mul_of_nonneg_left
        (measureReal_roundedCoordinateObservable_ne_zero_le
          hA hρ hρ_lt hh) hB
    _ = 2 * (ρ⁻¹ + 1 / 2) ^ (2 * p) *
        Real.exp
          (-((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2) := by
      simp [B]
      ring

/-- The Gaussian support exponent is the paper's positive constant divided by
the radius. -/
lemma roundedSupportExponent_eq {A ρ h : ℝ}
    (hA : 0 < A) (hh : 0 < h) :
    (roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2 / 2 =
      (roundedLayerThreshold ρ 0) ^ 2 / (2 * A ^ 2) / h := by
  have hsqrt : Real.sqrt h ≠ 0 := (Real.sqrt_pos.2 hh).ne'
  have hsqrt_sq : (Real.sqrt h) ^ 2 = h := Real.sq_sqrt hh.le
  field_simp [hA.ne', hsqrt]
  nlinarith

/-- Exponential decay in the inverse radius dominates every fixed natural
power, uniformly on the unit radius interval. -/
lemma exists_pos_exp_neg_div_le_mul_pow {c : ℝ} (hc : 0 < c) (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      Real.exp (-c / h) ≤ C * h ^ p := by
  let f : ℝ → ℝ :=
    (fun x : ℝ =>
      (Polynomial.X ^ p).eval x⁻¹ * expNegInvGlue x) ∘
      fun h : ℝ => h / c
  have hf : Continuous f :=
    (expNegInvGlue.continuous_polynomial_eval_inv_mul
      (Polynomial.X ^ p)).comp (continuous_id.div_const c)
  obtain ⟨M, hM⟩ :=
    isCompact_Icc.bddAbove_image hf.continuousOn
  let D := max 1 M
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  let C := D / c ^ p
  have hcPow : 0 < c ^ p := pow_pos hc p
  refine ⟨C, div_pos hD hcPow, ?_⟩
  intro h hh hh_one
  have hf_le : f h ≤ D :=
    (hM ⟨h, ⟨hh.le, hh_one⟩, rfl⟩).trans (le_max_right _ _)
  have hf_eq :
      f h = (c / h) ^ p * Real.exp (-c / h) := by
    simp only [f, Function.comp_apply, Polynomial.eval_pow, Polynomial.eval_X]
    rw [show expNegInvGlue (h / c) = Real.exp (-c / h) by
      simp [expNegInvGlue, not_le.mpr (div_pos hh hc)]
      field_simp [hc.ne', hh.ne']]
    congr 2
    field_simp [hc.ne', hh.ne']
  calc
    Real.exp (-c / h) =
        (h ^ p / c ^ p) * f h := by
      rw [hf_eq, div_pow]
      field_simp [hc.ne', hh.ne']
    _ ≤ (h ^ p / c ^ p) * D :=
      mul_le_mul_of_nonneg_left hf_le (div_nonneg (pow_nonneg hh.le p) hcPow.le)
    _ = C * h ^ p := by
      dsimp [C]
      field_simp [hc.ne']

/-- The paper's fixed-moment bound for one rounded coordinate: its `p`-th
moment is at most a constant times the `p`-th power of the radius. -/
lemma exists_pos_integral_pow_roundedCoordinateObservable_le_mul_pow
    {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 ≤ h →
      ∫ g, (roundedCoordinateObservable A ρ h g) ^ p
          ∂(gaussianReal 0 1) ≤ C * h ^ p := by
  let c := (roundedLayerThreshold ρ 0) ^ 2 / (2 * A ^ 2)
  have hc : 0 < c := by
    have hb := roundedLayerThreshold_zero_pos hρ hρ_lt
    dsimp [c]
    exact div_pos (sq_pos_of_pos hb)
      (mul_pos (by norm_num) (sq_pos_of_pos hA))
  obtain ⟨D, hD, hdecay⟩ :=
    exists_pos_exp_neg_div_le_mul_pow hc p
  let S : ℝ := (ρ⁻¹ + 1 / 2) ^ (2 * p)
  have hbase : 0 < ρ⁻¹ + 1 / 2 := by positivity
  have hS : 0 < S := pow_pos hbase _
  let C := max (2 * S * D) S
  have hC : 0 < C := hS.trans_le (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro h hh
  rcases hh.eq_or_lt with rfl | hh
  · have hQ : Q₁ (0 : ℝ) = 0 := (Q₁_zero_iff 0).mpr (by norm_num)
    simp [roundedCoordinateObservable, hQ, Nat.ne_of_gt hp]
  · by_cases hh_one : h ≤ 1
    · have hmoment :=
        integral_pow_roundedCoordinateObservable_le_exp
          hA hρ hρ_lt hh p hp
      have hrate :
          (roundedLayerThreshold ρ 0) ^ 2 / (2 * A ^ 2) = c := rfl
      have hexponent :
          -((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2 =
            -c / h := by
        rw [show
          -((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2) / 2 =
            -((roundedLayerThreshold ρ 0 / (A * Real.sqrt h)) ^ 2 / 2) by ring,
          roundedSupportExponent_eq hA hh, hrate]
        ring
      rw [hexponent] at hmoment
      calc
        ∫ g, (roundedCoordinateObservable A ρ h g) ^ p
            ∂(gaussianReal 0 1) ≤
            2 * S * Real.exp (-c / h) := by
          simpa [S] using hmoment
        _ ≤ 2 * S * (D * h ^ p) := by
          gcongr
          exact hdecay h hh hh_one
        _ = (2 * S * D) * h ^ p := by ring
        _ ≤ C * h ^ p := by
          gcongr
          exact le_max_left _ _
    · have hone : 1 ≤ h := (not_le.mp hh_one).le
      have hpoint :
          ∀ g : ℝ, (roundedCoordinateObservable A ρ h g) ^ p ≤ S := by
        intro g
        exact (pow_le_pow_left₀
          (roundedCoordinateObservable_nonneg A ρ h g)
          (roundedCoordinateObservable_le_sq hρ) p).trans_eq (by
            simp [S, pow_mul])
      have hintegral :
          ∫ g, (roundedCoordinateObservable A ρ h g) ^ p
              ∂(gaussianReal 0 1) ≤ S := by
        calc
          ∫ g, (roundedCoordinateObservable A ρ h g) ^ p
              ∂(gaussianReal 0 1) ≤
              ∫ _ : ℝ, S ∂(gaussianReal 0 1) :=
            integral_mono
              (integrable_pow_roundedCoordinateObservable hρ p)
              (integrable_const S) hpoint
          _ = S := by simp
      calc
        ∫ g, (roundedCoordinateObservable A ρ h g) ^ p
            ∂(gaussianReal 0 1) ≤ S := hintegral
        _ ≤ C := le_max_right _ _
        _ ≤ C * h ^ p :=
          le_mul_of_one_le_right hC.le (one_le_pow₀ hone)

/-- The unconditional form of the paper's fixed-precision one-step noise
variance estimate. -/
lemma exists_pos_integral_sq_Hmap_sub_roundedMeanMap_le
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ h : ℝ, 0 ≤ h →
      ∫ g, (Hmap A ρ N h g - roundedMeanMap A ρ h) ^ 2
          ∂(gaussianVec N) ≤
        C * (N : ℝ)⁻¹ * h ^ 2 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_pos_integral_pow_roundedCoordinateObservable_le_mul_pow
      hA hρ hρ_lt 2 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro N hN h hh
  calc
    ∫ g, (Hmap A ρ N h g - roundedMeanMap A ρ h) ^ 2
        ∂(gaussianVec N) ≤
      (N : ℝ)⁻¹ *
        ∫ g, (roundedCoordinateObservable A ρ h g) ^ 2
          ∂(gaussianReal 0 1) :=
      integral_sq_Hmap_sub_roundedMeanMap_le hρ hN
    _ ≤ (N : ℝ)⁻¹ * (C * h ^ 2) := by
      gcongr
      exact hmoment h hh
    _ = C * (N : ℝ)⁻¹ * h ^ 2 := by ring

/-- The canonical-path conditional form of the paper's one-step noise
variance estimate. -/
lemma exists_pos_condExp_sq_next_sub_roundedMeanMap_le
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ}, 0 < N →
        ∀ (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ),
          (∀ᵐ ω ∂(markovPathMeasure μ₀ (Hkernel A ρ N)), 0 ≤ ω t) →
          (markovPathMeasure μ₀ (Hkernel A ρ N))[
              fun ω => (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2 |
              Filtration.piLE t]
            ≤ᵐ[markovPathMeasure μ₀ (Hkernel A ρ N)]
              fun ω => C * (N : ℝ)⁻¹ * (ω t) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_integral_sq_Hmap_sub_roundedMeanMap_le hA hρ hρ_lt
  refine ⟨C, hC, ?_⟩
  intro N hN μ₀ _ t hnonneg
  have heq :=
    condExp_sq_next_sub_roundedMeanMap_eq
      hA hρ hρ_lt hN μ₀ t
  filter_upwards [heq, hnonneg] with ω hω_eq hω_nonneg
  rw [hω_eq]
  exact hbound N hN (ω t) hω_nonneg

/-- On an a.e. radius-tracking event, the canonical one-step conditional
noise is controlled by the deterministic tracked radius and terminal scale. -/
lemma exists_pos_condExp_sq_next_sub_roundedMeanMap_le_of_tracking
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    {N : ℕ} (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℕ) (h a δ : ℝ),
      0 ≤ h → 0 ≤ a → 0 ≤ δ →
      (∀ᵐ ω ∂(markovPathMeasure μ₀ (Hkernel A ρ N)),
        0 ≤ ω t ∧ |ω t - h| ≤ δ * (h + a)) →
      (markovPathMeasure μ₀ (Hkernel A ρ N))[
          fun ω => (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2 |
          Filtration.piLE t]
        ≤ᵐ[markovPathMeasure μ₀ (Hkernel A ρ N)]
          fun _ => C * (1 + δ) ^ 2 * (N : ℝ)⁻¹ * (h + a) ^ 2 := by
  obtain ⟨C, hC, hnoise⟩ :=
    exists_pos_condExp_sq_next_sub_roundedMeanMap_le
      hA hρ hρ_lt
  refine ⟨C, hC, ?_⟩
  intro t h a δ hh ha hδ htracking
  have hnonneg :
      ∀ᵐ ω ∂(markovPathMeasure μ₀ (Hkernel A ρ N)), 0 ≤ ω t :=
    htracking.mono fun _ hω => hω.1
  filter_upwards [hnoise hN μ₀ t hnonneg, htracking] with ω hω_noise hω_tracking
  calc
    (markovPathMeasure μ₀ (Hkernel A ρ N))[
        fun ω => (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2 |
        Filtration.piLE t] ω ≤
        C * (N : ℝ)⁻¹ * (ω t) ^ 2 := hω_noise
    _ ≤ C * (N : ℝ)⁻¹ * ((1 + δ) ^ 2 * (h + a) ^ 2) := by
      gcongr
      exact state_sq_le_of_abs_sub_le_mul_add
        hω_tracking.1 hh ha hδ hω_tracking.2
    _ = C * (1 + δ) ^ 2 * (N : ℝ)⁻¹ * (h + a) ^ 2 := by ring

/-- A uniform raw conditional variance constant gives the stopped normalized
successor-noise bound, with the local tracking factor `(1 + δ)²`. -/
lemma condExp_sq_stoppedNormalizedRadiusNoise_succ_le_of_raw
    {A ρ h₀ a δ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T : ℕ} {C : ℝ} (hC : 0 < C)
    (hnoise : ∀ t : ℕ,
      (∀ᵐ ω ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)),
        0 ≤ ω t) →
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
          fun ω => (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2 |
          Filtration.piLE t]
        ≤ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
          fun ω => C * (N : ℝ)⁻¹ * (ω t) ^ 2) :
    ∀ t : ℕ, t ≤ T →
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
          fun ω =>
            stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2 |
          Filtration.piLE t]
        ≤ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
          fun _ =>
            (C * (1 + δ) ^ 2) * (N : ℝ)⁻¹ *
              roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2 := by
  let D := C * (1 + δ) ^ 2
  have hD : 0 < D := by
    exact mul_pos hC (sq_pos_of_pos (by linarith))
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hN
  intro t htT
  have hnonneg :
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)),
        0 ≤ ω t :=
    markovPathMeasure_dirac_ae_eval_nonneg (A := A) hh₀ hρ hN t
  have hraw := hnoise t hnonneg
  have heq :=
    condExp_sq_stoppedNormalizedRadiusNoise_succ
      (h₀ := h₀) (a := a) (δ := δ)
      hA hρ hρ_lt hN htT
  have horbit : 0 ≤ roundedOrbit A ρ h₀ t :=
    roundedOrbit_nonneg hh₀ t
  have hdenom : 0 < roundedOrbit A ρ h₀ t + a :=
    add_pos_of_nonneg_of_pos horbit ha
  filter_upwards [heq, hraw, hnonneg] with ω hω_eq hω_raw hω_nonneg
  rw [hω_eq]
  by_cases hsurv :
      t < radiusTrackingExitTime A ρ h₀ a δ T ω
  · rw [Set.indicator_of_mem
      (show ω ∈ {ω | t <
        radiusTrackingExitTime A ρ h₀ a δ T ω} from hsurv)]
    have hlocal :
        |ω t - roundedOrbit A ρ h₀ t| ≤
          δ * (roundedOrbit A ρ h₀ t + a) := by
      simpa [radiusTrackingGood, radiusTrackingError] using
        radiusTrackingGood_of_lt_exit htT hsurv
    have hstate :
        (ω t) ^ 2 ≤
          (1 + δ) ^ 2 * (roundedOrbit A ρ h₀ t + a) ^ 2 :=
      state_sq_le_of_abs_sub_le_mul_add
        hω_nonneg horbit ha.le hδ hlocal
    calc
      (roundedBeta A ρ a (roundedOrbit A ρ h₀ t) /
            (roundedOrbit A ρ h₀ t + a)) ^ 2 *
          (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
            fun ω =>
              (ω (t + 1) - roundedMeanMap A ρ (ω t)) ^ 2 |
            Filtration.piLE t] ω ≤
          (roundedBeta A ρ a (roundedOrbit A ρ h₀ t) /
              (roundedOrbit A ρ h₀ t + a)) ^ 2 *
            (C * (N : ℝ)⁻¹ * (ω t) ^ 2) :=
        mul_le_mul_of_nonneg_left hω_raw (sq_nonneg _)
      _ ≤
          (roundedBeta A ρ a (roundedOrbit A ρ h₀ t) /
              (roundedOrbit A ρ h₀ t + a)) ^ 2 *
            (C * (N : ℝ)⁻¹ *
              ((1 + δ) ^ 2 *
                (roundedOrbit A ρ h₀ t + a) ^ 2)) := by
        gcongr
      _ = D * (N : ℝ)⁻¹ *
          roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2 := by
        dsimp [D]
        field_simp [hdenom.ne']
  · rw [Set.indicator_of_notMem
      (show ω ∉ {ω | t <
        radiusTrackingExitTime A ρ h₀ a δ T ω} from hsurv),
      zero_mul]
    exact mul_nonneg
      (mul_nonneg hD.le (inv_nonneg.mpr hNreal.le))
      (sq_nonneg _)

/-- The stopped normalized successor noise has the conditional variance scale
`C N⁻¹ β_t²` used by the common stopped-moment estimate. -/
lemma exists_pos_condExp_sq_stoppedNormalizedRadiusNoise_succ_le
    {A ρ h₀ a δ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, t ≤ T →
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
          fun ω =>
            stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2 |
          Filtration.piLE t]
        ≤ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
          fun _ =>
            C * (N : ℝ)⁻¹ *
              roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2 := by
  obtain ⟨C, hC, hnoise⟩ :=
    exists_pos_condExp_sq_next_sub_roundedMeanMap_le
      hA hρ hρ_lt
  refine ⟨C * (1 + δ) ^ 2,
    mul_pos hC (sq_pos_of_pos (by linarith)), ?_⟩
  exact condExp_sq_stoppedNormalizedRadiusNoise_succ_le_of_raw
    hA hρ hρ_lt hh₀ ha hδ hN hC
      (hnoise hN (Measure.dirac h₀))

/-- For tracking tolerances `δ ≤ 1/4`, one positive constant controls the
stopped normalized successor-noise variance uniformly in the initial radius,
terminal scale, dimension, horizon, and time. -/
lemma exists_pos_uniform_condExp_sq_stoppedNormalizedRadiusNoise_succ_le
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {h₀ a δ : ℝ}, 0 ≤ h₀ → 0 < a → 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ {N : ℕ}, 0 < N → ∀ (T t : ℕ), t ≤ T →
          (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[
              fun ω =>
                stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2 |
              Filtration.piLE t]
            ≤ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
              fun _ =>
                D * (N : ℝ)⁻¹ *
                  roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2 := by
  obtain ⟨C, hC, hnoise⟩ :=
    exists_pos_condExp_sq_next_sub_roundedMeanMap_le hA hρ hρ_lt
  let D := C * (5 / 4 : ℝ) ^ 2
  have hD : 0 < D := mul_pos hC (sq_pos_of_pos (by norm_num))
  refine ⟨D, hD, ?_⟩
  intro h₀ a δ hh₀ ha hδ hδ_quarter N hN T t htT
  have hlocal :=
    condExp_sq_stoppedNormalizedRadiusNoise_succ_le_of_raw
      hA hρ hρ_lt hh₀ ha hδ hN hC
        (hnoise hN (Measure.dirac h₀)) t htT
  filter_upwards [hlocal] with ω hω
  refine hω.trans ?_
  dsimp [D]
  gcongr
  nlinarith

/-- The canonical stopped normalized-radius recursion satisfies the weighted
one-step conditional second-moment estimate. -/
lemma stoppedNormalizedRadiusError_condExp_step
    {A ρ h₀ a δ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {T t : ℕ} (htT : t ≤ T)
    {C : ℝ} (hC : 0 ≤ C)
    (hnoise :
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[fun ω =>
            stoppedNormalizedRadiusNoise A ρ h₀ a δ T (t + 1) ω ^ 2 |
          Filtration.piLE t]
        ≤ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
          fun _ =>
            C * (N : ℝ)⁻¹ *
              roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2) :
    (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[fun ω =>
          backWeight
              (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
              (T + 1) (t + 1) *
            stoppedValue (normalizedRadiusError A ρ h₀ a)
              (radiusTrackingExitTime A ρ h₀ a δ T) (t + 1) ω ^ 2 |
        Filtration.piLE t]
      ≤ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
        fun ω =>
          backWeight
              (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
              (T + 1) t *
            stoppedValue (normalizedRadiusError A ρ h₀ a)
              (radiusTrackingExitTime A ρ h₀ a δ T) t ω ^ 2 +
          backWeight
              (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
              (T + 1) (t + 1) *
            (C * (N : ℝ)⁻¹ *
              roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2) := by
  let α : ℕ → ℝ :=
    fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u)
  let R : ℕ → (ℕ → ℝ) → ℝ :=
    normalizedRadiusError A ρ h₀ a
  let M : ℕ → (ℕ → ℝ) → ℝ :=
    fun u => stoppedRadiusMultiplier A ρ h₀ a δ T u
  let η : ℕ → (ℕ → ℝ) → ℝ :=
    stoppedNormalizedRadiusNoise A ρ h₀ a δ T
  let τ : (ℕ → ℝ) → ℕ :=
    radiusTrackingExitTime A ρ h₀ a δ T
  let c : ℝ :=
    C * (N : ℝ)⁻¹ *
      roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2
  have ht : t < T + 1 := Nat.lt_succ_of_le htT
  have hc : 0 ≤ c := by
    exact mul_nonneg
      (mul_nonneg hC (inv_nonneg.mpr (Nat.cast_nonneg N)))
      (sq_nonneg _)
  have hstep := stopped_condExp_step
    (μ := markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))
    (ℱ := Filtration.piLE)
    (R := R) (A := M) (η := η) (τ := τ)
    (α := α t)
    (W₀ := backWeight α (T + 1) t)
    (W₁ := backWeight α (T + 1) (t + 1))
    (c := c)
    (measurableSet_lt_radiusTrackingExitTime htT)
    (fun ω hω =>
      normalizedRadiusError_succ_eq_stopped_of_lt_exit hh₀ ha hω)
    (stronglyMeasurable_stoppedNormalizedRadiusError
      A ρ h₀ a δ T t)
    (stronglyMeasurable_stoppedRadiusMultiplier_mul_normalizedRadiusError
      hA hρ hρ_lt h₀ a δ htT)
    (sq_stoppedRadiusMultiplier_le_roundedAlpha_sq_ae
      hA hρ hρ_lt hh₀ ha hδ hN htT)
    (condExp_stoppedNormalizedRadiusNoise_succ_eq_zero
      (h₀ := h₀) (a := a) (δ := δ) hA hρ hρ_lt hN htT)
    hnoise hc
    (backWeight_nonneg α (T + 1) (t + 1))
    (backWeight_succ_le ht)
    (sq_mul_backWeight_succ_le ht)
    (integrable_sq_stoppedRadiusMultiplier_mul_normalizedRadiusError
      hA hρ hρ_lt hh₀ ha hδ hN htT)
    (integrable_stoppedRadiusDrift_mul_stoppedNormalizedRadiusNoise_succ
      hA hρ hρ_lt hh₀ ha hδ hN htT)
    (integrable_sq_stoppedNormalizedRadiusNoise_succ
      (h₀ := h₀) (a := a) (δ := δ) hA hρ hρ_lt hN htT)
    (integrable_stoppedNormalizedRadiusNoise_succ
      (h₀ := h₀) (a := a) (δ := δ) hA hρ hρ_lt hN htT)
    (integrable_sq_stoppedRadiusDrift_add_stoppedNormalizedRadiusNoise_succ
      hA hρ hρ_lt hh₀ ha hδ hN htT)
    (integrable_weighted_sq_stoppedNormalizedRadiusError
      (δ := δ) hh₀ ha hρ hN T t
        (backWeight α (T + 1) (t + 1)))
  simpa only [α, R, M, η, τ, c] using hstep

/-- A single positive variance constant controls every weighted stopped
normalized-radius conditional step through the capped horizon. -/
lemma exists_pos_stoppedNormalizedRadiusError_condExp_step
    {A ρ h₀ a δ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) (T : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, t ≤ T →
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[fun ω =>
          backWeight
              (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
              (T + 1) (t + 1) *
            stoppedValue (normalizedRadiusError A ρ h₀ a)
              (radiusTrackingExitTime A ρ h₀ a δ T) (t + 1) ω ^ 2 |
        Filtration.piLE t]
        ≤ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
          fun ω =>
            backWeight
                (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                (T + 1) t *
              stoppedValue (normalizedRadiusError A ρ h₀ a)
                (radiusTrackingExitTime A ρ h₀ a δ T) t ω ^ 2 +
            backWeight
                (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                (T + 1) (t + 1) *
              (C * (N : ℝ)⁻¹ *
                roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2) := by
  obtain ⟨C, hC, hnoise⟩ :=
    exists_pos_condExp_sq_stoppedNormalizedRadiusNoise_succ_le
      hA hρ hρ_lt hh₀ ha hδ hN (T := T)
  refine ⟨C, hC, ?_⟩
  intro t htT
  exact stoppedNormalizedRadiusError_condExp_step
    hA hρ hρ_lt hh₀ ha hδ hN htT hC.le (hnoise t htT)

/-- One positive constant controls every weighted stopped normalized-error
conditional step uniformly in all radius-tracking parameters. -/
lemma exists_pos_uniform_stoppedNormalizedRadiusError_condExp_step
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {h₀ a δ : ℝ}, 0 ≤ h₀ → 0 < a → 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ {N : ℕ}, 0 < N → ∀ (T t : ℕ), t ≤ T →
          (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))[fun ω =>
              backWeight
                  (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                  (T + 1) (t + 1) *
                stoppedValue (normalizedRadiusError A ρ h₀ a)
                  (radiusTrackingExitTime A ρ h₀ a δ T) (t + 1) ω ^ 2 |
            Filtration.piLE t]
            ≤ᵐ[markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)]
              fun ω =>
                backWeight
                    (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                    (T + 1) t *
                  stoppedValue (normalizedRadiusError A ρ h₀ a)
                    (radiusTrackingExitTime A ρ h₀ a δ T) t ω ^ 2 +
                backWeight
                    (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                    (T + 1) (t + 1) *
                  (C * (N : ℝ)⁻¹ *
                    roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2) := by
  obtain ⟨C, hC, hnoise⟩ :=
    exists_pos_uniform_condExp_sq_stoppedNormalizedRadiusNoise_succ_le
      hA hρ hρ_lt
  refine ⟨C, hC, ?_⟩
  intro h₀ a δ hh₀ ha hδ hδ_quarter N hN T t htT
  exact stoppedNormalizedRadiusError_condExp_step
    hA hρ hρ_lt hh₀ ha hδ hN htT hC.le
      (hnoise hh₀ ha hδ hδ_quarter hN T t htT)

/-- Integrating the uniform conditional estimate gives the scalar weighted
stopped-moment recursion at every step through the capped horizon. -/
lemma exists_pos_stoppedNormalizedRadiusError_moment_recursion
    {A ρ h₀ a δ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) (T : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, t ≤ T →
      (∫ ω,
        backWeight
            (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
            (T + 1) (t + 1) *
          stoppedValue (normalizedRadiusError A ρ h₀ a)
            (radiusTrackingExitTime A ρ h₀ a δ T) (t + 1) ω ^ 2
        ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) ≤
        (∫ ω,
          backWeight
              (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
              (T + 1) t *
            stoppedValue (normalizedRadiusError A ρ h₀ a)
              (radiusTrackingExitTime A ρ h₀ a δ T) t ω ^ 2
          ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) +
        backWeight
            (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
            (T + 1) (t + 1) *
          (C * (N : ℝ)⁻¹ *
            roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2) := by
  obtain ⟨C, hC, hcond⟩ :=
    exists_pos_stoppedNormalizedRadiusError_condExp_step
      hA hρ hρ_lt hh₀ ha hδ hN T
  refine ⟨C, hC, ?_⟩
  intro t htT
  exact stopped_moment_recursion
    (hcond t htT)
    (integrable_weighted_sq_stoppedNormalizedRadiusError
      (δ := δ) hh₀ ha hρ hN T t
        (backWeight
          (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
          (T + 1) t))

/-- One positive constant controls the integrated weighted stopped-moment
recursion uniformly in all radius-tracking parameters. -/
lemma exists_pos_uniform_stoppedNormalizedRadiusError_moment_recursion
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {h₀ a δ : ℝ}, 0 ≤ h₀ → 0 < a → 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ {N : ℕ}, 0 < N → ∀ (T t : ℕ), t ≤ T →
          (∫ ω,
            backWeight
                (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                (T + 1) (t + 1) *
              stoppedValue (normalizedRadiusError A ρ h₀ a)
                (radiusTrackingExitTime A ρ h₀ a δ T) (t + 1) ω ^ 2
            ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) ≤
            (∫ ω,
              backWeight
                  (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                  (T + 1) t *
                stoppedValue (normalizedRadiusError A ρ h₀ a)
                  (radiusTrackingExitTime A ρ h₀ a δ T) t ω ^ 2
              ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) +
            backWeight
                (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                (T + 1) (t + 1) *
              (C * (N : ℝ)⁻¹ *
                roundedBeta A ρ a (roundedOrbit A ρ h₀ t) ^ 2) := by
  obtain ⟨C, hC, hcond⟩ :=
    exists_pos_uniform_stoppedNormalizedRadiusError_condExp_step
      hA hρ hρ_lt
  refine ⟨C, hC, ?_⟩
  intro h₀ a δ hh₀ ha hδ hδ_quarter N hN T t htT
  exact stopped_moment_recursion
    (hcond hh₀ ha hδ hδ_quarter hN T t htT)
    (integrable_weighted_sq_stoppedNormalizedRadiusError
      (δ := δ) hh₀ ha hρ hN T t
        (backWeight
          (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
          (T + 1) t))

/-- The stopped normalized tracking error at the capped endpoint has the
telescoped `N⁻¹` second-moment bound controlled by the deterministic tracking
amplification. -/
lemma exists_pos_stoppedNormalizedRadiusError_secondMoment_le
    {A ρ h₀ a δ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) (T : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∫ ω,
        stoppedValue (normalizedRadiusError A ρ h₀ a)
          (radiusTrackingExitTime A ρ h₀ a δ T) (T + 1) ω ^ 2
        ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) ≤
        ((T + 1 : ℕ) : ℝ) *
          (C *
            trackingAmplification
              (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
              (fun u => roundedBeta A ρ a (roundedOrbit A ρ h₀ u))
              (T + 1) ^ 2 / (N : ℝ)) := by
  let α : ℕ → ℝ :=
    fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u)
  let σ : ℕ → ℝ :=
    fun u => roundedBeta A ρ a (roundedOrbit A ρ h₀ u)
  let R : ℕ → (ℕ → ℝ) → ℝ :=
    normalizedRadiusError A ρ h₀ a
  let τ : (ℕ → ℝ) → ℕ :=
    radiusTrackingExitTime A ρ h₀ a δ T
  obtain ⟨C, hC, hrec⟩ :=
    exists_pos_stoppedNormalizedRadiusError_moment_recursion
      hA hρ hρ_lt hh₀ ha hδ hN T
  have hstep : ∀ t : ℕ, t < T + 1 →
      (∫ ω,
        backWeight α (T + 1) (t + 1) *
          stoppedValue R τ (t + 1) ω ^ 2
        ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) ≤
        (∫ ω,
          backWeight α (T + 1) t *
            stoppedValue R τ t ω ^ 2
          ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) +
        backWeight α (T + 1) (t + 1) *
          (C * σ t ^ 2 / (N : ℝ)) := by
    intro t ht
    have h := hrec t (Nat.le_of_lt_succ ht)
    simpa only [α, σ, R, τ, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using h
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hCN : 0 ≤ C / (N : ℝ) :=
    div_nonneg hC.le hNreal.le
  have hα : ∀ u : ℕ, u < T + 1 → 0 ≤ α u := by
    intro u hu
    exact roundedAlpha_nonneg hA hρ hρ_lt
      (roundedOrbit_nonneg hh₀ u) ha.le hδ
  have hσ : ∀ u : ℕ, u < T + 1 → 0 ≤ σ u := by
    intro u hu
    exact roundedBeta_nonneg (roundedOrbit_nonneg hh₀ u) ha.le
  have hamp : ∀ t : ℕ, t < T + 1 →
      backWeight α (T + 1) (t + 1) * σ t ^ 2 ≤
        trackingAmplification α σ (T + 1) ^ 2 :=
    fun t ht =>
      backWeight_mul_sigma_sq_le_trackingAmplification_sq
        hα ht (hσ t ht)
  have hbase := stopped_moment_backWeight_endpoints
    (R := R) (τ := τ) (α := α) (σ := σ)
    (T := T + 1) (C := C) (N := (N : ℝ))
    (K := trackingAmplification α σ (T + 1))
    hstep hCN hamp
  have hinit :
      ∫ ω, R 0 ω ^ 2
          ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [
      markovPathMeasure_dirac_ae_eval_zero_eq
        h₀ (Hkernel A ρ N)] with ω hω
    simp [R, normalizedRadiusError, radiusTrackingError, hω]
  rw [hinit, mul_zero, zero_add] at hbase
  refine ⟨C, hC, ?_⟩
  simpa only [α, σ, R, τ] using hbase

/-- One positive constant controls the stopped normalized tracking-error
endpoint second moment uniformly in all radius-tracking parameters. -/
lemma exists_pos_uniform_stoppedNormalizedRadiusError_secondMoment_le
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {h₀ a δ : ℝ}, 0 ≤ h₀ → 0 < a → 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ {N : ℕ}, 0 < N → ∀ T : ℕ,
          (∫ ω,
            stoppedValue (normalizedRadiusError A ρ h₀ a)
              (radiusTrackingExitTime A ρ h₀ a δ T) (T + 1) ω ^ 2
            ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) ≤
            ((T + 1 : ℕ) : ℝ) *
              (C *
                trackingAmplification
                  (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                  (fun u => roundedBeta A ρ a (roundedOrbit A ρ h₀ u))
                  (T + 1) ^ 2 / (N : ℝ)) := by
  obtain ⟨C, hC, hrec⟩ :=
    exists_pos_uniform_stoppedNormalizedRadiusError_moment_recursion
      hA hρ hρ_lt
  refine ⟨C, hC, ?_⟩
  intro h₀ a δ hh₀ ha hδ hδ_quarter N hN T
  let α : ℕ → ℝ :=
    fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u)
  let σ : ℕ → ℝ :=
    fun u => roundedBeta A ρ a (roundedOrbit A ρ h₀ u)
  let R : ℕ → (ℕ → ℝ) → ℝ :=
    normalizedRadiusError A ρ h₀ a
  let τ : (ℕ → ℝ) → ℕ :=
    radiusTrackingExitTime A ρ h₀ a δ T
  have hstep : ∀ t : ℕ, t < T + 1 →
      (∫ ω,
        backWeight α (T + 1) (t + 1) *
          stoppedValue R τ (t + 1) ω ^ 2
        ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) ≤
        (∫ ω,
          backWeight α (T + 1) t *
            stoppedValue R τ t ω ^ 2
          ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))) +
        backWeight α (T + 1) (t + 1) *
          (C * σ t ^ 2 / (N : ℝ)) := by
    intro t ht
    have h :=
      hrec hh₀ ha hδ hδ_quarter hN T t (Nat.le_of_lt_succ ht)
    simpa only [α, σ, R, τ, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using h
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hCN : 0 ≤ C / (N : ℝ) :=
    div_nonneg hC.le hNreal.le
  have hα : ∀ u : ℕ, u < T + 1 → 0 ≤ α u := by
    intro u hu
    exact roundedAlpha_nonneg hA hρ hρ_lt
      (roundedOrbit_nonneg hh₀ u) ha.le hδ
  have hσ : ∀ u : ℕ, u < T + 1 → 0 ≤ σ u := by
    intro u hu
    exact roundedBeta_nonneg (roundedOrbit_nonneg hh₀ u) ha.le
  have hamp : ∀ t : ℕ, t < T + 1 →
      backWeight α (T + 1) (t + 1) * σ t ^ 2 ≤
        trackingAmplification α σ (T + 1) ^ 2 :=
    fun t ht =>
      backWeight_mul_sigma_sq_le_trackingAmplification_sq
        hα ht (hσ t ht)
  have hbase := stopped_moment_backWeight_endpoints
    (R := R) (τ := τ) (α := α) (σ := σ)
    (T := T + 1) (C := C) (N := (N : ℝ))
    (K := trackingAmplification α σ (T + 1))
    hstep hCN hamp
  have hinit :
      ∫ ω, R 0 ω ^ 2
          ∂(markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [
      markovPathMeasure_dirac_ae_eval_zero_eq
        h₀ (Hkernel A ρ N)] with ω hω
    simp [R, normalizedRadiusError, radiusTrackingError, hω]
  rw [hinit, mul_zero, zero_add] at hbase
  simpa only [α, σ, R, τ] using hbase

/-- The capped normalized-radius tracking exit probability has the canonical
Chebyshev bound controlled by the deterministic tracking amplification. -/
lemma exists_pos_radiusTrackingExitProbability_le
    {A ρ h₀ a δ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (ha : 0 < a) (hδ : 0 < δ)
    {N : ℕ} (hN : 0 < N) (T : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)).real
          {ω | radiusTrackingExitTime A ρ h₀ a δ T ω ≤ T} ≤
        (((T + 1 : ℕ) : ℝ) *
          (C *
            trackingAmplification
              (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
              (fun u => roundedBeta A ρ a (roundedOrbit A ρ h₀ u))
              (T + 1) ^ 2 / (N : ℝ))) / δ ^ 2 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_pos_stoppedNormalizedRadiusError_secondMoment_le
      hA hρ hρ_lt hh₀ ha hδ.le hN T
  have hcheb :=
    exit_prob_le_stopped_moment_div_of_le
      (μ := markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))
      (R := normalizedRadiusError A ρ h₀ a)
      (τ := radiusTrackingExitTime A ρ h₀ a δ T)
      (T := T) (S := T + 1)
      (Nat.le_succ T) hδ
      (measurableSet_radiusTrackingExitTime_le A ρ h₀ a δ T)
      (fun ω hω =>
        delta_lt_abs_normalizedRadiusError_at_exit hh₀ ha hω)
      (integrable_sq_stoppedNormalizedRadiusError
        (δ := δ) hh₀ ha hρ hN T (T + 1))
  refine ⟨C, hC, hcheb.trans ?_⟩
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hδ)).2 hmoment

/-- One positive constant controls the capped normalized-radius tracking exit
probability uniformly in all radius-tracking parameters. -/
lemma exists_pos_uniform_radiusTrackingExitProbability_le
    {A ρ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {h₀ a δ : ℝ}, 0 ≤ h₀ → 0 < a → 0 < δ → δ ≤ 1 / 4 →
        ∀ {N : ℕ}, 0 < N → ∀ T : ℕ,
          (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)).real
              {ω | radiusTrackingExitTime A ρ h₀ a δ T ω ≤ T} ≤
            (((T + 1 : ℕ) : ℝ) *
              (C *
                trackingAmplification
                  (fun u => roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))
                  (fun u => roundedBeta A ρ a (roundedOrbit A ρ h₀ u))
                  (T + 1) ^ 2 / (N : ℝ))) / δ ^ 2 := by
  obtain ⟨C, hC, hmoment⟩ :=
    exists_pos_uniform_stoppedNormalizedRadiusError_secondMoment_le
      hA hρ hρ_lt
  refine ⟨C, hC, ?_⟩
  intro h₀ a δ hh₀ ha hδ hδ_quarter N hN T
  have hcheb :=
    exit_prob_le_stopped_moment_div_of_le
      (μ := markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N))
      (R := normalizedRadiusError A ρ h₀ a)
      (τ := radiusTrackingExitTime A ρ h₀ a δ T)
      (T := T) (S := T + 1)
      (Nat.le_succ T) hδ
      (measurableSet_radiusTrackingExitTime_le A ρ h₀ a δ T)
      (fun ω hω =>
        delta_lt_abs_normalizedRadiusError_at_exit hh₀ ha hω)
      (integrable_sq_stoppedNormalizedRadiusError
        (δ := δ) hh₀ ha hρ hN T (T + 1))
  refine hcheb.trans ?_
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hδ)).2
    (hmoment hh₀ ha hδ.le hδ_quarter hN T)

/-- **Fixed-precision radius concentration**
(`prop:subcritical-exact-radius-concentration`).  For bounded deterministic
initial vectors and every horizon satisfying the paper's subpolynomial rate
condition, the maximal normalized radius error converges to zero in
probability. -/
theorem subcritical_exact_radius_concentration
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1)
    (Tbar : ℕ → ℕ)
    (hTbar : ∀ C : ℝ,
      Tendsto
        (fun N : ℕ =>
          (Tbar N : ℝ) / (N : ℝ) *
            Real.exp (C * (Real.log (Real.log N)) ^ 2))
        atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto
        (fun N : ℕ =>
          (markovPathMeasure
              (Measure.dirac (roundedInitialRadius ρ N (x N)))
              (Hkernel A ρ N)).real
            {ω | ∃ t ≤ Tbar N,
              δ <
                |normalizedRadiusError A ρ
                  (roundedInitialRadius ρ N (x N))
                  (fixedPrecisionScale N) t ω|})
        atTop (𝓝 0) := by
  intro δ hδ
  let ε := min δ (1 / 4 : ℝ)
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hε_quarter : ε ≤ 1 / 4 := min_le_right _ _
  let C₀ := (ρ⁻¹ + 1 / 2) ^ 2
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    exact sq_pos_of_pos (add_pos (inv_pos.mpr hρ) (by norm_num))
  let r := min (1 / 4 : ℝ) C₀
  have hr : 0 < r := lt_min (by norm_num) hC₀
  have hr_half : r < 1 / 2 := by
    exact (min_le_left (1 / 4 : ℝ) C₀).trans_lt (by norm_num)
  have hrC₀ : r ≤ C₀ := min_le_right _ _
  obtain ⟨Cnoise, hCnoise, hexit⟩ :=
    exists_pos_uniform_radiusTrackingExitProbability_le
      hA hρ hρ_lt
  obtain ⟨Camp, hCamp, Namp, hamp⟩ :=
    exists_eventually_uniform_trackingAmplification_le_exp_sq
      hA hA_lt hρ hρ_lt hC₀ hr hr_half hrC₀
  have hrate :=
    tendsto_succ_nat_div_mul_exp_log_log_sq_zero
      Tbar hTbar (2 * Camp)
  have hupper :
      Tendsto
        (fun N : ℕ =>
          (Cnoise / ε ^ 2) *
            (((Tbar N + 1 : ℕ) : ℝ) / (N : ℝ) *
              Real.exp ((2 * Camp) *
                (Real.log (Real.log N)) ^ 2)))
        atTop (𝓝 0) := by
    simpa using hrate.const_mul (Cnoise / ε ^ 2)
  have hεprob :
      Tendsto
        (fun N : ℕ =>
          (markovPathMeasure
              (Measure.dirac (roundedInitialRadius ρ N (x N)))
              (Hkernel A ρ N)).real
            {ω | ∃ t ≤ Tbar N,
              ε <
                |normalizedRadiusError A ρ
                  (roundedInitialRadius ρ N (x N))
                  (fixedPrecisionScale N) t ω|})
        atTop (𝓝 0) := by
    refine squeeze_zero'
      (g := fun N : ℕ =>
        (Cnoise / ε ^ 2) *
          (((Tbar N + 1 : ℕ) : ℝ) / (N : ℝ) *
            Real.exp ((2 * Camp) *
              (Real.log (Real.log N)) ^ 2)))
      (Eventually.of_forall fun N => by positivity) ?_ hupper
    filter_upwards [eventually_ge_atTop (max Namp 2)] with N hNlarge
    · have hNamp : Namp ≤ N := le_trans (le_max_left Namp 2) hNlarge
      have hNtwo : 2 ≤ N := le_trans (le_max_right Namp 2) hNlarge
      have hN : 0 < N := by omega
      have hNone : 1 < N := by omega
      let h₀ := roundedInitialRadius ρ N (x N)
      have hh₀ : 0 ≤ h₀ := roundedInitialRadius_nonneg ρ N (x N)
      have hh₀C₀ : h₀ ≤ C₀ := by
        dsimp [h₀, C₀]
        exact roundedInitialRadius_le_sq hρ hN (hx N)
      have ha : 0 < fixedPrecisionScale N :=
        fixedPrecisionScale_pos hNone
      let α : ℕ → ℝ :=
        fun u => roundedAlpha A ρ ε (fixedPrecisionScale N)
          (roundedOrbit A ρ h₀ u)
      let σ : ℕ → ℝ :=
        fun u => roundedBeta A ρ (fixedPrecisionScale N)
          (roundedOrbit A ρ h₀ u)
      let K := trackingAmplification α σ (Tbar N + 1)
      have hK :
          K ≤ Real.exp
            (Camp * (Real.log (Real.log N)) ^ 2) := by
        simpa only [K, α, σ] using
          hamp N hNamp h₀ hh₀ hh₀C₀ ε hε.le hε_quarter
            (Tbar N + 1)
      have hKnonneg : 0 ≤ K :=
        le_trans zero_le_one (one_le_trackingAmplification α σ (Tbar N + 1))
      have hKsq :
          K ^ 2 ≤ Real.exp
            ((2 * Camp) * (Real.log (Real.log N)) ^ 2) := by
        calc
          K ^ 2 ≤
              Real.exp (Camp * (Real.log (Real.log N)) ^ 2) ^ 2 :=
            pow_le_pow_left₀ hKnonneg hK 2
          _ = Real.exp
              ((2 * Camp) * (Real.log (Real.log N)) ^ 2) := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
      have hexitBound :=
        hexit hh₀ ha hε hε_quarter hN (Tbar N)
      have hevent :
          {ω | ∃ t ≤ Tbar N,
              ε <
                |normalizedRadiusError A ρ h₀
                  (fixedPrecisionScale N) t ω|} =
            {ω | radiusTrackingExitTime A ρ h₀
              (fixedPrecisionScale N) ε (Tbar N) ω ≤ Tbar N} := by
        ext ω
        exact
          (radiusTrackingExitTime_le_iff_exists_abs_normalizedRadiusError_gt
            hh₀ ha).symm
      rw [show roundedInitialRadius ρ N (x N) = h₀ by rfl, hevent]
      calc
        (markovPathMeasure (Measure.dirac h₀) (Hkernel A ρ N)).real
            {ω | radiusTrackingExitTime A ρ h₀
              (fixedPrecisionScale N) ε (Tbar N) ω ≤ Tbar N} ≤
            (((Tbar N + 1 : ℕ) : ℝ) *
              (Cnoise * K ^ 2 / (N : ℝ))) / ε ^ 2 := by
          simpa only [K, α, σ] using hexitBound
        _ ≤ (((Tbar N + 1 : ℕ) : ℝ) *
              (Cnoise *
                Real.exp ((2 * Camp) *
                  (Real.log (Real.log N)) ^ 2) / (N : ℝ))) / ε ^ 2 := by
          gcongr
        _ = (Cnoise / ε ^ 2) *
              (((Tbar N + 1 : ℕ) : ℝ) / (N : ℝ) *
                Real.exp ((2 * Camp) *
                  (Real.log (Real.log N)) ^ 2)) := by ring
  refine squeeze_zero'
    (g := fun N : ℕ =>
      (markovPathMeasure
          (Measure.dirac (roundedInitialRadius ρ N (x N)))
          (Hkernel A ρ N)).real
        {ω | ∃ t ≤ Tbar N,
          ε <
            |normalizedRadiusError A ρ
              (roundedInitialRadius ρ N (x N))
              (fixedPrecisionScale N) t ω|})
    (Eventually.of_forall fun N => by positivity) ?_ hεprob
  exact Eventually.of_forall fun N =>
    measureReal_mono (by
      rintro ω ⟨t, htT, htδ⟩
      exact ⟨t, htT, hεδ.trans_lt htδ⟩)

end AbsorptionCutoff
