/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib
import AbsorptionCutoff.Rounding

/-!
# Unit-grid lattice comparison map

Begins the paper's `lem:subcritical-lattice-regimes` (§4, "Fixed-precision dimension
cutoff"). The linearized rounded dynamics are dominated by the unit-grid lattice
comparison map

`L_A(h) = 𝔼[Q₁(A√h · G)²]`,  `G ~ 𝒩(0,1)`,

whose profile is `m(α) = 𝔼[Q₁(α G)²]` (so `L_A(h) = m(A√h)`), and whose subcritical
threshold is `A_lat² = inf_{α>0} α²/m(α)`. When `A < A_lat` the map is a global
contraction `L_A(h) ≤ θ_A h` for some `θ_A ∈ (0,1)`.

## Main definitions
* `AbsorptionCutoff.latticeProfile` — `m(α) = 𝔼[Q₁(αG)²]`.
* `AbsorptionCutoff.latticeMap`     — `L_A(h) = m(A√h)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace AbsorptionCutoff

/-- The unit-grid lattice profile `m(α) = 𝔼[Q₁(αG)²]` for `G ~ 𝒩(0,1)`
(paper `eq:subcritical-lattice-threshold`). -/
noncomputable def latticeProfile (α : ℝ) : ℝ :=
  ∫ g, ((Q₁ (α * g) : ℝ)) ^ 2 ∂(gaussianReal 0 1)

/-- The unit-grid lattice comparison map `L_A(h) = m(A√h)`
(paper `eq:subcritical-lattice-map`): `L_A(h) = 𝔼[Q₁(A√h·G)²]`. -/
noncomputable def latticeMap (A h : ℝ) : ℝ := latticeProfile (A * Real.sqrt h)

@[simp] lemma latticeMap_eq (A h : ℝ) :
    latticeMap A h = latticeProfile (A * Real.sqrt h) := rfl

/-- The rounded squared-radius mean map
`V_{A,ρ}(h) = 𝔼[Q₁(ρ⁻¹ tanh(ρA√h G))²]` (paper `eq:rounded-radius-map`). -/
noncomputable def roundedMeanMap (A ρ h : ℝ) : ℝ :=
  ∫ g, ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) : ℝ)) ^ 2
    ∂(gaussianReal 0 1)

/-- The origin is fixed by the rounded squared-radius mean map. -/
@[simp] lemma roundedMeanMap_zero (A ρ : ℝ) : roundedMeanMap A ρ 0 = 0 := by
  have hQ : Q₁ (0 : ℝ) = 0 := (Q₁_zero_iff 0).mpr (by norm_num)
  simp [roundedMeanMap, hQ]

/-- The lattice profile is nonnegative (an integral of a square). -/
lemma latticeProfile_nonneg (α : ℝ) : 0 ≤ latticeProfile α :=
  integral_nonneg fun g => by positivity

/-- `|Q₁ u|` is within `1/2` of `|u|`; in particular `|(Q₁ u : ℝ)| ≤ |u| + 1/2`
(paper's rounding bound `|Q₁(u)| ≤ |u| + 1/2` on `{|u|>1/2}`, here stated for all `u`). -/
lemma abs_Q₁_le (u : ℝ) : |(Q₁ u : ℝ)| ≤ |u| + 2⁻¹ := by
  have h := Q₁_sub_le u
  have h2 := abs_sub_abs_le_abs_sub (Q₁ u : ℝ) u
  linarith

/-- `|Q₁ u| ≤ 2|u|` for every `u`: on the zero bin `{|u|≤1/2}` the left side vanishes, and
off it `|Q₁ u| ≤ |u| + 1/2 ≤ 2|u|` (paper's `|Q₁(u)| ≤ 2|u|` on `{|u|>1/2}`). -/
lemma abs_Q₁_le_two_abs (u : ℝ) : |(Q₁ u : ℝ)| ≤ 2 * |u| := by
  by_cases h : |u| ≤ 2⁻¹
  · rw [(Q₁_zero_iff u).mpr h, Int.cast_zero, abs_zero]; positivity
  · have h1 := abs_Q₁_le u
    have h' : 2⁻¹ < |u| := lt_of_not_ge h
    linarith

/-- Unit-grid rounding is monotone.  This will make its discontinuity set countable,
which is the a.e. input in the continuity proof for `latticeProfile`. -/
lemma monotone_Q₁ : Monotone Q₁ := by
  intro u v huv
  unfold Q₁
  by_cases hu : 0 ≤ u
  · have hv : 0 ≤ v := hu.trans huv
    rw [if_pos hu, if_pos hv]
    exact Int.ceil_mono (sub_le_sub_right huv _)
  · by_cases hv : 0 ≤ v
    · rw [if_neg hu, if_pos hv]
      have hlu : 0 ≤ ⌈-u - 2⁻¹⌉ :=
        Int.ceil_nonneg_of_neg_one_lt (by have := lt_of_not_ge hu; linarith)
      have hrv : 0 ≤ ⌈v - 2⁻¹⌉ :=
        Int.ceil_nonneg_of_neg_one_lt (by linarith)
      omega
    · rw [if_neg hu, if_neg hv]
      exact neg_le_neg (Int.ceil_mono (sub_le_sub_right (neg_le_neg huv) _))

/-- The magnitude of unit-grid rounding depends only on the magnitude of its input. -/
lemma abs_Q₁_eq_ceil_abs_sub (u : ℝ) :
    |(Q₁ u : ℝ)| = (⌈|u| - 2⁻¹⌉ : ℤ) := by
  have hceil : 0 ≤ ⌈|u| - 2⁻¹⌉ := by
    exact Int.ceil_nonneg_of_neg_one_lt (by nlinarith [abs_nonneg u])
  unfold Q₁
  by_cases hu : 0 ≤ u
  · rw [if_pos hu, abs_of_nonneg hu, abs_of_nonneg]
    · simpa [abs_of_nonneg hu] using hceil
  · have hu' : u < 0 := not_le.mp hu
    rw [if_neg hu, abs_of_neg hu', Int.cast_neg, abs_neg, abs_of_nonneg]
    · simpa [abs_of_neg hu'] using hceil

/-- Unit-grid rounding is monotone in magnitude. -/
lemma abs_Q₁_mono {u v : ℝ} (huv : |u| ≤ |v|) :
    |(Q₁ u : ℝ)| ≤ |(Q₁ v : ℝ)| := by
  rw [abs_Q₁_eq_ceil_abs_sub, abs_Q₁_eq_ceil_abs_sub]
  exact_mod_cast Int.ceil_mono (sub_le_sub_right huv _)

private lemma lattice_continuous_tanh : Continuous Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x from
    funext Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

private lemma lattice_hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh
  have hfun : (fun y => Real.sinh y / Real.cosh y) = Real.tanh :=
    (funext Real.tanh_eq_sinh_div_cosh).symm
  rw [hfun] at h
  have hval : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) /
      Real.cosh x ^ 2 = 1 - Real.tanh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rwa [hval] at h

/-- Lightweight strict monotonicity of `tanh`, kept in the lattice import path. -/
lemma strictMono_tanh_light : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(lattice_hasDerivAt_tanh x).deriv]
  linarith [Real.tanh_sq_lt_one x]

private lemma lattice_tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp
  · have hmono : StrictMonoOn (fun t => t - Real.tanh t) (Set.Ici (0 : ℝ)) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact (continuous_id.sub lattice_continuous_tanh).continuousOn
      · intro t ht
        rw [interior_Ici] at ht
        have htpos : 0 < Real.tanh t := by
          rw [Real.tanh_eq_sinh_div_cosh]
          exact div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos t)
        have hd : HasDerivAt (fun t => t - Real.tanh t)
            (1 - (1 - Real.tanh t ^ 2)) t :=
          (hasDerivAt_id t).sub (lattice_hasDerivAt_tanh t)
        rw [hd.deriv]
        nlinarith [mul_pos htpos htpos]
    have h0 := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hx.le) hx
    simp only [Real.tanh_zero, sub_zero] at h0
    linarith

/-- The hyperbolic tangent has no larger magnitude than its argument. -/
lemma abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  by_cases hx : 0 ≤ x
  · have h0 : 0 ≤ Real.tanh x := by
      have := strictMono_tanh_light.monotone hx
      simpa using this
    rw [abs_of_nonneg hx, abs_of_nonneg h0]
    exact lattice_tanh_le_self hx
  · have hx' : x < 0 := not_le.mp hx
    have h0 : Real.tanh x ≤ 0 := by
      have := strictMono_tanh_light.monotone hx'.le
      simpa using this
    rw [abs_of_neg hx', abs_of_nonpos h0]
    have htan := lattice_tanh_le_self (show 0 ≤ -x by linarith)
    rw [Real.tanh_neg] at htan
    linarith

/-- Standard-Gaussian second moment (local copy, to keep `Lattice` off the heavier
`MeanMap` import). -/
private lemma integrable_sq_gaussian' :
    Integrable (fun g : ℝ => g ^ 2) (gaussianReal 0 1) := by
  simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq

/-- Standard-Gaussian second moment (local copy, to keep `Lattice` off the heavier
`MeanMap` import). -/
private lemma integral_sq_gaussian' :
    ∫ g : ℝ, g ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hv := variance_id_gaussianReal (μ := 0) (v := 1)
  have hi : ∫ g : ℝ, g ∂(gaussianReal 0 1) = 0 :=
    integral_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at hv
  simp only [id_eq, hi, sub_zero] at hv
  simpa using hv

/-- The degree-seven Taylor lower bound for the standard-Gaussian exponential on `[1,2]`. -/
private lemma gaussianTailTaylorLower {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    (∑ m ∈ Finset.range 8, (-x ^ 2 / 2) ^ m / m.factorial) -
        (x ^ 2 / 2) ^ 8 / Nat.factorial 8 * 2 ≤ Real.exp (-x ^ 2 / 2) := by
  have hneg : -x ^ 2 / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num)
  have harg : ‖((-x ^ 2 / 2 : ℝ) : ℂ)‖ / ((Nat.succ 8 : ℕ) : ℝ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hneg]
    norm_num
    nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
  have h := Complex.exp_bound' (x := ((-x ^ 2 / 2 : ℝ) : ℂ)) (n := 8) harg
  norm_cast at h
  have hlower := (abs_le.mp h).1
  norm_num at hlower ⊢
  linarith

/-- The explicit Taylor lower polynomial has integral greater than `1/3` on `[1,2]`. -/
private lemma gaussianTailTaylorLower_integral :
    (1 / 3 : ℝ) <
      ∫ x in (1 : ℝ)..2,
        ((∑ m ∈ Finset.range 8, (-x ^ 2 / 2) ^ m / m.factorial) -
          (x ^ 2 / 2) ^ 8 / Nat.factorial 8 * 2) := by
  norm_num [Finset.sum_range_succ]
  ring_nf
  let F : ℝ → ℝ := fun x =>
    x - x ^ 3 / 6 + x ^ 5 / 40 - x ^ 7 / 336 + x ^ 9 / 3456 -
      x ^ 11 / 42240 + x ^ 13 / 599040 - x ^ 15 / 9676800 -
      x ^ 17 / 87736320
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (fun x _ => by
      dsimp [F]
      convert (hasDerivAt_id x
        |>.sub (((hasDerivAt_id x).pow 3).div_const 6)
        |>.add (((hasDerivAt_id x).pow 5).div_const 40)
        |>.sub (((hasDerivAt_id x).pow 7).div_const 336)
        |>.add (((hasDerivAt_id x).pow 9).div_const 3456)
        |>.sub (((hasDerivAt_id x).pow 11).div_const 42240)
        |>.add (((hasDerivAt_id x).pow 13).div_const 599040)
        |>.sub (((hasDerivAt_id x).pow 15).div_const 9676800)
        |>.sub (((hasDerivAt_id x).pow 17).div_const 87736320)) using 1
      · funext y
        dsimp
      · simp
        ring)
    (by
      apply Continuous.intervalIntegrable
      fun_prop)]
  dsimp [F]
  norm_num

private lemma integral_exp_neg_sq_div_two_gt :
    (1 / 3 : ℝ) < ∫ x in (1 : ℝ)..2, Real.exp (-x ^ 2 / 2) := by
  apply lt_of_lt_of_le gaussianTailTaylorLower_integral
  apply intervalIntegral.integral_mono_on (by norm_num)
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop
  · intro x hx
    exact gaussianTailTaylorLower hx.1 hx.2

private lemma sqrt_two_pi_lt_eight_thirds : Real.sqrt (2 * Real.pi) < 8 / 3 := by
  have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hpi := Real.pi_lt_d2
  have hsqrt0 := Real.sqrt_nonneg (2 * Real.pi)
  nlinarith

private lemma integral_gaussianPDFReal_one_two_gt :
    (1 / 8 : ℝ) <
      ∫ x in (1 : ℝ)..2, gaussianPDFReal 0 1 x := by
  have hinv : (3 / 8 : ℝ) < (Real.sqrt (2 * Real.pi))⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) (by positivity)]
    norm_num
    simpa only [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] using
      sqrt_two_pi_lt_eight_thirds
  have heq : (∫ x in (1 : ℝ)..2, gaussianPDFReal 0 1 x) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x in (1 : ℝ)..2, Real.exp (-x ^ 2 / 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
      intervalIntegral.integral_const_mul]
  rw [heq]
  have hexp0 : 0 ≤ ∫ x in (1 : ℝ)..2, Real.exp (-x ^ 2 / 2) := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun x _ => (Real.exp_pos _).le
  nlinarith [integral_exp_neg_sq_div_two_gt]

private lemma gaussianReal_Ioc_one_two_gt :
    (1 / 8 : ℝ) < (gaussianReal 0 1).real (Set.Ioc 1 2) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc
    fun x _ => gaussianPDFReal_nonneg 0 1 x)]
  rw [← intervalIntegral.integral_of_le (by norm_num)]
  exact integral_gaussianPDFReal_one_two_gt

private lemma gaussianReal_Ico_neg_two_neg_one_gt :
    (1 / 8 : ℝ) < (gaussianReal 0 1).real (Set.Ico (-2) (-1)) := by
  have hmap := congrArg (fun μ : Measure ℝ => μ (Set.Ioc 1 2))
    (gaussianReal_map_neg (μ := 0) (v := 1))
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioc] at hmap
  have hpre : (fun x : ℝ => -x) ⁻¹' Set.Ioc 1 2 = Set.Ico (-2) (-1) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith
  simp only [neg_zero] at hmap
  rw [hpre] at hmap
  rw [measureReal_def, hmap]
  exact gaussianReal_Ioc_one_two_gt

/-- The elementary standard-Gaussian tail estimate used in the paper:
`ℙ(|G| > 1) > 1/4`.  It suffices to integrate the density on `(1,2]` and its reflection. -/
lemma gaussianReal_abs_gt_one_gt_one_fourth :
    (1 / 4 : ℝ) < (gaussianReal 0 1).real {g : ℝ | 1 < |g|} := by
  let P : Set ℝ := Set.Ioc 1 2
  let N : Set ℝ := Set.Ico (-2) (-1)
  have hdisj : Disjoint P N := by
    rw [Set.disjoint_left]
    intro x hxP hxN
    dsimp [P, N] at hxP hxN
    linarith [hxP.1, hxN.2]
  have hsub : P ∪ N ⊆ {g : ℝ | 1 < |g|} := by
    intro x hx
    rcases hx with hx | hx
    · dsimp [P] at hx
      simp only [Set.mem_setOf_eq, abs_of_pos (lt_trans zero_lt_one hx.1)]
      exact hx.1
    · dsimp [N] at hx
      simp only [Set.mem_setOf_eq, abs_of_neg (lt_trans hx.2 (by norm_num))]
      linarith [hx.2]
  have hmono := measure_mono (μ := gaussianReal 0 1) hsub
  have hfiniteP : (gaussianReal 0 1) P ≠ ⊤ := measure_ne_top _ _
  have hfiniteN : (gaussianReal 0 1) N ≠ ⊤ := measure_ne_top _ _
  have hunion :
      (gaussianReal 0 1).real (P ∪ N) =
        (gaussianReal 0 1).real P + (gaussianReal 0 1).real N := by
    rw [measureReal_def, measure_union hdisj measurableSet_Ico,
      ENNReal.toReal_add hfiniteP hfiniteN, measureReal_def, measureReal_def]
  have hmonoReal :
      (gaussianReal 0 1).real (P ∪ N) ≤
        (gaussianReal 0 1).real {g : ℝ | 1 < |g|} := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmono
  dsimp [P, N] at hunion ⊢
  rw [hunion] at hmonoReal
  nlinarith [gaussianReal_Ioc_one_two_gt, gaussianReal_Ico_neg_two_neg_one_gt]

/-- The squared rounded coordinate `Q₁(αG)²` is `𝒩(0,1)`-integrable, dominated by
`2(αG)² + 1/2`. -/
lemma integrable_sq_Q₁_gaussian (α : ℝ) :
    Integrable (fun g => ((Q₁ (α * g) : ℝ)) ^ 2) (gaussianReal 0 1) := by
  have hQmeas : Measurable (fun g => (Q₁ (α * g) : ℝ)) :=
    (measurable_of_countable _).comp (measurable_Q₁.comp (measurable_id.const_mul α))
  refine Integrable.mono' (g := fun g => 2 * (α * g) ^ 2 + 2⁻¹) ?_
    (hQmeas.pow_const 2).aestronglyMeasurable ?_
  · have h1 : Integrable (fun g : ℝ => 2 * (α * g) ^ 2) (gaussianReal 0 1) := by
      have hfun : (fun g : ℝ => 2 * (α * g) ^ 2) = (fun g : ℝ => 2 * α ^ 2 * g ^ 2) := by
        funext g; ring
      rw [hfun]
      exact integrable_sq_gaussian'.const_mul _
    exact h1.add (integrable_const _)
  · filter_upwards with g
    have hb := abs_Q₁_le (α * g)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : |(Q₁ (α * g) : ℝ)| ^ 2 ≤ (|α * g| + 2⁻¹) ^ 2 := by
      apply sq_le_sq'
      · linarith [abs_nonneg (α * g), abs_nonneg (Q₁ (α * g) : ℝ)]
      · exact hb
    nlinarith [h1, sq_nonneg (|α * g| - 2⁻¹), sq_abs (α * g), sq_abs (Q₁ (α * g) : ℝ)]

/-- The exact rounded mean map is dominated by its unit-grid lattice linearization. -/
lemma roundedMeanMap_le_latticeMap {A ρ h : ℝ} (hρ : 0 < ρ) :
    roundedMeanMap A ρ h ≤ latticeMap A h := by
  let f : ℝ → ℝ := fun g =>
    ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) : ℝ)) ^ 2
  let F : ℝ → ℝ := fun g => ((Q₁ (A * Real.sqrt h * g) : ℝ)) ^ 2
  have hle : ∀ g, f g ≤ F g := by
    intro g
    have htanh := abs_tanh_le_abs (ρ * (A * Real.sqrt h * g))
    have harg :
        |ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)| ≤
          |A * Real.sqrt h * g| := by
      rw [abs_mul, abs_inv, abs_of_pos hρ]
      rw [show ρ * A * Real.sqrt h * g = ρ * (A * Real.sqrt h * g) by ring]
      rw [abs_mul, abs_of_pos hρ] at htanh
      calc
        ρ⁻¹ * |Real.tanh (ρ * (A * Real.sqrt h * g))|
            ≤ ρ⁻¹ * (ρ * |A * Real.sqrt h * g|) :=
              mul_le_mul_of_nonneg_left htanh (by positivity)
        _ = |A * Real.sqrt h * g| := by field_simp
    have hQ := abs_Q₁_mono harg
    dsimp [f, F]
    simpa only [sq_abs] using
      (pow_le_pow_left₀
        (abs_nonneg (Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g)) : ℝ)) hQ 2)
  have hFint : Integrable F (gaussianReal 0 1) := by
    simpa [F, mul_assoc] using integrable_sq_Q₁_gaussian (A * Real.sqrt h)
  have hfmeas : AEStronglyMeasurable f (gaussianReal 0 1) := by
    apply Measurable.aestronglyMeasurable
    exact ((measurable_of_countable _).comp
      (measurable_Q₁.comp
        (measurable_const.mul (lattice_continuous_tanh.measurable.comp (by fun_prop))))).pow_const 2
  have hfint : Integrable f (gaussianReal 0 1) :=
    Integrable.mono' hFint hfmeas (Eventually.of_forall fun g => by
      dsimp [f, F]
      rw [abs_of_nonneg (by positivity)]
      exact hle g)
  rw [roundedMeanMap, latticeMap, latticeProfile]
  exact integral_mono hfint hFint hle

/-- The lattice profile is strictly positive for `α ≠ 0`: the rounded coordinate is nonzero,
hence `Q₁(αG)² ≥ 1`, on `{|αG|>1/2}`, a set of positive Gaussian measure. -/
lemma latticeProfile_pos {α : ℝ} (hα : α ≠ 0) : 0 < latticeProfile α := by
  set S : Set ℝ := {g : ℝ | 2⁻¹ < |α * g|} with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const (measurable_id.const_mul α).abs
  have hgS : 0 < (gaussianReal 0 1) S := by
    rw [pos_iff_ne_zero]
    intro h0
    have hvol0 : volume S = 0 := gaussianReal_absolutelyContinuous' 0 (by norm_num) h0
    have hαpos : 0 < |α| := abs_pos.mpr hα
    have hsub : Set.Ioi (1 / (2 * |α|)) ⊆ S := by
      intro g hg
      simp only [Set.mem_Ioi] at hg
      have hg0 : 0 < g := lt_of_le_of_lt (by positivity) hg
      simp only [hS, Set.mem_setOf_eq, abs_mul, abs_of_pos hg0]
      rw [div_lt_iff₀ (by positivity)] at hg
      nlinarith [hg, hαpos, hg0]
    have hmono := measure_mono (μ := volume) hsub
    rw [Real.volume_Ioi, hvol0] at hmono
    simp at hmono
  have hind_int : Integrable (S.indicator (fun _ => (1 : ℝ))) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  have hle : (S.indicator (fun _ => (1 : ℝ))) ≤ fun g => ((Q₁ (α * g) : ℝ)) ^ 2 := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      have hne : Q₁ (α * g) ≠ 0 := by
        rw [Ne, Q₁_zero_iff]
        simp only [hS, Set.mem_setOf_eq] at hg
        linarith
      have h1 : (1 : ℝ) ≤ |(Q₁ (α * g) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hne
      nlinarith [h1, sq_abs (Q₁ (α * g) : ℝ)]
    · rw [Set.indicator_of_notMem hg]; positivity
  calc (0 : ℝ) < (gaussianReal 0 1).real S :=
        ENNReal.toReal_pos hgS.ne' (measure_ne_top _ _)
    _ = ∫ g, S.indicator (fun _ => (1 : ℝ)) g ∂(gaussianReal 0 1) := by
        rw [integral_indicator_const _ hSmeas, smul_eq_mul, mul_one]
    _ ≤ latticeProfile α :=
        integral_mono hind_int (integrable_sq_Q₁_gaussian α) hle

/-- At scale `1/2`, the lattice profile is strictly larger than `1/4`, since
`Q₁(G/2)² ≥ 1` on `{|G| > 1}` and that event has probability greater than `1/4`. -/
lemma one_fourth_lt_latticeProfile_half :
    (1 / 4 : ℝ) < latticeProfile (1 / 2) := by
  let S : Set ℝ := {g : ℝ | 1 < |g|}
  have hSmeas : MeasurableSet S :=
    measurableSet_lt measurable_const measurable_id.abs
  have hind_int : Integrable (S.indicator (fun _ => (1 : ℝ))) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  have hle : S.indicator (fun _ => (1 : ℝ)) ≤
      fun g => ((Q₁ ((1 / 2 : ℝ) * g) : ℝ)) ^ 2 := by
    intro g
    by_cases hg : g ∈ S
    · rw [Set.indicator_of_mem hg]
      have hne : Q₁ ((1 / 2 : ℝ) * g) ≠ 0 := by
        rw [Ne, Q₁_zero_iff]
        dsimp [S] at hg
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        norm_num
        linarith
      have h1 : (1 : ℝ) ≤ |(Q₁ ((1 / 2 : ℝ) * g) : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs hne
      nlinarith [h1, sq_abs (Q₁ ((1 / 2 : ℝ) * g) : ℝ)]
    · rw [Set.indicator_of_notMem hg]
      positivity
  calc
    (1 / 4 : ℝ) < (gaussianReal 0 1).real S := by
      exact gaussianReal_abs_gt_one_gt_one_fourth
    _ = ∫ g, S.indicator (fun _ => (1 : ℝ)) g ∂(gaussianReal 0 1) := by
      rw [integral_indicator_const _ hSmeas, smul_eq_mul, mul_one]
    _ ≤ latticeProfile (1 / 2) := by
      rw [latticeProfile]
      exact integral_mono hind_int (integrable_sq_Q₁_gaussian _) hle

/-- Near-zero endpoint (`eq:subcritical-lattice-small-alpha`): `m(α)/α² → 0` as `α ↓ 0`.
Dominated convergence of `g ↦ (Q₁(αg)/α)²`: bounded by `4g²` (from `|Q₁ u| ≤ 2|u|`) and
tending to `0` a.e. (for `g ≠ 0`, `Q₁(αg) = 0` once `|αg| ≤ 1/2`, i.e. eventually as `α↓0`). -/
lemma latticeProfile_ratio_tendsto_zero :
    Tendsto (fun α => latticeProfile α / α ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hbound_int : Integrable (fun g : ℝ => 4 * g ^ 2) (gaussianReal 0 1) :=
    integrable_sq_gaussian'.const_mul 4
  have hne : ∀ᵐ g ∂(gaussianReal 0 1), g ≠ 0 := by
    haveI : NullSingletonClass (gaussianReal 0 1) :=
      nullSingletonClass_gaussianReal (by norm_num)
    have h0 : (gaussianReal 0 1) {(0 : ℝ)} = 0 := measure_singleton 0
    rw [ae_iff]
    convert h0 using 2
    ext a; simp
  have hconv : Tendsto
      (fun α => ∫ g, ((Q₁ (α * g) : ℝ)) ^ 2 / α ^ 2 ∂(gaussianReal 0 1))
      (𝓝[>] 0) (𝓝 (∫ _g, (0 : ℝ) ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun g => 4 * g ^ 2)
      ?_ ?_ hbound_int ?_
    · filter_upwards [self_mem_nhdsWithin] with α _
      have hQmeas : Measurable (fun g => (Q₁ (α * g) : ℝ)) :=
        (measurable_of_countable _).comp (measurable_Q₁.comp (measurable_id.const_mul α))
      exact ((hQmeas.pow_const 2).div_const (α ^ 2)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with α (hα : 0 < α)
      filter_upwards with g
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity),
        ← sq_abs ((Q₁ (α * g) : ℝ))]
      calc |(Q₁ (α * g) : ℝ)| ^ 2 ≤ (2 * |α * g|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (abs_Q₁_le_two_abs _) 2
        _ = 4 * g ^ 2 * α ^ 2 := by rw [mul_pow, sq_abs]; ring
    · filter_upwards [hne] with g hg
      have hev : ∀ᶠ α in 𝓝[>] (0 : ℝ), |α * g| ≤ 2⁻¹ := by
        have htend : Tendsto (fun α : ℝ => |α * g|) (𝓝[>] 0) (𝓝 0) := by
          have h0 : Tendsto (fun α : ℝ => α * g) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
            simpa using ((continuous_mul_const g).tendsto 0).mono_left nhdsWithin_le_nhds
          simpa using h0.abs
        exact htend.eventually_le_const (by norm_num)
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hev] with α hα2
      rw [(Q₁_zero_iff (α * g)).mpr hα2, Int.cast_zero]
      simp
  simp only [integral_zero] at hconv
  refine hconv.congr' ?_
  filter_upwards with α
  rw [latticeProfile, integral_div]

/-- Large-scale endpoint (`eq:subcritical-lattice-large-alpha`):
`m(α)/α² → 1` as `α → ∞`.  After division by `α`, the rounding error is at most
`1/(2α)`, while for `α ≥ 1` the squared integrand is dominated by `(|g|+1)²`. -/
lemma latticeProfile_ratio_tendsto_one :
    Tendsto (fun α => latticeProfile α / α ^ 2) atTop (𝓝 1) := by
  have habs_int : Integrable (fun g : ℝ => |g|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  have hbound_int : Integrable (fun g : ℝ => (|g| + 1) ^ 2) (gaussianReal 0 1) := by
    have heq : (fun g : ℝ => (|g| + 1) ^ 2) =
        fun g => g ^ 2 + 2 * |g| + 1 := by
      funext g
      rw [← sq_abs g]
      ring
    rw [heq]
    exact (integrable_sq_gaussian'.add (habs_int.const_mul 2)).add (integrable_const 1)
  have hconv : Tendsto
      (fun α => ∫ g, ((Q₁ (α * g) : ℝ)) ^ 2 / α ^ 2 ∂(gaussianReal 0 1))
      atTop (𝓝 (∫ g, g ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun g => (|g| + 1) ^ 2)
      ?_ ?_ hbound_int ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with α hα
      have hQmeas : Measurable (fun g => (Q₁ (α * g) : ℝ)) :=
        (measurable_of_countable _).comp (measurable_Q₁.comp (measurable_id.const_mul α))
      exact ((hQmeas.pow_const 2).div_const (α ^ 2)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with α hα
      have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one hα
      filter_upwards with g
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hquot : |(Q₁ (α * g) : ℝ) / α| ≤ |g| + 1 := by
        rw [abs_div, abs_of_pos hαpos, div_le_iff₀ hαpos]
        have hQ := abs_Q₁_le (α * g)
        rw [abs_mul, abs_of_pos hαpos] at hQ
        nlinarith
      have hsq := pow_le_pow_left₀ (abs_nonneg ((Q₁ (α * g) : ℝ) / α)) hquot 2
      rw [sq_abs, div_pow] at hsq
      exact hsq
    · filter_upwards with g
      have herr : Tendsto
          (fun α : ℝ => (Q₁ (α * g) : ℝ) / α - g) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_abs_tendsto_zero]
        have hhalf : Tendsto (fun α : ℝ => (2⁻¹ : ℝ) / α) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        refine squeeze_zero' (Eventually.of_forall fun α => abs_nonneg _) ?_
          hhalf
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with α hα
        simp only [Function.comp_apply]
        have heq : (Q₁ (α * g) : ℝ) / α - g =
            ((Q₁ (α * g) : ℝ) - α * g) / α := by
          field_simp
        rw [heq, abs_div, abs_of_pos hα]
        have hQ := Q₁_sub_le (α * g)
        exact div_le_div_of_nonneg_right hQ (le_of_lt hα)
      have hquot : Tendsto (fun α : ℝ => (Q₁ (α * g) : ℝ) / α) atTop (𝓝 g) := by
        simpa only [sub_add_cancel, zero_add] using herr.add_const g
      simpa [div_pow] using hquot.pow 2
  rw [integral_sq_gaussian'] at hconv
  refine hconv.congr' ?_
  filter_upwards with α
  rw [latticeProfile, integral_div]

/-- The lattice profile is continuous on the positive half-line.  Following the paper,
this is dominated convergence on a bounded `α`-neighborhood.  The rounded integrand
converges pointwise away from the countable discontinuity set of the monotone map `Q₁`;
that exceptional set has zero Gaussian measure. -/
lemma continuousOn_latticeProfile : ContinuousOn latticeProfile (Set.Ioi 0) := by
  intro α hα
  have hα0 : α ≠ 0 := ne_of_gt hα
  let q : ℝ → ℝ := fun u => (Q₁ u : ℝ)
  have hqmono : Monotone q := by
    intro u v huv
    dsimp [q]
    exact_mod_cast (monotone_Q₁ huv)
  let D : Set ℝ := {u | ¬ContinuousAt q u}
  have hDcount : D.Countable := hqmono.countable_not_continuousAt
  have hinj : Function.Injective (fun g : ℝ => α * g) := by
    intro g₁ g₂ heq
    exact mul_left_cancel₀ hα0 heq
  have hprecount : ((fun g : ℝ => α * g) ⁻¹' D).Countable :=
    hDcount.preimage hinj
  haveI : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hae : ∀ᵐ g ∂(gaussianReal 0 1), ContinuousAt q (α * g) := by
    filter_upwards [hprecount.ae_notMem (gaussianReal 0 1)] with g hg
    simpa only [Set.mem_preimage, D, Set.mem_setOf_eq, not_not] using hg
  let R : ℝ := |α| + 1
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have habs_int : Integrable (fun g : ℝ => |g|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  have hbound_int : Integrable (fun g : ℝ => (R * |g| + 2⁻¹) ^ 2)
      (gaussianReal 0 1) := by
    have heq : (fun g : ℝ => (R * |g| + 2⁻¹) ^ 2) =
        fun g => R ^ 2 * g ^ 2 + R * |g| + 4⁻¹ := by
      funext g
      rw [← sq_abs g]
      ring
    rw [heq]
    exact ((integrable_sq_gaussian'.const_mul _).add (habs_int.const_mul R)).add
      (integrable_const _)
  have hαbound : ∀ᶠ β in 𝓝 α, |β| ≤ R := by
    have ht : Tendsto (fun β : ℝ => |β|) (𝓝 α) (𝓝 |α|) :=
      continuous_id.abs.continuousAt
    exact ht.eventually_le_const (by dsimp [R]; linarith)
  have hconv : Tendsto
      (fun β => ∫ g, ((Q₁ (β * g) : ℝ)) ^ 2 ∂(gaussianReal 0 1))
      (𝓝 α) (𝓝 (∫ g, ((Q₁ (α * g) : ℝ)) ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun g => (R * |g| + 2⁻¹) ^ 2) ?_ ?_ hbound_int ?_
    · filter_upwards with β
      have hQmeas : Measurable (fun g => (Q₁ (β * g) : ℝ)) :=
        (measurable_of_countable _).comp (measurable_Q₁.comp (measurable_id.const_mul β))
      exact (hQmeas.pow_const 2).aestronglyMeasurable
    · filter_upwards [hαbound] with β hβ
      filter_upwards with g
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hQ := abs_Q₁_le (β * g)
      have hmul : |β * g| ≤ R * |g| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hβ (abs_nonneg g)
      have hsum : |β * g| + 2⁻¹ ≤ R * |g| + 2⁻¹ :=
        add_le_add_left hmul _
      have hs := pow_le_pow_left₀ (abs_nonneg (Q₁ (β * g) : ℝ))
        (hQ.trans hsum) 2
      simpa [sq_abs] using hs
    · filter_upwards [hae] with g hg
      have harg : Tendsto (fun β : ℝ => β * g) (𝓝 α) (𝓝 (α * g)) :=
        (continuous_mul_const g).continuousAt
      exact (Filter.Tendsto.comp hg harg).pow 2
  have hc : ContinuousAt latticeProfile α := by
    change Tendsto (fun β => latticeProfile β) (𝓝 α) (𝓝 (latticeProfile α))
    simpa only [latticeProfile] using hconv
  exact hc.continuousWithinAt

/-- The normalized lattice profile `m(α)/α²` is continuous for positive `α`. -/
lemma continuousOn_latticeProfile_ratio :
    ContinuousOn (fun α => latticeProfile α / α ^ 2) (Set.Ioi 0) :=
  continuousOn_latticeProfile.div (continuousOn_id.pow 2)
    (fun _ hα => pow_ne_zero 2 (ne_of_gt hα))

/-- The squared lattice threshold
`A_lat² = inf_{α>0} α² / m(α)` (paper `eq:subcritical-lattice-threshold`). -/
noncomputable def latticeThresholdSq : ℝ :=
  ⨅ α : {α : ℝ // 0 < α}, (α : ℝ) ^ 2 / latticeProfile α

/-- The lattice threshold `A_lat`, chosen as the nonnegative square root of
`inf_{α>0} α² / m(α)`. -/
noncomputable def latticeThreshold : ℝ :=
  Real.sqrt latticeThresholdSq

/-- Every ratio entering the definition of `latticeThresholdSq` is nonnegative. -/
lemma latticeProfile_sq_div_nonneg (α : {α : ℝ // 0 < α}) :
    0 ≤ (α : ℝ) ^ 2 / latticeProfile α :=
  div_nonneg (sq_nonneg _) (latticeProfile_nonneg _)

/-- The zero-bin estimate `|Q₁(u)| ≤ 2|u|` gives the global bound
`m(α) ≤ 4α²`. -/
lemma latticeProfile_le_four_mul_sq (α : ℝ) :
    latticeProfile α ≤ 4 * α ^ 2 := by
  have hright : Integrable (fun g : ℝ => 4 * α ^ 2 * g ^ 2) (gaussianReal 0 1) :=
    integrable_sq_gaussian'.const_mul _
  calc
    latticeProfile α
        ≤ ∫ g : ℝ, 4 * α ^ 2 * g ^ 2 ∂(gaussianReal 0 1) := by
          rw [latticeProfile]
          refine integral_mono (integrable_sq_Q₁_gaussian α) hright ?_
          intro g
          have hsq := pow_le_pow_left₀ (abs_nonneg (Q₁ (α * g) : ℝ))
            (abs_Q₁_le_two_abs (α * g)) 2
          rw [sq_abs, mul_pow, sq_abs] at hsq
          nlinarith
    _ = 4 * α ^ 2 := by rw [integral_const_mul, integral_sq_gaussian', mul_one]

/-- Every positive-scale ratio defining the squared lattice threshold is at least `1/4`. -/
lemma one_fourth_le_latticeProfile_sq_div (α : {α : ℝ // 0 < α}) :
    (4 : ℝ)⁻¹ ≤ (α : ℝ) ^ 2 / latticeProfile α := by
  rw [le_div_iff₀ (latticeProfile_pos (ne_of_gt α.property))]
  have hbound := latticeProfile_le_four_mul_sq (α : ℝ)
  nlinarith

/-- The squared lattice threshold is nonnegative. -/
lemma latticeThresholdSq_nonneg : 0 ≤ latticeThresholdSq := by
  rw [latticeThresholdSq]
  exact le_ciInf fun α => latticeProfile_sq_div_nonneg α

/-- The squared lattice threshold is strictly positive. -/
lemma latticeThresholdSq_pos : 0 < latticeThresholdSq := by
  have hquarter : (4 : ℝ)⁻¹ ≤ latticeThresholdSq := by
    rw [latticeThresholdSq]
    exact le_ciInf one_fourth_le_latticeProfile_sq_div
  positivity

/-- The squared lattice threshold is strictly smaller than one, by evaluating its
defining infimum at `α = 1/2`. -/
lemma latticeThresholdSq_lt_one : latticeThresholdSq < 1 := by
  let α : {α : ℝ // 0 < α} := ⟨1 / 2, by norm_num⟩
  have hbdd : BddBelow (Set.range fun β : {β : ℝ // 0 < β} =>
      (β : ℝ) ^ 2 / latticeProfile β) :=
    ⟨0, Set.forall_mem_range.mpr fun β => latticeProfile_sq_div_nonneg β⟩
  have hle : latticeThresholdSq ≤ (α : ℝ) ^ 2 / latticeProfile α := by
    rw [latticeThresholdSq]
    exact ciInf_le hbdd α
  have hratio : (α : ℝ) ^ 2 / latticeProfile α < 1 := by
    rw [div_lt_one (latticeProfile_pos (ne_of_gt α.property))]
    dsimp [α]
    norm_num
    exact one_fourth_lt_latticeProfile_half
  exact hle.trans_lt hratio

/-- The lattice threshold is nonnegative. -/
lemma latticeThreshold_nonneg : 0 ≤ latticeThreshold :=
  Real.sqrt_nonneg _

/-- The lattice threshold is strictly positive. -/
lemma latticeThreshold_pos : 0 < latticeThreshold := by
  rw [latticeThreshold]
  exact Real.sqrt_pos.2 latticeThresholdSq_pos

/-- The lattice threshold belongs to the open unit interval. -/
lemma latticeThreshold_lt_one : latticeThreshold < 1 := by
  have hsquare : latticeThreshold ^ 2 = latticeThresholdSq := by
    rw [latticeThreshold, Real.sq_sqrt latticeThresholdSq_nonneg]
  nlinarith [hsquare, latticeThreshold_nonneg, latticeThresholdSq_lt_one]

/-- Squaring the lattice threshold recovers the infimum defining its square. -/
@[simp] lemma latticeThreshold_sq : latticeThreshold ^ 2 = latticeThresholdSq := by
  rw [latticeThreshold, Real.sq_sqrt latticeThresholdSq_nonneg]

/-- The squared lattice threshold is below every positive-scale ratio entering its
defining infimum. -/
lemma latticeThresholdSq_le_sq_div_profile {α : ℝ} (hα : 0 < α) :
    latticeThresholdSq ≤ α ^ 2 / latticeProfile α := by
  let β : {β : ℝ // 0 < β} := ⟨α, hα⟩
  have hbdd : BddBelow (Set.range fun γ : {γ : ℝ // 0 < γ} =>
      (γ : ℝ) ^ 2 / latticeProfile γ) :=
    ⟨0, Set.forall_mem_range.mpr fun γ => latticeProfile_sq_div_nonneg γ⟩
  rw [latticeThresholdSq]
  exact ciInf_le hbdd β

/-- Below the lattice threshold, the normalized profile is strictly contractive at
every positive scale. -/
lemma sq_mul_latticeProfile_div_sq_lt_one {A α : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hα : 0 < α) :
    A ^ 2 * latticeProfile α / α ^ 2 < 1 := by
  have hA_sq : A ^ 2 < latticeThresholdSq := by
    rw [← latticeThreshold_sq]
    nlinarith
  have hratio : A ^ 2 < α ^ 2 / latticeProfile α :=
    lt_of_lt_of_le hA_sq (latticeThresholdSq_le_sq_div_profile hα)
  rw [lt_div_iff₀ (latticeProfile_pos (ne_of_gt hα))] at hratio
  rw [div_lt_one (sq_pos_of_pos hα)]
  exact hratio

/-- Normalizing `L_A(h)` by `h` is the same as normalizing the profile at the scale
`α = A√h`, with the factor `A²` restored. -/
lemma latticeMap_div_eq_sq_mul_profile_div_sq {A h : ℝ} (hA : 0 < A) (hh : 0 < h) :
    latticeMap A h / h =
      A ^ 2 * latticeProfile (A * Real.sqrt h) / (A * Real.sqrt h) ^ 2 := by
  rw [latticeMap_eq]
  have hsqrt_sq : (Real.sqrt h) ^ 2 = h := Real.sq_sqrt (le_of_lt hh)
  have hA0 : A ≠ 0 := ne_of_gt hA
  rw [mul_pow, hsqrt_sq]
  field_simp

/-- At small positive radii, the normalized comparison map tends to zero. -/
lemma latticeMap_ratio_tendsto_zero {A : ℝ} (hA : 0 < A) :
    Tendsto (fun h => latticeMap A h / h) (𝓝[>] 0) (𝓝 0) := by
  have hsqrt : Tendsto (fun h : ℝ => Real.sqrt h) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact Real.sqrt_pos.2 hh
  have hscale : Tendsto (fun h : ℝ => A * Real.sqrt h) (𝓝[>] 0) (𝓝[>] 0) := by
    simpa using Filter.TendstoNhdsWithinIoi.const_mul hA hsqrt
  have hconv : Tendsto
      (fun h => A ^ 2 * (latticeProfile (A * Real.sqrt h) / (A * Real.sqrt h) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (latticeProfile_ratio_tendsto_zero.comp hscale).const_mul (A ^ 2)
  refine hconv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [latticeMap_div_eq_sq_mul_profile_div_sq hA hh, mul_div_assoc]

/-- At large radii, the normalized comparison map tends to `A²`. -/
lemma latticeMap_ratio_tendsto_sq_atTop {A : ℝ} (hA : 0 < A) :
    Tendsto (fun h => latticeMap A h / h) atTop (𝓝 (A ^ 2)) := by
  have hscale : Tendsto (fun h : ℝ => A * Real.sqrt h) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hA Real.tendsto_sqrt_atTop
  have hconv : Tendsto
      (fun h => A ^ 2 * (latticeProfile (A * Real.sqrt h) / (A * Real.sqrt h) ^ 2))
      atTop (𝓝 (A ^ 2)) := by
    simpa using (latticeProfile_ratio_tendsto_one.comp hscale).const_mul (A ^ 2)
  refine hconv.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with h hh
  rw [latticeMap_div_eq_sq_mul_profile_div_sq hA hh, mul_div_assoc]

/-- The normalized comparison map `L_A(h)/h` is continuous at positive radii. -/
lemma continuousOn_latticeMap_ratio {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun h => latticeMap A h / h) (Set.Ioi 0) := by
  have hscale : ContinuousOn (fun h : ℝ => A * Real.sqrt h) (Set.Ioi 0) :=
    continuous_const.mul Real.continuous_sqrt |>.continuousOn
  have hmap : ContinuousOn (fun h : ℝ => latticeProfile (A * Real.sqrt h)) (Set.Ioi 0) := by
    refine continuousOn_latticeProfile.comp hscale ?_
    intro h hh
    exact mul_pos hA (Real.sqrt_pos.2 hh)
  exact hmap.div continuousOn_id (fun h hh => ne_of_gt hh)

/-- Below threshold, the normalized comparison map is pointwise strictly below one. -/
lemma latticeMap_ratio_lt_one {A h : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hh : 0 < h) :
    latticeMap A h / h < 1 := by
  rw [latticeMap_div_eq_sq_mul_profile_div_sq hA hh]
  exact sq_mul_latticeProfile_div_sq_lt_one hA hA_lt
    (mul_pos hA (Real.sqrt_pos.2 hh))

/-- Below threshold, the normalized comparison map is already below one on both tails. -/
lemma exists_latticeMap_ratio_tail_cutoffs {A : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) :
    ∃ a R : ℝ, 0 < a ∧ a ≤ R ∧
      (∀ h, 0 < h → h < a → latticeMap A h / h < 1) ∧
      (∀ h, R ≤ h → latticeMap A h / h < 1) := by
  have hsmall : {h : ℝ | latticeMap A h / h < 1} ∈ 𝓝[>] 0 :=
    latticeMap_ratio_tendsto_zero hA (Iio_mem_nhds (by norm_num))
  obtain ⟨a, ha, hasub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  have hA_sq : A ^ 2 < 1 := by
    nlinarith [latticeThreshold_lt_one]
  have hlarge : {h : ℝ | latticeMap A h / h < 1} ∈ atTop :=
    latticeMap_ratio_tendsto_sq_atTop hA (Iio_mem_nhds hA_sq)
  obtain ⟨R₀, hR₀⟩ := mem_atTop_sets.mp hlarge
  refine ⟨a, max a R₀, ha, le_max_left _ _, ?_, ?_⟩
  · intro h hh hha
    exact hasub ⟨hh, hha⟩
  · intro h hRh
    exact hR₀ h (le_trans (le_max_right _ _) hRh)

/-- Below threshold, both tails of the normalized comparison map admit one common
uniform bound strictly below one. -/
lemma exists_latticeMap_ratio_tail_bound {A : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) :
    ∃ a R θ : ℝ, 0 < a ∧ a ≤ R ∧ θ < 1 ∧
      (∀ h, 0 < h → h < a → latticeMap A h / h ≤ θ) ∧
      (∀ h, R ≤ h → latticeMap A h / h ≤ θ) := by
  let θ : ℝ := max (1 / 2) ((A ^ 2 + 1) / 2)
  have hA_sq : A ^ 2 < 1 := by
    nlinarith [latticeThreshold_lt_one]
  have hθ : θ < 1 := by
    dsimp [θ]
    exact max_lt (by norm_num) (by linarith)
  have hzeroθ : 0 < θ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hAθ : A ^ 2 < θ :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hsmall : {h : ℝ | latticeMap A h / h < θ} ∈ 𝓝[>] 0 :=
    latticeMap_ratio_tendsto_zero hA (Iio_mem_nhds hzeroθ)
  obtain ⟨a, ha, hasub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  have hlarge : {h : ℝ | latticeMap A h / h < θ} ∈ atTop :=
    latticeMap_ratio_tendsto_sq_atTop hA (Iio_mem_nhds hAθ)
  obtain ⟨R₀, hR₀⟩ := mem_atTop_sets.mp hlarge
  refine ⟨a, max a R₀, θ, ha, le_max_left _ _, hθ, ?_, ?_⟩
  · intro h hh hha
    exact le_of_lt (hasub ⟨hh, hha⟩)
  · intro h hRh
    exact le_of_lt (hR₀ h (le_trans (le_max_right _ _) hRh))

/-- On every positive compact middle interval, the normalized comparison map has a
uniform bound strictly below one. -/
lemma exists_latticeMap_ratio_middle_bound {A a R : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (ha : 0 < a) (haR : a ≤ R) :
    ∃ θ : ℝ, θ < 1 ∧ ∀ h ∈ Set.Icc a R, latticeMap A h / h ≤ θ := by
  have hne : (Set.Icc a R).Nonempty := Set.nonempty_Icc.mpr haR
  have hcont : ContinuousOn (fun h => latticeMap A h / h) (Set.Icc a R) :=
    (continuousOn_latticeMap_ratio hA).mono fun h hh =>
      lt_of_lt_of_le ha hh.1
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  refine ⟨latticeMap A x / x, latticeMap_ratio_lt_one hA hA_lt
    (lt_of_lt_of_le ha hx.1), ?_⟩
  exact hmax

/-- Below the lattice threshold, the comparison map is a uniform strict contraction
on the whole positive half-line (claim (II) of `lem:subcritical-lattice-regimes`). -/
lemma exists_latticeMap_le_mul {A : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ h, 0 < h → latticeMap A h ≤ θ * h := by
  obtain ⟨a, R, θtail, ha, haR, hθtail, hsmall, hlarge⟩ :=
    exists_latticeMap_ratio_tail_bound hA hA_lt
  obtain ⟨θmid, hθmid, hmiddle⟩ :=
    exists_latticeMap_ratio_middle_bound hA hA_lt ha haR
  let θ : ℝ := max (1 / 2) (max θtail θmid)
  have hθpos : 0 < θ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hθlt : θ < 1 := by
    dsimp [θ]
    exact max_lt (by norm_num) (max_lt hθtail hθmid)
  refine ⟨θ, hθpos, hθlt, ?_⟩
  intro h hh
  rw [← div_le_iff₀ hh]
  by_cases hha : h < a
  · exact (hsmall h hh hha).trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
  by_cases hRh : R ≤ h
  · exact (hlarge h hRh).trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hhmem : h ∈ Set.Icc a R := ⟨not_lt.mp hha, not_le.mp hRh |>.le⟩
    exact (hmiddle h hhmem).trans
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Below the lattice threshold, the exact rounded mean map contracts uniformly,
independently of the positive grid scale (claim (III) of
`lem:subcritical-lattice-regimes`). -/
lemma exists_roundedMeanMap_le_mul {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hρ : 0 < ρ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ h, 0 ≤ h → roundedMeanMap A ρ h ≤ θ * h := by
  obtain ⟨θ, hθpos, hθlt, hcontract⟩ := exists_latticeMap_le_mul hA hA_lt
  refine ⟨θ, hθpos, hθlt, ?_⟩
  intro h hh
  rcases eq_or_lt_of_le hh with rfl | hh
  · simp
  · exact (roundedMeanMap_le_latticeMap hρ).trans (hcontract h hh)

end AbsorptionCutoff
