/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedPrecision
import Mathlib.Order.Lattice.Nat

/-!
# Normalized amplification along rounded deterministic orbits

Begins the paper's `lem:subcritical-normalized-lattice-amplification` (§4).
-/

namespace AbsorptionCutoff

open Filter MeasureTheory
open scoped Topology

/-- The terminal deterministic radius scale `a_N = 1 / log N`. -/
noncomputable def fixedPrecisionScale (N : ℕ) : ℝ :=
  (Real.log N)⁻¹

/-- The reciprocal terminal scale is exactly `log N`. -/
lemma fixedPrecisionScale_inv (N : ℕ) :
    (fixedPrecisionScale N)⁻¹ = Real.log N := by
  rw [fixedPrecisionScale, inv_inv]

/-- Division by the terminal scale is multiplication by `log N`. -/
lemma div_fixedPrecisionScale (K : ℝ) (N : ℕ) :
    K / fixedPrecisionScale N = K * Real.log N := by
  rw [div_eq_mul_inv, fixedPrecisionScale_inv]

/-- The logarithmic tail horizon is exactly an affine function of `log log N`. -/
lemma log_div_fixedPrecisionScale {C₀ : ℝ} {N : ℕ}
    (hC₀ : 0 < C₀) (hN : 1 < N) :
    Real.log (C₀ / fixedPrecisionScale N) =
      Real.log C₀ + Real.log (Real.log N) := by
  rw [div_fixedPrecisionScale, Real.log_mul hC₀.ne'
    (Real.log_pos (by exact_mod_cast hN)).ne']

/-- The deterministic orbit of the fixed-precision rounded mean map. -/
noncomputable def roundedOrbit (A ρ h₀ : ℝ) (t : ℕ) : ℝ :=
  (roundedMeanMap A ρ)^[t] h₀

/-- The first deterministic time at which the rounded orbit reaches radius
`r`, with the usual `sInf ∅ = 0` convention. -/
noncomputable def roundedOrbitEntrance (A ρ h₀ r : ℝ) : ℕ :=
  sInf {t : ℕ | roundedOrbit A ρ h₀ t ≤ r}

/-- A nonempty entrance set is reached at its infimum. -/
lemma roundedOrbitEntrance_spec {A ρ h₀ r : ℝ}
    (hexists : ∃ t : ℕ, roundedOrbit A ρ h₀ t ≤ r) :
    roundedOrbit A ρ h₀ (roundedOrbitEntrance A ρ h₀ r) ≤ r := by
  exact Nat.sInf_mem hexists

/-- Strictly before the entrance index, the orbit remains above the target
radius. -/
lemma roundedOrbit_lt_entrance {A ρ h₀ r : ℝ} {t : ℕ}
    (ht : t < roundedOrbitEntrance A ρ h₀ r) :
    r < roundedOrbit A ρ h₀ t := by
  by_contra hnot
  have hmem : t ∈ {u : ℕ | roundedOrbit A ρ h₀ u ≤ r} := not_lt.mp hnot
  exact (not_le_of_gt ht) (Nat.sInf_le hmem)

/-- An antitone orbit stays below a target radius after entering it. -/
lemma roundedOrbit_le_of_entrance_le {A ρ h₀ r : ℝ} {t : ℕ}
    (hexists : ∃ u : ℕ, roundedOrbit A ρ h₀ u ≤ r)
    (hanti : Antitone (roundedOrbit A ρ h₀))
    (ht : roundedOrbitEntrance A ρ h₀ r ≤ t) :
    roundedOrbit A ρ h₀ t ≤ r :=
  (hanti ht).trans (roundedOrbitEntrance_spec hexists)

/-- Reaching a smaller radius cannot occur before reaching a larger one. -/
lemma roundedOrbitEntrance_mono_radius {A ρ h₀ a r : ℝ}
    (har : a ≤ r)
    (hexists : ∃ u : ℕ, roundedOrbit A ρ h₀ u ≤ a) :
    roundedOrbitEntrance A ρ h₀ r ≤ roundedOrbitEntrance A ρ h₀ a := by
  apply Nat.sInf_le
  exact (roundedOrbitEntrance_spec hexists).trans har

/-- The rounded deterministic orbit starts from its prescribed initial radius. -/
@[simp]
lemma roundedOrbit_zero (A ρ h₀ : ℝ) :
    roundedOrbit A ρ h₀ 0 = h₀ := by
  simp [roundedOrbit]

/-- The rounded deterministic orbit obeys the mean-map recursion. -/
lemma roundedOrbit_succ (A ρ h₀ : ℝ) (t : ℕ) :
    roundedOrbit A ρ h₀ (t + 1) =
      roundedMeanMap A ρ (roundedOrbit A ρ h₀ t) := by
  exact Function.iterate_succ_apply' (roundedMeanMap A ρ) t h₀

/-- The terminal deterministic radius scale is positive once `N>1`. -/
lemma fixedPrecisionScale_pos {N : ℕ} (hN : 1 < N) :
    0 < fixedPrecisionScale N := by
  rw [fixedPrecisionScale]
  exact inv_pos.mpr (Real.log_pos (by exact_mod_cast hN))

/-- The terminal fixed-precision radius tends to zero with the dimension. -/
lemma tendsto_fixedPrecisionScale_zero :
    Tendsto fixedPrecisionScale atTop (𝓝 0) := by
  convert
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop using 1
  ext N
  rfl

/-- The double logarithm of the dimension diverges. -/
lemma tendsto_log_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log N)) atTop atTop := by
  convert Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) using 1
  ext N
  rfl

/-- Every quadratic-logarithmic exponential is sublinear in the dimension:
`N⁻¹ exp(C (log log N)²) → 0`. -/
lemma tendsto_inv_nat_mul_exp_log_log_sq_zero (C : ℝ) :
    Tendsto
      (fun N : ℕ =>
        (N : ℝ)⁻¹ * Real.exp (C * (Real.log (Real.log N)) ^ 2))
      atTop (𝓝 0) := by
  let Cp := |C| + 1
  have hCp : 0 < Cp := by
    dsimp [Cp]
    linarith [abs_nonneg C]
  have hlogNat :
      Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmallReal :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log x ^ 2‖ ≤ (2 * Cp)⁻¹ * ‖x‖ :=
    Asymptotics.isLittleO_iff.mp
      (Real.isLittleO_pow_log_id_atTop (n := 2))
      (inv_pos.mpr (mul_pos (by norm_num) hCp))
  have hsmallNat :
      ∀ᶠ N : ℕ in atTop,
        ‖Real.log (Real.log N) ^ 2‖ ≤
          (2 * Cp)⁻¹ * ‖Real.log N‖ :=
    hlogNat.eventually hsmallReal
  have hlogNonneg :
      ∀ᶠ N : ℕ in atTop, 0 ≤ Real.log (N : ℝ) :=
    hlogNat.eventually (eventually_ge_atTop 0)
  have hexponent :
      ∀ᶠ N : ℕ in atTop,
        C * (Real.log (Real.log N)) ^ 2 - Real.log N ≤
          (-1 / 2 : ℝ) * Real.log N := by
    filter_upwards [hsmallNat, hlogNonneg] with N hsmall hlog
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg hlog] at hsmall
    have hCCp : C ≤ Cp := by
      dsimp [Cp]
      linarith [le_abs_self C]
    have hsquare :
        C * (Real.log (Real.log N)) ^ 2 ≤
          (1 / 2 : ℝ) * Real.log N := by
      calc
        C * (Real.log (Real.log N)) ^ 2 ≤
            Cp * (Real.log (Real.log N)) ^ 2 :=
          mul_le_mul_of_nonneg_right hCCp (sq_nonneg _)
        _ ≤ Cp * ((2 * Cp)⁻¹ * Real.log N) :=
          mul_le_mul_of_nonneg_left hsmall hCp.le
        _ = (1 / 2 : ℝ) * Real.log N := by
          field_simp [hCp.ne']
    linarith
  have heq :
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ)⁻¹ *
            Real.exp (C * (Real.log (Real.log N)) ^ 2) =
          Real.exp
            (C * (Real.log (Real.log N)) ^ 2 - Real.log N) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hinv : (N : ℝ)⁻¹ = Real.exp (-Real.log N) := by
      rw [Real.exp_neg, Real.exp_log hNreal]
    rw [hinv, ← Real.exp_add]
    congr 1
    ring
  have hupper :
      Tendsto (fun N : ℕ => Real.exp ((-1 / 2 : ℝ) * Real.log N))
        atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact hlogNat.const_mul_atTop_of_neg (by norm_num)
  refine squeeze_zero'
    (f := fun N : ℕ =>
      (N : ℝ)⁻¹ * Real.exp (C * (Real.log (Real.log N)) ^ 2))
    (g := fun N : ℕ => Real.exp ((-1 / 2 : ℝ) * Real.log N))
    (Eventually.of_forall fun N => by positivity) ?_ hupper
  filter_upwards [heq, hexponent] with N hEq hbound
  calc
    (N : ℝ)⁻¹ * Real.exp (C * (Real.log (Real.log N)) ^ 2) =
        Real.exp
          (C * (Real.log (Real.log N)) ^ 2 - Real.log N) := hEq
    _ ≤ Real.exp ((-1 / 2 : ℝ) * Real.log N) :=
      Real.exp_le_exp.mpr hbound

/-- The paper's horizon hypothesis is unchanged if the capped-exit sentinel
replaces `T_N` by `T_N + 1`. -/
lemma tendsto_succ_nat_div_mul_exp_log_log_sq_zero
    (T : ℕ → ℕ)
    (hT : ∀ C : ℝ,
      Tendsto
        (fun N : ℕ =>
          (T N : ℝ) / (N : ℝ) *
            Real.exp (C * (Real.log (Real.log N)) ^ 2))
        atTop (𝓝 0))
    (C : ℝ) :
    Tendsto
      (fun N : ℕ =>
        ((T N + 1 : ℕ) : ℝ) / (N : ℝ) *
          Real.exp (C * (Real.log (Real.log N)) ^ 2))
      atTop (𝓝 0) := by
  have hadd :=
    (hT C).add (tendsto_inv_nat_mul_exp_log_log_sq_zero C)
  convert hadd using 1
  · ext N
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  · simp

/-- Every fixed real number is eventually below `log log N`. -/
lemma exists_eventually_le_log_log_nat (x : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → x ≤ Real.log (Real.log N) := by
  have heventually :
      ∀ᶠ N : ℕ in atTop, x ≤ Real.log (Real.log N) :=
    tendsto_log_log_nat_atTop.eventually_ge_atTop x
  rw [eventually_atTop] at heventually
  exact heventually

/-- Every positive constant times `log N` is eventually at least one. -/
lemma exists_eventually_one_le_mul_log_nat {K : ℝ} (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ K * Real.log N := by
  have htend :
      Tendsto (fun N : ℕ => Real.log N) atTop atTop := by
    convert Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop using 1
    ext N
    rfl
  have heventually :
      ∀ᶠ N : ℕ in atTop, 1 / K ≤ Real.log N :=
    htend.eventually_ge_atTop (1 / K)
  rw [eventually_atTop] at heventually
  obtain ⟨N₀, hN₀⟩ := heventually
  refine ⟨N₀, ?_⟩
  intro N hN
  simpa [mul_comm] using (div_le_iff₀ hK).mp (hN₀ N hN)

/-- Eventually, the logarithm of the truncated tail factor is affine in
`log log N`. -/
lemma exists_eventually_log_max_one_mul_log_eq {K : ℝ} (hK : 0 < K) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.log (max 1 (K * Real.log N)) =
        Real.log K + Real.log (Real.log N) := by
  obtain ⟨N₀, hN₀⟩ := exists_eventually_one_le_mul_log_nat hK
  refine ⟨N₀, ?_⟩
  intro N hN
  have hmul := hN₀ N hN
  have hlog : 0 < Real.log N := by nlinarith
  rw [max_eq_right hmul, Real.log_mul hK.ne' hlog.ne']

/-- Beyond a finite dimension threshold, the terminal scale is positive and
below any prescribed positive bound. -/
lemma exists_eventually_fixedPrecisionScale_bounds {a₀ : ℝ} (ha₀ : 0 < a₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      1 < N ∧ 0 < fixedPrecisionScale N ∧ fixedPrecisionScale N ≤ a₀ := by
  have heventually : ∀ᶠ N : ℕ in atTop, fixedPrecisionScale N < a₀ :=
    (tendsto_order.1 tendsto_fixedPrecisionScale_zero).2 a₀ ha₀
  rw [eventually_atTop] at heventually
  obtain ⟨N₁, hN₁⟩ := heventually
  refine ⟨max 2 N₁, ?_⟩
  intro N hN
  have hNtwo : 2 ≤ N := (le_max_left 2 N₁).trans hN
  have hN₁N : N₁ ≤ N := (le_max_right 2 N₁).trans hN
  have hNone : 1 < N := by omega
  exact ⟨hNone, fixedPrecisionScale_pos hNone, (hN₁ N hN₁N).le⟩

/-- The rounded mean map is nonnegative because it is an integral of squares. -/
lemma roundedMeanMap_nonneg (A ρ h : ℝ) :
    0 ≤ roundedMeanMap A ρ h :=
  integral_nonneg fun g => by positivity

/-- The rounded mean map vanishes on the nonpositive half-line. -/
lemma roundedMeanMap_of_nonpos (A ρ : ℝ) {h : ℝ} (hh : h ≤ 0) :
    roundedMeanMap A ρ h = 0 := by
  have hQ : Q₁ (0 : ℝ) = 0 := (Q₁_zero_iff 0).mpr (by norm_num)
  simp [roundedMeanMap, Real.sqrt_eq_zero_of_nonpos hh, hQ]

/-- The rounded mean map has the paper's flat extension at the radius origin. -/
lemma hasDerivAt_roundedMeanMap_zero {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    HasDerivAt (roundedMeanMap A ρ) 0 0 := by
  obtain ⟨c, C, hc, hC, hbound⟩ :=
    exists_roundedMeanMap_small_radius_bounds hA hρ hρ_lt
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine (tendsto_const_nhds (x := 0)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : h ≤ 0 := hh.le
    simp [slope, roundedMeanMap_of_nonpos A ρ hh',
      roundedMeanMap_of_nonpos A ρ le_rfl]
  · have hscale : Tendsto (fun h : ℝ => h / c) (𝓝 0) (𝓝 0) := by
      convert (continuousAt_id.div_const c).tendsto using 1 <;> simp
    have hcore :
        Tendsto (fun h : ℝ => (c / h) * Real.exp (-c / h))
          (𝓝[>] 0) (𝓝 0) := by
      have ht :=
        (expNegInvGlue.tendsto_polynomial_inv_mul_zero
          (Polynomial.X : Polynomial ℝ)).comp hscale
      refine (ht.mono_left inf_le_left).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hhpos : 0 < h := hh
      have hhc : 0 < h / c := div_pos hhpos hc
      change Polynomial.X.eval (h / c)⁻¹ * expNegInvGlue (h / c) =
        (c / h) * Real.exp (-c / h)
      rw [show (h / c)⁻¹ = c / h by field_simp [hc.ne', hhpos.ne']]
      simp only [Polynomial.eval_X, expNegInvGlue, if_neg (not_le.mpr hhc)]
      congr 2
      field_simp [hc.ne', hhpos.ne']
    have hupper :
        Tendsto (fun h : ℝ => C * Real.exp (-c / h) / h)
          (𝓝[>] 0) (𝓝 0) := by
      convert (hcore.const_mul (C / c)) using 1
      · ext h
        by_cases hh : h = 0
        · simp [hh]
        · field_simp [hc.ne', hh]
      · simp
    apply squeeze_zero'
    · filter_upwards [self_mem_nhdsWithin] with h hh
      have hhpos : 0 < h := hh
      simpa [slope, roundedMeanMap_of_nonpos A ρ le_rfl,
        smul_eq_mul, div_eq_inv_mul] using
        div_nonneg (roundedMeanMap_nonneg A ρ h) hhpos.le
    · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with h hh
      simpa [slope, roundedMeanMap_of_nonpos A ρ le_rfl,
        smul_eq_mul, div_eq_inv_mul] using
        (div_le_div_iff_of_pos_right hh.1).mpr (hbound h hh.1 hh.2).1
    · have hslopeUpper :
          Tendsto (fun h : ℝ => h⁻¹ * (C * Real.exp (-(h⁻¹ * c))))
            (𝓝[>] 0) (𝓝 0) := by
          refine hupper.congr' ?_
          filter_upwards with h
          simp only [div_eq_mul_inv]
          ring_nf
      simpa only [slope, roundedMeanMap_of_nonpos A ρ le_rfl,
        sub_zero, smul_eq_mul] using hslopeUpper

/-- The derivative of the rounded mean map vanishes at the radius origin. -/
lemma deriv_roundedMeanMap_zero {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    deriv (roundedMeanMap A ρ) 0 = 0 :=
  (hasDerivAt_roundedMeanMap_zero hA hρ hρ_lt).deriv

/-- The rounded mean map, extended by zero on the nonpositive half-line, is
globally continuous. -/
lemma continuous_roundedMeanMap {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    Continuous (roundedMeanMap A ρ) := by
  rw [continuous_iff_continuousAt]
  intro h
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have heq : roundedMeanMap A ρ =ᶠ[𝓝 h] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds hh] with u hu
      exact roundedMeanMap_of_nonpos A ρ hu.le
    have ht : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 h) (𝓝 0) :=
      tendsto_const_nhds
    have hzero : roundedMeanMap A ρ h = 0 :=
      roundedMeanMap_of_nonpos A ρ hh.le
    change Tendsto (roundedMeanMap A ρ) (𝓝 h)
      (𝓝 (roundedMeanMap A ρ h))
    rw [hzero]
    exact ht.congr' heq.symm
  · exact (hasDerivAt_roundedMeanMap_zero hA hρ hρ_lt).continuousAt
  · exact (hasDerivAt_roundedMeanMap hA hρ hh).continuousAt

/-- The rescaled inverse-square exponential envelope extends continuously
through the origin. -/
lemma continuous_inv_sq_mul_expNegInvGlue_div (c : ℝ) :
    Continuous
      ((fun x : ℝ =>
          (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
        fun u : ℝ => u / c) :=
  (expNegInvGlue.continuous_polynomial_eval_inv_mul
    (Polynomial.X ^ 2)).comp (continuous_id.div_const c)

/-- The rescaled inverse-square exponential envelope vanishes at the origin. -/
lemma tendsto_inv_sq_mul_expNegInvGlue_div_zero (c : ℝ) :
    Tendsto
      ((fun x : ℝ =>
          (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
        fun u : ℝ => u / c)
      (𝓝 0) (𝓝 0) := by
  let f : ℝ → ℝ :=
    (fun x : ℝ =>
      (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
      fun u : ℝ => u / c
  have hf : Continuous f := continuous_inv_sq_mul_expNegInvGlue_div c
  have hf0 : f 0 = 0 := by simp [f]
  have ht : Tendsto f (𝓝 0) (𝓝 (f 0)) := hf.continuousAt
  rw [hf0] at ht
  exact ht

/-- Vanishing at the origin is uniform on intervals whose right endpoint
shrinks to zero. -/
lemma exists_scale_inv_sq_mul_expNegInvGlue_le {c ε : ℝ} (hε : 0 < ε) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ a₀ →
        ∀ u ∈ Set.Icc (0 : ℝ) (2 * a),
          (((fun x : ℝ =>
              (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
            fun v : ℝ => v / c) u) ≤ ε := by
  have ht := tendsto_inv_sq_mul_expNegInvGlue_div_zero c
  rw [Metric.tendsto_nhds_nhds] at ht
  obtain ⟨η, hη, hcontrol⟩ :=
    ht ε hε
  refine ⟨η / 3, by positivity, ?_⟩
  intro a ha haη u hu
  have huη : dist u 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
    linarith [hu.2]
  have hout := hcontrol huη
  rw [Real.dist_eq, sub_zero] at hout
  exact (le_abs_self _).trans hout.le

/-- The continuously extended inverse-square exponential envelope is uniformly
bounded on every compact small-radius interval. -/
lemma exists_pos_inv_sq_mul_expNegInvGlue_bound (c r : ℝ) :
    ∃ D : ℝ, 0 < D ∧
      ∀ u ∈ Set.Icc (0 : ℝ) (2 * r),
        ((fun x : ℝ =>
            (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
          fun v : ℝ => v / c) u ≤ D := by
  obtain ⟨M, hM⟩ :=
    isCompact_Icc.bddAbove_image
      (continuous_inv_sq_mul_expNegInvGlue_div c).continuousOn
  let D := max 1 M
  refine ⟨D, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro u hu
  exact (hM ⟨u, hu, rfl⟩).trans (le_max_right _ _)

/-- On the positive half-line, the glued envelope is exactly the rescaled
inverse-square exponential appearing in the derivative estimate. -/
lemma mul_rpow_neg_two_exp_eq_rescaled_glue {c C u : ℝ}
    (hc : 0 < c) (hu : 0 < u) :
    C * u ^ (-2 : ℝ) * Real.exp (-c / u) =
      (C / c ^ 2) *
        (((fun x : ℝ =>
            (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
          fun v : ℝ => v / c) u) := by
  rw [Real.rpow_neg hu.le, Real.rpow_two]
  simp only [Function.comp_apply]
  rw [show expNegInvGlue (u / c) = Real.exp (-(u / c)⁻¹) by
    simp [expNegInvGlue, not_le.mpr (div_pos hu hc)]]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  field_simp [hc.ne', hu.ne']

/-- Every rounded deterministic orbit with nonnegative initial radius remains
nonnegative. -/
lemma roundedOrbit_nonneg {A ρ h₀ : ℝ} (hh₀ : 0 ≤ h₀) (t : ℕ) :
    0 ≤ roundedOrbit A ρ h₀ t := by
  induction t with
  | zero => simpa using hh₀
  | succ t ih =>
      rw [roundedOrbit_succ]
      exact roundedMeanMap_nonneg A ρ _

/-- A one-step contraction iterates to a geometric bound along the rounded orbit. -/
lemma roundedOrbit_le_pow {A ρ h₀ θ : ℝ}
    (hh₀ : 0 ≤ h₀) (hθ : 0 ≤ θ)
    (hcontract : ∀ h, 0 ≤ h → roundedMeanMap A ρ h ≤ θ * h) (t : ℕ) :
    roundedOrbit A ρ h₀ t ≤ θ ^ t * h₀ := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [roundedOrbit_succ]
      calc
        roundedMeanMap A ρ (roundedOrbit A ρ h₀ t) ≤
            θ * roundedOrbit A ρ h₀ t :=
          hcontract _ (roundedOrbit_nonneg hh₀ t)
        _ ≤ θ * (θ ^ t * h₀) := mul_le_mul_of_nonneg_left ih hθ
        _ = θ ^ (t + 1) * h₀ := by rw [pow_succ]; ring

/-- A rounded mean map below the diagonal generates an antitone deterministic
orbit. -/
lemma roundedOrbit_antitone_of_map_le {A ρ h₀ : ℝ}
    (hh₀ : 0 ≤ h₀)
    (hmap : ∀ h : ℝ, 0 ≤ h → roundedMeanMap A ρ h ≤ h) :
    Antitone (roundedOrbit A ρ h₀) := by
  apply antitone_nat_of_succ_le
  intro t
  rw [roundedOrbit_succ]
  exact hmap _ (roundedOrbit_nonneg hh₀ t)

/-- Every lattice-subcritical rounded deterministic orbit is antitone. -/
lemma roundedOrbit_antitone {A ρ h₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hh₀ : 0 ≤ h₀) :
    Antitone (roundedOrbit A ρ h₀) := by
  obtain ⟨θ, hθ, hθ_lt, hcontract⟩ :=
    exists_roundedMeanMap_le_mul hA hA_lt hρ
  apply roundedOrbit_antitone_of_map_le hh₀
  intro h hh
  exact (hcontract h hh).trans
    (mul_le_of_le_one_left hh hθ_lt.le)

/-- Any orbit controlled by a geometric sequence eventually enters every
fixed positive radius. -/
lemma exists_roundedOrbit_lt_radius_of_le_pow {A ρ h₀ θ r : ℝ}
    (hθ : 0 ≤ θ) (hθ_lt : θ < 1) (hr : 0 < r)
    (hbound : ∀ t : ℕ, roundedOrbit A ρ h₀ t ≤ θ ^ t * h₀) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → roundedOrbit A ρ h₀ t < r := by
  have htend :
      Tendsto (fun t : ℕ => θ ^ t * h₀) atTop (𝓝 0) :=
    by simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ_lt).mul_const h₀
  have heventually : ∀ᶠ t : ℕ in atTop, θ ^ t * h₀ < r :=
    (tendsto_order.1 htend).2 r hr
  rw [eventually_atTop] at heventually
  obtain ⟨T, hT⟩ := heventually
  exact ⟨T, fun t hTt => (hbound t).trans_lt (hT t hTt)⟩

/-- A geometric trajectory can remain above a positive scale for at most a
logarithmic number of steps. -/
lemma natCast_le_log_div_neg_log_of_le_geometric
    {θ a C₀ : ℝ} {t : ℕ}
    (hθ : 0 < θ) (hθ_lt : θ < 1) (ha : 0 < a) (hC₀ : 0 < C₀)
    (hle : a ≤ θ ^ t * C₀) :
    (t : ℝ) ≤ Real.log (C₀ / a) / (-Real.log θ) := by
  have hpow : 0 < θ ^ t := pow_pos hθ t
  have hlog :=
    Real.log_le_log ha hle
  rw [Real.log_mul hpow.ne' hC₀.ne', Real.log_pow] at hlog
  have hneglog : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ hθ_lt)
  rw [le_div_iff₀ hneglog, Real.log_div hC₀.ne' ha.ne']
  nlinarith

/-- The same logarithmic survival bound applies to any rounded orbit dominated
by the geometric trajectory. -/
lemma natCast_le_log_div_neg_log_of_roundedOrbit_ge
    {A ρ h₀ θ a C₀ : ℝ} {t : ℕ}
    (hθ : 0 < θ) (hθ_lt : θ < 1) (ha : 0 < a) (hC₀ : 0 < C₀)
    (hh₀C₀ : h₀ ≤ C₀)
    (hbound : ∀ u : ℕ, roundedOrbit A ρ h₀ u ≤ θ ^ u * h₀)
    (haorbit : a ≤ roundedOrbit A ρ h₀ t) :
    (t : ℝ) ≤ Real.log (C₀ / a) / (-Real.log θ) := by
  apply natCast_le_log_div_neg_log_of_le_geometric hθ hθ_lt ha hC₀
  exact haorbit.trans <| (hbound t).trans <|
    mul_le_mul_of_nonneg_left hh₀C₀ (pow_nonneg hθ.le t)

/-- Lattice subcriticality supplies the paper's geometric deterministic-orbit
contraction. -/
lemma exists_roundedOrbit_le_pow {A ρ h₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hρ : 0 < ρ) (hh₀ : 0 ≤ h₀) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ t : ℕ, roundedOrbit A ρ h₀ t ≤ θ ^ t * h₀ := by
  obtain ⟨θ, hθ, hθ_lt, hcontract⟩ :=
    exists_roundedMeanMap_le_mul hA hA_lt hρ
  exact ⟨θ, hθ, hθ_lt, roundedOrbit_le_pow hh₀ hθ.le hcontract⟩

/-- Lattice subcriticality bounds every time at which the orbit remains above
the terminal scale by a logarithmic ratio. -/
lemma exists_subcritical_time_le_log_fixedPrecisionScale
    {A ρ h₀ C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hρ : 0 < ρ)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ N : ℕ, 1 < N → ∀ t : ℕ,
        fixedPrecisionScale N ≤ roundedOrbit A ρ h₀ t →
        (t : ℝ) ≤
          Real.log (C₀ / fixedPrecisionScale N) / (-Real.log θ) := by
  obtain ⟨θ, hθ, hθ_lt, hbound⟩ :=
    exists_roundedOrbit_le_pow hA hA_lt hρ hh₀
  refine ⟨θ, hθ, hθ_lt, ?_⟩
  intro N hN t hscale
  exact natCast_le_log_div_neg_log_of_roundedOrbit_ge hθ hθ_lt
    (fixedPrecisionScale_pos hN) hC₀ hh₀C₀ hbound hscale

/-- Paper-shaped form of the subcritical tail-length bound, explicitly affine
in `log log N`. -/
lemma exists_subcritical_time_le_log_log
    {A ρ h₀ C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hρ : 0 < ρ)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      ∀ N : ℕ, 1 < N → ∀ t : ℕ,
        fixedPrecisionScale N ≤ roundedOrbit A ρ h₀ t →
        (t : ℝ) ≤
          (Real.log C₀ + Real.log (Real.log N)) / (-Real.log θ) := by
  obtain ⟨θ, hθ, hθ_lt, htime⟩ :=
    exists_subcritical_time_le_log_fixedPrecisionScale
      hA hA_lt hρ hh₀ hh₀C₀ hC₀
  refine ⟨θ, hθ, hθ_lt, ?_⟩
  intro N hN t hscale
  simpa only [log_div_fixedPrecisionScale hC₀ hN] using
    htime N hN t hscale

/-- Eventually, every time at which the subcritical orbit remains above the
terminal scale is at most a constant times `log log N`. -/
lemma exists_eventually_subcritical_time_le_mul_log_log
    {A ρ h₀ C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hρ : 0 < ρ)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀) :
    ∃ D : ℝ, 0 < D ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ t : ℕ, fixedPrecisionScale N ≤ roundedOrbit A ρ h₀ t →
        (t : ℝ) ≤ D * Real.log (Real.log N) := by
  obtain ⟨θ, hθ, hθ_lt, htime⟩ :=
    exists_subcritical_time_le_log_log
      hA hA_lt hρ hh₀ hh₀C₀ hC₀
  have hdenom : 0 < -Real.log θ :=
    neg_pos.mpr (Real.log_neg hθ hθ_lt)
  let D := 2 / (-Real.log θ)
  have hD : 0 < D := div_pos (by norm_num) hdenom
  obtain ⟨N₁, hN₁⟩ :=
    exists_eventually_le_log_log_nat (max 1 |Real.log C₀|)
  refine ⟨D, hD, max 2 N₁, ?_⟩
  intro N hN t hscale
  have hNtwo : 2 ≤ N := (le_max_left 2 N₁).trans hN
  have hNone : 1 < N := by omega
  have hN₁N : N₁ ≤ N := (le_max_right 2 N₁).trans hN
  have hlower :
      max 1 |Real.log C₀| ≤ Real.log (Real.log N) :=
    hN₁ N hN₁N
  have hnum :
      Real.log C₀ + Real.log (Real.log N) ≤
        2 * Real.log (Real.log N) := by
    linarith [le_abs_self (Real.log C₀),
      (le_max_right 1 |Real.log C₀|).trans hlower]
  calc
    (t : ℝ) ≤
        (Real.log C₀ + Real.log (Real.log N)) / (-Real.log θ) :=
      htime N hNone t hscale
    _ ≤ (2 * Real.log (Real.log N)) / (-Real.log θ) :=
      (div_le_div_iff_of_pos_right hdenom).mpr hnum
    _ = D * Real.log (Real.log N) := by
      dsimp [D]
      field_simp [hdenom.ne']

/-- Every contiguous segment on which the subcritical orbit remains above
`a_N` has length at most a constant times `log log N`. -/
lemma exists_eventually_subcritical_tail_length_le_mul_log_log
    {A ρ h₀ C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold) (hρ : 0 < ρ)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀) :
    ∃ D : ℝ, 0 < D ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ s t : ℕ,
        (∀ u ∈ Finset.Ico s t,
          fixedPrecisionScale N ≤ roundedOrbit A ρ h₀ u) →
        ((t - s : ℕ) : ℝ) ≤ (D + 1) * Real.log (Real.log N) := by
  obtain ⟨D, hD, N₁, htime⟩ :=
    exists_eventually_subcritical_time_le_mul_log_log
      hA hA_lt hρ hh₀ hh₀C₀ hC₀
  obtain ⟨N₂, hN₂⟩ := exists_eventually_le_log_log_nat 1
  refine ⟨D, hD, max N₁ N₂, ?_⟩
  intro N hN s t horbit
  have hN₁N : N₁ ≤ N := (le_max_left N₁ N₂).trans hN
  have hN₂N : N₂ ≤ N := (le_max_right N₁ N₂).trans hN
  have hloglog : 1 ≤ Real.log (Real.log N) := hN₂ N hN₂N
  by_cases hst : s < t
  · have hlast : t - 1 ∈ Finset.Ico s t := by
      simp only [Finset.mem_Ico]
      omega
    have hlastTime :=
      htime N hN₁N (t - 1) (horbit (t - 1) hlast)
    have hsuble : ((t - s : ℕ) : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast Nat.sub_le t s
    have ht : (t : ℝ) = ((t - 1 : ℕ) : ℝ) + 1 := by
      norm_cast
      omega
    nlinarith
  · have hts : t ≤ s := not_lt.mp hst
    rw [Nat.sub_eq_zero_of_le hts]
    norm_num only [Nat.cast_zero]
    exact mul_nonneg (add_nonneg hD.le zero_le_one)
      (zero_le_one.trans hloglog)

/-- The `O(log log N)` length bound is uniform over every nonnegative initial
radius bounded by the same compact constant `C₀`. -/
lemma exists_eventually_uniform_subcritical_tail_length_le_mul_log_log
    {A ρ C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hC₀ : 0 < C₀) :
    ∃ D : ℝ, 0 < D ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h₀ : ℝ, 0 ≤ h₀ → h₀ ≤ C₀ → ∀ s t : ℕ,
        (∀ u ∈ Finset.Ico s t,
          fixedPrecisionScale N ≤ roundedOrbit A ρ h₀ u) →
        ((t - s : ℕ) : ℝ) ≤ (D + 1) * Real.log (Real.log N) := by
  obtain ⟨θ, hθ, hθ_lt, hcontract⟩ :=
    exists_roundedMeanMap_le_mul hA hA_lt hρ
  have hdenom : 0 < -Real.log θ :=
    neg_pos.mpr (Real.log_neg hθ hθ_lt)
  let D := 2 / (-Real.log θ)
  have hD : 0 < D := div_pos (by norm_num) hdenom
  obtain ⟨Nell, hell⟩ :=
    exists_eventually_le_log_log_nat (max 1 |Real.log C₀|)
  refine ⟨D, hD, max 2 Nell, ?_⟩
  intro N hN h₀ hh₀ hh₀C₀ s t horbit
  have hNtwo : 2 ≤ N := (le_max_left 2 Nell).trans hN
  have hNone : 1 < N := by omega
  have hNell : Nell ≤ N := (le_max_right 2 Nell).trans hN
  have hellN :
      max 1 |Real.log C₀| ≤ Real.log (Real.log N) :=
    hell N hNell
  have hell_one : 1 ≤ Real.log (Real.log N) :=
    (le_max_left 1 |Real.log C₀|).trans hellN
  by_cases hst : s < t
  · have hlast : t - 1 ∈ Finset.Ico s t := by
      simp only [Finset.mem_Ico]
      omega
    have horbitBound :
        ∀ u : ℕ, roundedOrbit A ρ h₀ u ≤ θ ^ u * h₀ :=
      roundedOrbit_le_pow hh₀ hθ.le hcontract
    have hlastTime :=
      natCast_le_log_div_neg_log_of_roundedOrbit_ge
        hθ hθ_lt (fixedPrecisionScale_pos hNone) hC₀ hh₀C₀
        horbitBound (horbit (t - 1) hlast)
    rw [log_div_fixedPrecisionScale hC₀ hNone] at hlastTime
    have hnum :
        Real.log C₀ + Real.log (Real.log N) ≤
          2 * Real.log (Real.log N) := by
      linarith [le_abs_self (Real.log C₀),
        (le_max_right 1 |Real.log C₀|).trans hellN]
    have hlastBound :
        ((t - 1 : ℕ) : ℝ) ≤ D * Real.log (Real.log N) := by
      calc
        ((t - 1 : ℕ) : ℝ) ≤
            (Real.log C₀ + Real.log (Real.log N)) / (-Real.log θ) :=
          hlastTime
        _ ≤ (2 * Real.log (Real.log N)) / (-Real.log θ) :=
          (div_le_div_iff_of_pos_right hdenom).mpr hnum
        _ = D * Real.log (Real.log N) := by
          dsimp [D]
          field_simp [hdenom.ne']
    have hsuble : ((t - s : ℕ) : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast Nat.sub_le t s
    have ht : (t : ℝ) = ((t - 1 : ℕ) : ℝ) + 1 := by
      norm_cast
      omega
    nlinarith
  · have hts : t ≤ s := not_lt.mp hst
    rw [Nat.sub_eq_zero_of_le hts]
    norm_num only [Nat.cast_zero]
    exact mul_nonneg (add_nonneg hD.le zero_le_one)
      (zero_le_one.trans hell_one)

/-- Every lattice-subcritical rounded orbit enters a prescribed positive
radius after a finite deterministic time. -/
lemma exists_roundedOrbit_lt_radius {A ρ h₀ r : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hh₀ : 0 ≤ h₀) (hr : 0 < r) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → roundedOrbit A ρ h₀ t < r := by
  obtain ⟨θ, hθ, hθ_lt, hbound⟩ :=
    exists_roundedOrbit_le_pow hA hA_lt hρ hh₀
  exact exists_roundedOrbit_lt_radius_of_le_pow hθ.le hθ_lt hr hbound

/-- Every positive-radius entrance set is nonempty under lattice
subcriticality, so the orbit reaches the target at its entrance index. -/
lemma roundedOrbitEntrance_spec_of_subcritical {A ρ h₀ r : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hh₀ : 0 ≤ h₀) (hr : 0 < r) :
    roundedOrbit A ρ h₀ (roundedOrbitEntrance A ρ h₀ r) ≤ r := by
  obtain ⟨T, hT⟩ :=
    exists_roundedOrbit_lt_radius hA hA_lt hρ hh₀ hr
  apply roundedOrbitEntrance_spec
  exact ⟨T, (hT T le_rfl).le⟩

/-- Between the entrances into radii `r` and `a`, the orbit lies in the
pre-terminal tail `(a,r]`. -/
lemma roundedOrbit_mem_tail_between_entrances
    {A ρ h₀ a r : ℝ} {u : ℕ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hh₀ : 0 ≤ h₀) (hr : 0 < r)
    (hru : roundedOrbitEntrance A ρ h₀ r ≤ u)
    (hua : u < roundedOrbitEntrance A ρ h₀ a) :
    a < roundedOrbit A ρ h₀ u ∧ roundedOrbit A ρ h₀ u ≤ r := by
  have hrSpec :=
    roundedOrbitEntrance_spec_of_subcritical hA hA_lt hρ hh₀ hr
  exact ⟨roundedOrbit_lt_entrance hua,
    roundedOrbit_le_of_entrance_le
      ⟨roundedOrbitEntrance A ρ h₀ r, hrSpec⟩
      (roundedOrbit_antitone hA hA_lt hρ hh₀) hru⟩

/-- Before entering radius `r`, a subcritical orbit stays in the compact
interval `(r,C₀]` determined by its initial upper bound. -/
lemma roundedOrbit_mem_compact_before_entrance
    {A ρ h₀ r C₀ : ℝ} {u : ℕ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀)
    (hu : u < roundedOrbitEntrance A ρ h₀ r) :
    r < roundedOrbit A ρ h₀ u ∧ roundedOrbit A ρ h₀ u ≤ C₀ := by
  have hupper :
      roundedOrbit A ρ h₀ u ≤ roundedOrbit A ρ h₀ 0 :=
    roundedOrbit_antitone hA hA_lt hρ hh₀ (Nat.zero_le u)
  exact ⟨roundedOrbit_lt_entrance hu, by simpa using hupper.trans hh₀C₀⟩

/-- After entering a positive terminal radius, a subcritical orbit remains
below it. -/
lemma roundedOrbit_mem_terminal_after_entrance
    {A ρ h₀ a : ℝ} {u : ℕ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hh₀ : 0 ≤ h₀) (ha : 0 < a)
    (hu : roundedOrbitEntrance A ρ h₀ a ≤ u) :
    roundedOrbit A ρ h₀ u ≤ a := by
  have haSpec :=
    roundedOrbitEntrance_spec_of_subcritical hA hA_lt hρ hh₀ ha
  exact roundedOrbit_le_of_entrance_le
    ⟨roundedOrbitEntrance A ρ h₀ a, haSpec⟩
    (roundedOrbit_antitone hA hA_lt hρ hh₀) hu

/-- The nonnegative local radius window used to linearize around a deterministic
orbit point. -/
def roundedOrbitWindow (δ a h : ℝ) : Set ℝ :=
  {u : ℝ | 0 ≤ u ∧ |u - h| ≤ δ * (h + a)}

/-- The supremum of the rounded-map derivative on the local orbit window. -/
noncomputable def roundedLocalDerivativeSup (A ρ δ a h : ℝ) : ℝ :=
  sSup (deriv (roundedMeanMap A ρ) '' roundedOrbitWindow δ a h)

/-- The normalized one-step radius ratio from the paper. -/
noncomputable def roundedBeta (A ρ a h : ℝ) : ℝ :=
  (h + a) / (roundedMeanMap A ρ h + a)

/-- The normalized one-step amplification factor from the paper. -/
noncomputable def roundedAlpha (A ρ δ a h : ℝ) : ℝ :=
  roundedLocalDerivativeSup A ρ δ a h * roundedBeta A ρ a h

/-- The product of truncated one-step amplification factors over `[s,t)`. -/
noncomputable def roundedAmplificationProduct
    (A ρ δ a h₀ : ℝ) (s t : ℕ) : ℝ :=
  ∏ u ∈ Finset.Ico s t,
    max 1 (roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))

/-- The full two-term normalized amplification expression from
`eq:subcritical-global-amplification`. -/
noncomputable def roundedAmplificationCombination
    (A ρ δ a h₀ : ℝ) (s t : ℕ) : ℝ :=
  roundedAmplificationProduct A ρ δ a h₀ s t +
    roundedBeta A ρ a (roundedOrbit A ρ h₀ s) *
      roundedAmplificationProduct A ρ δ a h₀ (s + 1) t

/-- Unfolding the full normalized amplification expression. -/
lemma roundedAmplificationCombination_eq
    (A ρ δ a h₀ : ℝ) (s t : ℕ) :
    roundedAmplificationCombination A ρ δ a h₀ s t =
      roundedAmplificationProduct A ρ δ a h₀ s t +
        roundedBeta A ρ a (roundedOrbit A ρ h₀ s) *
          roundedAmplificationProduct A ρ δ a h₀ (s + 1) t :=
  rfl

/-- Clamp a proposed cut time `τ` to the natural interval `[s,t]`. -/
def natIntervalCut (s t τ : ℕ) : ℕ :=
  max s (min t τ)

/-- A clamped cut belongs to its interval when the interval is ordered. -/
lemma natIntervalCut_mem_Icc {s t τ : ℕ} (hst : s ≤ t) :
    natIntervalCut s t τ ∈ Set.Icc s t := by
  simp only [natIntervalCut, Set.mem_Icc]
  omega

/-- Clamping to a fixed interval is monotone in the proposed cut time. -/
lemma natIntervalCut_mono {s t τ₁ τ₂ : ℕ} (hτ : τ₁ ≤ τ₂) :
    natIntervalCut s t τ₁ ≤ natIntervalCut s t τ₂ := by
  simp only [natIntervalCut]
  omega

/-- Every index before a clamped cut is before the original cut time. -/
lemma lt_of_mem_Ico_natIntervalCut {s t τ u : ℕ}
    (hu : u ∈ Finset.Ico s (natIntervalCut s t τ)) :
    u < τ := by
  simp only [Finset.mem_Ico, natIntervalCut] at hu
  omega

/-- Every index after a clamped cut is after the original cut time. -/
lemma le_of_mem_Ico_natIntervalCut {s t τ u : ℕ}
    (hu : u ∈ Finset.Ico (natIntervalCut s t τ) t) :
    τ ≤ u := by
  simp only [Finset.mem_Ico, natIntervalCut] at hu
  omega

/-- Between two ordered clamped cuts, indices lie between the original cut
times. -/
lemma mem_Ico_of_mem_between_natIntervalCuts {s t τ₁ τ₂ u : ℕ}
    (hτ : τ₁ ≤ τ₂)
    (hu : u ∈ Finset.Ico
      (natIntervalCut s t τ₁) (natIntervalCut s t τ₂)) :
    u ∈ Finset.Ico τ₁ τ₂ := by
  simp only [Finset.mem_Ico, natIntervalCut] at hu ⊢
  omega

/-- An amplification product over an empty or reversed interval is one. -/
lemma roundedAmplificationProduct_eq_one_of_le
    (A ρ δ a h₀ : ℝ) {s t : ℕ} (hts : t ≤ s) :
    roundedAmplificationProduct A ρ δ a h₀ s t = 1 := by
  rw [roundedAmplificationProduct,
    Finset.Ico_eq_empty (not_lt.mpr hts)]
  simp

/-- Every truncated amplification product is at least one. -/
lemma one_le_roundedAmplificationProduct
    (A ρ δ a h₀ : ℝ) (s t : ℕ) :
    1 ≤ roundedAmplificationProduct A ρ δ a h₀ s t := by
  rw [roundedAmplificationProduct]
  apply Finset.one_le_prod
  intro u hu
  exact le_max_left _ _

/-- Extending the right endpoint appends the corresponding one-step factor. -/
lemma roundedAmplificationProduct_succ
    (A ρ δ a h₀ : ℝ) {s t : ℕ} (hst : s ≤ t) :
    roundedAmplificationProduct A ρ δ a h₀ s (t + 1) =
      roundedAmplificationProduct A ρ δ a h₀ s t *
        max 1 (roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ t)) := by
  rw [roundedAmplificationProduct, roundedAmplificationProduct,
    Finset.prod_Ico_succ_top hst]

/-- Amplification products split multiplicatively across consecutive
intervals. -/
lemma roundedAmplificationProduct_consecutive
    (A ρ δ a h₀ : ℝ) {s m t : ℕ} (hsm : s ≤ m) (hmt : m ≤ t) :
    roundedAmplificationProduct A ρ δ a h₀ s t =
      roundedAmplificationProduct A ρ δ a h₀ s m *
        roundedAmplificationProduct A ρ δ a h₀ m t := by
  unfold roundedAmplificationProduct
  exact (Finset.prod_Ico_consecutive
    (fun u : ℕ =>
      max 1 (roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u))) hsm hmt).symm

/-- Ordered clamped cuts split an amplification product into prefix, middle,
and suffix factors. -/
lemma roundedAmplificationProduct_three_clamped
    (A ρ δ a h₀ : ℝ) {s t τ₁ τ₂ : ℕ}
    (hst : s ≤ t) (hτ : τ₁ ≤ τ₂) :
    roundedAmplificationProduct A ρ δ a h₀ s t =
      roundedAmplificationProduct A ρ δ a h₀ s
          (natIntervalCut s t τ₁) *
        roundedAmplificationProduct A ρ δ a h₀
          (natIntervalCut s t τ₁) (natIntervalCut s t τ₂) *
        roundedAmplificationProduct A ρ δ a h₀
          (natIntervalCut s t τ₂) t := by
  have hcut₁ := natIntervalCut_mem_Icc (τ := τ₁) hst
  have hcut₂ := natIntervalCut_mem_Icc (τ := τ₂) hst
  rw [roundedAmplificationProduct_consecutive A ρ δ a h₀ hcut₁.1 hcut₁.2,
    roundedAmplificationProduct_consecutive A ρ δ a h₀
      (natIntervalCut_mono hτ) hcut₂.2]
  ring

/-- A uniform one-step bound controls the full finite amplification product. -/
lemma roundedAmplificationProduct_le_pow
    {A ρ δ a h₀ M : ℝ} {s t : ℕ} (hM : 1 ≤ M)
    (hα : ∀ u ∈ Finset.Ico s t,
      roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u) ≤ M) :
    roundedAmplificationProduct A ρ δ a h₀ s t ≤ M ^ (t - s) := by
  rw [roundedAmplificationProduct]
  calc
    ∏ u ∈ Finset.Ico s t,
        max 1 (roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u)) ≤
        ∏ _u ∈ Finset.Ico s t, M :=
      Finset.prod_le_prod
        (fun _ _ => le_trans zero_le_one (le_max_left _ _))
        (fun u hu => max_le hM (hα u hu))
    _ = M ^ (t - s) := by
      rw [Finset.prod_const, Nat.card_Ico]

/-- A power with both exponent and base-log controlled linearly by `ℓ` is
bounded by an exponential quadratic in `ℓ`. -/
lemma pow_le_exp_mul_sq_of_natCast_le_of_log_le
    {M D E ℓ : ℝ} {n : ℕ}
    (hM : 1 ≤ M) (hD : 0 ≤ D) (hℓ : 0 ≤ ℓ)
    (hn : (n : ℝ) ≤ D * ℓ) (hlog : Real.log M ≤ E * ℓ) :
    M ^ n ≤ Real.exp (D * E * ℓ ^ 2) := by
  rw [← Real.log_le_iff_le_exp (pow_pos (zero_lt_one.trans_le hM) n),
    Real.log_pow]
  calc
    (n : ℝ) * Real.log M ≤ (D * ℓ) * (E * ℓ) :=
      mul_le_mul hn hlog (Real.log_nonneg hM)
        (mul_nonneg hD hℓ)
    _ = D * E * ℓ ^ 2 := by ring

/-- If every one-step amplification is nonexpansive, the truncated product is
exactly one. -/
lemma roundedAmplificationProduct_eq_one_of_alpha_le_one
    {A ρ δ a h₀ : ℝ} {s t : ℕ}
    (hα : ∀ u ∈ Finset.Ico s t,
      roundedAlpha A ρ δ a (roundedOrbit A ρ h₀ u) ≤ 1) :
    roundedAmplificationProduct A ρ δ a h₀ s t = 1 := by
  rw [roundedAmplificationProduct]
  apply Finset.prod_eq_one
  intro u hu
  exact max_eq_left (hα u hu)

/-- Membership in the local orbit window is the paper's pair of inequalities. -/
lemma mem_roundedOrbitWindow_iff {δ a h u : ℝ} :
    u ∈ roundedOrbitWindow δ a h ↔
      0 ≤ u ∧ |u - h| ≤ δ * (h + a) :=
  Iff.rfl

/-- A point in the local orbit window lies above its explicit lower endpoint. -/
lemma roundedOrbitWindow_lower {δ a h u : ℝ}
    (hu : u ∈ roundedOrbitWindow δ a h) :
    h - δ * (h + a) ≤ u := by
  have habs := (abs_le.mp hu.2).1
  linarith

/-- A point in the local orbit window lies below its explicit upper endpoint. -/
lemma roundedOrbitWindow_upper {δ a h u : ℝ}
    (hu : u ∈ roundedOrbitWindow δ a h) :
    u ≤ h + δ * (h + a) := by
  have habs := (abs_le.mp hu.2).2
  linarith

/-- In the tail regime `a ≤ h`, the local window is contained in the
paper's multiplicative comparison interval around `h`. -/
lemma roundedOrbitWindow_subset_tail_comparison {δ a h : ℝ}
    (hah : a ≤ h) (hδ : 0 ≤ δ) :
    roundedOrbitWindow δ a h ⊆
      Set.Icc ((1 - 2 * δ) * h) ((1 + 2 * δ) * h) := by
  intro u hu
  have hδah : δ * (h + a) ≤ 2 * δ * h := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hah)]
  constructor
  · nlinarith [roundedOrbitWindow_lower hu]
  · nlinarith [roundedOrbitWindow_upper hu]

/-- A tail-regime local window remains inside the small-radius interval on
which the paper's derivative estimate applies. -/
lemma roundedOrbitWindow_subset_tail_radius {δ a h r : ℝ}
    (ha : 0 ≤ a) (hah : a ≤ h) (hhr : h ≤ r)
    (hδ : 0 ≤ δ) (hδ_quarter : δ ≤ 1 / 4) :
    roundedOrbitWindow δ a h ⊆ Set.Icc 0 (2 * r) := by
  intro u hu
  have hcomparison :=
    roundedOrbitWindow_subset_tail_comparison hah hδ hu
  have hh : 0 ≤ h := ha.trans hah
  have hfactor : 1 + 2 * δ ≤ 3 / 2 := by linarith
  have hupper : (1 + 2 * δ) * h ≤ (3 / 2) * h :=
    mul_le_mul_of_nonneg_right hfactor hh
  constructor
  · exact hu.1
  · linarith [hcomparison.2]

/-- Once the orbit is below the terminal scale, its local window remains in
twice that scale. -/
lemma roundedOrbitWindow_subset_terminal_radius {δ a h : ℝ}
    (hh : 0 ≤ h) (hha : h ≤ a) (hδ_quarter : δ ≤ 1 / 4) :
    roundedOrbitWindow δ a h ⊆ Set.Icc 0 (2 * a) := by
  intro u hu
  have hsum : h + a ≤ 2 * a := by linarith
  have hproduct : δ * (h + a) ≤ (1 / 4) * (2 * a) :=
    mul_le_mul hδ_quarter hsum (by linarith) (by norm_num)
  constructor
  · exact hu.1
  · linarith [roundedOrbitWindow_upper hu]

/-- On the pre-terminal tail, the normalized radius ratio grows at most like
the reciprocal terminal scale. -/
lemma roundedBeta_le_two_mul_div {A ρ a h r : ℝ}
    (ha : 0 < a) (hah : a ≤ h) (hhr : h ≤ r) :
    roundedBeta A ρ a h ≤ 2 * r / a := by
  have hnum : 0 ≤ h + a := by linarith
  have hdenom : a ≤ roundedMeanMap A ρ h + a := by
    linarith [roundedMeanMap_nonneg A ρ h]
  rw [roundedBeta]
  calc
    (h + a) / (roundedMeanMap A ρ h + a) ≤ (h + a) / a :=
      div_le_div_of_nonneg_left hnum ha hdenom
    _ ≤ 2 * r / a := (div_le_div_iff_of_pos_right ha).mpr (by linarith)

/-- In the terminal regime, the normalized radius ratio is at most two. -/
lemma roundedBeta_le_two_of_le_scale {A ρ a h : ℝ}
    (ha : 0 < a) (hh : 0 ≤ h) (hha : h ≤ a) :
    roundedBeta A ρ a h ≤ 2 := by
  have hnum : 0 ≤ h + a := by linarith
  have hdenom : a ≤ roundedMeanMap A ρ h + a := by
    linarith [roundedMeanMap_nonneg A ρ h]
  rw [roundedBeta]
  calc
    (h + a) / (roundedMeanMap A ρ h + a) ≤ (h + a) / a :=
      div_le_div_of_nonneg_left hnum ha hdenom
    _ ≤ 2 := (div_le_iff₀ ha).mpr (by linarith)

/-- The center belongs to its local orbit window when the parameters are
nonnegative. -/
lemma mem_roundedOrbitWindow_self {δ a h : ℝ}
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    h ∈ roundedOrbitWindow δ a h := by
  refine ⟨hh, ?_⟩
  rw [sub_self, abs_zero]
  positivity

/-- The local orbit window is contained in its explicit nonnegative bounding
interval. -/
lemma roundedOrbitWindow_subset_Icc {δ a h : ℝ} :
    roundedOrbitWindow δ a h ⊆ Set.Icc 0 (h + δ * (h + a)) := by
  intro u hu
  exact ⟨hu.1, roundedOrbitWindow_upper hu⟩

/-- In the paper's compact orbit regime, the local window stays in a fixed
positive compact interval. -/
lemma roundedOrbitWindow_subset_compact_regime {δ a h r C₀ : ℝ}
    (hr : 0 < r) (hrh : r ≤ h) (hhC₀ : h ≤ C₀)
    (ha : 0 ≤ a) (har : a ≤ r) (hδ_quarter : δ ≤ 1 / 4) :
    roundedOrbitWindow δ a h ⊆ Set.Icc (r / 2) (2 * C₀) := by
  intro u hu
  have hha : h + a ≤ 2 * h := by linarith
  have hproduct : δ * (h + a) ≤ (1 / 4) * (2 * h) :=
    mul_le_mul hδ_quarter hha (by linarith) (by norm_num)
  constructor
  · have hlower := roundedOrbitWindow_lower hu
    linarith
  · have hupper := roundedOrbitWindow_upper hu
    linarith

/-- The local orbit window is closed. -/
lemma isClosed_roundedOrbitWindow (δ a h : ℝ) :
    IsClosed (roundedOrbitWindow δ a h) := by
  rw [roundedOrbitWindow]
  exact isClosed_le continuous_const continuous_id |>.inter
    (isClosed_le (continuous_abs.comp (continuous_id.sub continuous_const))
      continuous_const)

/-- The local orbit window is bounded. -/
lemma isBounded_roundedOrbitWindow (δ a h : ℝ) :
    Bornology.IsBounded (roundedOrbitWindow δ a h) :=
  (Metric.isBounded_Icc 0 (h + δ * (h + a))).subset
    (roundedOrbitWindow_subset_Icc (δ := δ) (a := a) (h := h))

/-- The local orbit window is compact. -/
lemma isCompact_roundedOrbitWindow (δ a h : ℝ) :
    IsCompact (roundedOrbitWindow δ a h) :=
  Metric.isCompact_of_isClosed_isBounded
    (isClosed_roundedOrbitWindow δ a h) (isBounded_roundedOrbitWindow δ a h)

/-- Pointwise derivative control on a nonempty local orbit window controls the
paper's local derivative supremum. -/
lemma roundedLocalDerivativeSup_le_of_deriv_le {A ρ δ a h L : ℝ}
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hderiv : ∀ u ∈ roundedOrbitWindow δ a h,
      deriv (roundedMeanMap A ρ) u ≤ L) :
    roundedLocalDerivativeSup A ρ δ a h ≤ L := by
  rw [roundedLocalDerivativeSup]
  apply csSup_le
  · exact ⟨deriv (roundedMeanMap A ρ) h, h,
      mem_roundedOrbitWindow_self hδ ha hh, rfl⟩
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact hderiv u hu

/-- A derivative bound on the paper's fixed compact interval controls every
compact-regime local derivative supremum. -/
lemma roundedLocalDerivativeSup_le_compact_bound {A ρ δ a h r C₀ L : ℝ}
    (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hr : 0 < r) (hrh : r ≤ h) (hhC₀ : h ≤ C₀)
    (har : a ≤ r) (hδ_quarter : δ ≤ 1 / 4)
    (hderiv : ∀ u ∈ Set.Icc (r / 2) (2 * C₀),
      deriv (roundedMeanMap A ρ) u ≤ L) :
    roundedLocalDerivativeSup A ρ δ a h ≤ L := by
  apply roundedLocalDerivativeSup_le_of_deriv_le hδ ha hh
  intro u hu
  exact hderiv u
    (roundedOrbitWindow_subset_compact_regime
      hr hrh hhC₀ ha har hδ_quarter hu)

/-- The local derivative supremum is uniformly bounded while the orbit lies
between the terminal scale and a sufficiently small fixed radius. -/
lemma exists_tail_roundedLocalDerivativeSup_bound {A ρ r : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hr_half : r < 1 / 2) :
    ∃ L : ℝ, 0 < L ∧
      ∀ h a δ : ℝ, 0 ≤ a → a ≤ h → h ≤ r →
        0 ≤ δ → δ ≤ 1 / 4 →
        roundedLocalDerivativeSup A ρ δ a h ≤ L := by
  obtain ⟨c, C, hc, hC, hsmall⟩ :=
    exists_roundedMeanMap_small_radius_bounds hA hρ hρ_lt
      (r := 2 * r) (by positivity) (by linarith)
  obtain ⟨D, hD, hDbound⟩ :=
    exists_pos_inv_sq_mul_expNegInvGlue_bound c r
  let L := max 1 ((C / c ^ 2) * D)
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨L, hL, ?_⟩
  intro h a δ ha hah hhr hδ hδ_quarter
  apply roundedLocalDerivativeSup_le_of_deriv_le hδ ha (ha.trans hah)
  intro u hu
  have huIcc :=
    roundedOrbitWindow_subset_tail_radius ha hah hhr hδ hδ_quarter hu
  by_cases hu0 : u = 0
  · rw [hu0, deriv_roundedMeanMap_zero hA hρ hρ_lt]
    exact hL.le
  · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    calc
      deriv (roundedMeanMap A ρ) u ≤
          C * u ^ (-2 : ℝ) * Real.exp (-c / u) :=
        (hsmall u hupos huIcc.2).2
      _ = (C / c ^ 2) *
          (((fun x : ℝ =>
              (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
            fun v : ℝ => v / c) u) :=
        mul_rpow_neg_two_exp_eq_rescaled_glue hc hupos
      _ ≤ (C / c ^ 2) * D :=
        mul_le_mul_of_nonneg_left (hDbound u huIcc)
          (div_nonneg hC.le (sq_nonneg c))
      _ ≤ L := le_max_right _ _

/-- At sufficiently small terminal scales, the local derivative supremum is at
most one half. -/
lemma exists_terminal_roundedLocalDerivativeSup_le_half {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ h a δ : ℝ, 0 < a → a ≤ a₀ → 0 ≤ h → h ≤ a →
        0 ≤ δ → δ ≤ 1 / 4 →
        roundedLocalDerivativeSup A ρ δ a h ≤ 1 / 2 := by
  obtain ⟨c, C, hc, hC, hsmall⟩ :=
    exists_roundedMeanMap_small_radius_bounds hA hρ hρ_lt
      (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hε : 0 < c ^ 2 / (2 * C) := by positivity
  obtain ⟨a₁, ha₁, henvelope⟩ :=
    exists_scale_inv_sq_mul_expNegInvGlue_le (c := c) hε
  let a₀ := min (1 / 4 : ℝ) a₁
  have ha₀ : 0 < a₀ := lt_min (by norm_num) ha₁
  refine ⟨a₀, ha₀, ?_⟩
  intro h a δ ha haa₀ hh hha hδ hδ_quarter
  have haa₁ : a ≤ a₁ := haa₀.trans (min_le_right _ _)
  apply roundedLocalDerivativeSup_le_of_deriv_le hδ ha.le hh
  intro u hu
  have huIcc :=
    roundedOrbitWindow_subset_terminal_radius hh hha hδ_quarter hu
  have hu_half : u ≤ 1 / 2 := by
    have haaquarter : a ≤ 1 / 4 := haa₀.trans (min_le_left _ _)
    linarith [huIcc.2]
  by_cases hu0 : u = 0
  · rw [hu0, deriv_roundedMeanMap_zero hA hρ hρ_lt]
    norm_num
  · have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    calc
      deriv (roundedMeanMap A ρ) u ≤
          C * u ^ (-2 : ℝ) * Real.exp (-c / u) :=
        (hsmall u hupos hu_half).2
      _ = (C / c ^ 2) *
          (((fun x : ℝ =>
              (Polynomial.X ^ 2).eval x⁻¹ * expNegInvGlue x) ∘
            fun v : ℝ => v / c) u) :=
        mul_rpow_neg_two_exp_eq_rescaled_glue hc hupos
      _ ≤ (C / c ^ 2) * (c ^ 2 / (2 * C)) :=
        mul_le_mul_of_nonneg_left
          (henvelope a ha.le haa₁ u huIcc)
          (div_nonneg hC.le (sq_nonneg c))
      _ = 1 / 2 := by field_simp [hc.ne', hC.ne']

/-- At sufficiently small terminal scales, the radius ratio is bounded by two
and the normalized amplification factor is at most one. -/
lemma exists_terminal_regime_normalized_bounds {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ h a δ : ℝ, 0 < a → a ≤ a₀ → 0 ≤ h → h ≤ a →
        0 ≤ δ → δ ≤ 1 / 4 →
        roundedBeta A ρ a h ≤ 2 ∧ roundedAlpha A ρ δ a h ≤ 1 := by
  obtain ⟨a₀, ha₀, hlocal⟩ :=
    exists_terminal_roundedLocalDerivativeSup_le_half hA hρ hρ_lt
  refine ⟨a₀, ha₀, ?_⟩
  intro h a δ ha haa₀ hh hha hδ hδ_quarter
  have hbeta := roundedBeta_le_two_of_le_scale (A := A) (ρ := ρ) ha hh hha
  have hbeta_nonneg : 0 ≤ roundedBeta A ρ a h := by
    rw [roundedBeta]
    exact div_nonneg (by linarith)
      (by linarith [roundedMeanMap_nonneg A ρ h])
  refine ⟨hbeta, ?_⟩
  rw [roundedAlpha]
  calc
    roundedLocalDerivativeSup A ρ δ a h * roundedBeta A ρ a h ≤
        (1 / 2 : ℝ) * 2 :=
      mul_le_mul
        (hlocal h a δ ha haa₀ hh hha hδ hδ_quarter)
        hbeta hbeta_nonneg (by norm_num)
    _ = 1 := by norm_num

/-- For every sufficiently large dimension, normalized amplification is
nonexpansive throughout the terminal orbit regime. -/
lemma exists_eventually_terminal_regime_normalized_bounds {A ρ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h δ : ℝ, 0 ≤ h → h ≤ fixedPrecisionScale N →
        0 ≤ δ → δ ≤ 1 / 4 →
        roundedBeta A ρ (fixedPrecisionScale N) h ≤ 2 ∧
          roundedAlpha A ρ δ (fixedPrecisionScale N) h ≤ 1 := by
  obtain ⟨a₀, ha₀, hterminal⟩ :=
    exists_terminal_regime_normalized_bounds hA hρ hρ_lt
  obtain ⟨N₀, hN₀⟩ :=
    exists_eventually_fixedPrecisionScale_bounds ha₀
  refine ⟨N₀, ?_⟩
  intro N hN h δ hh hhscale hδ hδ_quarter
  obtain ⟨_, hscale, hscalea₀⟩ := hN₀ N hN
  exact hterminal h (fixedPrecisionScale N) δ hscale hscalea₀
    hh hhscale hδ hδ_quarter

/-- For sufficiently large dimensions, every amplification product supported
inside the terminal orbit regime is exactly one. -/
lemma exists_eventually_terminal_amplificationProduct_eq_one
    {A ρ h₀ : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ,
          (∀ u ∈ Finset.Ico s t,
            roundedOrbit A ρ h₀ u ≤ fixedPrecisionScale N) →
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t = 1 := by
  obtain ⟨N₀, hterminal⟩ :=
    exists_eventually_terminal_regime_normalized_bounds hA hρ hρ_lt
  refine ⟨N₀, ?_⟩
  intro N hN δ hδ hδ_quarter s t horbit
  apply roundedAmplificationProduct_eq_one_of_alpha_le_one
  intro u hu
  exact (hterminal N hN (roundedOrbit A ρ h₀ u) δ
    (roundedOrbit_nonneg hh₀ u) (horbit u hu) hδ hδ_quarter).2

/-- The clamped suffix beginning at the terminal entrance has amplification
product exactly one in every sufficiently large dimension. -/
lemma exists_eventually_terminal_suffix_amplificationProduct_eq_one
    {A ρ h₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hh₀ : 0 ≤ h₀) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ,
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀
            (natIntervalCut s t
              (roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N))) t = 1 := by
  obtain ⟨Nterm, hterm⟩ :=
    exists_eventually_terminal_amplificationProduct_eq_one
      hA hρ hρ_lt hh₀
  obtain ⟨Nscale, hscale⟩ :=
    exists_eventually_fixedPrecisionScale_bounds (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max Nterm Nscale, ?_⟩
  intro N hN δ hδ hδ_quarter s t
  have hNterm : Nterm ≤ N := (le_max_left Nterm Nscale).trans hN
  have hNscale : Nscale ≤ N := (le_max_right Nterm Nscale).trans hN
  obtain ⟨_, hscalePos, _⟩ := hscale N hNscale
  apply hterm N hNterm δ hδ hδ_quarter
  intro u hu
  apply roundedOrbit_mem_terminal_after_entrance
    hA hA_lt hρ hh₀ hscalePos
  exact le_of_mem_Ico_natIntervalCut hu

/-- Throughout the pre-terminal tail, both normalized factors grow at most
like the reciprocal terminal scale. -/
lemma exists_tail_regime_normalized_bounds {A ρ r : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hr_half : r < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ h a δ : ℝ, 0 < a → a ≤ h → h ≤ r →
        0 ≤ δ → δ ≤ 1 / 4 →
        roundedBeta A ρ a h ≤ K / a ∧
          roundedAlpha A ρ δ a h ≤ K / a := by
  obtain ⟨L, hL, hlocal⟩ :=
    exists_tail_roundedLocalDerivativeSup_bound hA hρ hρ_lt hr hr_half
  let K := max 1 (max (2 * r) (L * (2 * r)))
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro h a δ ha hah hhr hδ hδ_quarter
  have hbeta := roundedBeta_le_two_mul_div (A := A) (ρ := ρ) ha hah hhr
  have hbeta_nonneg : 0 ≤ roundedBeta A ρ a h := by
    rw [roundedBeta]
    exact div_nonneg (by linarith)
      (by linarith [roundedMeanMap_nonneg A ρ h])
  have htwo : 2 * r ≤ K :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hLtwo : L * (2 * r) ≤ K :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  constructor
  · exact hbeta.trans ((div_le_div_iff_of_pos_right ha).mpr htwo)
  · rw [roundedAlpha]
    calc
      roundedLocalDerivativeSup A ρ δ a h * roundedBeta A ρ a h ≤
          L * (2 * r / a) :=
        mul_le_mul
          (hlocal h a δ ha.le hah hhr hδ hδ_quarter)
          hbeta hbeta_nonneg hL.le
      _ = (L * (2 * r)) / a := by ring
      _ ≤ K / a := (div_le_div_iff_of_pos_right ha).mpr hLtwo

/-- For every sufficiently large dimension, both normalized factors on the
pre-terminal tail are bounded by a constant times `a_N⁻¹`. -/
lemma exists_eventually_tail_regime_normalized_bounds {A ρ r : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hr_half : r < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h δ : ℝ, fixedPrecisionScale N ≤ h → h ≤ r →
        0 ≤ δ → δ ≤ 1 / 4 →
        roundedBeta A ρ (fixedPrecisionScale N) h ≤
            K / fixedPrecisionScale N ∧
          roundedAlpha A ρ δ (fixedPrecisionScale N) h ≤
            K / fixedPrecisionScale N := by
  obtain ⟨K, hK, htail⟩ :=
    exists_tail_regime_normalized_bounds hA hρ hρ_lt hr hr_half
  obtain ⟨N₀, hN₀⟩ :=
    exists_eventually_fixedPrecisionScale_bounds hr
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN h δ hscaleh hhr hδ hδ_quarter
  obtain ⟨_, hscale, _⟩ := hN₀ N hN
  exact htail h (fixedPrecisionScale N) δ hscale hscaleh hhr
    hδ hδ_quarter

/-- Paper-shaped form of the pre-terminal tail estimate, with amplification
bounded by a constant times `log N`. -/
lemma exists_eventually_tail_regime_normalized_bounds_log {A ρ r : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hr_half : r < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h δ : ℝ, fixedPrecisionScale N ≤ h → h ≤ r →
        0 ≤ δ → δ ≤ 1 / 4 →
        roundedBeta A ρ (fixedPrecisionScale N) h ≤ K * Real.log N ∧
          roundedAlpha A ρ δ (fixedPrecisionScale N) h ≤ K * Real.log N := by
  obtain ⟨K, hK, N₀, htail⟩ :=
    exists_eventually_tail_regime_normalized_bounds
      hA hρ hρ_lt hr hr_half
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN h δ hscaleh hhr hδ hδ_quarter
  simpa only [div_fixedPrecisionScale] using
    htail N hN h δ hscaleh hhr hδ hδ_quarter

/-- A pre-terminal tail segment contributes at most one `K log N` factor per
time step to the truncated amplification product. -/
lemma exists_eventually_tail_amplificationProduct_le_pow {A ρ h₀ r : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hr_half : r < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ,
          (∀ u ∈ Finset.Ico s t,
            fixedPrecisionScale N ≤ roundedOrbit A ρ h₀ u ∧
              roundedOrbit A ρ h₀ u ≤ r) →
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t ≤
            (max 1 (K * Real.log N)) ^ (t - s) := by
  obtain ⟨K, hK, N₀, htail⟩ :=
    exists_eventually_tail_regime_normalized_bounds_log
      hA hρ hρ_lt hr hr_half
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN δ hδ hδ_quarter s t horbit
  apply roundedAmplificationProduct_le_pow (le_max_left _ _)
  intro u hu
  exact (htail N hN (roundedOrbit A ρ h₀ u) δ
    (horbit u hu).1 (horbit u hu).2 hδ hδ_quarter).2.trans
      (le_max_right _ _)

/-- The amplification product across any pre-terminal tail segment has the
paper's quadratic-logarithmic exponential bound. -/
lemma exists_eventually_tail_amplificationProduct_le_exp_sq
    {A ρ h₀ C₀ r : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ,
          (∀ u ∈ Finset.Ico s t,
            fixedPrecisionScale N ≤ roundedOrbit A ρ h₀ u ∧
              roundedOrbit A ρ h₀ u ≤ r) →
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t ≤
            Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨K, hK, Ntail, htail⟩ :=
    exists_eventually_tail_amplificationProduct_le_pow
      hA hρ hρ_lt hr hr_half
  obtain ⟨D, hD, Nlength, hlength⟩ :=
    exists_eventually_subcritical_tail_length_le_mul_log_log
      hA hA_lt hρ hh₀ hh₀C₀ hC₀
  obtain ⟨Nlog, hlog⟩ :=
    exists_eventually_log_max_one_mul_log_eq hK
  obtain ⟨Nell, hell⟩ :=
    exists_eventually_le_log_log_nat (max 1 |Real.log K|)
  let C := (D + 1) * 2
  have hC : 0 < C := mul_pos (by linarith) (by norm_num)
  let N₀ := max Ntail (max Nlength (max Nlog Nell))
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN δ hδ hδ_quarter s t horbit
  have hNtail : Ntail ≤ N :=
    (le_max_left Ntail (max Nlength (max Nlog Nell))).trans hN
  have hNlength : Nlength ≤ N :=
    (le_max_left Nlength (max Nlog Nell)).trans
      ((le_max_right Ntail (max Nlength (max Nlog Nell))).trans hN)
  have hNlog : Nlog ≤ N :=
    (le_max_left Nlog Nell).trans
      ((le_max_right Nlength (max Nlog Nell)).trans
        ((le_max_right Ntail (max Nlength (max Nlog Nell))).trans hN))
  have hNell : Nell ≤ N :=
    (le_max_right Nlog Nell).trans
      ((le_max_right Nlength (max Nlog Nell)).trans
        ((le_max_right Ntail (max Nlength (max Nlog Nell))).trans hN))
  have hprod :=
    htail N hNtail δ hδ hδ_quarter s t horbit
  have hlen :=
    hlength N hNlength s t fun u hu => (horbit u hu).1
  have hlogeq := hlog N hNlog
  have hellN := hell N hNell
  have hell_nonneg : 0 ≤ Real.log (Real.log N) :=
    zero_le_one.trans ((le_max_left 1 |Real.log K|).trans hellN)
  have hlogle :
      Real.log (max 1 (K * Real.log N)) ≤
        2 * Real.log (Real.log N) := by
    rw [hlogeq]
    linarith [le_abs_self (Real.log K),
      (le_max_right 1 |Real.log K|).trans hellN]
  have hpow :=
    pow_le_exp_mul_sq_of_natCast_le_of_log_le
      (le_max_left _ _) (add_nonneg hD.le zero_le_one)
      hell_nonneg hlen hlogle
  exact hprod.trans (by simpa [C] using hpow)

/-- The clamped factor between `τ_r` and `τ_{a_N}` satisfies the quadratic
logarithmic exponential bound. -/
lemma exists_eventually_middle_amplificationProduct_le_exp_sq
    {A ρ h₀ C₀ r : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ,
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀
              (natIntervalCut s t (roundedOrbitEntrance A ρ h₀ r))
              (natIntervalCut s t
                (roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N))) ≤
            Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨C, hC, Ntail, htail⟩ :=
    exists_eventually_tail_amplificationProduct_le_exp_sq
      hA hA_lt hρ hρ_lt hh₀ hh₀C₀ hC₀ hr hr_half
  obtain ⟨Nscale, hscale⟩ :=
    exists_eventually_fixedPrecisionScale_bounds hr
  refine ⟨C, hC, max Ntail Nscale, ?_⟩
  intro N hN δ hδ hδ_quarter s t
  have hNtail : Ntail ≤ N := (le_max_left Ntail Nscale).trans hN
  have hNscale : Nscale ≤ N := (le_max_right Ntail Nscale).trans hN
  obtain ⟨_, hscalePos, hscaler⟩ := hscale N hNscale
  have haSpec :=
    roundedOrbitEntrance_spec_of_subcritical
      hA hA_lt hρ hh₀ hscalePos
  have hentrance :
      roundedOrbitEntrance A ρ h₀ r ≤
        roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N) :=
    roundedOrbitEntrance_mono_radius hscaler
      ⟨roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N), haSpec⟩
  apply htail N hNtail δ hδ hδ_quarter
  intro u hu
  have hubetween :=
    mem_Ico_of_mem_between_natIntervalCuts hentrance hu
  have hubounds :
      roundedOrbitEntrance A ρ h₀ r ≤ u ∧
        u < roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N) := by
    simpa only [Finset.mem_Ico] using hubetween
  have hutail :=
    roundedOrbit_mem_tail_between_entrances
      hA hA_lt hρ hh₀ hr hubounds.1 hubounds.2
  exact ⟨hutail.1.le, hutail.2⟩

/-- The paper's positive map lower bound and local derivative upper bound, uniform
throughout the compact pre-terminal orbit regime. -/
lemma exists_compact_regime_rounded_bounds {A ρ r C₀ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hrC₀ : r ≤ C₀) :
    ∃ m L : ℝ, 0 < m ∧ 0 < L ∧
      ∀ h a δ : ℝ, r ≤ h → h ≤ C₀ → 0 ≤ a → a ≤ r →
        0 ≤ δ → δ ≤ 1 / 4 →
        m ≤ roundedMeanMap A ρ h ∧
          roundedLocalDerivativeSup A ρ δ a h ≤ L := by
  have hrhalf : 0 < r / 2 := by positivity
  have hinterval : r / 2 ≤ 2 * C₀ := by linarith
  obtain ⟨m, L, hm, hL, hbounds⟩ :=
    exists_roundedMeanMap_compact_bounds hA hρ hρ_lt hrhalf hinterval
  refine ⟨m, L, hm, hL, ?_⟩
  intro h a δ hrh hhC₀ ha har hδ hδ_quarter
  have hh : 0 ≤ h := le_trans hr.le hrh
  have hhmem : h ∈ Set.Icc (r / 2) (2 * C₀) := by
    constructor <;> linarith
  exact ⟨(hbounds h hhmem).1,
    roundedLocalDerivativeSup_le_compact_bound hδ ha hh hr hrh hhC₀ har
      hδ_quarter fun u hu => (hbounds u hu).2⟩

/-- Before the orbit enters the small-radius regime, both normalized one-step
factors are bounded by a single positive constant. -/
lemma exists_compact_regime_normalized_bounds {A ρ r C₀ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hrC₀ : r ≤ C₀) :
    ∃ B : ℝ, 0 < B ∧
      ∀ h a δ : ℝ, r ≤ h → h ≤ C₀ → 0 ≤ a → a ≤ r →
        0 ≤ δ → δ ≤ 1 / 4 →
        roundedBeta A ρ a h ≤ B ∧ roundedAlpha A ρ δ a h ≤ B := by
  obtain ⟨m, L, hm, hL, hbounds⟩ :=
    exists_compact_regime_rounded_bounds hA hρ hρ_lt hr hrC₀
  let b := (C₀ + r) / m
  let B := max 1 (max b (L * b))
  refine ⟨B, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro h a δ hrh hhC₀ ha har hδ hδ_quarter
  obtain ⟨hmap, hlocal⟩ :=
    hbounds h a δ hrh hhC₀ ha har hδ hδ_quarter
  have hdenom : 0 < roundedMeanMap A ρ h + a := by linarith
  have hnum : h + a ≤ C₀ + r := by linarith
  have hbeta_nonneg : 0 ≤ roundedBeta A ρ a h := by
    rw [roundedBeta]
    exact div_nonneg (by linarith) hdenom.le
  have hbeta : roundedBeta A ρ a h ≤ b := by
    dsimp [roundedBeta, b]
    rw [le_div_iff₀ hm]
    calc
      (h + a) / (roundedMeanMap A ρ h + a) * m ≤
          (h + a) / (roundedMeanMap A ρ h + a) *
            (roundedMeanMap A ρ h + a) :=
        mul_le_mul_of_nonneg_left (by linarith) hbeta_nonneg
      _ = h + a := div_mul_cancel₀ _ hdenom.ne'
      _ ≤ C₀ + r := hnum
  constructor
  · exact hbeta.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  · rw [roundedAlpha]
    exact (mul_le_mul hlocal hbeta hbeta_nonneg hL.le).trans
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-- Uniformly over all orbit radii below `C₀`, the normalized radius ratio is
eventually bounded by a constant times `log N`. -/
lemma exists_eventually_roundedBeta_le_mul_log
    {A ρ r C₀ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h : ℝ, 0 ≤ h → h ≤ C₀ →
        roundedBeta A ρ (fixedPrecisionScale N) h ≤ K * Real.log N := by
  obtain ⟨B, hB, hcompact⟩ :=
    exists_compact_regime_normalized_bounds hA hρ hρ_lt hr hrC₀
  obtain ⟨K, hK, Ntail, htail⟩ :=
    exists_eventually_tail_regime_normalized_bounds_log
      hA hρ hρ_lt hr hr_half
  obtain ⟨Nscale, hscale⟩ :=
    exists_eventually_fixedPrecisionScale_bounds hr
  obtain ⟨Nlog, hlog⟩ :=
    exists_eventually_one_le_mul_log_nat (show (0 : ℝ) < 1 by norm_num)
  let Kglobal := max B (max K 2)
  have hKglobal : 0 < Kglobal :=
    hB.trans_le (le_max_left _ _)
  let N₀ := max Ntail (max Nscale Nlog)
  refine ⟨Kglobal, hKglobal, N₀, ?_⟩
  intro N hN h hh hhC₀
  have hNtail : Ntail ≤ N :=
    (le_max_left Ntail (max Nscale Nlog)).trans hN
  have hNscale : Nscale ≤ N :=
    (le_max_left Nscale Nlog).trans
      ((le_max_right Ntail (max Nscale Nlog)).trans hN)
  have hNlog : Nlog ≤ N :=
    (le_max_right Nscale Nlog).trans
      ((le_max_right Ntail (max Nscale Nlog)).trans hN)
  obtain ⟨_, hscalePos, hscaler⟩ := hscale N hNscale
  have honeLog : 1 ≤ Real.log N := by
    simpa using hlog N hNlog
  have hglobalLog :
      Kglobal ≤ Kglobal * Real.log N := by
    simpa using mul_le_mul_of_nonneg_left honeLog hKglobal.le
  by_cases hrh : r ≤ h
  · have hbeta :=
      (hcompact h (fixedPrecisionScale N) 0 hrh hhC₀
        hscalePos.le hscaler (by norm_num) (by norm_num)).1
    exact hbeta.trans <| (le_max_left B (max K 2)).trans hglobalLog
  · by_cases hscaleh : fixedPrecisionScale N ≤ h
    · have hbeta :=
        (htail N hNtail h 0 hscaleh (not_le.mp hrh).le
          (by norm_num) (by norm_num)).1
      exact hbeta.trans <|
        mul_le_mul_of_nonneg_right
          (le_trans (le_max_left K 2) (le_max_right B (max K 2)))
          (zero_le_one.trans honeLog)
    · have hbeta :=
        roundedBeta_le_two_of_le_scale (A := A) (ρ := ρ)
          hscalePos hh (not_le.mp hscaleh).le
      exact hbeta.trans <|
        (le_trans (le_max_right K 2) (le_max_right B (max K 2))).trans
          hglobalLog

/-- Uniformly over all orbit radii below `C₀`, the normalized derivative
factor is eventually bounded by a constant times `log N`. -/
lemma exists_eventually_roundedAlpha_le_mul_log
    {A ρ r C₀ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h δ : ℝ, 0 ≤ h → h ≤ C₀ → 0 ≤ δ → δ ≤ 1 / 4 →
        roundedAlpha A ρ δ (fixedPrecisionScale N) h ≤
          K * Real.log N := by
  obtain ⟨B, hB, hcompact⟩ :=
    exists_compact_regime_normalized_bounds hA hρ hρ_lt hr hrC₀
  obtain ⟨K, hK, Ntail, htail⟩ :=
    exists_eventually_tail_regime_normalized_bounds_log
      hA hρ hρ_lt hr hr_half
  obtain ⟨Nterm, hterm⟩ :=
    exists_eventually_terminal_regime_normalized_bounds hA hρ hρ_lt
  obtain ⟨Nscale, hscale⟩ :=
    exists_eventually_fixedPrecisionScale_bounds hr
  obtain ⟨Nlog, hlog⟩ :=
    exists_eventually_one_le_mul_log_nat (show (0 : ℝ) < 1 by norm_num)
  let Kglobal := max B (max K 1)
  have hKglobal : 0 < Kglobal :=
    hB.trans_le (le_max_left _ _)
  let N₀ := max Ntail (max Nterm (max Nscale Nlog))
  refine ⟨Kglobal, hKglobal, N₀, ?_⟩
  intro N hN h δ hh hhC₀ hδ hδ_quarter
  have hNtail : Ntail ≤ N :=
    (le_max_left Ntail (max Nterm (max Nscale Nlog))).trans hN
  have hNterm : Nterm ≤ N :=
    (le_max_left Nterm (max Nscale Nlog)).trans
      ((le_max_right Ntail (max Nterm (max Nscale Nlog))).trans hN)
  have hNscale : Nscale ≤ N :=
    (le_max_left Nscale Nlog).trans
      ((le_max_right Nterm (max Nscale Nlog)).trans
        ((le_max_right Ntail (max Nterm (max Nscale Nlog))).trans hN))
  have hNlog : Nlog ≤ N :=
    (le_max_right Nscale Nlog).trans
      ((le_max_right Nterm (max Nscale Nlog)).trans
        ((le_max_right Ntail (max Nterm (max Nscale Nlog))).trans hN))
  obtain ⟨_, hscalePos, hscaler⟩ := hscale N hNscale
  have honeLog : 1 ≤ Real.log N := by
    simpa using hlog N hNlog
  have hglobalLog :
      Kglobal ≤ Kglobal * Real.log N := by
    simpa using mul_le_mul_of_nonneg_left honeLog hKglobal.le
  by_cases hrh : r ≤ h
  · have halpha :=
      (hcompact h (fixedPrecisionScale N) δ hrh hhC₀
        hscalePos.le hscaler hδ hδ_quarter).2
    exact halpha.trans <| (le_max_left B (max K 1)).trans hglobalLog
  · by_cases hscaleh : fixedPrecisionScale N ≤ h
    · have halpha :=
        (htail N hNtail h δ hscaleh (not_le.mp hrh).le
          hδ hδ_quarter).2
      exact halpha.trans <|
        mul_le_mul_of_nonneg_right
          (le_trans (le_max_left K 1) (le_max_right B (max K 1)))
          (zero_le_one.trans honeLog)
    · have halpha :=
        (hterm N hNterm h δ hh (not_le.mp hscaleh).le
          hδ hδ_quarter).2
      exact halpha.trans <|
        (le_trans (le_max_right K 1) (le_max_right B (max K 1))).trans
          hglobalLog

/-- Amplification products are subpolynomial uniformly over every initial
radius in the compact interval `[0,C₀]`. -/
lemma exists_eventually_uniform_amplificationProduct_le_exp_sq
    {A ρ r C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h₀ : ℝ, 0 ≤ h₀ → h₀ ≤ C₀ →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
          ∀ s t : ℕ, s ≤ t →
            roundedAmplificationProduct A ρ δ
                (fixedPrecisionScale N) h₀ s t ≤
              Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨K, hK, Nalpha, halpha⟩ :=
    exists_eventually_roundedAlpha_le_mul_log
      hA hρ hρ_lt hr hr_half hrC₀
  obtain ⟨D, hD, Nlength, hlength⟩ :=
    exists_eventually_uniform_subcritical_tail_length_le_mul_log_log
      hA hA_lt hρ hC₀
  obtain ⟨Nterm, hterm⟩ :=
    exists_eventually_terminal_regime_normalized_bounds hA hρ hρ_lt
  obtain ⟨Nlog, hlog⟩ :=
    exists_eventually_log_max_one_mul_log_eq hK
  obtain ⟨Nell, hell⟩ :=
    exists_eventually_le_log_log_nat (max 1 |Real.log K|)
  let C := (D + 1) * 2
  have hC : 0 < C := mul_pos (by linarith) (by norm_num)
  let N₀ := max Nalpha (max Nlength (max Nterm (max Nlog (max Nell 2))))
  refine ⟨C, hC, N₀, ?_⟩
  intro N hN h₀ hh₀ hh₀C₀ δ hδ hδ_quarter s t hst
  have hNalpha : Nalpha ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNlength : Nlength ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNterm : Nterm ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNlog : Nlog ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNell : Nell ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNtwo : 2 ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNone : 1 < N := by omega
  let τa := roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N)
  let m := natIntervalCut s t τa
  have hm := natIntervalCut_mem_Icc (τ := τa) hst
  have hsplit :=
    roundedAmplificationProduct_consecutive
      A ρ δ (fixedPrecisionScale N) h₀ hm.1 hm.2
  have hsuffix :
      roundedAmplificationProduct A ρ δ
          (fixedPrecisionScale N) h₀ m t = 1 := by
    apply roundedAmplificationProduct_eq_one_of_alpha_le_one
    intro u hu
    apply (hterm N hNterm (roundedOrbit A ρ h₀ u) δ
      (roundedOrbit_nonneg hh₀ u) ?_ hδ hδ_quarter).2
    apply roundedOrbit_mem_terminal_after_entrance
      hA hA_lt hρ hh₀ (fixedPrecisionScale_pos hNone)
    exact le_of_mem_Ico_natIntervalCut hu
  have hprefix :
      roundedAmplificationProduct A ρ δ
          (fixedPrecisionScale N) h₀ s m ≤
        max 1 (K * Real.log N) ^ (m - s) := by
    apply roundedAmplificationProduct_le_pow (le_max_left _ _)
    intro u hu
    apply (halpha N hNalpha (roundedOrbit A ρ h₀ u) δ
      (roundedOrbit_nonneg hh₀ u) ?_ hδ hδ_quarter).trans
      (le_max_right _ _)
    exact (roundedOrbit_antitone hA hA_lt hρ hh₀ (Nat.zero_le u)).trans
      (by simpa using hh₀C₀)
  have hlen :
      (((m - s : ℕ) : ℝ)) ≤
        (D + 1) * Real.log (Real.log N) := by
    apply hlength N hNlength h₀ hh₀ hh₀C₀ s m
    intro u hu
    exact (roundedOrbit_lt_entrance
      (lt_of_mem_Ico_natIntervalCut hu)).le
  have hlogeq := hlog N hNlog
  have hellN := hell N hNell
  have hell_nonneg : 0 ≤ Real.log (Real.log N) :=
    zero_le_one.trans ((le_max_left 1 |Real.log K|).trans hellN)
  have hlogle :
      Real.log (max 1 (K * Real.log N)) ≤
        2 * Real.log (Real.log N) := by
    rw [hlogeq]
    linarith [le_abs_self (Real.log K),
      (le_max_right 1 |Real.log K|).trans hellN]
  have hpow :=
    pow_le_exp_mul_sq_of_natCast_le_of_log_le
      (le_max_left _ _) (add_nonneg hD.le zero_le_one)
      hell_nonneg hlen hlogle
  calc
    roundedAmplificationProduct A ρ δ
        (fixedPrecisionScale N) h₀ s t =
        roundedAmplificationProduct A ρ δ
            (fixedPrecisionScale N) h₀ s m *
          roundedAmplificationProduct A ρ δ
            (fixedPrecisionScale N) h₀ m t := hsplit
    _ = roundedAmplificationProduct A ρ δ
          (fixedPrecisionScale N) h₀ s m := by rw [hsuffix, mul_one]
    _ ≤ max 1 (K * Real.log N) ^ (m - s) := hprefix
    _ ≤ Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
      simpa [C] using hpow

/-- A single logarithmic prefactor is absorbed by enlarging the quadratic
`log log N` exponent. -/
lemma exists_eventually_one_add_mul_log_mul_exp_le_exp_sq
    {K C : ℝ} (hK : 0 < K) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 + K * Real.log N) *
          Real.exp (C * (Real.log (Real.log N)) ^ 2) ≤
        Real.exp (C' * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨Nfactor, hfactor⟩ :=
    exists_eventually_one_le_mul_log_nat hK
  obtain ⟨Nell, hell⟩ :=
    exists_eventually_le_log_log_nat (max 1 |Real.log (2 * K)|)
  refine ⟨C + 2, by linarith, max Nfactor Nell, ?_⟩
  intro N hN
  have hNfactor : Nfactor ≤ N :=
    (le_max_left Nfactor Nell).trans hN
  have hNell : Nell ≤ N :=
    (le_max_right Nfactor Nell).trans hN
  have hKlog : 1 ≤ K * Real.log N := hfactor N hNfactor
  have hlog : 0 < Real.log N := by
    nlinarith [hK]
  have htwoKlog : 0 < (2 * K) * Real.log N := by positivity
  have hellN := hell N hNell
  have hone : 1 ≤ Real.log (Real.log N) :=
    (le_max_left 1 |Real.log (2 * K)|).trans hellN
  have hlogTwoK : Real.log (2 * K) ≤ Real.log (Real.log N) :=
    (le_abs_self (Real.log (2 * K))).trans
      ((le_max_right 1 |Real.log (2 * K)|).trans hellN)
  calc
    (1 + K * Real.log N) *
        Real.exp (C * (Real.log (Real.log N)) ^ 2) ≤
        ((2 * K) * Real.log N) *
          Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
      gcongr
      linarith
    _ = Real.exp
        (Real.log (2 * K) + Real.log (Real.log N) +
          C * (Real.log (Real.log N)) ^ 2) := by
      rw [← Real.exp_log htwoKlog, Real.log_mul (by positivity) hlog.ne']
      simp only [Real.exp_add]
    _ ≤ Real.exp ((C + 2) * (Real.log (Real.log N)) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (Real.log (Real.log N) - 1)]

/-- A compact pre-terminal orbit segment contributes only a
dimension-independent factor per time step. -/
lemma exists_eventually_compact_amplificationProduct_le_pow
    {A ρ h₀ r C₀ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hr : 0 < r) (hrC₀ : r ≤ C₀) :
    ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ,
          (∀ u ∈ Finset.Ico s t,
            r ≤ roundedOrbit A ρ h₀ u ∧
              roundedOrbit A ρ h₀ u ≤ C₀) →
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t ≤
            (max 1 B) ^ (t - s) := by
  obtain ⟨B, hB, hcompact⟩ :=
    exists_compact_regime_normalized_bounds hA hρ hρ_lt hr hrC₀
  obtain ⟨N₀, hN₀⟩ :=
    exists_eventually_fixedPrecisionScale_bounds hr
  refine ⟨B, hB, N₀, ?_⟩
  intro N hN δ hδ hδ_quarter s t horbit
  obtain ⟨_, hscale, hscaler⟩ := hN₀ N hN
  apply roundedAmplificationProduct_le_pow (le_max_left _ _)
  intro u hu
  exact (hcompact (roundedOrbit A ρ h₀ u) (fixedPrecisionScale N) δ
    (horbit u hu).1 (horbit u hu).2 hscale.le hscaler hδ hδ_quarter).2.trans
      (le_max_right _ _)

/-- The compact-prefix factor cut at `τ_r` is bounded by one
dimension-independent positive constant. -/
lemma exists_eventually_compact_prefix_amplificationProduct_le
    {A ρ h₀ r C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀)
    (hr : 0 < r) (hrC₀ : r ≤ C₀) :
    ∃ Q : ℝ, 0 < Q ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ,
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s
              (natIntervalCut s t (roundedOrbitEntrance A ρ h₀ r)) ≤ Q := by
  obtain ⟨B, hB, N₀, hcompact⟩ :=
    exists_eventually_compact_amplificationProduct_le_pow
      hA hρ hρ_lt hr hrC₀
  let τr := roundedOrbitEntrance A ρ h₀ r
  let Q := (max 1 B) ^ τr
  have hQ : 0 < Q := pow_pos (zero_lt_one.trans_le (le_max_left _ _)) τr
  refine ⟨Q, hQ, N₀, ?_⟩
  intro N hN δ hδ hδ_quarter s t
  have hprod :=
    hcompact N hN δ hδ hδ_quarter s (natIntervalCut s t τr) ?_
  · exact hprod.trans <| pow_le_pow_right₀ (le_max_left _ _) (by
      dsimp [τr, natIntervalCut]
      omega)
  · intro u hu
    have huτ : u < roundedOrbitEntrance A ρ h₀ r := by
      exact lt_of_mem_Ico_natIntervalCut hu
    have horbit :=
      roundedOrbit_mem_compact_before_entrance
        hA hA_lt hρ hh₀ hh₀C₀ huτ
    exact ⟨horbit.1.le, horbit.2⟩

/-- Combining the compact prefix, pre-terminal tail, and terminal suffix gives
the global amplification product bound up to one fixed prefactor. -/
lemma exists_eventually_amplificationProduct_le_mul_exp_sq
    {A ρ h₀ C₀ r : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ Q C : ℝ, 0 < Q ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ, s ≤ t →
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t ≤
            Q * Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨Q, hQ, Npre, hpre⟩ :=
    exists_eventually_compact_prefix_amplificationProduct_le
      hA hA_lt hρ hρ_lt hh₀ hh₀C₀ hr hrC₀
  obtain ⟨C, hC, Nmid, hmid⟩ :=
    exists_eventually_middle_amplificationProduct_le_exp_sq
      hA hA_lt hρ hρ_lt hh₀ hh₀C₀ hC₀ hr hr_half
  obtain ⟨Nsuf, hsuf⟩ :=
    exists_eventually_terminal_suffix_amplificationProduct_eq_one
      hA hA_lt hρ hρ_lt hh₀
  obtain ⟨Nscale, hscale⟩ :=
    exists_eventually_fixedPrecisionScale_bounds hr
  let N₀ := max Npre (max Nmid (max Nsuf Nscale))
  refine ⟨Q, C, hQ, hC, N₀, ?_⟩
  intro N hN δ hδ hδ_quarter s t hst
  have hNpre : Npre ≤ N :=
    (le_max_left Npre (max Nmid (max Nsuf Nscale))).trans hN
  have hNmid : Nmid ≤ N :=
    (le_max_left Nmid (max Nsuf Nscale)).trans
      ((le_max_right Npre (max Nmid (max Nsuf Nscale))).trans hN)
  have hNsuf : Nsuf ≤ N :=
    (le_max_left Nsuf Nscale).trans
      ((le_max_right Nmid (max Nsuf Nscale)).trans
        ((le_max_right Npre (max Nmid (max Nsuf Nscale))).trans hN))
  have hNscale : Nscale ≤ N :=
    (le_max_right Nsuf Nscale).trans
      ((le_max_right Nmid (max Nsuf Nscale)).trans
        ((le_max_right Npre (max Nmid (max Nsuf Nscale))).trans hN))
  obtain ⟨_, hscalePos, hscaler⟩ := hscale N hNscale
  have haSpec :=
    roundedOrbitEntrance_spec_of_subcritical
      hA hA_lt hρ hh₀ hscalePos
  have hentrance :
      roundedOrbitEntrance A ρ h₀ r ≤
        roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N) :=
    roundedOrbitEntrance_mono_radius hscaler
      ⟨roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N), haSpec⟩
  have hsplit :=
    roundedAmplificationProduct_three_clamped
      A ρ δ (fixedPrecisionScale N) h₀ hst hentrance
  have hprefix := hpre N hNpre δ hδ hδ_quarter s t
  have hmiddle := hmid N hNmid δ hδ hδ_quarter s t
  have hsuffix := hsuf N hNsuf δ hδ hδ_quarter s t
  calc
    roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t =
        roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s
            (natIntervalCut s t (roundedOrbitEntrance A ρ h₀ r)) *
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀
            (natIntervalCut s t (roundedOrbitEntrance A ρ h₀ r))
            (natIntervalCut s t
              (roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N))) *
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀
            (natIntervalCut s t
              (roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N))) t :=
      hsplit
    _ = roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s
            (natIntervalCut s t (roundedOrbitEntrance A ρ h₀ r)) *
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀
            (natIntervalCut s t (roundedOrbitEntrance A ρ h₀ r))
            (natIntervalCut s t
              (roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N))) := by
      rw [hsuffix]
      ring
    _ ≤ Q * Real.exp (C * (Real.log (Real.log N)) ^ 2) :=
      mul_le_mul hprefix hmiddle
        (zero_le_one.trans
          (one_le_roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀
            (natIntervalCut s t (roundedOrbitEntrance A ρ h₀ r))
            (natIntervalCut s t
              (roundedOrbitEntrance A ρ h₀ (fixedPrecisionScale N)))))
        hQ.le

/-- The fixed compact-prefix prefactor can be absorbed into the quadratic
logarithmic exponent. -/
lemma exists_eventually_amplificationProduct_le_exp_sq
    {A ρ h₀ C₀ r : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ, s ≤ t →
          roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t ≤
            Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨Q, C, hQ, hC, Nbase, hbase⟩ :=
    exists_eventually_amplificationProduct_le_mul_exp_sq
      hA hA_lt hρ hρ_lt hh₀ hh₀C₀ hC₀ hr hr_half hrC₀
  obtain ⟨Nell, hell⟩ :=
    exists_eventually_le_log_log_nat (max 1 |Real.log Q|)
  refine ⟨C + 1, by linarith, max Nbase Nell, ?_⟩
  intro N hN δ hδ hδ_quarter s t hst
  have hNbase : Nbase ≤ N := (le_max_left Nbase Nell).trans hN
  have hNell : Nell ≤ N := (le_max_right Nbase Nell).trans hN
  have hellN := hell N hNell
  have hlogQ : Real.log Q ≤ Real.log (Real.log N) :=
    (le_abs_self (Real.log Q)).trans
      ((le_max_right 1 |Real.log Q|).trans hellN)
  have hone : 1 ≤ Real.log (Real.log N) :=
    (le_max_left 1 |Real.log Q|).trans hellN
  calc
    roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t ≤
        Q * Real.exp (C * (Real.log (Real.log N)) ^ 2) :=
      hbase N hNbase δ hδ hδ_quarter s t hst
    _ = Real.exp
        (Real.log Q + C * (Real.log (Real.log N)) ^ 2) := by
      calc
        Q * Real.exp (C * (Real.log (Real.log N)) ^ 2) =
            Real.exp (Real.log Q) *
              Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
          rw [Real.exp_log hQ]
        _ = Real.exp
            (Real.log Q + C * (Real.log (Real.log N)) ^ 2) :=
          (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C + 1) * (Real.log (Real.log N)) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (Real.log (Real.log N) - 1)]

/-- The paper's full product-plus-radius-ratio amplification is subpolynomial,
uniformly over every nonempty time interval. -/
lemma exists_eventually_roundedAmplificationCombination_le_exp_sq
    {A ρ h₀ C₀ r : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (hh₀ : 0 ≤ h₀) (hh₀C₀ : h₀ ≤ C₀) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
        ∀ s t : ℕ, s < t →
          roundedAmplificationCombination A ρ δ
              (fixedPrecisionScale N) h₀ s t ≤
            Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨C, hC, Nproduct, hproduct⟩ :=
    exists_eventually_amplificationProduct_le_exp_sq
      hA hA_lt hρ hρ_lt hh₀ hh₀C₀ hC₀ hr hr_half hrC₀
  obtain ⟨K, hK, Nbeta, hbeta⟩ :=
    exists_eventually_roundedBeta_le_mul_log
      hA hρ hρ_lt hr hr_half hrC₀
  obtain ⟨Nscale, hscale⟩ :=
    exists_eventually_fixedPrecisionScale_bounds hr
  obtain ⟨C', hC', Nabsorb, habsorb⟩ :=
    exists_eventually_one_add_mul_log_mul_exp_le_exp_sq hK hC
  let N₀ := max Nproduct (max Nbeta (max Nscale Nabsorb))
  refine ⟨C', hC', N₀, ?_⟩
  intro N hN δ hδ hδ_quarter s t hst
  have hNproduct : Nproduct ≤ N :=
    (le_max_left Nproduct (max Nbeta (max Nscale Nabsorb))).trans hN
  have hNbeta : Nbeta ≤ N :=
    (le_max_left Nbeta (max Nscale Nabsorb)).trans
      ((le_max_right Nproduct (max Nbeta (max Nscale Nabsorb))).trans hN)
  have hNscale : Nscale ≤ N :=
    (le_max_left Nscale Nabsorb).trans
      ((le_max_right Nbeta (max Nscale Nabsorb)).trans
        ((le_max_right Nproduct (max Nbeta (max Nscale Nabsorb))).trans hN))
  have hNabsorb : Nabsorb ≤ N :=
    (le_max_right Nscale Nabsorb).trans
      ((le_max_right Nbeta (max Nscale Nabsorb)).trans
        ((le_max_right Nproduct (max Nbeta (max Nscale Nabsorb))).trans hN))
  obtain ⟨_, hscalePos, _⟩ := hscale N hNscale
  have horbitNonneg : 0 ≤ roundedOrbit A ρ h₀ s :=
    roundedOrbit_nonneg hh₀ s
  have horbitC₀ : roundedOrbit A ρ h₀ s ≤ C₀ := by
    calc
      roundedOrbit A ρ h₀ s ≤ roundedOrbit A ρ h₀ 0 :=
        roundedOrbit_antitone hA hA_lt hρ hh₀ (Nat.zero_le s)
      _ = h₀ := roundedOrbit_zero A ρ h₀
      _ ≤ C₀ := hh₀C₀
  have hbetaBound :=
    hbeta N hNbeta (roundedOrbit A ρ h₀ s) horbitNonneg horbitC₀
  have hbetaNonneg :
      0 ≤ roundedBeta A ρ (fixedPrecisionScale N)
        (roundedOrbit A ρ h₀ s) := by
    rw [roundedBeta]
    exact div_nonneg (by linarith)
      (by linarith [roundedMeanMap_nonneg A ρ (roundedOrbit A ρ h₀ s)])
  have hKlogNonneg : 0 ≤ K * Real.log N :=
    hbetaNonneg.trans hbetaBound
  have hfirst :=
    hproduct N hNproduct δ hδ hδ_quarter s t hst.le
  have hshift :=
    hproduct N hNproduct δ hδ hδ_quarter (s + 1) t hst
  rw [roundedAmplificationCombination_eq]
  calc
    roundedAmplificationProduct A ρ δ (fixedPrecisionScale N) h₀ s t +
        roundedBeta A ρ (fixedPrecisionScale N)
            (roundedOrbit A ρ h₀ s) *
          roundedAmplificationProduct A ρ δ
            (fixedPrecisionScale N) h₀ (s + 1) t ≤
        Real.exp (C * (Real.log (Real.log N)) ^ 2) +
          (K * Real.log N) *
            Real.exp (C * (Real.log (Real.log N)) ^ 2) :=
      add_le_add hfirst <|
        mul_le_mul hbetaBound hshift
          (one_le_roundedAmplificationProduct A ρ δ
            (fixedPrecisionScale N) h₀ (s + 1) t |>.trans' (by norm_num))
          hKlogNonneg
    _ = (1 + K * Real.log N) *
          Real.exp (C * (Real.log (Real.log N)) ^ 2) := by ring
    _ ≤ Real.exp (C' * (Real.log (Real.log N)) ^ 2) :=
      habsorb N hNabsorb

/-- The full product-plus-radius-ratio amplification is uniformly
subpolynomial over every initial radius in `[0,C₀]`. -/
lemma exists_eventually_uniform_roundedAmplificationCombination_le_exp_sq
    {A ρ r C₀ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1) (hC₀ : 0 < C₀)
    (hr : 0 < r) (hr_half : r < 1 / 2) (hrC₀ : r ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ h₀ : ℝ, 0 ≤ h₀ → h₀ ≤ C₀ →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 4 →
          ∀ s t : ℕ, s < t →
            roundedAmplificationCombination A ρ δ
                (fixedPrecisionScale N) h₀ s t ≤
              Real.exp (C * (Real.log (Real.log N)) ^ 2) := by
  obtain ⟨C, hC, Nproduct, hproduct⟩ :=
    exists_eventually_uniform_amplificationProduct_le_exp_sq
      hA hA_lt hρ hρ_lt hC₀ hr hr_half hrC₀
  obtain ⟨K, hK, Nbeta, hbeta⟩ :=
    exists_eventually_roundedBeta_le_mul_log
      hA hρ hρ_lt hr hr_half hrC₀
  obtain ⟨C', hC', Nabsorb, habsorb⟩ :=
    exists_eventually_one_add_mul_log_mul_exp_le_exp_sq hK hC
  let N₀ := max Nproduct (max Nbeta (max Nabsorb 2))
  refine ⟨C', hC', N₀, ?_⟩
  intro N hN h₀ hh₀ hh₀C₀ δ hδ hδ_quarter s t hst
  have hNproduct : Nproduct ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNbeta : Nbeta ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNabsorb : Nabsorb ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNtwo : 2 ≤ N := by
    dsimp [N₀] at hN
    omega
  have hNone : 1 < N := by omega
  have hp₁ :=
    hproduct N hNproduct h₀ hh₀ hh₀C₀ δ hδ hδ_quarter
      s t hst.le
  have hp₂ :=
    hproduct N hNproduct h₀ hh₀ hh₀C₀ δ hδ hδ_quarter
      (s + 1) t (Nat.succ_le_iff.mpr hst)
  have horbitNonneg : 0 ≤ roundedOrbit A ρ h₀ s :=
    roundedOrbit_nonneg hh₀ s
  have horbitC₀ : roundedOrbit A ρ h₀ s ≤ C₀ := by
    calc
      roundedOrbit A ρ h₀ s ≤ roundedOrbit A ρ h₀ 0 :=
        roundedOrbit_antitone hA hA_lt hρ hh₀ (Nat.zero_le s)
      _ = h₀ := roundedOrbit_zero A ρ h₀
      _ ≤ C₀ := hh₀C₀
  have hβ :=
    hbeta N hNbeta (roundedOrbit A ρ h₀ s) horbitNonneg horbitC₀
  have hp₂_nonneg :
      0 ≤ roundedAmplificationProduct A ρ δ
        (fixedPrecisionScale N) h₀ (s + 1) t :=
    Finset.prod_nonneg fun _ _ =>
      le_trans zero_le_one (le_max_left _ _)
  have hKlog_nonneg : 0 ≤ K * Real.log N :=
    mul_nonneg hK.le (Real.log_pos (by exact_mod_cast hNone)).le
  rw [roundedAmplificationCombination_eq]
  calc
    roundedAmplificationProduct A ρ δ
          (fixedPrecisionScale N) h₀ s t +
        roundedBeta A ρ (fixedPrecisionScale N)
            (roundedOrbit A ρ h₀ s) *
          roundedAmplificationProduct A ρ δ
            (fixedPrecisionScale N) h₀ (s + 1) t ≤
        Real.exp (C * (Real.log (Real.log N)) ^ 2) +
          (K * Real.log N) *
            Real.exp (C * (Real.log (Real.log N)) ^ 2) :=
      add_le_add hp₁
        (mul_le_mul hβ hp₂ hp₂_nonneg hKlog_nonneg)
    _ = (1 + K * Real.log N) *
          Real.exp (C * (Real.log (Real.log N)) ^ 2) := by ring
    _ ≤ Real.exp (C' * (Real.log (Real.log N)) ^ 2) :=
      habsorb N hNabsorb

end AbsorptionCutoff
