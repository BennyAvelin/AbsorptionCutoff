/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.InvariantLaw
import AbsorptionCutoff.Supercritical.TruncatedCramer
import AbsorptionCutoff.Supercritical.Deterministic
import AbsorptionCutoff.MarkovTrajectory
import Mathlib.Probability.Moments.SubGaussian

/-!
# Uniqueness of the reconstructed nonzero invariant law

This file transfers uniqueness of the normalized nonzero squared-radius law
to the invariant vector law reconstructed through `Jkernel`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory Topology

namespace AbsorptionCutoff

private lemma inverseMomentTruncation_coeff_pos (k : ℕ) :
    (0 : ℝ) < k + 1 := by
  exact_mod_cast Nat.succ_pos k

private lemma inverseMomentTruncation_den_pos (k : ℕ) (q : ℝ) :
    0 < 1 + (k + 1 : ℝ) * |q| :=
  add_pos_of_pos_of_nonneg zero_lt_one
    (mul_nonneg (inverseMomentTruncation_coeff_pos k).le (abs_nonneg q))

/-- A bounded continuous reciprocal-moment truncation which retains the value `1` at
the origin.  The index controls the scale on which the truncation detects mass near
zero. -/
noncomputable def inverseMomentTruncation (k : ℕ) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun q => (1 + (k + 1 : ℝ) * |q|)⁻¹)
    ((continuous_const.add (continuous_const.mul continuous_abs)).inv₀
      (fun q => (inverseMomentTruncation_den_pos k q).ne'))
    1
    (fun q => by
      have hden := inverseMomentTruncation_den_pos k q
      have hone : 1 ≤ 1 + (k + 1 : ℝ) * |q| :=
        le_add_of_nonneg_right
          (mul_nonneg (inverseMomentTruncation_coeff_pos k).le (abs_nonneg q))
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden)]
      exact inv_le_one_of_one_le₀ hone)

@[simp]
lemma inverseMomentTruncation_apply (k : ℕ) (q : ℝ) :
    inverseMomentTruncation k q = (1 + (k + 1 : ℝ) * |q|)⁻¹ :=
  rfl

@[simp]
lemma inverseMomentTruncation_zero (k : ℕ) :
    inverseMomentTruncation k 0 = 1 := by
  simp

lemma inverseMomentTruncation_nonneg (k : ℕ) (q : ℝ) :
    0 ≤ inverseMomentTruncation k q := by
  rw [inverseMomentTruncation_apply]
  exact inv_nonneg.mpr (inverseMomentTruncation_den_pos k q).le

lemma inverseMomentTruncation_le_one (k : ℕ) (q : ℝ) :
    inverseMomentTruncation k q ≤ 1 := by
  rw [inverseMomentTruncation_apply]
  exact inv_le_one_of_one_le₀ <|
    le_add_of_nonneg_right
      (mul_nonneg (inverseMomentTruncation_coeff_pos k).le (abs_nonneg q))

/-- At every positive radius, the truncation is bounded by the reciprocal moment
rescaled by `(k+1)⁻¹`. -/
lemma inverseMomentTruncation_le_scaled_inv (k : ℕ) {q : ℝ} (hq : 0 < q) :
    inverseMomentTruncation k q ≤ (k + 1 : ℝ)⁻¹ * q⁻¹ := by
  rw [inverseMomentTruncation_apply, abs_of_pos hq, ← mul_inv]
  exact inv_anti₀ (mul_pos (inverseMomentTruncation_coeff_pos k) hq)
    (le_add_of_nonneg_left zero_le_one)

/-- A weak limit of probability measures with uniformly bounded reciprocal moments
has no atom at the origin, provided the approximating measures are supported on
the positive half-line. -/
theorem apply_singleton_zero_of_tendsto_of_uniform_integral_inv
    (μs : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hconv : Tendsto μs atTop (𝓝 ν))
    (hpos : ∀ n, ∀ᵐ q ∂(μs n : Measure ℝ), 0 < q)
    (hinv : ∀ n, Integrable (fun q : ℝ => q⁻¹) (μs n : Measure ℝ))
    {C : ℝ}
    (hbound : ∀ n, ∫ q, q⁻¹ ∂(μs n : Measure ℝ) ≤ C) :
    (ν : Measure ℝ) ({0} : Set ℝ) = 0 := by
  have htrunc_bound (k n : ℕ) :
      ∫ q, inverseMomentTruncation k q ∂(μs n : Measure ℝ) ≤
        (k + 1 : ℝ)⁻¹ * C := by
    calc
      ∫ q, inverseMomentTruncation k q ∂(μs n : Measure ℝ) ≤
          ∫ q, (k + 1 : ℝ)⁻¹ * q⁻¹ ∂(μs n : Measure ℝ) :=
        integral_mono_ae
          (BoundedContinuousFunction.integrable _ _)
          ((hinv n).const_mul _)
          ((hpos n).mono fun q hq => inverseMomentTruncation_le_scaled_inv k hq)
      _ = (k + 1 : ℝ)⁻¹ * ∫ q, q⁻¹ ∂(μs n : Measure ℝ) := by
        rw [integral_const_mul]
      _ ≤ (k + 1 : ℝ)⁻¹ * C :=
        mul_le_mul_of_nonneg_left (hbound n)
          (inv_nonneg.mpr (inverseMomentTruncation_coeff_pos k).le)
  have hlimit_bound (k : ℕ) :
      ∫ q, inverseMomentTruncation k q ∂(ν : Measure ℝ) ≤
        (k + 1 : ℝ)⁻¹ * C := by
    exact le_of_tendsto
      ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
        (inverseMomentTruncation k))
      (Eventually.of_forall (htrunc_bound k))
  have hatom_le (k : ℕ) :
      (ν : Measure ℝ).real ({0} : Set ℝ) ≤
        ∫ q, inverseMomentTruncation k q ∂(ν : Measure ℝ) := by
    calc
      (ν : Measure ℝ).real ({0} : Set ℝ) =
          ∫ q in ({0} : Set ℝ), inverseMomentTruncation k q ∂(ν : Measure ℝ) := by
        rw [integral_singleton, inverseMomentTruncation_zero, smul_eq_mul, mul_one]
      _ ≤ ∫ q, inverseMomentTruncation k q ∂(ν : Measure ℝ) :=
        setIntegral_le_integral
          (BoundedContinuousFunction.integrable _ _)
          (Eventually.of_forall (inverseMomentTruncation_nonneg k))
  have hmass_bound (k : ℕ) :
      (ν : Measure ℝ).real ({0} : Set ℝ) ≤ C / (k + 1 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using (hatom_le k).trans (hlimit_bound k)
  have htozero :
      Tendsto (fun k : ℕ => C / (k + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
  have hmass_nonpos : (ν : Measure ℝ).real ({0} : Set ℝ) ≤ 0 :=
    ge_of_tendsto' htozero hmass_bound
  have hmass_zero : (ν : Measure ℝ).real ({0} : Set ℝ) = 0 :=
    le_antisymm hmass_nonpos measureReal_nonneg
  exact (measureReal_eq_zero_iff).mp hmass_zero

/-- A uniform negative-moment bound passes to a weak probability limit when
both the approximating laws and the limit are carried by the positive
half-line. -/
theorem integrable_neg_rpow_of_tendsto_of_uniform_integral
    {p : ℝ} (hp : 0 ≤ p)
    (μs : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hconv : Tendsto μs atTop (𝓝 ν))
    (hμpos : ∀ n, ∀ᵐ q ∂(μs n : Measure ℝ), 0 < q)
    (hνpos : ∀ᵐ q ∂(ν : Measure ℝ), 0 < q)
    (hint :
      ∀ n, Integrable (fun q : ℝ => q ^ (-p)) (μs n : Measure ℝ))
    {C : ℝ}
    (hbound :
      ∀ n, (∫ q : ℝ, q ^ (-p) ∂(μs n : Measure ℝ)) ≤ C) :
    Integrable (fun q : ℝ => q ^ (-p)) (ν : Measure ℝ) ∧
      (∫ q : ℝ, q ^ (-p) ∂(ν : Measure ℝ)) ≤ C := by
  have htrunc_bound (k n : ℕ) :
      (∫ q, negativeMomentTruncation p hp k q
          ∂(μs n : Measure ℝ)) ≤ C := by
    exact (integral_mono_ae
      (BoundedContinuousFunction.integrable _ _)
      (hint n)
      ((hμpos n).mono fun q hq => negativeMomentTruncation_le hp hq k)).trans
        (hbound n)
  have hlimit_bound (k : ℕ) :
      (∫ q, negativeMomentTruncation p hp k q
          ∂(ν : Measure ℝ)) ≤ C := by
    exact le_of_tendsto
      ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv)
        (negativeMomentTruncation p hp k))
      (Eventually.of_forall (htrunc_bound k))
  have hlintegral_tendsto :
      Tendsto
        (fun k : ℕ =>
          ∫⁻ q, ENNReal.ofReal (negativeMomentTruncation p hp k q)
            ∂(ν : Measure ℝ))
        atTop
        (𝓝 (∫⁻ q, ENNReal.ofReal (q ^ (-p)) ∂(ν : Measure ℝ))) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro k
      exact
        (negativeMomentTruncation p hp k).continuous.measurable
          |>.aemeasurable.ennreal_ofReal
    · filter_upwards with q
      intro k l hkl
      exact ENNReal.ofReal_le_ofReal
        (negativeMomentTruncation_mono hp hkl q)
    · filter_upwards [hνpos] with q hq
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_negativeMomentTruncation hp hq)
  have hlintegral_bound (k : ℕ) :
      (∫⁻ q, ENNReal.ofReal (negativeMomentTruncation p hp k q)
          ∂(ν : Measure ℝ)) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (BoundedContinuousFunction.integrable _ _)
      (Eventually.of_forall
        (negativeMomentTruncation_nonneg p hp k))]
    exact ENNReal.ofReal_le_ofReal (hlimit_bound k)
  have htarget_lintegral_bound :
      (∫⁻ q, ENNReal.ofReal (q ^ (-p)) ∂(ν : Measure ℝ)) ≤
        ENNReal.ofReal C :=
    le_of_tendsto hlintegral_tendsto
      (Eventually.of_forall hlintegral_bound)
  have htarget_nonneg :
      ∀ᵐ q ∂(ν : Measure ℝ), 0 ≤ q ^ (-p) :=
    hνpos.mono fun q hq => Real.rpow_nonneg hq.le _
  have htarget :
      Integrable (fun q : ℝ => q ^ (-p)) (ν : Measure ℝ) := by
    refine ⟨(by fun_prop), (hasFiniteIntegral_iff_ofReal htarget_nonneg).2 ?_⟩
    exact htarget_lintegral_bound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨htarget, ?_⟩
  have hintegral_tendsto :
      Tendsto
        (fun k : ℕ =>
          ∫ q, negativeMomentTruncation p hp k q ∂(ν : Measure ℝ))
        atTop
        (𝓝 (∫ q, q ^ (-p) ∂(ν : Measure ℝ))) := by
    apply integral_tendsto_of_tendsto_of_monotone
    · intro k
      exact BoundedContinuousFunction.integrable _ _
    · exact htarget
    · filter_upwards with q
      intro k l hkl
      exact negativeMomentTruncation_mono hp hkl q
    · filter_upwards [hνpos] with q hq
      exact tendsto_negativeMomentTruncation hp hq
  exact le_of_tendsto hintegral_tendsto
    (Eventually.of_forall hlimit_bound)

/-- Every power of `Kchain` started in the open interior remains in the open
interior almost surely. -/
lemma Kchain_pow_apply_Ioo_eq_one
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N) {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (t : ℕ) :
    ((Kchain A N) ^ t) q (Set.Ioo (0 : ℝ) 1) = 1 := by
  induction t with
  | zero =>
      rw [pow_zero]
      change Measure.dirac q (Set.Ioo (0 : ℝ) 1) = 1
      rw [Measure.dirac_apply' _ measurableSet_Ioo, Set.indicator_of_mem hq]
      rfl
  | succ t ht =>
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ measurableSet_Ioo]
      calc
        ∫⁻ y, Kchain A N y (Set.Ioo (0 : ℝ) 1) ∂((Kchain A N) ^ t) q =
            ∫⁻ _y, (1 : ENNReal) ∂((Kchain A N) ^ t) q := by
          apply lintegral_congr_ae
          filter_upwards [(mem_ae_iff_prob_eq_one measurableSet_Ioo).2 ht] with y hy
          exact Kchain_apply_Ioo_eq_one hA hy.1 hN
        _ = 1 := by simp

/-- Every positive-length Cesàro average of `Kchain` started in the open
interior remains in the open interior almost surely. -/
lemma cesaroPM_apply_Ioo_eq_one
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N) {q : ℝ}
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    (cesaroPM A N q n : Measure ℝ) (Set.Ioo (0 : ℝ) 1) = 1 := by
  rw [cesaroPM_toMeasure]
  simp only [cesaroMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Kchain_pow_apply_Ioo_eq_one hA hN hq, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, smul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 n.succ_ne_zero) (by simp)

/-- Under the explicit finite-dimensional supercritical criterion, `Kchain`
has an invariant probability supported on `[0,1]` with no atom at the
absorbing origin. -/
theorem exists_invariant_Kchain_apply_singleton_zero_of_dimension
    {A : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N) :
    ∃ ν : ProbabilityMeasure ℝ,
      Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
      (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
      (ν : Measure ℝ) ({0} : Set ℝ) = 0 := by
  let q₀ : ℝ := 1 / 2
  have hq₀Ioo : q₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [q₀]
    norm_num
  have hq₀Icc : q₀ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hq₀Ioo.1.le, hq₀Ioo.2.le⟩
  have hq₀Ioc : q₀ ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨hq₀Ioo.1, hq₀Ioo.2.le⟩
  obtain ⟨ν, φ, _hφ, hconv, hν, hνsupport⟩ :=
    exists_invariant_of_cesaro_with_subseq A (Nat.zero_lt_of_lt hN) hq₀Icc
  obtain ⟨C, _hC, hcesaro⟩ :=
    exists_uniform_integral_inv_cesaroMeasure_le hA hN hdim hq₀Ioc
  refine ⟨ν, hν, hνsupport, ?_⟩
  apply apply_singleton_zero_of_tendsto_of_uniform_integral_inv
    (fun n => cesaroPM A N q₀ (φ n)) ν hconv
  · intro n
    have hmem :
        ∀ᵐ y ∂(cesaroPM A N q₀ (φ n) : Measure ℝ),
          y ∈ Set.Ioo (0 : ℝ) 1 :=
      (mem_ae_iff_prob_eq_one measurableSet_Ioo).2
        (cesaroPM_apply_Ioo_eq_one (zero_lt_one.trans hA)
          (Nat.zero_lt_of_lt hN) hq₀Ioo (φ n))
    exact hmem.mono fun y hy => hy.1
  · intro n
    simpa only [cesaroPM_toMeasure] using
      (hcesaro (φ n + 1) (Nat.succ_pos (φ n))).1
  · intro n
    simpa only [cesaroPM_toMeasure] using
      (hcesaro (φ n + 1) (Nat.succ_pos (φ n))).2

/-- A uniform negative-moment estimate for the Cesàro laws passes to an
invariant subsequential limit, with the same bound. -/
theorem exists_invariant_Kchain_integrable_neg_rpow_of_uniform_cesaro
    {A p C : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N) (hp : 0 ≤ p)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hcesaro :
      ∀ T : ℕ, 0 < T →
        Integrable
            (fun y : ℝ => y ^ (-p))
            (cesaroMeasure (Kchain A N) q T) ∧
          (∫ y : ℝ, y ^ (-p)
              ∂cesaroMeasure (Kchain A N) q T) ≤ C) :
    ∃ ν : ProbabilityMeasure ℝ,
      Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
        (ν : Measure ℝ) ({0} : Set ℝ) = 0 ∧
        Integrable (fun y : ℝ => y ^ (-p)) (ν : Measure ℝ) ∧
        (∫ y : ℝ, y ^ (-p) ∂(ν : Measure ℝ)) ≤ C := by
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
  have hqIoc : q ∈ Set.Ioc (0 : ℝ) 1 := ⟨hq.1, hq.2.le⟩
  obtain ⟨ν, φ, _hφ, hconv, hν, hνsupport⟩ :=
    exists_invariant_of_cesaro_with_subseq A
      (Nat.zero_lt_of_lt hN) hqIcc
  have hμpos (n : ℕ) :
      ∀ᵐ y ∂(cesaroPM A N q (φ n) : Measure ℝ), 0 < y := by
    have hmem :
        ∀ᵐ y ∂(cesaroPM A N q (φ n) : Measure ℝ),
          y ∈ Set.Ioo (0 : ℝ) 1 :=
      (mem_ae_iff_prob_eq_one measurableSet_Ioo).2
        (cesaroPM_apply_Ioo_eq_one (zero_lt_one.trans hA)
          (Nat.zero_lt_of_lt hN) hq (φ n))
    exact hmem.mono fun y hy => hy.1
  obtain ⟨Cinv, _hCinv, hinv_cesaro⟩ :=
    exists_uniform_integral_inv_cesaroMeasure_le hA hN hdim hqIoc
  have hinv (n : ℕ) :
      Integrable (fun y : ℝ => y⁻¹)
        (cesaroPM A N q (φ n) : Measure ℝ) := by
    simpa only [cesaroPM_toMeasure] using
      (hinv_cesaro (φ n + 1) (Nat.succ_pos (φ n))).1
  have hinv_bound (n : ℕ) :
      (∫ y : ℝ, y⁻¹ ∂(cesaroPM A N q (φ n) : Measure ℝ)) ≤ Cinv := by
    simpa only [cesaroPM_toMeasure] using
      (hinv_cesaro (φ n + 1) (Nat.succ_pos (φ n))).2
  have hν0 : (ν : Measure ℝ) ({0} : Set ℝ) = 0 :=
    apply_singleton_zero_of_tendsto_of_uniform_integral_inv
      (fun n => cesaroPM A N q (φ n)) ν hconv hμpos hinv hinv_bound
  have hνIcc :
      ∀ᵐ y ∂(ν : Measure ℝ), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hνsupport
  have hνne : ∀ᵐ y ∂(ν : Measure ℝ), y ≠ 0 := by
    rw [ae_iff]
    simpa using hν0
  have hνpos : ∀ᵐ y ∂(ν : Measure ℝ), 0 < y := by
    filter_upwards [hνIcc, hνne] with y hy hy0
    exact lt_of_le_of_ne hy.1 (Ne.symm hy0)
  have hneg_int (n : ℕ) :
      Integrable (fun y : ℝ => y ^ (-p))
        (cesaroPM A N q (φ n) : Measure ℝ) := by
    simpa only [cesaroPM_toMeasure] using
      (hcesaro (φ n + 1) (Nat.succ_pos (φ n))).1
  have hneg_bound (n : ℕ) :
      (∫ y : ℝ, y ^ (-p)
          ∂(cesaroPM A N q (φ n) : Measure ℝ)) ≤ C := by
    simpa only [cesaroPM_toMeasure] using
      (hcesaro (φ n + 1) (Nat.succ_pos (φ n))).2
  have hmoment :=
    integrable_neg_rpow_of_tendsto_of_uniform_integral
      hp (fun n => cesaroPM A N q (φ n)) ν hconv
      hμpos hνpos hneg_int hneg_bound
  exact ⟨ν, hν, hνsupport, hν0, hmoment.1, hmoment.2⟩

/-- A negative moment controls the mass of a fixed interval near the origin.
This is the paper's Markov-inequality step for localization. -/
lemma measureReal_Ioc_le_rpow_mul_integral_neg_rpow
    {μ : Measure ℝ} [IsFiniteMeasure μ] {p r : ℝ}
    (hp : 0 ≤ p) (hr : 0 < r)
    (hμpos : ∀ᵐ q ∂μ, 0 < q)
    (hint : Integrable (fun q : ℝ => q ^ (-p)) μ) :
    μ.real (Set.Ioc 0 r) ≤
      r ^ p * ∫ q : ℝ, q ^ (-p) ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ] fun q : ℝ => q ^ (-p) :=
    hμpos.mono fun q hq => (Real.rpow_pos_of_pos hq (-p)).le
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg hnonneg hint (r ^ (-p))
  have hsubset :
      Set.Ioc (0 : ℝ) r ⊆ {q : ℝ | r ^ (-p) ≤ q ^ (-p)} := by
    intro q hq
    exact Real.rpow_le_rpow_of_nonpos hq.1 hq.2 (neg_nonpos.mpr hp)
  have hmul :
      r ^ (-p) * μ.real (Set.Ioc (0 : ℝ) r) ≤
        ∫ q : ℝ, q ^ (-p) ∂μ :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
      (Real.rpow_pos_of_pos hr (-p)).le).trans hmarkov
  calc
    μ.real (Set.Ioc (0 : ℝ) r)
        ≤ (∫ q : ℝ, q ^ (-p) ∂μ) / r ^ (-p) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hr (-p))).2 <| by
        simpa only [mul_comm] using hmul
    _ = r ^ p * ∫ q : ℝ, q ^ (-p) ∂μ := by
      rw [Real.rpow_neg hr.le, div_inv_eq_mul, mul_comm]

/-- For a positive exponent, the fixed small-radius threshold can be chosen
below any prescribed cap so that its logarithmic moment exponent is negative. -/
lemma exists_pos_lt_and_add_mul_log_neg
    {R₀ γ : ℝ} (hR₀ : 0 < R₀) (hγ : 0 < γ) (b : ℝ) :
    ∃ r ∈ Set.Ioo (0 : ℝ) R₀, b + γ * Real.log r < 0 := by
  let s : ℝ := Real.exp (-(|b| + 1) / γ)
  let r : ℝ := min (R₀ / 2) s
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) hs
  have hrR₀ : r < R₀ := by
    exact (min_le_left (R₀ / 2) s).trans_lt (by linarith)
  refine ⟨r, ⟨hr, hrR₀⟩, ?_⟩
  have hrs : r ≤ s := min_le_right (R₀ / 2) s
  have hlog : Real.log r ≤ -(|b| + 1) / γ := by
    calc
      Real.log r ≤ Real.log s := Real.log_le_log hr hrs
      _ = -(|b| + 1) / γ := by simp only [s, Real.log_exp]
  have hmul :
      γ * Real.log r ≤ γ * (-(|b| + 1) / γ) :=
    mul_le_mul_of_nonneg_left hlog hγ.le
  have hcancel : γ * (-(|b| + 1) / γ) = -(|b| + 1) := by
    field_simp [hγ.ne']
  rw [hcancel] at hmul
  nlinarith [le_abs_self b]

/-- The explicit invariant-moment maximum is bounded by one fixed prefactor
times one exponential rate in every positive dimension. -/
lemma exists_exponential_envelope_invariant_moment_max
    {γ κ b : ℝ} (hκ : 0 < κ) :
    ∃ C B : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
      max ((1 / 2 : ℝ) ^ (-(γ * (N : ℝ))))
          (Real.exp (b * (N : ℝ)) /
            (1 - Real.exp (-(κ * (N : ℝ))))) ≤
        C * Real.exp (B * (N : ℝ)) := by
  let d : ℝ := 1 - Real.exp (-κ)
  let C : ℝ := d⁻¹
  let B : ℝ := max (-γ * Real.log (1 / 2 : ℝ)) b
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hκ))
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, B, hC, ?_⟩
  intro N hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNnonneg : (0 : ℝ) ≤ N := hNreal.trans' zero_le_one
  have hCge : 1 ≤ C := by
    have hdle : d ≤ 1 := by
      dsimp [d]
      exact sub_le_self 1 (Real.exp_pos (-κ)).le
    simpa only [C, inv_one] using inv_anti₀ hd hdle
  have hfirst :
      (1 / 2 : ℝ) ^ (-(γ * (N : ℝ))) ≤
        C * Real.exp (B * (N : ℝ)) := by
    have hrate : -γ * Real.log (1 / 2 : ℝ) ≤ B :=
      le_max_left _ _
    have hexp :
        (1 / 2 : ℝ) ^ (-(γ * (N : ℝ))) ≤
          Real.exp (B * (N : ℝ)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      apply Real.exp_le_exp.mpr
      calc
        Real.log (1 / 2 : ℝ) * (-(γ * (N : ℝ))) =
            (-γ * Real.log (1 / 2 : ℝ)) * (N : ℝ) := by ring
        _ ≤ B * (N : ℝ) :=
          mul_le_mul_of_nonneg_right hrate hNnonneg
    exact hexp.trans <| by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hCge (Real.exp_pos (B * (N : ℝ))).le
  have hdN :
      d ≤ 1 - Real.exp (-(κ * (N : ℝ))) := by
    dsimp [d]
    have hκN : κ ≤ κ * (N : ℝ) := by nlinarith
    have hexp :
        Real.exp (-(κ * (N : ℝ))) ≤ Real.exp (-κ) :=
      Real.exp_le_exp.mpr (neg_le_neg hκN)
    linarith
  have hdenpos : 0 < 1 - Real.exp (-(κ * (N : ℝ))) :=
    hd.trans_le hdN
  have hinv :
      (1 - Real.exp (-(κ * (N : ℝ))))⁻¹ ≤ C := by
    simpa only [C] using inv_anti₀ hd hdN
  have hsecond :
      Real.exp (b * (N : ℝ)) /
          (1 - Real.exp (-(κ * (N : ℝ)))) ≤
        C * Real.exp (B * (N : ℝ)) := by
    have hrate : b ≤ B := le_max_right _ _
    have hexp :
        Real.exp (b * (N : ℝ)) ≤ Real.exp (B * (N : ℝ)) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hrate hNnonneg)
    rw [div_eq_mul_inv]
    calc
      Real.exp (b * (N : ℝ)) *
            (1 - Real.exp (-(κ * (N : ℝ))))⁻¹
          ≤ Real.exp (B * (N : ℝ)) * C :=
        mul_le_mul hexp hinv (inv_nonneg.mpr hdenpos.le)
          (Real.exp_pos (B * (N : ℝ))).le
      _ = C * Real.exp (B * (N : ℝ)) := mul_comm _ _
  exact max_le hfirst hsecond

/-- Paper-facing invariant-law negative-moment bound in every sufficiently
large dimension. -/
theorem exists_eventually_invariant_Kchain_integrable_neg_rpow
    {A qStar R : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hR : R ∈ Set.Ioo (0 : ℝ) qStar) :
    ∃ R₀ γ κ b : ℝ, ∃ N₀ : ℕ,
      R₀ ∈ Set.Ioc 0 1 ∧ R₀ < qStar - R ∧
        γ ∈ Set.Ioo 0 (1 / 2 : ℝ) ∧ 0 < κ ∧
          ∀ N : ℕ, N₀ ≤ N →
            ∃ ν : ProbabilityMeasure ℝ,
              Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
                (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
                (ν : Measure ℝ) ({0} : Set ℝ) = 0 ∧
                Integrable
                    (fun y : ℝ => y ^ (-(γ * (N : ℝ))))
                    (ν : Measure ℝ) ∧
                (∫ y : ℝ, y ^ (-(γ * (N : ℝ)))
                    ∂(ν : Measure ℝ)) ≤
                  max ((1 / 2 : ℝ) ^ (-(γ * (N : ℝ))))
                    (Real.exp (b * (N : ℝ)) /
                      (1 - Real.exp (-(κ * (N : ℝ))))) := by
  obtain ⟨R₀, γ, κ, b, N₀, hR₀, hR₀cap, hγ, hκ, hmoment⟩ :=
    exists_eventually_uniform_integral_neg_rpow_Kchain_pow_and_cesaroMeasure_le
      hA hqStar hR
  obtain ⟨N₁, hthreshold⟩ :=
    exists_dimension_threshold_for_reciprocal_moment hA
  refine ⟨R₀, γ, κ, b, max N₀ N₁, hR₀, hR₀cap, hγ, hκ, ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (Nat.le_max_left N₀ N₁).trans hN
  have hN₁le : N₁ ≤ N := (Nat.le_max_right N₀ N₁).trans hN
  obtain ⟨hNtwo, hdim⟩ := hthreshold N hN₁le
  let q₀ : ℝ := 1 / 2
  have hq₀Ioo : q₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [q₀]
    norm_num
  have hq₀Ioc : q₀ ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨hq₀Ioo.1, hq₀Ioo.2.le⟩
  obtain ⟨C, _hC, hCeq, hcesaro⟩ :=
    (hmoment N hN₀ (Nat.zero_lt_of_lt hNtwo) q₀ hq₀Ioc).2
  obtain ⟨ν, hν, hνsupport, hν0, hνint, hνbound⟩ :=
    exists_invariant_Kchain_integrable_neg_rpow_of_uniform_cesaro
      hA hNtwo hdim
      (mul_nonneg hγ.1.le (Nat.cast_nonneg N))
      hq₀Ioo hcesaro
  refine ⟨ν, hν, hνsupport, hν0, hνint, ?_⟩
  simpa only [q₀, hCeq] using hνbound

/-- In every sufficiently large dimension, an invariant origin-free radius
law has exponentially small mass below one fixed positive threshold. -/
theorem exists_eventually_invariant_Kchain_small_ball_le_exp
    {A qStar R : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hR : R ∈ Set.Ioo (0 : ℝ) qStar) :
    ∃ r C c : ℝ, ∃ N₀ : ℕ,
      r ∈ Set.Ioo 0 (qStar - R) ∧ 0 < C ∧ 0 < c ∧
        ∀ N : ℕ, N₀ ≤ N →
          ∃ ν : ProbabilityMeasure ℝ,
            Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
              (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
              (ν : Measure ℝ) ({0} : Set ℝ) = 0 ∧
              (ν : Measure ℝ).real (Set.Ioc 0 r) ≤
                C * Real.exp (-(c * (N : ℝ))) := by
  obtain ⟨R₀, γ, κ, b, N₀, hR₀, hR₀cap, hγ, hκ, hmoment⟩ :=
    exists_eventually_invariant_Kchain_integrable_neg_rpow hA hqStar hR
  obtain ⟨C, B, hC, henvelope⟩ :=
    exists_exponential_envelope_invariant_moment_max hκ
  obtain ⟨r, hr, hrate⟩ :=
    exists_pos_lt_and_add_mul_log_neg hR₀.1 hγ.1 B
  let c : ℝ := -(B + γ * Real.log r)
  have hc : 0 < c := by
    dsimp [c]
    exact neg_pos.mpr hrate
  refine ⟨r, C, c, max N₀ 1, ⟨hr.1, hr.2.trans hR₀cap⟩, hC, hc, ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (Nat.le_max_left N₀ 1).trans hN
  have hNone : 1 ≤ N := (Nat.le_max_right N₀ 1).trans hN
  have hNpos : 0 < N := Nat.zero_lt_of_lt hNone
  obtain ⟨ν, hν, hνsupport, hν0, hνint, hνbound⟩ :=
    hmoment N hN₀
  have hνIcc :
      ∀ᵐ y ∂(ν : Measure ℝ), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hνsupport
  have hνne : ∀ᵐ y ∂(ν : Measure ℝ), y ≠ 0 := by
    rw [ae_iff]
    simpa using hν0
  have hνpos : ∀ᵐ y ∂(ν : Measure ℝ), 0 < y := by
    filter_upwards [hνIcc, hνne] with y hy hy0
    exact lt_of_le_of_ne hy.1 (Ne.symm hy0)
  have hsmall :
      (ν : Measure ℝ).real (Set.Ioc 0 r) ≤
        r ^ (γ * (N : ℝ)) *
          ∫ y : ℝ, y ^ (-(γ * (N : ℝ))) ∂(ν : Measure ℝ) :=
    measureReal_Ioc_le_rpow_mul_integral_neg_rpow
      (mul_nonneg hγ.1.le (Nat.cast_nonneg N)) hr.1 hνpos hνint
  have hmoment_exp :
      (∫ y : ℝ, y ^ (-(γ * (N : ℝ))) ∂(ν : Measure ℝ)) ≤
        C * Real.exp (B * (N : ℝ)) :=
    hνbound.trans (henvelope N hNpos)
  refine ⟨ν, hν, hνsupport, hν0, hsmall.trans ?_⟩
  calc
    r ^ (γ * (N : ℝ)) *
          ∫ y : ℝ, y ^ (-(γ * (N : ℝ))) ∂(ν : Measure ℝ)
        ≤ r ^ (γ * (N : ℝ)) *
            (C * Real.exp (B * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hmoment_exp
        (Real.rpow_pos_of_pos hr.1 (γ * (N : ℝ))).le
    _ = C * Real.exp (-(c * (N : ℝ))) := by
      rw [Real.rpow_def_of_pos hr.1]
      calc
        Real.exp (Real.log r * (γ * (N : ℝ))) *
              (C * Real.exp (B * (N : ℝ))) =
            C * (Real.exp (Real.log r * (γ * (N : ℝ))) *
              Real.exp (B * (N : ℝ))) := by ring
        _ = C * Real.exp
              (Real.log r * (γ * (N : ℝ)) + B * (N : ℝ)) := by
            rw [Real.exp_add]
        _ = C * Real.exp (-(c * (N : ℝ))) := by
            congr 2
            dsimp [c]
            ring

/-- The exact sub-Gaussian variance proxy for the unrounded empirical
Gaussian radius update. -/
noncomputable def FmapSubgaussianParameter (N : ℕ) : NNReal :=
  NNReal.mk (((N : ℝ)⁻¹) ^ 2) (sq_nonneg ((N : ℝ)⁻¹)) *
    ∑ _i : Fin N, ((‖(1 : ℝ)‖₊ / 2) ^ 2)

/-- For positive dimension, the unrounded empirical-average proxy is
`1 / (4N)`. -/
lemma coe_FmapSubgaussianParameter {N : ℕ} (hN : 0 < N) :
    (FmapSubgaussianParameter N : ℝ) = 1 / (4 * N) := by
  unfold FmapSubgaussianParameter
  simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_pow,
    NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, NNReal.coe_natCast]
  norm_num [Real.norm_eq_abs]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- The centered one-step unrounded radius has second moment at most `1/(4N)`,
by independence and the `[0,1]` coordinate variance bound. -/
lemma integral_sq_Fmap_sub_V_le
    {A q : ℝ} {N : ℕ} (hN : 0 < N) :
    ∫ g, (Fmap A N q g - V A q) ^ 2 ∂(gaussianVec N) ≤
      1 / (4 * (N : ℝ)) := by
  let U : ℝ → ℝ :=
    fun x => Real.tanh (A * Real.sqrt q * x) ^ 2
  have hUmeas : AEStronglyMeasurable U (gaussianReal 0 1) :=
    ((continuous_tanh.comp (by fun_prop)).pow 2).aestronglyMeasurable
  have hUbounds :
      ∀ᵐ x ∂(gaussianReal 0 1), U x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards with x
    exact ⟨sq_nonneg _, (Real.tanh_sq_lt_one _).le⟩
  have hUmem : MemLp U 2 (gaussianReal 0 1) :=
    memLp_of_bounded hUbounds hUmeas 2
  have hvarSum :
      variance (fun g : Fin N → ℝ => ∑ i, U (g i)) (gaussianVec N) =
        ∑ _i : Fin N, variance U (gaussianReal 0 1) := by
    unfold gaussianVec
    rw [show (fun g : Fin N → ℝ => ∑ i, U (g i)) =
        ∑ i, fun g : Fin N → ℝ => U (g i) by
      funext g
      simp]
    exact variance_sum_pi (X := fun _ : Fin N => U) fun _ => hUmem
  have hFmeas :
      AEMeasurable (Fmap A N q) (gaussianVec N) := by
    have hpair :
        Measurable (fun g : Fin N → ℝ => (q, g)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_Fmap A N).comp hpair).aemeasurable
  rw [← integral_Fmap hN.ne' q, ← variance_eq_integral hFmeas]
  have hvarF :
      variance (Fmap A N q) (gaussianVec N) =
        (N : ℝ)⁻¹ ^ 2 *
          ((N : ℝ) * variance U (gaussianReal 0 1)) := by
    unfold Fmap
    rw [variance_const_mul]
    change (N : ℝ)⁻¹ ^ 2 *
        variance (fun g : Fin N → ℝ => ∑ i, U (g i)) (gaussianVec N) =
      _
    rw [hvarSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [hvarF]
  have hvarU :
      variance U (gaussianReal 0 1) ≤ 1 / 4 := by
    convert
      (variance_le_sq_of_bounded hUbounds hUmeas.aemeasurable) using 1
    norm_num
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (N : ℝ)⁻¹ ^ 2 *
          ((N : ℝ) * variance U (gaussianReal 0 1))
        ≤ (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * (1 / 4)) := by
      gcongr
    _ = 1 / (4 * (N : ℝ)) := by
      field_simp

/-- The one-step squared error about a fixed point splits into the squared
deterministic error and the centered noise variance. -/
lemma integral_sq_Fmap_sub_fixed_eq
    {A q qStar : ℝ} {N : ℕ} (hN : 0 < N) :
    ∫ g, (Fmap A N q g - qStar) ^ 2 ∂(gaussianVec N) =
      (V A q - qStar) ^ 2 +
        ∫ g, (Fmap A N q g - V A q) ^ 2 ∂(gaussianVec N) := by
  have hFmeas :
      AEMeasurable (Fmap A N q) (gaussianVec N) := by
    have hpair :
        Measurable (fun g : Fin N → ℝ => (q, g)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_Fmap A N).comp hpair).aemeasurable
  have hFstrong :
      AEStronglyMeasurable (Fmap A N q) (gaussianVec N) :=
    hFmeas.aestronglyMeasurable
  have hFbounds :
      ∀ᵐ g ∂(gaussianVec N), Fmap A N q g ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards with g
    exact ⟨Fmap_nonneg A N q g, (Fmap_lt_one hN q g).le⟩
  have hFmem :
      MemLp (Fmap A N q) 2 (gaussianVec N) :=
    memLp_of_bounded hFbounds hFstrong 2
  have hFint :
      Integrable (Fmap A N q) (gaussianVec N) :=
    hFmem.integrable (by norm_num)
  have hYmem :
      MemLp (fun g => Fmap A N q g - qStar) 2 (gaussianVec N) :=
    hFmem.sub (memLp_const qStar)
  have hmeanY :
      ∫ g, (Fmap A N q g - qStar) ∂(gaussianVec N) =
        V A q - qStar := by
    rw [integral_sub hFint (integrable_const qStar),
      integral_Fmap hN.ne' q, integral_const, probReal_univ, one_smul]
  have hvarY :
      variance (fun g => Fmap A N q g - qStar) (gaussianVec N) =
        ∫ g, (Fmap A N q g - qStar) ^ 2 ∂(gaussianVec N) -
          (V A q - qStar) ^ 2 := by
    simpa only [Pi.pow_apply, hmeanY] using variance_eq_sub hYmem
  have hvarShift :
      variance (fun g => Fmap A N q g - qStar) (gaussianVec N) =
        variance (Fmap A N q) (gaussianVec N) :=
    variance_sub_const hFstrong qStar
  have hvarF :
      variance (Fmap A N q) (gaussianVec N) =
        ∫ g, (Fmap A N q g - V A q) ^ 2 ∂(gaussianVec N) := by
    simpa only [integral_Fmap hN.ne' q] using
      variance_eq_integral hFmeas
  calc
    ∫ g, (Fmap A N q g - qStar) ^ 2 ∂(gaussianVec N) =
        variance (fun g => Fmap A N q g - qStar) (gaussianVec N) +
          (V A q - qStar) ^ 2 := by linarith
    _ = (V A q - qStar) ^ 2 +
          ∫ g, (Fmap A N q g - V A q) ^ 2 ∂(gaussianVec N) := by
      rw [hvarShift, hvarF, add_comm]

/-- A supported invariant radius law transports squared error through one
`Kchain` step, written as the Gaussian double integral of `Fmap`. -/
lemma invariant_integral_sq_sub_fixed_eq_integral_integral_Fmap
    {A qStar : ℝ} {N : ℕ} (hN : 0 < N)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν)
    (hνsupport : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) :
    ∫ q, (q - qStar) ^ 2 ∂ν =
      ∫ q, (∫ g, (Fmap A N q g - qStar) ^ 2
        ∂(gaussianVec N)) ∂ν := by
  let φ : ℝ → ℝ :=
    Set.Icc (0 : ℝ) 1 |>.indicator (fun q => (q - qStar) ^ 2)
  have hφmeas : Measurable φ := by
    dsimp [φ]
    exact ((measurable_id.sub measurable_const).pow_const 2).indicator
      measurableSet_Icc
  have hφbound : ∀ q : ℝ, ‖φ q‖ ≤ 1 := by
    intro q
    by_cases hq : q ∈ Set.Icc (0 : ℝ) 1
    · rw [show φ q = (q - qStar) ^ 2 by
        simp only [φ, Set.indicator_of_mem hq],
        Real.norm_eq_abs, abs_sq]
      have hdiff : |q - qStar| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hq.1, hq.2, hqStar.1, hqStar.2]
      have hsq :=
        (sq_le_sq₀ (abs_nonneg (q - qStar)) zero_le_one).2 hdiff
      simpa only [sq_abs, one_pow] using hsq
    · rw [show φ q = 0 by
        simp only [φ, Set.indicator_of_notMem hq], norm_zero]
      norm_num
  have hstation :=
    stationary_equation A N ν hν hφmeas hφbound
  have hνIcc :
      ∀ᵐ q ∂ν, q ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hνsupport
  have hleft :
      ∫ q, φ q ∂ν = ∫ q, (q - qStar) ^ 2 ∂ν := by
    apply integral_congr_ae
    filter_upwards [hνIcc] with q hq
    simp only [φ, Set.indicator_of_mem hq]
  have hright :
      ∫ q, (∫ g, φ (Fmap A N q g) ∂(gaussianVec N)) ∂ν =
        ∫ q, (∫ g, (Fmap A N q g - qStar) ^ 2
          ∂(gaussianVec N)) ∂ν := by
    apply integral_congr_ae
    filter_upwards with q
    apply integral_congr_ae
    filter_upwards with g
    have hFmem :
        Fmap A N q g ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨Fmap_nonneg A N q g, (Fmap_lt_one hN q g).le⟩
    simp only [φ, Set.indicator_of_mem hFmem]
  calc
    ∫ q, (q - qStar) ^ 2 ∂ν = ∫ q, φ q ∂ν := hleft.symm
    _ = ∫ q, (∫ g, φ (Fmap A N q g) ∂(gaussianVec N)) ∂ν :=
      hstation
    _ = ∫ q, (∫ g, (Fmap A N q g - qStar) ^ 2
        ∂(gaussianVec N)) ∂ν := hright

/-- Combining stationary transport with the conditional error decomposition
gives the stationary deterministic-plus-noise second-moment recursion. -/
lemma invariant_integral_sq_sub_fixed_eq_integral_add_noise
    {A qStar : ℝ} {N : ℕ} (hN : 0 < N)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν)
    (hνsupport : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) :
    ∫ q, (q - qStar) ^ 2 ∂ν =
      ∫ q, ((V A q - qStar) ^ 2 +
        ∫ g, (Fmap A N q g - V A q) ^ 2
          ∂(gaussianVec N)) ∂ν := by
  rw [invariant_integral_sq_sub_fixed_eq_integral_integral_Fmap
    hN hqStar ν hν hνsupport]
  apply integral_congr_ae
  filter_upwards with q
  exact integral_sq_Fmap_sub_fixed_eq hN

/-- The stationary second moment is bounded by the deterministic squared
error integral plus the uniform one-step noise variance `1/(4N)`. -/
lemma invariant_integral_sq_sub_fixed_le_integral_sq_V_add
    {A qStar : ℝ} {N : ℕ} (hN : 0 < N)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν)
    (hνsupport : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) :
    ∫ q, (q - qStar) ^ 2 ∂ν ≤
      (∫ q, (V A q - qStar) ^ 2 ∂ν) + 1 / (4 * (N : ℝ)) := by
  let D : ℝ → ℝ := fun q => (V A q - qStar) ^ 2
  let W : ℝ → ℝ := fun q =>
    ∫ g, (Fmap A N q g - V A q) ^ 2 ∂(gaussianVec N)
  have hDstrong : StronglyMeasurable D := by
    dsimp [D]
    exact (((V_continuous A).sub continuous_const).pow 2).stronglyMeasurable
  have hDbound : ∀ q : ℝ, ‖D q‖ ≤ 1 := by
    intro q
    rw [show D q = (V A q - qStar) ^ 2 by rfl,
      Real.norm_eq_abs, abs_sq]
    have hdiff : |V A q - qStar| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        linarith [V_nonneg A q, V_lt_one A q, hqStar.1, hqStar.2]
    have hsq :=
      (sq_le_sq₀ (abs_nonneg (V A q - qStar)) zero_le_one).2 hdiff
    simpa only [sq_abs, one_pow] using hsq
  have hDint : Integrable D ν :=
    Integrable.of_bound hDstrong.aestronglyMeasurable 1
      (Filter.Eventually.of_forall hDbound)
  have hjoint :
      StronglyMeasurable
        (fun p : ℝ × (Fin N → ℝ) =>
          (Fmap A N p.1 p.2 - V A p.1) ^ 2) := by
    exact ((measurable_Fmap A N).sub
      ((V_continuous A).measurable.comp measurable_fst)).pow_const
        2 |>.stronglyMeasurable
  have hWstrong : StronglyMeasurable W := by
    dsimp [W]
    exact hjoint.integral_prod_right'
  have hWnonneg : ∀ q : ℝ, 0 ≤ W q := by
    intro q
    dsimp [W]
    exact integral_nonneg fun g => sq_nonneg _
  have hWbound : ∀ q : ℝ, W q ≤ 1 / (4 * (N : ℝ)) := by
    intro q
    exact integral_sq_Fmap_sub_V_le hN
  have hWint : Integrable W ν := by
    refine Integrable.of_bound hWstrong.aestronglyMeasurable
      (1 / (4 * (N : ℝ))) ?_
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg q)]
    exact hWbound q
  have hWIntegral :
      ∫ q, W q ∂ν ≤ 1 / (4 * (N : ℝ)) := by
    calc
      ∫ q, W q ∂ν ≤ ∫ _q : ℝ, (1 / (4 * (N : ℝ))) ∂ν :=
        integral_mono_ae hWint (integrable_const _) <|
          Filter.Eventually.of_forall hWbound
      _ = 1 / (4 * (N : ℝ)) := by
        rw [integral_const, probReal_univ, one_smul]
  calc
    ∫ q, (q - qStar) ^ 2 ∂ν =
        ∫ q, (D q + W q) ∂ν := by
      simpa only [D, W] using
        invariant_integral_sq_sub_fixed_eq_integral_add_noise
          hN hqStar ν hν hνsupport
    _ = (∫ q, D q ∂ν) + ∫ q, W q ∂ν :=
      integral_add hDint hWint
    _ ≤ (∫ q, D q ∂ν) + 1 / (4 * (N : ℝ)) :=
      add_le_add_right hWIntegral _
    _ = (∫ q, (V A q - qStar) ^ 2 ∂ν) +
        1 / (4 * (N : ℝ)) := by rfl

/-- A derivative bound on a positive interval centered at a fixed point
implies the corresponding secant contraction throughout that interval. -/
lemma abs_V_sub_fixed_le_mul_abs_sub_fixed_of_deriv_le
    {A qStar κ R x : ℝ}
    (hA : A ≠ 0) (hfix : V A qStar = qStar)
    (hR : 0 < R) (hRq : R < qStar)
    (hderiv : ∀ y : ℝ, |y - qStar| ≤ R → |deriv (V A) y| ≤ κ)
    (hx : |x - qStar| ≤ R) :
    |V A x - qStar| ≤ κ * |x - qStar| := by
  have hxmem : x ∈ Set.Icc (qStar - R) (qStar + R) := by
    rw [abs_le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hqmem : qStar ∈ Set.Icc (qStar - R) (qStar + R) := by
    constructor <;> linarith [hR]
  have hdiff :
      ∀ y ∈ Set.Icc (qStar - R) (qStar + R),
        DifferentiableAt ℝ (V A) y := by
    intro y hy
    have hypos : 0 < y := by
      linarith [hy.1, hRq]
    exact (hasDerivAt_V hA hypos).differentiableAt
  have hbound :
      ∀ y ∈ Set.Icc (qStar - R) (qStar + R),
        ‖deriv (V A) y‖ ≤ κ := by
    intro y hy
    rw [Real.norm_eq_abs]
    apply hderiv y
    rw [abs_le]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hmv :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (qStar - R) (qStar + R)) hqmem hxmem
  simpa only [Real.norm_eq_abs, hfix] using hmv

/-- Split the deterministic squared error over a stable interval and its bad
complement, using contraction on the former and the unit bound on the latter. -/
lemma integral_sq_V_sub_fixed_le_sq_mul_integral_add_measureReal
    {A qStar κ R : ℝ}
    (hA : A ≠ 0) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hκ : 0 ≤ κ)
    (hR : 0 < R) (hRq : R < qStar)
    (hderiv : ∀ y : ℝ, |y - qStar| ≤ R → |deriv (V A) y| ≤ κ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hνsupport : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0) :
    ∫ q, (V A q - qStar) ^ 2 ∂ν ≤
      κ ^ 2 * ∫ q, (q - qStar) ^ 2 ∂ν +
        ν.real {q : ℝ | R < |q - qStar|} := by
  let D : ℝ → ℝ := fun q => (V A q - qStar) ^ 2
  let E : ℝ → ℝ := fun q => (q - qStar) ^ 2
  let B : Set ℝ := {q : ℝ | R < |q - qStar|}
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_lt measurable_const
      ((measurable_id.sub measurable_const).abs)
  have hDstrong : StronglyMeasurable D := by
    dsimp [D]
    exact (((V_continuous A).sub continuous_const).pow 2).stronglyMeasurable
  have hDbound : ∀ q : ℝ, D q ≤ 1 := by
    intro q
    have hdiff : |V A q - qStar| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        linarith [V_nonneg A q, V_lt_one A q, hqStar.1, hqStar.2]
    have hsq :=
      (sq_le_sq₀ (abs_nonneg (V A q - qStar)) zero_le_one).2 hdiff
    simpa only [D, sq_abs, one_pow] using hsq
  have hDint : Integrable D ν := by
    refine Integrable.of_bound hDstrong.aestronglyMeasurable 1 ?_
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [D]
      positivity)]
    exact hDbound q
  have hEstrong : StronglyMeasurable E := by
    dsimp [E]
    exact ((continuous_id.sub continuous_const).pow 2).stronglyMeasurable
  have hνIcc :
      ∀ᵐ q ∂ν, q ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hνsupport
  have hEint : Integrable E ν := by
    refine Integrable.of_bound hEstrong.aestronglyMeasurable 1 ?_
    filter_upwards [hνIcc] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [E]
      positivity)]
    have hdiff : |q - qStar| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hq.1, hq.2, hqStar.1, hqStar.2]
    have hsq :=
      (sq_le_sq₀ (abs_nonneg (q - qStar)) zero_le_one).2 hdiff
    simpa only [E, sq_abs, one_pow] using hsq
  have hstable (q : ℝ) (hq : |q - qStar| ≤ R) :
      D q ≤ κ ^ 2 * E q := by
    have hcontract :=
      abs_V_sub_fixed_le_mul_abs_sub_fixed_of_deriv_le
        hA hfix hR hRq hderiv hq
    have hsq :=
      (sq_le_sq₀ (abs_nonneg (V A q - qStar))
        (mul_nonneg hκ (abs_nonneg (q - qStar)))).2 hcontract
    simpa only [D, E, sq_abs, mul_pow] using hsq
  have hindicator :
      Integrable (B.indicator (fun _ : ℝ => (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ)).indicator hB
  have hκEint : Integrable (fun q => κ ^ 2 * E q) ν :=
    hEint.const_mul (κ ^ 2)
  have hrightint :
      Integrable
        (fun q => κ ^ 2 * E q + B.indicator (fun _ => (1 : ℝ)) q) ν :=
    hκEint.add hindicator
  have hpoint :
      D ≤ᵐ[ν] fun q => κ ^ 2 * E q +
        B.indicator (fun _ => (1 : ℝ)) q := by
    filter_upwards with q
    by_cases hq : |q - qStar| ≤ R
    · have hqB : q ∉ B := by
        dsimp [B]
        exact not_lt_of_ge hq
      rw [Set.indicator_of_notMem hqB, add_zero]
      exact hstable q hq
    · have hqB : q ∈ B := by
        dsimp [B]
        exact lt_of_not_ge hq
      rw [Set.indicator_of_mem hqB]
      exact (hDbound q).trans
        (le_add_of_nonneg_left
          (mul_nonneg (sq_nonneg κ) (by
            dsimp [E]
            positivity)))
  calc
    ∫ q, (V A q - qStar) ^ 2 ∂ν = ∫ q, D q ∂ν := by rfl
    _ ≤ ∫ q, (κ ^ 2 * E q +
          B.indicator (fun _ => (1 : ℝ)) q) ∂ν :=
      integral_mono_ae hDint hrightint hpoint
    _ = κ ^ 2 * ∫ q, E q ∂ν + ν.real B := by
      rw [integral_add hκEint hindicator, integral_const_mul,
        integral_indicator_const, smul_eq_mul, mul_one]
      exact hB
    _ = κ ^ 2 * ∫ q, (q - qStar) ^ 2 ∂ν +
        ν.real {q : ℝ | R < |q - qStar|} := by rfl

/-- The centered unrounded empirical Gaussian radius update has the exact
Hoeffding sub-Gaussian parameter `1 / (4N)`. -/
lemma hasSubgaussianMGF_Fmap_sub_V
    {A q : ℝ} {N : ℕ} (hN : 0 < N) :
    HasSubgaussianMGF
      (fun g : Fin N → ℝ => Fmap A N q g - V A q)
      (FmapSubgaussianParameter N) (gaussianVec N) := by
  let X : Fin N → (Fin N → ℝ) → ℝ :=
    fun i g => Real.tanh (A * Real.sqrt q * g i) ^ 2
  have hXmean (i : Fin N) :
      ∫ g, X i g ∂(gaussianVec N) = V A q := by
    have hpm :
        (gaussianVec N).map (Function.eval i) = gaussianReal 0 1 := by
      unfold gaussianVec
      rw [Measure.pi_map_eval]
      simp
    have hf :
        AEStronglyMeasurable
          (fun x : ℝ => Real.tanh (A * Real.sqrt q * x) ^ 2)
          ((gaussianVec N).map (Function.eval i)) :=
      ((continuous_tanh.comp (by fun_prop)).pow 2).aestronglyMeasurable
    have hφ :
        AEMeasurable (Function.eval i) (gaussianVec N) :=
      (measurable_pi_apply i).aemeasurable
    have hmap := integral_map hφ hf
    rw [hpm] at hmap
    exact hmap.symm
  have hXsub (i : Fin N) :
      HasSubgaussianMGF
        (fun g => X i g - V A q)
        ((‖(1 : ℝ)‖₊ / 2) ^ 2) (gaussianVec N) := by
    have hXMeas :
        AEMeasurable (X i) (gaussianVec N) :=
      ((continuous_tanh.comp (by fun_prop)).pow 2).measurable.aemeasurable
    have hXBounds :
        ∀ᵐ g ∂(gaussianVec N), X i g ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards with g
      exact ⟨sq_nonneg _, (Real.tanh_sq_lt_one _).le⟩
    have hsubG :=
      hasSubgaussianMGF_of_mem_Icc hXMeas hXBounds
    rw [hXmean i] at hsubG
    simpa only [X, sub_zero] using hsubG
  have hindep :
      iIndepFun (fun i g => X i g - V A q) (gaussianVec N) := by
    have hEval :
        iIndepFun (fun i (g : Fin N → ℝ) => g i) (gaussianVec N) := by
      unfold gaussianVec
      exact iIndepFun_pi fun _ => aemeasurable_id
    have hcomp := hEval.comp
      (fun _ x => Real.tanh (A * Real.sqrt q * x) ^ 2 - V A q)
      (fun _ => ((continuous_tanh.comp (by fun_prop)).pow 2).measurable.sub
        measurable_const)
    change iIndepFun
      (fun i =>
        (fun x => Real.tanh (A * Real.sqrt q * x) ^ 2 - V A q) ∘
          (fun g : Fin N → ℝ => g i))
      (gaussianVec N)
    exact hcomp
  have hsum :
      HasSubgaussianMGF
        (fun g : Fin N → ℝ => ∑ i, (X i g - V A q))
        (∑ _i : Fin N, ((‖(1 : ℝ)‖₊ / 2) ^ 2))
        (gaussianVec N) := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun
      hindep (s := Finset.univ) (fun i _ => hXsub i)
  have hscaled := hsum.const_mul ((N : ℝ)⁻¹)
  change HasSubgaussianMGF _ (FmapSubgaussianParameter N)
    (gaussianVec N) at hscaled
  apply hscaled.congr
  filter_upwards with g
  unfold Fmap
  simp only [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, X]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- The unrounded empirical Gaussian radius update is exponentially
concentrated about the deterministic mean map, uniformly in the input radius. -/
lemma measureReal_abs_Fmap_sub_V_gt_le
    {A q ε : ℝ} {N : ℕ} (hN : 0 < N) (hε : 0 < ε) :
    (gaussianVec N).real
        {g : Fin N → ℝ | |Fmap A N q g - V A q| > ε} ≤
      2 * Real.exp (-2 * N * ε ^ 2) := by
  let X := fun g : Fin N → ℝ => Fmap A N q g - V A q
  have hsub :
      HasSubgaussianMGF X (FmapSubgaussianParameter N) (gaussianVec N) := by
    simpa only [X] using hasSubgaussianMGF_Fmap_sub_V (A := A) (q := q) hN
  have hupper :
      (gaussianVec N).real {g : Fin N → ℝ | ε ≤ X g} ≤
        Real.exp (-2 * N * ε ^ 2) := by
    calc
      _ ≤ Real.exp
          (-ε ^ 2 / (2 * FmapSubgaussianParameter N)) :=
        hsub.measure_ge_le hε.le
      _ = _ := by
        congr 1
        rw [coe_FmapSubgaussianParameter hN]
        have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        field_simp
        ring
  have hlower :
      (gaussianVec N).real {g : Fin N → ℝ | X g ≤ -ε} ≤
        Real.exp (-2 * N * ε ^ 2) := by
    have hset :
        {g : Fin N → ℝ | X g ≤ -ε} =
          {g : Fin N → ℝ | ε ≤ -X g} := by
      ext g
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hg <;> linarith
    rw [hset]
    calc
      _ ≤ Real.exp
          (-ε ^ 2 / (2 * FmapSubgaussianParameter N)) :=
        hsub.neg.measure_ge_le hε.le
      _ = _ := by
        congr 1
        rw [coe_FmapSubgaussianParameter hN]
        have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        field_simp
        ring
  have hevent :
      {g : Fin N → ℝ | |X g| > ε} =
        {g : Fin N → ℝ | X g < -ε} ∪
          {g : Fin N → ℝ | ε < X g} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hg
      by_cases hx : 0 ≤ X g
      · right
        simpa [abs_of_nonneg hx] using hg
      · left
        have hxneg : X g < 0 := lt_of_not_ge hx
        rw [abs_of_neg hxneg] at hg
        linarith
    · rintro (hg | hg)
      · have hxneg : X g < 0 := hg.trans (neg_neg_of_pos hε)
        rw [abs_of_neg hxneg]
        linarith
      · have hxpos : 0 < X g := hε.trans hg
        simpa [abs_of_pos hxpos] using hg
  have hlowerMono :
      (gaussianVec N).real {g : Fin N → ℝ | X g < -ε} ≤
        (gaussianVec N).real {g : Fin N → ℝ | X g ≤ -ε} := by
    apply measureReal_mono
    · intro g hg
      change X g < -ε at hg
      change X g ≤ -ε
      exact hg.le
    · exact measure_ne_top _ _
  have hupperMono :
      (gaussianVec N).real {g : Fin N → ℝ | ε < X g} ≤
        (gaussianVec N).real {g : Fin N → ℝ | ε ≤ X g} := by
    apply measureReal_mono
    · intro g hg
      change ε < X g at hg
      change ε ≤ X g
      exact hg.le
    · exact measure_ne_top _ _
  rw [show
    {g : Fin N → ℝ | |Fmap A N q g - V A q| > ε} =
      {g : Fin N → ℝ | |X g| > ε} by rfl, hevent]
  calc
    _ ≤ (gaussianVec N).real {g : Fin N → ℝ | X g < -ε} +
        (gaussianVec N).real {g : Fin N → ℝ | ε < X g} :=
      measureReal_union_le _ _
    _ ≤ (gaussianVec N).real {g : Fin N → ℝ | X g ≤ -ε} +
        (gaussianVec N).real {g : Fin N → ℝ | ε ≤ X g} :=
      add_le_add hlowerMono hupperMono
    _ ≤ Real.exp (-2 * N * ε ^ 2) +
        Real.exp (-2 * N * ε ^ 2) :=
      add_le_add hlower hupper
    _ = _ := by ring

/-- Kernel form of the unrounded one-step Hoeffding estimate. -/
lemma Kchain_measureReal_abs_sub_V_gt_le
    {A q ε : ℝ} {N : ℕ} (hN : 0 < N) (hε : 0 < ε) :
    (Kchain A N q).real {y : ℝ | |y - V A q| > ε} ≤
      2 * Real.exp (-2 * N * ε ^ 2) := by
  rw [Kchain_apply, measureReal_def,
    Measure.map_apply (continuous_Fmap_right A N q).measurable
      (measurableSet_lt measurable_const
        (measurable_id.sub measurable_const).abs :
        MeasurableSet {y : ℝ | |y - V A q| > ε})]
  exact measureReal_abs_Fmap_sub_V_gt_le hN hε

/-- Every positive-time coordinate of a canonical unrounded radius path lies
in `[0,1]` almost surely. -/
lemma markovPathMeasure_ae_eval_succ_mem_Kchain_Icc
    {A : ℝ} {N : ℕ} (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure μ₀ (Kchain A N)),
      ω (t + 1) ∈ Set.Icc (0 : ℝ) 1 := by
  have hzero : ∀ a : ℝ,
      Kchain A N a ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
    fun a => Kchain_apply_Icc_compl A hN a
  rw [ae_iff]
  have hset :
      {ω : ℕ → ℝ | ω (t + 1) ∉ Set.Icc (0 : ℝ) 1} =
        (fun ω : ℕ → ℝ => ω (t + 1)) ⁻¹'
          (Set.Icc (0 : ℝ) 1)ᶜ := rfl
  rw [show {ω : ℕ → ℝ | ¬ω (t + 1) ∈ Set.Icc (0 : ℝ) 1} =
      {ω : ℕ → ℝ | ω (t + 1) ∉ Set.Icc (0 : ℝ) 1} by rfl,
    hset, ← Measure.map_apply (measurable_pi_apply (t + 1))
      measurableSet_Icc.compl,
    markovPathMeasure_map_eval_succ,
    Measure.bind_apply measurableSet_Icc.compl
      (Kchain A N).aemeasurable]
  simp only [hzero, lintegral_zero]

/-- A canonical unrounded radius path started in `[0,1]` remains there at
every fixed time almost surely. -/
lemma markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc
    {A q : ℝ} {N : ℕ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hN : 0 < N) (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
      ω t ∈ Set.Icc (0 : ℝ) 1 := by
  cases t with
  | zero =>
      have hω0 :
          ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
            ω 0 = q := by
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
      filter_upwards [hω0] with ω hω
      simpa only [hω] using hq
  | succ t =>
      exact markovPathMeasure_ae_eval_succ_mem_Kchain_Icc
        hN (Measure.dirac q) t

/-- Through every fixed horizon, all coordinates of a canonical unrounded
radius path started in `[0,1]` remain there almost surely. -/
lemma markovPathMeasure_dirac_ae_forall_le_mem_Kchain_Icc
    {A q : ℝ} {N : ℕ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hN : 0 < N) (T : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
      ∀ s ≤ T, ω s ∈ Set.Icc (0 : ℝ) 1 := by
  have hfin :
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
        ∀ s ∈ Finset.range (T + 1),
          ω s ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Filter.eventually_all_finset]
    intro s _hs
    exact markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc hq hN s
  filter_upwards [hfin] with ω hω
  intro s hsT
  exact hω s (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hsT))

/-- Under the canonical unrounded path law, every transition obeys the same
Hoeffding bound as the state-dependent kernel. -/
lemma markovPathMeasure_measureReal_abs_next_sub_V_gt_le
    {A q ε : ℝ} {N : ℕ} (hN : 0 < N) (hε : 0 < ε) (t : ℕ) :
    (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
        {ω : ℕ → ℝ | |ω (t + 1) - V A (ω t)| > ε} ≤
      2 * Real.exp (-2 * N * ε ^ 2) := by
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac q) (Kchain A N)
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
      (Measure.dirac q) (Kchain A N) t hψ hψint
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

/-- The event that an unrounded radius transition deviates from its
conditional mean somewhere in the first `T` steps. -/
def finiteHorizonKchainStepDeviationEvent
    (A ε : ℝ) (T : ℕ) : Set (ℕ → ℝ) :=
  ⋃ s ∈ Finset.range T,
    {ω : ℕ → ℝ | |ω (s + 1) - V A (ω s)| > ε}

/-- A union bound upgrades the unrounded one-step Hoeffding estimate to every
transition in a fixed finite horizon. -/
lemma markovPathMeasure_measureReal_finiteHorizonKchainStepDeviationEvent_le
    {A q ε : ℝ} {N T : ℕ} (hN : 0 < N) (hε : 0 < ε) :
    (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
        (finiteHorizonKchainStepDeviationEvent A ε T) ≤
      2 * T * Real.exp (-2 * N * ε ^ 2) := by
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac q) (Kchain A N)
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
      exact markovPathMeasure_measureReal_abs_next_sub_V_gt_le
        hN hε s
    _ = 2 * T * Real.exp (-2 * N * ε ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, b]
      ring

/-- At every fixed horizon, one positive step tolerance makes all
`[0,1]`-valued perturbed paths uniformly track the deterministic `V` orbit. -/
lemma exists_pos_uniform_V_tracking_tolerance
    (A : ℝ) (T : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℕ → ℝ,
        x 0 = q →
        (∀ s ≤ T, x s ∈ Set.Icc (0 : ℝ) 1) →
        (∀ s < T, |x (s + 1) - V A (x s)| ≤ δ) →
        |x T - (V A)^[T] q| < η := by
  induction T generalizing η with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro q _hq x hx0 _hxmem _hnoise
      simpa only [Function.iterate_zero_apply, hx0, sub_self, abs_zero]
        using hη
  | succ T ih =>
      have huc :
          UniformContinuousOn (V A) (Set.Icc (0 : ℝ) 1) :=
        isCompact_Icc.uniformContinuousOn_of_continuous
          (V_continuous A).continuousOn
      obtain ⟨γ, hγ, hcontrol⟩ :=
        (Metric.uniformContinuousOn_iff.mp huc)
          (η / 2) (half_pos hη)
      obtain ⟨δ₀, hδ₀, htrack⟩ := ih hγ
      refine ⟨min δ₀ (η / 2), lt_min hδ₀ (half_pos hη), ?_⟩
      intro q hq x hx0 hxmem hnoise
      have horbit : ∀ n : ℕ, (V A)^[n] q ∈ Set.Icc (0 : ℝ) 1 := by
        intro n
        induction n with
        | zero => simpa using hq
        | succ n hn =>
            rw [Function.iterate_succ_apply']
            exact ⟨V_nonneg A ((V A)^[n] q),
              (V_lt_one A ((V A)^[n] q)).le⟩
      have hprev : |x T - (V A)^[T] q| < γ := by
        apply htrack q hq x hx0
        · intro s hs
          exact hxmem s (hs.trans (Nat.le_succ T))
        · intro s hs
          exact (hnoise s (hs.trans_le (Nat.le_succ T))).trans
            (min_le_left _ _)
      have hmap :
          |V A (x T) - V A ((V A)^[T] q)| < η / 2 := by
        have hdist : dist (x T) ((V A)^[T] q) < γ := by
          simpa only [Real.dist_eq] using hprev
        simpa only [Real.dist_eq] using
          hcontrol (x T) (hxmem T (Nat.le_succ T))
            ((V A)^[T] q) (horbit T) hdist
      rw [Function.iterate_succ_apply']
      calc
        |x (T + 1) - V A ((V A)^[T] q)| =
            |(x (T + 1) - V A (x T)) +
              (V A (x T) - V A ((V A)^[T] q))| := by
                congr 1
                ring
        _ ≤ |x (T + 1) - V A (x T)| +
              |V A (x T) - V A ((V A)^[T] q)| :=
          abs_add_le _ _
        _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt
          ((hnoise T (Nat.lt_succ_self T)).trans (min_le_right _ _)) hmap
        _ = η := by ring

/-- Through every fixed horizon, a canonical unrounded path tracks its
deterministic orbit with exponentially high probability. -/
lemma exists_pos_markovPathMeasure_measureReal_abs_sub_iterate_V_ge_le
    (A : ℝ) (T : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, 0 < N → ∀ q ∈ Set.Icc (0 : ℝ) 1,
        (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
            {ω : ℕ → ℝ | η ≤ |ω T - (V A)^[T] q|} ≤
          2 * T * Real.exp (-2 * N * δ ^ 2) := by
  obtain ⟨δ, hδ, htrack⟩ :=
    exists_pos_uniform_V_tracking_tolerance A T hη
  refine ⟨δ, hδ, ?_⟩
  intro N hN q hq
  let μ : Measure (ℕ → ℝ) :=
    markovPathMeasure (Measure.dirac q) (Kchain A N)
  let E : Set (ℕ → ℝ) :=
    {ω | η ≤ |ω T - (V A)^[T] q|}
  let B : Set (ℕ → ℝ) :=
    finiteHorizonKchainStepDeviationEvent A δ T
  have hω0 :
      ∀ᵐ ω ∂μ, ω 0 = q := by
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
  have hωmem :
      ∀ᵐ ω ∂μ, ∀ s ≤ T, ω s ∈ Set.Icc (0 : ℝ) 1 := by
    exact markovPathMeasure_dirac_ae_forall_le_mem_Kchain_Icc hq hN T
  have hsubset : E ≤ᵐ[μ] B := by
    filter_upwards [hω0, hωmem] with ω hω0 hωmem
    intro hterminal
    by_contra hnotBad
    have hnoise :
        ∀ s < T, |ω (s + 1) - V A (ω s)| ≤ δ := by
      intro s hs
      apply le_of_not_gt
      intro hlarge
      apply hnotBad
      change ω ∈ finiteHorizonKchainStepDeviationEvent A δ T
      simp only [finiteHorizonKchainStepDeviationEvent,
        Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨s, Finset.mem_range.mpr hs, hlarge⟩
    have hterminalLt :=
      htrack q hq ω hω0 hωmem hnoise
    exact (not_le_of_gt hterminalLt) hterminal
  have hreal : μ.real E ≤ μ.real B := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ B)
      (measure_mono_ae hsubset)
  exact hreal.trans <|
    markovPathMeasure_measureReal_finiteHorizonKchainStepDeviationEvent_le
      hN hδ

/-- Uniform canonical-path entrance into the deterministic stable interval
has exponentially small failure probability. -/
theorem exists_uniform_markovPathMeasure_stable_entrance_exp_bound
    {A qStar r : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hr : r ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ κ R η : ℝ, ∃ m : ℕ, ∃ C c : ℝ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C ∧ 0 < c ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
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
    dsimp [C]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨κ, R, η, m, C, c, hκ0, hκ1, hη0, hηR, hRinterior,
    hC, hc, hderiv, ?_⟩
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
          |ω m - (V A)^[m] q| + |(V A)^[m] q - qStar| := by
      calc
        |ω m - qStar| =
            |(ω m - (V A)^[m] q) + ((V A)^[m] q - qStar)| := by
              congr 1
              ring
        _ ≤ _ := abs_add_le _ _
    linarith [hentry q hq]
  calc
    (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
          {ω : ℕ → ℝ | R < |ω m - qStar|}
        ≤ (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
            {ω : ℕ → ℝ | η ≤ |ω m - (V A)^[m] q|} :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ 2 * m * Real.exp (-2 * N * δ ^ 2) :=
      htrack N hN q hqIcc
    _ ≤ C * Real.exp (-(c * (N : ℝ))) := by
      dsimp [C, c]
      rw [show -(2 * δ ^ 2 * (N : ℝ)) =
          -2 * (N : ℝ) * δ ^ 2 by ring]
      gcongr
      norm_num

/-- The common fixed-time stable entrance estimate in `m`-step kernel form. -/
theorem exists_uniform_Kchain_pow_stable_entrance_exp_bound
    {A qStar r : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hr : r ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ κ R η : ℝ, ∃ m : ℕ, ∃ C c : ℝ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C ∧ 0 < c ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ N : ℕ, 0 < N → ∀ q ∈ Set.Icc r 1,
        (((Kchain A N) ^ m) q).real
            {y : ℝ | R < |y - qStar|} ≤
          C * Real.exp (-(c * (N : ℝ))) := by
  obtain ⟨κ, R, η, m, C, c, hκ0, hκ1, hη0, hηR,
      hRinterior, hC, hc, hderiv, hpath⟩ :=
    exists_uniform_markovPathMeasure_stable_entrance_exp_bound
      hA hqStar hfix hr
  refine ⟨κ, R, η, m, C, c, hκ0, hκ1, hη0, hηR,
    hRinterior, hC, hc, hderiv, ?_⟩
  intro N hN q hq
  have hset : MeasurableSet {y : ℝ | R < |y - qStar|} :=
    measurableSet_lt measurable_const
      ((measurable_id.sub measurable_const).abs)
  have hpre :
      (fun ω : ℕ → ℝ => ω m) ⁻¹' {y : ℝ | R < |y - qStar|} =
        {ω : ℕ → ℝ | R < |ω m - qStar|} := rfl
  rw [measureReal_def,
    ← markovPathMeasure_dirac_map_eval q (Kchain A N) m,
    Measure.map_apply (measurable_pi_apply m) hset, hpre]
  simpa only [measureReal_def] using hpath N hN q hq

/-- Split an invariant target probability into mass on a bad starting set and
a uniform iterate bound from its complement. -/
lemma invariant_measureReal_le_add_of_ae_kernel_pow_measureReal_le
    {α : Type*} [MeasurableSpace α]
    {κ : Kernel α α} [IsMarkovKernel κ]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (hμ : Kernel.Invariant κ μ) {S B : Set α}
    (hS : MeasurableSet S) (hB : MeasurableSet B)
    (m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hbound : ∀ᵐ x ∂μ, x ∉ B → ((κ ^ m) x).real S ≤ p) :
    μ.real S ≤ μ.real B + p := by
  let f : α → ℝ := fun x => ((κ ^ m) x).real S
  have hkmeas : Measurable (fun x => (κ ^ m) x S) :=
    (κ ^ m).measurable_coe hS
  have hfmeas : Measurable f :=
    hkmeas.ennreal_toReal
  have hflt : ∀ x : α, (κ ^ m) x S < ⊤ :=
    fun x => lt_top_iff_ne_top.mpr (measure_ne_top _ _)
  have hinvariant :
      μ.real S = ∫ x, f x ∂μ := by
    calc
      μ.real S = (((κ ^ m) ∘ₘ μ).real S) :=
        congrArg (fun ν : Measure α => ν.real S)
          (invariant_pow hμ m).def.symm
      _ = ∫ x, f x ∂μ := by
        rw [measureReal_def,
          Measure.bind_apply hS (κ ^ m).aemeasurable,
          ← integral_toReal hkmeas.aemeasurable
            (Filter.Eventually.of_forall hflt)]
        rfl
  have hfint : Integrable f μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      hfmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
    exact measureReal_le_one
  have hindicator :
      Integrable (B.indicator (fun _ : α => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hpint : Integrable (fun _ : α => p) μ :=
    integrable_const p
  have hgint :
      Integrable
        (fun x : α => B.indicator (fun _ => (1 : ℝ)) x + p) μ :=
    hindicator.add hpint
  have hpoint :
      f ≤ᵐ[μ] fun x : α => B.indicator (fun _ => (1 : ℝ)) x + p := by
    filter_upwards [hbound] with x hx
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem hxB]
      exact measureReal_le_one.trans (le_add_of_nonneg_right hp)
    · rw [Set.indicator_of_notMem hxB, zero_add]
      exact hx hxB
  calc
    μ.real S = ∫ x, f x ∂μ := hinvariant
    _ ≤ ∫ x, (B.indicator (fun _ => (1 : ℝ)) x + p) ∂μ :=
      integral_mono_ae hfint hgint hpoint
    _ = μ.real B + p := by
      rw [integral_add hindicator hpint, integral_indicator_const,
        smul_eq_mul, mul_one,
        integral_const, probReal_univ, one_smul]
      exact hB

/-- A sum of two exponential errors is bounded by their combined coefficient
at the slower of the two rates. -/
lemma add_mul_exp_neg_le_mul_add_exp_neg_min
    {C₀ c₀ C₁ c₁ n : ℝ}
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hn : 0 ≤ n) :
    C₀ * Real.exp (-(c₀ * n)) + C₁ * Real.exp (-(c₁ * n)) ≤
      (C₀ + C₁) * Real.exp (-(min c₀ c₁ * n)) := by
  have harg₀ : -(c₀ * n) ≤ -(min c₀ c₁ * n) := by
    linarith [mul_le_mul_of_nonneg_right (min_le_left c₀ c₁) hn]
  have harg₁ : -(c₁ * n) ≤ -(min c₀ c₁ * n) := by
    linarith [mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) hn]
  calc
    C₀ * Real.exp (-(c₀ * n)) + C₁ * Real.exp (-(c₁ * n))
        ≤ C₀ * Real.exp (-(min c₀ c₁ * n)) +
            C₁ * Real.exp (-(min c₀ c₁ * n)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg₀) hC₀)
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg₁) hC₁)
    _ = (C₀ + C₁) * Real.exp (-(min c₀ c₁ * n)) := by ring

/-- In every sufficiently large dimension, a stationary origin-free radius
law has exponentially small mass outside one stable interval, up to the sum
of the near-zero and finite-time entrance estimates. -/
theorem exists_eventually_invariant_Kchain_stable_interval_le_exp_add
    {A qStar : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ R η r C₀ c₀ C₁ c₁ : ℝ, ∃ N₀ : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < r ∧ r ≤ 1 ∧
      0 < C₀ ∧ 0 < c₀ ∧ 0 < C₁ ∧ 0 < c₁ ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∃ ν : ProbabilityMeasure ℝ,
          Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
          (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
          (ν : Measure ℝ) ({0} : Set ℝ) = 0 ∧
          (ν : Measure ℝ).real {y : ℝ | R < |y - qStar|} ≤
            C₀ * Real.exp (-(c₀ * (N : ℝ))) +
              C₁ * Real.exp (-(c₁ * (N : ℝ))) := by
  let R₀ : ℝ := qStar / 2
  have hR₀ : R₀ ∈ Set.Ioo (0 : ℝ) qStar := by
    dsimp [R₀]
    constructor <;> linarith [hqStar.1]
  obtain ⟨r, C₀, c₀, N₀, hr, hC₀, hc₀, hsmall⟩ :=
    exists_eventually_invariant_Kchain_small_ball_le_exp
      hA hqStar hR₀
  have hr_one : r ≤ 1 := by
    dsimp [R₀] at hr
    linarith [hr.2, hqStar.2]
  obtain ⟨κ, R, η, m, C₁, c₁, hκ0, hκ1, hη0, hηR,
      hRinterior, hC₁, hc₁, hderiv, hentrance⟩ :=
    exists_uniform_Kchain_pow_stable_entrance_exp_bound
      hA hqStar hfix ⟨hr.1, hr_one⟩
  refine ⟨κ, R, η, r, C₀, c₀, C₁, c₁, max N₀ 1,
    hκ0, hκ1, hη0, hηR, hRinterior, hr.1, hr_one,
    hC₀, hc₀, hC₁, hc₁, hderiv, ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (Nat.le_max_left N₀ 1).trans hN
  have hNpos : 0 < N := Nat.zero_lt_of_lt <|
    (Nat.le_max_right N₀ 1).trans hN
  obtain ⟨ν, hν, hνsupport, hν0, hνsmall⟩ := hsmall N hN₀
  refine ⟨ν, hν, hνsupport, hν0, ?_⟩
  have hS : MeasurableSet {y : ℝ | R < |y - qStar|} :=
    measurableSet_lt measurable_const
      ((measurable_id.sub measurable_const).abs)
  have hνIcc :
      ∀ᵐ q ∂(ν : Measure ℝ), q ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact hνsupport
  have hνne : ∀ᵐ q ∂(ν : Measure ℝ), q ≠ 0 := by
    rw [ae_iff]
    simpa using hν0
  have hbound :
      ∀ᵐ q ∂(ν : Measure ℝ), q ∉ Set.Ioc (0 : ℝ) r →
        (((Kchain A N) ^ m) q).real
            {y : ℝ | R < |y - qStar|} ≤
          C₁ * Real.exp (-(c₁ * (N : ℝ))) := by
    filter_upwards [hνIcc, hνne] with q hq hq0
    intro hqsmall
    apply hentrance N hNpos q
    refine ⟨?_, hq.2⟩
    by_contra hrq
    apply hqsmall
    exact
      ⟨lt_of_le_of_ne hq.1 (Ne.symm hq0),
        (lt_of_not_ge hrq).le⟩
  have hsplit :=
    invariant_measureReal_le_add_of_ae_kernel_pow_measureReal_le
      hν hS measurableSet_Ioc m
      (mul_nonneg hC₁.le (Real.exp_pos _).le) hbound
  exact hsplit.trans (add_le_add_left hνsmall _)

/-- In every sufficiently large dimension, a stationary origin-free radius
law is exponentially localized in one stable interval about the positive
fixed point. -/
theorem exists_eventually_invariant_Kchain_stable_interval_le_exp
    {A qStar : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ R η C c : ℝ, ∃ N₀ : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C ∧ 0 < c ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∃ ν : ProbabilityMeasure ℝ,
          Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
          (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
          (ν : Measure ℝ) ({0} : Set ℝ) = 0 ∧
          (ν : Measure ℝ).real {y : ℝ | R < |y - qStar|} ≤
            C * Real.exp (-(c * (N : ℝ))) := by
  obtain ⟨κ, R, η, _r, C₀, c₀, C₁, c₁, N₀,
      hκ0, hκ1, hη0, hηR, hRinterior, _hr0, _hr1,
      hC₀, hc₀, hC₁, hc₁, hderiv, hlocalization⟩ :=
    exists_eventually_invariant_Kchain_stable_interval_le_exp_add
      hA hqStar hfix
  let C : ℝ := C₀ + C₁
  let c : ℝ := min c₀ c₁
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min hc₀ hc₁
  refine ⟨κ, R, η, C, c, N₀, hκ0, hκ1, hη0, hηR,
    hRinterior, hC, hc, hderiv, ?_⟩
  intro N hN
  obtain ⟨ν, hν, hνsupport, hν0, hνlocalization⟩ :=
    hlocalization N hN
  refine ⟨ν, hν, hνsupport, hν0, hνlocalization.trans ?_⟩
  simpa only [C, c] using
    (add_mul_exp_neg_le_mul_add_exp_neg_min
      hC₀.le hC₁.le (Nat.cast_nonneg N))

/-- The exponential stationary localization estimate implies the paper's
weaker `N⁻¹` localization bound after enlarging its coefficient. -/
theorem exists_eventually_invariant_Kchain_stable_interval_le_inv_nat
    {A qStar : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ R η C : ℝ, ∃ N₀ : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∃ ν : ProbabilityMeasure ℝ,
          Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
          (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
          (ν : Measure ℝ) ({0} : Set ℝ) = 0 ∧
          (ν : Measure ℝ).real {y : ℝ | R < |y - qStar|} ≤
            C / (N : ℝ) := by
  obtain ⟨κ, R, η, C₀, c, N₀, hκ0, hκ1, hη0, hηR,
      hRinterior, hC₀, hc, hderiv, hlocalization⟩ :=
    exists_eventually_invariant_Kchain_stable_interval_le_exp
      hA hqStar hfix
  let C : ℝ := C₀ / c
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos hC₀ hc
  refine ⟨κ, R, η, C, max N₀ 1, hκ0, hκ1, hη0, hηR,
    hRinterior, hC, hderiv, ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (Nat.le_max_left N₀ 1).trans hN
  have hNpos : 0 < N :=
    Nat.zero_lt_of_lt ((Nat.le_max_right N₀ 1).trans hN)
  obtain ⟨ν, hν, hνsupport, hν0, hνlocalization⟩ :=
    hlocalization N hN₀
  refine ⟨ν, hν, hνsupport, hν0, hνlocalization.trans ?_⟩
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcN : 0 < c * (N : ℝ) := mul_pos hc hNreal
  have hcNle : c * (N : ℝ) ≤ Real.exp (c * (N : ℝ)) := by
    exact (le_add_of_nonneg_right zero_le_one).trans
      (Real.add_one_le_exp (c * (N : ℝ)))
  have hexp :
      Real.exp (-(c * (N : ℝ))) ≤ (c * (N : ℝ))⁻¹ := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le hcN hcNle)
  calc
    C₀ * Real.exp (-(c * (N : ℝ)))
        ≤ C₀ * (c * (N : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hexp hC₀.le
    _ = C / (N : ℝ) := by
      dsimp [C]
      field_simp

/-- In every sufficiently large dimension, the selected stationary radius law
has fixed-point second moment of order `N⁻¹`. -/
theorem exists_eventually_invariant_Kchain_integral_sq_sub_fixed_le_inv_nat
    {A qStar : ℝ} (hA : 1 < A)
    (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ R η C : ℝ, ∃ N₀ : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < C ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∃ ν : ProbabilityMeasure ℝ,
          Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
          (ν : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 ∧
          (ν : Measure ℝ) ({0} : Set ℝ) = 0 ∧
          (∫ q, (q - qStar) ^ 2 ∂(ν : Measure ℝ)) ≤
            C / (N : ℝ) := by
  obtain ⟨κ, R, η, Cbad, N₀, hκ0, hκ1, hη0, hηR,
      hRinterior, hCbad, hderiv, hlocalization⟩ :=
    exists_eventually_invariant_Kchain_stable_interval_le_inv_nat
      hA hqStar hfix
  have hκsq : κ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hκ0 zero_le_one).2 hκ1
  have hden : 0 < 1 - κ ^ 2 := sub_pos.mpr hκsq
  let C : ℝ := (Cbad + 1 / 4) / (1 - κ ^ 2)
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (add_pos hCbad (by norm_num)) hden
  refine ⟨κ, R, η, C, max N₀ 1, hκ0, hκ1, hη0, hηR,
    hRinterior, hC, hderiv, ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (Nat.le_max_left N₀ 1).trans hN
  have hNpos : 0 < N :=
    Nat.zero_lt_of_lt ((Nat.le_max_right N₀ 1).trans hN)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨ν, hν, hνsupport, hν0, hνbad⟩ :=
    hlocalization N hN₀
  let M : ℝ :=
    ∫ q, (q - qStar) ^ 2 ∂(ν : Measure ℝ)
  have hnoise :
      M ≤ (∫ q, (V A q - qStar) ^ 2 ∂(ν : Measure ℝ)) +
        1 / (4 * (N : ℝ)) := by
    dsimp [M]
    exact invariant_integral_sq_sub_fixed_le_integral_sq_V_add
      hNpos hqStar (ν : Measure ℝ) hν hνsupport
  have hdet :
      (∫ q, (V A q - qStar) ^ 2 ∂(ν : Measure ℝ)) ≤
        κ ^ 2 * M +
          (ν : Measure ℝ).real {q : ℝ | R < |q - qStar|} := by
    dsimp [M]
    exact integral_sq_V_sub_fixed_le_sq_mul_integral_add_measureReal
      (ne_of_gt (zero_lt_one.trans hA)) hqStar hfix hκ0
      (hη0.trans hηR) (hRinterior.trans_le (min_le_left _ _))
      hderiv (ν : Measure ℝ) hνsupport
  have hrec :
      M ≤ κ ^ 2 * M + (Cbad + 1 / 4) / (N : ℝ) := by
    calc
      M ≤ (∫ q, (V A q - qStar) ^ 2 ∂(ν : Measure ℝ)) +
          1 / (4 * (N : ℝ)) := hnoise
      _ ≤ (κ ^ 2 * M +
            (ν : Measure ℝ).real {q : ℝ | R < |q - qStar|}) +
          1 / (4 * (N : ℝ)) := by
        gcongr
      _ ≤ (κ ^ 2 * M + Cbad / (N : ℝ)) +
          1 / (4 * (N : ℝ)) := by
        gcongr
      _ = κ ^ 2 * M + (Cbad + 1 / 4) / (N : ℝ) := by
        field_simp [ne_of_gt hNreal]
        ring
  refine ⟨ν, hν, hνsupport, hν0, ?_⟩
  have htarget :
      C / (N : ℝ) =
        ((Cbad + 1 / 4) / (N : ℝ)) / (1 - κ ^ 2) := by
    dsimp [C]
    field_simp [ne_of_gt hNreal, ne_of_gt hden]
  rw [htarget, le_div_iff₀ hden]
  nlinarith [hrec]

/-- Under the explicit finite-dimensional supercritical criterion, there is a
unique invariant probability for `Kchain` having no atom at the origin. -/
theorem exists_unique_invariant_probability_Kchain_of_apply_singleton_zero
    {A : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N) :
    ∃! ν : ProbabilityMeasure ℝ,
      Kernel.Invariant (Kchain A N) (ν : Measure ℝ) ∧
      (ν : Measure ℝ) ({0} : Set ℝ) = 0 := by
  obtain ⟨ν, hν, hνsupport, hν0⟩ :=
    exists_invariant_Kchain_apply_singleton_zero_of_dimension hA hN hdim
  refine ⟨ν, ⟨hν, hν0⟩, ?_⟩
  intro μ hμ
  apply ProbabilityMeasure.toMeasure_injective
  have hμsupport :
      (μ : Measure ℝ) ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
    invariant_Kchain_apply_Icc_compl A (Nat.zero_lt_of_lt hN) (μ : Measure ℝ) hμ.1
  have hμ0lt : (μ : Measure ℝ) ({0} : Set ℝ) < 1 := by
    rw [hμ.2]
    exact zero_lt_one
  have hν0lt : (ν : Measure ℝ) ({0} : Set ℝ) < 1 := by
    rw [hν0]
    exact zero_lt_one
  have hparts :=
    nonzeroPart_eq_of_invariant_Kchain (zero_lt_one.trans hA)
      (Nat.zero_lt_of_lt hN) (μ : Measure ℝ) (ν : Measure ℝ)
      hμ.1 hν hμsupport hνsupport hμ0lt hν0lt
  rw [nonzeroPart_eq_self_of_apply_singleton_zero _ hμ.2,
    nonzeroPart_eq_self_of_apply_singleton_zero _ hν0] at hparts
  exact hparts

/-- Any two supported, nontrivial invariant squared-radius probabilities
reconstruct the same nonzero invariant vector law. -/
theorem invariant_Pkernel_nonzeroPart_unique
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Kernel.Invariant (Kchain A N) μ)
    (hν : Kernel.Invariant (Kchain A N) ν)
    (hμ_support : μ ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hν_support : ν ((Set.Icc (0 : ℝ) 1)ᶜ) = 0)
    (hμ0 : μ ({0} : Set ℝ) < 1)
    (hν0 : ν ({0} : Set ℝ) < 1) :
    (Jkernel A N) ∘ₘ nonzeroPart μ =
      (Jkernel A N) ∘ₘ nonzeroPart ν :=
  congrArg (fun ρ : Measure ℝ => (Jkernel A N) ∘ₘ ρ)
    (nonzeroPart_eq_of_invariant_Kchain hA hN μ ν
      hμ hν hμ_support hν_support hμ0 hν0)

/-- Any two nontrivial invariant vector probabilities have the same invariant vector law
reconstructed from the normalized nonzero components of their squared-radius laws. -/
theorem invariant_Pkernel_nonzeroPart_unique_of_invariant_Pkernel
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (π ρ : Measure (Fin N → ℝ))
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hρ : Kernel.Invariant (Pkernel A N) ρ)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) < 1)
    (hρ0 : ρ ({0} : Set (Fin N → ℝ)) < 1) :
    (Jkernel A N) ∘ₘ nonzeroPart (π.map (radiusSq N)) =
      (Jkernel A N) ∘ₘ nonzeroPart (ρ.map (radiusSq N)) := by
  letI : IsProbabilityMeasure (π.map (radiusSq N)) :=
    Measure.isProbabilityMeasure_map (measurable_radiusSq N).aemeasurable
  letI : IsProbabilityMeasure (ρ.map (radiusSq N)) :=
    Measure.isProbabilityMeasure_map (measurable_radiusSq N).aemeasurable
  have hπ_radius :
      Kernel.Invariant (Kchain A N) (π.map (radiusSq N)) :=
    invariant_Kchain_map_radiusSq_of_invariant_Pkernel A N π hπ
  have hρ_radius :
      Kernel.Invariant (Kchain A N) (ρ.map (radiusSq N)) :=
    invariant_Kchain_map_radiusSq_of_invariant_Pkernel A N ρ hρ
  exact invariant_Pkernel_nonzeroPart_unique hA hN
    (π.map (radiusSq N)) (ρ.map (radiusSq N))
    hπ_radius hρ_radius
    (invariant_Kchain_apply_Icc_compl A hN (π.map (radiusSq N)) hπ_radius)
    (invariant_Kchain_apply_Icc_compl A hN (ρ.map (radiusSq N)) hρ_radius)
    (by simpa only [map_radiusSq_apply_singleton_zero hN] using hπ0)
    (by simpa only [map_radiusSq_apply_singleton_zero hN] using hρ0)

/-- The unrounded vector kernel has at most one invariant probability with no mass at
the absorbing origin. -/
theorem invariant_probability_unique_Pkernel_of_apply_singleton_zero
    {A : ℝ} {N : ℕ} (hA : 0 < A) (hN : 0 < N)
    (π ρ : Measure (Fin N → ℝ))
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hρ : Kernel.Invariant (Pkernel A N) ρ)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hρ0 : ρ ({0} : Set (Fin N → ℝ)) = 0) :
    π = ρ := by
  have hπ_radius0 :
      (π.map (radiusSq N)) ({0} : Set ℝ) = 0 := by
    rw [map_radiusSq_apply_singleton_zero hN, hπ0]
  have hρ_radius0 :
      (ρ.map (radiusSq N)) ({0} : Set ℝ) = 0 := by
    rw [map_radiusSq_apply_singleton_zero hN, hρ0]
  have hreconstructed :
      (Jkernel A N) ∘ₘ nonzeroPart (π.map (radiusSq N)) =
        (Jkernel A N) ∘ₘ nonzeroPart (ρ.map (radiusSq N)) :=
    invariant_Pkernel_nonzeroPart_unique_of_invariant_Pkernel hA hN
      π ρ hπ hρ (by simp [hπ0]) (by simp [hρ0])
  rw [nonzeroPart_eq_self_of_apply_singleton_zero _ hπ_radius0,
    nonzeroPart_eq_self_of_apply_singleton_zero _ hρ_radius0] at hreconstructed
  calc
    π = (Jkernel A N) ∘ₘ (π.map (radiusSq N)) :=
      eq_Jkernel_comp_map_radiusSq_of_invariant_Pkernel A N π hπ
    _ = (Jkernel A N) ∘ₘ (ρ.map (radiusSq N)) := hreconstructed
    _ = ρ :=
      (eq_Jkernel_comp_map_radiusSq_of_invariant_Pkernel A N ρ hρ).symm

/-- Under the explicit finite-dimensional supercritical criterion, there is a
unique invariant probability for the vector kernel having no atom at the
absorbing origin. -/
theorem exists_unique_invariant_probability_Pkernel_of_apply_singleton_zero
    {A : ℝ} {N : ℕ} (hA : 1 < A) (hN : 2 < N)
    (hdim : 2 * A ^ 2 < (A ^ 2 - 1) * N) :
    ∃! π : ProbabilityMeasure (Fin N → ℝ),
      Kernel.Invariant (Pkernel A N) (π : Measure (Fin N → ℝ)) ∧
      (π : Measure (Fin N → ℝ)) ({0} : Set (Fin N → ℝ)) = 0 := by
  obtain ⟨ν, hν, _hνsupport, hν0⟩ :=
    exists_invariant_Kchain_apply_singleton_zero_of_dimension hA hN hdim
  let π : ProbabilityMeasure (Fin N → ℝ) :=
    ⟨(Jkernel A N) ∘ₘ (ν : Measure ℝ), inferInstance⟩
  have hπ :
      Kernel.Invariant (Pkernel A N) (π : Measure (Fin N → ℝ)) := by
    dsimp [π]
    exact invariant_Pkernel_of_invariant_Kchain A N (ν : Measure ℝ) hν
  have hπ0 :
      (π : Measure (Fin N → ℝ)) ({0} : Set (Fin N → ℝ)) = 0 := by
    rw [← map_radiusSq_apply_singleton_zero (Nat.zero_lt_of_lt hN)]
    dsimp [π]
    rw [radiusSq_map_Jkernel_comp, hν.def, hν0]
  refine ⟨π, ⟨hπ, hπ0⟩, ?_⟩
  intro ρ hρ
  apply ProbabilityMeasure.toMeasure_injective
  exact invariant_probability_unique_Pkernel_of_apply_singleton_zero
    (zero_lt_one.trans hA) (Nat.zero_lt_of_lt hN)
    (ρ : Measure (Fin N → ℝ)) (π : Measure (Fin N → ℝ))
    hρ.1 hπ hρ.2 hπ0

end AbsorptionCutoff
