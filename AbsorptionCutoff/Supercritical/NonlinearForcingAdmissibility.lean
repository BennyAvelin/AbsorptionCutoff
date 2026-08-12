/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.NonlinearForcing

/-!
# Admissibility of the nonlinear renewal forcing

This continuation module carries the remaining proof of
`prop:nd-forcing-admissibility`. The base `NonlinearForcing` module establishes
the forcing, Gaussian-isotropy transport, and the fixed-state polar envelope;
this file begins with the averaging and directly Riemann integrable estimates.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

namespace Renewal

/-- A real translate of one unit cell meets at most two integer unit cells. -/
lemma cellSup_comp_sub_le_add (g : ℝ → ENNReal) (a : ℝ) (k : ℤ) :
    cellSup (fun x => g (x - a)) k ≤
      cellSup g (k + ⌊(-a)⌋) + cellSup g (k + ⌊(-a)⌋ + 1) := by
  apply iSup₂_le
  intro x hx
  have hfloor : ((⌊(-a)⌋ : ℤ) : ℝ) ≤ -a := Int.floor_le (-a)
  have hceil : -a < ((⌊(-a)⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (-a)
  have hlo : ((k + ⌊(-a)⌋ : ℤ) : ℝ) ≤ x - a := by
    norm_num at hx ⊢
    linarith [hx.1]
  have hhi : x - a ≤ ((k + ⌊(-a)⌋ + 2 : ℤ) : ℝ) := by
    norm_num at hx ⊢
    linarith [hx.2]
  by_cases hm : x - a ≤ ((k + ⌊(-a)⌋ + 1 : ℤ) : ℝ)
  · apply le_trans (le_cellSup (k := k + ⌊(-a)⌋) ?_) (le_add_right le_rfl)
    constructor
    · exact hlo
    · norm_num at hm ⊢
      exact hm
  · have hright : x - a ∈ Set.Icc
        ((k + ⌊(-a)⌋ + 1 : ℤ) : ℝ) ((k + ⌊(-a)⌋ + 1 : ℤ) + 1) := by
      constructor
      · exact le_of_not_ge hm
      · norm_num at hhi ⊢
        linarith
    exact le_trans (le_cellSup hright) (le_add_left le_rfl)

/-- Translating a nonnegative kernel by a real shift costs at most a factor two
in the directly Riemann integrable norm. -/
lemma driNorm_comp_sub_le_two_mul (g : ℝ → ENNReal) (a : ℝ) :
    driNorm (fun x => g (x - a)) ≤ 2 * driNorm g := by
  rw [driNorm_def]
  calc
    ∑' k : ℤ, cellSup (fun x => g (x - a)) k ≤
        ∑' k : ℤ, (cellSup g (k + ⌊(-a)⌋) +
          cellSup g (k + ⌊(-a)⌋ + 1)) :=
      ENNReal.tsum_le_tsum (cellSup_comp_sub_le_add g a)
    _ = (∑' k : ℤ, cellSup g (k + ⌊(-a)⌋)) +
        ∑' k : ℤ, cellSup g (k + ⌊(-a)⌋ + 1) := ENNReal.tsum_add
    _ = driNorm g + driNorm g := by
      rw [driNorm_def]
      congr 1
      · simpa using (Equiv.addRight ⌊(-a)⌋).tsum_eq (cellSup g)
      · simpa [add_assoc] using
          (Equiv.addRight (⌊(-a)⌋ + 1)).tsum_eq (cellSup g)
    _ = 2 * driNorm g := by ring

/-- A cell supremum of nonnegative integrals is bounded by the integral of the
pointwise cell supremum. -/
lemma cellSup_lintegral_le_lintegral_cellSup {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (F : α → ℝ → ENNReal) (k : ℤ) :
    cellSup (fun y => ∫⁻ p, F p y ∂μ) k ≤
      ∫⁻ p, cellSup (F p) k ∂μ := by
  apply iSup₂_le
  intro y hy
  exact lintegral_mono fun p => le_cellSup hy

/-- Under the natural cell-sup measurability hypothesis, the d.R.i. norm of a
nonnegative integral is bounded by the integral of the pointwise d.R.i. norms. -/
lemma driNorm_lintegral_le_lintegral_driNorm
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α → ℝ → ENNReal)
    (hF : ∀ k : ℤ, AEMeasurable (fun p => cellSup (F p) k) μ) :
    driNorm (fun y => ∫⁻ p, F p y ∂μ) ≤
      ∫⁻ p, driNorm (F p) ∂μ := by
  rw [driNorm_def]
  calc
    ∑' k : ℤ, cellSup (fun y => ∫⁻ p, F p y ∂μ) k ≤
        ∑' k : ℤ, ∫⁻ p, cellSup (F p) k ∂μ :=
      ENNReal.tsum_le_tsum (cellSup_lintegral_le_lintegral_cellSup μ F)
    _ = ∫⁻ p, ∑' k : ℤ, cellSup (F p) k ∂μ := (lintegral_tsum hF).symm
    _ = ∫⁻ p, driNorm (F p) ∂μ := rfl

/-- Cell suprema of a continuous nonnegative kernel vary continuously under
real translations. -/
lemma continuous_cellSup_comp_sub (g : ℝ → ENNReal) (hg : Continuous g) (k : ℤ) :
    Continuous fun a : ℝ => cellSup (fun x => g (x - a)) k := by
  have hs := (isCompact_Icc : IsCompact (Set.Icc (k : ℝ) (k + 1))).continuous_sSup
    (f := fun a x : ℝ => g (x - a)) (by fun_prop)
  simpa only [cellSup, sSup_image] using hs

end Renewal

/-- The exponentially weighted polar envelope has a uniform finite d.R.i. norm
under every real translation. -/
theorem driNorm_exp_mul_polarEnvelope_comp_sub_le_two_mul
    {N : ℕ} {β : ℝ} (hβ : 0 < β) (hβN : β < N) (a : ℝ) :
    Renewal.driNorm
        (fun t : ℝ => ENNReal.ofReal
          (Real.exp (β * (t - a)) * polarEnvelope N (t - a))) ≤
      2 * Renewal.driNorm
        (fun t : ℝ => ENNReal.ofReal (Real.exp (β * t) * polarEnvelope N t)) ∧
    Renewal.driNorm
        (fun t : ℝ => ENNReal.ofReal
          (Real.exp (β * (t - a)) * polarEnvelope N (t - a))) ≠ ⊤ := by
  have hle := Renewal.driNorm_comp_sub_le_two_mul
    (fun t : ℝ => ENNReal.ofReal (Real.exp (β * t) * polarEnvelope N t)) a
  refine ⟨hle, ne_top_of_le_ne_top ?_ hle⟩
  exact ENNReal.mul_ne_top (by norm_num)
    (driNorm_exp_mul_polarEnvelope_ne_top hβ hβN)

/-- An origin-free law has unit angular coordinate almost surely under its
log-polar pushforward. -/
lemma ae_norm_snd_logPolarLaw_eq_one (N : ℕ) (π : Measure (Fin N → ℝ))
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0) :
    ∀ᵐ p ∂logPolarLaw N π, ‖p.2‖ = 1 := by
  rw [logPolarLaw]
  have hp : MeasurableSet {p : ℝ × EuclideanSpace ℝ (Fin N) | ‖p.2‖ = 1} :=
    measurable_snd.norm measurableSet_eq
  rw [ae_map_iff (measurable_logPolarCoords N).aemeasurable hp]
  have hae : ∀ᵐ x ∂π, gaussianEuclideanNorm N x ≠ 0 := by
    rw [ae_iff]
    simpa using horigin
  filter_upwards [hae] with x hx
  exact norm_angular N hx

/-- Coordinate-box support places the log-polar radius `exp (-Y)` in the range
`(0, √N]` required by the polar perturbation estimate. -/
lemma ae_exp_neg_fst_logPolarLaw_le_sqrt (N : ℕ) (π : Measure (Fin N → ℝ))
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    ∀ᵐ p ∂logPolarLaw N π, Real.exp (-p.1) ≤ Real.sqrt N := by
  rw [logPolarLaw]
  have hp : MeasurableSet
      {p : ℝ × EuclideanSpace ℝ (Fin N) | Real.exp (-p.1) ≤ Real.sqrt N} :=
    measurable_fst.neg.exp measurableSet_Iic
  rw [ae_map_iff (measurable_logPolarCoords N).aemeasurable hp]
  have hae : ∀ᵐ x ∂π, gaussianEuclideanNorm N x ≠ 0 := by
    rw [ae_iff]
    simpa using horigin
  filter_upwards [hae, hsupport] with x hx hbox
  rw [exp_neg_logRadius N hx]
  exact gaussianEuclideanNorm_le_sqrt_nat N hbox

/-- Fubini disintegration of `nonlinearForcing` into the fixed `(Y, Θ)` fibers
controlled by `exists_nonlinearForcingFiber_polarEnvelope`. -/
theorem nonlinearForcing_eq_integral_fiber (A : ℝ) (N : ℕ)
    {π : Measure (Fin N → ℝ)} [IsProbabilityMeasure π]
    (β y C : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}
    (hφm : Measurable φ) (hφ : ∀ θ, |φ θ| ≤ C) :
    nonlinearForcing A N π β y φ =
      Real.exp (β * y) *
        ∫ p, ((∫ W, nonlinearForcingPlusFiber N (Real.exp (-p.1)) (y - p.1) φ
            (fun i => ∑ j, W i j * WithLp.ofLp p.2 j) ∂gaussianMat A N) -
          ∫ W, nonlinearForcingZeroFiber N (y - p.1) φ
            (fun i => ∑ j, W i j * WithLp.ofLp p.2 j) ∂gaussianMat A N)
          ∂logPolarLaw N π := by
  have hp := integrable_nonlinearForcingPlusIntegrand A N (π := π) y C hφm hφ
  have hz := integrable_nonlinearForcingZeroIntegrand A N (π := π) y C hφm hφ
  unfold nonlinearForcing
  rw [integral_prod _ hp, integral_prod _ hz,
    ← integral_sub hp.integral_prod_left hz.integral_prod_left]
  refine congrArg (fun z : ℝ => Real.exp (β * y) * z) ?_
  apply integral_congr_ae
  filter_upwards [] with p
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with W
    exact nonlinearForcingPlusIntegrand_eq_fiber N y p.1 p.2 W φ
  · apply integral_congr_ae
    filter_upwards [] with W
    exact nonlinearForcingZeroIntegrand_eq_fiber N y p.1 p.2 W φ

/-- The fixed-state polar envelope averages to a global forcing bound whenever
its log-polar majorant is integrable. -/
theorem exists_abs_nonlinearForcing_le_integral_polarEnvelope
    (A : ℝ) {N : ℕ} (hA : A ≠ 0) (hN : 0 < N)
    (hσ : (A ^ 2 / N).toNNReal ≠ 0)
    (hσ0 : (0 : ℝ) < (A ^ 2 / N).toNNReal)
    {β δ : ℝ} (hβ : 0 < β) (hβN : β < (N : ℝ))
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      Renewal.driNorm
        (fun t : ℝ => ENNReal.ofReal (Real.exp (β * t) * polarEnvelope N t)) ≠ ⊤ ∧
      ∀ (y : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}, Measurable φ →
        (∀ z, |φ z| ≤ 1) →
        Integrable
          (fun p : ℝ × EuclideanSpace ℝ (Fin N) =>
            Real.exp (-p.1) ^ δ * polarEnvelope N (y - p.1))
          (logPolarLaw N π) →
        |nonlinearForcing A N π β y φ| ≤
          C * Real.exp (β * y) *
            ∫ p, Real.exp (-p.1) ^ δ * polarEnvelope N (y - p.1)
              ∂logPolarLaw N π := by
  obtain ⟨C, hC, hdri, hfiber⟩ :=
    exists_nonlinearForcingFiber_polarEnvelope
      A hA hN hσ hσ0 hβ hβN hδ0 hδ2
  refine ⟨C, hC, hdri, ?_⟩
  intro y φ hφ habs hmajor
  let F : (ℝ × EuclideanSpace ℝ (Fin N)) → ℝ := fun p =>
    (∫ W, nonlinearForcingPlusFiber N (Real.exp (-p.1)) (y - p.1) φ
        (fun i => ∑ j, W i j * WithLp.ofLp p.2 j) ∂gaussianMat A N) -
      ∫ W, nonlinearForcingZeroFiber N (y - p.1) φ
        (fun i => ∑ j, W i j * WithLp.ofLp p.2 j) ∂gaussianMat A N
  let G : (ℝ × EuclideanSpace ℝ (Fin N)) → ℝ := fun p =>
    Real.exp (-p.1) ^ δ * polarEnvelope N (y - p.1)
  have hθ := ae_norm_snd_logPolarLaw_eq_one N π horigin
  have hrN := ae_exp_neg_fst_logPolarLaw_le_sqrt N π horigin hsupport
  have hpoint : ∀ᵐ p ∂logPolarLaw N π, ‖F p‖ ≤ C * G p := by
    filter_upwards [hθ, hrN] with p hpθ hpr
    simpa only [F, G, Real.norm_eq_abs, mul_assoc] using
      hfiber (Real.exp_pos (-p.1)) hpr (y - p.1) p.2 hpθ hφ habs
  have hnorm : ‖∫ p, F p ∂logPolarLaw N π‖ ≤
      ∫ p, C * G p ∂logPolarLaw N π :=
    norm_integral_le_of_norm_le (hmajor.const_mul C) hpoint
  rw [nonlinearForcing_eq_integral_fiber A N β y 1 hφ habs]
  change |Real.exp (β * y) * ∫ p, F p ∂logPolarLaw N π| ≤ _
  rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
  calc
    Real.exp (β * y) * |∫ p, F p ∂logPolarLaw N π|
      ≤ Real.exp (β * y) * ∫ p, C * G p ∂logPolarLaw N π := by
        rw [← Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _)
    _ = C * Real.exp (β * y) * ∫ p, G p ∂logPolarLaw N π := by
      rw [integral_const_mul]
      ring

/-- The averaged polar majorant is a tilted translate of the d.R.i. envelope. -/
lemma exp_mul_rpow_polarEnvelope_eq_tilted (N : ℕ) (β δ y Y : ℝ) :
    Real.exp (β * y) *
        (Real.exp (-Y) ^ δ * polarEnvelope N (y - Y)) =
      Real.exp ((β - δ) * Y) *
        (Real.exp (β * (y - Y)) * polarEnvelope N (y - Y)) := by
  rw [← Real.exp_mul]
  rw [← mul_assoc, ← Real.exp_add, ← mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

/-- The exponentially weighted polar envelope is uniformly bounded by one. -/
lemma exp_mul_polarEnvelope_le_one {N : ℕ} {β t : ℝ}
    (hβ0 : 0 ≤ β) (hβN : β ≤ N) :
    Real.exp (β * t) * polarEnvelope N t ≤ 1 := by
  rcases le_total t 0 with ht | ht
  · rw [polarEnvelope_of_nonpos ht, mul_one, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos hβ0 ht
  · rw [polarEnvelope_of_nonneg ht, ← Real.exp_nat_mul, ← Real.exp_add,
      Real.exp_le_one_iff]
    nlinarith

/-- A negative radial moment becomes a positive exponential moment of the
first log-polar coordinate. -/
lemma integrable_exp_fst_logPolarLaw_of_integrable_neg_rpow {N : ℕ} {α : ℝ}
    (π : Measure (Fin N → ℝ))
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    (h : Integrable (fun x => gaussianEuclideanNorm N x ^ (-α)) π) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Real.exp (α * p.1))
      (logPolarLaw N π) := by
  rw [logPolarLaw, integrable_map_measure
    (by fun_prop : AEStronglyMeasurable
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Real.exp (α * p.1))
      (π.map fun x => (logRadius N x, angular N x)))
    (measurable_logPolarCoords N).aemeasurable]
  refine h.congr ?_
  have hae : ∀ᵐ x ∂π, gaussianEuclideanNorm N x ≠ 0 := by
    rw [ae_iff]
    simpa using horigin
  filter_upwards [hae] with x hx
  change gaussianEuclideanNorm N x ^ (-α) = Real.exp (α * logRadius N x)
  have hpos : 0 < gaussianEuclideanNorm N x :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity) (Ne.symm hx)
  rw [logRadius, Real.rpow_def_of_pos hpos]
  congr 1
  ring

/-- The subcritical invariant-law moment at exponent `β - δ`, expressed in
log-polar coordinates. -/
lemma integrable_exp_cramerExponent_sub_fst_logPolarLaw_of_invariant_Pkernel
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0) :
    Integrable
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) =>
        Real.exp ((cramerExponent A N - δ) * p.1))
      (logPolarLaw N π) := by
  have hp : 0 < (cramerExponent A N - δ) / 2 := by linarith
  have hpβ : 2 * ((cramerExponent A N - δ) / 2) <
      cramerExponent A N := by linarith
  have hm := integrable_neg_rpow_gaussianEuclideanNorm_of_invariant_Pkernel
    hA hN hsc hp hpβ π hπ hπ0
  have hm' : Integrable
      (fun x => gaussianEuclideanNorm N x ^ (-(cramerExponent A N - δ))) π := by
    convert hm using 1
    ring_nf
  have horigin : π {x | gaussianEuclideanNorm N x = 0} = 0 := by
    rw [show {x | gaussianEuclideanNorm N x = 0} = ({0} : Set (Fin N → ℝ)) by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact gaussianEuclideanNorm_eq_zero_iff N x]
    exact hπ0
  exact integrable_exp_fst_logPolarLaw_of_integrable_neg_rpow π horigin hm'

/-- The forcing majorant is dominated by the tilted radial exponential moment. -/
lemma rpow_mul_polarEnvelope_le_exp_tilt {N : ℕ} {β δ y Y : ℝ}
    (hβ0 : 0 ≤ β) (hβN : β ≤ N) :
    Real.exp (-Y) ^ δ * polarEnvelope N (y - Y) ≤
      Real.exp (-β * y) * Real.exp ((β - δ) * Y) := by
  calc
    Real.exp (-Y) ^ δ * polarEnvelope N (y - Y) =
        Real.exp (-β * y) * (Real.exp (β * y) *
          (Real.exp (-Y) ^ δ * polarEnvelope N (y - Y))) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ = Real.exp (-β * y) * (Real.exp ((β - δ) * Y) *
        (Real.exp (β * (y - Y)) * polarEnvelope N (y - Y))) := by
      rw [exp_mul_rpow_polarEnvelope_eq_tilted]
    _ ≤ Real.exp (-β * y) * Real.exp ((β - δ) * Y) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      simpa using mul_le_mul_of_nonneg_left
        (exp_mul_polarEnvelope_le_one hβ0 hβN)
        (Real.exp_nonneg ((β - δ) * Y))

/-- An integrable tilted radial moment makes every shifted forcing majorant
integrable. -/
lemma integrable_rpow_mul_polarEnvelope_of_integrable_exp_tilt
    {N : ℕ} {β δ y : ℝ} (hβ0 : 0 ≤ β) (hβN : β ≤ N)
    (hδ0 : 0 ≤ δ) (π : Measure (Fin N → ℝ))
    (hmoment : Integrable
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Real.exp ((β - δ) * p.1))
      (logPolarLaw N π)) :
    Integrable
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) =>
        Real.exp (-p.1) ^ δ * polarEnvelope N (y - p.1))
      (logPolarLaw N π) := by
  apply (hmoment.const_mul (Real.exp (-β * y))).mono'
  · have hrpow : Measurable
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => Real.exp (-p.1) ^ δ) :=
      (Real.continuous_rpow_const hδ0).measurable.comp (by fun_prop)
    exact (hrpow.mul (by unfold polarEnvelope; fun_prop)).aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (Real.exp_nonneg _) _)
        (polarEnvelope_nonneg N _))]
    exact rpow_mul_polarEnvelope_le_exp_tilt hβ0 hβN

/-- Under the invariant-law hypotheses, every shifted forcing majorant is
integrable. -/
lemma integrable_rpow_mul_polarEnvelope_of_invariant_Pkernel
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0) (y : ℝ) :
    Integrable
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) =>
        Real.exp (-p.1) ^ δ * polarEnvelope N (y - p.1))
      (logPolarLaw N π) := by
  have hβmem := cramerExponent_mem hA hN hsc
  apply integrable_rpow_mul_polarEnvelope_of_integrable_exp_tilt
    hβmem.1.le hβmem.2.le hδ0.le π
  exact integrable_exp_cramerExponent_sub_fst_logPolarLaw_of_invariant_Pkernel
    hA hN hsc hδ0 hδβ π hπ hπ0

/-- The invariant-law nonlinear forcing is globally controlled by the averaged
polar envelope, with no separate majorant-integrability assumption. -/
theorem exists_abs_nonlinearForcing_le_integral_polarEnvelope_of_invariant_Pkernel
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2)
    (hδβ : δ < cramerExponent A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0)
    (hsupport : ∀ᵐ x ∂π, ∀ i, |x i| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      Renewal.driNorm
        (fun t : ℝ => ENNReal.ofReal
          (Real.exp (cramerExponent A N * t) * polarEnvelope N t)) ≠ ⊤ ∧
      ∀ (y : ℝ) {φ : EuclideanSpace ℝ (Fin N) → ℝ}, Measurable φ →
        (∀ z, |φ z| ≤ 1) →
        |nonlinearForcing A N π (cramerExponent A N) y φ| ≤
          C * Real.exp (cramerExponent A N * y) *
            ∫ p, Real.exp (-p.1) ^ δ * polarEnvelope N (y - p.1)
              ∂logPolarLaw N π := by
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hvar : 0 < A ^ 2 / (N : ℝ) :=
    div_pos (sq_pos_of_pos hA) hNreal
  have hσ0 : (0 : ℝ) < (A ^ 2 / N).toNNReal := Real.toNNReal_pos.mpr hvar
  have hσ : (A ^ 2 / N).toNNReal ≠ 0 := ne_of_gt hσ0
  have hβmem := cramerExponent_mem hA hN hsc
  have horigin : π {x | gaussianEuclideanNorm N x = 0} = 0 := by
    rw [show {x | gaussianEuclideanNorm N x = 0} = ({0} : Set (Fin N → ℝ)) by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact gaussianEuclideanNorm_eq_zero_iff N x]
    exact hπ0
  obtain ⟨C, hC, hdri, hbound⟩ :=
    exists_abs_nonlinearForcing_le_integral_polarEnvelope
      A hA0 hN hσ hσ0 hβmem.1 hβmem.2 hδ0 hδ2 π horigin hsupport
  refine ⟨C, hC, hdri, ?_⟩
  intro y φ hφ habs
  exact hbound y hφ habs
    (integrable_rpow_mul_polarEnvelope_of_invariant_Pkernel
      hA hN hsc hδ0 hδβ π hπ hπ0 y)

end AbsorptionCutoff
