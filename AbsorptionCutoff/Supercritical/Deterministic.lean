/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.MeanMap.Derivative
import AbsorptionCutoff.MeanMap.Dynamics

/-! ### Second-order regularity of the Gaussian mean map

The Koenigs argument in the proof of
`eq:gaussian-deterministic-asymptotic` starts from the quadratic Taylor
remainder of `V_A` at its positive fixed point.  This file begins the
constructive real-analysis route by differentiating the pointwise derivative
integrand `dV`.  All statements are made away from `q = 0`, which is exactly
what is needed near the positive fixed point.
-/

open Set MeasureTheory ProbabilityTheory Filter

namespace AbsorptionCutoff

/-- The pointwise second derivative of
`q ↦ tanh²(A √q g)`.  The two summands respectively come from differentiating
`q ↦ (Ag)/√q` and `x ↦ tanh x (1 - tanh² x)`. -/
noncomputable def d2V (A q g : ℝ) : ℝ :=
  let z := A * g
  let x := z * Real.sqrt q
  (-(z / (2 * q * Real.sqrt q)) * Real.tanh x * (1 - Real.tanh x ^ 2)
    + (z ^ 2 / (2 * q)) * (1 - Real.tanh x ^ 2)
      * (1 - 3 * Real.tanh x ^ 2))

/-- Away from `q = 0`, the first derivative integrand can be written without
the removable quotient `tanh x / x`. -/
lemma dV_eq_div_sqrt {A q g : ℝ} (hq : 0 < q) :
    dV A q g =
      (A * g / Real.sqrt q) * Real.tanh (A * g * Real.sqrt q)
        * (1 - Real.tanh (A * g * Real.sqrt q) ^ 2) := by
  have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have harg : A * Real.sqrt q * g = (A * g) * Real.sqrt q := by ring
  rw [dV, harg]
  rcases eq_or_ne (A * g) 0 with hz | hz
  · simp [hz]
  · field_simp

/-- Pointwise second differentiation of the Gaussian mean-map integrand. -/
lemma hasDerivAt_dV {A q g : ℝ} (hq : 0 < q) :
    HasDerivAt (fun x => dV A x g) (d2V A q g) q := by
  let z := A * g
  let t : ℝ → ℝ := fun x => Real.tanh (z * Real.sqrt x)
  have hsqrt_ne : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt x)
      (1 / (2 * Real.sqrt q)) q :=
    Real.hasDerivAt_sqrt hq.ne'
  have hx : HasDerivAt (fun x : ℝ => z * Real.sqrt x)
      (z * (1 / (2 * Real.sqrt q))) q :=
    hsqrt.const_mul z
  have ht : HasDerivAt t
      ((1 - t q ^ 2) * (z * (1 / (2 * Real.sqrt q)))) q := by
    simpa only [t, Function.comp_def] using
      (hasDerivAt_tanh (z * Real.sqrt q)).comp q hx
  have hs : HasDerivAt (fun x => 1 - t x ^ 2)
      (0 - 2 * t q ^ (2 - 1) *
        ((1 - t q ^ 2) * (z * (1 / (2 * Real.sqrt q))))) q :=
    (hasDerivAt_const q 1).sub (ht.pow 2)
  have hzdiv : HasDerivAt (fun x : ℝ => z / Real.sqrt x)
      ((0 * Real.sqrt q - z * (1 / (2 * Real.sqrt q))) /
        Real.sqrt q ^ 2) q :=
    (hasDerivAt_const q z).div hsqrt hsqrt_ne
  have hraw := (hzdiv.mul ht).mul hs
  simp only [Pi.mul_apply] at hraw
  have heq :
        (((0 * Real.sqrt q - z * (1 / (2 * Real.sqrt q))) /
              Real.sqrt q ^ 2 * t q
            + z / Real.sqrt q *
              ((1 - t q ^ 2) * (z * (1 / (2 * Real.sqrt q)))))
            * (1 - t q ^ 2)
          + (z / Real.sqrt q * t q) *
            (0 - 2 * t q ^ (2 - 1) *
              ((1 - t q ^ 2) * (z * (1 / (2 * Real.sqrt q))))))
          = d2V A q g := by
    simp only [d2V, z, t]
    have hsqrt_sq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
    field_simp
    rw [hsqrt_sq]
    ring
  rw [heq] at hraw
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq] with x hx
  simpa only [z, t, Pi.mul_apply] using
    (dV_eq_div_sqrt (A := A) (g := g) hx)

/-- A pointwise bound for the second derivative integrand away from zero.
The bound uses only the first two powers of the Gaussian coordinate. -/
lemma abs_d2V_le {A q g : ℝ} (hq : 0 < q) :
    |d2V A q g| ≤
      |A * g| / (2 * q * Real.sqrt q) + (A * g) ^ 2 / q := by
  let z := A * g
  let x := z * Real.sqrt q
  have hsqrt : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have ht : |Real.tanh x| ≤ 1 :=
    (abs_le).2 ⟨(Real.neg_one_lt_tanh x).le, (Real.tanh_lt_one x).le⟩
  have ht_sq_nonneg : 0 ≤ Real.tanh x ^ 2 := sq_nonneg _
  have ht_sq_le : Real.tanh x ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) ht
  have hs_nonneg : 0 ≤ 1 - Real.tanh x ^ 2 := by linarith
  have hs_le : 1 - Real.tanh x ^ 2 ≤ 1 := by linarith
  have hs_abs : |1 - Real.tanh x ^ 2| ≤ 1 := by
    rw [abs_of_nonneg hs_nonneg]
    exact hs_le
  have hu_abs : |1 - 3 * Real.tanh x ^ 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hden1 : 0 < 2 * q * Real.sqrt q := by positivity
  have hden2 : 0 < 2 * q := by positivity
  rw [d2V]
  change
    |-(z / (2 * q * Real.sqrt q)) * Real.tanh x *
          (1 - Real.tanh x ^ 2) +
        (z ^ 2 / (2 * q)) * (1 - Real.tanh x ^ 2) *
          (1 - 3 * Real.tanh x ^ 2)| ≤
      |z| / (2 * q * Real.sqrt q) + z ^ 2 / q
  calc
    _ ≤
        |-(z / (2 * q * Real.sqrt q)) * Real.tanh x *
            (1 - Real.tanh x ^ 2)|
          + |(z ^ 2 / (2 * q)) * (1 - Real.tanh x ^ 2) *
            (1 - 3 * Real.tanh x ^ 2)| := abs_add_le _ _
    _ ≤ |z| / (2 * q * Real.sqrt q) + z ^ 2 / q := by
      simp only [abs_mul, abs_neg, abs_div,
        abs_of_pos hden1, abs_of_pos hden2, abs_pow]
      have hzsq : |z| ^ 2 = z ^ 2 := sq_abs z
      rw [hzsq]
      gcongr
      · calc
          |z| / (2 * q * Real.sqrt q) * |Real.tanh x| *
                |1 - Real.tanh x ^ 2|
              ≤ |z| / (2 * q * Real.sqrt q) * 1 * 1 := by gcongr
          _ = |z| / (2 * q * Real.sqrt q) := by ring
      · calc
          z ^ 2 / (2 * q) * |1 - Real.tanh x ^ 2| *
                |1 - 3 * Real.tanh x ^ 2|
              ≤ z ^ 2 / (2 * q) * 1 * 2 := by gcongr
          _ = z ^ 2 / q := by field_simp

/-- A Gaussian-integrable majorant for `d2V A q` when `q ≥ a > 0`. -/
noncomputable def d2VBound (A a g : ℝ) : ℝ :=
  |A * g| / (2 * a * Real.sqrt a) + (A * g) ^ 2 / a

/-- The second derivative integrand is measurable in the Gaussian coordinate. -/
lemma measurable_d2V (A q : ℝ) : Measurable (fun g => d2V A q g) := by
  have hz : Measurable (fun g : ℝ => A * g) := measurable_id.const_mul A
  have hx : Measurable (fun g : ℝ => (A * g) * Real.sqrt q) :=
    hz.mul measurable_const
  have ht : Measurable (fun g : ℝ => Real.tanh ((A * g) * Real.sqrt q)) :=
    continuous_tanh.measurable.comp hx
  simp only [d2V]
  exact
    ((((hz.div_const (2 * q * Real.sqrt q)).neg.mul ht).mul
        (measurable_const.sub (ht.pow_const 2))).add
      ((((hz.pow_const 2).div_const (2 * q)).mul
        (measurable_const.sub (ht.pow_const 2))).mul
        (measurable_const.sub (measurable_const.mul (ht.pow_const 2)))))

/-- `d2VBound A a` is integrable for every fixed lower-radius parameter `a`. -/
lemma integrable_d2VBound (A a : ℝ) :
    Integrable (d2VBound A a) (gaussianReal 0 1) := by
  have habs : Integrable (fun g : ℝ => |g|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  have heq :
      d2VBound A a =
        fun g : ℝ =>
          (|A| / (2 * a * Real.sqrt a)) * |g| + (A ^ 2 / a) * g ^ 2 := by
    funext g
    rw [d2VBound, abs_mul, mul_pow]
    ring
  rw [heq]
  exact
    (habs.const_mul (|A| / (2 * a * Real.sqrt a))).add
      (integrable_sq_gaussian.const_mul (A ^ 2 / a))

/-- The majorant at a positive lower radius controls `d2V` uniformly above
that radius. -/
lemma abs_d2V_le_d2VBound {A a q g : ℝ} (ha : 0 < a) (haq : a ≤ q) :
    |d2V A q g| ≤ d2VBound A a g := by
  have hq : 0 < q := lt_of_lt_of_le ha haq
  have hsqrt : Real.sqrt a ≤ Real.sqrt q := Real.sqrt_le_sqrt haq
  have hden :
      2 * a * Real.sqrt a ≤ 2 * q * Real.sqrt q := by
    gcongr
  have hden_pos : 0 < 2 * a * Real.sqrt a := by positivity
  have hfirst :
      |A * g| / (2 * q * Real.sqrt q) ≤
        |A * g| / (2 * a * Real.sqrt a) :=
    div_le_div_of_nonneg_left (abs_nonneg _) hden_pos hden
  have hsecond : (A * g) ^ 2 / q ≤ (A * g) ^ 2 / a :=
    div_le_div_of_nonneg_left (sq_nonneg _) ha haq
  exact (abs_d2V_le hq).trans (add_le_add hfirst hsecond)

/-- The Gaussian mean map is twice differentiable at every positive `q`.
This is the second-order input for the paper's quadratic Taylor estimate at
the attracting fixed point. -/
lemma hasDerivAt_deriv_V {A q : ℝ} (hA : A ≠ 0) (hq : 0 < q) :
    HasDerivAt (deriv (V A))
      (∫ g, d2V A q g ∂(gaussianReal 0 1)) q := by
  let a := q / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hqa : a < q := by dsimp [a]; linarith
  have hFmeas : ∀ᶠ x in nhds q,
      AEStronglyMeasurable (fun g => dV A x g) (gaussianReal 0 1) := by
    filter_upwards with x
    exact (measurable_dV A x).aestronglyMeasurable
  have hbound : ∀ᵐ g ∂(gaussianReal 0 1), ∀ x ∈ Set.Ioi a,
      ‖d2V A x g‖ ≤ d2VBound A a g := by
    filter_upwards with g
    intro x hx
    rw [Real.norm_eq_abs]
    exact abs_d2V_le_d2VBound ha hx.le
  have hdiff : ∀ᵐ g ∂(gaussianReal 0 1), ∀ x ∈ Set.Ioi a,
      HasDerivAt (fun x => dV A x g) (d2V A x g) x := by
    filter_upwards with g
    intro x hx
    exact hasDerivAt_dV (lt_trans ha hx)
  have hint :
      HasDerivAt
        (fun x => ∫ g, dV A x g ∂(gaussianReal 0 1))
        (∫ g, d2V A q g ∂(gaussianReal 0 1)) q :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x g => dV A x g) (F' := fun x g => d2V A x g)
      (Ioi_mem_nhds hqa) hFmeas (integrable_dV q)
      (measurable_d2V A q).aestronglyMeasurable hbound
      (integrable_d2VBound A a) hdiff).2
  apply hint.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq] with x hx
  exact (hasDerivAt_V hA hx).deriv

/-- On every compact positive interval, `V_A'` has a finite Lipschitz
constant.  This is the local derivative-regularity statement used in the
Koenigs factor estimate. -/
lemma exists_deriv_V_lipschitzOn_Icc {A a b : ℝ}
    (hA : A ≠ 0) (ha : 0 < a) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |deriv (V A) y - deriv (V A) x| ≤ L * |y - x| := by
  let L := ∫ g, d2VBound A a g ∂(gaussianReal 0 1)
  have hL : 0 ≤ L := by
    apply integral_nonneg
    intro g
    dsimp [L, d2VBound]
    positivity
  have hdiff : ∀ x ∈ Set.Icc a b,
      DifferentiableAt ℝ (deriv (V A)) x := by
    intro x hx
    exact (hasDerivAt_deriv_V hA (lt_of_lt_of_le ha hx.1)).differentiableAt
  have hderiv : ∀ x ∈ Set.Icc a b,
      ‖deriv (deriv (V A)) x‖ ≤ L := by
    intro x hx
    rw [(hasDerivAt_deriv_V hA (lt_of_lt_of_le ha hx.1)).deriv]
    exact norm_integral_le_of_norm_le (integrable_d2VBound A a)
      (Eventually.of_forall fun g => by
        rw [Real.norm_eq_abs]
        exact abs_d2V_le_d2VBound ha hx.1)
  refine ⟨L, hL, ?_⟩
  intro x hx y hy
  have hmv :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv
      (convex_Icc a b) hx hy
  simpa only [Real.norm_eq_abs] using hmv

/-! ### The Koenigs factor estimate -/

/-- Near a positive fixed point, the secant multiplier differs from the
linearized multiplier by at most a constant times the distance to the fixed
point.  The quotient is only needed away from `qStar`: deterministic orbits
approach the fixed point monotonically without hitting it, exactly as in the
paper's Koenigs product.

This is the paper's
`(V_A(y) - q_*) / (y - q_*) = μ_A + O(|y - q_*|)`. -/
lemma exists_koenigsFactorEstimate {A qStar : ℝ}
    (hA : A ≠ 0) (hqStar : 0 < qStar) (hfix : V A qStar = qStar) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ Set.Icc (qStar / 2) (3 * qStar / 2), y ≠ qStar →
        |(V A y - qStar) / (y - qStar) - deriv (V A) qStar| ≤
          L * |y - qStar| := by
  have hleft : 0 < qStar / 2 := by linarith
  obtain ⟨L, hL, hLip⟩ :=
    exists_deriv_V_lipschitzOn_Icc
      (A := A) (a := qStar / 2) (b := 3 * qStar / 2) hA hleft
  refine ⟨L, hL, ?_⟩
  intro y hy hyne
  have hqmem : qStar ∈ Set.Icc (qStar / 2) (3 * qStar / 2) := by
    constructor <;> linarith
  have hnum : V A y - qStar = V A y - V A qStar := by rw [hfix]
  rcases lt_or_gt_of_ne hyne with hylt | hygt
  · have hcont : ContinuousOn (V A) (Set.Icc y qStar) :=
      (V_continuous A).continuousOn
    have hdiff : DifferentiableOn ℝ (V A) (Set.Ioo y qStar) := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hleft (hy.1.trans hx.1.le)
      exact (hasDerivAt_V hA hxpos).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcSlope⟩ :=
      exists_deriv_eq_slope (f := V A) hylt hcont hdiff
    have hcmem : c ∈ Set.Icc (qStar / 2) (3 * qStar / 2) := by
      exact ⟨hy.1.trans hc.1.le, hc.2.le.trans hqmem.2⟩
    have hquot :
        (V A y - qStar) / (y - qStar) = deriv (V A) c := by
      rw [hnum, hcSlope]
      field_simp [sub_ne_zero.mpr hyne]
      ring
    rw [hquot]
    refine (hLip qStar hqmem c hcmem).trans ?_
    have hcy : |c - qStar| ≤ |y - qStar| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hc.2.le),
        abs_of_nonpos (sub_nonpos.mpr hylt.le)]
      linarith [hc.1, hc.2]
    exact mul_le_mul_of_nonneg_left hcy hL
  · have hcont : ContinuousOn (V A) (Set.Icc qStar y) :=
      (V_continuous A).continuousOn
    have hdiff : DifferentiableOn ℝ (V A) (Set.Ioo qStar y) := by
      intro x hx
      exact (hasDerivAt_V hA (hqStar.trans hx.1)).differentiableAt.differentiableWithinAt
    obtain ⟨c, hc, hcSlope⟩ :=
      exists_deriv_eq_slope (f := V A) hygt hcont hdiff
    have hcmem : c ∈ Set.Icc (qStar / 2) (3 * qStar / 2) := by
      exact ⟨hqmem.1.trans hc.1.le, hc.2.le.trans hy.2⟩
    have hquot :
        (V A y - qStar) / (y - qStar) = deriv (V A) c := by
      rw [hnum, hcSlope]
    rw [hquot]
    refine (hLip qStar hqmem c hcmem).trans ?_
    have hcy : |c - qStar| ≤ |y - qStar| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hc.1.le),
        abs_of_nonneg (sub_nonneg.mpr hygt.le)]
      linarith [hc.1, hc.2]
    exact mul_le_mul_of_nonneg_left hcy hL

/-! ### Local geometric contraction -/

/-- A positive attracting fixed point has a compact invariant neighborhood
on which both `V_A'` and the corresponding secant slopes are bounded by a
common contraction factor.  The factor is chosen constructively as
`κ = (μ_A + 1) / 2`; the radius is then shrunk using the compact Lipschitz
bound on `V_A'`. -/
lemma exists_local_V_contraction_with_deriv {A qStar : ℝ}
    (hA : A ≠ 0) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ δ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ 0 < δ ∧
      δ ≤ min (qStar / 2) ((1 - qStar) / 2) ∧
      (∀ x : ℝ, |x - qStar| ≤ δ → |deriv (V A) x| ≤ κ) ∧
      ∀ x : ℝ, |x - qStar| ≤ δ →
        |V A x - qStar| ≤ κ * |x - qStar| := by
  let μ := deriv (V A) qStar
  have hμ : μ ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa only [μ] using V_multiplier_mem_Ioo hA hqStar hfix
  obtain ⟨L, hL, hLip⟩ :=
    exists_deriv_V_lipschitzOn_Icc
      (A := A) (a := qStar / 2) (b := 3 * qStar / 2) hA (by linarith [hqStar.1])
  let d := (1 - μ) / 2
  let κ := (μ + 1) / 2
  let δ := min (min (qStar / 2) ((1 - qStar) / 2)) (d / (L + 1))
  have hd : 0 < d := by dsimp [d]; linarith [hμ.2]
  have hLone : 0 < L + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min
      (lt_min (by linarith [hqStar.1]) (by linarith [hqStar.2]))
      (div_pos hd hLone)
  have hδcompact : δ ≤ min (qStar / 2) ((1 - qStar) / 2) := by
    dsimp [δ]
    exact min_le_left _ _
  have hδq : δ ≤ qStar / 2 := by
    exact hδcompact.trans (min_le_left _ _)
  have hLδ : L * δ ≤ d := by
    calc
      L * δ ≤ L * (d / (L + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hL
      _ = d * (L / (L + 1)) := by ring
      _ ≤ d * 1 := by
        gcongr
        rw [div_le_iff₀ hLone]
        linarith
      _ = d := mul_one _
  have hκ0 : 0 ≤ κ := by dsimp [κ]; linarith [hμ.1]
  have hκ1 : κ < 1 := by dsimp [κ]; linarith [hμ.2]
  have hqmem : qStar ∈ Set.Icc (qStar / 2) (3 * qStar / 2) := by
    constructor <;> linarith [hqStar.1]
  have hderiv :
      ∀ x : ℝ, |x - qStar| ≤ δ → |deriv (V A) x| ≤ κ := by
    intro x hx
    have hxmem : x ∈ Set.Icc (qStar / 2) (3 * qStar / 2) := by
      rw [abs_le] at hx
      constructor <;> linarith [hδq]
    have hdiff := hLip qStar hqmem x hxmem
    have hdiff' :
        |deriv (V A) x - μ| ≤ L * |x - qStar| := by
      simpa only [μ] using hdiff
    calc
      |deriv (V A) x| =
          |μ + (deriv (V A) x - μ)| := by
            congr 1
            ring
      _ ≤ |μ| + |deriv (V A) x - μ| := abs_add_le _ _
      _ = μ + |deriv (V A) x - μ| := by rw [abs_of_pos hμ.1]
      _ ≤ μ + L * |x - qStar| := by linarith [hdiff']
      _ ≤ μ + L * δ := by gcongr
      _ ≤ μ + d := by linarith [hLδ]
      _ = κ := by dsimp [d, κ]; ring
  refine ⟨κ, δ, hκ0, hκ1, hδ, hδcompact, hderiv, ?_⟩
  intro x hx
  have hxmem : x ∈ Set.Icc (qStar - δ) (qStar + δ) := by
    rw [abs_le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hqmem' : qStar ∈ Set.Icc (qStar - δ) (qStar + δ) := by
    constructor <;> linarith [hδ]
  have hdiff : ∀ y ∈ Set.Icc (qStar - δ) (qStar + δ),
      DifferentiableAt ℝ (V A) y := by
    intro y hy
    have hypos : 0 < y := by linarith [hqStar.1, hδq, hy.1]
    exact (hasDerivAt_V hA hypos).differentiableAt
  have hbound : ∀ y ∈ Set.Icc (qStar - δ) (qStar + δ),
      ‖deriv (V A) y‖ ≤ κ := by
    intro y hy
    rw [Real.norm_eq_abs]
    apply hderiv y
    rw [abs_le]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hmv :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (qStar - δ) (qStar + δ)) hqmem' hxmem
  simpa only [Real.norm_eq_abs, hfix] using hmv

/-- A positive attracting fixed point has a compact invariant contraction
neighborhood. -/
lemma exists_local_V_contraction {A qStar : ℝ}
    (hA : A ≠ 0) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ δ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ 0 < δ ∧ δ ≤ qStar / 2 ∧
      ∀ x : ℝ, |x - qStar| ≤ δ →
        |V A x - qStar| ≤ κ * |x - qStar| := by
  obtain ⟨κ, δ, hκ0, hκ1, hδ, hδcompact, _hderiv, hcontract⟩ :=
    exists_local_V_contraction_with_deriv hA hqStar hfix
  exact ⟨κ, δ, hκ0, hκ1, hδ,
    hδcompact.trans (min_le_left _ _), hcontract⟩

/-- Inside the local contraction neighborhood, every iterate has the expected
geometric bound and the total orbit displacement from the fixed point is
summable.  This is the summability input for the paper's Koenigs product. -/
theorem exists_local_geometric_contraction_and_summable {A qStar : ℝ}
    (hA : A ≠ 0) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ∃ κ δ : ℝ, 0 ≤ κ ∧ κ < 1 ∧ 0 < δ ∧
      ∀ x : ℝ, |x - qStar| ≤ δ →
        (∀ n : ℕ,
          |(V A)^[n] x - qStar| ≤ κ ^ n * |x - qStar|) ∧
        Summable (fun n : ℕ => |(V A)^[n] x - qStar|) := by
  obtain ⟨κ, δ, hκ0, hκ1, hδ, _hδq, hcontract⟩ :=
    exists_local_V_contraction hA hqStar hfix
  refine ⟨κ, δ, hκ0, hκ1, hδ, ?_⟩
  intro x hx
  have hκle : κ ≤ 1 := hκ1.le
  have hiter :
      ∀ n : ℕ, |(V A)^[n] x - qStar| ≤ κ ^ n * |x - qStar| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hinv : |(V A)^[n] x - qStar| ≤ δ := by
          calc
            |(V A)^[n] x - qStar| ≤ κ ^ n * |x - qStar| := ih
            _ ≤ 1 * |x - qStar| := by
              gcongr
              exact pow_le_one₀ hκ0 hκle
            _ ≤ δ := by simpa using hx
        rw [Function.iterate_succ_apply']
        calc
          |V A ((V A)^[n] x) - qStar| ≤
              κ * |(V A)^[n] x - qStar| :=
            hcontract _ hinv
          _ ≤ κ * (κ ^ n * |x - qStar|) :=
            mul_le_mul_of_nonneg_left ih hκ0
          _ = κ ^ (n + 1) * |x - qStar| := by
            rw [pow_succ']
            ring
  refine ⟨hiter, ?_⟩
  have hgeom :
      Summable (fun n : ℕ => κ ^ n * |x - qStar|) :=
    (summable_geometric_of_lt_one hκ0 hκ1).mul_right _
  exact hgeom.of_nonneg_of_le (fun n => abs_nonneg _) hiter

/-- Every supercritical deterministic orbit from the paper's full range
`q ∈ (0, 1]` has summable displacement from the positive fixed point.
Global orbit convergence supplies a finite entrance time into the local
contraction neighborhood; `summable_nat_add_iff` then restores the discarded
finite prefix. -/
theorem summable_abs_V_orbit_sub_fixed {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    Summable (fun n : ℕ => |(V A)^[n] q - qStar|) := by
  obtain ⟨_κ, δ, _hκ0, _hκ1, hδ, hlocal⟩ :=
    exists_local_geometric_contraction_and_summable
      (A := A) (qStar := qStar) (by linarith) hqStar hfix
  have htend :
      Tendsto (fun n : ℕ => (V A)^[n] q) atTop (nhds qStar) :=
    V_orbit_tendsto_Ioc hA hqStar hfix hq
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 htend) δ hδ
  have henter : |(V A)^[N] q - qStar| ≤ δ := by
    have henterlt : |(V A)^[N] q - qStar| < δ := by
      simpa only [Real.dist_eq] using hN N le_rfl
    exact henterlt.le
  have htail :
      Summable (fun n : ℕ => |(V A)^[n] ((V A)^[N] q) - qStar|) :=
    (hlocal ((V A)^[N] q) henter).2
  rw [← summable_nat_add_iff N]
  exact htail.congr fun n => by
    rw [Function.iterate_add_apply]

/-! ### Orbitwise Koenigs factors -/

/-- The multiplicative correction appearing in the paper's Koenigs product.
It is the secant multiplier along the deterministic orbit, normalized by the
fixed-point multiplier. -/
noncomputable def koenigsOrbitFactor
    (A qStar q : ℝ) (n : ℕ) : ℝ :=
  ((V A ((V A)^[n] q) - qStar) / ((V A)^[n] q - qStar)) /
    deriv (V A) qStar

/-- An orbit started away from the positive fixed point never hits it.
Indeed, strict monotonicity of `V_A` preserves whichever strict side of
`qStar` contains the initial point. -/
lemma V_iterate_ne_fixed {A qStar q : ℝ}
    (hA : A ≠ 0) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) (n : ℕ) :
    (V A)^[n] q ≠ qStar := by
  rcases lt_or_gt_of_ne hqne with hqleft | hqright
  · have hside : ∀ m : ℕ, 0 < (V A)^[m] q ∧ (V A)^[m] q < qStar := by
      intro m
      induction m with
      | zero => simpa using And.intro hq.1 hqleft
      | succ m ih =>
          rw [Function.iterate_succ_apply']
          have hm_mem : (V A)^[m] q ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨ih.1.le, (ih.2.trans hqStar.2).le⟩
          have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨le_rfl, zero_le_one⟩
          have hstar_mem : qStar ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨hqStar.1.le, hqStar.2.le⟩
          constructor
          · have hpos :=
              V_strictMonoOn hA hzero_mem hm_mem ih.1
            simpa only [V_zero] using hpos
          · have hlt :=
              V_strictMonoOn hA hm_mem hstar_mem ih.2
            simpa only [hfix] using hlt
    exact (hside n).2.ne
  · have hside : ∀ m : ℕ, qStar < (V A)^[m] q ∧ (V A)^[m] q ≤ 1 := by
      intro m
      induction m with
      | zero => simpa using And.intro hqright hq.2
      | succ m ih =>
          rw [Function.iterate_succ_apply']
          have hm_mem : (V A)^[m] q ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨hqStar.1.le.trans ih.1.le, ih.2⟩
          have hstar_mem : qStar ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨hqStar.1.le, hqStar.2.le⟩
          constructor
          · have hgt :=
              V_strictMonoOn hA hstar_mem hm_mem ih.1
            simpa only [hfix] using hgt
          · exact (V_lt_one A ((V A)^[m] q)).le
    exact (hside n).1.ne'

/-- The deviations of the orbitwise Koenigs factors from one are summable.
After the orbit enters the fixed compact neighborhood of `qStar`, the local
secant estimate bounds each deviation by a constant times the corresponding
orbit displacement; the latter series is globally summable. -/
theorem summable_abs_koenigsOrbitFactor_sub_one {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) :
    Summable (fun n : ℕ => |koenigsOrbitFactor A qStar q n - 1|) := by
  let μ := deriv (V A) qStar
  have hA0 : A ≠ 0 := by linarith
  have hμ : 0 < μ := by
    exact (V_multiplier_mem_Ioo hA0 hqStar hfix).1
  obtain ⟨L, hL, hfactor⟩ :=
    exists_koenigsFactorEstimate hA0 hqStar.1 hfix
  have horbit :
      Summable (fun n : ℕ => |(V A)^[n] q - qStar|) :=
    summable_abs_V_orbit_sub_fixed hA hqStar hfix hq
  have hmajor :
      Summable (fun n : ℕ => (L / μ) * |(V A)^[n] q - qStar|) :=
    Summable.mul_left (L / μ) horbit
  have htend :
      Tendsto (fun n : ℕ => (V A)^[n] q) atTop (nhds qStar) :=
    V_orbit_tendsto_Ioc hA hqStar hfix hq
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 htend) (qStar / 2) (by linarith [hqStar.1])
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [eventually_atTop.2 ⟨N, hN⟩] with n hn
  let y := (V A)^[n] q
  have hyclose : |y - qStar| < qStar / 2 := by
    simpa only [y, Real.dist_eq] using hn
  have hymem : y ∈ Set.Icc (qStar / 2) (3 * qStar / 2) := by
    rw [abs_lt] at hyclose
    constructor <;> linarith [hyclose.1, hyclose.2]
  have hyne : y ≠ qStar :=
    V_iterate_ne_fixed hA0 hqStar hfix hq hqne n
  have hsecant :
      |(V A y - qStar) / (y - qStar) - μ| ≤ L * |y - qStar| :=
    hfactor y hymem hyne
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  change
    |((V A y - qStar) / (y - qStar)) / μ - 1| ≤
      (L / μ) * |y - qStar|
  calc
    |((V A y - qStar) / (y - qStar)) / μ - 1| =
        |(V A y - qStar) / (y - qStar) - μ| / μ := by
          rw [div_sub_one hμ.ne', abs_div, abs_of_pos hμ]
    _ ≤ (L * |y - qStar|) / μ :=
      (div_le_div_iff_of_pos_right hμ).2 hsecant
    _ = (L / μ) * |y - qStar| := by ring

/-- Every Koenigs factor along a nonstationary supercritical orbit is
positive.  The orbit remains in `(0, 1]` and on one strict side of `qStar`;
strict monotonicity therefore gives the numerator and denominator of the
secant multiplier the same sign. -/
lemma koenigsOrbitFactor_pos {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) (n : ℕ) :
    0 < koenigsOrbitFactor A qStar q n := by
  have hA0 : A ≠ 0 := by linarith
  have hμ : 0 < deriv (V A) qStar :=
    (V_multiplier_mem_Ioo hA0 hqStar hfix).1
  have horbit_mem : ∀ m : ℕ, (V A)^[m] q ∈ Set.Ioc (0 : ℝ) 1 := by
    intro m
    induction m with
    | zero => simpa using hq
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        have hzero_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨le_rfl, zero_le_one⟩
        have hm_mem : (V A)^[m] q ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨ih.1.le, ih.2⟩
        constructor
        · have hpos := V_strictMonoOn hA0 hzero_mem hm_mem ih.1
          simpa only [V_zero] using hpos
        · exact (V_lt_one A ((V A)^[m] q)).le
  let y := (V A)^[n] q
  have hymem : y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(horbit_mem n).1.le, (horbit_mem n).2⟩
  have hstar_mem : qStar ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hqStar.1.le, hqStar.2.le⟩
  have hyne : y ≠ qStar :=
    V_iterate_ne_fixed hA0 hqStar hfix hq hqne n
  rw [koenigsOrbitFactor]
  change 0 < ((V A y - qStar) / (y - qStar)) / deriv (V A) qStar
  rcases lt_or_gt_of_ne hyne with hylt | hygt
  · have hVlt : V A y < qStar := by
      have := V_strictMonoOn hA0 hymem hstar_mem hylt
      simpa only [hfix] using this
    exact div_pos (div_pos_of_neg_of_neg (sub_neg.mpr hVlt) (sub_neg.mpr hylt)) hμ
  · have hVgt : qStar < V A y := by
      have := V_strictMonoOn hA0 hstar_mem hymem hygt
      simpa only [hfix] using this
    exact div_pos (div_pos (sub_pos.mpr hVgt) (sub_pos.mpr hygt)) hμ

/-- The infinite product of the orbitwise Koenigs correction factors. -/
noncomputable def koenigsOrbitProduct (A qStar q : ℝ) : ℝ :=
  ∏' n : ℕ, koenigsOrbitFactor A qStar q n

/-- The orbitwise Koenigs product converges and is nonzero.  Absolute
summability of `factor - 1` gives convergence through
`Real.multipliable_one_add_of_summable`; pointwise positivity rules out a
vanishing factor and hence makes the infinite product nonzero. -/
theorem multipliable_koenigsOrbitFactor_and_product_ne_zero
    {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) :
    Multipliable (koenigsOrbitFactor A qStar q) ∧
      koenigsOrbitProduct A qStar q ≠ 0 := by
  have habs :=
    summable_abs_koenigsOrbitFactor_sub_one hA hqStar hfix hq hqne
  have herr :
      Summable (fun n : ℕ => koenigsOrbitFactor A qStar q n - 1) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using habs
  have hmult_one :
      Multipliable (fun n : ℕ =>
        1 + (koenigsOrbitFactor A qStar q n - 1)) :=
    Real.multipliable_one_add_of_summable herr
  have hne :
      ∀ n : ℕ, 1 + (koenigsOrbitFactor A qStar q n - 1) ≠ 0 := by
    intro n
    have hpos :=
      koenigsOrbitFactor_pos hA hqStar hfix hq hqne n
    linarith
  have hmult : Multipliable (koenigsOrbitFactor A qStar q) :=
    hmult_one.congr fun n => by ring
  have hprod_one_ne :=
    tprod_one_add_ne_zero_of_summable
      (f := fun n : ℕ => koenigsOrbitFactor A qStar q n - 1)
      hne (by simpa only [Real.norm_eq_abs] using habs)
  have hprod_eq :
      koenigsOrbitProduct A qStar q =
        ∏' n : ℕ, (1 + (koenigsOrbitFactor A qStar q n - 1)) := by
    unfold koenigsOrbitProduct
    apply tprod_congr
    intro n
    ring
  constructor
  · exact hmult
  · rw [hprod_eq]
    exact hprod_one_ne

/-! ### Pointwise Koenigs limit -/

/-- The finite Koenigs product telescopes to the normalized deterministic
orbit.  This is the finite identity displayed in the paper before passing to
the infinite product. -/
lemma mul_prod_range_koenigsOrbitFactor_eq_normalized
    {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) (n : ℕ) :
    (q - qStar) *
        ∏ j ∈ Finset.range n, koenigsOrbitFactor A qStar q j =
      ((V A)^[n] q - qStar) * (deriv (V A) qStar)⁻¹ ^ n := by
  have hA0 : A ≠ 0 := by linarith
  have hμ : 0 < deriv (V A) qStar :=
    (V_multiplier_mem_Ioo hA0 hqStar hfix).1
  induction n with
  | zero => simp
  | succ n ih =>
      have horbit_ne : (V A)^[n] q - qStar ≠ 0 :=
        sub_ne_zero.mpr (V_iterate_ne_fixed hA0 hqStar hfix hq hqne n)
      rw [Finset.prod_range_succ, ← mul_assoc, ih,
        Function.iterate_succ_apply', koenigsOrbitFactor, pow_succ]
      field_simp [horbit_ne, hμ.ne']

/-- The pointwise Koenigs coefficient is nonzero away from the fixed point. -/
lemma mul_koenigsOrbitProduct_ne_zero {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) :
    (q - qStar) * koenigsOrbitProduct A qStar q ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hqne)
    (multipliable_koenigsOrbitFactor_and_product_ne_zero
      hA hqStar hfix hq hqne).2

/-- The normalized deterministic orbit converges pointwise to its nonzero
Koenigs coefficient.  The finite telescoping identity transfers convergence
of the partial products to the normalized orbit. -/
theorem tendsto_normalized_V_orbit_sub_fixed {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) :
    Tendsto
      (fun n : ℕ =>
        ((V A)^[n] q - qStar) * (deriv (V A) qStar)⁻¹ ^ n)
      atTop
      (nhds ((q - qStar) * koenigsOrbitProduct A qStar q)) := by
  have hmult :=
    (multipliable_koenigsOrbitFactor_and_product_ne_zero
      hA hqStar hfix hq hqne).1
  have hprod :
      Tendsto
        (fun n : ℕ =>
          ∏ j ∈ Finset.range n, koenigsOrbitFactor A qStar q j)
        atTop (nhds (koenigsOrbitProduct A qStar q)) := by
    simpa only [koenigsOrbitProduct] using hmult.tendsto_prod_tprod_nat
  have hscaled :=
    hprod.const_mul (q - qStar)
  exact hscaled.congr' <| Eventually.of_forall fun n =>
    mul_prod_range_koenigsOrbitFactor_eq_normalized
      hA hqStar hfix hq hqne n

/-! ### Pointwise Koenigs asymptotic -/

/-- The coefficient in the pointwise Koenigs asymptotic. -/
noncomputable def koenigsCoefficient (A qStar q : ℝ) : ℝ :=
  (q - qStar) * koenigsOrbitProduct A qStar q

/-- Away from the fixed point, the pointwise Koenigs coefficient is nonzero. -/
lemma koenigsCoefficient_ne_zero {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) :
    koenigsCoefficient A qStar q ≠ 0 := by
  simpa only [koenigsCoefficient] using
    mul_koenigsOrbitProduct_ne_zero hA hqStar hfix hq hqne

/-- Pointwise Koenigs asymptotic in little-`o` form:
`V_A^n(q) - qStar = C(q) μ^n + o(μ^n)`.  It is the direct ratio
reformulation of `tendsto_normalized_V_orbit_sub_fixed`. -/
theorem V_orbit_sub_fixed_sub_koenigsCoefficient_mul_pow_isLittleO
    {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1)
    (hqne : q ≠ qStar) :
    Asymptotics.IsLittleO atTop
      (fun n : ℕ =>
        ((V A)^[n] q - qStar) -
          koenigsCoefficient A qStar q * deriv (V A) qStar ^ n)
      (fun n : ℕ => deriv (V A) qStar ^ n) := by
  let μ := deriv (V A) qStar
  let C := koenigsCoefficient A qStar q
  have hA0 : A ≠ 0 := by linarith
  have hμ : 0 < μ := by
    exact (V_multiplier_mem_Ioo hA0 hqStar hfix).1
  have hnorm :
      Tendsto
        (fun n : ℕ => ((V A)^[n] q - qStar) * μ⁻¹ ^ n)
        atTop (nhds C) := by
    simpa only [μ, C, koenigsCoefficient] using
      tendsto_normalized_V_orbit_sub_fixed hA hqStar hfix hq hqne
  have hzero :
      Tendsto
        (fun n : ℕ => ((V A)^[n] q - qStar) * μ⁻¹ ^ n - C)
        atTop (nhds 0) :=
    tendsto_sub_nhds_zero_iff.mpr hnorm
  apply Asymptotics.isLittleO_of_tendsto
  · intro n hn
    exact (pow_ne_zero n hμ.ne' hn).elim
  · apply hzero.congr'
    filter_upwards with n
    change
      ((V A)^[n] q - qStar) * μ⁻¹ ^ n - C =
        (((V A)^[n] q - qStar) - C * μ ^ n) / μ ^ n
    rw [inv_pow]
    rw [eq_div_iff (pow_ne_zero n hμ.ne')]
    field_simp [pow_ne_zero n hμ.ne']

/-! ### Uniform entrance near a nonstationary initial point -/

/-- One deterministic update cannot increase the distance to the positive
fixed point on the canonical positive radius interval. -/
lemma abs_V_sub_fixed_le_abs_sub_fixed
    {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    |V A q - qStar| ≤ |q - qStar| := by
  have hA0 : A ≠ 0 := by linarith
  have hqIcc : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2⟩
  have hqStarIcc : qStar ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hqStar.1.le, hqStar.2.le⟩
  rcases le_total q qStar with hle | hge
  · have hVle : V A q ≤ qStar := by
      have hmono :=
        (V_strictMonoOn hA0).monotoneOn hqIcc hqStarIcc hle
      simpa only [hfix] using hmono
    have hqV : q ≤ V A q := by
      rcases eq_or_lt_of_le hle with heq | hlt
      · rw [heq, hfix]
      · exact (V_gt_self_of_lt_fixed hA0 hqStar hfix
          ⟨hq.1, hlt.trans hqStar.2⟩ hlt).le
    rw [abs_of_nonpos (sub_nonpos.mpr hVle),
      abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  · have hVge : qStar ≤ V A q := by
      have hmono :=
        (V_strictMonoOn hA0).monotoneOn hqStarIcc hqIcc hge
      simpa only [hfix] using hmono
    have hVq : V A q ≤ q := by
      rcases eq_or_lt_of_le hge with heq | hgt
      · rw [← heq, hfix]
      · by_cases hq1 : q = 1
        · rw [hq1]
          exact (V_lt_one A 1).le
        · have hqlt : q < 1 := lt_of_le_of_ne hq.2 hq1
          exact (V_lt_self_of_gt_fixed hA0 hqStar hfix
            ⟨hq.1, hqlt⟩ hgt).le
    rw [abs_of_nonneg (sub_nonneg.mpr hVge),
      abs_of_nonneg (sub_nonneg.mpr hge)]
    linarith

/-- Along every positive deterministic orbit, the distance to the positive
fixed point is nonincreasing. -/
lemma antitone_abs_V_iterate_sub_fixed
    {A qStar q : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq : q ∈ Set.Ioc (0 : ℝ) 1) :
    Antitone (fun n : ℕ => |(V A)^[n] q - qStar|) := by
  have hA0 : A ≠ 0 := by linarith
  have horbit : ∀ n : ℕ, (V A)^[n] q ∈ Set.Ioc (0 : ℝ) 1 := by
    intro n
    induction n with
    | zero => simpa using hq
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨le_rfl, zero_le_one⟩
        have hn : (V A)^[n] q ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨ih.1.le, ih.2⟩
        constructor
        · have hpos := V_strictMonoOn hA0 hzero hn ih.1
          simpa only [V_zero] using hpos
        · exact (V_lt_one A ((V A)^[n] q)).le
  apply antitone_nat_of_succ_le
  intro n
  rw [Function.iterate_succ_apply']
  exact abs_V_sub_fixed_le_abs_sub_fixed hA hqStar hfix (horbit n)

/-- On every compact interval bounded away from zero, one deterministic
iterate time makes every orbit uniformly close to the positive fixed point. -/
lemma exists_uniform_V_iterate_abs_sub_fixed_lt
    {A qStar r ε : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hr : r ∈ Set.Ioc (0 : ℝ) 1)
    (hε : 0 < ε) :
    ∃ m : ℕ, ∀ q ∈ Set.Icc r 1, |(V A)^[m] q - qStar| < ε := by
  have huniform :
      TendstoUniformlyOn
        (fun n q => |(V A)^[n] q - qStar|) (fun _ => 0)
        atTop (Set.Icc r 1) := by
    apply Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
    · intro n
      exact ((((V_continuous A).iterate n).sub continuous_const).abs).continuousOn
    · intro q hq
      exact antitone_abs_V_iterate_sub_fixed hA hqStar hfix
        ⟨lt_of_lt_of_le hr.1 hq.1, hq.2⟩
    · exact continuous_const.continuousOn
    · intro q hq
      have hqIoc : q ∈ Set.Ioc (0 : ℝ) 1 :=
        ⟨lt_of_lt_of_le hr.1 hq.1, hq.2⟩
      simpa using
        ((V_orbit_tendsto_Ioc hA hqStar hfix hqIoc).sub
          (tendsto_const_nhds (x := qStar))).abs
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  obtain ⟨m, hm⟩ := (huniform ε hε).exists
  refine ⟨m, fun q hq => ?_⟩
  simpa [Real.dist_eq] using hm q hq

/-- Every deterministic orbit starting in a compact interval bounded away
from zero enters one common contraction interval with a positive margin. -/
lemma exists_uniform_V_iterate_stable_margin
    {A qStar r : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hr : r ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ κ R η : ℝ, ∃ m : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      (∀ x : ℝ, |x - qStar| ≤ R →
        |V A x - qStar| ≤ κ * |x - qStar|) ∧
      ∀ q ∈ Set.Icc r 1, |(V A)^[m] q - qStar| ≤ R - η := by
  have hA0 : A ≠ 0 := by linarith
  obtain ⟨κ, R, hκ0, hκ1, hR, hRcompact, hderiv, hcontract⟩ :=
    exists_local_V_contraction_with_deriv hA0 hqStar hfix
  have hRq : R ≤ qStar / 2 :=
    hRcompact.trans (min_le_left _ _)
  have hRone : R ≤ (1 - qStar) / 2 :=
    hRcompact.trans (min_le_right _ _)
  have hRinterior : R < min qStar (1 - qStar) := by
    exact lt_min
      (hRq.trans_lt (by linarith [hqStar.1]))
      (hRone.trans_lt (by linarith [hqStar.2]))
  obtain ⟨m, hm⟩ :=
    exists_uniform_V_iterate_abs_sub_fixed_lt
      hA hqStar hfix hr (show 0 < R / 2 by linarith)
  refine ⟨κ, R, R / 2, m, hκ0, hκ1, by linarith, by linarith,
    hRinterior, hderiv, hcontract, ?_⟩
  intro q hq
  rw [show R - R / 2 = R / 2 by ring]
  exact (hm q hq).le

/-- The deterministic stable-interval entrance is uniform over every compact
interval bounded away from zero, with one geometric bound after entry. -/
theorem exists_uniform_stable_V_orbit_interval_Icc
    {A qStar r : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hr : r ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ κ R η : ℝ, ∃ m : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ q ∈ Set.Icc r 1, ∀ n : ℕ,
        |(V A)^[n + m] q - qStar| ≤ κ ^ n * (R - η) := by
  obtain ⟨κ, R, η, m, hκ0, hκ1, hη0, hηR, hRinterior,
      hderiv, hcontract, hentry⟩ :=
    exists_uniform_V_iterate_stable_margin hA hqStar hfix hr
  refine ⟨κ, R, η, m, hκ0, hκ1, hη0, hηR, hRinterior,
    hderiv, ?_⟩
  intro q hq
  have hmentry : |(V A)^[m] q - qStar| ≤ R - η :=
    hentry q hq
  have hmentryR : |(V A)^[m] q - qStar| ≤ R := by
    linarith
  have hκle : κ ≤ 1 := hκ1.le
  have hiter :
      ∀ n : ℕ,
        |(V A)^[n] ((V A)^[m] q) - qStar| ≤
          κ ^ n * |(V A)^[m] q - qStar| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hinv :
            |(V A)^[n] ((V A)^[m] q) - qStar| ≤ R := by
          calc
            |(V A)^[n] ((V A)^[m] q) - qStar| ≤
                κ ^ n * |(V A)^[m] q - qStar| := ih
            _ ≤ 1 * |(V A)^[m] q - qStar| := by
              gcongr
              exact pow_le_one₀ hκ0 hκle
            _ ≤ R := by simpa using hmentryR
        rw [Function.iterate_succ_apply']
        calc
          |V A ((V A)^[n] ((V A)^[m] q)) - qStar| ≤
              κ * |(V A)^[n] ((V A)^[m] q) - qStar| :=
            hcontract _ hinv
          _ ≤ κ * (κ ^ n * |(V A)^[m] q - qStar|) :=
            mul_le_mul_of_nonneg_left ih hκ0
          _ = κ ^ (n + 1) * |(V A)^[m] q - qStar| := by
            rw [pow_succ']
            ring
  intro n
  rw [Function.iterate_add_apply]
  exact (hiter n).trans
    (mul_le_mul_of_nonneg_left hmentry (pow_nonneg hκ0 n))

/-- Every sufficiently small relative neighborhood of an initial point has a
common entrance time into the strict interior of a compact contraction
interval around the positive fixed point.  No nonstationarity assumption on
the initial point is needed. -/
theorem exists_uniform_stable_V_orbit_interval
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ κ R η r : ℝ, ∃ s : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧ 0 < r ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ q ∈ Set.Ioc (0 : ℝ) 1, |q - q₀| < r →
        ∀ n : ℕ,
          |(V A)^[n + s] q - qStar| ≤ κ ^ n * (R - η) := by
  have hA0 : A ≠ 0 := by linarith
  obtain ⟨κ, R, hκ0, hκ1, hR, hRcompact, hderiv, hcontract⟩ :=
    exists_local_V_contraction_with_deriv hA0 hqStar hfix
  have hRq : R ≤ qStar / 2 :=
    hRcompact.trans (min_le_left _ _)
  have hRone : R ≤ (1 - qStar) / 2 :=
    hRcompact.trans (min_le_right _ _)
  have hRinterior : R < min qStar (1 - qStar) := by
    exact lt_min
      (hRq.trans_lt (by linarith [hqStar.1]))
      (hRone.trans_lt (by linarith [hqStar.2]))
  have htend :
      Tendsto (fun n : ℕ => (V A)^[n] q₀) atTop (nhds qStar) :=
    V_orbit_tendsto_Ioc hA hqStar hfix hq₀
  obtain ⟨s, hs⟩ :=
    (Metric.tendsto_atTop.1 htend) (R / 4) (by linarith)
  have hsclose :
      dist ((V A)^[s] q₀) qStar < R / 4 :=
    hs s le_rfl
  have hcont : Continuous ((V A)^[s]) :=
    (V_continuous A).iterate s
  obtain ⟨r, hr, hrmap⟩ :=
    (Metric.continuousAt_iff.1 hcont.continuousAt)
      (R / 4) (by linarith)
  refine ⟨κ, R, R / 2, r, s, hκ0, hκ1, by linarith,
    by linarith, hRinterior, hr, hderiv, ?_⟩
  intro q _hq hqclose
  have hqr : dist q q₀ < r := by
    simpa only [Real.dist_eq] using hqclose
  have hsmap :
      dist ((V A)^[s] q) ((V A)^[s] q₀) < R / 4 :=
    hrmap hqr
  have hsentrylt : |(V A)^[s] q - qStar| < R / 2 := by
    rw [← Real.dist_eq]
    calc
      dist ((V A)^[s] q) qStar ≤
          dist ((V A)^[s] q) ((V A)^[s] q₀) +
            dist ((V A)^[s] q₀) qStar :=
        dist_triangle _ _ _
      _ < R / 4 + R / 4 := add_lt_add hsmap hsclose
      _ = R / 2 := by ring
  have hsentry : |(V A)^[s] q - qStar| ≤ R - R / 2 := by
    rw [show R - R / 2 = R / 2 by ring]
    exact hsentrylt.le
  have hsentryR : |(V A)^[s] q - qStar| ≤ R := by
    linarith
  have hκle : κ ≤ 1 := hκ1.le
  have hiter :
      ∀ n : ℕ,
        |(V A)^[n] ((V A)^[s] q) - qStar| ≤
          κ ^ n * |(V A)^[s] q - qStar| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hinv :
            |(V A)^[n] ((V A)^[s] q) - qStar| ≤ R := by
          calc
            |(V A)^[n] ((V A)^[s] q) - qStar| ≤
                κ ^ n * |(V A)^[s] q - qStar| := ih
            _ ≤ 1 * |(V A)^[s] q - qStar| := by
              gcongr
              exact pow_le_one₀ hκ0 hκle
            _ ≤ R := by simpa using hsentryR
        rw [Function.iterate_succ_apply']
        calc
          |V A ((V A)^[n] ((V A)^[s] q)) - qStar| ≤
              κ * |(V A)^[n] ((V A)^[s] q) - qStar| :=
            hcontract _ hinv
          _ ≤ κ * (κ ^ n * |(V A)^[s] q - qStar|) :=
            mul_le_mul_of_nonneg_left ih hκ0
          _ = κ ^ (n + 1) * |(V A)^[s] q - qStar| := by
            rw [pow_succ']
            ring
  intro n
  rw [Function.iterate_add_apply]
  exact (hiter n).trans
    (mul_le_mul_of_nonneg_left hsentry (pow_nonneg hκ0 n))

/-- A sequence of initial points converging inside `(0, 1]` eventually has a
common entrance time and contraction interval.  This is the sequence-facing
form of the deterministic stable-interval entrance used for the
finite-dimensional initial conditions in the paper. -/
theorem exists_eventually_stable_V_orbit_interval
    {A qStar q₀ : ℝ} (qN : ℕ → ℝ)
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hqN : Tendsto qN atTop (nhds q₀))
    (hqNmem : ∀ᶠ N : ℕ in atTop, qN N ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ κ R η : ℝ, ∃ s N₀ : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < η ∧ η < R ∧
      R < min qStar (1 - qStar) ∧
      (∀ x : ℝ, |x - qStar| ≤ R → |deriv (V A) x| ≤ κ) ∧
      ∀ N ≥ N₀, ∀ n : ℕ,
        |(V A)^[n + s] (qN N) - qStar| ≤ κ ^ n * (R - η) := by
  obtain ⟨κ, R, η, r, s, hκ0, hκ1, hη, hηR, hRinterior, hr,
      hderiv, hstable⟩ :=
    exists_uniform_stable_V_orbit_interval hA hqStar hfix hq₀
  obtain ⟨Nclose, hNclose⟩ :=
    (Metric.tendsto_atTop.1 hqN) r hr
  obtain ⟨Nmem, hNmem⟩ :=
    eventually_atTop.1 hqNmem
  refine ⟨κ, R, η, s, max Nclose Nmem, hκ0, hκ1, hη, hηR,
    hRinterior, hderiv, ?_⟩
  intro N hN n
  apply hstable (qN N)
  · exact hNmem N ((le_max_right Nclose Nmem).trans hN)
  · simpa only [Real.dist_eq] using
      hNclose N ((le_max_left Nclose Nmem).trans hN)

/-- A relative compact neighborhood of any `q₀ ≠ qStar` has a common finite
entrance time into one contraction neighborhood of `qStar`.  From that time
on, every orbit in the neighborhood is controlled by the same summable
geometric majorant.  The neighborhood radius also keeps every initial point
away from both `0` and `qStar`. -/
theorem exists_uniform_eventual_geometric_V_orbit_bound
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar) :
    ∃ κ δ r : ℝ, ∃ s : ℕ,
      0 ≤ κ ∧ κ < 1 ∧ 0 < δ ∧ δ ≤ qStar / 2 ∧ 0 < r ∧
      Summable (fun n : ℕ => κ ^ n * δ) ∧
      ∀ q ∈ Set.Ioc (0 : ℝ) 1, |q - q₀| ≤ r →
        q ≠ qStar ∧
        ∀ n : ℕ,
          |(V A)^[n + s] q - qStar| ≤ κ ^ n * δ := by
  have hA0 : A ≠ 0 := by linarith
  obtain ⟨κ, δ, hκ0, hκ1, hδ, hδStar, hcontract⟩ :=
    exists_local_V_contraction hA0 hqStar hfix
  have htend :
      Tendsto (fun n : ℕ => (V A)^[n] q₀) atTop (nhds qStar) :=
    V_orbit_tendsto_Ioc hA hqStar hfix hq₀
  obtain ⟨s, hs⟩ :=
    (Metric.tendsto_atTop.1 htend) (δ / 2) (by linarith)
  have hsclose :
      dist ((V A)^[s] q₀) qStar < δ / 2 :=
    hs s le_rfl
  have hcont : Continuous ((V A)^[s]) :=
    (V_continuous A).iterate s
  obtain ⟨r₀, hr₀, hr₀map⟩ :=
    (Metric.continuousAt_iff.1 hcont.continuousAt)
      (δ / 2) (by linarith)
  have hq₀dist : 0 < |q₀ - qStar| :=
    abs_pos.mpr (sub_ne_zero.mpr hq₀ne)
  let r := min (r₀ / 2) (min (q₀ / 2) (|q₀ - qStar| / 2))
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (by linarith) (lt_min (by linarith [hq₀.1]) (by linarith))
  have hmajor :
      Summable (fun n : ℕ => κ ^ n * δ) :=
    (summable_geometric_of_lt_one hκ0 hκ1).mul_right δ
  refine ⟨κ, δ, r, s, hκ0, hκ1, hδ, hδStar, hr, hmajor, ?_⟩
  intro q hq hqclose
  have hqr₀ : dist q q₀ < r₀ := by
    rw [Real.dist_eq]
    calc
      |q - q₀| ≤ r := hqclose
      _ ≤ r₀ / 2 := by
        dsimp only [r]
        exact min_le_left _ _
      _ < r₀ := by linarith
  have hsmap :
      dist ((V A)^[s] q) ((V A)^[s] q₀) < δ / 2 :=
    hr₀map hqr₀
  have hsentry : |(V A)^[s] q - qStar| ≤ δ := by
    have hsentrylt : |(V A)^[s] q - qStar| < δ := by
      rw [← Real.dist_eq]
      calc
        dist ((V A)^[s] q) qStar ≤
            dist ((V A)^[s] q) ((V A)^[s] q₀) +
              dist ((V A)^[s] q₀) qStar :=
          dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := add_lt_add hsmap hsclose
        _ = δ := by ring
    exact hsentrylt.le
  have hqne : q ≠ qStar := by
    intro heq
    have hdist_le : |q₀ - qStar| ≤ r := by
      rw [heq, abs_sub_comm] at hqclose
      exact hqclose
    have hr_le : r ≤ |q₀ - qStar| / 2 := by
      dsimp only [r]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨hqne, ?_⟩
  have hκle : κ ≤ 1 := hκ1.le
  have hiter :
      ∀ n : ℕ,
        |(V A)^[n] ((V A)^[s] q) - qStar| ≤
          κ ^ n * |(V A)^[s] q - qStar| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hinv :
            |(V A)^[n] ((V A)^[s] q) - qStar| ≤ δ := by
          calc
            |(V A)^[n] ((V A)^[s] q) - qStar| ≤
                κ ^ n * |(V A)^[s] q - qStar| := ih
            _ ≤ 1 * |(V A)^[s] q - qStar| := by
              gcongr
              exact pow_le_one₀ hκ0 hκle
            _ ≤ δ := by simpa using hsentry
        rw [Function.iterate_succ_apply']
        calc
          |V A ((V A)^[n] ((V A)^[s] q)) - qStar| ≤
              κ * |(V A)^[n] ((V A)^[s] q) - qStar| :=
            hcontract _ hinv
          _ ≤ κ * (κ ^ n * |(V A)^[s] q - qStar|) :=
            mul_le_mul_of_nonneg_left ih hκ0
          _ = κ ^ (n + 1) * |(V A)^[s] q - qStar| := by
            rw [pow_succ']
            ring
  intro n
  rw [Function.iterate_add_apply]
  exact (hiter n).trans
    (mul_le_mul_of_nonneg_left hsentry (pow_nonneg hκ0 n))

/-! ### Uniform Koenigs-factor tail bound -/

/-- On a sufficiently small relative compact neighborhood of `q₀`, the
shifted Koenigs-factor errors have one summable numerical majorant.  This is
the Weierstrass bound needed for uniform convergence of the tail product. -/
theorem exists_uniform_summable_koenigsOrbitFactor_tail_bound
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar) :
    ∃ r : ℝ, ∃ s : ℕ, ∃ u : ℕ → ℝ,
      0 < r ∧ r ≤ q₀ / 2 ∧ r ≤ |q₀ - qStar| / 2 ∧
      (∀ n : ℕ, 0 ≤ u n) ∧ Summable u ∧
      ∀ q ∈ Set.Ioc (0 : ℝ) 1, |q - q₀| ≤ r →
        q ≠ qStar ∧
        ∀ n : ℕ,
          |koenigsOrbitFactor A qStar q (n + s) - 1| ≤ u n := by
  have hA0 : A ≠ 0 := by linarith
  let μ := deriv (V A) qStar
  have hμ : 0 < μ := by
    exact (V_multiplier_mem_Ioo hA0 hqStar hfix).1
  obtain ⟨L, hL, hfactor⟩ :=
    exists_koenigsFactorEstimate hA0 hqStar.1 hfix
  obtain ⟨κ, δ, r₀, s, hκ0, hκ1, hδ, hδStar, hr₀,
      hgeom, horbit⟩ :=
    exists_uniform_eventual_geometric_V_orbit_bound
      hA hqStar hfix hq₀ hq₀ne
  let r := min r₀ (min (q₀ / 2) (|q₀ - qStar| / 2))
  let u : ℕ → ℝ := fun n => (L / μ) * (κ ^ n * δ)
  have hq₀dist : 0 < |q₀ - qStar| :=
    abs_pos.mpr (sub_ne_zero.mpr hq₀ne)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min hr₀ (lt_min (by linarith [hq₀.1]) (by linarith))
  have hrupp : r ≤ r₀ := by
    dsimp only [r]
    exact min_le_left _ _
  have hrq₀ : r ≤ q₀ / 2 := by
    dsimp only [r]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrdist : r ≤ |q₀ - qStar| / 2 := by
    dsimp only [r]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hu0 : ∀ n : ℕ, 0 ≤ u n := by
    intro n
    dsimp only [u]
    positivity
  have husum : Summable u := by
    dsimp only [u]
    exact Summable.mul_left (L / μ) hgeom
  refine ⟨r, s, u, hr, hrq₀, hrdist, hu0, husum, ?_⟩
  intro q hq hqclose
  obtain ⟨hqne, hqbound⟩ :=
    horbit q hq (hqclose.trans hrupp)
  refine ⟨hqne, ?_⟩
  intro n
  let y := (V A)^[n + s] q
  have hybound : |y - qStar| ≤ κ ^ n * δ := by
    simpa only [y] using hqbound n
  have hκpow : κ ^ n ≤ 1 :=
    pow_le_one₀ hκ0 hκ1.le
  have hyδ : |y - qStar| ≤ δ := by
    exact hybound.trans <| by
      calc
        κ ^ n * δ ≤ 1 * δ := by gcongr
        _ = δ := one_mul δ
  have hymem : y ∈ Set.Icc (qStar / 2) (3 * qStar / 2) := by
    rw [abs_le] at hyδ
    constructor <;> linarith [hδStar]
  have hyne : y ≠ qStar :=
    V_iterate_ne_fixed hA0 hqStar hfix hq hqne (n + s)
  have hsecant :
      |(V A y - qStar) / (y - qStar) - μ| ≤ L * |y - qStar| :=
    hfactor y hymem hyne
  change
    |((V A y - qStar) / (y - qStar)) / μ - 1| ≤ u n
  calc
    |((V A y - qStar) / (y - qStar)) / μ - 1| =
        |(V A y - qStar) / (y - qStar) - μ| / μ := by
          rw [div_sub_one hμ.ne', abs_div, abs_of_pos hμ]
    _ ≤ (L * |y - qStar|) / μ :=
      (div_le_div_iff_of_pos_right hμ).2 hsecant
    _ ≤ (L * (κ ^ n * δ)) / μ :=
      (div_le_div_iff_of_pos_right hμ).2
        (mul_le_mul_of_nonneg_left hybound hL)
    _ = u n := by
      dsimp only [u]
      ring

/-! ### Uniform convergence of the Koenigs tail product -/

/-- On a closed relative neighborhood of `q₀`, the shifted Koenigs-factor
product converges uniformly.  Each factor is continuous there because the
whole neighborhood stays in `(0, 1] \ {qStar}`, so no orbit denominator
vanishes. -/
theorem exists_hasProdUniformlyOn_koenigsOrbitFactor_tail
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar) :
    ∃ r : ℝ, 0 < r ∧ ∃ s : ℕ,
      q₀ ∈ Set.Icc (q₀ - r) (min (q₀ + r) 1) ∧
      HasProdUniformlyOn
        (fun n q =>
          koenigsOrbitFactor A qStar q (n + s))
        (fun q =>
          ∏' n : ℕ, koenigsOrbitFactor A qStar q (n + s))
        (Set.Icc (q₀ - r) (min (q₀ + r) 1)) := by
  have hA0 : A ≠ 0 := by linarith
  obtain ⟨r, s, u, hr, hrq₀, _hrdist, hu0, husum, hbound⟩ :=
    exists_uniform_summable_koenigsOrbitFactor_tail_bound
      hA hqStar hfix hq₀ hq₀ne
  let K : Set ℝ := Set.Icc (q₀ - r) (min (q₀ + r) 1)
  let e : ℕ → ℝ → ℝ :=
    fun n q => koenigsOrbitFactor A qStar q (n + s) - 1
  have hq₀K : q₀ ∈ K := by
    dsimp only [K]
    exact ⟨by linarith, le_min (by linarith) hq₀.2⟩
  have hKstate : ∀ q ∈ K, q ∈ Set.Ioc (0 : ℝ) 1 := by
    intro q hqK
    dsimp only [K] at hqK
    constructor
    · have hq₀half : 0 < q₀ / 2 := by linarith [hq₀.1]
      have hlow : q₀ / 2 ≤ q₀ - r := by linarith [hrq₀]
      exact hq₀half.trans_le (hlow.trans hqK.1)
    · exact hqK.2.trans (min_le_right _ _)
  have hKclose : ∀ q ∈ K, |q - q₀| ≤ r := by
    intro q hqK
    dsimp only [K] at hqK
    rw [abs_le]
    constructor
    · linarith [hqK.1]
    · linarith [hqK.2, min_le_left (q₀ + r) 1]
  have hcts : ∀ n : ℕ, ContinuousOn (e n) K := by
    intro n
    have hiterCont : Continuous (fun q : ℝ => (V A)^[n + s] q) :=
      (V_continuous A).iterate (n + s)
    have hnumCont :
        Continuous (fun q : ℝ => V A ((V A)^[n + s] q) - qStar) :=
      ((V_continuous A).comp hiterCont).sub continuous_const
    have hdenCont :
        Continuous (fun q : ℝ => (V A)^[n + s] q - qStar) :=
      hiterCont.sub continuous_const
    have hdenne :
        ∀ q ∈ K, (V A)^[n + s] q - qStar ≠ 0 := by
      intro q hqK
      obtain ⟨hqne, _⟩ :=
        hbound q (hKstate q hqK) (hKclose q hqK)
      exact sub_ne_zero.mpr
        (V_iterate_ne_fixed hA0 hqStar hfix (q := q) (hKstate q hqK)
          hqne (n + s))
    have hfactorCont :
        ContinuousOn
          (fun q : ℝ => koenigsOrbitFactor A qStar q (n + s)) K := by
      simpa only [koenigsOrbitFactor, Pi.div_apply] using
        (hnumCont.continuousOn.div hdenCont.continuousOn hdenne).div_const
          (deriv (V A) qStar)
    exact hfactorCont.sub continuousOn_const
  have huniform :
      ∀ᶠ n : ℕ in atTop, ∀ q ∈ K, ‖e n q‖ ≤ u n := by
    filter_upwards with n
    intro q hqK
    have hqbound :=
      (hbound q (hKstate q hqK) (hKclose q hqK)).2 n
    simpa only [e, Real.norm_eq_abs] using hqbound
  have hprodOne :
      HasProdUniformlyOn
        (fun n q => 1 + e n q)
        (fun q => ∏' n : ℕ, (1 + e n q)) K :=
    husum.hasProdUniformlyOn_nat_one_add isCompact_Icc huniform hcts
  have htermEq :
      (fun n q => 1 + e n q) =
        (fun n q => koenigsOrbitFactor A qStar q (n + s)) := by
    funext n q
    dsimp only [e]
    ring
  have hprodEq :
      (fun q => ∏' n : ℕ, (1 + e n q)) =
        (fun q => ∏' n : ℕ,
          koenigsOrbitFactor A qStar q (n + s)) := by
    funext q
    apply tprod_congr
    intro n
    dsimp only [e]
    ring
  rw [htermEq, hprodEq] at hprodOne
  exact ⟨r, hr, s, hq₀K, hprodOne⟩

/-! ### Local uniformity and continuity of the Koenigs coefficient -/

/-- Every orbitwise Koenigs factor is continuous on a set of nonstationary
initial states.  The exclusion of `qStar` keeps the corresponding orbit
denominator nonzero. -/
lemma continuousOn_koenigsOrbitFactor
    {A qStar : ℝ} {K : Set ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar)
    (hK : K ⊆ Set.Ioc (0 : ℝ) 1 \ {qStar}) (n : ℕ) :
    ContinuousOn
      (fun q : ℝ => koenigsOrbitFactor A qStar q n) K := by
  have hA0 : A ≠ 0 := by linarith
  have hiterCont : Continuous (fun q : ℝ => (V A)^[n] q) :=
    (V_continuous A).iterate n
  have hnumCont :
      Continuous (fun q : ℝ => V A ((V A)^[n] q) - qStar) :=
    ((V_continuous A).comp hiterCont).sub continuous_const
  have hdenCont :
      Continuous (fun q : ℝ => (V A)^[n] q - qStar) :=
    hiterCont.sub continuous_const
  have hdenne :
      ∀ q ∈ K, (V A)^[n] q - qStar ≠ 0 := by
    intro q hqK
    have hq := (hK hqK).1
    have hqne : q ≠ qStar := by
      simpa only [Set.mem_singleton_iff] using (hK hqK).2
    exact sub_ne_zero.mpr
      (V_iterate_ne_fixed hA0 hqStar hfix hq hqne n)
  simpa only [koenigsOrbitFactor, Pi.div_apply] using
    (hnumCont.continuousOn.div hdenCont.continuousOn hdenne).div_const
      (deriv (V A) qStar)

/-- Around every nonstationary initial state, the full finite Koenigs
coefficients converge uniformly to `koenigsCoefficient`.  This transfers the
uniform convergence of the shifted tail product by multiplying with the
continuous, hence bounded, finite prefix on a compact relative neighborhood.
-/
theorem exists_tendstoUniformlyOn_koenigsCoefficient
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar) :
    ∃ r : ℝ, 0 < r ∧
      q₀ ∈ Set.Icc (q₀ - r) (min (q₀ + r) 1) ∧
      Set.Icc (q₀ - r) (min (q₀ + r) 1) ⊆
        Set.Ioc (0 : ℝ) 1 \ {qStar} ∧
      ∃ s : ℕ,
        TendstoUniformlyOn
          (fun n q =>
            (q - qStar) *
              ∏ i ∈ Finset.range (n + s),
                koenigsOrbitFactor A qStar q i)
          (fun q => koenigsCoefficient A qStar q)
          atTop
          (Set.Icc (q₀ - r) (min (q₀ + r) 1)) := by
  obtain ⟨r₀, hr₀, s, _hq₀K₀, htail⟩ :=
    exists_hasProdUniformlyOn_koenigsOrbitFactor_tail
      hA hqStar hfix hq₀ hq₀ne
  let r := min r₀ (min (q₀ / 2) (|q₀ - qStar| / 2))
  let K : Set ℝ := Set.Icc (q₀ - r) (min (q₀ + r) 1)
  let K₀ : Set ℝ := Set.Icc (q₀ - r₀) (min (q₀ + r₀) 1)
  have hq₀dist : 0 < |q₀ - qStar| :=
    abs_pos.mpr (sub_ne_zero.mpr hq₀ne)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min hr₀
      (lt_min (by linarith [hq₀.1]) (by linarith))
  have hrr₀ : r ≤ r₀ := by
    dsimp only [r]
    exact min_le_left _ _
  have hrq₀ : r ≤ q₀ / 2 := by
    dsimp only [r]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrdist : r ≤ |q₀ - qStar| / 2 := by
    dsimp only [r]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hq₀K : q₀ ∈ K := by
    dsimp only [K]
    exact ⟨by linarith, le_min (by linarith) hq₀.2⟩
  have hKK₀ : K ⊆ K₀ := by
    intro q hqK
    dsimp only [K, K₀] at hqK ⊢
    constructor
    · linarith [hqK.1]
    · exact le_min
        (hqK.2.trans (min_le_left _ _) |>.trans <| by linarith)
        (hqK.2.trans (min_le_right _ _))
  have hKD : K ⊆ Set.Ioc (0 : ℝ) 1 \ {qStar} := by
    intro q hqK
    dsimp only [K] at hqK
    constructor
    · constructor
      · have hlow : q₀ / 2 ≤ q₀ - r := by linarith
        exact (by linarith [hq₀.1] : 0 < q₀ / 2).trans_le
          (hlow.trans hqK.1)
      · exact hqK.2.trans (min_le_right _ _)
    · simp only [mem_singleton_iff]
      intro hqeq
      have hclose : |q₀ - qStar| ≤ r := by
        rw [← hqeq, abs_sub_comm]
        rw [abs_le]
        constructor
        · linarith [hqK.1]
        · linarith [hqK.2, min_le_left (q₀ + r) 1]
      linarith
  have htailK :
      HasProdUniformlyOn
        (fun n q => koenigsOrbitFactor A qStar q (n + s))
        (fun q => ∏' n : ℕ,
          koenigsOrbitFactor A qStar q (n + s)) K :=
    htail.mono hKK₀
  let P : ℝ → ℝ := fun q =>
    (q - qStar) *
      ∏ i ∈ Finset.range s, koenigsOrbitFactor A qStar q i
  let T : ℝ → ℝ := fun q =>
    ∏' n : ℕ, koenigsOrbitFactor A qStar q (n + s)
  have hPcont : ContinuousOn P K := by
    apply (continuousOn_id.sub continuousOn_const).mul
    apply continuousOn_finsetProd
    intro i _hi
    exact continuousOn_koenigsOrbitFactor hA hqStar hfix hKD i
  obtain ⟨B, hB⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hPcont
  have hB0 : 0 ≤ B :=
    (norm_nonneg (P q₀)).trans (hB q₀ hq₀K)
  let M := B + 1
  have hM : 0 < M := by dsimp only [M]; linarith
  have hPM : ∀ q ∈ K, |P q| ≤ M := by
    intro q hqK
    rw [← Real.norm_eq_abs]
    exact (hB q hqK).trans (by dsimp only [M]; linarith)
  have hcoeffEq : ∀ q ∈ K,
      koenigsCoefficient A qStar q = P q * T q := by
    intro q hqK
    have hsplit :=
      (htailK.hasProd hqK).multipliable.prod_mul_tprod_nat_mul'
    dsimp only [P, T, koenigsCoefficient, koenigsOrbitProduct]
    rw [← hsplit]
    ring
  have hPT :
      TendstoUniformlyOn
        (fun n q =>
          P q *
            ∏ i ∈ Finset.range n,
              koenigsOrbitFactor A qStar q (i + s))
        (fun q => koenigsCoefficient A qStar q) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hεM : 0 < ε / M := div_pos hε hM
    have htailMetric :=
      Metric.tendstoUniformlyOn_iff.mp
        htailK.tendstoUniformlyOn_finsetRange (ε / M) hεM
    filter_upwards [htailMetric] with n hn
    intro q hqK
    have hn' :
        |T q -
            ∏ i ∈ Finset.range n,
              koenigsOrbitFactor A qStar q (i + s)| < ε / M := by
      simpa only [T, Real.dist_eq] using hn q hqK
    rw [hcoeffEq q hqK, Real.dist_eq, ← mul_sub, abs_mul]
    calc
      |P q| *
            |T q -
              ∏ i ∈ Finset.range n,
                koenigsOrbitFactor A qStar q (i + s)|
          ≤ M *
            |T q -
              ∏ i ∈ Finset.range n,
                koenigsOrbitFactor A qStar q (i + s)| := by
            gcongr
            exact hPM q hqK
      _ < M * (ε / M) :=
        mul_lt_mul_of_pos_left hn' hM
      _ = ε := by field_simp
  refine ⟨r, hr, hq₀K, hKD, s, ?_⟩
  apply hPT.congr
  filter_upwards with n
  intro q _hqK
  dsimp only [P]
  rw [Nat.add_comm n s, Finset.prod_range_add]
  simp only [Nat.add_comm, mul_assoc]

/-- The Koenigs coefficient is continuous on the supercritical state space
away from the stationary initial state.  At `q = 1` this is relative
continuity on `(0, 1]`, as required by the paper. -/
theorem continuousOn_koenigsCoefficient
    {A qStar : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) :
    ContinuousOn
      (koenigsCoefficient A qStar)
      (Set.Ioc (0 : ℝ) 1 \ {qStar}) := by
  intro q₀ hq₀
  have hq₀ne : q₀ ≠ qStar := by
    simpa only [Set.mem_singleton_iff] using hq₀.2
  obtain ⟨r, hr, hq₀K, hKD, s, huniform⟩ :=
    exists_tendstoUniformlyOn_koenigsCoefficient
      hA hqStar hfix hq₀.1 hq₀ne
  let K : Set ℝ := Set.Icc (q₀ - r) (min (q₀ + r) 1)
  have happCont : ∀ n : ℕ,
      ContinuousOn
        (fun q =>
          (q - qStar) *
            ∏ i ∈ Finset.range (n + s),
              koenigsOrbitFactor A qStar q i) K := by
    intro n
    apply (continuousOn_id.sub continuousOn_const).mul
    apply continuousOn_finsetProd
    intro i _hi
    exact continuousOn_koenigsOrbitFactor hA hqStar hfix hKD i
  have hcoeffCont :
      ContinuousOn (koenigsCoefficient A qStar) K :=
    huniform.continuousOn
      (Frequently.of_forall happCont)
  apply (hcoeffCont q₀ hq₀K).mono_of_mem_nhdsWithin
  filter_upwards
    [mem_nhdsWithin_of_mem_nhds <|
      Ioo_mem_nhds (by linarith : q₀ - r < q₀)
        (by linarith : q₀ < q₀ + r),
      self_mem_nhdsWithin] with q hq hqD
  dsimp only [K]
  exact ⟨hq.1.le, le_min hq.2.le hqD.1.2⟩

/-! ### Locally uniform Koenigs asymptotic -/

/-- On a relative neighborhood of every nonstationary initial state, the
normalized deterministic orbit converges uniformly to the Koenigs
coefficient, after the common entrance time supplied by the local contraction
argument.  This is the paper's finite-product telescoping identity transferred
through the locally uniform product limit. -/
theorem exists_tendstoUniformlyOn_shifted_normalized_V_orbit_sub_fixed
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar) :
    ∃ r : ℝ, 0 < r ∧
      q₀ ∈ Set.Icc (q₀ - r) (min (q₀ + r) 1) ∧
      Set.Icc (q₀ - r) (min (q₀ + r) 1) ⊆
        Set.Ioc (0 : ℝ) 1 \ {qStar} ∧
      ∃ s : ℕ,
        TendstoUniformlyOn
          (fun n q =>
            ((V A)^[n + s] q - qStar) *
              (deriv (V A) qStar)⁻¹ ^ (n + s))
          (fun q => koenigsCoefficient A qStar q)
          atTop
          (Set.Icc (q₀ - r) (min (q₀ + r) 1)) := by
  obtain ⟨r, hr, hq₀K, hKD, s, huniform⟩ :=
    exists_tendstoUniformlyOn_koenigsCoefficient
      hA hqStar hfix hq₀ hq₀ne
  refine ⟨r, hr, hq₀K, hKD, s, ?_⟩
  apply huniform.congr
  filter_upwards with n
  intro q hqK
  have hq := (hKD hqK).1
  have hqne : q ≠ qStar := by
    simpa only [Set.mem_singleton_iff] using (hKD hqK).2
  exact mul_prod_range_koenigsOrbitFactor_eq_normalized
    hA hqStar hfix hq hqne (n + s)

/-- The normalized deterministic orbit converges locally uniformly to the
Koenigs coefficient without retaining the auxiliary entrance-time shift.
The shifted sequence is cofinal in `ℕ`, so deleting its finite prefix does not
change the uniform limit. -/
theorem exists_tendstoUniformlyOn_normalized_V_orbit_sub_fixed
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar) :
    ∃ r : ℝ, 0 < r ∧
      q₀ ∈ Set.Icc (q₀ - r) (min (q₀ + r) 1) ∧
      Set.Icc (q₀ - r) (min (q₀ + r) 1) ⊆
        Set.Ioc (0 : ℝ) 1 \ {qStar} ∧
      TendstoUniformlyOn
        (fun n q =>
          ((V A)^[n] q - qStar) *
            (deriv (V A) qStar)⁻¹ ^ n)
        (fun q => koenigsCoefficient A qStar q)
        atTop
        (Set.Icc (q₀ - r) (min (q₀ + r) 1)) := by
  obtain ⟨r, hr, hq₀K, hKD, s, hshift⟩ :=
    exists_tendstoUniformlyOn_shifted_normalized_V_orbit_sub_fixed
      hA hqStar hfix hq₀ hq₀ne
  let K : Set ℝ := Set.Icc (q₀ - r) (min (q₀ + r) 1)
  have hfull :
      TendstoUniformlyOn
        (fun n q =>
          ((V A)^[n] q - qStar) *
            (deriv (V A) qStar)⁻¹ ^ n)
        (fun q => koenigsCoefficient A qStar q) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff] at hshift ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hshift ε hε)
    apply eventually_atTop.2
    refine ⟨N + s, ?_⟩
    intro n hn q hqK
    have hsle : s ≤ n := by omega
    simpa only [Nat.sub_add_cancel hsle] using
      hN (n - s) (by omega) q hqK
  exact ⟨r, hr, hq₀K, hKD, hfull⟩

/-- Locally uniformly near every nonstationary initial state, the error in
the Koenigs asymptotic is little relative to the multiplier power.  This is
the paper's
`(V_A^n(q) - qStar - C(q) μ^n) / μ^n → 0`,
with convergence uniform on one relative neighborhood of `q₀`. -/
theorem exists_tendstoUniformlyOn_koenigs_remainder_ratio
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar) :
    ∃ r : ℝ, 0 < r ∧
      q₀ ∈ Set.Icc (q₀ - r) (min (q₀ + r) 1) ∧
      Set.Icc (q₀ - r) (min (q₀ + r) 1) ⊆
        Set.Ioc (0 : ℝ) 1 \ {qStar} ∧
      TendstoUniformlyOn
        (fun n q =>
          (((V A)^[n] q - qStar) -
              koenigsCoefficient A qStar q *
                deriv (V A) qStar ^ n) /
            deriv (V A) qStar ^ n)
        (fun _q => 0)
        atTop
        (Set.Icc (q₀ - r) (min (q₀ + r) 1)) := by
  obtain ⟨r, hr, hq₀K, hKD, huniform⟩ :=
    exists_tendstoUniformlyOn_normalized_V_orbit_sub_fixed
      hA hqStar hfix hq₀ hq₀ne
  have hA0 : A ≠ 0 := by linarith
  have hμne : deriv (V A) qStar ≠ 0 :=
    (V_multiplier_mem_Ioo hA0 hqStar hfix).1.ne'
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  refine ⟨r, hr, hq₀K, hKD, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [huniform ε hε] with n hn
  intro q hqK
  have hdist := hn q hqK
  rw [Real.dist_eq] at hdist ⊢
  rw [zero_sub, abs_neg]
  have heq :
      (((V A)^[n] q - qStar) -
            koenigsCoefficient A qStar q *
              deriv (V A) qStar ^ n) /
          deriv (V A) qStar ^ n =
        ((V A)^[n] q - qStar) *
            (deriv (V A) qStar)⁻¹ ^ n -
          koenigsCoefficient A qStar q := by
    rw [inv_pow]
    field_simp [pow_ne_zero n hμne]
  rw [heq, abs_sub_comm]
  exact hdist

/-- Paper-facing capstone for the Koenigs clause: near every nonstationary
initial state there is a continuous, locally nonzero coefficient for which
the normalized asymptotic remainder tends uniformly to zero. -/
theorem exists_continuous_local_uniform_koenigs_asymptotic
    {A qStar q₀ : ℝ}
    (hA : 1 < A) (hqStar : qStar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : V A qStar = qStar) (hq₀ : q₀ ∈ Set.Ioc (0 : ℝ) 1)
    (hq₀ne : q₀ ≠ qStar) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ → ℝ,
      q₀ ∈ Set.Icc (q₀ - r) (min (q₀ + r) 1) ∧
      Set.Icc (q₀ - r) (min (q₀ + r) 1) ⊆
        Set.Ioc (0 : ℝ) 1 \ {qStar} ∧
      ContinuousOn C (Set.Icc (q₀ - r) (min (q₀ + r) 1)) ∧
      (∀ q ∈ Set.Icc (q₀ - r) (min (q₀ + r) 1), C q ≠ 0) ∧
      TendstoUniformlyOn
        (fun n q =>
          (((V A)^[n] q - qStar) -
              C q * deriv (V A) qStar ^ n) /
            deriv (V A) qStar ^ n)
        (fun _q => 0)
        atTop
        (Set.Icc (q₀ - r) (min (q₀ + r) 1)) := by
  obtain ⟨r, hr, hq₀K, hKD, huniform⟩ :=
    exists_tendstoUniformlyOn_koenigs_remainder_ratio
      hA hqStar hfix hq₀ hq₀ne
  refine ⟨r, hr, koenigsCoefficient A qStar, hq₀K, hKD, ?_, ?_, huniform⟩
  · exact (continuousOn_koenigsCoefficient hA hqStar hfix).mono hKD
  · intro q hqK
    have hq := (hKD hqK).1
    have hqne : q ≠ qStar := by
      simpa only [Set.mem_singleton_iff] using (hKD hqK).2
    exact koenigsCoefficient_ne_zero hA hqStar hfix hq hqne

end AbsorptionCutoff
