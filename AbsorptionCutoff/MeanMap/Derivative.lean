import AbsorptionCutoff.MeanMap.Basic

open Set MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-! ### Derivative of `V_A` and the multiplier `μ_A = V_A'(q_*)`

Second half of the paper's `lem:gaussian-mean-field-concavity`: at the positive fixed
point, `0 < V_A'(q_*) < V_A(q_*)/q_* = 1`. We differentiate `V_A` under the integral
sign — the pointwise `q`-derivative `f_{Ag}'(q) = (Ag)²·(tanh x/x)·sech²x` (`x=A√q·g`,
`hasDerivAt_f`) is dominated by `g ↦ (Ag)²`, integrable since the standard Gaussian has
a finite second moment (`memLp_id_gaussianReal`). This gives `V_A'(q) = ∫ f_{Ag}'(q)`,
which is `> 0` (positive integrand off the null set `{g=0}`); strict concavity supplies
the strict upper bound `< 1`. -/

/-- `0 ≤ tanh x / x` (they share a sign; `= 0` only at `x = 0`). -/
lemma tanh_div_self_nonneg (x : ℝ) : 0 ≤ Real.tanh x / x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · exact le_of_lt (div_pos_of_neg_of_neg (by rw [← Real.tanh_zero]; exact tanh_strictMono hx) hx)
  · simp [hx]
  · exact le_of_lt (div_pos (by rw [← Real.tanh_zero]; exact tanh_strictMono hx) hx)

/-- `0 < tanh x / x` for `x ≠ 0`. -/
lemma tanh_div_self_pos {x : ℝ} (hx : x ≠ 0) : 0 < Real.tanh x / x := by
  rcases lt_or_gt_of_ne hx with h | h
  · exact div_pos_of_neg_of_neg (by rw [← Real.tanh_zero]; exact tanh_strictMono h) h
  · exact div_pos (by rw [← Real.tanh_zero]; exact tanh_strictMono h) h

/-- `tanh x / x ≤ 1` (since `|tanh x| ≤ |x|`). -/
lemma tanh_div_self_le_one (x : ℝ) : Real.tanh x / x ≤ 1 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [div_le_iff_of_neg hx, one_mul]
    have h := tanh_le_self (x := -x) (by linarith)
    rw [Real.tanh_neg] at h; linarith
  · simp [hx]
  · rw [div_le_one hx]; exact tanh_le_self hx.le

/-- The pointwise `q`-derivative of the `V_A` integrand `g ↦ tanh²(A√q·g)` (via
`hasDerivAt_f` with `a = A·g`): `f_{Ag}'(q) = (Ag)²·(tanh x/x)·(1−tanh²x)`, `x = A√q·g`.
The middle factor has a removable singularity at `g = 0` (a `μ`-null point). -/
noncomputable def dV (A q g : ℝ) : ℝ :=
  (A * g) ^ 2 * (Real.tanh (A * Real.sqrt q * g) / (A * Real.sqrt q * g))
    * (1 - Real.tanh (A * Real.sqrt q * g) ^ 2)

/-- `dV ≥ 0`: a product of three nonnegative factors. -/
lemma dV_nonneg (A q g : ℝ) : 0 ≤ dV A q g := by
  refine mul_nonneg (mul_nonneg (by positivity) (tanh_div_self_nonneg _)) ?_
  linarith [Real.tanh_sq_lt_one (A * Real.sqrt q * g)]

/-- `dV ≤ (Ag)²`: the middle and right factors both lie in `[0,1]`. -/
lemma dV_le (A q g : ℝ) : dV A q g ≤ (A * g) ^ 2 := by
  have hbr : (Real.tanh (A * Real.sqrt q * g) / (A * Real.sqrt q * g))
      * (1 - Real.tanh (A * Real.sqrt q * g) ^ 2) ≤ 1 :=
    mul_le_one₀ (tanh_div_self_le_one _)
      (by linarith [Real.tanh_sq_lt_one (A * Real.sqrt q * g)])
      (by linarith [sq_nonneg (Real.tanh (A * Real.sqrt q * g))])
  calc dV A q g
      = (A * g) ^ 2 * ((Real.tanh (A * Real.sqrt q * g) / (A * Real.sqrt q * g))
          * (1 - Real.tanh (A * Real.sqrt q * g) ^ 2)) := by rw [dV]; ring
    _ ≤ (A * g) ^ 2 * 1 := mul_le_mul_of_nonneg_left hbr (by positivity)
    _ = (A * g) ^ 2 := mul_one _

/-- `dV > 0` when `A ≠ 0`, `q > 0`, `g ≠ 0`: all three factors are strictly positive. -/
lemma dV_pos {A q g : ℝ} (hA : A ≠ 0) (hq : 0 < q) (hg : g ≠ 0) : 0 < dV A q g := by
  have hx : A * Real.sqrt q * g ≠ 0 :=
    mul_ne_zero (mul_ne_zero hA (Real.sqrt_pos.mpr hq).ne') hg
  have hAg : A * g ≠ 0 := mul_ne_zero hA hg
  refine mul_pos (mul_pos (by positivity) (tanh_div_self_pos hx)) ?_
  linarith [Real.tanh_sq_lt_one (A * Real.sqrt q * g)]

/-- Pointwise `HasDerivAt` for the `V_A` integrand: repackage `hasDerivAt_f` (proved at
`a = A·g`) into the `A√q·g` argument order used by `V`. -/
lemma hasDerivAt_Vintegrand {A g q : ℝ} (hA : A ≠ 0) (hg : g ≠ 0) (hq : 0 < q) :
    HasDerivAt (fun q => Real.tanh (A * Real.sqrt q * g) ^ 2) (dV A q g) q := by
  have h := hasDerivAt_f (a := A * g) (mul_ne_zero hA hg) hq
  have e : ∀ s : ℝ, A * g * Real.sqrt s = A * Real.sqrt s * g := fun s => mul_right_comm A g _
  simp only [e] at h
  exact h

/-- `g ↦ dV A q g` is measurable. -/
lemma measurable_dV (A q : ℝ) : Measurable (fun g => dV A q g) := by
  have h1 : Measurable (fun g : ℝ => A * Real.sqrt q * g) := measurable_id.const_mul _
  have htanh : Measurable (fun g : ℝ => Real.tanh (A * Real.sqrt q * g)) :=
    continuous_tanh.measurable.comp h1
  unfold dV
  exact (((measurable_id.const_mul A).pow_const 2).mul (htanh.div h1)).mul
    (measurable_const.sub (htanh.pow_const 2))

/-- **`V_A` is differentiable at each interior point**, obtained by differentiating under
the integral sign (`eq:gaussian-mean-field` differentiated in `q`): `V_A'(q) = ∫ f_{Ag}'(q)`.
The derivative integrand `dV A q` is dominated by `g ↦ (Ag)²`, integrable by the finite
Gaussian second moment (`integrable_sq_gaussian`); apply
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the neighbourhood `s = (0,∞)`. -/
lemma hasDerivAt_V {A : ℝ} (hA : A ≠ 0) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (V A) (∫ g, dV A q g ∂(gaussianReal 0 1)) q := by
  have hbound_int : Integrable (fun g : ℝ => A ^ 2 * g ^ 2) (gaussianReal 0 1) :=
    integrable_sq_gaussian.const_mul (A ^ 2)
  have hFmeas : ∀ᶠ x in nhds q, AEStronglyMeasurable
      (fun g => Real.tanh (A * Real.sqrt x * g) ^ 2) (gaussianReal 0 1) := by
    filter_upwards with x
    exact ((continuous_tanh.comp (by fun_prop)).pow 2).aestronglyMeasurable
  have hFint : Integrable (fun g => Real.tanh (A * Real.sqrt q * g) ^ 2) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((continuous_tanh.comp (by fun_prop)).pow 2).aestronglyMeasurable ?_
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (Real.tanh_sq_lt_one _).le
  have hne : ∀ᵐ g ∂(gaussianReal 0 1), g ≠ 0 := by
    rw [ae_iff]; simpa using gaussianReal_singleton_zero
  have hbound : ∀ᵐ g ∂(gaussianReal 0 1), ∀ x ∈ Set.Ioi (0 : ℝ),
      ‖dV A x g‖ ≤ A ^ 2 * g ^ 2 := by
    filter_upwards with g
    intro x _
    rw [Real.norm_eq_abs, abs_of_nonneg (dV_nonneg A x g)]
    calc dV A x g ≤ (A * g) ^ 2 := dV_le A x g
      _ = A ^ 2 * g ^ 2 := by ring
  have hdiff : ∀ᵐ g ∂(gaussianReal 0 1), ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun x => Real.tanh (A * Real.sqrt x * g) ^ 2) (dV A x g) x := by
    filter_upwards [hne] with g hg
    intro x hx
    exact hasDerivAt_Vintegrand hA hg hx
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun g => A ^ 2 * g ^ 2)
    (F := fun q g => Real.tanh (A * Real.sqrt q * g) ^ 2) (F' := fun q g => dV A q g)
    (Ioi_mem_nhds hq) hFmeas hFint (measurable_dV A q).aestronglyMeasurable hbound hbound_int
    hdiff).2

/-- The derivative integrand `dV A q` is integrable (dominated by `g ↦ A²g²`). -/
lemma integrable_dV {A : ℝ} (q : ℝ) : Integrable (fun g => dV A q g) (gaussianReal 0 1) := by
  refine Integrable.mono' (integrable_sq_gaussian.const_mul (A ^ 2))
    (measurable_dV A q).aestronglyMeasurable ?_
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_nonneg (dV_nonneg A q g)]
  calc dV A q g ≤ (A * g) ^ 2 := dV_le A q g
    _ = A ^ 2 * g ^ 2 := by ring

/-- **`V_A'(q) > 0`** for `A ≠ 0` and `q > 0` (paper `eq:gaussian-fixed-point`, lower bound):
`V_A'(q) = ∫ dV A q`, whose integrand is `≥ 0` everywhere and `> 0` off the null set `{g=0}`. -/
lemma V_deriv_pos {A : ℝ} (hA : A ≠ 0) {q : ℝ} (hq : 0 < q) : 0 < deriv (V A) q := by
  rw [(hasDerivAt_V hA hq).deriv]
  have hsupp : 0 < (gaussianReal 0 1) (Function.support (fun g => dV A q g)) := by
    have hsub : {(0 : ℝ)}ᶜ ⊆ Function.support (fun g => dV A q g) := by
      intro g hg
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hg
      exact ne_of_gt (dV_pos hA hq hg)
    have h0 : 0 < (gaussianReal 0 1) ({(0 : ℝ)}ᶜ) := by
      rw [prob_compl_eq_one_sub (measurableSet_singleton 0), gaussianReal_singleton_zero]; simp
    exact lt_of_lt_of_le h0 (measure_mono hsub)
  exact (integral_pos_iff_support_of_nonneg (fun g => dV_nonneg A q g) (integrable_dV q)).mpr hsupp

/-- **`V_A'(q_*) < 1`** at a positive fixed point (`A ≠ 0`, `q_* ∈ (0,1)`, `V_A q_* = q_*`):
strict concavity of `V_A` puts its graph strictly below the tangent line at `q_*`, so the
chord slope `V_A(q_*)/q_* = 1` from the origin strictly exceeds `V_A'(q_*)`. -/
lemma V_deriv_lt_one {A : ℝ} (hA : A ≠ 0) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hfix : V A q = q) : deriv (V A) q < 1 := by
  have hd : HasDerivAt (V A) (∫ g, dV A q g ∂(gaussianReal 0 1)) q := hasDerivAt_V hA hq.1
  have hconv : StrictConvexOn ℝ (Icc (0 : ℝ) 1) (-(V A)) := (V_strictConcaveOn hA).neg
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hqmem : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.le⟩
  have hslope := hconv.slope_lt_of_hasDerivAt h0mem hqmem hq.1 hd.neg
  rw [slope_def_field] at hslope
  simp only [Pi.neg_apply, V_zero, neg_zero, sub_zero, hfix] at hslope
  rw [neg_div, div_self hq.1.ne'] at hslope
  rw [hd.deriv]
  linarith [hslope]

/-- **The multiplier `μ_A = V_A'(q_*) ∈ (0,1)`** (paper `eq:gaussian-fixed-point`): at any
positive fixed point `q_* ∈ (0,1)` of `V_A` (`A ≠ 0`), the derivative — the geometric rate
governing the linearized orbit — lies strictly between `0` and `1`. This is the linearization
half of `lem:gaussian-mean-field-concavity`. -/
theorem V_multiplier_mem_Ioo {A : ℝ} (hA : A ≠ 0) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (hfix : V A q = q) : deriv (V A) q ∈ Ioo (0 : ℝ) 1 :=
  ⟨V_deriv_pos hA hq.1, V_deriv_lt_one hA hq hfix⟩

end AbsorptionCutoff
