/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.LogPolar

/-!
# The nonlinear polar perturbation estimate

Unit **A-8a** of the Chapter 7 lane: the paper's
`lem:nd-gaussian-polar-perturbation`, the analytic heart of §7's nonlinear half.

The statement compares the true log-polar step with its linearization at the
level of *densities*. Writing `T_r u = r⁻¹ tanh(r u)` and `U = (A/√N)G`, the
claim is that for every `δ ∈ (0,2)` there are `C < ∞` and an envelope
`h : ℝ → [0,∞)` with `∑_k sup_{[k,k+1]} e^{β t} h(t) < ∞` such that the polar
error between `T_r U` and `U`, restricted to the ball of radius `e^{-t}`, is at
most `C r^δ h(t)`. The envelope that comes out of the proof is
`h(t) = min{1, e^{-Nt}}`, and `β_{A,N} < N` is exactly what makes it summable.

The paper's proof has four independent estimates, each formalized as its own
unit here:

1. the density of `T_r U` (`eq:nd-nonlinear-linearized-density`), a change of
   variables through `artanh`;
2. the Taylor bound `|log(p_r/p₀)| ≤ C r²(1+‖v‖⁴)` on `‖v‖ ≤ r^{-1/2}`;
3. the annulus `r^{-1/2} < ‖v‖ ≤ (2r)⁻¹` and the Gaussian tail beyond it;
4. integration to `eq:nd-density-error-ball` and the choice of `h`.

## Mathlib gap

`Real.artanh` exists (`Mathlib/Analysis/SpecialFunctions/Artanh.lean`) with its
bijection and monotonicity theory, but **its derivative is not in Mathlib**. The
first declaration below supplies it, from `artanh_eq_half_log`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AbsorptionCutoff

/-! ### The derivative of `artanh` -/

/-- **`artanh' x = (1 − x²)⁻¹`** on `(−1, 1)`. Not in Mathlib, which has
`Real.artanh` but no differentiation lemmas for it; proved here from
`Real.artanh_eq_half_log`, since `½ log((1+x)/(1−x))` differentiates by the
quotient and logarithm rules.

This is the Jacobian factor of the change of variables
`eq:nd-nonlinear-linearized-density`: the density of `r⁻¹ tanh(rU)` picks up
`∏ᵢ (1 − r²vᵢ²)⁻¹` precisely because of it. -/
theorem hasDerivAt_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 - x ^ 2)⁻¹ x := by
  obtain ⟨hx1, hx2⟩ := hx
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) < 1 - x := by linarith
  have h3 : (1 : ℝ) - x ^ 2 ≠ 0 := by nlinarith
  have hd : HasDerivAt (fun y : ℝ => Real.log ((1 + y) / (1 - y)) / 2) ((1 - x ^ 2)⁻¹) x := by
    have hnum : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add 1
    have hden : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have hdiv : HasDerivAt (fun y : ℝ => (1 + y) / (1 - y))
        ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2) x := hnum.div hden h2.ne'
    have hlog := (hdiv.log (by positivity)).div_const 2
    have hval : (1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2 / ((1 + x) / (1 - x)) / 2
        = (1 - x ^ 2)⁻¹ := by field_simp; ring
    rwa [hval] at hlog
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx1 hx2] with y hy
  rw [Real.artanh_eq_half_log (Set.Ioo_subset_Icc_self hy)]
  ring

/-- `artanh` is differentiable on `(−1, 1)`. -/
theorem differentiableAt_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ Real.artanh x :=
  (hasDerivAt_artanh hx).differentiableAt

@[simp] theorem deriv_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv Real.artanh x = (1 - x ^ 2)⁻¹ :=
  (hasDerivAt_artanh hx).deriv

/-! ### The scalar substitution `T_r` and its inverse

The paper's `T_r u = r⁻¹ tanh(r u)` (tex L5044–5046), a diffeomorphism of `ℝ`
onto `(−r⁻¹, r⁻¹)`. Everything in
`eq:nd-nonlinear-linearized-density` is a product over coordinates, so the whole
substitution is understood once this one-dimensional map is. -/

/-- `T_r u = r⁻¹ tanh(r u)`, the normalized nonlinear step. As `r ↓ 0` it tends
to the identity, and the perturbation estimate measures the rate. -/
noncomputable def tanhScale (r u : ℝ) : ℝ := r⁻¹ * Real.tanh (r * u)

/-- The inverse substitution `T_r⁻¹ v = r⁻¹ artanh(r v)`, defined on
`(−r⁻¹, r⁻¹)`. -/
noncomputable def tanhScaleInv (r v : ℝ) : ℝ := r⁻¹ * Real.artanh (r * v)

/-- `T_r` maps `ℝ` into the open box `(−r⁻¹, r⁻¹)` — the range restriction that
makes the transformed density carry the indicator `1_{|r vᵢ| < 1}`. -/
lemma tanhScale_mem_Ioo {r : ℝ} (hr : 0 < r) (u : ℝ) :
    tanhScale r u ∈ Set.Ioo (-r⁻¹) r⁻¹ := by
  have h := Real.abs_tanh_lt_one (r * u)
  rw [abs_lt] at h
  constructor <;> · rw [tanhScale]; nlinarith [inv_pos.2 hr, h.1, h.2]

lemma tanhScaleInv_tanhScale {r : ℝ} (hr : 0 < r) (u : ℝ) :
    tanhScaleInv r (tanhScale r u) = u := by
  rw [tanhScaleInv, tanhScale, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul,
    Real.artanh_tanh, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

lemma tanhScale_tanhScaleInv {r v : ℝ} (hr : 0 < r) (hv : r * v ∈ Set.Ioo (-1 : ℝ) 1) :
    tanhScale r (tanhScaleInv r v) = v := by
  rw [tanhScale, tanhScaleInv, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul,
    Real.tanh_artanh hv, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- **The Jacobian of the inverse substitution**:
`(T_r⁻¹)'(v) = (1 − r²v²)⁻¹`.

This single factor is the whole content of the product
`∏ᵢ (1 − r²vᵢ²)⁻¹` in `eq:nd-nonlinear-linearized-density`; the chain rule turns
`hasDerivAt_artanh`'s `(1 − x²)⁻¹` into it, the two factors of `r` cancelling
against `r⁻¹`. -/
lemma hasDerivAt_tanhScaleInv {r v : ℝ} (hr : 0 < r) (hv : r * v ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (tanhScaleInv r) ((1 - r ^ 2 * v ^ 2)⁻¹) v := by
  have hmul : HasDerivAt (fun w : ℝ => r * w) r v := by
    simpa using (hasDerivAt_id v).const_mul r
  have hcomp := ((hasDerivAt_artanh hv).comp v hmul).const_mul r⁻¹
  have hval : r⁻¹ * ((1 - (r * v) ^ 2)⁻¹ * r) = (1 - r ^ 2 * v ^ 2)⁻¹ := by
    have h1 : (1 : ℝ) - (r * v) ^ 2 = 1 - r ^ 2 * v ^ 2 := by ring
    rw [h1, mul_comm ((1 - r ^ 2 * v ^ 2)⁻¹) r, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  rwa [hval] at hcomp

/-- The Jacobian is positive throughout the box, so no absolute value survives. -/
lemma one_sub_sq_pos {r v : ℝ} (hv : r * v ∈ Set.Ioo (-1 : ℝ) 1) : (0 : ℝ) < 1 - r ^ 2 * v ^ 2 := by
  obtain ⟨h1, h2⟩ := hv
  nlinarith

lemma mul_mem_Ioo_of_mem_Ioo_inv {r v : ℝ} (hr : 0 < r) (hv : v ∈ Set.Ioo (-r⁻¹) r⁻¹) :
    r * v ∈ Set.Ioo (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := hv
  constructor
  · nlinarith [mul_lt_mul_of_pos_left h1 hr, mul_inv_cancel₀ hr.ne']
  · nlinarith [mul_lt_mul_of_pos_left h2 hr, mul_inv_cancel₀ hr.ne']

/-- `T_r⁻¹` maps the box `(−r⁻¹, r⁻¹)` *onto* `ℝ`. -/
lemma image_tanhScaleInv {r : ℝ} (hr : 0 < r) :
    tanhScaleInv r '' (Set.Ioo (-r⁻¹) r⁻¹) = Set.univ := by
  ext u
  simp only [Set.mem_image, Set.mem_univ, iff_true]
  exact ⟨tanhScale r u, tanhScale_mem_Ioo hr u, tanhScaleInv_tanhScale hr u⟩

lemma injOn_tanhScaleInv {r : ℝ} (hr : 0 < r) :
    Set.InjOn (tanhScaleInv r) (Set.Ioo (-r⁻¹) r⁻¹) := by
  intro a ha b hb hab
  rw [← tanhScale_tanhScaleInv hr (mul_mem_Ioo_of_mem_Ioo_inv hr ha), hab,
    tanhScale_tanhScaleInv hr (mul_mem_Ioo_of_mem_Ioo_inv hr hb)]

/-- **The scalar change of variables** behind
`eq:nd-nonlinear-linearized-density`: substituting `u = T_r⁻¹ v` turns an
integral over `ℝ` into one over the box `(−r⁻¹, r⁻¹)`, at the cost of the
Jacobian `(1 − r²v²)⁻¹`.

Applied with `G u = g(T_r u) · p₀(u)` this says exactly that the law of `T_r U`
has density `v ↦ p₀(T_r⁻¹ v)(1 − r²v²)⁻¹` supported in the box — the paper's
`p_r`. The `N`-dimensional statement is the product of `N` copies of this. -/
theorem lintegral_eq_setLIntegral_tanhScaleInv {r : ℝ} (hr : 0 < r) (G : ℝ → ℝ≥0∞) :
    ∫⁻ u : ℝ, G u
      = ∫⁻ v in Set.Ioo (-r⁻¹) r⁻¹,
          ENNReal.ofReal (1 - r ^ 2 * v ^ 2)⁻¹ * G (tanhScaleInv r v) := by
  have hd : ∀ v ∈ Set.Ioo (-r⁻¹) r⁻¹,
      HasDerivWithinAt (tanhScaleInv r) ((1 - r ^ 2 * v ^ 2)⁻¹) (Set.Ioo (-r⁻¹) r⁻¹) v :=
    fun v hv => (hasDerivAt_tanhScaleInv hr (mul_mem_Ioo_of_mem_Ioo_inv hr hv)).hasDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hd
    (injOn_tanhScaleInv hr) G
  rw [image_tanhScaleInv hr, Measure.restrict_univ] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  congr 2
  exact abs_of_nonneg
    (inv_nonneg.2 (one_sub_sq_pos (mul_mem_Ioo_of_mem_Ioo_inv hr hv)).le)

lemma measurable_tanhScale (r : ℝ) : Measurable (tanhScale r) := by
  unfold tanhScale
  exact (continuous_tanh.measurable.comp (measurable_const_mul r)).const_mul r⁻¹

/-- **The scalar transformed law**, `eq:nd-nonlinear-linearized-density` in one
dimension: pushing Lebesgue measure forward through `T_r` gives Lebesgue measure
on the box `(−r⁻¹, r⁻¹)` weighted by the Jacobian `(1 − r²v²)⁻¹`.

Stated as an identity of *measures* rather than of integrals, because that is the
form the `N`-dimensional lift needs — the product map
`v ↦ (T_r(vᵢ))ᵢ` pushes `Measure.pi` forward to the `Measure.pi` of the factors. -/
theorem map_tanhScale_volume {r : ℝ} (hr : 0 < r) :
    Measure.map (tanhScale r) volume
      = (volume.restrict (Set.Ioo (-r⁻¹) r⁻¹)).withDensity
          (fun v => ENNReal.ofReal (1 - r ^ 2 * v ^ 2)⁻¹) := by
  refine Measure.ext fun s hs => ?_
  have hpre : MeasurableSet (tanhScale r ⁻¹' s) := (measurable_tanhScale r) hs
  have key := lintegral_eq_setLIntegral_tanhScaleInv hr
      ((tanhScale r ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)))
  rw [lintegral_indicator hpre, setLIntegral_const, one_mul] at key
  -- on the box, membership in `T_r⁻¹' s` after `T_r⁻¹` is membership in `s`
  have hind : ∀ v ∈ Set.Ioo (-r⁻¹) r⁻¹,
      (tanhScale r ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) (tanhScaleInv r v)
        = s.indicator (fun _ => (1 : ℝ≥0∞)) v := by
    intro v hv
    have hiff : tanhScaleInv r v ∈ tanhScale r ⁻¹' s ↔ v ∈ s := by
      rw [Set.mem_preimage, tanhScale_tanhScaleInv hr (mul_mem_Ioo_of_mem_Ioo_inv hr hv)]
    by_cases hmem : v ∈ s
    · rw [Set.indicator_of_mem (hiff.2 hmem), Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem fun h => hmem (hiff.1 h), Set.indicator_of_notMem hmem]
  have hmul : ∀ x : ℝ,
      ENNReal.ofReal (1 - r ^ 2 * x ^ 2)⁻¹ * s.indicator (fun _ => (1 : ℝ≥0∞)) x
        = s.indicator (fun y => ENNReal.ofReal (1 - r ^ 2 * y ^ 2)⁻¹) x := by
    intro x
    by_cases h : x ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  rw [Measure.map_apply (measurable_tanhScale r) hs, key,
    setLIntegral_congr_fun measurableSet_Ioo (fun v hv => by rw [hind v hv]),
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  simp_rw [hmul]
  rw [lintegral_indicator hs, Measure.restrict_restrict hs]

/-! ### Products and densities

Two general facts needed to turn the coordinatewise transformed law into an
`N`-dimensional *density*. **Neither is in Mathlib** — there is no
`Measure.pi`/`withDensity` interaction at all (`loogle` finds none, and
`Mathlib/MeasureTheory/Constructions/Pi.lean` has no `lintegral` lemma), and the
only product-of-integrals result, `lintegral_prod_eq_prod_lintegral_of_indepFun`,
needs a probability measure and `iIndepFun`, which is not the setting here (the
base measure is Lebesgue). -/

/-- **Fubini for a coordinatewise product**, over `Measure.pi` of σ-finite
measures. Proved by induction on `n` through `measurePreserving_piFinSuccAbove`,
splitting off the `0`-th coordinate and applying `lintegral_prod`. -/
theorem lintegral_pi_prod : ∀ {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (g : Fin n → ℝ → ℝ≥0∞), (∀ i, Measurable (g i)) →
    ∫⁻ v : Fin n → ℝ, ∏ i, g i (v i) ∂Measure.pi μ = ∏ i, ∫⁻ x, g i x ∂(μ i) := by
  intro n
  induction n with
  | zero => intro μ _ g hg; simp
  | succ n ih =>
    intro μ _ g hg
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he
    set G : ℝ × (Fin n → ℝ) → ℝ≥0∞ :=
      fun p => g 0 p.1 * ∏ j : Fin n, g (Fin.succAbove 0 j) (p.2 j) with hG
    have hmp := measurePreserving_piFinSuccAbove (α := fun _ : Fin (n + 1) => ℝ) μ 0
    have hprod : Measurable fun w : Fin n → ℝ => ∏ j : Fin n, g (Fin.succAbove 0 j) (w j) :=
      Finset.measurable_prod _ fun j _ => (hg _).comp (measurable_pi_apply j)
    have hGmeas : Measurable G :=
      ((hg 0).comp measurable_fst).mul (hprod.comp measurable_snd)
    have hinner : ∀ x : ℝ, ∫⁻ w : Fin n → ℝ, G (x, w)
          ∂(Measure.pi fun j => μ (Fin.succAbove 0 j))
        = g 0 x * ∏ j : Fin n, ∫⁻ y, g (Fin.succAbove 0 j) y ∂(μ (Fin.succAbove 0 j)) := by
      intro x
      simp only [hG]
      rw [lintegral_const_mul (g 0 x) hprod,
        ih (fun j => μ (Fin.succAbove 0 j)) (fun j => g (Fin.succAbove 0 j)) (fun j => hg _)]
    calc ∫⁻ v : Fin (n + 1) → ℝ, ∏ i, g i (v i) ∂Measure.pi μ
        = ∫⁻ v : Fin (n + 1) → ℝ, G (e v) ∂Measure.pi μ := by
          refine lintegral_congr fun v => ?_
          simp [hG, he, Fin.prod_univ_succ, Fin.tail]
      _ = ∫⁻ p, G p ∂((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))) :=
          hmp.lintegral_comp hGmeas
      _ = ∫⁻ x, (∫⁻ w, G (x, w) ∂(Measure.pi fun j => μ (Fin.succAbove 0 j))) ∂(μ 0) :=
          MeasureTheory.lintegral_prod _ hGmeas.aemeasurable
      _ = ∫⁻ x, g 0 x * ∏ j : Fin n, ∫⁻ y, g (Fin.succAbove 0 j) y ∂(μ (Fin.succAbove 0 j))
            ∂(μ 0) := by simp only [hinner]
      _ = (∫⁻ x, g 0 x ∂(μ 0)) *
            ∏ j : Fin n, ∫⁻ y, g (Fin.succAbove 0 j) y ∂(μ (Fin.succAbove 0 j)) :=
          lintegral_mul_const _ (hg 0)
      _ = ∏ i, ∫⁻ x, g i x ∂(μ i) := by rw [Fin.prod_univ_succ]; simp

/-- **Pushing a density through a measurable embedding**:
`(μ.withDensity g).map f = (μ.map f).withDensity (g ∘ f⁻¹)`, for `f` a measurable
embedding with measurable left inverse `finv`.

Also **not in Mathlib** — the only nearby result is
`MeasurableEmbedding.map_withDensity_rnDeriv`, which is about Radon–Nikodym
derivatives of a pair of measures. Both sides evaluate on a measurable `s` to
`∫⁻ x in f⁻¹' s, g x ∂μ`, the right-hand one via `setLIntegral_map`. -/
theorem map_withDensity_of_measurableEmbedding {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {f : α → β} (hf : MeasurableEmbedding f) {finv : β → α}
    (hfinv : Measurable finv) (hleft : ∀ x, finv (f x) = x) (μ : Measure α)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    (μ.withDensity g).map f = (μ.map f).withDensity (fun y => g (finv y)) := by
  ext s hs
  rw [hf.map_apply, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs]
  refine Eq.trans ?_ (setLIntegral_map (μ := μ) hs (hg.comp hfinv) hf.measurable).symm
  exact lintegral_congr fun x => by simp only [Function.comp_apply, hleft]

/-- **A product of densities is the density of the product**:
`∏ᵢ (μᵢ.withDensity fᵢ) = (∏ᵢ μᵢ).withDensity (v ↦ ∏ᵢ fᵢ(vᵢ))`.

Both sides agree on measurable boxes — the right-hand side by
`Measure.restrict_pi_pi` and `lintegral_pi_prod` — so `Measure.pi_eq` identifies
them. The `SigmaFinite` hypothesis on the weighted factors is what `Measure.pi_eq`
needs; in the application each factor is a probability density, so it is free. -/
theorem pi_withDensity {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i))
      = (Measure.pi μ).withDensity (fun v => ∏ i, f i (v i)) := by
  refine Measure.pi_eq (μ := fun i => (μ i).withDensity (f i)) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_pi_prod _ f hf]
  exact Finset.prod_congr rfl fun i _ => (withDensity_apply (f i) (hs i)).symm

/-! ### The `N`-dimensional transformed law

`eq:nd-nonlinear-linearized-density` proper. The substitution acts coordinatewise,
so the `N`-dimensional law is the `Measure.pi` of `N` copies of the scalar one —
which is exactly why the paper argues "in one dimension the function …" and then
takes products. -/

lemma measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh; fun_prop

lemma measurable_tanhScaleInv (r : ℝ) : Measurable (tanhScaleInv r) :=
  (measurable_artanh.comp (measurable_const_mul r)).const_mul r⁻¹

/-- `T_r` has range exactly the box `(−r⁻¹, r⁻¹)`. -/
lemma range_tanhScale {r : ℝ} (hr : 0 < r) :
    Set.range (tanhScale r) = Set.Ioo (-r⁻¹) r⁻¹ := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩; exact tanhScale_mem_Ioo hr u
  · intro hv
    exact ⟨tanhScaleInv r v, tanhScale_tanhScaleInv hr (mul_mem_Ioo_of_mem_Ioo_inv hr hv)⟩

/-- `T_r` is a measurable embedding — it is injective with measurable inverse and
measurable (open) range. This is what makes `Measure.map (tanhScale r) volume`
σ-finite, hence eligible for `Measure.pi_map_pi`. -/
lemma measurableEmbedding_tanhScale {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (tanhScale r) :=
  MeasurableEmbedding.of_measurable_inverse (g := tanhScaleInv r)
    (measurable_tanhScale r) (by rw [range_tanhScale hr]; exact measurableSet_Ioo)
    (measurable_tanhScaleInv r) (fun u => tanhScaleInv_tanhScale hr u)

lemma sigmaFinite_map_tanhScale {r : ℝ} (hr : 0 < r) :
    SigmaFinite (Measure.map (tanhScale r) (volume : Measure ℝ)) :=
  (measurableEmbedding_tanhScale hr).sigmaFinite_map

/-- **`eq:nd-nonlinear-linearized-density`** (tex L5053–5058): the law of
`T_r U = r⁻¹ tanh(r U)` for `U` with independent coordinates is the product of
`N` copies of the scalar transformed law — Lebesgue measure on the box
`(−r⁻¹, r⁻¹)^N` weighted by `∏ᵢ (1 − r²vᵢ²)⁻¹`, which is the paper's `p_r`
divided by `p₀ ∘ T_r⁻¹`. -/
theorem map_tanhScaleVec_volume {N : ℕ} {r : ℝ} (hr : 0 < r) :
    Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i)) volume
      = Measure.pi fun _ : Fin N =>
          (volume.restrict (Set.Ioo (-r⁻¹) r⁻¹)).withDensity
            (fun v => ENNReal.ofReal (1 - r ^ 2 * v ^ 2)⁻¹) := by
  have hsf : ∀ _i : Fin N, SigmaFinite (Measure.map (tanhScale r) (volume : Measure ℝ)) :=
    fun _ => sigmaFinite_map_tanhScale hr
  rw [volume_pi,
    Measure.pi_map_pi (hμ := hsf) fun _ => (measurable_tanhScale r).aemeasurable]
  exact congrArg Measure.pi (funext fun _ => map_tanhScale_volume hr)

/-- **The scalar transformed density** (A-8a, step 6b): if `U₁` has density `p`
with respect to Lebesgue measure, then `T_r U₁` has density

`v ↦ (1 − r²v²)⁻¹ p(r⁻¹ artanh(r v))` on the box `(−r⁻¹, r⁻¹)`,

which is the one-dimensional case of `eq:nd-nonlinear-linearized-density` — the
paper's indicator `1_{|rv|<1}` being carried by the `restrict`. The `N`-dimensional
density is the product of `N` copies of this, by `pi_withDensity`.

Note the statement is for an *arbitrary* base density `p`, not just the Gaussian:
nothing in the change of variables uses Gaussianity, which enters only in the
Taylor bound, where `log p` must be quadratic. -/
theorem map_tanhScale_withDensity {r : ℝ} (hr : 0 < r) {p : ℝ → ℝ≥0∞} (hp : Measurable p) :
    Measure.map (tanhScale r) (volume.withDensity p)
      = (volume.restrict (Set.Ioo (-r⁻¹) r⁻¹)).withDensity
          (fun v => ENNReal.ofReal (1 - r ^ 2 * v ^ 2)⁻¹ * p (tanhScaleInv r v)) := by
  rw [map_withDensity_of_measurableEmbedding (measurableEmbedding_tanhScale hr)
      (measurable_tanhScaleInv r) (fun x => tanhScaleInv_tanhScale hr x) volume hp,
    map_tanhScale_volume hr]
  exact (withDensity_mul (f := fun v : ℝ => ENNReal.ofReal (1 - r ^ 2 * v ^ 2)⁻¹)
    (g := fun v : ℝ => p (tanhScaleInv r v)) _ (by fun_prop)
    (hp.comp (measurable_tanhScaleInv r))).symm

/-- The scalar transformed density of `map_tanhScale_withDensity`, packaged as a
function on all of `ℝ` — the box `(−r⁻¹, r⁻¹)` becomes the paper's indicator
`1_{|rv|<1}`. In this form the `N`-dimensional density is literally
`v ↦ ∏ᵢ tanhScaleDensity r p (vᵢ)`. -/
noncomputable def tanhScaleDensity (r : ℝ) (p : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  (Set.Ioo (-r⁻¹) r⁻¹).indicator
    (fun v => ENNReal.ofReal (1 - r ^ 2 * v ^ 2)⁻¹ * p (tanhScaleInv r v))

lemma measurable_tanhScaleDensity {r : ℝ} {p : ℝ → ℝ≥0∞} (hp : Measurable p) :
    Measurable (tanhScaleDensity r p) :=
  Measurable.indicator
    ((by fun_prop : Measurable fun v : ℝ => ENNReal.ofReal (1 - r ^ 2 * v ^ 2)⁻¹).mul
      (hp.comp (measurable_tanhScaleInv r))) measurableSet_Ioo

/-- `map_tanhScale_withDensity` with the restriction absorbed into the density. -/
theorem map_tanhScale_withDensity' {r : ℝ} (hr : 0 < r) {p : ℝ → ℝ≥0∞} (hp : Measurable p) :
    Measure.map (tanhScale r) (volume.withDensity p)
      = volume.withDensity (tanhScaleDensity r p) := by
  rw [map_tanhScale_withDensity hr hp, tanhScaleDensity,
    withDensity_indicator measurableSet_Ioo]

/-- **`p₀` in product form**: if the coordinates of `U` are i.i.d. with Lebesgue
density `p`, then `U` has density `v ↦ ∏ᵢ p(vᵢ)` on `ℝ^N`. -/
theorem pi_withDensity_volume {N : ℕ} {p : ℝ → ℝ≥0∞} (hp : Measurable p)
    [SigmaFinite ((volume : Measure ℝ).withDensity p)] :
    (Measure.pi fun _ : Fin N => (volume : Measure ℝ).withDensity p)
      = (volume : Measure (Fin N → ℝ)).withDensity (fun v => ∏ i, p (v i)) := by
  rw [volume_pi]
  exact pi_withDensity _ _ fun _ => hp

/-- **`eq:nd-nonlinear-linearized-density` in density form** (A-8a, step 6c):
if the coordinates of `U` are i.i.d. with density `p`, then `T_r U` has density

`p_r(v) = ∏ᵢ (1 − r²vᵢ²)⁻¹ p(r⁻¹ artanh(r vᵢ)) 1_{|r vᵢ|<1}`

with respect to Lebesgue measure on `ℝ^N` — the paper's `p_r` exactly. The
measure-level version `map_tanhScaleVec_volume` is upgraded here by
`map_tanhScale_withDensity'` on each factor and `pi_withDensity` on the product.
The probability hypothesis is only used for the σ-finiteness `Measure.pi` needs;
in the application `p` is the Gaussian density. -/
theorem map_tanhScaleVec_withDensity {N : ℕ} {r : ℝ} (hr : 0 < r) {p : ℝ → ℝ≥0∞}
    (hp : Measurable p) [IsProbabilityMeasure ((volume : Measure ℝ).withDensity p)] :
    Measure.map (fun v : Fin N → ℝ => fun i => tanhScale r (v i))
        (Measure.pi fun _ : Fin N => (volume : Measure ℝ).withDensity p)
      = (volume : Measure (Fin N → ℝ)).withDensity
          (fun v => ∏ i, tanhScaleDensity r p (v i)) := by
  haveI hprob : IsProbabilityMeasure
      (Measure.map (tanhScale r) ((volume : Measure ℝ).withDensity p)) :=
    Measure.isProbabilityMeasure_map (measurable_tanhScale r).aemeasurable
  haveI hprob' : IsProbabilityMeasure
      ((volume : Measure ℝ).withDensity (tanhScaleDensity r p)) := by
    rw [← map_tanhScale_withDensity' hr hp]; exact hprob
  have hsf : ∀ _i : Fin N,
      SigmaFinite (Measure.map (tanhScale r) ((volume : Measure ℝ).withDensity p)) :=
    fun _ => inferInstance
  rw [Measure.pi_map_pi (hμ := hsf) fun _ => (measurable_tanhScale r).aemeasurable]
  simp_rw [map_tanhScale_withDensity' hr hp]
  rw [volume_pi]
  exact pi_withDensity _ _ fun _ => measurable_tanhScaleDensity hp

/-! ### Scalar inputs for the Taylor bound

The paper's expansion of `log(p_r/p₀)` (tex L5093–5100) rests on two
one-dimensional inequalities, in the regime `|r vᵢ| ≤ 1/2` that the constraint
`‖v‖₂ ≤ r^{-1/2}` provides. Neither is in Mathlib. -/

/-- **`artanh x = x + O(|x|³)`** on `|x| ≤ 1/2`, with the explicit constant `4/3`.

The paper's `r⁻¹ arctanh(r vᵢ) = vᵢ + O(r²|vᵢ|³)` is this after dividing by `r`.
Mathlib has no Taylor expansion for `artanh`; the bound follows from
`hasDerivAt_artanh` by the mean value inequality on the segment `[0, x]`, where
`|artanh′ t − 1| = t²/(1 − t²) ≤ (4/3)x²`. Running the argument on that segment
rather than on all of `[−1/2, 1/2]` is what produces a *cubic* rather than a
linear bound. -/
theorem abs_artanh_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.artanh x - x| ≤ (4 / 3) * |x| ^ 3 := by
  rcases abs_le.1 hx with ⟨hx1, hx2⟩
  have hmem : ∀ t ∈ Set.uIcc (0 : ℝ) x, |t| ≤ |x| := by
    intro t ht
    rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      · rw [abs_le] at *; constructor <;> linarith [abs_nonneg x, le_abs_self x, neg_abs_le x]
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x,
      HasDerivWithinAt (fun s : ℝ => Real.artanh s - s) ((1 - t ^ 2)⁻¹ - 1)
        (Set.uIcc 0 x) t := by
    intro t ht
    rcases abs_le.1 ((hmem t ht).trans hx) with ⟨a, b⟩
    exact ((hasDerivAt_artanh ⟨by linarith, by linarith⟩).sub (hasDerivAt_id t)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc (0 : ℝ) x, ‖(1 - t ^ 2)⁻¹ - 1‖ ≤ (4 / 3) * |x| ^ 2 := by
    intro t ht
    have hb := hmem t ht
    rcases abs_le.1 (hb.trans hx) with ⟨a, b⟩
    have ht2 : t ^ 2 ≤ |x| ^ 2 := by nlinarith [sq_abs t, sq_abs x, abs_nonneg t, abs_nonneg x]
    have hden : (3 : ℝ) / 4 ≤ 1 - t ^ 2 := by nlinarith
    have hne : (1 : ℝ) - t ^ 2 ≠ 0 := ne_of_gt (by linarith)
    have hval : (1 - t ^ 2)⁻¹ - 1 = t ^ 2 / (1 - t ^ 2) := by
      rw [eq_div_iff hne]; field_simp; ring
    rw [hval, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg t, abs_nonneg x]
  have hkey := (convex_uIcc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.artanh_zero, sub_zero, Real.norm_eq_abs] at hkey
  calc |Real.artanh x - x| ≤ (4 / 3) * |x| ^ 2 * |x| := by simpa using hkey
    _ = (4 / 3) * |x| ^ 3 := by ring

/-- **`|log(1 − s)| ≤ 2s`** on `0 ≤ s ≤ 1/2`.

This is the paper's `−log(1 − r²vᵢ²) = O(r²vᵢ²)`, the contribution of the
Jacobian to `log(p_r/p₀)`. Proved from `Real.log_le_sub_one_of_pos` applied to
`(1 − s)⁻¹`, which gives `−log(1 − s) ≤ s/(1 − s) ≤ 2s`. -/
theorem abs_log_one_sub_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    |Real.log (1 - s)| ≤ 2 * s := by
  have hpos : (0 : ℝ) < 1 - s := by linarith
  have hnonpos : Real.log (1 - s) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  rw [abs_of_nonpos hnonpos, neg_le]
  have hlog : Real.log (1 - s)⁻¹ ≤ (1 - s)⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at hlog
  have hval : (1 - s)⁻¹ - 1 = s / (1 - s) := by
    rw [eq_div_iff (ne_of_gt hpos)]; field_simp; ring
  rw [hval] at hlog
  have hfrac : s / (1 - s) ≤ 2 * s := by
    rw [div_le_iff₀ hpos]; nlinarith
  linarith

/-! ### The coordinate estimates at `T_r⁻¹`

The two scalar inequalities above, transported to the substitution itself. Both
run in the regime `|r vᵢ| ≤ 1/2`, which the constraint `‖v‖₂ ≤ r^{-1/2}` supplies
once `r ≤ 1/4`. -/

/-- **`r⁻¹ artanh(r v) = v + O(r²|v|³)`** (tex L5088–5091), the paper's first
displayed expansion. This is `abs_artanh_sub_le` divided by `r`. -/
theorem abs_tanhScaleInv_sub_le {r v : ℝ} (hr : 0 < r) (hrv : |r * v| ≤ 1 / 2) :
    |tanhScaleInv r v - v| ≤ (4 / 3) * r ^ 2 * |v| ^ 3 := by
  have hkey := abs_artanh_sub_le hrv
  have hrewrite : tanhScaleInv r v - v = r⁻¹ * (Real.artanh (r * v) - r * v) := by
    unfold tanhScaleInv; field_simp
  rw [hrewrite, abs_mul, abs_of_pos (inv_pos.2 hr)]
  rw [abs_mul, abs_of_pos hr, mul_pow] at hkey
  calc r⁻¹ * |Real.artanh (r * v) - r * v| ≤ r⁻¹ * ((4 / 3) * (r ^ 3 * |v| ^ 3)) := by
        gcongr
    _ = (4 / 3) * r ^ 2 * |v| ^ 3 := by field_simp

/-- The *squared* coordinate error, `|(T_r⁻¹v)² − v²| ≤ (28/9) r² v⁴`.

This is the form the Gaussian exponent consumes: `log p₀` is quadratic, so the
contribution of the substitution to `log(p_r/p₀)` is a sum of these. Factoring
`w² − v² = (w − v)(w + v)` and using `|w − v| ≤ |v|/3` — which is where
`r²v² ≤ 1/4` enters — gives `|w + v| ≤ (7/3)|v|`, so only *fourth* powers appear
and the vector sum needs nothing beyond `∑ᵢ vᵢ⁴ ≤ (∑ᵢ vᵢ²)²`. -/
theorem abs_sq_tanhScaleInv_sub_sq_le {r v : ℝ} (hr : 0 < r) (hrv : |r * v| ≤ 1 / 2) :
    |tanhScaleInv r v ^ 2 - v ^ 2| ≤ (28 / 9) * r ^ 2 * v ^ 4 := by
  set w := tanhScaleInv r v with hw
  have hdiff : |w - v| ≤ (4 / 3) * r ^ 2 * |v| ^ 3 := abs_tanhScaleInv_sub_le hr hrv
  have hr2 : r ^ 2 * v ^ 2 ≤ 1 / 4 := by
    have := abs_mul r v ▸ hrv
    nlinarith [sq_abs (r * v), abs_nonneg (r * v)]
  have hsmall : |w - v| ≤ (1 / 3) * |v| := by
    have h3 : (4 / 3) * r ^ 2 * |v| ^ 3 = (4 / 3) * (r ^ 2 * v ^ 2) * |v| := by
      rw [← sq_abs v]; ring
    calc |w - v| ≤ (4 / 3) * (r ^ 2 * v ^ 2) * |v| := by rw [← h3]; exact hdiff
      _ ≤ (4 / 3) * (1 / 4) * |v| := by gcongr
      _ = (1 / 3) * |v| := by ring
  have hsum : |w + v| ≤ (7 / 3) * |v| := by
    have hrw : w + v = (w - v) + 2 * v := by ring
    calc |w + v| ≤ |w - v| + |2 * v| := by rw [hrw]; exact abs_add_le _ _
      _ ≤ (1 / 3) * |v| + 2 * |v| := by
          rw [abs_mul]; simp only [abs_two]; linarith
      _ = (7 / 3) * |v| := by ring
  have hfac : w ^ 2 - v ^ 2 = (w - v) * (w + v) := by ring
  rw [hfac, abs_mul]
  calc |w - v| * |w + v| ≤ ((4 / 3) * r ^ 2 * |v| ^ 3) * ((7 / 3) * |v|) := by gcongr
    _ = (28 / 9) * r ^ 2 * |v| ^ 4 := by ring
    _ = (28 / 9) * r ^ 2 * v ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity : (0:ℝ) ≤ v ^ 4)]

/-! ### The `N`-dimensional Taylor bound

Paper `|log(p_r(v)/p₀(v))| ≤ C r²(1 + ‖v‖₂⁴)` on `‖v‖₂ ≤ r^{-1/2}`
(tex L5093–5104). Stated density-free: `p₀` is the density of `U = (A/√N)G`, so
`log p₀(u) = const − c‖u‖₂²` with `c = N/(2A²)`, and by
`eq:nd-nonlinear-linearized-density`

`log(p_r(v)/p₀(v)) = −c ∑ᵢ ((T_r⁻¹v)ᵢ² − vᵢ²) − ∑ᵢ log(1 − r²vᵢ²)`,

which is (minus) the expression bounded below. Keeping the statement at this
level means it is a fact about `tanhScaleInv` alone, provable — and reusable —
without carrying the Gaussian density around.

**Regime deviation from the paper, recorded.** The paper runs this estimate for
`0 < r < 1`; we require `r ≤ 1/4`. The reason: `‖v‖₂ ≤ r^{-1/2}` and `r < 1`
only give `|r vᵢ| ≤ r^{1/2} ≤ 1`, whereas both scalar inputs above need
`|r vᵢ| ≤ 1/2`, i.e. `r ≤ 1/4`. Nothing is lost. The paper already handles
`r ≥ 1` separately (tex L5071–5080) by uniform boundedness of `p_r` on a
compact range of `r` bounded away from zero, and that argument applies verbatim
to `1/4 ≤ r ≤ √N`; the middle range is absorbed into the constant of
`eq:nd-density-error-ball`, whose `r^δ` factor is bounded below there. -/

/-- **The `N`-dimensional Taylor bound** (tex L5093–5104):
`|log(p_r(v)/p₀(v))| ≤ C r²(1 + ‖v‖₂⁴)` for `0 < r ≤ 1/4` and `‖v‖₂ ≤ r^{-1/2}`
(the hypothesis `hv`), with the explicit constant `C = (28/9)c + 2`.

The two halves are summed separately, as the paper does: the substitution
contributes `c ∑ᵢ |(T_r⁻¹v)ᵢ² − vᵢ²| ≤ (28/9) c r² ∑ᵢ vᵢ⁴ ≤ (28/9) c r² ‖v‖₂⁴`
via `Finset.sum_sq_le_sq_sum_of_nonneg`, and the Jacobian contributes
`∑ᵢ |log(1 − r²vᵢ²)| ≤ 2r² ‖v‖₂²`. The `1 +` absorbs the quadratic term. -/
theorem abs_logDensityRatio_le {N : ℕ} {r c : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    (hc : 0 ≤ c) (v : Fin N → ℝ) (hv : r * ∑ i, v i ^ 2 ≤ 1) :
    |c * ∑ i, (tanhScaleInv r (v i) ^ 2 - v i ^ 2) + ∑ i, Real.log (1 - r ^ 2 * v i ^ 2)|
      ≤ ((28 / 9) * c + 2) * r ^ 2 * (1 + (∑ i, v i ^ 2) ^ 2) := by
  set S := ∑ i, v i ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  -- `‖v‖₂ ≤ r^{-1/2}` puts every coordinate in the scalar lemmas' regime.
  have hcoord : ∀ i : Fin N, r ^ 2 * v i ^ 2 ≤ 1 / 4 := by
    intro i
    have hle : v i ^ 2 ≤ S := Finset.single_le_sum (f := fun i => v i ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [sq_nonneg (v i), sq_nonneg r]
  have hreg : ∀ i : Fin N, |r * v i| ≤ 1 / 2 := by
    intro i
    have h := hcoord i
    have hsq : |r * v i| ^ 2 ≤ 1 / 4 := by rw [sq_abs]; nlinarith
    nlinarith [abs_nonneg (r * v i)]
  have hquartic : ∑ i, v i ^ 4 ≤ S ^ 2 := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := (Finset.univ : Finset (Fin N)))
      (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _)
    calc ∑ i, v i ^ 4 = ∑ i, (v i ^ 2) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ S ^ 2 := hsq
  -- the substitution term
  have hsubst : |∑ i, (tanhScaleInv r (v i) ^ 2 - v i ^ 2)| ≤ (28 / 9) * r ^ 2 * S ^ 2 := by
    calc |∑ i, (tanhScaleInv r (v i) ^ 2 - v i ^ 2)|
        ≤ ∑ i, |tanhScaleInv r (v i) ^ 2 - v i ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (28 / 9) * r ^ 2 * v i ^ 4 :=
          Finset.sum_le_sum fun i _ => abs_sq_tanhScaleInv_sub_sq_le hr (hreg i)
      _ = (28 / 9) * r ^ 2 * ∑ i, v i ^ 4 := by rw [Finset.mul_sum]
      _ ≤ (28 / 9) * r ^ 2 * S ^ 2 := by gcongr
  -- the Jacobian term
  have hjac : |∑ i, Real.log (1 - r ^ 2 * v i ^ 2)| ≤ 2 * r ^ 2 * S := by
    calc |∑ i, Real.log (1 - r ^ 2 * v i ^ 2)| ≤ ∑ i, |Real.log (1 - r ^ 2 * v i ^ 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, 2 * (r ^ 2 * v i ^ 2) := Finset.sum_le_sum fun i _ =>
          abs_log_one_sub_le (by positivity) ((hcoord i).trans (by norm_num))
      _ = 2 * r ^ 2 * S := by
          rw [hS, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hfin : |c * ∑ i, (tanhScaleInv r (v i) ^ 2 - v i ^ 2) + ∑ i, Real.log (1 - r ^ 2 * v i ^ 2)|
      ≤ c * ((28 / 9) * r ^ 2 * S ^ 2) + 2 * r ^ 2 * S := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hc]
    exact add_le_add (by gcongr) hjac
  refine hfin.trans ?_
  nlinarith [sq_nonneg (S - 1), sq_nonneg r, sq_nonneg S, mul_nonneg hc (sq_nonneg r)]

/-! ### The density ratio at the Gaussian

`abs_logDensityRatio_le` bounds a bracket; this section identifies that bracket
as the actual log-ratio `log(p_r/p₀)` when the base density is Gaussian, which is
the only place Gaussianity of `U` is used in A-8a. With `p₀ = ∏ᵢ g(vᵢ)`,
`g = gaussianPDFReal 0 σ²` and `c = 1/(2σ²)`, the normalizing constants cancel
and the exponents subtract, leaving exactly

`p_r(v) = p₀(v) · exp( −[ c ∑ᵢ ((T_r⁻¹v)ᵢ² − vᵢ²) + ∑ᵢ log(1 − r²vᵢ²) ] )`. -/

/-- `|e^x − 1| ≤ |x| e^{|x|}`. Mathlib's `Real.abs_exp_sub_one_le` assumes
`|x| ≤ 1`; this is the unrestricted form, from the mean value inequality on the
segment `[0, x]`, where `|exp′| ≤ e^{|x|}`. -/
theorem abs_exp_sub_one_le (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) x, HasDerivWithinAt Real.exp (Real.exp t)
      (Set.uIcc 0 x) t := fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.uIcc (0 : ℝ) x, ‖Real.exp t‖ ≤ Real.exp |x| := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos t), Real.exp_le_exp]
    rcases Set.mem_uIcc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2.trans (le_abs_self x)
    · exact h2.trans (abs_nonneg x)
  have hkey := (convex_uIcc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  simp only [Real.exp_zero, Real.norm_eq_abs, sub_zero] at hkey
  calc |Real.exp x - 1| ≤ Real.exp |x| * |x| := by simpa [abs_sub_comm] using hkey
    _ = |x| * Real.exp |x| := by ring

/-- **The scalar density ratio** at the Gaussian: one coordinate's transformed
density is the original times `exp` of (minus) that coordinate's contribution to
the bracket of `abs_logDensityRatio_le`. -/
theorem gaussianPDFReal_tanhScaleInv {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0) {r v : ℝ}
    (hpos : (0 : ℝ) < 1 - r ^ 2 * v ^ 2) :
    (1 - r ^ 2 * v ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r v)
      = gaussianPDFReal 0 σ2 v *
        Real.exp (-((2 * (σ2 : ℝ))⁻¹ * ((tanhScaleInv r v) ^ 2 - v ^ 2)
          + Real.log (1 - r ^ 2 * v ^ 2))) := by
  set w := tanhScaleInv r v
  set c : ℝ := (2 * (σ2 : ℝ))⁻¹ with hc
  rw [gaussianPDFReal_def]
  simp only [sub_zero]
  rw [Real.exp_neg, Real.exp_add, Real.exp_log hpos]
  have hcw : -w ^ 2 / (2 * (σ2 : ℝ)) = -(c * w ^ 2) := by rw [hc]; field_simp
  have hcv : -v ^ 2 / (2 * (σ2 : ℝ)) = -(c * v ^ 2) := by rw [hc]; field_simp
  rw [hcw, hcv, show c * (w ^ 2 - v ^ 2) = c * w ^ 2 - c * v ^ 2 by ring, Real.exp_sub,
    Real.exp_neg, Real.exp_neg]
  have h1 : Real.exp (c * w ^ 2) ≠ 0 := (Real.exp_pos _).ne'
  have h2 : Real.exp (c * v ^ 2) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- **`p_r = p₀ · e^{−L}`** with `L` the bracket of `abs_logDensityRatio_le`
(`c = 1/(2σ²)`). The product of the scalar identities: the exponentials multiply
into the exponential of the sum, which is what makes the `N`-dimensional Taylor
bound apply coordinatewise-summed rather than one coordinate at a time. -/
theorem prod_gaussianPDFReal_tanhScaleInv {N : ℕ} {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0) {r : ℝ}
    (v : Fin N → ℝ) (hpos : ∀ i, (0 : ℝ) < 1 - r ^ 2 * (v i) ^ 2) :
    ∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
      = (∏ i, gaussianPDFReal 0 σ2 (v i)) *
        Real.exp (-((2 * (σ2 : ℝ))⁻¹ * ∑ i, ((tanhScaleInv r (v i)) ^ 2 - (v i) ^ 2)
          + ∑ i, Real.log (1 - r ^ 2 * (v i) ^ 2))) := by
  have hfac : ∀ i : Fin N, (1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i))
      = gaussianPDFReal 0 σ2 (v i) *
        Real.exp (-((2 * (σ2 : ℝ))⁻¹ * ((tanhScaleInv r (v i)) ^ 2 - (v i) ^ 2)
          + Real.log (1 - r ^ 2 * (v i) ^ 2))) :=
    fun i => gaussianPDFReal_tanhScaleInv hσ (hpos i)
  simp only [hfac]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]

/-- Every coordinate of a `v` in the regime satisfies `r²vᵢ² ≤ 1/4`, since
`vᵢ² ≤ ‖v‖₂² ≤ r⁻¹` and `r ≤ 1/4`. In particular `1 − r²vᵢ² > 0`, so `v` lies in
the box where `p_r` is given by `eq:nd-nonlinear-linearized-density`. -/
theorem sq_mul_sq_le_of_sum_sq {N : ℕ} {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4)
    (v : Fin N → ℝ) (hv : r * ∑ i, v i ^ 2 ≤ 1) (i : Fin N) : r ^ 2 * (v i) ^ 2 ≤ 1 / 4 := by
  have hle : v i ^ 2 ≤ ∑ j, v j ^ 2 := Finset.single_le_sum (f := fun j => v j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [sq_nonneg (v i), sq_nonneg r, Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
    sq_nonneg (v j))]

/-- **The density difference bound** (A-8a, step 6d; tex L5085 and L5100–5104):
on `‖v‖₂ ≤ r^{-1/2}` with `r ≤ 1/4`,

`|p_r(v) − p₀(v)| ≤ C r²(1 + ‖v‖₂⁴) p₀(v)`,

the paper's `C r²(1+‖v‖₂⁴)e^{-c‖v‖₂²}` — the Gaussian factor is `p₀` itself.

The exponential in `|e^{-L} − 1| ≤ |L|e^{|L|}` costs only a constant because the
regime bounds the exponent: `r²(1+‖v‖₂⁴) ≤ r² + (r‖v‖₂²)² ≤ 2`, so `|L| ≤ 2K`
and `e^{|L|} ≤ e^{2K}`. This is the step the paper compresses into "and the
displayed bound follows after decreasing `c`". -/
theorem abs_prod_sub_prod_gaussianPDFReal_le {N : ℕ} {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (v : Fin N → ℝ) (hv : r * ∑ i, v i ^ 2 ≤ 1) :
    |∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
        - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ (((28 / 9) * (2 * (σ2 : ℝ))⁻¹ + 2) * Real.exp (2 * ((28 / 9) * (2 * (σ2 : ℝ))⁻¹ + 2)))
          * r ^ 2 * (1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i) := by
  set c : ℝ := (2 * (σ2 : ℝ))⁻¹ with hc
  set K : ℝ := (28 / 9) * c + 2 with hK
  set S : ℝ := ∑ i, v i ^ 2 with hS
  set P : ℝ := ∏ i, gaussianPDFReal 0 σ2 (v i) with hP
  set L : ℝ := c * ∑ i, (tanhScaleInv r (v i) ^ 2 - v i ^ 2)
    + ∑ i, Real.log (1 - r ^ 2 * v i ^ 2) with hL
  have hc0 : 0 ≤ c := by positivity
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
  have hpos : ∀ i, (0 : ℝ) < 1 - r ^ 2 * (v i) ^ 2 := fun i => by
    have := sq_mul_sq_le_of_sum_sq hr hr4 v hv i; linarith
  have hLbound : |L| ≤ K * r ^ 2 * (1 + S ^ 2) := abs_logDensityRatio_le hr hr4 hc0 v hv
  have hrS : 0 ≤ r * S := by positivity
  have hrS2 : (r * S) ^ 2 ≤ 1 := by nlinarith
  have hreg : r ^ 2 * (1 + S ^ 2) ≤ 2 := by nlinarith
  have hLsmall : |L| ≤ 2 * K := by
    calc |L| ≤ K * r ^ 2 * (1 + S ^ 2) := hLbound
      _ = K * (r ^ 2 * (1 + S ^ 2)) := by ring
      _ ≤ K * 2 := by gcongr
      _ = 2 * K := by ring
  rw [prod_gaussianPDFReal_tanhScaleInv hσ v hpos, ← hL]
  have hfac : P * Real.exp (-L) - P = P * (Real.exp (-L) - 1) := by ring
  rw [hfac, abs_mul, abs_of_nonneg hP0]
  calc P * |Real.exp (-L) - 1| ≤ P * (|(-L)| * Real.exp |(-L)|) := by
        gcongr; exact abs_exp_sub_one_le _
    _ = P * (|L| * Real.exp |L|) := by rw [abs_neg]
    _ ≤ P * ((K * r ^ 2 * (1 + S ^ 2)) * Real.exp (2 * K)) := by gcongr
    _ = (K * Real.exp (2 * K)) * r ^ 2 * (1 + S ^ 2) * P := by ring

/-! ### The annulus `r^{-1/2} < ‖v‖₂ ≤ (2r)⁻¹`

Tex L5105–5108. Outside the inner ball the Taylor bound is unavailable, but it
is also unnecessary: there `r²(1+‖v‖₂⁴) ≥ 1`, so a *crude* comparison of the two
densities already gives the same shape of bound. The comparison is
`p_r ≤ (4/3)^N p₀`, from two coordinatewise facts — the Jacobian
`(1 − r²vᵢ²)⁻¹ ≤ 4/3` on `|r vᵢ| ≤ 1/2`, and `|T_r⁻¹v| ≥ |v|` (because
`|artanh x| ≥ |x|`), which makes the Gaussian factor *decrease*. The resulting
constant depends on `N`, as the paper's does. -/

/-- `x ≤ artanh x` on `[0, 1)`. **Not in Mathlib** — neither this nor the
equivalent `tanh x ≤ x`. The derivative of `artanh s − s` is `(1−s²)⁻¹ − 1 ≥ 0`,
so `artanh s − s` is monotone on `[0, x]` and vanishes at `0`. -/
theorem self_le_artanh {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : x ≤ Real.artanh x := by
  have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Ioo (-1 : ℝ) 1 := fun t ht =>
    ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hx1⟩
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt (fun s : ℝ => Real.artanh s - s) ((1 - t ^ 2)⁻¹ - 1) t := fun t ht =>
    (hasDerivAt_artanh (hsub ht)).sub (hasDerivAt_id t)
  have hmono : MonotoneOn (fun s : ℝ => Real.artanh s - s) (Set.Icc 0 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x) ?_ ?_ ?_
    · exact fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hmem := hsub ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      rw [(hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).deriv, sub_nonneg]
      have h1 : t ^ 2 < 1 := by nlinarith [hmem.1, hmem.2]
      rw [le_inv_comm₀ (by norm_num) (by linarith : (0 : ℝ) < 1 - t ^ 2)]
      nlinarith [sq_nonneg t]
  have hkey := hmono (Set.left_mem_Icc.2 hx0) (Set.right_mem_Icc.2 hx0) hx0
  simp only [Real.artanh_zero, sub_zero] at hkey
  linarith

/-- `artanh` is odd. Mathlib's `Real.artanh_neg` is a *sign* lemma
(`artanh x < 0`), not this. -/
theorem artanh_neg_eq (x : ℝ) : Real.artanh (-x) = -Real.artanh x := by
  unfold Real.artanh
  rw [show (1 + -x) / (1 - -x) = ((1 + x) / (1 - x))⁻¹ by rw [inv_div]; ring_nf,
    Real.sqrt_inv, Real.log_inv]

theorem abs_le_abs_artanh {x : ℝ} (hx : |x| < 1) : |x| ≤ |Real.artanh x| := by
  rcases le_or_gt 0 x with hx0 | hx0
  · have h := self_le_artanh hx0 (lt_of_le_of_lt (le_abs_self x) hx)
    rw [abs_of_nonneg hx0, abs_of_nonneg (le_trans hx0 h)]
    exact h
  · have h1 : -x < 1 := by rw [abs_of_neg hx0] at hx; exact hx
    have h := self_le_artanh (by linarith) h1
    rw [artanh_neg_eq] at h
    rw [abs_of_neg hx0, abs_of_nonpos (by linarith)]
    linarith

/-- **`T_r⁻¹` moves points outward**: `|r⁻¹ artanh(r v)| ≥ |v|`. This is what
makes the Gaussian factor of `p_r` no larger than that of `p₀`. -/
theorem abs_le_abs_tanhScaleInv {r v : ℝ} (hr : 0 < r) (hrv : |r * v| < 1) :
    |v| ≤ |tanhScaleInv r v| := by
  have h := abs_le_abs_artanh hrv
  rw [tanhScaleInv, abs_mul, abs_of_pos (inv_pos.2 hr)]
  rw [abs_mul, abs_of_pos hr] at h
  calc |v| = r⁻¹ * (r * |v|) := by field_simp
    _ ≤ r⁻¹ * |Real.artanh (r * v)| := by gcongr

/-- The centred Gaussian density decreases in `|x|`. -/
theorem gaussianPDFReal_le_of_abs_le {σ2 : ℝ≥0} (hσ0 : (0 : ℝ) < σ2) {x y : ℝ} (h : |x| ≤ |y|) :
    gaussianPDFReal 0 σ2 y ≤ gaussianPDFReal 0 σ2 x := by
  rw [gaussianPDFReal_def]
  simp only [sub_zero]
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith [sq_abs x, sq_abs y, abs_nonneg x, abs_nonneg y]
  gcongr

/-- **The density difference bound on the whole box** (A-8a, step 6e): the bound
of `abs_prod_sub_prod_gaussianPDFReal_le` extends from the inner ball
`‖v‖₂ ≤ r^{-1/2}` to every `v` with `|r vᵢ| ≤ 1/2` — in particular to the
paper's `‖v‖₂ ≤ (2r)⁻¹` — at the cost of enlarging the constant to
`max{K e^{2K}, (4/3)^N + 1}`.

On the annulus the argument is the paper's: `r²(1+‖v‖₂⁴) ≥ r²‖v‖₂⁴ ≥ 1`, and
`|p_r − p₀| ≤ p_r + p₀ ≤ ((4/3)^N + 1)p₀` needs no Taylor expansion at all. -/
theorem abs_prod_sub_prod_gaussianPDFReal_le_of_box {N : ℕ} {σ2 : ℝ≥0} (hσ : (σ2 : ℝ) ≠ 0)
    (hσ0 : (0 : ℝ) < σ2) {r : ℝ} (hr : 0 < r) (hr4 : r ≤ 1 / 4) (v : Fin N → ℝ)
    (hbox : ∀ i, |r * v i| ≤ 1 / 2) :
    |∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
        - ∏ i, gaussianPDFReal 0 σ2 (v i)|
      ≤ max (((28 / 9) * (2 * (σ2 : ℝ))⁻¹ + 2)
              * Real.exp (2 * ((28 / 9) * (2 * (σ2 : ℝ))⁻¹ + 2))) ((4 / 3 : ℝ) ^ N + 1)
          * r ^ 2 * (1 + (∑ i, v i ^ 2) ^ 2) * ∏ i, gaussianPDFReal 0 σ2 (v i) := by
  set S : ℝ := ∑ i, v i ^ 2 with hS
  set P : ℝ := ∏ i, gaussianPDFReal 0 σ2 (v i) with hP
  set A : ℝ := ∏ i, ((1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)))
    with hA
  set K : ℝ := ((28 / 9) * (2 * (σ2 : ℝ))⁻¹ + 2)
    * Real.exp (2 * ((28 / 9) * (2 * (σ2 : ℝ))⁻¹ + 2)) with hK
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 σ2 (v i)
  have hsq : ∀ i, r ^ 2 * (v i) ^ 2 ≤ 1 / 4 := by
    intro i
    have := hbox i
    nlinarith [sq_abs (r * v i), abs_nonneg (r * v i)]
  have hposi : ∀ i, (0 : ℝ) < 1 - r ^ 2 * (v i) ^ 2 := fun i => by have := hsq i; linarith
  have hCN : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ N + 1 := by positivity
  rcases le_or_gt (r * S) 1 with hin | hout
  · exact (abs_prod_sub_prod_gaussianPDFReal_le hσ hr hr4 v hin).trans
      (by gcongr; exact le_max_left _ _)
  · have hAle : A ≤ (4 / 3 : ℝ) ^ N * P := by
      have hfac : ∀ i ∈ Finset.univ,
          (1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i))
            ≤ (4 / 3 : ℝ) * gaussianPDFReal 0 σ2 (v i) := by
        intro i _
        have hjac : (1 - r ^ 2 * (v i) ^ 2)⁻¹ ≤ 4 / 3 := by
          rw [inv_le_comm₀ (hposi i) (by norm_num)]; have := hsq i; linarith
        have hg : gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)) ≤ gaussianPDFReal 0 σ2 (v i) :=
          gaussianPDFReal_le_of_abs_le hσ0
            (abs_le_abs_tanhScaleInv hr (lt_of_le_of_lt (hbox i) (by norm_num)))
        exact mul_le_mul hjac hg (gaussianPDFReal_nonneg 0 σ2 _) (by norm_num)
      have hnonneg : ∀ i ∈ Finset.univ, (0 : ℝ) ≤
          (1 - r ^ 2 * (v i) ^ 2)⁻¹ * gaussianPDFReal 0 σ2 (tanhScaleInv r (v i)) := fun i _ =>
        mul_nonneg (le_of_lt (inv_pos.2 (hposi i))) (gaussianPDFReal_nonneg 0 σ2 _)
      calc A ≤ ∏ i, ((4 / 3 : ℝ) * gaussianPDFReal 0 σ2 (v i)) :=
            Finset.prod_le_prod hnonneg hfac
        _ = (4 / 3 : ℝ) ^ N * P := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hA0 : 0 ≤ A :=
      Finset.prod_nonneg fun i _ =>
        mul_nonneg (le_of_lt (inv_pos.2 (hposi i))) (gaussianPDFReal_nonneg 0 σ2 _)
    have hone : (1 : ℝ) ≤ r ^ 2 * (1 + S ^ 2) := by nlinarith
    have hstep : |A - P| ≤ ((4 / 3 : ℝ) ^ N + 1) * P := by
      rw [abs_sub_le_iff]
      constructor <;> nlinarith
    refine hstep.trans ?_
    calc ((4 / 3 : ℝ) ^ N + 1) * P = ((4 / 3 : ℝ) ^ N + 1) * 1 * P := by ring
      _ ≤ ((4 / 3 : ℝ) ^ N + 1) * (r ^ 2 * (1 + S ^ 2)) * P := by gcongr
      _ = ((4 / 3 : ℝ) ^ N + 1) * r ^ 2 * (1 + S ^ 2) * P := by ring
      _ ≤ max K ((4 / 3 : ℝ) ^ N + 1) * r ^ 2 * (1 + S ^ 2) * P := by
          gcongr
          exact le_max_right _ _

/-! ### Elementary inputs for the integration

Two facts used to integrate the density bound over a ball
(`eq:nd-density-error-ball`, tex L5111–5115). Both are `N`-dimensional
bookkeeping, independent of everything Gaussian.

The first replaces the Euclidean ball by a cube: the paper's `ρ^N` comes from
`volume(B(0,ρ)) ≍ ρ^N`, and since only an upper bound is needed, the cube
`(−ρ, ρ)^N` does the job with `Measure.pi_pi` alone — no Haar-measure ball
volume required. The second turns the polynomial weight `1 + ‖v‖₂⁴` into a
*product* over coordinates, which is what makes `lintegral_pi_prod` apply and
reduces the finiteness of `∫(1+‖v‖₂⁴)p₀` to a scalar Gaussian fourth moment. -/

/-- The Euclidean ball of radius `ρ` sits inside the cube `(−ρ, ρ)^N`, so its
volume is at most `(2ρ)^N`. -/
theorem volume_sum_sq_lt_le {N : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2} ≤ ENNReal.ofReal ((2 * ρ) ^ N) := by
  have hsub : {v : Fin N → ℝ | ∑ i, v i ^ 2 < ρ ^ 2}
      ⊆ Set.univ.pi (fun _ : Fin N => Set.Ioo (-ρ) ρ) := by
    intro v hv
    simp only [Set.mem_setOf_eq] at hv
    intro i _
    have hle : v i ^ 2 ≤ ∑ j, v j ^ 2 := Finset.single_le_sum (f := fun j => v j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : v i ^ 2 < ρ ^ 2 := lt_of_le_of_lt hle hv
    constructor <;> nlinarith [sq_nonneg (v i + ρ), sq_nonneg (v i - ρ)]
  refine (measure_mono hsub).trans ?_
  rw [volume_pi, Measure.pi_pi]
  simp only [Real.volume_Ioo]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (by linarith)]
  ring_nf
  exact le_rfl

/-- `1 + ∑ᵢ aᵢ ≤ ∏ᵢ (1 + aᵢ)` for nonnegative `aᵢ` — the dropped terms of the
expansion are all nonnegative. -/
theorem one_add_sum_le_prod {N : ℕ} (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i, a i ≤ ∏ i, (1 + a i) := by
  classical
  induction (Finset.univ : Finset (Fin N)) using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hs : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => ha j
      nlinarith [ha i, ih]

/-- **The polynomial weight is dominated by a product**:
`1 + ‖v‖₂⁴ ≤ ∏ᵢ (1 + vᵢ²)²`. -/
theorem one_add_sq_sum_sq_le_prod {N : ℕ} (v : Fin N → ℝ) :
    1 + (∑ i, v i ^ 2) ^ 2 ≤ ∏ i, (1 + v i ^ 2) ^ 2 := by
  have hS : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 : 1 + ∑ i, v i ^ 2 ≤ ∏ i, (1 + v i ^ 2) :=
    one_add_sum_le_prod _ fun i => sq_nonneg _
  rw [show ∏ i, (1 + v i ^ 2) ^ 2 = (∏ i, (1 + v i ^ 2)) ^ 2 from Finset.prod_pow ..]
  nlinarith [h1, hS]

/-! ### The envelope and `eq:nd-polar-envelope-dri`

The envelope the proof produces is `h(t) = min{1, e^{-Nt}}` (tex L5128–5132), and
the requirement on it is
`∑_{k∈ℤ} sup_{t∈[k,k+1]} e^{β_{A,N} t} h(t) < ∞` — which is *literally*
`Renewal.driNorm` of `t ↦ e^{βt}h(t)`, the finiteness hypothesis the key renewal
theorem consumes. So the check is stated that way, and `β_{A,N} < N` is exactly
what makes it hold: `e^{βt}h(t)` grows like `e^{βt}` to the left of the origin and
decays like `e^{-(N−β)t}` to the right, so both tails are geometric with ratio
`e^{-a}`, `a = min{β, N−β} > 0`. -/

/-- Summability of the two-sided geometric majorant `e^{-a|k|}` over `ℤ`. -/
lemma summable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Summable (fun k : ℤ => Real.exp (-(a * |(k : ℝ)|))) := by
  have hcast : ∀ k : ℤ, ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := fun k => by simp
  have key : ∀ k : ℤ, Real.exp (-(a * |(k : ℝ)|)) = Real.exp (-a) ^ k.natAbs := by
    intro k; rw [← Real.exp_nat_mul, hcast k]; ring_nf
  simp only [key]
  have hgeom : Summable (fun n : ℕ => Real.exp (-a) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by rw [Real.exp_lt_one_iff]; linarith)
  refine Summable.of_nat_of_neg ?_ ?_ <;> simpa using hgeom

/-- The paper's envelope `h(t) = min{1, e^{-Nt}}` (tex L5131). -/
noncomputable def polarEnvelope (N : ℕ) (t : ℝ) : ℝ := min 1 (Real.exp (-((N : ℝ) * t)))

lemma polarEnvelope_nonneg (N : ℕ) (t : ℝ) : 0 ≤ polarEnvelope N t :=
  le_min zero_le_one (Real.exp_nonneg _)

lemma polarEnvelope_le_one (N : ℕ) (t : ℝ) : polarEnvelope N t ≤ 1 := min_le_left _ _

/-- **`eq:nd-polar-envelope-dri`** (tex L5024–5028): for `0 < β < N`,

`∑_{k∈ℤ} sup_{t∈[k,k+1]} e^{βt} h(t) < ∞`,  `h(t) = min{1, e^{-Nt}}`,

stated as finiteness of `Renewal.driNorm`. On the cell `[k,k+1]` the profile is
at most `e^β e^{-a|k|}` with `a = min{β, N−β}`: for `k ≥ 0` use `h ≤ e^{-Nt}` and
`t ≥ k`, for `k ≤ −1` use `h ≤ 1` and `t ≤ k+1 ≤ 0`. Both cases are geometric,
and this is the *only* place the Cramér exponent bound `β_{A,N} < N` from
`lem:nd-gaussian-cramer-exponent` is spent. -/
theorem driNorm_exp_mul_polarEnvelope_ne_top {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (hβN : β < (N : ℝ)) :
    Renewal.driNorm
        (fun t : ℝ => ENNReal.ofReal (Real.exp (β * t) * polarEnvelope N t)) ≠ ∞ := by
  set a : ℝ := min β ((N : ℝ) - β) with ha
  have ha0 : 0 < a := lt_min hβ (by linarith)
  have haβ : a ≤ β := min_le_left _ _
  have haN : a ≤ (N : ℝ) - β := min_le_right _ _
  have hcell : ∀ k : ℤ,
      Renewal.cellSup (fun t : ℝ => ENNReal.ofReal (Real.exp (β * t) * polarEnvelope N t)) k
        ≤ ENNReal.ofReal (Real.exp β * Real.exp (-(a * |(k : ℝ)|))) := by
    intro k
    refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
    rw [Set.mem_Icc] at ht
    rcases le_or_gt 0 k with hk | hk
    · have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have habs : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg hk0
      have hstep : Real.exp (β * t) * polarEnvelope N t ≤ Real.exp (-(a * |(k : ℝ)|)) := by
        calc Real.exp (β * t) * polarEnvelope N t
            ≤ Real.exp (β * t) * Real.exp (-((N : ℝ) * t)) := by gcongr; exact min_le_right _ _
          _ = Real.exp ((β - (N : ℝ)) * t) := by rw [← Real.exp_add]; ring_nf
          _ ≤ Real.exp (-(a * |(k : ℝ)|)) := by
              rw [Real.exp_le_exp, habs]; nlinarith [ht.1]
      exact hstep.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (Real.one_le_exp hβ.le))
    · have hk1 : (k : ℝ) + 1 ≤ 0 := by
        have : k + 1 ≤ 0 := by omega
        exact_mod_cast this
      have habs : |(k : ℝ)| = -(k : ℝ) := abs_of_nonpos (by linarith)
      calc Real.exp (β * t) * polarEnvelope N t ≤ Real.exp (β * t) * 1 := by
            gcongr; exact polarEnvelope_le_one N t
        _ = Real.exp (β * t) := mul_one _
        _ ≤ Real.exp (β * ((k : ℝ) + 1)) := by rw [Real.exp_le_exp]; nlinarith [ht.2]
        _ = Real.exp β * Real.exp (β * (k : ℝ)) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp β * Real.exp (-(a * |(k : ℝ)|)) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.2 (by rw [habs]; nlinarith)) (Real.exp_nonneg _)
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hcell)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    ((summable_exp_neg_mul_abs ha0).mul_left _)]
  exact ENNReal.ofReal_ne_top

end AbsorptionCutoff
