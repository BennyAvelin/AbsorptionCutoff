/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# The squared-radius mean map and its fixed points

Formalizes the deterministic core of the paper's `lem:gaussian-mean-field-concavity`
(§2): a strictly concave, increasing self-map of `[0,1]` fixing `0` and lying below
the diagonal at `1` has a unique positive fixed point, to which every interior orbit
converges. Also defines the Gaussian squared-radius mean map `V_A`.

## Main results
* `AbsorptionCutoff.exists_unique_positive_fixed` — abstract fixed point via IVT + strict
  concavity; `exists_unique_positive_fixed_of_ratio` — the same via a strictly
  antitone ratio `q ↦ f q / q` (the route used here).
* `AbsorptionCutoff.V` — the mean map `V_A(q) = 𝔼[tanh²(A √q · G)]`, `G ∼ N(0,1)`.
* Tanh calculus (filling Mathlib gaps): `hasDerivAt_tanh`, `deriv_tanh`,
  `self_lt_sinh`, `tanh_div_self_strictAntiOn`, `tanh_sq_comp_div_strictAnti(')`.
* Facts about `V_A`: `V_zero`, `V_nonneg`, `V_lt_one`, `V_continuous`,
  `V_ratio_strictAntiOn` (`q ↦ V_A(q)/q` strictly decreasing for `A ≠ 0`).
* **`AbsorptionCutoff.V_exists_unique_fixed`** — for `A ≠ 0`, `V_A` has a unique positive
  fixed point once it exceeds the diagonal at some `q₀` (which holds for `A > 1`).
  This is the operational content of `lem:gaussian-mean-field-concavity`, proved
  unconditionally via the ratio route.

## Continuations
`AbsorptionCutoff.MeanMap.Dynamics` proves the right derivative at zero and the complete
fixed-point/orbit classification. `AbsorptionCutoff.Supercritical.Deterministic`
constructs the Koenigs coefficient and proves the pointwise and locally uniform
linearization asymptotics used by the supercritical cutoff theorem.
-/

open Set MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- A strictly concave `f` on `[0,1]` with `f 0 = 0` cannot have two distinct
positive fixed points: writing the smaller one as a strict convex combination of `0`
and the larger, strict concavity forces it strictly above the diagonal. -/
lemma no_two_fixed {f : ℝ → ℝ} (hconc : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) f)
    (hf0 : f 0 = 0) {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hfa : f a = a) (hfb : f b = b) (hab : a < b) : False := by
  have hb0 : 0 < b := hb.1
  have ha0 : 0 < a := ha.1
  set s := (b - a) / b with hs
  set t := a / b with ht
  have hs0 : 0 < s := by rw [hs]; exact div_pos (by linarith) hb0
  have ht0 : 0 < t := by rw [ht]; exact div_pos ha0 hb0
  have hsum : s + t = 1 := by rw [hs, ht]; field_simp; ring
  have mem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  have memb : b ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hb0, le_of_lt hb.2⟩
  have hne : (0 : ℝ) ≠ b := ne_of_lt hb0
  have hcomb : s • (0 : ℝ) + t • b = a := by
    simp only [smul_eq_mul, mul_zero, zero_add, ht]; field_simp
  have key := hconc.2 mem0 memb hne hs0 ht0 hsum
  rw [hf0, hfb, hcomb, hfa] at key
  exact lt_irrefl a key

/-- **Existence and uniqueness of the positive fixed point** (state-independent core
of `lem:gaussian-mean-field-concavity`). A continuous, strictly concave self-map `f`
of `[0,1]` with `f 0 = 0`, `f 1 < 1`, that exceeds the diagonal at some interior
point, has a unique fixed point in `(0,1)`. -/
theorem exists_unique_positive_fixed
    {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hconc : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) f)
    (hf0 : f 0 = 0) (hf1 : f 1 < 1)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hexceed : q₀ < f q₀) :
    ∃! q, q ∈ Ioo (0 : ℝ) 1 ∧ f q = q := by
  set g : ℝ → ℝ := fun x => f x - x with hg
  have hsub : Icc q₀ 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (le_of_lt hq₀.1) le_rfl
  have hgc : ContinuousOn g (Icc q₀ 1) := (hcont.mono hsub).sub continuousOn_id
  have hq₀1 : q₀ ≤ 1 := le_of_lt hq₀.2
  have hg1 : g 1 < 0 := by simp only [hg]; linarith
  have hgq₀ : 0 < g q₀ := by simp only [hg]; linarith
  have h0mem : (0 : ℝ) ∈ Icc (g 1) (g q₀) := ⟨le_of_lt hg1, le_of_lt hgq₀⟩
  obtain ⟨c, hcmem, hgc0⟩ := intermediate_value_Icc' hq₀1 hgc h0mem
  have hc_fix : f c = c := by have : f c - c = 0 := hgc0; linarith
  have hc0 : 0 < c := lt_of_lt_of_le hq₀.1 hcmem.1
  have hc1 : c < 1 := by
    rcases lt_or_eq_of_le hcmem.2 with h | h
    · exact h
    · exfalso; rw [h] at hgc0; simp only [hg] at hgc0; linarith
  have hcmem' : c ∈ Ioo (0 : ℝ) 1 := ⟨hc0, hc1⟩
  refine ⟨c, ⟨hcmem', hc_fix⟩, ?_⟩
  rintro y ⟨hymem, hyfix⟩
  rcases lt_trichotomy y c with h | h | h
  · exact (no_two_fixed hconc hf0 hymem hcmem' hyfix hc_fix h).elim
  · exact h
  · exact (no_two_fixed hconc hf0 hcmem' hymem hc_fix hyfix h).elim

/-- Fixed-point existence/uniqueness via a strictly antitone ratio `q ↦ f q / q`
(sidesteps concavity): a positive fixed point satisfies `f q / q = 1`, and an
injective (strictly antitone) ratio has at most one such point. This is the route
used for `V_A`, whose ratio monotonicity follows from `tanh_div_self_strictAntiOn`. -/
theorem exists_unique_positive_fixed_of_ratio
    {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc (0 : ℝ) 1)) (hf1 : f 1 < 1)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hexceed : q₀ < f q₀)
    (hratio : StrictAntiOn (fun q => f q / q) (Ioo (0 : ℝ) 1)) :
    ∃! q, q ∈ Ioo (0 : ℝ) 1 ∧ f q = q := by
  set g : ℝ → ℝ := fun x => f x - x with hg
  have hsub : Icc q₀ 1 ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (le_of_lt hq₀.1) le_rfl
  have hgc : ContinuousOn g (Icc q₀ 1) := (hcont.mono hsub).sub continuousOn_id
  have hg1 : g 1 < 0 := by simp only [hg]; linarith
  have hgq₀ : 0 < g q₀ := by simp only [hg]; linarith
  have h0mem : (0 : ℝ) ∈ Icc (g 1) (g q₀) := ⟨le_of_lt hg1, le_of_lt hgq₀⟩
  obtain ⟨c, hcmem, hgc0⟩ := intermediate_value_Icc' (le_of_lt hq₀.2) hgc h0mem
  have hc_fix : f c = c := by have : f c - c = 0 := hgc0; linarith
  have hc0 : 0 < c := lt_of_lt_of_le hq₀.1 hcmem.1
  have hc1 : c < 1 := by
    rcases lt_or_eq_of_le hcmem.2 with h | h
    · exact h
    · exfalso; rw [h] at hgc0; simp only [hg] at hgc0; linarith
  have hcmem' : c ∈ Ioo (0 : ℝ) 1 := ⟨hc0, hc1⟩
  refine ⟨c, ⟨hcmem', hc_fix⟩, ?_⟩
  rintro y ⟨hymem, hyfix⟩
  apply hratio.injOn hymem hcmem'
  change f y / y = f c / c
  rw [hyfix, hc_fix, div_self hymem.1.ne', div_self hcmem'.1.ne']

/-- The squared-radius mean map `V_A(q) = 𝔼[tanh²(A √q · G)]`, `G ∼ N(0,1)`
(paper §2, `eq:gaussian-mean-field`). -/
noncomputable def V (A q : ℝ) : ℝ :=
  ∫ g, Real.tanh (A * Real.sqrt q * g) ^ 2 ∂(gaussianReal 0 1)

/-- `tanh` is continuous (built from `sinh/cosh`; not known to `fun_prop`). -/
lemma continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-- Derivative of `tanh` (missing from Mathlib): `tanh' x = 1 - tanh² x`. Built from
the quotient rule on `sinh / cosh`. Foundational for the concavity of `V_A`. -/
lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hcosh : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh
  have hfun : (fun y => Real.sinh y / Real.cosh y) = Real.tanh :=
    (funext Real.tanh_eq_sinh_div_cosh).symm
  rw [hfun] at h
  have hval : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2
      = 1 - Real.tanh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]; field_simp
  rwa [hval] at h

/-- `deriv tanh x = 1 - tanh² x`. -/
lemma deriv_tanh (x : ℝ) : deriv Real.tanh x = 1 - Real.tanh x ^ 2 := (hasDerivAt_tanh x).deriv

/-- `tanh` is strictly increasing (missing from Mathlib): its derivative `1 − tanh²`
is everywhere positive. -/
lemma tanh_strictMono : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [deriv_tanh]
  linarith [Real.tanh_sq_lt_one x]

/-- `sech² = 1 − tanh²` is strictly decreasing on `(0,∞)` — a step in the paper's
strict-concavity argument for `V_A` (`f_a'(q) = a²·(tanh x/x)·sech²x` decreasing).
On positives `tanh² ↑`, so `1 − tanh² ↓`. -/
lemma sech_sq_strictAntiOn :
    StrictAntiOn (fun x => 1 - Real.tanh x ^ 2) (Set.Ioi (0 : ℝ)) := by
  intro x hx y _ hxy
  have hx0 : (0 : ℝ) < x := hx
  have htxpos : 0 < Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hx0) (Real.cosh_pos x)
  have hmono : Real.tanh x < Real.tanh y := tanh_strictMono hxy
  simp only
  nlinarith [htxpos, hmono]

/-- The paper's derivative formula for `f_a(q) = tanh²(a√q)`:
`f_a'(q) = a²·(tanh x/x)·sech²x` with `x = a√q` (chain rule through `√`). -/
lemma hasDerivAt_f {a q : ℝ} (ha : a ≠ 0) (hq : 0 < q) :
    HasDerivAt (fun q => Real.tanh (a * Real.sqrt q) ^ 2)
      (a ^ 2 * (Real.tanh (a * Real.sqrt q) / (a * Real.sqrt q))
        * (1 - Real.tanh (a * Real.sqrt q) ^ 2)) q := by
  have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have haq : a * Real.sqrt q ≠ 0 := mul_ne_zero ha hsqrt
  have hu : HasDerivAt (fun q => a * Real.sqrt q) (a * (1 / (2 * Real.sqrt q))) q :=
    (Real.hasDerivAt_sqrt hq.ne').const_mul a
  have hf := ((hasDerivAt_tanh (a * Real.sqrt q)).comp q hu).pow 2
  have hval : a ^ 2 * (Real.tanh (a * Real.sqrt q) / (a * Real.sqrt q))
        * (1 - Real.tanh (a * Real.sqrt q) ^ 2)
      = (2 : ℕ) * Real.tanh (a * Real.sqrt q) ^ (2 - 1)
        * ((1 - Real.tanh (a * Real.sqrt q) ^ 2) * (a * (1 / (2 * Real.sqrt q)))) := by
    field_simp
    push_cast
    ring
  rw [hval]
  exact hf

/-- `y < sinh y` for `y > 0` (missing from Mathlib): `sinh − id` has positive
derivative `cosh − 1 > 0`. Used to sign the derivative of `tanh x / x`. -/
lemma self_lt_sinh {y : ℝ} (hy : 0 < y) : y < Real.sinh y := by
  have hmono : StrictMonoOn (fun x => Real.sinh x - x) (Set.Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (Real.continuous_sinh.sub continuous_id).continuousOn
    · intro x hx
      rw [interior_Ici] at hx
      have hxpos : (0 : ℝ) < x := hx
      have hderiv : HasDerivAt (fun x => Real.sinh x - x) (Real.cosh x - 1) x :=
        (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
      rw [hderiv.deriv]
      have : 1 < Real.cosh x := Real.one_lt_cosh.mpr (ne_of_gt hxpos)
      linarith
  have h0 := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hy.le) hy
  simp only [Real.sinh_zero, sub_zero] at h0
  linarith

/-- `tanh x ≤ x` for `x ≥ 0` (missing from Mathlib): `x − tanh x` is strictly
increasing on `[0,∞)` with derivative `tanh² > 0`. -/
lemma tanh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h; simp
  · have hmono : StrictMonoOn (fun t => t - Real.tanh t) (Set.Ici (0 : ℝ)) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      · exact (continuous_id.sub continuous_tanh).continuousOn
      · intro t ht
        rw [interior_Ici] at ht
        have htpos : 0 < Real.tanh t := by
          rw [Real.tanh_eq_sinh_div_cosh]
          exact div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos t)
        have hd : HasDerivAt (fun t => t - Real.tanh t) (1 - (1 - Real.tanh t ^ 2)) t :=
          (hasDerivAt_id t).sub (hasDerivAt_tanh t)
        rw [hd.deriv]; nlinarith [mul_pos htpos htpos]
    have h0 := hmono Set.self_mem_Ici (Set.mem_Ici.mpr hx) h
    simp only [Real.tanh_zero, sub_zero] at h0
    linarith

/-- `x ↦ tanh x / x` is strictly decreasing on `(0,∞)`. The crux behind the strict
concavity of `V_A`: its derivative `((1−tanh²)x − tanh)/x²` is negative because
`x < sinh x cosh x = sinh(2x)/2`. -/
lemma tanh_div_self_strictAntiOn :
    StrictAntiOn (fun x => Real.tanh x / x) (Set.Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact ContinuousOn.div continuous_tanh.continuousOn continuousOn_id
      (fun x hx => (Set.mem_Ioi.mp hx).ne')
  · intro x hx
    rw [interior_Ioi] at hx
    have hxpos : (0 : ℝ) < x := hx
    have hderiv : HasDerivAt (fun x => Real.tanh x / x)
        (((1 - Real.tanh x ^ 2) * x - Real.tanh x * 1) / x ^ 2) x :=
      (hasDerivAt_tanh x).div (hasDerivAt_id x) (ne_of_gt hxpos)
    rw [hderiv.deriv]
    have hkey : x - Real.sinh x * Real.cosh x < 0 := by
      have h2x : 2 * x < Real.sinh (2 * x) := self_lt_sinh (by linarith)
      rw [Real.sinh_two_mul] at h2x; linarith
    have hmul : ((1 - Real.tanh x ^ 2) * x - Real.tanh x * 1) * Real.cosh x ^ 2
        = x - Real.sinh x * Real.cosh x := by
      have hcne : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
      rw [Real.tanh_eq_sinh_div_cosh]; field_simp; linear_combination x * Real.cosh_sq x
    have hnum : (1 - Real.tanh x ^ 2) * x - Real.tanh x * 1 < 0 := by
      nlinarith [hmul, hkey, (by positivity : (0 : ℝ) < Real.cosh x ^ 2)]
    exact div_neg_of_neg_of_pos hnum (by positivity)

/-- Pointwise ratio monotonicity (`c > 0`): `q ↦ tanh²(c√q)/q` is strictly
decreasing on `(0,∞)`, since it equals `c²·(tanh w/w)²` with `w = c√q`. -/
lemma tanh_sq_comp_div_strictAnti {c : ℝ} (hc : 0 < c) :
    StrictAntiOn (fun q => Real.tanh (c * Real.sqrt q) ^ 2 / q) (Set.Ioi (0 : ℝ)) := by
  have hid : ∀ q : ℝ, 0 < q → Real.tanh (c * Real.sqrt q) ^ 2 / q
      = c ^ 2 * (Real.tanh (c * Real.sqrt q) / (c * Real.sqrt q)) ^ 2 := by
    intro q hq
    have h1 : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    have h2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
    field_simp
    rw [h2]; ring
  intro q₁ hq₁ q₂ hq₂ hlt
  have hq₁0 : (0 : ℝ) < q₁ := hq₁
  have hq₂0 : (0 : ℝ) < q₂ := hq₂
  have hw₁ : (0 : ℝ) < c * Real.sqrt q₁ := by positivity
  have hw₂ : (0 : ℝ) < c * Real.sqrt q₂ := by positivity
  have hwlt : c * Real.sqrt q₁ < c * Real.sqrt q₂ :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hq₁0.le hlt) hc
  have hr : Real.tanh (c * Real.sqrt q₂) / (c * Real.sqrt q₂)
      < Real.tanh (c * Real.sqrt q₁) / (c * Real.sqrt q₁) :=
    tanh_div_self_strictAntiOn (Set.mem_Ioi.mpr hw₁) (Set.mem_Ioi.mpr hw₂) hwlt
  have hr₂pos : 0 < Real.tanh (c * Real.sqrt q₂) / (c * Real.sqrt q₂) :=
    div_pos (by rw [Real.tanh_eq_sinh_div_cosh]
                exact div_pos (Real.sinh_pos_iff.mpr hw₂) (Real.cosh_pos _)) hw₂
  have hsq : (Real.tanh (c * Real.sqrt q₂) / (c * Real.sqrt q₂)) ^ 2
      < (Real.tanh (c * Real.sqrt q₁) / (c * Real.sqrt q₁)) ^ 2 :=
    sq_lt_sq' (by linarith) hr
  simp only [hid q₁ hq₁0, hid q₂ hq₂0]
  exact mul_lt_mul_of_pos_left hsq (by positivity)

/-- Same, for any `c ≠ 0` (reduce to `|c|` via `tanh(c√q)² = tanh(|c|√q)²`). This is
the pointwise input for the ratio monotonicity of `V_A` (with `c = A·g`). -/
lemma tanh_sq_comp_div_strictAnti' {c : ℝ} (hc : c ≠ 0) :
    StrictAntiOn (fun q => Real.tanh (c * Real.sqrt q) ^ 2 / q) (Set.Ioi (0 : ℝ)) := by
  have heq : (fun q => Real.tanh (c * Real.sqrt q) ^ 2 / q)
      = (fun q => Real.tanh (|c| * Real.sqrt q) ^ 2 / q) := by
    funext q
    rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, Real.tanh_neg, neg_sq]
  rw [heq]
  exact tanh_sq_comp_div_strictAnti (abs_pos.mpr hc)

/-- `f_a'(q) = a²·(tanh x/x)·sech²x` (`x=a√q`) is strictly decreasing on `(0,∞)` for
`a>0`: a product of two positive strictly-decreasing functions, composed with the
increasing `x = a√q`. This is the paper's key monotonicity for the concavity of `V_A`. -/
lemma deriv_f_strictAntiOn {a : ℝ} (ha : 0 < a) :
    StrictAntiOn (fun q => a ^ 2 * (Real.tanh (a * Real.sqrt q) / (a * Real.sqrt q))
      * (1 - Real.tanh (a * Real.sqrt q) ^ 2)) (Set.Ioi (0 : ℝ)) := by
  intro q₁ hq₁ q₂ hq₂ hlt
  have hq₁0 : (0 : ℝ) < q₁ := hq₁
  have hq₂0 : (0 : ℝ) < q₂ := hq₂
  have hx₁ : (0 : ℝ) < a * Real.sqrt q₁ := by positivity
  have hx₂ : (0 : ℝ) < a * Real.sqrt q₂ := by positivity
  have hxlt : a * Real.sqrt q₁ < a * Real.sqrt q₂ :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hq₁0.le hlt) ha
  have hr : Real.tanh (a * Real.sqrt q₂) / (a * Real.sqrt q₂)
      < Real.tanh (a * Real.sqrt q₁) / (a * Real.sqrt q₁) :=
    tanh_div_self_strictAntiOn (Set.mem_Ioi.mpr hx₁) (Set.mem_Ioi.mpr hx₂) hxlt
  have hs : 1 - Real.tanh (a * Real.sqrt q₂) ^ 2 < 1 - Real.tanh (a * Real.sqrt q₁) ^ 2 :=
    sech_sq_strictAntiOn (Set.mem_Ioi.mpr hx₁) (Set.mem_Ioi.mpr hx₂) hxlt
  have hr₂pos : 0 < Real.tanh (a * Real.sqrt q₂) / (a * Real.sqrt q₂) :=
    div_pos (by rw [Real.tanh_eq_sinh_div_cosh]
                exact div_pos (Real.sinh_pos_iff.mpr hx₂) (Real.cosh_pos _)) hx₂
  have hs₂pos : 0 < 1 - Real.tanh (a * Real.sqrt q₂) ^ 2 := by
    linarith [Real.tanh_sq_lt_one (a * Real.sqrt q₂)]
  have hprod := mul_lt_mul'' hr hs (le_of_lt hr₂pos) (le_of_lt hs₂pos)
  have hregroup : ∀ q : ℝ, a ^ 2 * (Real.tanh (a * Real.sqrt q) / (a * Real.sqrt q))
      * (1 - Real.tanh (a * Real.sqrt q) ^ 2)
      = a ^ 2 * ((Real.tanh (a * Real.sqrt q) / (a * Real.sqrt q))
        * (1 - Real.tanh (a * Real.sqrt q) ^ 2)) := fun q => by ring
  simp only [hregroup]
  exact mul_lt_mul_of_pos_left hprod (by positivity)

/-- `f_a(q) = tanh²(a√q)` is strictly concave on `[0,1]` for `a > 0` (paper's route):
its derivative `f_a'` is strictly decreasing (`deriv_f_strictAntiOn`). -/
lemma f_strictConcaveOn {a : ℝ} (ha : 0 < a) :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun q => Real.tanh (a * Real.sqrt q) ^ 2) := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 1)
    ((continuous_tanh.comp (continuous_const.mul Real.continuous_sqrt)).pow 2).continuousOn ?_
  rw [interior_Icc]
  have heqon : Set.EqOn (fun q => a ^ 2 * (Real.tanh (a * Real.sqrt q) / (a * Real.sqrt q))
      * (1 - Real.tanh (a * Real.sqrt q) ^ 2))
      (deriv (fun q => Real.tanh (a * Real.sqrt q) ^ 2)) (Set.Ioo 0 1) := by
    intro q hq
    exact ((hasDerivAt_f ha.ne' hq.1).deriv).symm
  exact ((deriv_f_strictAntiOn ha).mono (fun q hq => hq.1)).congr heqon

/-- Same for any `c ≠ 0` (reduce to `|c|` via `tanh(c√q)² = tanh(|c|√q)²`): the
pointwise input `q ↦ tanh²(c√q)` is strictly concave on `[0,1]` (with `c = A·g`). -/
lemma f_strictConcaveOn' {c : ℝ} (hc : c ≠ 0) :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun q => Real.tanh (c * Real.sqrt q) ^ 2) := by
  have heq : (fun q => Real.tanh (c * Real.sqrt q) ^ 2)
      = (fun q => Real.tanh (|c| * Real.sqrt q) ^ 2) := by
    funext q
    rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, Real.tanh_neg, neg_sq]
  rw [heq]
  exact f_strictConcaveOn (abs_pos.mpr hc)

/-- `V_A(0) = 0`: at `q = 0` the integrand is `tanh²(0) = 0`. -/
lemma V_zero (A : ℝ) : V A 0 = 0 := by
  simp only [V, Real.sqrt_zero, mul_zero, zero_mul, Real.tanh_zero]; simp

/-- `V_A ≥ 0`: the integrand is a square. -/
lemma V_nonneg (A q : ℝ) : 0 ≤ V A q := by
  apply integral_nonneg; intro g; positivity

/-- `V_A` is continuous (continuity under the integral, dominated by `1`). Discharges
the continuity hypothesis of the fixed-point statement. -/
lemma V_continuous (A : ℝ) : Continuous (V A) := by
  apply continuous_of_dominated (bound := fun _ => (1 : ℝ))
  · intro q
    exact ((continuous_tanh.comp (by fun_prop)).pow 2).aestronglyMeasurable
  · intro q
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [Real.tanh_lt_one (A * Real.sqrt q * g), Real.neg_one_lt_tanh (A * Real.sqrt q * g)]
  · exact integrable_const 1
  · filter_upwards with g
    exact (continuous_tanh.comp ((continuous_const.mul Real.continuous_sqrt).mul
      continuous_const)).pow 2

/-- `V_A(q) < 1`: since `tanh² < 1` pointwise, `1 − V_A(q) = ∫ (1 − tanh²) dμ > 0`.
In particular `V_A(1) < 1`, discharging one structural hypothesis below. -/
lemma V_lt_one (A q : ℝ) : V A q < 1 := by
  have hcont : Continuous (fun g : ℝ => Real.tanh (A * Real.sqrt q * g) ^ 2) :=
    (continuous_tanh.comp (by fun_prop)).pow 2
  have hbdd : ∀ g : ℝ, Real.tanh (A * Real.sqrt q * g) ^ 2 ≤ 1 := fun g => by
    nlinarith [Real.tanh_lt_one (A * Real.sqrt q * g),
      Real.neg_one_lt_tanh (A * Real.sqrt q * g)]
  have hint : Integrable (fun g : ℝ => Real.tanh (A * Real.sqrt q * g) ^ 2)
      (gaussianReal 0 1) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hcont.measurable.aestronglyMeasurable
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hbdd g
  have hpos : ∀ g : ℝ, 0 < 1 - Real.tanh (A * Real.sqrt q * g) ^ 2 := fun g => by
    nlinarith [Real.tanh_lt_one (A * Real.sqrt q * g),
      Real.neg_one_lt_tanh (A * Real.sqrt q * g)]
  have hint' : Integrable (fun g : ℝ => 1 - Real.tanh (A * Real.sqrt q * g) ^ 2)
      (gaussianReal 0 1) := (integrable_const 1).sub hint
  have hsupp : (0 : ENNReal) < (gaussianReal 0 1)
      (Function.support fun g : ℝ => 1 - Real.tanh (A * Real.sqrt q * g) ^ 2) := by
    have hset : (Function.support fun g : ℝ => 1 - Real.tanh (A * Real.sqrt q * g) ^ 2)
        = Set.univ := by
      ext g
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (hpos g)
    rw [hset, measure_univ]; exact one_pos
  have hintpos : 0 < ∫ g, (1 - Real.tanh (A * Real.sqrt q * g) ^ 2) ∂(gaussianReal 0 1) :=
    (integral_pos_iff_support_of_nonneg (fun g => le_of_lt (hpos g)) hint').mpr hsupp
  have h1 : ∫ g, (1 - Real.tanh (A * Real.sqrt q * g) ^ 2) ∂(gaussianReal 0 1)
      = ∫ _g : ℝ, (1 : ℝ) ∂(gaussianReal 0 1)
        - ∫ g, Real.tanh (A * Real.sqrt q * g) ^ 2 ∂(gaussianReal 0 1) :=
    integral_sub (integrable_const 1) hint
  have hone : ∫ _g : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) = 1 := by simp
  rw [h1, hone] at hintpos
  change (∫ g, Real.tanh (A * Real.sqrt q * g) ^ 2 ∂(gaussianReal 0 1)) < 1
  linarith [hintpos]

/-- The paper's positive-fixed-point statement for `V_A`. Continuity (`V_continuous`)
and the boundary value `V_A(1) < 1` (`V_lt_one`) are now supplied; the only remaining
hypotheses are strict concavity of `V_A` and that it exceeds the diagonal at some `q₀`
(the latter coming from `V_A'(0+) = A² > 1` when `A > 1`). Discharging strict concavity
makes this `lem:gaussian-mean-field-concavity` outright. -/
theorem V_exists_unique_fixed_of_structural {A : ℝ}
    (hconc : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (V A))
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hexceed : q₀ < V A q₀) :
    ∃! q, q ∈ Ioo (0 : ℝ) 1 ∧ V A q = q :=
  exists_unique_positive_fixed (V_continuous A).continuousOn hconc (V_zero A)
    (V_lt_one A 1) hq₀ hexceed

/-- The Gaussian has no atom at `0` (`{0}` is `volume`-null and the Gaussian is
absolutely continuous). Needed for the strict integral inequality below. -/
lemma gaussianReal_singleton_zero : (gaussianReal 0 1) {(0 : ℝ)} = 0 :=
  (gaussianReal_absolutelyContinuous 0 (by norm_num)) (by simp)

/-- **Ratio monotonicity of `V_A`** (for `A ≠ 0`): `q ↦ V_A(q)/q` is strictly
decreasing on `(0,1)`. Integrate the pointwise `tanh_sq_comp_div_strictAnti'`
(strict off the null set `{g = 0}`) via `integral_pos_iff_support_of_nonneg`. -/
lemma V_ratio_strictAntiOn {A : ℝ} (hA : A ≠ 0) :
    StrictAntiOn (fun q => V A q / q) (Set.Ioo (0 : ℝ) 1) := by
  have hInt : ∀ q : ℝ, Integrable
      (fun g => Real.tanh (A * Real.sqrt q * g) ^ 2 / q) (gaussianReal 0 1) := by
    intro q
    have hm : AEStronglyMeasurable
        (fun g => Real.tanh (A * Real.sqrt q * g) ^ 2) (gaussianReal 0 1) :=
      ((continuous_tanh.comp (by fun_prop)).pow 2).measurable.aestronglyMeasurable
    apply Integrable.div_const
    refine Integrable.mono' (integrable_const (1 : ℝ)) hm ?_
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (Real.tanh_sq_lt_one _).le
  have hVq : ∀ q : ℝ, V A q / q
      = ∫ g, Real.tanh (A * Real.sqrt q * g) ^ 2 / q ∂(gaussianReal 0 1) := by
    intro q; rw [V, integral_div]
  intro q₁ hq₁ q₂ hq₂ hlt
  have hq₁0 : 0 < q₁ := hq₁.1
  have hq₂0 : 0 < q₂ := hq₂.1
  have harg : ∀ q g : ℝ, A * Real.sqrt q * g = A * g * Real.sqrt q := fun q g => by ring
  have hstrict : ∀ g : ℝ, g ≠ 0 →
      Real.tanh (A * Real.sqrt q₂ * g) ^ 2 / q₂ < Real.tanh (A * Real.sqrt q₁ * g) ^ 2 / q₁ := by
    intro g hg
    have key := tanh_sq_comp_div_strictAnti' (mul_ne_zero hA hg)
      (Set.mem_Ioi.mpr hq₁0) (Set.mem_Ioi.mpr hq₂0) hlt
    rw [harg q₁ g, harg q₂ g]; exact key
  have hle : ∀ g : ℝ,
      Real.tanh (A * Real.sqrt q₂ * g) ^ 2 / q₂ ≤ Real.tanh (A * Real.sqrt q₁ * g) ^ 2 / q₁ := by
    intro g; rcases eq_or_ne g 0 with hg | hg
    · subst hg; simp
    · exact (hstrict g hg).le
  have hnn : ∀ g : ℝ, 0 ≤ Real.tanh (A * Real.sqrt q₁ * g) ^ 2 / q₁
      - Real.tanh (A * Real.sqrt q₂ * g) ^ 2 / q₂ := fun g => by linarith [hle g]
  have hsupp : 0 < (gaussianReal 0 1) (Function.support (fun g =>
      Real.tanh (A * Real.sqrt q₁ * g) ^ 2 / q₁ - Real.tanh (A * Real.sqrt q₂ * g) ^ 2 / q₂)) := by
    have hsub : {(0 : ℝ)}ᶜ ⊆ Function.support (fun g =>
        Real.tanh (A * Real.sqrt q₁ * g) ^ 2 / q₁ - Real.tanh (A * Real.sqrt q₂ * g) ^ 2 / q₂) := by
      intro g hg
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hg
      simp only [Function.mem_support, ne_eq, sub_eq_zero]
      exact ne_of_gt (hstrict g hg)
    have h0 : 0 < (gaussianReal 0 1) ({(0 : ℝ)}ᶜ) := by
      rw [prob_compl_eq_one_sub (measurableSet_singleton 0), gaussianReal_singleton_zero]; simp
    exact lt_of_lt_of_le h0 (measure_mono hsub)
  have hpos : 0 < ∫ g, (Real.tanh (A * Real.sqrt q₁ * g) ^ 2 / q₁
      - Real.tanh (A * Real.sqrt q₂ * g) ^ 2 / q₂) ∂(gaussianReal 0 1) :=
    (integral_pos_iff_support_of_nonneg hnn ((hInt q₁).sub (hInt q₂))).mpr hsupp
  rw [integral_sub (hInt q₁) (hInt q₂)] at hpos
  change V A q₂ / q₂ < V A q₁ / q₁
  rw [hVq q₁, hVq q₂]; linarith [hpos]

/-- **`V_A` is strictly concave on `[0,1]`** for `A ≠ 0` (paper's
`lem:gaussian-mean-field-concavity`): integrate the pointwise strict concavity
`f_strictConcaveOn'` of `q ↦ tanh²(A·g·√q)`, which is strict off the Gaussian-null
set `{g = 0}`, via `integral_pos_iff_support_of_nonneg`. -/
lemma V_strictConcaveOn {A : ℝ} (hA : A ≠ 0) :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (V A) := by
  refine ⟨convex_Icc 0 1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hInt : ∀ q : ℝ, Integrable (fun g => Real.tanh (A * Real.sqrt q * g) ^ 2)
      (gaussianReal 0 1) := by
    intro q
    have hm : AEStronglyMeasurable (fun g => Real.tanh (A * Real.sqrt q * g) ^ 2)
        (gaussianReal 0 1) :=
      ((continuous_tanh.comp (by fun_prop)).pow 2).measurable.aestronglyMeasurable
    refine Integrable.mono' (integrable_const (1 : ℝ)) hm ?_
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (Real.tanh_sq_lt_one _).le
  have hstrict : ∀ g : ℝ, g ≠ 0 →
      a * Real.tanh (A * Real.sqrt x * g) ^ 2 + b * Real.tanh (A * Real.sqrt y * g) ^ 2
        < Real.tanh (A * Real.sqrt (a * x + b * y) * g) ^ 2 := by
    intro g hg
    have hpc := (f_strictConcaveOn' (mul_ne_zero hA hg)).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at hpc
    rw [mul_right_comm A g (Real.sqrt x), mul_right_comm A g (Real.sqrt y),
        mul_right_comm A g (Real.sqrt (a * x + b * y))] at hpc
    exact hpc
  have hle : ∀ g : ℝ,
      a * Real.tanh (A * Real.sqrt x * g) ^ 2 + b * Real.tanh (A * Real.sqrt y * g) ^ 2
        ≤ Real.tanh (A * Real.sqrt (a * x + b * y) * g) ^ 2 := by
    intro g; rcases eq_or_ne g 0 with hg | hg
    · subst hg; simp
    · exact (hstrict g hg).le
  have hLint : Integrable (fun g => a * Real.tanh (A * Real.sqrt x * g) ^ 2
      + b * Real.tanh (A * Real.sqrt y * g) ^ 2) (gaussianReal 0 1) :=
    ((hInt x).const_mul a).add ((hInt y).const_mul b)
  have hlin : a * V A x + b * V A y
      = ∫ g, (a * Real.tanh (A * Real.sqrt x * g) ^ 2
          + b * Real.tanh (A * Real.sqrt y * g) ^ 2) ∂(gaussianReal 0 1) := by
    simp only [V]
    rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add ((hInt x).const_mul a) ((hInt y).const_mul b)]
  have hnn : ∀ g : ℝ, 0 ≤ Real.tanh (A * Real.sqrt (a * x + b * y) * g) ^ 2
      - (a * Real.tanh (A * Real.sqrt x * g) ^ 2 + b * Real.tanh (A * Real.sqrt y * g) ^ 2) :=
    fun g => by linarith [hle g]
  have hsupp : 0 < (gaussianReal 0 1) (Function.support (fun g =>
      Real.tanh (A * Real.sqrt (a * x + b * y) * g) ^ 2
        - (a * Real.tanh (A * Real.sqrt x * g) ^ 2
          + b * Real.tanh (A * Real.sqrt y * g) ^ 2))) := by
    have hsub : {(0 : ℝ)}ᶜ ⊆ Function.support (fun g =>
        Real.tanh (A * Real.sqrt (a * x + b * y) * g) ^ 2
          - (a * Real.tanh (A * Real.sqrt x * g) ^ 2
            + b * Real.tanh (A * Real.sqrt y * g) ^ 2)) := by
      intro g hg
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hg
      simp only [Function.mem_support, ne_eq, sub_eq_zero]
      exact ne_of_gt (hstrict g hg)
    have h0 : 0 < (gaussianReal 0 1) ({(0 : ℝ)}ᶜ) := by
      rw [prob_compl_eq_one_sub (measurableSet_singleton 0), gaussianReal_singleton_zero]; simp
    exact lt_of_lt_of_le h0 (measure_mono hsub)
  have hpos : 0 < ∫ g, (Real.tanh (A * Real.sqrt (a * x + b * y) * g) ^ 2
      - (a * Real.tanh (A * Real.sqrt x * g) ^ 2 + b * Real.tanh (A * Real.sqrt y * g) ^ 2))
      ∂(gaussianReal 0 1) :=
    (integral_pos_iff_support_of_nonneg hnn ((hInt (a * x + b * y)).sub hLint)).mpr hsupp
  have hRV : (∫ g, Real.tanh (A * Real.sqrt (a * x + b * y) * g) ^ 2 ∂(gaussianReal 0 1))
      = V A (a * x + b * y) := rfl
  rw [integral_sub (hInt (a * x + b * y)) hLint, hRV, ← hlin] at hpos
  linarith [hpos]

/-- **`V_A` is strictly increasing on `[0,1]`** for `A ≠ 0` (paper's
`lem:gaussian-mean-field-concavity`): pointwise `q ↦ tanh²(A·g·√q)` is increasing
(`tanh` increasing, `√` increasing), strict off the Gaussian-null set `{g = 0}`;
integrate. -/
lemma V_strictMonoOn {A : ℝ} (hA : A ≠ 0) : StrictMonoOn (V A) (Icc (0 : ℝ) 1) := by
  intro q₁ hq₁ q₂ hq₂ hlt
  have hq₁0 : 0 ≤ q₁ := hq₁.1
  have hInt : ∀ q : ℝ, Integrable (fun g => Real.tanh (A * Real.sqrt q * g) ^ 2)
      (gaussianReal 0 1) := by
    intro q
    have hm : AEStronglyMeasurable (fun g => Real.tanh (A * Real.sqrt q * g) ^ 2)
        (gaussianReal 0 1) :=
      ((continuous_tanh.comp (by fun_prop)).pow 2).measurable.aestronglyMeasurable
    refine Integrable.mono' (integrable_const (1 : ℝ)) hm ?_
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (Real.tanh_sq_lt_one _).le
  have hstrict : ∀ g : ℝ, g ≠ 0 →
      Real.tanh (A * Real.sqrt q₁ * g) ^ 2 < Real.tanh (A * Real.sqrt q₂ * g) ^ 2 := by
    intro g hg
    have hev : ∀ q : ℝ, Real.tanh (A * Real.sqrt q * g) ^ 2
        = Real.tanh (|A * g| * Real.sqrt q) ^ 2 := by
      intro q
      rw [mul_right_comm A (Real.sqrt q) g]
      rcases abs_cases (A * g) with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
      · rw [h, neg_mul, Real.tanh_neg, neg_sq]
    rw [hev q₁, hev q₂]
    have hcabs : 0 < |A * g| := abs_pos.mpr (mul_ne_zero hA hg)
    have hu : |A * g| * Real.sqrt q₁ < |A * g| * Real.sqrt q₂ :=
      mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt hq₁0 hlt) hcabs
    have h1 : Real.tanh (|A * g| * Real.sqrt q₁) < Real.tanh (|A * g| * Real.sqrt q₂) :=
      tanh_strictMono hu
    have h0 : 0 ≤ Real.tanh (|A * g| * Real.sqrt q₁) := by
      have hge : (0 : ℝ) ≤ |A * g| * Real.sqrt q₁ := by positivity
      calc (0 : ℝ) = Real.tanh 0 := Real.tanh_zero.symm
        _ ≤ _ := tanh_strictMono.monotone hge
    nlinarith [h1, h0]
  have hle : ∀ g : ℝ,
      Real.tanh (A * Real.sqrt q₁ * g) ^ 2 ≤ Real.tanh (A * Real.sqrt q₂ * g) ^ 2 := by
    intro g; rcases eq_or_ne g 0 with hg | hg
    · subst hg; simp
    · exact (hstrict g hg).le
  have hnn : ∀ g : ℝ, 0 ≤ Real.tanh (A * Real.sqrt q₂ * g) ^ 2
      - Real.tanh (A * Real.sqrt q₁ * g) ^ 2 := fun g => by linarith [hle g]
  have hsupp : 0 < (gaussianReal 0 1) (Function.support (fun g =>
      Real.tanh (A * Real.sqrt q₂ * g) ^ 2 - Real.tanh (A * Real.sqrt q₁ * g) ^ 2)) := by
    have hsub : {(0 : ℝ)}ᶜ ⊆ Function.support (fun g =>
        Real.tanh (A * Real.sqrt q₂ * g) ^ 2 - Real.tanh (A * Real.sqrt q₁ * g) ^ 2) := by
      intro g hg
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hg
      simp only [Function.mem_support, ne_eq, sub_eq_zero]
      exact ne_of_gt (hstrict g hg)
    have h0 : 0 < (gaussianReal 0 1) ({(0 : ℝ)}ᶜ) := by
      rw [prob_compl_eq_one_sub (measurableSet_singleton 0), gaussianReal_singleton_zero]; simp
    exact lt_of_lt_of_le h0 (measure_mono hsub)
  have hpos : 0 < ∫ g, (Real.tanh (A * Real.sqrt q₂ * g) ^ 2
      - Real.tanh (A * Real.sqrt q₁ * g) ^ 2) ∂(gaussianReal 0 1) :=
    (integral_pos_iff_support_of_nonneg hnn ((hInt q₂).sub (hInt q₁))).mpr hsupp
  rw [integral_sub (hInt q₂) (hInt q₁)] at hpos
  change V A q₁ < V A q₂
  have hVq₁ : (∫ g, Real.tanh (A * Real.sqrt q₁ * g) ^ 2 ∂(gaussianReal 0 1)) = V A q₁ := rfl
  have hVq₂ : (∫ g, Real.tanh (A * Real.sqrt q₂ * g) ^ 2 ∂(gaussianReal 0 1)) = V A q₂ := rfl
  rw [hVq₁, hVq₂] at hpos
  linarith [hpos]

/-- **Unconditional fixed point for `V_A`** = the paper's `lem:gaussian-mean-field-concavity`:
for `A ≠ 0`, once `V_A` exceeds the diagonal at some interior `q₀` (which holds when
`A > 1`), it has a unique positive fixed point. Proved the paper's way — via strict
concavity of `V_A` (`V_strictConcaveOn`); continuity and `V_A(1) < 1` are also discharged. -/
theorem V_exists_unique_fixed {A : ℝ} (hA : A ≠ 0)
    {q₀ : ℝ} (hq₀ : q₀ ∈ Ioo (0 : ℝ) 1) (hexceed : q₀ < V A q₀) :
    ∃! q, q ∈ Ioo (0 : ℝ) 1 ∧ V A q = q :=
  exists_unique_positive_fixed (V_continuous A).continuousOn (V_strictConcaveOn hA)
    (V_zero A) (V_lt_one A 1) hq₀ hexceed

/-- Second moment of the standard Gaussian is finite: `g ↦ g²` is integrable. -/
lemma integrable_sq_gaussian : Integrable (fun g : ℝ => g ^ 2) (gaussianReal 0 1) := by
  simpa using (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq

end AbsorptionCutoff
