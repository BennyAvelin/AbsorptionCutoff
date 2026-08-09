import AbsorptionCutoff.MeanMap.Basic

open Set MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-! ### The near-zero slope `V_A'(0+) = A²` and the exceed-diagonal hypothesis

Paper `lem:gaussian-mean-field-concavity`: `V_A(q) = A²q + o(q)` near `0`, so
`V_A'(0+) = lim_{q→0⁺} V_A(q)/q = A²`. For `A > 1` this exceeds the diagonal near `0`,
discharging the last hypothesis of `V_exists_unique_fixed`. The limit is dominated
convergence of `g ↦ tanh²(A√q·g)/q → (Ag)²` (bound `tanh²x ≤ x²`, integrable second
moment), using `∫ g² = 1`. -/

open Filter Topology

/-- `tanh² x ≤ x²` (i.e. `|tanh x| ≤ |x|`). -/
lemma tanh_sq_le_sq (x : ℝ) : Real.tanh x ^ 2 ≤ x ^ 2 := by
  rcases le_total 0 x with hx | hx
  · have h0 : 0 ≤ Real.tanh x := by have := tanh_strictMono.monotone hx; simpa using this
    nlinarith [tanh_le_self hx, h0]
  · have h1 : Real.tanh (-x) ≤ -x := tanh_le_self (by linarith)
    rw [Real.tanh_neg] at h1
    have h2 : Real.tanh x ≤ 0 := by have := tanh_strictMono.monotone hx; simpa using this
    nlinarith [h1, h2]

/-- `tanh u / u → 1` as `u → 0` (the slope of `tanh` at `0`, where `tanh'(0) = 1`). -/
lemma tendsto_tanh_div_self_one :
    Tendsto (fun u : ℝ => Real.tanh u / u) (𝓝[≠] 0) (𝓝 1) := by
  have hd : HasDerivAt Real.tanh 1 0 := by simpa using hasDerivAt_tanh 0
  refine hd.tendsto_slope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u _
  rw [slope_def_field, Real.tanh_zero, sub_zero, sub_zero]

/-- Second moment of the standard Gaussian: `∫ g² = Var[id] = 1` (its mean is `0`). -/
lemma integral_sq_gaussian : ∫ g : ℝ, g ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hv := variance_id_gaussianReal (μ := 0) (v := 1)
  have hi : ∫ g : ℝ, g ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at hv
  simp only [id_eq, hi, sub_zero] at hv
  simpa using hv

/-- Pointwise near-zero limit of the ratio integrand: for `g ≠ 0`,
`tanh²(A√q·g)/q → (Ag)²` as `q → 0⁺` (write it as `(tanh u/u)²·(Ag)²`, `u=A√q·g→0`). -/
lemma tendsto_tanh_sq_div_ratio {A g : ℝ} (hA : A ≠ 0) (hg : g ≠ 0) :
    Tendsto (fun q : ℝ => Real.tanh (A * Real.sqrt q * g) ^ 2 / q) (𝓝[>] 0) (𝓝 ((A * g) ^ 2)) := by
  have hmap : Tendsto (fun q : ℝ => A * Real.sqrt q * g) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun q : ℝ => A * Real.sqrt q * g) := by fun_prop
      have h : Tendsto (fun q : ℝ => A * Real.sqrt q * g) (𝓝[>] 0) (𝓝 (A * Real.sqrt 0 * g)) :=
        (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    · filter_upwards [self_mem_nhdsWithin] with q (hq : 0 < q)
      exact mul_ne_zero (mul_ne_zero hA (Real.sqrt_pos.mpr hq).ne') hg
  have hsq : Tendsto (fun q : ℝ => (Real.tanh (A * Real.sqrt q * g) / (A * Real.sqrt q * g)) ^ 2)
      (𝓝[>] 0) (𝓝 1) := by simpa using (tendsto_tanh_div_self_one.comp hmap).pow 2
  have hfin := hsq.mul_const ((A * g) ^ 2)
  simp only [one_mul] at hfin
  refine hfin.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q (hq : 0 < q)
  have hsqrt : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hu : A * Real.sqrt q * g ≠ 0 := mul_ne_zero (mul_ne_zero hA (Real.sqrt_pos.mpr hq).ne') hg
  field_simp
  rw [hsqrt]; ring

/-- **`V_A'(0+) = A²`** (paper `eq:gaussian-mean-field-near-zero`): the near-zero slope
`V_A(q)/q → A²` as `q → 0⁺`. Dominated convergence of `g ↦ tanh²(A√q·g)/q → (Ag)²`
(bound `tanh² x ≤ x²`, integrable second moment `A²g²`), with `∫ g² = 1`. -/
lemma V_ratio_tendsto {A : ℝ} (hA : A ≠ 0) :
    Tendsto (fun q => V A q / q) (𝓝[>] 0) (𝓝 (A ^ 2)) := by
  have hbound_int : Integrable (fun g : ℝ => A ^ 2 * g ^ 2) (gaussianReal 0 1) :=
    integrable_sq_gaussian.const_mul (A ^ 2)
  have hne : ∀ᵐ g ∂(gaussianReal 0 1), g ≠ 0 := by
    rw [ae_iff]; simpa using gaussianReal_singleton_zero
  have htarget : ∫ g, (A * g) ^ 2 ∂(gaussianReal 0 1) = A ^ 2 := by
    have he : (fun g : ℝ => (A * g) ^ 2) = fun g => A ^ 2 * g ^ 2 := by funext g; ring
    rw [he, integral_const_mul, integral_sq_gaussian, mul_one]
  have hconv : Tendsto
      (fun q => ∫ g, Real.tanh (A * Real.sqrt q * g) ^ 2 / q ∂(gaussianReal 0 1))
      (𝓝[>] 0) (𝓝 (∫ g, (A * g) ^ 2 ∂(gaussianReal 0 1))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun g => A ^ 2 * g ^ 2)
      ?_ ?_ hbound_int ?_
    · filter_upwards [self_mem_nhdsWithin] with q _
      exact (((continuous_tanh.comp (by fun_prop)).pow 2).div_const q).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with q (hq : 0 < q)
      filter_upwards with g
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hq]
      calc Real.tanh (A * Real.sqrt q * g) ^ 2 ≤ (A * Real.sqrt q * g) ^ 2 := tanh_sq_le_sq _
        _ = A ^ 2 * g ^ 2 * q := by rw [mul_pow, mul_pow, Real.sq_sqrt hq.le]; ring
    · filter_upwards [hne] with g hg
      exact tendsto_tanh_sq_div_ratio hA hg
  rw [htarget] at hconv
  refine hconv.congr' ?_
  filter_upwards with q
  rw [V, integral_div]

/-- For `A > 1`, `V_A` exceeds the diagonal near `0` (since `V_A(q)/q → A² > 1`),
supplying the exceed-diagonal hypothesis of `V_exists_unique_fixed`. -/
lemma V_exceeds_diagonal_of_one_lt {A : ℝ} (hA : 1 < A) :
    ∃ q ∈ Ioo (0 : ℝ) 1, q < V A q := by
  have hA0 : A ≠ 0 := (by linarith : (0 : ℝ) < A).ne'
  have hlt : (1 : ℝ) < A ^ 2 := by nlinarith
  have hev : ∀ᶠ q in 𝓝[>] (0 : ℝ), 1 < V A q / q :=
    (V_ratio_tendsto hA0).eventually (eventually_gt_nhds hlt)
  have hev2 : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hev3 : ∀ᶠ q in 𝓝[>] (0 : ℝ), (0 : ℝ) < q := by
    filter_upwards [self_mem_nhdsWithin] with q hq; exact hq
  obtain ⟨q, ⟨hq1, hq2⟩, hq3⟩ := ((hev.and hev2).and hev3).exists
  refine ⟨q, ⟨hq3, hq2⟩, ?_⟩
  rw [lt_div_iff₀ hq3, one_mul] at hq1
  exact hq1

/-- **Unconditional fixed point for `A > 1`** — the full `A>1` case of the paper's
`lem:gaussian-mean-field-concavity`: for `A > 1`, `V_A` has a unique positive fixed point,
with no exceed-diagonal hypothesis (it is now derived from `V_A'(0+) = A² > 1`). -/
theorem V_exists_unique_fixed_of_one_lt {A : ℝ} (hA : 1 < A) :
    ∃! q, q ∈ Ioo (0 : ℝ) 1 ∧ V A q = q := by
  obtain ⟨q₀, hq₀, hexceed⟩ := V_exceeds_diagonal_of_one_lt hA
  exact V_exists_unique_fixed ((by linarith : (0 : ℝ) < A).ne') hq₀ hexceed

/-- The ratio `V_A(q)/q` is strictly below its right-limit `A²` throughout `(0,1)`
(`A ≠ 0`): it is `StrictAntiOn` with right-limit `A²` at `0⁺`. Compare `q` with `q/2`. -/
lemma V_ratio_lt_sq {A : ℝ} (hA : A ≠ 0) {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    V A q / q < A ^ 2 := by
  have hq''0 : 0 < q / 2 := by linarith [hq.1]
  have hq''q : q / 2 < q := by linarith [hq.1]
  have hq''1 : q / 2 < 1 := lt_trans hq''q hq.2
  have hq''mem : q / 2 ∈ Ioo (0 : ℝ) 1 := ⟨hq''0, hq''1⟩
  have hle : V A (q / 2) / (q / 2) ≤ A ^ 2 := by
    refine ge_of_tendsto (V_ratio_tendsto hA) ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hq''0).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (zero_lt_one)).filter_mono nhdsWithin_le_nhds]
      with q' (hq'0 : 0 < q') (hq'lt : q' < q / 2) (hq'1 : q' < 1)
    exact le_of_lt (V_ratio_strictAntiOn hA ⟨hq'0, hq'1⟩ hq''mem hq'lt)
  have hlt : V A q / q < V A (q / 2) / (q / 2) :=
    V_ratio_strictAntiOn hA hq''mem ⟨hq.1, hq.2⟩ hq''q
  linarith

/-- `A ∈ (0,1]` ⇒ `V_A(q) < q` for all `q ∈ (0,1)`: `V_A(q)/q < A² ≤ 1`. -/
lemma V_lt_self_of_le_one {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) : V A q < q := by
  have hsq : A ^ 2 ≤ 1 := pow_le_one₀ hA0.le hA1
  have hr : V A q / q < 1 := lt_of_lt_of_le (V_ratio_lt_sq hA0.ne' hq) hsq
  rwa [div_lt_one hq.1] at hr

/-- **`A ≤ 1` ⇒ `0` is the only fixed point of `V_A` in `[0,1]`** (the `A≤1` case of the
paper's `lem:gaussian-mean-field-concavity`): `V_A(q) < q` on `(0,1)` (`V_lt_self_of_le_one`)
and `V_A(1) < 1` (`V_lt_one`) rule out any positive fixed point; `V_A(0) = 0` is the one. -/
theorem V_fixed_eq_zero_of_le_one {A : ℝ} (hA0 : 0 < A) (hA1 : A ≤ 1) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hfix : V A q = q) : q = 0 := by
  rcases eq_or_lt_of_le hq.1 with h | h
  · exact h.symm
  · exfalso
    rcases eq_or_lt_of_le hq.2 with h1 | h1
    · rw [h1] at hfix; linarith [V_lt_one A 1]
    · linarith [V_lt_self_of_le_one hA0 hA1 ⟨h, h1⟩]

/-! ### Deterministic orbit convergence `V_A^t(q) → q_*` (`A > 1`)

The convergence clause of `lem:gaussian-mean-field-concavity`: for `A > 1` every orbit of
`V_A` started in `(0,1)` converges to the unique positive fixed point `q_*`. The paper's
argument: `V_A` is increasing (`V_strictMonoOn`) and, relative to `q_*`, lies above the
diagonal below `q_*` and below it above `q_*` (the ratio `V_A(q)/q` is strictly antitone
and equals `1` at `q_*`). Hence each orbit is monotone and bounded, so it converges; its
limit is a fixed point (continuity), hence `q_*` by uniqueness. -/

/-- **Below the fixed point `V_A` exceeds the diagonal.** If `q_* ∈ (0,1)` is a fixed point
and `0 < q < q_*`, then `q < V_A(q)`, since the ratio `V_A(q)/q > V_A(q_*)/q_* = 1`. -/
lemma V_gt_self_of_lt_fixed {A : ℝ} (hA : A ≠ 0) {qstar : ℝ}
    (hstar : qstar ∈ Ioo (0 : ℝ) 1) (hfix : V A qstar = qstar) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hlt : q < qstar) : q < V A q := by
  have hratio : V A qstar / qstar < V A q / q := V_ratio_strictAntiOn hA hq hstar hlt
  rw [hfix, div_self hstar.1.ne', lt_div_iff₀ hq.1, one_mul] at hratio
  exact hratio

/-- **Above the fixed point `V_A` lies below the diagonal.** If `q_* ∈ (0,1)` is a fixed
point and `q_* < q < 1`, then `V_A(q) < q`, since the ratio `V_A(q)/q < V_A(q_*)/q_* = 1`. -/
lemma V_lt_self_of_gt_fixed {A : ℝ} (hA : A ≠ 0) {qstar : ℝ}
    (hstar : qstar ∈ Ioo (0 : ℝ) 1) (hfix : V A qstar = qstar) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) (hgt : qstar < q) : V A q < q := by
  have hratio : V A q / q < V A qstar / qstar := V_ratio_strictAntiOn hA hstar hq hgt
  rw [hfix, div_self hstar.1.ne', div_lt_one hq.1] at hratio
  exact hratio

/-- **Orbit convergence below the fixed point.** For `A > 1`, a positive fixed point
`q_* ∈ (0,1)`, and a start `0 < q ≤ q_*`, the orbit `V_A^t(q)` increases and stays in
`(0, q_*]` (`V_A` increasing; above the diagonal below `q_*`), so it converges to its
supremum; by continuity the limit is a fixed point in `(0,1)`, hence `q_*` by uniqueness. -/
theorem V_orbit_tendsto_of_le_fixed {A : ℝ} (hA : 1 < A) {qstar : ℝ}
    (hstar : qstar ∈ Ioo (0 : ℝ) 1) (hfix : V A qstar = qstar) {q : ℝ}
    (hq0 : 0 < q) (hqle : q ≤ qstar) :
    Tendsto (fun t => (V A)^[t] q) atTop (𝓝 qstar) := by
  have hA0 : A ≠ 0 := (by linarith : (0 : ℝ) < A).ne'
  set u : ℕ → ℝ := fun t => (V A)^[t] q with hu
  have hstar1 : qstar < 1 := hstar.2
  have hstarmem : qstar ∈ Icc (0 : ℝ) 1 := ⟨hstar.1.le, hstar.2.le⟩
  -- Invariant: the orbit stays in `(0, q_*]`.
  have hinv : ∀ t, 0 < u t ∧ u t ≤ qstar := by
    intro t
    induction t with
    | zero => exact ⟨hq0, hqle⟩
    | succ n ih =>
      obtain ⟨hpos, hle⟩ := ih
      have hmem : u n ∈ Icc (0 : ℝ) 1 := ⟨hpos.le, le_trans hle hstar1.le⟩
      have hsucc : u (n + 1) = V A (u n) := Function.iterate_succ_apply' (V A) n q
      refine ⟨?_, ?_⟩
      · rw [hsucc]
        have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
        have hstep := V_strictMonoOn hA0 h0mem hmem hpos
        rwa [V_zero] at hstep
      · rw [hsucc]
        have hstep := (V_strictMonoOn hA0).monotoneOn hmem hstarmem hle
        rwa [hfix] at hstep
  -- The orbit is monotone increasing (`V_A(x) ≥ x` on `(0, q_*]`).
  have hmono : Monotone u := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    obtain ⟨hpos, hle⟩ := hinv n
    have hsucc : u (n + 1) = V A (u n) := Function.iterate_succ_apply' (V A) n q
    rw [hsucc]
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (V_gt_self_of_lt_fixed hA0 hstar hfix ⟨hpos, lt_trans hlt hstar1⟩ hlt).le
    · rw [heq]; exact le_of_eq hfix.symm
  have hbdd : BddAbove (Set.range u) := ⟨qstar, by rintro _ ⟨t, rfl⟩; exact (hinv t).2⟩
  have htends : Tendsto u atTop (𝓝 (⨆ t, u t)) := tendsto_atTop_ciSup hmono hbdd
  have hLfix : V A (⨆ t, u t) = ⨆ t, u t :=
    isFixedPt_of_tendsto_iterate htends (V_continuous A).continuousAt
  have hu0 : u 0 = q := by simp [hu]
  have hq_le : q ≤ ⨆ t, u t := by rw [← hu0]; exact le_ciSup hbdd 0
  have hLpos : 0 < ⨆ t, u t := lt_of_lt_of_le hq0 hq_le
  have hLle : (⨆ t, u t) ≤ qstar := ciSup_le (fun t => (hinv t).2)
  have hLmem : (⨆ t, u t) ∈ Ioo (0 : ℝ) 1 := ⟨hLpos, lt_of_le_of_lt hLle hstar1⟩
  have heq : (⨆ t, u t) = qstar :=
    (V_exists_unique_fixed_of_one_lt hA).unique ⟨hLmem, hLfix⟩ ⟨hstar, hfix⟩
  rw [← heq]; exact htends

/-- **Orbit convergence above the fixed point.** For `A > 1`, a positive fixed point
`q_* ∈ (0,1)`, and a start `q_* ≤ q < 1`, the orbit `V_A^t(q)` decreases and stays in
`[q_*, 1)` (`V_A` increasing; below the diagonal above `q_*`), so it converges to its
infimum; by continuity the limit is a fixed point in `(0,1)`, hence `q_*` by uniqueness. -/
theorem V_orbit_tendsto_of_ge_fixed {A : ℝ} (hA : 1 < A) {qstar : ℝ}
    (hstar : qstar ∈ Ioo (0 : ℝ) 1) (hfix : V A qstar = qstar) {q : ℝ}
    (hq1 : q < 1) (hqge : qstar ≤ q) :
    Tendsto (fun t => (V A)^[t] q) atTop (𝓝 qstar) := by
  have hA0 : A ≠ 0 := (by linarith : (0 : ℝ) < A).ne'
  set u : ℕ → ℝ := fun t => (V A)^[t] q with hu
  have hstar0 : 0 < qstar := hstar.1
  have hstarmem : qstar ∈ Icc (0 : ℝ) 1 := ⟨hstar.1.le, hstar.2.le⟩
  -- Invariant: the orbit stays in `[q_*, 1)`.
  have hinv : ∀ t, qstar ≤ u t ∧ u t < 1 := by
    intro t
    induction t with
    | zero => exact ⟨hqge, hq1⟩
    | succ n ih =>
      obtain ⟨hge, hlt1⟩ := ih
      have hmem : u n ∈ Icc (0 : ℝ) 1 := ⟨le_trans hstar0.le hge, hlt1.le⟩
      have hsucc : u (n + 1) = V A (u n) := Function.iterate_succ_apply' (V A) n q
      refine ⟨?_, ?_⟩
      · rw [hsucc]
        have hstep := (V_strictMonoOn hA0).monotoneOn hstarmem hmem hge
        rwa [hfix] at hstep
      · rw [hsucc]; exact V_lt_one A (u n)
  -- The orbit is monotone decreasing (`V_A(x) ≤ x` on `[q_*, 1)`).
  have hanti : Antitone u := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    obtain ⟨hge, hlt1⟩ := hinv n
    have hsucc : u (n + 1) = V A (u n) := Function.iterate_succ_apply' (V A) n q
    rw [hsucc]
    rcases lt_or_eq_of_le hge with hlt | heq
    · exact (V_lt_self_of_gt_fixed hA0 hstar hfix ⟨lt_trans hstar0 hlt, hlt1⟩ hlt).le
    · rw [← heq]; exact le_of_eq hfix
  have hbdd : BddBelow (Set.range u) := ⟨qstar, by rintro _ ⟨t, rfl⟩; exact (hinv t).1⟩
  have htends : Tendsto u atTop (𝓝 (⨅ t, u t)) := tendsto_atTop_ciInf hanti hbdd
  have hLfix : V A (⨅ t, u t) = ⨅ t, u t :=
    isFixedPt_of_tendsto_iterate htends (V_continuous A).continuousAt
  have hu0 : u 0 = q := by simp [hu]
  have hL_le : (⨅ t, u t) ≤ q := by rw [← hu0]; exact ciInf_le hbdd 0
  have hL_ge : qstar ≤ ⨅ t, u t := le_ciInf (fun t => (hinv t).1)
  have hLmem : (⨅ t, u t) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le hstar0 hL_ge, lt_of_le_of_lt hL_le hq1⟩
  have heq : (⨅ t, u t) = qstar :=
    (V_exists_unique_fixed_of_one_lt hA).unique ⟨hLmem, hLfix⟩ ⟨hstar, hfix⟩
  rw [← heq]; exact htends

/-- **Deterministic orbit convergence** (convergence clause of the paper's
`lem:gaussian-mean-field-concavity`): for `A > 1`, every interior orbit `V_A^t(q)`
(`q ∈ (0,1)`) converges to the unique positive fixed point `q_*`. Splits on `q ≤ q_*`
vs `q_* ≤ q` into the two monotone cases. -/
theorem V_orbit_tendsto {A : ℝ} (hA : 1 < A) {qstar : ℝ}
    (hstar : qstar ∈ Ioo (0 : ℝ) 1) (hfix : V A qstar = qstar) {q : ℝ}
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun t => (V A)^[t] q) atTop (𝓝 qstar) := by
  rcases le_total q qstar with hle | hge
  · exact V_orbit_tendsto_of_le_fixed hA hstar hfix hq.1 hle
  · exact V_orbit_tendsto_of_ge_fixed hA hstar hfix hq.2 hge

/-- **Existence of the fixed point together with global interior convergence** for `A > 1`:
packages `V_exists_unique_fixed_of_one_lt` with `V_orbit_tendsto` — there is a fixed point
`q_* ∈ (0,1)` to which every interior orbit converges. -/
theorem exists_fixed_and_orbit_tendsto {A : ℝ} (hA : 1 < A) :
    ∃ qstar ∈ Ioo (0 : ℝ) 1, V A qstar = qstar ∧
      ∀ q ∈ Ioo (0 : ℝ) 1, Tendsto (fun t => (V A)^[t] q) atTop (𝓝 qstar) := by
  obtain ⟨qstar, ⟨hstar, hfix⟩, _⟩ := V_exists_unique_fixed_of_one_lt hA
  exact ⟨qstar, hstar, hfix, fun q hq => V_orbit_tendsto hA hstar hfix hq⟩

/-- **Orbit convergence from the half-open interval `(0,1]`** — the paper's full statement.
`V_A` maps `(0,1]` into the interior `(0,1)` (`0 < V_A(q)` for `q > 0`; `V_A(q) < 1`), so the
orbit from `t = 1` on is interior and converges by `V_orbit_tendsto`; a one-step shift
(`tendsto_add_atTop_iff_nat`) transfers convergence to the full orbit, covering `q = 1`. -/
theorem V_orbit_tendsto_Ioc {A : ℝ} (hA : 1 < A) {qstar : ℝ}
    (hstar : qstar ∈ Ioo (0 : ℝ) 1) (hfix : V A qstar = qstar) {q : ℝ}
    (hq : q ∈ Ioc (0 : ℝ) 1) :
    Tendsto (fun t => (V A)^[t] q) atTop (𝓝 qstar) := by
  have hA0 : A ≠ 0 := (by linarith : (0 : ℝ) < A).ne'
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hqmem : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2⟩
  have hVpos : 0 < V A q := by
    have hstep := V_strictMonoOn hA0 h0mem hqmem hq.1; rwa [V_zero] at hstep
  have hVmem : V A q ∈ Ioo (0 : ℝ) 1 := ⟨hVpos, V_lt_one A q⟩
  have htail : Tendsto (fun t => (V A)^[t] (V A q)) atTop (𝓝 qstar) :=
    V_orbit_tendsto hA hstar hfix hVmem
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa [Function.iterate_succ_apply] using htail

end AbsorptionCutoff
