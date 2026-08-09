/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingDecay

/-!
# Fixed-width coupling multiplier product bounds

This continuation module factors exponential moments of iid synchronous log
multipliers and proves uniform subproduct bounds through logarithmic horizons.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- Applying logarithm coordinatewise preserves mutual independence of the
synchronous discrepancy multipliers. -/
lemma iIndepFun_fixedWidthDiscrepancyLogMultiplier
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) :
    iIndepFun
      (fixedWidthDiscrepancyLogMultiplier hN ρ x0)
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hind :=
    (iIndepFun_fixedWidthDiscrepancyMultiplier A hN ρ x0).comp
      (fun _ ↦ Real.log) (fun _ ↦ Real.measurable_log)
  change iIndepFun
    (fun n ω ↦ Real.log
      (fixedWidthDiscrepancyMultiplier hN ρ x0 n ω))
    (fixedWidthMatrixGaussianMeasure A N)
  simpa only [Function.comp_def] using hind

/-- Every path log multiplier has the same distribution as the time-zero log
multiplier. -/
lemma identDistrib_fixedWidthDiscrepancyLogMultiplier_zero
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) :
    IdentDistrib
      (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n)
      (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
      (fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthMatrixGaussianMeasure A N) :=
  (identDistrib_fixedWidthDiscrepancyLogMultiplier hA hN ρ x0 n).trans
    (identDistrib_fixedWidthDiscrepancyLogMultiplier hA hN ρ x0 0).symm

/-- Log multipliers at arbitrary meshes, initial states, and times have the
same common Gaussian radial law. -/
lemma identDistrib_fixedWidthDiscrepancyLogMultiplier_cross
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ ρ' : ℝ) (x0 x0' : Fin N → ℝ) (n m : ℕ) :
    IdentDistrib
      (fixedWidthDiscrepancyLogMultiplier hN ρ x0 n)
      (fixedWidthDiscrepancyLogMultiplier hN ρ' x0' m)
      (fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthMatrixGaussianMeasure A N) :=
  (identDistrib_fixedWidthDiscrepancyLogMultiplier hA hN ρ x0 n).trans
    (identDistrib_fixedWidthDiscrepancyLogMultiplier hA hN ρ' x0' m).symm

/-- Fixed-width subcriticality selects one positive decaying exponential
moment that works simultaneously for every rounding mesh. -/
lemma exists_pos_uniform_integrable_mgf_fixedWidthDiscrepancyLogMultiplier_lt_one
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) :
    ∃ s : ℝ, 0 < s ∧
      ∀ ρ : ℝ,
        Integrable (fun ω ↦ Real.exp
          (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
          (fixedWidthMatrixGaussianMeasure A N) ∧
        mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
          (fixedWidthMatrixGaussianMeasure A N) s < 1 := by
  obtain ⟨s, hs, hint0, hq0⟩ :=
    exists_pos_integrable_mgf_fixedWidthDiscrepancyLogMultiplier_lt_one
      hA hN hsub 0 x0 0
  refine ⟨s, hs, ?_⟩
  intro ρ
  have hident :=
    identDistrib_fixedWidthDiscrepancyLogMultiplier_cross
      hA hN ρ 0 x0 x0 0 0
  have hidentExp := hident.comp
    (u := fun z : ℝ ↦ Real.exp (s * z)) (by fun_prop)
  have hint := hidentExp.integrable_iff.mpr hint0
  have hmgf :=
    mgf_congr_of_identDistrib
      (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
      (fixedWidthDiscrepancyLogMultiplier hN 0 x0 0)
      hident s
  refine ⟨hint, ?_⟩
  rw [hmgf]
  exact hq0

/-- One integrable exponential moment at time zero propagates to the
exponential of every finite initial sum of path log multipliers. -/
lemma integrable_exp_mul_sum_fixedWidthDiscrepancyLogMultiplier
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) (s : ℝ)
    (hint0 : Integrable (fun ω ↦ Real.exp
      (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
      (fixedWidthMatrixGaussianMeasure A N)) :
    Integrable (fun ω ↦ Real.exp
      (s * (∑ j ∈ Finset.range n,
        fixedWidthDiscrepancyLogMultiplier hN ρ x0 j ω)))
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hfun :
      (fun ω ↦ Real.exp (s * ∑ j ∈ Finset.range n,
        fixedWidthDiscrepancyLogMultiplier hN ρ x0 j ω)) =
        (fun ω ↦ Real.exp (s * (∑ j ∈ Finset.range n,
          fixedWidthDiscrepancyLogMultiplier hN ρ x0 j) ω)) := by
    funext ω
    simp
  rw [hfun]
  refine (iIndepFun_fixedWidthDiscrepancyLogMultiplier A hN ρ x0)
    |>.integrable_exp_mul_sum
      (measurable_fixedWidthDiscrepancyLogMultiplier hN ρ x0) ?_
  intro j _
  have hident :=
    (identDistrib_fixedWidthDiscrepancyLogMultiplier_zero hA hN ρ x0 j).comp
      (u := fun z : ℝ ↦ Real.exp (s * z)) (by fun_prop)
  exact hident.integrable_iff.mpr hint0

/-- Chernoff bound for an initial block of iid path log multipliers, with the
common time-zero mgf raised to the block length. -/
lemma measureReal_sum_fixedWidthDiscrepancyLogMultiplier_ge_le
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (n : ℕ) (s a : ℝ)
    (hs : 0 ≤ s)
    (hint0 : Integrable (fun ω ↦ Real.exp
      (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
      (fixedWidthMatrixGaussianMeasure A N)) :
    (fixedWidthMatrixGaussianMeasure A N).real
      {ω | a ≤ ∑ j ∈ Finset.range n,
        fixedWidthDiscrepancyLogMultiplier hN ρ x0 j ω} ≤
      Real.exp (-s * a) *
        mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
          (fixedWidthMatrixGaussianMeasure A N) s ^ n := by
  exact measure_sum_ge_le_exp_mul_mgf_pow
    (fixedWidthMatrixGaussianMeasure A N)
    (fixedWidthDiscrepancyLogMultiplier hN ρ x0) n s a hs
    (measurable_fixedWidthDiscrepancyLogMultiplier hN ρ x0)
    (iIndepFun_fixedWidthDiscrepancyLogMultiplier A hN ρ x0)
    (identDistrib_fixedWidthDiscrepancyLogMultiplier_zero hA hN ρ x0)
    (integrable_exp_mul_sum_fixedWidthDiscrepancyLogMultiplier
      hA hN ρ x0 n s hint0)

/-- A time-zero exponential moment propagates to every finite shifted block of
path log multipliers. -/
lemma integrable_exp_mul_shiftedSum_fixedWidthDiscrepancyLogMultiplier
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (i n : ℕ) (s : ℝ)
    (hint0 : Integrable (fun ω ↦ Real.exp
      (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
      (fixedWidthMatrixGaussianMeasure A N)) :
    Integrable (fun ω ↦ Real.exp
      (s * (∑ j ∈ Finset.range n,
        fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j) ω)))
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hshift : iIndepFun
      (fun j ↦ fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j))
      (fixedWidthMatrixGaussianMeasure A N) :=
    (iIndepFun_fixedWidthDiscrepancyLogMultiplier A hN ρ x0).precomp
      (fun _ _ h ↦ Nat.add_left_cancel h)
  have hfun :
      (fun ω ↦ Real.exp (s * ∑ j ∈ Finset.range n,
        fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j) ω)) =
        (fun ω ↦ Real.exp (s * (∑ j ∈ Finset.range n,
          fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j)) ω)) := by
    funext ω
    simp
  rw [hfun]
  refine hshift.integrable_exp_mul_sum
    (fun j ↦
      measurable_fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j)) ?_
  intro j _
  have hident :=
    (identDistrib_fixedWidthDiscrepancyLogMultiplier_zero
      hA hN ρ x0 (i + j)).comp
      (u := fun z : ℝ ↦ Real.exp (s * z)) (by fun_prop)
  exact hident.integrable_iff.mpr hint0

/-- Chernoff bound for every finite shifted block of iid path log multipliers,
expressed with the common time-zero mgf. -/
lemma measureReal_shiftedSum_fixedWidthDiscrepancyLogMultiplier_ge_le
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (i n : ℕ) (s a : ℝ)
    (hs : 0 ≤ s)
    (hint0 : Integrable (fun ω ↦ Real.exp
      (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
      (fixedWidthMatrixGaussianMeasure A N)) :
    (fixedWidthMatrixGaussianMeasure A N).real
      {ω | a ≤ ∑ j ∈ Finset.range n,
        fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j) ω} ≤
      Real.exp (-s * a) *
        mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
          (fixedWidthMatrixGaussianMeasure A N) s ^ n := by
  let X : ℕ → fixedWidthMatrixSampleSpace N → ℝ :=
    fun j ↦ fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j)
  have hind : iIndepFun X (fixedWidthMatrixGaussianMeasure A N) := by
    dsimp [X]
    exact (iIndepFun_fixedWidthDiscrepancyLogMultiplier A hN ρ x0).precomp
      (fun _ _ h ↦ Nat.add_left_cancel h)
  have hident : ∀ j, IdentDistrib (X j) (X 0)
      (fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthMatrixGaussianMeasure A N) := by
    intro j
    dsimp [X]
    simpa only [Nat.add_zero] using
      (identDistrib_fixedWidthDiscrepancyLogMultiplier_zero
        hA hN ρ x0 (i + j)).trans
        (identDistrib_fixedWidthDiscrepancyLogMultiplier_zero
          hA hN ρ x0 i).symm
  have hbound := measure_sum_ge_le_exp_mul_mgf_pow
    (fixedWidthMatrixGaussianMeasure A N) X n s a hs
    (fun j ↦
      measurable_fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j))
    hind hident
    (integrable_exp_mul_shiftedSum_fixedWidthDiscrepancyLogMultiplier
      hA hN ρ x0 i n s hint0)
  have hmgf :
      mgf (X 0) (fixedWidthMatrixGaussianMeasure A N) s =
        mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
          (fixedWidthMatrixGaussianMeasure A N) s := by
    dsimp [X]
    simpa only [Nat.add_zero] using
      mgf_congr_of_identDistrib
        (fixedWidthDiscrepancyLogMultiplier hN ρ x0 i)
        (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
        (identDistrib_fixedWidthDiscrepancyLogMultiplier_zero
          hA hN ρ x0 i) s
  simpa only [X, hmgf] using hbound

/-- A nonnegative multiplier block product is bounded by the exponential of
the corresponding log-multiplier sum, including on zero-multiplier paths. -/
lemma prod_fixedWidthDiscrepancyMultiplier_le_exp_sum_logMultiplier
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ)
    (i n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    (∏ j ∈ Finset.range n,
      fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω) ≤
      Real.exp (∑ j ∈ Finset.range n,
        fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j) ω) := by
  calc
    (∏ j ∈ Finset.range n,
        fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω) ≤
      ∏ j ∈ Finset.range n,
        Real.exp (Real.log
          (fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω)) := by
        apply Finset.prod_le_prod
        · intro j _
          unfold fixedWidthDiscrepancyMultiplier gaussianEuclideanNorm
          positivity
        · intro j _
          exact Real.le_exp_log _
    _ = Real.exp (∑ j ∈ Finset.range n,
        fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j) ω) := by
      rw [Real.exp_sum]
      rfl

/-- Chernoff bound for a genuine shifted multiplier product at an exponential
threshold. -/
lemma measureReal_prod_fixedWidthDiscrepancyMultiplier_gt_exp_le
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (i n : ℕ) (s a : ℝ)
    (hs : 0 ≤ s)
    (hint0 : Integrable (fun ω ↦ Real.exp
      (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
      (fixedWidthMatrixGaussianMeasure A N)) :
    (fixedWidthMatrixGaussianMeasure A N).real
      {ω | Real.exp a < ∏ j ∈ Finset.range n,
        fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω} ≤
      Real.exp (-s * a) *
        mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
          (fixedWidthMatrixGaussianMeasure A N) s ^ n := by
  calc
    (fixedWidthMatrixGaussianMeasure A N).real
        {ω | Real.exp a < ∏ j ∈ Finset.range n,
          fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω} ≤
      (fixedWidthMatrixGaussianMeasure A N).real
        {ω | a ≤ ∑ j ∈ Finset.range n,
          fixedWidthDiscrepancyLogMultiplier hN ρ x0 (i + j) ω} := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro ω hω
        exact (Real.exp_lt_exp.mp
          (hω.trans_le
            (prod_fixedWidthDiscrepancyMultiplier_le_exp_sum_logMultiplier
              hN ρ x0 i n ω))).le
    _ ≤ _ :=
      measureReal_shiftedSum_fixedWidthDiscrepancyLogMultiplier_ge_le
        hA hN ρ x0 i n s a hs hint0

/-- Event that some multiplier subproduct contained in the horizon
`{0, ..., T}` exceeds the exponential threshold `exp a`. -/
noncomputable def fixedWidthMultiplierSubproductBadSet
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ)
    (T : ℕ) (a : ℝ) : Set (fixedWidthMatrixSampleSpace N) :=
  ⋃ i ∈ Finset.range (T + 1),
    ⋃ n ∈ Finset.range (T - i + 1),
      {ω | Real.exp a < ∏ j ∈ Finset.range n,
        fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω}

/-- Finite union bound for all multiplier subproducts through time `T`. -/
lemma measureReal_fixedWidthMultiplierSubproductBadSet_le_sum
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (T : ℕ) (s a : ℝ)
    (hs : 0 ≤ s)
    (hint0 : Integrable (fun ω ↦ Real.exp
      (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
      (fixedWidthMatrixGaussianMeasure A N)) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthMultiplierSubproductBadSet hN ρ x0 T a) ≤
      ∑ i ∈ Finset.range (T + 1),
        ∑ n ∈ Finset.range (T - i + 1),
          Real.exp (-s * a) *
            mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
              (fixedWidthMatrixGaussianMeasure A N) s ^ n := by
  rw [fixedWidthMultiplierSubproductBadSet]
  calc
    (fixedWidthMatrixGaussianMeasure A N).real
        (⋃ i ∈ Finset.range (T + 1),
          ⋃ n ∈ Finset.range (T - i + 1),
            {ω | Real.exp a < ∏ j ∈ Finset.range n,
              fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω}) ≤
      ∑ i ∈ Finset.range (T + 1),
        (fixedWidthMatrixGaussianMeasure A N).real
          (⋃ n ∈ Finset.range (T - i + 1),
            {ω | Real.exp a < ∏ j ∈ Finset.range n,
              fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω}) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.range (T + 1),
        ∑ n ∈ Finset.range (T - i + 1),
          (fixedWidthMatrixGaussianMeasure A N).real
            {ω | Real.exp a < ∏ j ∈ Finset.range n,
              fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω} := by
      apply Finset.sum_le_sum
      intro i _
      exact measureReal_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro n _
      exact measureReal_prod_fixedWidthDiscrepancyMultiplier_gt_exp_le
        hA hN ρ x0 i n s a hs hint0

/-- Every finite initial geometric sum with ratio in `[0,1)` is bounded by the
full geometric-series mass. -/
lemma sum_range_pow_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (m : ℕ) :
    ∑ n ∈ Finset.range m, q ^ n ≤ (1 - q)⁻¹ := by
  have hsum : Summable (fun n : ℕ ↦ q ^ n) :=
    summable_geometric_of_norm_lt_one
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
  rw [← tsum_geometric_of_lt_one hq0 hq1]
  exact hsum.sum_le_tsum (Finset.range m)
    (fun n _ ↦ pow_nonneg hq0 n)

/-- The probability that any multiplier subproduct through time `T` exceeds
`exp a` is at most `(T+1) exp(-s a) / (1-q)`, where `q` is the common mgf. -/
lemma measureReal_fixedWidthMultiplierSubproductBadSet_le
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (T : ℕ) (s a : ℝ)
    (hs : 0 ≤ s)
    (hint0 : Integrable (fun ω ↦ Real.exp
      (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
      (fixedWidthMatrixGaussianMeasure A N))
    (hq1 : mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
      (fixedWidthMatrixGaussianMeasure A N) s < 1) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthMultiplierSubproductBadSet hN ρ x0 T a) ≤
      (T + 1 : ℕ) * (Real.exp (-s * a) *
        (1 - mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
          (fixedWidthMatrixGaussianMeasure A N) s)⁻¹) := by
  let q := mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
    (fixedWidthMatrixGaussianMeasure A N) s
  have hq0 : 0 ≤ q := mgf_nonneg
  calc
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthMultiplierSubproductBadSet hN ρ x0 T a) ≤
      ∑ i ∈ Finset.range (T + 1),
        ∑ n ∈ Finset.range (T - i + 1),
          Real.exp (-s * a) * q ^ n := by
      simpa only [q] using
        measureReal_fixedWidthMultiplierSubproductBadSet_le_sum
          hA hN ρ x0 T s a hs hint0
    _ = ∑ i ∈ Finset.range (T + 1),
        Real.exp (-s * a) *
          (∑ n ∈ Finset.range (T - i + 1), q ^ n) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ ∑ _i ∈ Finset.range (T + 1),
        Real.exp (-s * a) * (1 - q)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (sum_range_pow_le_inv_one_sub hq0 hq1 (T - i + 1))
        (Real.exp_pos _).le
    _ = (T + 1 : ℕ) *
        (Real.exp (-s * a) * (1 - q)⁻¹) := by
      simp
    _ = _ := by rfl

/-- Fixed-width subcriticality selects one positive exponential parameter for
which the finite-horizon subproduct bound holds at every horizon and threshold. -/
lemma exists_pos_fixedWidthMultiplierSubproductBadSet_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (ρ : ℝ) (x0 : Fin N → ℝ) :
    ∃ s : ℝ, 0 < s ∧
      Integrable (fun ω ↦ Real.exp
        (s * fixedWidthDiscrepancyLogMultiplier hN ρ x0 0 ω))
        (fixedWidthMatrixGaussianMeasure A N) ∧
      mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
        (fixedWidthMatrixGaussianMeasure A N) s < 1 ∧
      ∀ T : ℕ, ∀ a : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthMultiplierSubproductBadSet hN ρ x0 T a) ≤
          (T + 1 : ℕ) * (Real.exp (-s * a) *
            (1 - mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
              (fixedWidthMatrixGaussianMeasure A N) s)⁻¹) := by
  obtain ⟨s, hs, hint, hq⟩ :=
    exists_pos_integrable_mgf_fixedWidthDiscrepancyLogMultiplier_lt_one
      hA hN hsub ρ x0 0
  exact ⟨s, hs, hint, hq, fun T a ↦
    measureReal_fixedWidthMultiplierSubproductBadSet_le
      hA hN ρ x0 T s a hs.le hint hq⟩

/-- The selected exponential parameter and one common mgf value give the same
finite-horizon subproduct bound simultaneously for every rounding mesh. -/
lemma exists_pos_uniform_fixedWidthMultiplierSubproductBadSet_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) :
    ∃ s : ℝ, 0 < s ∧ ∃ q : ℝ, q < 1 ∧
      ∀ ρ : ℝ, ∀ T : ℕ, ∀ a : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthMultiplierSubproductBadSet hN ρ x0 T a) ≤
          (T + 1 : ℕ) * (Real.exp (-s * a) * (1 - q)⁻¹) := by
  obtain ⟨s, hs, hall⟩ :=
    exists_pos_uniform_integrable_mgf_fixedWidthDiscrepancyLogMultiplier_lt_one
      hA hN hsub x0
  let q := mgf (fixedWidthDiscrepancyLogMultiplier hN 0 x0 0)
    (fixedWidthMatrixGaussianMeasure A N) s
  have hq : q < 1 := (hall 0).2
  refine ⟨s, hs, q, hq, ?_⟩
  intro ρ T a
  have hident :=
    identDistrib_fixedWidthDiscrepancyLogMultiplier_cross
      hA hN ρ 0 x0 x0 0 0
  have hqeq :=
    mgf_congr_of_identDistrib
      (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
      (fixedWidthDiscrepancyLogMultiplier hN 0 x0 0)
      hident s
  have hbound := measureReal_fixedWidthMultiplierSubproductBadSet_le
    hA hN ρ x0 T s a hs.le (hall ρ).1 (hall ρ).2
  simpa only [q, hqeq] using hbound

/-- The paper's synchronous-comparison horizon on logarithmic scale `L`. -/
noncomputable def fixedWidthCouplingHorizon (C0 L : ℝ) : ℕ :=
  ⌊C0 * L⌋₊

/-- Logarithm of the paper's polylogarithmic multiplier threshold. -/
noncomputable def fixedWidthSubproductLogThreshold (p L : ℝ) : ℝ :=
  p * Real.log L

/-- If `s * p > 1`, the union-bound envelope at logarithmic horizon and
polylogarithmic threshold vanishes as the logarithmic scale tends to infinity. -/
lemma tendsto_fixedWidthSubproductLogEnvelope_zero
    (C0 s p c : ℝ) (hC0 : 0 ≤ C0) (hp : 1 < s * p) :
    Tendsto
      (fun L : ℝ =>
        ((fixedWidthCouplingHorizon C0 L + 1 : ℕ) : ℝ) *
          (Real.exp (-s * fixedWidthSubproductLogThreshold p L) * c))
      atTop (𝓝 0) := by
  change Tendsto
    (fun L : ℝ =>
      (((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ) *
        (Real.exp (-s * (p * Real.log L)) * c)))
    atTop (𝓝 0)
  have hratio0 :
      Tendsto (fun L : ℝ => (⌊C0 * L⌋₊ : ℝ) / L) atTop (𝓝 C0) :=
    tendsto_nat_floor_mul_div_atTop hC0
  have hratio :
      Tendsto
        (fun L : ℝ => (((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ) / L))
        atTop (𝓝 C0) := by
    convert hratio0.add tendsto_inv_atTop_zero using 1
    · ext L
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    · simp
  have hy : 0 < s * p - 1 := by linarith
  have heq :
      (fun L : ℝ => L * Real.exp (-s * (p * Real.log L))) =ᶠ[atTop]
        (fun L : ℝ => L ^ (-(s * p - 1))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [Real.rpow_def_of_pos hL]
    calc
      L * Real.exp (-s * (p * Real.log L)) =
          Real.exp (Real.log L) * Real.exp (-s * (p * Real.log L)) := by
            rw [Real.exp_log hL]
      _ = Real.exp (Real.log L + -s * (p * Real.log L)) := by
            rw [Real.exp_add]
      _ = Real.exp (Real.log L * (-(s * p - 1))) := by
            congr 1
            ring
  have hdecay :
      Tendsto
        (fun L : ℝ => L * Real.exp (-s * (p * Real.log L)))
        atTop (𝓝 0) := by
    rw [Filter.tendsto_congr' heq]
    exact tendsto_rpow_neg_atTop hy
  have hprod :
      Tendsto
        (fun L : ℝ =>
          ((((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ) / L) *
            (L * Real.exp (-s * (p * Real.log L)))) * c)
        atTop (𝓝 0) := by
    simpa using (hratio.mul hdecay).mul_const c
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  field_simp [hL.ne']

/-- Under fixed-width subcriticality, one polylogarithmic threshold exponent
makes every multiplier subproduct through logarithmic time small in probability. -/
lemma exists_pos_tendsto_measureReal_fixedWidthMultiplierSubproductBadSet_zero
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (ρ : ℝ) (x0 : Fin N → ℝ) (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∃ p : ℝ, 0 < p ∧
      Tendsto
        (fun L : ℝ =>
          (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthMultiplierSubproductBadSet hN ρ x0
              (fixedWidthCouplingHorizon C0 L)
              (fixedWidthSubproductLogThreshold p L)))
        atTop (𝓝 0) := by
  obtain ⟨s, hs, _hint, hq, hbound⟩ :=
    exists_pos_fixedWidthMultiplierSubproductBadSet_bound
      hA hN hsub ρ x0
  refine ⟨2 / s, div_pos (by norm_num) hs, ?_⟩
  have hsp : 1 < s * (2 / s) := by
    field_simp [hs.ne']
    norm_num
  have hupper :=
    tendsto_fixedWidthSubproductLogEnvelope_zero
      C0 s (2 / s)
        (1 - mgf (fixedWidthDiscrepancyLogMultiplier hN ρ x0 0)
          (fixedWidthMatrixGaussianMeasure A N) s)⁻¹
      hC0 hsp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun _L ↦ measureReal_nonneg)
    (fun L ↦ hbound
      (fixedWidthCouplingHorizon C0 L)
      (fixedWidthSubproductLogThreshold (2 / s) L))

/-- The logarithmic-horizon subproduct probability tends to zero along any
choice of rounding mesh depending on the logarithmic scale. -/
lemma exists_pos_tendsto_measureReal_fixedWidthMultiplierSubproductBadSet_zero_along
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (mesh : ℝ → ℝ) :
    ∃ p : ℝ, 0 < p ∧
      Tendsto
        (fun L : ℝ =>
          (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthMultiplierSubproductBadSet hN (mesh L) x0
              (fixedWidthCouplingHorizon C0 L)
              (fixedWidthSubproductLogThreshold p L)))
        atTop (𝓝 0) := by
  obtain ⟨s, hs, q, hq, hbound⟩ :=
    exists_pos_uniform_fixedWidthMultiplierSubproductBadSet_bound
      hA hN hsub x0
  refine ⟨2 / s, div_pos (by norm_num) hs, ?_⟩
  have hsp : 1 < s * (2 / s) := by
    field_simp [hs.ne']
    norm_num
  have hupper :=
    tendsto_fixedWidthSubproductLogEnvelope_zero
      C0 s (2 / s) (1 - q)⁻¹ hC0 hsp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun _L ↦ measureReal_nonneg)
    (fun L ↦ hbound (mesh L)
      (fixedWidthCouplingHorizon C0 L)
      (fixedWidthSubproductLogThreshold (2 / s) L))

/-- Eventually, the fixed dimension factor and the floored logarithmic horizon
cost at most two additional powers of the logarithmic scale. -/
lemma eventually_fixedWidthCouplingAffinePrefactor_le
    (N : ℕ) (C0 p0 : ℝ) (hC0 : 0 ≤ C0) :
    ∀ᶠ L : ℝ in atTop,
      (Real.sqrt N / 2) *
          (((fixedWidthCouplingHorizon C0 L + 1 : ℕ) : ℝ) *
            Real.exp (fixedWidthSubproductLogThreshold p0 L)) ≤
        Real.exp (fixedWidthSubproductLogThreshold (p0 + 2) L) := by
  change ∀ᶠ L : ℝ in atTop,
    (Real.sqrt N / 2) *
        (((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ) *
          Real.exp (p0 * Real.log L)) ≤
      Real.exp ((p0 + 2) * Real.log L)
  let b := Real.sqrt N / 2
  filter_upwards
    [eventually_gt_atTop (max 1 (b * (C0 + 1)))] with L hL
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL.le
  have hLb : b * (C0 + 1) ≤ L :=
    (le_max_right _ _).trans hL.le
  have hfloor : (⌊C0 * L⌋₊ : ℝ) ≤ C0 * L :=
    Nat.floor_le (mul_nonneg hC0 (by positivity))
  have hhorizon :
      (((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ)) ≤ (C0 + 1) * L := by
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      (⌊C0 * L⌋₊ : ℝ) + 1 ≤ C0 * L + 1 :=
        add_le_add hfloor le_rfl
      _ ≤ (C0 + 1) * L := by nlinarith
  have hb : 0 ≤ b :=
    div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hcoef :
      b * (((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ)) ≤ L ^ 2 := by
    calc
      b * (((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ)) ≤ b * ((C0 + 1) * L) :=
        mul_le_mul_of_nonneg_left hhorizon hb
      _ ≤ L * L := by nlinarith
      _ = L ^ 2 := by ring
  change b *
      ((((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ) *
        Real.exp (p0 * Real.log L))) ≤
    Real.exp ((p0 + 2) * Real.log L)
  calc
    b * ((((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ) *
        Real.exp (p0 * Real.log L))) =
        (b * (((⌊C0 * L⌋₊ + 1 : ℕ) : ℝ)) *
          Real.exp (p0 * Real.log L)) := by ring
    _ ≤ L ^ 2 * Real.exp (p0 * Real.log L) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = Real.exp ((p0 + 2) * Real.log L) := by
      have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL1
      rw [show L ^ 2 = Real.exp (2 * Real.log L) by
        calc
          L ^ 2 = (Real.exp (Real.log L)) ^ 2 := by
            rw [Real.exp_log hLpos]
          _ = Real.exp (2 * Real.log L) := by
            simpa using (Real.exp_nat_mul (Real.log L) 2).symm
        , ← Real.exp_add]
      congr 1
      ring

/-- Adding one affine-recursion step appends the common terminal multiplier to
all previous subproducts and adds the empty terminal subproduct. -/
lemma subproductSum_succ (M : ℕ → ℝ) (t : ℕ) :
    (∑ i ∈ Finset.range (t + 2),
      ∏ j ∈ Finset.range (t + 1 - i), M (i + j)) =
      M t * (∑ i ∈ Finset.range (t + 1),
        ∏ j ∈ Finset.range (t - i), M (i + j)) + 1 := by
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, Finset.prod_range_zero]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hit : i ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hsub : t + 1 - i = (t - i) + 1 := by omega
  rw [hsub, Finset.prod_range_succ]
  have hadd : i + (t - i) = t := Nat.add_sub_of_le hit
  rw [hadd]
  ring

/-- A scalar affine recursion with nonnegative multipliers is bounded by the
sum of all multiplier subproducts ending at the current time. -/
lemma le_mul_subproductSum_of_affine_recursion
    (u M : ℕ → ℝ) (b : ℝ) (hM : ∀ n, 0 ≤ M n)
    (hu0 : u 0 ≤ b)
    (hrec : ∀ n, u (n + 1) ≤ M n * u n + b) :
    ∀ t : ℕ, u t ≤ b * (∑ i ∈ Finset.range (t + 1),
      ∏ j ∈ Finset.range (t - i), M (i + j)) := by
  intro t
  induction t with
  | zero =>
      simpa using hu0
  | succ t iht =>
      calc
        u (t + 1) ≤ M t * u t + b := hrec t
        _ ≤ M t * (b * (∑ i ∈ Finset.range (t + 1),
            ∏ j ∈ Finset.range (t - i), M (i + j))) + b :=
          add_le_add (mul_le_mul_of_nonneg_left iht (hM t)) le_rfl
        _ = b * (∑ i ∈ Finset.range (t + 2),
            ∏ j ∈ Finset.range (t + 1 - i), M (i + j)) := by
          rw [subproductSum_succ]
          ring

/-- The synchronous rounded/unrounded discrepancy is bounded pathwise by one
rounding contribution times the sum of the corresponding multiplier
subproducts. -/
lemma fixedWidthVectorError_le_subproductSum
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (ω : fixedWidthMatrixSampleSpace N) (t : ℕ) :
    fixedWidthVectorError ρ N x0 t ω ≤
      (Real.sqrt N * (ρ / 2)) *
        (∑ i ∈ Finset.range (t + 1),
          ∏ j ∈ Finset.range (t - i),
            fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω) := by
  refine le_mul_subproductSum_of_affine_recursion
    (fun n ↦ fixedWidthVectorError ρ N x0 n ω)
    (fun n ↦ fixedWidthDiscrepancyMultiplier hN ρ x0 n ω)
    (Real.sqrt N * (ρ / 2)) ?_ ?_ ?_ t
  · intro n
    unfold fixedWidthDiscrepancyMultiplier gaussianEuclideanNorm
    exact Real.sqrt_nonneg _
  · exact fixedWidthVectorError_zero_le hρ N x0 ω
  · exact fun n ↦ fixedWidthVectorError_succ_le hρ hN x0 n ω

/-- Off the multiplier-subproduct bad event, the accumulated synchronous error
through time `T` is bounded by one rounding contribution times `(t+1) exp a`. -/
lemma fixedWidthVectorError_le_of_not_mem_subproductBadSet
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (T : ℕ) (a : ℝ)
    (ω : fixedWidthMatrixSampleSpace N)
    (hω : ω ∉ fixedWidthMultiplierSubproductBadSet hN ρ x0 T a)
    {t : ℕ} (ht : t ≤ T) :
    fixedWidthVectorError ρ N x0 t ω ≤
      (Real.sqrt N * (ρ / 2)) * ((t + 1 : ℕ) * Real.exp a) := by
  have hterm : ∀ i ∈ Finset.range (t + 1),
      (∏ j ∈ Finset.range (t - i),
        fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω) ≤
        Real.exp a := by
    intro i hi
    have hit : i ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hiT : i ∈ Finset.range (T + 1) := by
      rw [Finset.mem_range]
      omega
    have hnT : t - i ∈ Finset.range (T - i + 1) := by
      rw [Finset.mem_range]
      omega
    rw [fixedWidthMultiplierSubproductBadSet] at hω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hω
    exact le_of_not_gt (hω i hiT (t - i) hnT)
  have hsum :
      (∑ i ∈ Finset.range (t + 1),
        ∏ j ∈ Finset.range (t - i),
          fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω) ≤
        (t + 1 : ℕ) * Real.exp a := by
    calc
      (∑ i ∈ Finset.range (t + 1),
        ∏ j ∈ Finset.range (t - i),
          fixedWidthDiscrepancyMultiplier hN ρ x0 (i + j) ω) ≤
          ∑ _i ∈ Finset.range (t + 1), Real.exp a :=
        Finset.sum_le_sum hterm
      _ = (t + 1 : ℕ) * Real.exp a := by simp
  exact (fixedWidthVectorError_le_subproductSum hρ hN x0 ω t).trans
    (mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hρ.le (by norm_num))))

/-- Event that the synchronous rounded/unrounded discrepancy exceeds `R` at
some time through the finite horizon `T`. -/
noncomputable def fixedWidthCouplingErrorBadSet
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (T : ℕ) (R : ℝ) :
    Set (fixedWidthMatrixSampleSpace N) :=
  ⋃ t ∈ Finset.range (T + 1),
    {ω | R < fixedWidthVectorError ρ N x0 t ω}

/-- Raising the discrepancy threshold decreases the synchronous-error bad
event. -/
lemma fixedWidthCouplingErrorBadSet_mono
    (ρ : ℝ) (N : ℕ) (x0 : Fin N → ℝ) (T : ℕ)
    {R R' : ℝ} (hRR' : R ≤ R') :
    fixedWidthCouplingErrorBadSet ρ N x0 T R' ⊆
      fixedWidthCouplingErrorBadSet ρ N x0 T R := by
  intro ω hω
  rw [fixedWidthCouplingErrorBadSet] at hω ⊢
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hω ⊢
  obtain ⟨t, ht, herr⟩ := hω
  exact ⟨t, ht, hRR'.trans_lt herr⟩

/-- The synchronous-error event at the accumulated affine threshold is
contained in the corresponding multiplier-subproduct bad event. -/
lemma fixedWidthCouplingErrorBadSet_subset_subproductBadSet
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (T : ℕ) (a : ℝ) :
    fixedWidthCouplingErrorBadSet ρ N x0 T
        ((Real.sqrt N * (ρ / 2)) * ((T + 1 : ℕ) * Real.exp a)) ⊆
      fixedWidthMultiplierSubproductBadSet hN ρ x0 T a := by
  intro ω hω
  rw [fixedWidthCouplingErrorBadSet] at hω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hω
  obtain ⟨t, ht, herr⟩ := hω
  by_contra hgood
  have htT : t ≤ T := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
  have hb : 0 ≤ Real.sqrt N * (ρ / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hρ.le (by norm_num))
  have htime : ((t + 1 : ℕ) : ℝ) * Real.exp a ≤
      ((T + 1 : ℕ) : ℝ) * Real.exp a := by
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Nat.succ_le_succ htT)) (Real.exp_pos _).le
  exact (not_lt_of_ge
    ((fixedWidthVectorError_le_of_not_mem_subproductBadSet
        hρ hN x0 T a ω hgood htT).trans
      (mul_le_mul_of_nonneg_left htime hb))) herr

/-- Hence the probability of excessive synchronous error is at most the
probability of the multiplier-subproduct bad event. -/
lemma measureReal_fixedWidthCouplingErrorBadSet_le_subproductBadSet
    {A ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (x0 : Fin N → ℝ) (T : ℕ) (a : ℝ) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthCouplingErrorBadSet ρ N x0 T
          ((Real.sqrt N * (ρ / 2)) * ((T + 1 : ℕ) * Real.exp a))) ≤
      (fixedWidthMatrixGaussianMeasure A N).real
        (fixedWidthMultiplierSubproductBadSet hN ρ x0 T a) :=
  measureReal_mono
    (fixedWidthCouplingErrorBadSet_subset_subproductBadSet
      hρ hN x0 T a)
    (measure_ne_top _ _)

/-- Synchronous rounded and unrounded paths remain within a polylogarithmic
multiple of the mesh through logarithmic time, in probability, under the
exponential reparametrization `ρ = exp (-L)`. -/
lemma exists_pos_tendsto_measureReal_fixedWidthCouplingErrorBadSet_zero
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N)
    (x0 : Fin N → ℝ) (C0 : ℝ) (hC0 : 0 ≤ C0) :
    ∃ p : ℝ, 0 < p ∧
      Tendsto
        (fun L : ℝ =>
          (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthCouplingErrorBadSet (Real.exp (-L)) N x0
              (fixedWidthCouplingHorizon C0 L)
              (Real.exp (-L) * Real.exp
                (fixedWidthSubproductLogThreshold p L))))
        atTop (𝓝 0) := by
  obtain ⟨p0, hp0, hbad⟩ :=
    exists_pos_tendsto_measureReal_fixedWidthMultiplierSubproductBadSet_zero_along
      hA hN hsub x0 C0 hC0 (fun L ↦ Real.exp (-L))
  refine ⟨p0 + 2, by linarith, ?_⟩
  have hpref := eventually_fixedWidthCouplingAffinePrefactor_le
    N C0 p0 hC0
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbad
  · exact Filter.Eventually.of_forall (fun _L ↦ measureReal_nonneg)
  · filter_upwards [hpref] with L hL
    have hthreshold :
        (Real.sqrt N * (Real.exp (-L) / 2)) *
            (((fixedWidthCouplingHorizon C0 L + 1 : ℕ) : ℝ) *
              Real.exp (fixedWidthSubproductLogThreshold p0 L)) ≤
          Real.exp (-L) * Real.exp
            (fixedWidthSubproductLogThreshold (p0 + 2) L) := by
      calc
        (Real.sqrt N * (Real.exp (-L) / 2)) *
            (((fixedWidthCouplingHorizon C0 L + 1 : ℕ) : ℝ) *
              Real.exp (fixedWidthSubproductLogThreshold p0 L)) =
            Real.exp (-L) * ((Real.sqrt N / 2) *
              (((fixedWidthCouplingHorizon C0 L + 1 : ℕ) : ℝ) *
                Real.exp (fixedWidthSubproductLogThreshold p0 L))) := by ring
        _ ≤ Real.exp (-L) * Real.exp
            (fixedWidthSubproductLogThreshold (p0 + 2) L) :=
          mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
    calc
      (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet (Real.exp (-L)) N x0
            (fixedWidthCouplingHorizon C0 L)
            (Real.exp (-L) * Real.exp
              (fixedWidthSubproductLogThreshold (p0 + 2) L))) ≤
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthCouplingErrorBadSet (Real.exp (-L)) N x0
            (fixedWidthCouplingHorizon C0 L)
            ((Real.sqrt N * (Real.exp (-L) / 2)) *
              (((fixedWidthCouplingHorizon C0 L + 1 : ℕ) : ℝ) *
                Real.exp (fixedWidthSubproductLogThreshold p0 L)))) := by
          exact measureReal_mono
            (fixedWidthCouplingErrorBadSet_mono
              (Real.exp (-L)) N x0 (fixedWidthCouplingHorizon C0 L)
              hthreshold)
            (measure_ne_top _ _)
      _ ≤ (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthMultiplierSubproductBadSet hN (Real.exp (-L)) x0
            (fixedWidthCouplingHorizon C0 L)
            (fixedWidthSubproductLogThreshold p0 L)) :=
        measureReal_fixedWidthCouplingErrorBadSet_le_subproductBadSet
          (Real.exp_pos _) hN x0 (fixedWidthCouplingHorizon C0 L)
          (fixedWidthSubproductLogThreshold p0 L)

end AbsorptionCutoff
