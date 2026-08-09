/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthAbsorptionEntranceTransfer

/-!
# Fixed-width finite-grid absorption regeneration

This continuation module combines uniform logarithmic entrance and
bounded-region absorption minorization through the paper's return-time
regeneration argument.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- First entrance time of the exact-start rounded grid radius into the bounded
region `(-∞, Kstar]`. -/
noncomputable def fixedWidthRoundedGridEntranceTimeFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) :
    fixedWidthMatrixSampleSpace N → WithTop ℕ :=
  hittingAfter
    (fixedWidthRoundedGridRadiusFrom ρ N y0) (Set.Iic Kstar) 0

/-- The rounded grid entrance time exceeds `n` exactly when the grid radius
stays strictly above `Kstar` through time `n`. -/
lemma lt_fixedWidthRoundedGridEntranceTimeFrom_iff
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) (n : ℕ) :
    (n : WithTop ℕ) <
        fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω ↔
      ∀ j ≤ n,
        Kstar < fixedWidthRoundedGridRadiusFrom ρ N y0 j ω := by
  rw [← not_le]
  change
    (¬hittingAfter (fixedWidthRoundedGridRadiusFrom ρ N y0)
        (Set.Iic Kstar) 0 ω ≤ (n : WithTop ℕ)) ↔ _
  have hle :
      hittingAfter (fixedWidthRoundedGridRadiusFrom ρ N y0)
          (Set.Iic Kstar) 0 ω ≤ (n : WithTop ℕ) ↔
        ∃ j ≤ n,
          fixedWidthRoundedGridRadiusFrom ρ N y0 j ω ≤ Kstar := by
    simpa [Set.mem_Icc] using
      (MeasureTheory.hittingAfter_le_iff
        (u := fixedWidthRoundedGridRadiusFrom ρ N y0)
        (s := Set.Iic Kstar) (n := 0) (i := n) (ω := ω))
  rw [hle]
  simp only [not_exists]
  constructor
  · intro h j hj
    exact lt_of_not_ge fun hle' ↦ h j ⟨hj, hle'⟩
  · intro h j hj
    exact (not_lt_of_ge hj.2) (h j hj.1)

/-- Finite survival events for the rounded grid entrance time agree with the
previously packaged rounded grid-radius survival sets. -/
lemma fixedWidthRoundedGridSurvivalSetFrom_eq_lt_entranceTime
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (n : ℕ) :
    fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar n =
      {ω | (n : WithTop ℕ) <
        fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar ω} := by
  ext ω
  exact lt_fixedWidthRoundedGridEntranceTimeFrom_iff
    ρ N y0 Kstar ω n |>.symm

/-- A matrix innovation at time `s ≤ t` is measurable with respect to the
canonical matrix-prefix filtration at time `t`. -/
lemma measurable_fixedWidthMatrixEval_piLE
    {N : ℕ} {s t : ℕ} (hst : s ≤ t) :
    Measurable[Filtration.piLE t]
      (fun ω : fixedWidthMatrixSampleSpace N ↦ ω s) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have hrestrict :
      Measurable[MeasurableSpace.comap (Preorder.frestrictLe t) inferInstance]
        (Preorder.frestrictLe t :
          fixedWidthMatrixSampleSpace N →
            ((i : Finset.Iic t) → (Fin N → Fin N → ℝ))) :=
    comap_measurable _
  exact (measurable_pi_apply ⟨s, Finset.mem_Iic.mpr hst⟩).comp hrestrict

/-- The exact-start rounded vector path is adapted to the canonical
matrix-prefix filtration. -/
lemma measurable_fixedWidthRoundedVectorPathFrom_piLE
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable[Filtration.piLE n]
      (fixedWidthRoundedVectorPathFrom ρ N y0 n) := by
  induction n with
  | zero =>
      simp only [fixedWidthRoundedVectorPathFrom]
      exact measurable_const
  | succ n ih =>
      simp only [fixedWidthRoundedVectorPathFrom]
      have hpath :
          Measurable[Filtration.piLE (n + 1)]
            (fixedWidthRoundedVectorPathFrom ρ N y0 n) :=
        ih.mono (Filtration.piLE.mono (Nat.le_succ n)) le_rfl
      have hmatrix :
          Measurable[Filtration.piLE (n + 1)]
            (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n) :=
        measurable_fixedWidthMatrixEval_piLE (Nat.le_succ n)
      unfold roundedPstep
      have hP : Measurable[Filtration.piLE (n + 1)]
          (fun ω : fixedWidthMatrixSampleSpace N ↦
            Pstep N
              (fixedWidthRoundedVectorPathFrom ρ N y0 n ω) (ω n)) := by
        refine @measurable_pi_lambda
          (fixedWidthMatrixSampleSpace N) (Fin N) (fun _ ↦ ℝ)
          (Filtration.piLE (n + 1)) (fun _ ↦ inferInstance)
          (fun ω ↦ Pstep N
            (fixedWidthRoundedVectorPathFrom ρ N y0 n ω) (ω n)) ?_
        intro i
        unfold Pstep
        apply continuous_tanh.measurable.comp
        apply Finset.measurable_sum
        intro j _
        exact ((measurable_pi_apply j).comp
          ((measurable_pi_apply i).comp hmatrix)).mul
            ((measurable_pi_apply j).comp hpath)
      exact (measurable_Qρ ρ N).comp hP

/-- The exact-start rounded grid-radius process is adapted to the canonical
matrix-prefix filtration. -/
lemma measurable_fixedWidthRoundedGridRadiusFrom_piLE
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable[Filtration.piLE n]
      (fixedWidthRoundedGridRadiusFrom ρ N y0 n) := by
  exact ((measurable_gaussianEuclideanNorm N).comp
    (measurable_fixedWidthRoundedVectorPathFrom_piLE ρ N y0 n)).div_const ρ

lemma adapted_fixedWidthRoundedGridRadiusFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) :
    Adapted Filtration.piLE
      (fixedWidthRoundedGridRadiusFrom ρ N y0) :=
  measurable_fixedWidthRoundedGridRadiusFrom_piLE ρ N y0

/-- The exact-start rounded grid entrance time is a stopping time for the
canonical matrix-prefix filtration. -/
lemma isStoppingTime_fixedWidthRoundedGridEntranceTimeFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) :
    IsStoppingTime Filtration.piLE
      (fixedWidthRoundedGridEntranceTimeFrom ρ N y0 Kstar) := by
  unfold fixedWidthRoundedGridEntranceTimeFrom
  exact (adapted_fixedWidthRoundedGridRadiusFrom ρ N y0)
    |>.isStoppingTime_hittingAfter measurableSet_Iic

/-- First strictly positive return time of the exact-start rounded grid radius
to the bounded region `(-∞, Kstar]`. -/
noncomputable def fixedWidthRoundedGridReturnTimeFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) :
    fixedWidthMatrixSampleSpace N → WithTop ℕ :=
  hittingAfter
    (fixedWidthRoundedGridRadiusFrom ρ N y0) (Set.Iic Kstar) 1

/-- The positive return time exceeds `n` exactly when the grid radius stays
strictly above `Kstar` at every time in `[1,n]`. -/
lemma lt_fixedWidthRoundedGridReturnTimeFrom_iff
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) (n : ℕ) :
    (n : WithTop ℕ) <
        fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ↔
      ∀ j, 1 ≤ j → j ≤ n →
        Kstar < fixedWidthRoundedGridRadiusFrom ρ N y0 j ω := by
  rw [← not_le]
  change
    (¬hittingAfter (fixedWidthRoundedGridRadiusFrom ρ N y0)
        (Set.Iic Kstar) 1 ω ≤ (n : WithTop ℕ)) ↔ _
  have hle :
      hittingAfter (fixedWidthRoundedGridRadiusFrom ρ N y0)
          (Set.Iic Kstar) 1 ω ≤ (n : WithTop ℕ) ↔
        ∃ j, (1 ≤ j ∧ j ≤ n) ∧
          fixedWidthRoundedGridRadiusFrom ρ N y0 j ω ≤ Kstar := by
    simpa [Set.mem_Icc] using
      (MeasureTheory.hittingAfter_le_iff
        (u := fixedWidthRoundedGridRadiusFrom ρ N y0)
        (s := Set.Iic Kstar) (n := 1) (i := n) (ω := ω))
  rw [hle]
  simp only [not_exists]
  constructor
  · intro h j h1j hjn
    exact lt_of_not_ge fun hle' ↦ h j ⟨⟨h1j, hjn⟩, hle'⟩
  · intro h j hj
    exact (not_lt_of_ge hj.2) (h j hj.1.1 hj.1.2)

lemma one_le_fixedWidthRoundedGridReturnTimeFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) :
    (1 : WithTop ℕ) ≤
      fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω :=
  MeasureTheory.le_hittingAfter ω

/-- The positive bounded-region return time is a stopping time for the
canonical matrix-prefix filtration. -/
lemma isStoppingTime_fixedWidthRoundedGridReturnTimeFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) :
    IsStoppingTime Filtration.piLE
      (fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar) := by
  unfold fixedWidthRoundedGridReturnTimeFrom
  exact (adapted_fixedWidthRoundedGridRadiusFrom ρ N y0)
    |>.isStoppingTime_hittingAfter measurableSet_Iic

/-- Starting in the bounded grid-radius region, the time-one radius is bounded
by the first radial multiplier times `Kstar` plus the rounding drift. -/
lemma fixedWidthRoundedGridRadiusFrom_one_le
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (y0 : Fin N → ℝ) (Kstar : ℝ)
    (hK : fixedWidthRoundedInitialGridRadius ρ N y0 ≤ Kstar)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedGridRadiusFrom ρ N y0 1 ω ≤
      fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 0 ω * Kstar +
        Real.sqrt N / 2 := by
  calc
    fixedWidthRoundedGridRadiusFrom ρ N y0 1 ω ≤
        fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 0 ω *
            fixedWidthRoundedGridRadiusFrom ρ N y0 0 ω +
          Real.sqrt N / 2 := by
      simpa using
        (fixedWidthRoundedGridRadiusFrom_succ_le hρ hN y0 0 ω)
    _ ≤ fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 0 ω * Kstar +
          Real.sqrt N / 2 := by
      gcongr
      · exact fixedWidthAffineRoundedRadiusMultiplierFrom_nonneg
          hN ρ y0 ω 1
      · simpa using hK

/-- A positive power below both one and the Gaussian radial moment threshold
is integrable for the random time-one radius envelope used after a failed
absorption attempt. -/
lemma integrable_rpow_max_two_mul_add_fixedWidthRoundedRadiusMultiplierFrom
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ)
    {K b p : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hp : 0 < p) (hp_one : p ≤ 1) (hpN : p < N) :
    Integrable
      (fun ω : fixedWidthMatrixSampleSpace N ↦
        (max 2
          (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω * K + b)) ^ p)
      (fixedWidthMatrixGaussianMeasure A N) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let M := fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n
  have hMmeas : Measurable M :=
    measurable_fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n
  have hMpos : ∀ᵐ ω ∂μ, 0 < M ω :=
    ae_fixedWidthRoundedRadiusMultiplierFrom_pos hA hN ρ y0 n
  have hp_lower : -(N : ℝ) < p := by
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    linarith
  have hexp : Integrable (fun ω ↦ Real.exp (p * Real.log (M ω))) μ :=
    Ioo_subset_integrableExpSet_fixedWidthRoundedRadiusLogMultiplierFrom
      hA hN ρ y0 n ⟨hp_lower, hpN⟩
  have hMpow : Integrable (fun ω ↦ (M ω) ^ p) μ := by
    apply hexp.congr
    filter_upwards [hMpos] with ω hMω
    rw [Real.rpow_def_of_pos hMω]
    congr 1
    ring
  have hmajorant : Integrable
      (fun ω ↦ (2 + b) ^ p + K ^ p * (M ω) ^ p) μ :=
    (integrable_const ((2 + b) ^ p)).add (hMpow.const_mul (K ^ p))
  have hbaseMeas : Measurable
      (fun ω ↦ max 2 (M ω * K + b)) :=
    measurable_const.max ((hMmeas.mul_const K).add_const b)
  refine hmajorant.mono'
    (((Real.continuous_rpow_const hp.le).measurable.comp hbaseMeas)
      |>.aestronglyMeasurable) ?_
  filter_upwards [hMpos] with ω hMω
  have hKM : 0 ≤ K * M ω := mul_nonneg hK hMω.le
  have hbase : 0 ≤ max 2 (M ω * K + b) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hsum : 0 ≤ 2 + b := by positivity
  have hle : max 2 (M ω * K + b) ≤ (2 + b) + K * M ω := by
    apply max_le
    · linarith
    · nlinarith
  change ‖(max 2 (M ω * K + b)) ^ p‖ ≤
    (2 + b) ^ p + K ^ p * (M ω) ^ p
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hbase _)]
  calc
    (max 2 (M ω * K + b)) ^ p ≤
        ((2 + b) + K * M ω) ^ p :=
      Real.rpow_le_rpow hbase hle hp.le
    _ ≤ (2 + b) ^ p + (K * M ω) ^ p :=
      Real.rpow_add_le_add_rpow hsum hKM hp.le hp_one
    _ = (2 + b) ^ p + K ^ p * (M ω) ^ p := by
      rw [Real.mul_rpow hK hMω.le]

/-- An exponential upper tail gives every strictly smaller positive
exponential moment.  This is the layer-cake estimate used for bounded-region
return times. -/
lemma integrable_exp_mul_of_measure_tail_le_exp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → ℝ} (hXmeas : AEMeasurable X μ)
    (hXnonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    {C c s : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hsc : s < c)
    (htail : ∀ r, 0 < r →
      μ {ω | r < X ω} ≤ ENNReal.ofReal (C * Real.exp (-(c * r)))) :
    Integrable (fun ω ↦ Real.exp (s * X ω)) μ := by
  let g : ℝ → ℝ := fun r ↦ s * Real.exp (s * r)
  have hgcont : Continuous g :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hgint : ∀ r > 0, IntervalIntegrable g volume 0 r :=
    fun r _ ↦ hgcont.intervalIntegrable 0 r
  have hgnonneg : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)), 0 ≤ g r :=
    Eventually.of_forall fun r ↦ mul_nonneg hs.le (Real.exp_pos _).le
  have hlayer :=
    lintegral_comp_eq_lintegral_meas_lt_mul μ hXnonneg hXmeas hgint hgnonneg
  have hinterval (x : ℝ) :
      (∫ r in (0 : ℝ)..x, g r) = Real.exp (s * x) - 1 := by
    have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) x,
        HasDerivAt (fun y : ℝ ↦ Real.exp (s * y)) (g r) r := by
      intro r _
      simpa [g, mul_comm] using ((hasDerivAt_id r).const_mul s).exp
    calc
      (∫ r in (0 : ℝ)..x, g r) =
          Real.exp (s * x) - Real.exp (s * 0) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
          (hgcont.intervalIntegrable 0 x)
      _ = Real.exp (s * x) - 1 := by rw [mul_zero, Real.exp_zero]
  have hdecay : IntegrableOn
      (fun r : ℝ ↦ C * s * Real.exp (-((c - s) * r)))
      (Set.Ioi 0) volume := by
    change Integrable
      (fun r : ℝ ↦ C * s * Real.exp (-((c - s) * r)))
      (volume.restrict (Set.Ioi 0))
    apply ((exp_neg_integrableOn_Ioi 0 (sub_pos.mpr hsc)).const_mul
      (C * s)).congr
    exact Eventually.of_forall fun r ↦ by
      ring_nf
  have hrhs_le :
      (∫⁻ r in Set.Ioi (0 : ℝ),
          μ {ω | r < X ω} * ENNReal.ofReal (g r)) ≤
        ∫⁻ r in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (C * s * Real.exp (-((c - s) * r))) := by
    apply lintegral_mono_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    calc
      μ {ω | r < X ω} * ENNReal.ofReal (g r) ≤
          ENNReal.ofReal (C * Real.exp (-(c * r))) *
            ENNReal.ofReal (g r) :=
        mul_le_mul_left (htail r hr) _
      _ = ENNReal.ofReal
          (C * Real.exp (-(c * r)) * (s * Real.exp (s * r))) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC (Real.exp_pos _).le)]
      _ = ENNReal.ofReal
          (C * s * Real.exp (-((c - s) * r))) := by
        congr 1
        calc
          C * Real.exp (-(c * r)) * (s * Real.exp (s * r)) =
              C * s * (Real.exp (-(c * r)) * Real.exp (s * r)) := by
            ring
          _ = C * s * Real.exp (-((c - s) * r)) := by
            rw [← Real.exp_add]
            congr 2
            ring
  have hrhs_lt :
      (∫⁻ r in Set.Ioi (0 : ℝ),
          μ {ω | r < X ω} * ENNReal.ofReal (g r)) < ⊤ :=
    lt_of_le_of_lt hrhs_le hdecay.lintegral_lt_top
  have hminus_lt :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω) - 1) ∂μ) < ⊤ := by
    rw [← hlayer] at hrhs_lt
    simpa only [hinterval] using hrhs_lt
  have hexpMeas : AEMeasurable (fun ω ↦ Real.exp (s * X ω)) μ :=
    Real.continuous_exp.measurable.comp_aemeasurable (hXmeas.const_mul s)
  refine ⟨hexpMeas.aestronglyMeasurable,
    (hasFiniteIntegral_iff_norm _).mpr ?_⟩
  have hsplit : ∀ᵐ ω ∂μ,
      ENNReal.ofReal ‖Real.exp (s * X ω)‖ =
        1 + ENNReal.ofReal (Real.exp (s * X ω) - 1) := by
    filter_upwards [hXnonneg] with ω hXω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hminus : 0 ≤ Real.exp (s * X ω) - 1 :=
      sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hs.le hXω))
    calc
      ENNReal.ofReal (Real.exp (s * X ω)) =
          ENNReal.ofReal (1 + (Real.exp (s * X ω) - 1)) := by ring_nf
      _ = ENNReal.ofReal 1 +
          ENNReal.ofReal (Real.exp (s * X ω) - 1) :=
        ENNReal.ofReal_add (by norm_num) hminus
      _ = 1 + ENNReal.ofReal (Real.exp (s * X ω) - 1) := by norm_num
  rw [lintegral_congr_ae hsplit, lintegral_add_left measurable_const,
    lintegral_const]
  exact ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top (by simp)
        (lt_top_iff_ne_top.mpr (measure_ne_top μ Set.univ)),
      hminus_lt⟩

/-- Delete the first `m` matrix innovations from the canonical driving
sequence. -/
def fixedWidthMatrixShift (N m : ℕ) :
    fixedWidthMatrixSampleSpace N → fixedWidthMatrixSampleSpace N :=
  fun ω n ↦ ω (m + n)

lemma measurable_fixedWidthMatrixShift (N m : ℕ) :
    Measurable (fixedWidthMatrixShift N m) := by
  unfold fixedWidthMatrixShift
  exact measurable_pi_lambda _ fun n ↦ measurable_pi_apply (m + n)

/-- Deleting a deterministic matrix prefix preserves the canonical iid
Gaussian product law. -/
lemma map_fixedWidthMatrixShift (A : ℝ) (N m : ℕ) :
    Measure.map (fixedWidthMatrixShift N m)
        (fixedWidthMatrixGaussianMeasure A N) =
      fixedWidthMatrixGaussianMeasure A N := by
  unfold fixedWidthMatrixGaussianMeasure fixedWidthMatrixShift
  simpa using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ ↦ gaussianMat A N)
      (f := fun n : ℕ ↦ m + n)
      (fun _ _ h ↦ Nat.add_left_cancel h))

/-- The matrix prefix used before a deterministic time is independent of the
shifted sequence of all future innovations. -/
lemma indepFun_fixedWidthMatrixPrefix_shift (A : ℝ) (N m : ℕ) :
    IndepFun (fixedWidthMatrixPrefix N m) (fixedWidthMatrixShift N m)
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hproc : IndepFun
      (fun ω : fixedWidthMatrixSampleSpace N ↦ fun i : Fin m ↦ ω i)
      (fun ω : fixedWidthMatrixSampleSpace N ↦ fun j : ℕ ↦ ω (m + j))
      (fixedWidthMatrixGaussianMeasure A N) := by
    refine IndepFun.process_indepFun_process
      (P := fixedWidthMatrixGaussianMeasure A N)
      (X := fun (i : Fin m) (ω : fixedWidthMatrixSampleSpace N) ↦ ω i)
      (Y := fun (j : ℕ) (ω : fixedWidthMatrixSampleSpace N) ↦ ω (m + j))
      (fun i ↦ measurable_pi_apply (i : ℕ))
      (fun j ↦ measurable_pi_apply (m + j)) ?_
    intro I J
    let S : Finset ℕ := I.image fun i : Fin m ↦ (i : ℕ)
    let T : Finset ℕ := J.image fun j : ℕ ↦ m + j
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro k hkS hkT
      change k ∈ I.image (fun i : Fin m ↦ (i : ℕ)) at hkS
      change k ∈ J.image (fun j : ℕ ↦ m + j) at hkT
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hkS
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hkT
      have hi : (i : ℕ) < m := i.isLt
      omega
    have hbase :=
      (iIndepFun_fixedWidthMatrixCoordinate A N).indepFun_finset
        S T hdisj (fun k ↦ measurable_pi_apply k)
    let leftMap :
        (S → (Fin N → Fin N → ℝ)) →
          (I → (Fin N → Fin N → ℝ)) :=
      fun u i ↦ u ⟨i.1, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
    let rightMap :
        (T → (Fin N → Fin N → ℝ)) →
          (J → (Fin N → Fin N → ℝ)) :=
      fun u j ↦ u ⟨m + j.1,
        Finset.mem_image.mpr ⟨j.1, j.2, rfl⟩⟩
    have hleft : Measurable leftMap := by
      unfold leftMap
      exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
    have hright : Measurable rightMap := by
      unfold rightMap
      exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply _
    have hcomp := hbase.comp hleft hright
    convert hcomp using 1 <;> rfl
  change IndepFun
    (fun ω : fixedWidthMatrixSampleSpace N ↦ fun i : Fin m ↦ ω i)
    (fun ω : fixedWidthMatrixSampleSpace N ↦ fun j : ℕ ↦ ω (m + j))
    (fixedWidthMatrixGaussianMeasure A N)
  exact hproc

/-- The rounded state at deterministic time `m`, as an explicit measurable
function of the strict matrix prefix used to construct it. -/
noncomputable def fixedWidthRoundedStateFromPrefix
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (m : ℕ) :
    (Fin m → (Fin N → Fin N → ℝ)) → (Fin N → ℝ) :=
  fun u ↦ fixedWidthRoundedVectorPathFrom ρ N y0 m
    (fixedWidthExtendMatrixPrefix N m u)

lemma measurable_fixedWidthRoundedStateFromPrefix
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (m : ℕ) :
    Measurable (fixedWidthRoundedStateFromPrefix ρ N y0 m) :=
  (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 m).comp
    (measurable_fixedWidthExtendMatrixPrefix N m)

lemma fixedWidthRoundedStateFromPrefix_apply
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (m : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedStateFromPrefix ρ N y0 m
        (fixedWidthMatrixPrefix N m ω) =
      fixedWidthRoundedVectorPathFrom ρ N y0 m ω := by
  unfold fixedWidthRoundedStateFromPrefix
  apply fixedWidthRoundedVectorPathFrom_eq_of_forall_lt ρ N y0 m
  intro k hk
  simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix, hk]

/-- The rounded state at a deterministic restart time is independent of the
shifted future matrix driver. -/
lemma indepFun_fixedWidthRoundedVectorPathFrom_shift
    (A ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (m : ℕ) :
    IndepFun (fixedWidthRoundedVectorPathFrom ρ N y0 m)
      (fixedWidthMatrixShift N m)
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hcomp := (indepFun_fixedWidthMatrixPrefix_shift A N m).comp
    (measurable_fixedWidthRoundedStateFromPrefix ρ N y0 m)
    measurable_id
  convert hcomp using 1
  · funext ω
    exact (fixedWidthRoundedStateFromPrefix_apply ρ N y0 m ω).symm
  · rfl

/-- Restarting the exact-start rounded recursion at a deterministic time is
pathwise the same as starting from the state then present and deleting the
used matrix prefix. -/
lemma fixedWidthRoundedVectorPathFrom_add
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (m n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedVectorPathFrom ρ N y0 (m + n) ω =
      fixedWidthRoundedVectorPathFrom ρ N
        (fixedWidthRoundedVectorPathFrom ρ N y0 m ω) n
        (fixedWidthMatrixShift N m ω) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ]
      simp only [fixedWidthRoundedVectorPathFrom]
      rw [ih]
      rfl

lemma fixedWidthRoundedGridRadiusFrom_add
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (m n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedGridRadiusFrom ρ N y0 (m + n) ω =
      fixedWidthRoundedGridRadiusFrom ρ N
        (fixedWidthRoundedVectorPathFrom ρ N y0 m ω) n
        (fixedWidthMatrixShift N m ω) := by
  unfold fixedWidthRoundedGridRadiusFrom fixedWidthRoundedVectorRadiusFrom
  rw [fixedWidthRoundedVectorPathFrom_add]

/-- The positive return-time tail after time one is exactly the ordinary
entrance-time tail of the restarted path driven by the shifted matrices. -/
lemma succ_lt_fixedWidthRoundedGridReturnTimeFrom_iff
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ)
    (ω : fixedWidthMatrixSampleSpace N) (n : ℕ) :
    ((n + 1 : ℕ) : WithTop ℕ) <
        fixedWidthRoundedGridReturnTimeFrom ρ N y0 Kstar ω ↔
      (n : WithTop ℕ) <
        fixedWidthRoundedGridEntranceTimeFrom ρ N
          (fixedWidthRoundedVectorPathFrom ρ N y0 1 ω) Kstar
          (fixedWidthMatrixShift N 1 ω) := by
  rw [lt_fixedWidthRoundedGridReturnTimeFrom_iff,
    lt_fixedWidthRoundedGridEntranceTimeFrom_iff]
  constructor
  · intro h k hk
    have hradius := h (1 + k) (by omega) (by omega)
    rwa [fixedWidthRoundedGridRadiusFrom_add ρ N y0 1 k ω] at hradius
  · intro h j h1j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = 1 + k := by
      exact ⟨j - 1, by omega⟩
    rw [fixedWidthRoundedGridRadiusFrom_add ρ N y0 1 k ω]
    exact h k (by omega)

end AbsorptionCutoff
