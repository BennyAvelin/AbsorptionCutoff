/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthAbsorptionEntranceAssembly

/-!
# Fixed-width rounded entrance transfer

This continuation module transfers affine-recursion entrance bounds to the
actual grid-scaled rounded radius and begins the bounded-region absorption
argument.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- At every time, the actual grid-scaled rounded radius is bounded by the
aligned affine recursion started from its deterministic initial radius. -/
lemma fixedWidthRoundedGridRadiusFrom_le_affineRecursion
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (y0 : Fin N → ℝ) (n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedGridRadiusFrom ρ N y0 n ω ≤
      affineRecursion
        (fun k ↦ fixedWidthAffineRoundedRadiusMultiplierFrom
          hN ρ y0 k ω)
        (Real.sqrt N / 2)
        (fixedWidthRoundedGridRadiusFrom ρ N y0 0 ω) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        fixedWidthRoundedGridRadiusFrom ρ N y0 (n + 1) ω ≤
            fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω *
                fixedWidthRoundedGridRadiusFrom ρ N y0 n ω +
              Real.sqrt N / 2 :=
          fixedWidthRoundedGridRadiusFrom_succ_le hρ hN y0 n ω
        _ ≤ fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω *
                affineRecursion
                  (fun k ↦ fixedWidthAffineRoundedRadiusMultiplierFrom
                    hN ρ y0 k ω)
                  (Real.sqrt N / 2)
                  (fixedWidthRoundedGridRadiusFrom ρ N y0 0 ω) n +
              Real.sqrt N / 2 := by
          gcongr
          exact fixedWidthAffineRoundedRadiusMultiplierFrom_nonneg
            hN ρ y0 ω (n + 1)
        _ = affineRecursion
              (fun k ↦ fixedWidthAffineRoundedRadiusMultiplierFrom
                hN ρ y0 k ω)
              (Real.sqrt N / 2)
              (fixedWidthRoundedGridRadiusFrom ρ N y0 0 ω) (n + 1) := by
          rw [affineRecursion_succ]
          rfl

/-- Deterministic grid-scaled radius of the exact starting vector. -/
noncomputable def fixedWidthRoundedInitialGridRadius
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) : ℝ :=
  gaussianEuclideanNorm N y0 / ρ

@[simp] lemma fixedWidthRoundedGridRadiusFrom_zero
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedGridRadiusFrom ρ N y0 0 ω =
      fixedWidthRoundedInitialGridRadius ρ N y0 := rfl

/-- Event that the actual rounded grid radius remains strictly above
`Kstar` through time `n`. -/
def fixedWidthRoundedGridSurvivalSetFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (Kstar : ℝ) (n : ℕ) :
    Set (fixedWidthMatrixSampleSpace N) :=
  {ω | ∀ j ≤ n, Kstar <
    fixedWidthRoundedGridRadiusFrom ρ N y0 j ω}

/-- Survival of the actual rounded radius forces survival of its aligned
affine upper comparison. -/
lemma fixedWidthRoundedGridSurvivalSetFrom_subset_affineSurvivalSet
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (y0 : Fin N → ℝ) (Kstar : ℝ) (n : ℕ) :
    fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar n ⊆
      affineSurvivalSet
        (fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0)
        (Real.sqrt N / 2)
        (fixedWidthRoundedInitialGridRadius ρ N y0) Kstar n := by
  intro ω hω j hj
  exact (hω j hj).trans_le
    (by
      simpa using
        (fixedWidthRoundedGridRadiusFrom_le_affineRecursion
          (ρ := ρ) hρ hN y0 j ω))

/-- The actual rounded grid radius inherits logarithmic entrance with an
exponential excess-time tail from its affine upper comparison. -/
theorem exists_fixedWidthRoundedGridSurvivalSetFrom_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) {ρ : ℝ} (hρ : 0 < ρ)
    (y0 : Fin N → ℝ)
    (hK : 0 < fixedWidthRoundedInitialGridRadius ρ N y0) :
    ∃ Kstar c1 c2 c3 : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ r : ℝ,
        (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
            ⌊c1 * Real.log
              (fixedWidthRoundedInitialGridRadius ρ N y0) + r⌋₊) ≤
          c2 * Real.exp (-c3 * r) := by
  obtain ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, hbound⟩ :=
    exists_fixedWidthAffineRoundedRadiusEntrance_bound
      hA hN hsub ρ y0
  refine ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, ?_⟩
  intro r
  let n := ⌊c1 * Real.log
    (fixedWidthRoundedInitialGridRadius ρ N y0) + r⌋₊
  have hsubset :
      fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar n ⊆
        {ω | (n : ℕ∞) <
          affineEntranceTime
            (fun k ↦ fixedWidthAffineRoundedRadiusMultiplierFrom
              hN ρ y0 k ω)
            (Real.sqrt N / 2)
            (fixedWidthRoundedInitialGridRadius ρ N y0) Kstar} := by
    rw [← affineSurvivalSet_eq_lt_affineEntranceTime]
    exact fixedWidthRoundedGridSurvivalSetFrom_subset_affineSurvivalSet
      hρ hN y0 Kstar n
  exact (measureReal_mono hsubset).trans (hbound _ hK r)

/-- Every coordinate is bounded in absolute value by the Euclidean norm. -/
lemma abs_apply_le_gaussianEuclideanNorm
    {N : ℕ} (u : Fin N → ℝ) (i : Fin N) :
    |u i| ≤ gaussianEuclideanNorm N u := by
  apply (sq_le_sq₀ (abs_nonneg _)
    (by unfold gaussianEuclideanNorm; positivity)).mp
  rw [sq_abs]
  unfold gaussianEuclideanNorm
  rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N u)]
  unfold gaussianSquaredNorm
  exact Finset.single_le_sum
    (fun j _ ↦ sq_nonneg (u j)) (Finset.mem_univ i)

/-- From the bounded grid-radius region, a sufficiently small next radial
multiplier sends every pre-rounding coordinate into the zero bin. -/
lemma roundedPstep_eq_zero_of_radialMultiplier_le
    {ρ Kstar : ℝ} (hρ : 0 < ρ) (hKstar : 0 < Kstar)
    {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ)
    (W : Fin N → Fin N → ℝ)
    (hK : gaussianEuclideanNorm N x / ρ ≤ Kstar)
    (hM : gaussianEuclideanNorm N
      (Matrix.mulVec W (fixedWidthUnitDirection hN x)) ≤
        1 / (2 * Kstar)) :
    roundedPstep ρ N x W = 0 := by
  have hxnorm : gaussianEuclideanNorm N x ≤ Kstar * ρ :=
    (div_le_iff₀ hρ).mp hK
  have hmulnorm :
      gaussianEuclideanNorm N (Matrix.mulVec W x) ≤ ρ / 2 := by
    rw [gaussianEuclideanNorm_mulVec_eq_multiplier_mul hN]
    calc
      gaussianEuclideanNorm N
            (Matrix.mulVec W (fixedWidthUnitDirection hN x)) *
          gaussianEuclideanNorm N x ≤
          (1 / (2 * Kstar)) * (Kstar * ρ) := by
        exact mul_le_mul hM hxnorm
          (by unfold gaussianEuclideanNorm; positivity) (by positivity)
      _ = ρ / 2 := by field_simp [hKstar.ne']
  rw [roundedPstep, Qρ_eq_zero_iff hρ]
  intro i
  change |Real.tanh ((Matrix.mulVec W x) i)| ≤ ρ / 2
  exact (abs_tanh_le_abs _).trans
    ((abs_apply_le_gaussianEuclideanNorm
      (Matrix.mulVec W x) i).trans hmulnorm)

/-- Every nondegenerate symmetric interval has positive standard-Gaussian
mass, in the dependency leaf used by the fixed-width argument. -/
lemma gaussianReal_Icc_neg_pos_fixedWidth {t : ℝ} (ht : 0 < t) :
    0 < (gaussianReal 0 1).real (Set.Icc (-t) t) := by
  have hne : gaussianReal 0 1 (Set.Icc (-t) t) ≠ 0 := by
    intro hzero
    have hvol : volume (Set.Icc (-t) t) = 0 :=
      gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num) hzero
    rw [Real.volume_Icc] at hvol
    have hpos : 0 < ENNReal.ofReal (t - -t) :=
      ENNReal.ofReal_pos.mpr (by linarith)
    exact hpos.ne' hvol
  rw [measureReal_def]
  exact ENNReal.toReal_pos hne (measure_ne_top _ _)

/-- The common fixed-width radial multiplier law assigns positive mass below
every positive threshold. -/
lemma measureReal_fixedWidthRadialMultiplierLaw_Iic_pos
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) :
    0 < (fixedWidthRadialMultiplierLaw A N).real (Set.Iic t) := by
  let scale : ℝ := A / Real.sqrt N
  let δ : ℝ := t / (scale * N)
  let I : Set ℝ := Set.Icc (-δ) δ
  let E : Set (Fin N → ℝ) := Set.univ.pi fun _ ↦ I
  let p : ℝ := ((gaussianReal 0 1).real I) ^ N
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact div_pos hA (Real.sqrt_pos.mpr hNreal)
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hIpos : 0 < (gaussianReal 0 1).real I := by
    simpa only [I] using gaussianReal_Icc_neg_pos_fixedWidth hδ
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hEmeasure : (gaussianVec N).real E = p := by
    simp only [gaussianVec, E, I, p, measureReal_def]
    rw [Measure.pi_pi]
    simp
  have hsubset : E ⊆
      (fun g : Fin N → ℝ ↦
        scale * gaussianEuclideanNorm N g) ⁻¹' Set.Iic t := by
    intro g hg
    have hcoord : ∀ i, |g i| ≤ δ := by
      intro i
      rw [abs_le]
      exact hg i (Set.mem_univ i)
    have hsquared :
        gaussianSquaredNorm N g ≤ (N : ℝ) * δ ^ 2 := by
      unfold gaussianSquaredNorm
      calc
        ∑ i, g i ^ 2 ≤ ∑ _i : Fin N, δ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hsqi :=
            pow_le_pow_left₀ (abs_nonneg (g i)) (hcoord i) 2
          simpa only [sq_abs] using hsqi
        _ = (N : ℝ) * δ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_comm]
    have hnorm : gaussianEuclideanNorm N g ≤ (N : ℝ) * δ := by
      unfold gaussianEuclideanNorm
      apply (sq_le_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg hNreal.le hδ.le)).mp
      rw [Real.sq_sqrt (gaussianSquaredNorm_nonneg N g)]
      have hN_one : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith [sq_nonneg δ]
    change scale * gaussianEuclideanNorm N g ≤ t
    calc
      scale * gaussianEuclideanNorm N g ≤
          scale * ((N : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hnorm hscale.le
      _ = t := by
        dsimp only [δ]
        field_simp [hscale.ne', hNreal.ne']
  have htarget : 0 <
      (gaussianVec N).real
        ((fun g : Fin N → ℝ ↦
          scale * gaussianEuclideanNorm N g) ⁻¹' Set.Iic t) := by
    rw [← hEmeasure] at hp
    exact hp.trans_le (measureReal_mono hsubset)
  rw [fixedWidthRadialMultiplierLaw_eq_map_scaledGaussianEuclideanNorm
    hA hN, measureReal_def,
    Measure.map_apply
      ((measurable_gaussianEuclideanNorm N).const_mul _)
      measurableSet_Iic]
  simpa only [scale, measureReal_def] using htarget

/-- Every state in a bounded grid-radius region has a mesh-uniform positive
one-step chance to be absorbed at zero. -/
theorem exists_pos_le_measureReal_roundedPkernel_singleton_zero_of_gridRadius_le
    {A : ℝ} (hA : 0 < A) {ρ Kstar : ℝ}
    (hρ : 0 < ρ) (hKstar : 0 < Kstar)
    {N : ℕ} (hN : 0 < N) :
    ∃ p : ℝ, 0 < p ∧
      ∀ x : Fin N → ℝ,
        gaussianEuclideanNorm N x / ρ ≤ Kstar →
          p ≤ (roundedPkernel A ρ N x).real
            ({0} : Set (Fin N → ℝ)) := by
  let t : ℝ := 1 / (2 * Kstar)
  let p : ℝ := (fixedWidthRadialMultiplierLaw A N).real (Set.Iic t)
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hp : 0 < p :=
    measureReal_fixedWidthRadialMultiplierLaw_Iic_pos hA hN ht
  refine ⟨p, hp, ?_⟩
  intro x hx
  let radial : (Fin N → Fin N → ℝ) → ℝ :=
    fun W ↦ gaussianEuclideanNorm N
      (Matrix.mulVec W (fixedWidthUnitDirection hN x))
  have hradial : Measurable radial := by
    apply (measurable_gaussianEuclideanNorm N).comp
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    fun_prop
  have hradialLaw :
      Measure.map radial (gaussianMat A N) =
        fixedWidthRadialMultiplierLaw A N :=
    map_gaussianEuclideanNorm_mulVec_gaussianMat_of_unit A _
      (gaussianEuclideanNorm_fixedWidthUnitDirection hN x)
  have hsmallMeasure :
      (gaussianMat A N).real (radial ⁻¹' Set.Iic t) = p := by
    dsimp only [p]
    rw [← hradialLaw,
      map_measureReal_apply hradial measurableSet_Iic]
  have hsubset :
      radial ⁻¹' Set.Iic t ⊆
        roundedPstep ρ N x ⁻¹' ({0} : Set (Fin N → ℝ)) := by
    intro W hW
    change roundedPstep ρ N x W = 0
    apply roundedPstep_eq_zero_of_radialMultiplier_le
      hρ hKstar hN x W hx
    exact hW
  have hstep : Measurable (roundedPstep ρ N x) := by
    exact (measurable_Qρ ρ N).comp (measurable_Pstep_right N x)
  rw [roundedPkernel_apply,
    map_measureReal_apply hstep (measurableSet_singleton 0)]
  rw [← hsmallMeasure]
  exact measureReal_mono hsubset

/-- Finite prefixes of the affine-comparison multiplier process have the same
joint law for every mesh and every deterministic starting state. -/
lemma identDistrib_fixedWidthAffineRoundedRadiusMultiplierPrefixFrom
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (ρ ρ' : ℝ) (y0 y0' : Fin N → ℝ) (n : ℕ) :
    IdentDistrib
      (fun ω (i : Fin n) ↦
        fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 i ω)
      (fun ω (i : Fin n) ↦
        fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ' y0' i ω)
      (fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthMatrixGaussianMeasure A N) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  have hmeas :
      Measurable (fun ω (i : Fin n) ↦
        fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 i ω) :=
    measurable_pi_lambda _ fun i ↦
      measurable_fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 i
  have hmeas' :
      Measurable (fun ω (i : Fin n) ↦
        fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ' y0' i ω) :=
    measurable_pi_lambda _ fun i ↦
      measurable_fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ' y0' i
  have hind :
      iIndepFun
        (fun i : Fin n ↦
          fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 i)
        μ :=
    (iIndepFun_fixedWidthAffineRoundedRadiusMultiplierFrom
      A hN ρ y0).precomp Fin.val_injective
  have hind' :
      iIndepFun
        (fun i : Fin n ↦
          fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ' y0' i)
        μ :=
    (iIndepFun_fixedWidthAffineRoundedRadiusMultiplierFrom
      A hN ρ' y0').precomp Fin.val_injective
  refine ⟨hmeas.aemeasurable, hmeas'.aemeasurable, ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map
      (f := fun i : Fin n ↦
        fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0 i)
      (fun i ↦
        (measurable_fixedWidthAffineRoundedRadiusMultiplierFrom
          hN ρ y0 i).aemeasurable) hind,
    iIndepFun.map_fun_eq_pi_map
      (f := fun i : Fin n ↦
        fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ' y0' i)
      (fun i ↦
        (measurable_fixedWidthAffineRoundedRadiusMultiplierFrom
          hN ρ' y0' i).aemeasurable) hind']
  congr 1
  funext i
  rcases i with ⟨_ | k, hk⟩
  · rfl
  · exact
      (map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ y0 k).trans
        (map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ' y0' k).symm

/-- The affine-comparison survival probability is independent of the mesh and
the deterministic starting state used to construct the adapted multipliers. -/
lemma measureReal_fixedWidthAffineRoundedRadiusSurvivalSet_eq
    (A : ℝ) {N : ℕ} (hN : 0 < N)
    (ρ ρ' : ℝ) (y0 y0' : Fin N → ℝ)
    (b K Kstar : ℝ) (n : ℕ) :
    (fixedWidthMatrixGaussianMeasure A N).real
        (affineSurvivalSet
          (fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0)
          b K Kstar n) =
      (fixedWidthMatrixGaussianMeasure A N).real
        (affineSurvivalSet
          (fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ' y0')
          b K Kstar n) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let M := fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0
  let M' := fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ' y0'
  let pre : fixedWidthMatrixSampleSpace N → (Fin (n + 1) → ℝ) :=
    fun ω i ↦ M i ω
  let pre' : fixedWidthMatrixSampleSpace N → (Fin (n + 1) → ℝ) :=
    fun ω i ↦ M' i ω
  let extend : (Fin (n + 1) → ℝ) → ℕ → ℝ :=
    fun v k ↦ if hk : k < n + 1 then v ⟨k, hk⟩ else 0
  let S : Set (Fin (n + 1) → ℝ) :=
    affineSurvivalSet (fun k v ↦ extend v k) b K Kstar n
  have hextend : ∀ k,
      Measurable (fun v : Fin (n + 1) → ℝ ↦ extend v k) := by
    intro k
    by_cases hk : k < n + 1
    · simpa only [extend, dif_pos hk] using
        (measurable_pi_apply (⟨k, hk⟩ : Fin (n + 1)))
    · simpa only [extend, dif_neg hk] using
        (measurable_const :
          Measurable (fun _ : Fin (n + 1) → ℝ ↦ (0 : ℝ)))
  have hS : MeasurableSet S :=
    measurableSet_affineSurvivalSet
      (fun k v ↦ extend v k) b K Kstar n hextend
  have hrec :
      ∀ ω j, j ≤ n →
        affineRecursion (fun k ↦ extend (pre ω) k) b K j =
          affineRecursion (fun k ↦ M k ω) b K j := by
    intro ω j hj
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [affineRecursion_succ]
        rw [ih (Nat.le_trans (Nat.le_succ j) hj)]
        have hjlt : j + 1 < n + 1 := Nat.lt_succ_of_le hj
        simp only [extend, dif_pos hjlt, pre, M]
  have hrec' :
      ∀ ω j, j ≤ n →
        affineRecursion (fun k ↦ extend (pre' ω) k) b K j =
          affineRecursion (fun k ↦ M' k ω) b K j := by
    intro ω j hj
    induction j with
    | zero => rfl
    | succ j ih =>
        simp only [affineRecursion_succ]
        rw [ih (Nat.le_trans (Nat.le_succ j) hj)]
        have hjlt : j + 1 < n + 1 := Nat.lt_succ_of_le hj
        simp only [extend, dif_pos hjlt, pre', M']
  have hset :
      affineSurvivalSet M b K Kstar n = pre ⁻¹' S := by
    ext ω
    simp only [affineSurvivalSet, Set.mem_setOf_eq, Set.mem_preimage, S]
    constructor
    · intro h j hj
      rw [hrec ω j hj]
      exact h j hj
    · intro h j hj
      rw [← hrec ω j hj]
      exact h j hj
  have hset' :
      affineSurvivalSet M' b K Kstar n = pre' ⁻¹' S := by
    ext ω
    simp only [affineSurvivalSet, Set.mem_setOf_eq, Set.mem_preimage, S]
    constructor
    · intro h j hj
      rw [hrec' ω j hj]
      exact h j hj
    · intro h j hj
      rw [← hrec' ω j hj]
      exact h j hj
  have hmeasure :=
    (identDistrib_fixedWidthAffineRoundedRadiusMultiplierPrefixFrom
      A hN ρ ρ' y0 y0' (n + 1)).measure_preimage_eq hS
  change μ.real (affineSurvivalSet M b K Kstar n) =
    μ.real (affineSurvivalSet M' b K Kstar n)
  rw [hset, hset']
  exact congrArg ENNReal.toReal hmeasure

/-- The logarithmic entrance constants for the rounded grid radius can be
chosen uniformly before the mesh and deterministic-start quantifiers. -/
theorem exists_uniform_fixedWidthRoundedGridSurvivalSetFrom_bound
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsub : FixedWidthSubcritical A N) :
    ∃ Kstar c1 c2 c3 : ℝ,
      0 < Kstar ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ y0 : Fin N → ℝ,
        0 < fixedWidthRoundedInitialGridRadius ρ N y0 →
        ∀ r : ℝ,
          (fixedWidthMatrixGaussianMeasure A N).real
            (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar
              ⌊c1 * Real.log
                (fixedWidthRoundedInitialGridRadius ρ N y0) + r⌋₊) ≤
            c2 * Real.exp (-c3 * r) := by
  obtain ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, hbound⟩ :=
    exists_fixedWidthAffineRoundedRadiusEntrance_bound
      hA hN hsub 1 (0 : Fin N → ℝ)
  refine ⟨Kstar, c1, c2, c3, hKstar, hc1, hc2, hc3, ?_⟩
  intro ρ hρ y0 hK r
  let K := fixedWidthRoundedInitialGridRadius ρ N y0
  let n := ⌊c1 * Real.log K + r⌋₊
  calc
    (fixedWidthMatrixGaussianMeasure A N).real
          (fixedWidthRoundedGridSurvivalSetFrom ρ N y0 Kstar n) ≤
        (fixedWidthMatrixGaussianMeasure A N).real
          (affineSurvivalSet
            (fixedWidthAffineRoundedRadiusMultiplierFrom hN ρ y0)
            (Real.sqrt N / 2) K Kstar n) :=
      measureReal_mono
        (fixedWidthRoundedGridSurvivalSetFrom_subset_affineSurvivalSet
          hρ hN y0 Kstar n)
    _ = (fixedWidthMatrixGaussianMeasure A N).real
          (affineSurvivalSet
            (fixedWidthAffineRoundedRadiusMultiplierFrom
              hN 1 (0 : Fin N → ℝ))
            (Real.sqrt N / 2) K Kstar n) :=
      measureReal_fixedWidthAffineRoundedRadiusSurvivalSet_eq
        A hN ρ 1 y0 0 (Real.sqrt N / 2) K Kstar n
    _ ≤ c2 * Real.exp (-c3 * r) := by
      have href := hbound K hK r
      rwa [← affineSurvivalSet_eq_lt_affineEntranceTime] at href

end AbsorptionCutoff
