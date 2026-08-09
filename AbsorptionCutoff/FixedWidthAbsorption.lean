/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingProductBounds

/-!
# Fixed-width final-grid absorption

This continuation module proves the final finite-grid absorption estimate and
assembles it with the synchronous rounding comparison for Chapter 3.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

namespace AbsorptionCutoff

/-- Rounded vector path started from an exact deterministic grid point. -/
noncomputable def fixedWidthRoundedVectorPathFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → (Fin N → ℝ)
  | 0 => fun _ ↦ y0
  | n + 1 => fun ω ↦ roundedPstep ρ N
      (fixedWidthRoundedVectorPathFrom ρ N y0 n ω) (ω n)

/-- Euclidean radius of the exact-start rounded vector path. -/
noncomputable def fixedWidthRoundedVectorRadiusFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → ℝ :=
  fun n ω ↦ gaussianEuclideanNorm N
    (fixedWidthRoundedVectorPathFrom ρ N y0 n ω)

/-- Rounded radius measured in units of the grid mesh. -/
noncomputable def fixedWidthRoundedGridRadiusFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → ℝ :=
  fun n ω ↦ fixedWidthRoundedVectorRadiusFrom ρ N y0 n ω / ρ

/-- Radial multiplier in the current rounded path direction, with the fixed
reference direction used at the origin. -/
noncomputable def fixedWidthRoundedRadiusMultiplierFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) :
    ℕ → fixedWidthMatrixSampleSpace N → ℝ :=
  fun n ω ↦ gaussianEuclideanNorm N
    (Matrix.mulVec (ω n)
      (fixedWidthUnitDirection hN
        (fixedWidthRoundedVectorPathFrom ρ N y0 n ω)))

lemma measurable_fixedWidthRoundedVectorPathFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthRoundedVectorPathFrom ρ N y0 n) := by
  induction n with
  | zero =>
      simp only [fixedWidthRoundedVectorPathFrom]
      fun_prop
  | succ n ih =>
      simp only [fixedWidthRoundedVectorPathFrom]
      have hω : Measurable
          (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n) :=
        measurable_pi_apply n
      unfold roundedPstep
      apply (measurable_Qρ ρ N).comp
      apply measurable_pi_iff.mpr
      intro i
      unfold Pstep
      apply continuous_tanh.measurable.comp
      apply Finset.measurable_sum
      intro j _
      exact ((measurable_pi_apply j).comp
        ((measurable_pi_apply i).comp hω)).mul
          ((measurable_pi_apply j).comp ih)

lemma measurable_fixedWidthRoundedVectorRadiusFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthRoundedVectorRadiusFrom ρ N y0 n) :=
  (measurable_gaussianEuclideanNorm N).comp
    (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n)

lemma measurable_fixedWidthRoundedGridRadiusFrom
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthRoundedGridRadiusFrom ρ N y0 n) :=
  (measurable_fixedWidthRoundedVectorRadiusFrom ρ N y0 n).div_const ρ

lemma measurable_fixedWidthRoundedRadiusMultiplierFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n) := by
  have hω : Measurable
      (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n) :=
    measurable_pi_apply n
  have hθ : Measurable (fun ω : fixedWidthMatrixSampleSpace N ↦
      fixedWidthUnitDirection hN
        (fixedWidthRoundedVectorPathFrom ρ N y0 n ω)) :=
    (measurable_fixedWidthUnitDirection hN).comp
      (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n)
  have hmul : Measurable (fun ω : fixedWidthMatrixSampleSpace N ↦
      Matrix.mulVec (ω n)
        (fixedWidthUnitDirection hN
          (fixedWidthRoundedVectorPathFrom ρ N y0 n ω))) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp hω)).mul
        ((measurable_pi_apply j).comp hθ)
  exact (measurable_gaussianEuclideanNorm N).comp hmul

/-- The exact-start rounded path at time `n` depends only on the first `n`
matrix innovations. -/
lemma fixedWidthRoundedVectorPathFrom_eq_of_forall_lt
    (ρ : ℝ) (N : ℕ) (y0 : Fin N → ℝ) (n : ℕ)
    {ω ω' : fixedWidthMatrixSampleSpace N}
    (hω : ∀ k < n, ω k = ω' k) :
    fixedWidthRoundedVectorPathFrom ρ N y0 n ω =
      fixedWidthRoundedVectorPathFrom ρ N y0 n ω' := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [fixedWidthRoundedVectorPathFrom]
      rw [hω n (Nat.lt_succ_self n)]
      rw [ih (fun k hk ↦ hω k (Nat.lt_succ_of_lt hk))]

/-- The rounded path direction as an explicit measurable function of the
strict matrix prefix. -/
noncomputable def fixedWidthRoundedDirectionFromPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    (Fin n → (Fin N → Fin N → ℝ)) → (Fin N → ℝ) :=
  fun u ↦ fixedWidthUnitDirection hN
    (fixedWidthRoundedVectorPathFrom ρ N y0 n
      (fixedWidthExtendMatrixPrefix N n u))

lemma measurable_fixedWidthRoundedDirectionFromPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthRoundedDirectionFromPrefix hN ρ y0 n) :=
  (measurable_fixedWidthUnitDirection hN).comp
    ((measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n).comp
      (measurable_fixedWidthExtendMatrixPrefix N n))

lemma fixedWidthRoundedDirectionFromPrefix_apply
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedDirectionFromPrefix hN ρ y0 n
        (fixedWidthMatrixPrefix N n ω) =
      fixedWidthUnitDirection hN
        (fixedWidthRoundedVectorPathFrom ρ N y0 n ω) := by
  unfold fixedWidthRoundedDirectionFromPrefix
  apply congrArg (fixedWidthUnitDirection hN)
  apply fixedWidthRoundedVectorPathFrom_eq_of_forall_lt ρ N y0 n
  intro k hk
  simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix, hk]

/-- The exact-start rounded path direction is independent of the fresh matrix
innovation at the same time. -/
lemma indepFun_fixedWidthRoundedDirectionFrom_eval
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (y0 : Fin N → ℝ) (n : ℕ) :
    IndepFun
      (fun ω : fixedWidthMatrixSampleSpace N ↦
        fixedWidthUnitDirection hN
          (fixedWidthRoundedVectorPathFrom ρ N y0 n ω))
      (fun ω : fixedWidthMatrixSampleSpace N ↦ ω n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  have hcomp := (indepFun_fixedWidthMatrixPrefix_eval A N n).comp
    (measurable_fixedWidthRoundedDirectionFromPrefix hN ρ y0 n)
    measurable_id
  convert hcomp using 1
  · funext ω
    exact (fixedWidthRoundedDirectionFromPrefix_apply hN ρ y0 n ω).symm
  · rfl

/-- Every exact-start rounded-radius multiplier has the common fixed-width
Gaussian radial law. -/
lemma map_fixedWidthRoundedRadiusMultiplierFrom
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (y0 : Fin N → ℝ) (n : ℕ) :
    Measure.map (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n)
        (fixedWidthMatrixGaussianMeasure A N) =
      fixedWidthRadialMultiplierLaw A N := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let direction : fixedWidthMatrixSampleSpace N → (Fin N → ℝ) :=
    fun ω ↦ fixedWidthUnitDirection hN
      (fixedWidthRoundedVectorPathFrom ρ N y0 n ω)
  let current : fixedWidthMatrixSampleSpace N → (Fin N → Fin N → ℝ) :=
    fun ω ↦ ω n
  let ν := Measure.map direction μ
  let mulNorm :
      (Fin N → ℝ) × (Fin N → Fin N → ℝ) → ℝ :=
    fun p ↦ gaussianEuclideanNorm N (Matrix.mulVec p.2 p.1)
  have hdirection : Measurable direction :=
    (measurable_fixedWidthUnitDirection hN).comp
      (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n)
  have hcurrent : Measurable current := measurable_pi_apply n
  have hmulVec : Measurable
      (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) ↦
        Matrix.mulVec p.2 p.1) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp measurable_fst)
  have hmulNorm : Measurable mulNorm :=
    (measurable_gaussianEuclideanNorm N).comp hmulVec
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map hdirection.aemeasurable
  have hν : ∀ᵐ θ ∂ν, gaussianEuclideanNorm N θ = 1 := by
    change ∀ᵐ θ ∂Measure.map direction μ,
      gaussianEuclideanNorm N θ = 1
    exact (ae_map_iff hdirection.aemeasurable
      ((measurableSet_singleton 1).preimage
        (measurable_gaussianEuclideanNorm N))).2
      (Eventually.of_forall fun ω ↦
        gaussianEuclideanNorm_fixedWidthUnitDirection hN
          (fixedWidthRoundedVectorPathFrom ρ N y0 n ω))
  have hcurrentMap : Measure.map current μ = gaussianMat A N := by
    dsimp [current, μ, fixedWidthMatrixGaussianMeasure]
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ gaussianMat A N) n).map_eq
  have hpair :
      Measure.map (fun ω ↦ (direction ω, current ω)) μ =
        ν.prod (gaussianMat A N) := by
    have hmap :=
      (indepFun_fixedWidthRoundedDirectionFrom_eval A hN ρ y0 n)
        |>.map_prod_eq_prod_map_map
          hdirection.aemeasurable hcurrent.aemeasurable
    change Measure.map (fun ω ↦ (direction ω, current ω)) μ =
      (Measure.map direction μ).prod (Measure.map current μ) at hmap
    rw [hcurrentMap] at hmap
    exact hmap
  change Measure.map
      (mulNorm ∘ fun ω ↦ (direction ω, current ω)) μ = _
  rw [← Measure.map_map hmulNorm (hdirection.prodMk hcurrent), hpair]
  exact map_gaussianEuclideanNorm_mulVec_prod_eq_radialMultiplierLaw
    A ν hν

/-- Vector of the first `n` exact-start rounded-radius multipliers. -/
noncomputable def fixedWidthRoundedRadiusMultiplierPrefixFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    fixedWidthMatrixSampleSpace N → (Fin n → ℝ) :=
  fun ω k ↦ fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 k ω

lemma measurable_fixedWidthRoundedRadiusMultiplierPrefixFrom
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable (fixedWidthRoundedRadiusMultiplierPrefixFrom hN ρ y0 n) :=
  measurable_pi_lambda _ fun k ↦
    measurable_fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 k

/-- The first `n` rounded-radius multipliers as an explicit measurable function
of the first `n` matrix innovations. -/
noncomputable def fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    (Fin n → (Fin N → Fin N → ℝ)) → (Fin n → ℝ) :=
  fun u k ↦ fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 k
    (fixedWidthExtendMatrixPrefix N n u)

lemma measurable_fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ) :
    Measurable
      (fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix
        hN ρ y0 n) :=
  measurable_pi_lambda _ fun k ↦
    (measurable_fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 k).comp
      (measurable_fixedWidthExtendMatrixPrefix N n)

lemma fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix_apply
    {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) (n : ℕ)
    (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix hN ρ y0 n
        (fixedWidthMatrixPrefix N n ω) =
      fixedWidthRoundedRadiusMultiplierPrefixFrom hN ρ y0 n ω := by
  funext k
  have hseq : ∀ j < n,
      fixedWidthExtendMatrixPrefix N n
          (fixedWidthMatrixPrefix N n ω) j = ω j := by
    intro j hj
    simp [fixedWidthExtendMatrixPrefix, fixedWidthMatrixPrefix, hj]
  unfold fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix
    fixedWidthRoundedRadiusMultiplierPrefixFrom
  unfold fixedWidthRoundedRadiusMultiplierFrom
  rw [hseq k k.isLt]
  rw [fixedWidthRoundedVectorPathFrom_eq_of_forall_lt ρ N y0 k
    (fun j hj ↦ hseq j (lt_trans hj k.isLt))]

/-- The first `n` rounded-radius multipliers are independent of multiplier
`n`; this is the sequential-independence input for the iid process. -/
lemma indepFun_fixedWidthRoundedRadiusMultiplierPrefixFrom_next
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (y0 : Fin N → ℝ) (n : ℕ) :
    IndepFun
      (fixedWidthRoundedRadiusMultiplierPrefixFrom hN ρ y0 n)
      (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n)
      (fixedWidthMatrixGaussianMeasure A N) := by
  let μ := fixedWidthMatrixGaussianMeasure A N
  let past := fixedWidthRoundedRadiusMultiplierPrefixFrom hN ρ y0 n
  let direction : fixedWidthMatrixSampleSpace N → (Fin N → ℝ) :=
    fun ω ↦ fixedWidthUnitDirection hN
      (fixedWidthRoundedVectorPathFrom ρ N y0 n ω)
  let current : fixedWidthMatrixSampleSpace N → (Fin N → Fin N → ℝ) :=
    fun ω ↦ ω n
  let pastDirectionFromPrefix :
      (Fin n → (Fin N → Fin N → ℝ)) →
        ((Fin n → ℝ) × (Fin N → ℝ)) :=
    fun u ↦
      (fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix
          hN ρ y0 n u,
        fixedWidthRoundedDirectionFromPrefix hN ρ y0 n u)
  let ν := Measure.map (fun ω ↦ (past ω, direction ω)) μ
  let markMul :
      (((Fin n → ℝ) × (Fin N → ℝ)) × (Fin N → Fin N → ℝ)) →
        ((Fin n → ℝ) × ℝ) :=
    fun p ↦ (p.1.1,
      gaussianEuclideanNorm N (Matrix.mulVec p.2 p.1.2))
  have hpast : Measurable past :=
    measurable_fixedWidthRoundedRadiusMultiplierPrefixFrom hN ρ y0 n
  have hdirection : Measurable direction :=
    (measurable_fixedWidthUnitDirection hN).comp
      (measurable_fixedWidthRoundedVectorPathFrom ρ N y0 n)
  have hcurrent : Measurable current := measurable_pi_apply n
  have hpastDirectionFromPrefix : Measurable pastDirectionFromPrefix :=
    (measurable_fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix
      hN ρ y0 n).prodMk
        (measurable_fixedWidthRoundedDirectionFromPrefix hN ρ y0 n)
  have hpastDirection_apply (ω : fixedWidthMatrixSampleSpace N) :
      pastDirectionFromPrefix (fixedWidthMatrixPrefix N n ω) =
        (past ω, direction ω) := by
    apply Prod.ext
    · exact fixedWidthRoundedRadiusMultiplierPrefixFromMatrixPrefix_apply
        hN ρ y0 n ω
    · exact fixedWidthRoundedDirectionFromPrefix_apply hN ρ y0 n ω
  have hindCurrent :
      IndepFun (fun ω ↦ (past ω, direction ω)) current μ := by
    have hcomp := (indepFun_fixedWidthMatrixPrefix_eval A N n).comp
      hpastDirectionFromPrefix measurable_id
    convert hcomp using 1
    · funext ω
      exact (hpastDirection_apply ω).symm
    · rfl
  have hcurrentMap : Measure.map current μ = gaussianMat A N := by
    dsimp [current, μ, fixedWidthMatrixGaussianMeasure]
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ ↦ gaussianMat A N) n).map_eq
  have hpair :
      Measure.map (fun ω ↦ ((past ω, direction ω), current ω)) μ =
        ν.prod (gaussianMat A N) := by
    have hmap := hindCurrent.map_prod_eq_prod_map_map
      (hpast.prodMk hdirection).aemeasurable hcurrent.aemeasurable
    change Measure.map (fun ω ↦ ((past ω, direction ω), current ω)) μ =
      (Measure.map (fun ω ↦ (past ω, direction ω)) μ).prod
        (Measure.map current μ) at hmap
    rw [hcurrentMap] at hmap
    exact hmap
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map
      (hpast.prodMk hdirection).aemeasurable
  have hν : ∀ᵐ p ∂ν, gaussianEuclideanNorm N p.2 = 1 := by
    change ∀ᵐ p ∂Measure.map (fun ω ↦ (past ω, direction ω)) μ,
      gaussianEuclideanNorm N p.2 = 1
    exact (ae_map_iff (hpast.prodMk hdirection).aemeasurable
      ((measurableSet_singleton 1).preimage
        ((measurable_gaussianEuclideanNorm N).comp measurable_snd))).2
      (Eventually.of_forall fun ω ↦
        gaussianEuclideanNorm_fixedWidthUnitDirection hN
          (fixedWidthRoundedVectorPathFrom ρ N y0 n ω))
  have hmulVec : Measurable
      (fun p : (((Fin n → ℝ) × (Fin N → ℝ)) ×
          (Fin N → Fin N → ℝ)) ↦ Matrix.mulVec p.2 p.1.2) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.measurable_sum
    intro j _
    exact ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp measurable_snd)).mul
        ((measurable_pi_apply j).comp
          (measurable_snd.comp measurable_fst))
  have hmarkMul : Measurable markMul :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_gaussianEuclideanNorm N).comp hmulVec)
  have hjoint :
      Measure.map
          (fun ω ↦
            (past ω, fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω)) μ =
        (Measure.map past μ).prod
          (fixedWidthRadialMultiplierLaw A N) := by
    have hmarked :=
      map_mark_mulVec_prod_eq_prod_radialMultiplierLaw A ν hν
    have hmapped :
        Measure.map markMul
            (Measure.map
              (fun ω ↦ ((past ω, direction ω), current ω)) μ) =
          Measure.map markMul (ν.prod (gaussianMat A N)) := by
      rw [hpair]
    rw [Measure.map_map hmarkMul
      ((hpast.prodMk hdirection).prodMk hcurrent)] at hmapped
    have hleft :
        markMul ∘ (fun ω ↦ ((past ω, direction ω), current ω)) =
          fun ω ↦
            (past ω, fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω) := by
      funext ω
      rfl
    rw [hleft, hmarked] at hmapped
    have hfst :
        Measure.map Prod.fst ν = Measure.map past μ := by
      dsimp [ν]
      rw [Measure.map_map measurable_fst (hpast.prodMk hdirection)]
      rfl
    rw [hfst] at hmapped
    exact hmapped
  refine (indepFun_iff_map_prod_eq_prod_map_map
    hpast.aemeasurable
    (measurable_fixedWidthRoundedRadiusMultiplierFrom
      hN ρ y0 n).aemeasurable).2 ?_
  rw [map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ y0 n]
  exact hjoint

/-- The exact-start rounded-radius multipliers form a mutually independent
process under the canonical matrix Gaussian law. -/
lemma iIndepFun_fixedWidthRoundedRadiusMultiplierFrom
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ) (y0 : Fin N → ℝ) :
    iIndepFun
      (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0)
      (fixedWidthMatrixGaussianMeasure A N) := by
  apply iIndepFun_of_iIndepFun_fin_prefix
  apply iIndepFun_fin_prefix_of_indepFun_prefix_next
  · exact fun n ↦
      measurable_fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n
  · intro n
    change IndepFun
      (fixedWidthRoundedRadiusMultiplierPrefixFrom hN ρ y0 n)
      (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n)
      (fixedWidthMatrixGaussianMeasure A N)
    exact indepFun_fixedWidthRoundedRadiusMultiplierPrefixFrom_next
      A hN ρ y0 n

/-- Every rounded-radius multiplier is identically distributed with its
time-zero coordinate. -/
lemma identDistrib_fixedWidthRoundedRadiusMultiplierFrom_zero
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ)
    (y0 : Fin N → ℝ) (n : ℕ) :
    IdentDistrib
      (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n)
      (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 0)
      (fixedWidthMatrixGaussianMeasure A N)
      (fixedWidthMatrixGaussianMeasure A N) :=
  ⟨(measurable_fixedWidthRoundedRadiusMultiplierFrom
      hN ρ y0 n).aemeasurable,
    (measurable_fixedWidthRoundedRadiusMultiplierFrom
      hN ρ y0 0).aemeasurable,
    (map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ y0 n).trans
      (map_fixedWidthRoundedRadiusMultiplierFrom A hN ρ y0 0).symm⟩

/-- The unrounded update fixes the zero vector. -/
@[simp] lemma Pstep_zero (N : ℕ) (W : Fin N → Fin N → ℝ) :
    Pstep N 0 W = 0 := by
  funext i
  simp [Pstep]

/-- The rounded radius satisfies the same affine multiplier domination as the
synchronous discrepancy, before rescaling by the mesh. -/
lemma fixedWidthRoundedVectorRadiusFrom_succ_le
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (y0 : Fin N → ℝ) (n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedVectorRadiusFrom ρ N y0 (n + 1) ω ≤
      fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω *
          fixedWidthRoundedVectorRadiusFrom ρ N y0 n ω +
        Real.sqrt N * (ρ / 2) := by
  calc
    fixedWidthRoundedVectorRadiusFrom ρ N y0 (n + 1) ω =
        gaussianEuclideanNorm N
          (roundedPstep ρ N
              (fixedWidthRoundedVectorPathFrom ρ N y0 n ω) (ω n) -
            Pstep N 0 (ω n)) := by
      simp only [fixedWidthRoundedVectorRadiusFrom,
        fixedWidthRoundedVectorPathFrom, Pstep_zero, sub_zero]
    _ ≤ gaussianEuclideanNorm N
          (Matrix.mulVec (ω n)
            (fixedWidthRoundedVectorPathFrom ρ N y0 n ω - 0)) +
        Real.sqrt N * (ρ / 2) :=
      gaussianEuclideanNorm_roundedPstep_sub_Pstep_le
        hρ N 0 (fixedWidthRoundedVectorPathFrom ρ N y0 n ω) (ω n)
    _ = fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω *
          fixedWidthRoundedVectorRadiusFrom ρ N y0 n ω +
        Real.sqrt N * (ρ / 2) := by
      rw [sub_zero, gaussianEuclideanNorm_mulVec_eq_multiplier_mul hN]
      rfl

/-- After division by the mesh, the rounded radius is dominated by an affine
recursion with additive term `sqrt N / 2`. -/
lemma fixedWidthRoundedGridRadiusFrom_succ_le
    {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} (hN : 0 < N)
    (y0 : Fin N → ℝ) (n : ℕ) (ω : fixedWidthMatrixSampleSpace N) :
    fixedWidthRoundedGridRadiusFrom ρ N y0 (n + 1) ω ≤
      fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω *
          fixedWidthRoundedGridRadiusFrom ρ N y0 n ω +
        Real.sqrt N / 2 := by
  have h := div_le_div_of_nonneg_right
    (fixedWidthRoundedVectorRadiusFrom_succ_le hρ hN y0 n ω) hρ.le
  change fixedWidthRoundedVectorRadiusFrom ρ N y0 (n + 1) ω / ρ ≤
    fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω *
        (fixedWidthRoundedVectorRadiusFrom ρ N y0 n ω / ρ) +
      Real.sqrt N / 2
  calc
    fixedWidthRoundedVectorRadiusFrom ρ N y0 (n + 1) ω / ρ ≤
        (fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω *
            fixedWidthRoundedVectorRadiusFrom ρ N y0 n ω +
          Real.sqrt N * (ρ / 2)) / ρ := h
    _ = fixedWidthRoundedRadiusMultiplierFrom hN ρ y0 n ω *
          (fixedWidthRoundedVectorRadiusFrom ρ N y0 n ω / ρ) +
        Real.sqrt N / 2 := by
      field_simp [hρ.ne']

end AbsorptionCutoff
