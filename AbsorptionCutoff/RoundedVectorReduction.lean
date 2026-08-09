/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.VectorReduction
import AbsorptionCutoff.DimensionCutoff

/-!
# Rounded vector chain and scalar reduction

Introduces the rounded vector transition kernel from paper `eq:rounded-chain`.
Subsequent results in this module will identify its normalized rounded squared-radius
observable with the scalar kernel `Hkernel`.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace AbsorptionCutoff

/-- Coordinatewise rounding `Qρ ρ` is measurable. -/
lemma measurable_Qρ (ρ : ℝ) (N : ℕ) : Measurable (Qρ ρ : (Fin N → ℝ) → Fin N → ℝ) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Qρ gridRound
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  have hdiv : Measurable (fun x : Fin N → ℝ => x i / ρ) :=
    (measurable_pi_apply i).div measurable_const
  exact measurable_const.mul
    (hcast.comp (measurable_Q₁.comp hdiv))

/-- **Rounded vector step map** `Q_ρ(tanh(𝖶x))` (paper `eq:rounded-chain`). -/
noncomputable def roundedPstep
    (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) (W : Fin N → Fin N → ℝ) : Fin N → ℝ :=
  Qρ ρ (Pstep N x W)

/-- `roundedPstep` is jointly measurable in the state and weight matrix. -/
lemma measurable_roundedPstep (ρ : ℝ) (N : ℕ) :
    Measurable
      (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) =>
        roundedPstep ρ N p.1 p.2) :=
  (measurable_Qρ ρ N).comp (measurable_Pstep N)

/-- **Rounded vector transition kernel** `P_{ρ,A,N}` (paper `eq:rounded-chain`):
`P_{ρ,A,N}(x,·)` is the law of `Q_ρ(tanh(𝖶x))` for `𝖶 ∼ gaussianMat A N`. -/
noncomputable def roundedPkernel
    (A ρ : ℝ) (N : ℕ) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  Kernel.map
    ((Kernel.deterministic id measurable_id).prod (Kernel.const _ (gaussianMat A N)))
    (fun p => roundedPstep ρ N p.1 p.2)

instance (A ρ : ℝ) (N : ℕ) : IsMarkovKernel (roundedPkernel A ρ N) := by
  unfold roundedPkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_roundedPstep ρ N)

/-- The rounded vector kernel at `x` is the pushforward of the weight-matrix law under
the rounded step map. -/
lemma roundedPkernel_apply (A ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    roundedPkernel A ρ N x = (gaussianMat A N).map (roundedPstep ρ N x) := by
  unfold roundedPkernel
  rw [Kernel.map_apply _ (measurable_roundedPstep ρ N), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, id_eq, Measure.dirac_prod,
    Measure.map_map (measurable_roundedPstep ρ N)
      (by fun_prop : Measurable (Prod.mk x))]
  rfl

/-- The unrounded step map is measurable in the weight matrix when the state is fixed. -/
lemma measurable_Pstep_right (N : ℕ) (x : Fin N → ℝ) :
    Measurable (Pstep N x) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Pstep
  apply continuous_tanh.measurable.comp
  apply Finset.measurable_sum
  intro j _
  have hrow : Measurable (fun W : Fin N → Fin N → ℝ => W i) :=
    measurable_pi_apply i
  have hentry : Measurable (fun W : Fin N → Fin N → ℝ => W i j) :=
    (measurable_pi_apply j).comp hrow
  exact hentry.mul measurable_const

/-- The rounded vector kernel is the unrounded vector kernel followed by
coordinatewise rounding. -/
lemma roundedPkernel_apply_eq_map (A ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    roundedPkernel A ρ N x = (Pkernel A N x).map (Qρ ρ) := by
  calc
    roundedPkernel A ρ N x =
        (gaussianMat A N).map (roundedPstep ρ N x) :=
      roundedPkernel_apply A ρ N x
    _ = (gaussianMat A N).map (Qρ ρ ∘ Pstep N x) := rfl
    _ = ((gaussianMat A N).map (Pstep N x)).map (Qρ ρ) :=
      (Measure.map_map (measurable_Qρ ρ N) (measurable_Pstep_right N x)).symm
    _ = (Pkernel A N x).map (Qρ ρ) :=
      congrArg (fun μ : Measure (Fin N → ℝ) => μ.map (Qρ ρ))
        (Pkernel_apply A N x).symm

/-- A rounded vector step from the zero vector is identically zero. -/
lemma roundedPstep_zero (ρ : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) :
    roundedPstep ρ N 0 W = 0 := by
  have hQ : Q₁ (0 : ℝ) = 0 := (Q₁_zero_iff 0).mpr (by norm_num)
  funext i
  simp [roundedPstep, Qρ, gridRound, Pstep, hQ]

/-- **The zero vector is absorbing for the rounded vector chain** (paper
`eq:rounded-chain`). -/
lemma isAbsorbing_roundedPkernel (A ρ : ℝ) (N : ℕ) :
    IsAbsorbing (roundedPkernel A ρ N) 0 := by
  rw [IsAbsorbing, roundedPkernel_apply]
  rw [show roundedPstep ρ N (0 : Fin N → ℝ) = fun _ => (0 : Fin N → ℝ) from
    funext (roundedPstep_zero ρ N)]
  rw [Measure.map_const]
  simp

/-- **Normalized rounded squared radius**
`\mathscr H(x) = (Nρ²)⁻¹ ∑ᵢ xᵢ²` (paper `eq:subcritical-exact-grid-radius`).
On vectors in the grid `(ρℤ)^N`, this is the empirical squared unit-grid radius. -/
noncomputable def roundedRadiusSq
    (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  ((N : ℝ) * ρ ^ 2)⁻¹ * ∑ i, (x i) ^ 2

/-- The normalized rounded squared-radius observable is measurable. -/
lemma measurable_roundedRadiusSq (ρ : ℝ) (N : ℕ) :
    Measurable (roundedRadiusSq ρ N) := by
  unfold roundedRadiusSq
  fun_prop

/-- Rescaling the normalized rounded squared radius by `ρ²` recovers the usual
normalized squared radius. This remains valid in the zero-dimensional case. -/
lemma sq_mul_roundedRadiusSq {ρ : ℝ} (hρ : 0 < ρ)
    (N : ℕ) (x : Fin N → ℝ) :
    ρ ^ 2 * roundedRadiusSq ρ N x = radiusSq N x := by
  unfold roundedRadiusSq radiusSq
  rw [mul_inv_rev]
  calc
    ρ ^ 2 * ((ρ ^ 2)⁻¹ * (N : ℝ)⁻¹ * ∑ i, (x i) ^ 2) =
        (ρ ^ 2 * (ρ ^ 2)⁻¹) * (N : ℝ)⁻¹ * ∑ i, (x i) ^ 2 := by ring
    _ = (N : ℝ)⁻¹ * ∑ i, (x i) ^ 2 := by
      rw [mul_inv_cancel₀ (pow_ne_zero 2 hρ.ne'), one_mul]

/-- Square-root form of the radius rescaling, matching the scale in `Jmap` to
the scale `ρ A √h` in the rounded scalar map `Hmap`. -/
lemma mul_sqrt_roundedRadiusSq {ρ : ℝ} (hρ : 0 < ρ)
    (N : ℕ) (x : Fin N → ℝ) :
    ρ * Real.sqrt (roundedRadiusSq ρ N x) = Real.sqrt (radiusSq N x) := by
  calc
    ρ * Real.sqrt (roundedRadiusSq ρ N x) =
        Real.sqrt (ρ ^ 2) * Real.sqrt (roundedRadiusSq ρ N x) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hρ]
    _ = Real.sqrt (ρ ^ 2 * roundedRadiusSq ρ N x) :=
      (Real.sqrt_mul (sq_nonneg ρ) _).symm
    _ = Real.sqrt (radiusSq N x) := by
      rw [sq_mul_roundedRadiusSq hρ]

/-- Pointwise identification of the rounded radius of the Gaussian reconstruction
with the scalar rounded random map `Hmap`. -/
lemma roundedInitialRadius_Jmap {ρ : ℝ} (hρ : 0 < ρ)
    (A : ℝ) (N : ℕ) (x g : Fin N → ℝ) :
    roundedInitialRadius ρ N (Jmap A N (radiusSq N x) g) =
      Hmap A ρ N (roundedRadiusSq ρ N x) g := by
  have hscale := mul_sqrt_roundedRadiusSq hρ N x
  have harg : ∀ i : Fin N,
      Real.tanh (A * Real.sqrt (radiusSq N x) * g i) / ρ =
        ρ⁻¹ * Real.tanh
          (ρ * A * Real.sqrt (roundedRadiusSq ρ N x) * g i) := by
    intro i
    have hpre :
        A * Real.sqrt (radiusSq N x) * g i =
          ρ * A * Real.sqrt (roundedRadiusSq ρ N x) * g i := by
      rw [← hscale]
      ring
    rw [hpre]
    field_simp
  unfold roundedInitialRadius Jmap Hmap
  apply congrArg ((N : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [harg i]

/-- Rounding a vector and then taking its normalized rounded squared radius gives
exactly the deterministic initial radius used by the scalar chain. -/
lemma roundedRadiusSq_Qρ (ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    roundedRadiusSq ρ N (Qρ ρ x) = roundedInitialRadius ρ N x := by
  have hQ : Q₁ (0 : ℝ) = 0 := (Q₁_zero_iff 0).mpr (by norm_num)
  by_cases hρ : ρ = 0
  · subst ρ
    simp [roundedRadiusSq, roundedInitialRadius, Qρ, gridRound, hQ]
  · unfold roundedRadiusSq roundedInitialRadius Qρ gridRound
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, mul_inv_rev]
    calc
      (ρ ^ 2)⁻¹ * (N : ℝ)⁻¹ *
          (ρ ^ 2 * ∑ i, ((Q₁ (x i / ρ) : ℤ) : ℝ) ^ 2) =
          (N : ℝ)⁻¹ * ((ρ ^ 2)⁻¹ * ρ ^ 2) *
            ∑ i, ((Q₁ (x i / ρ) : ℤ) : ℝ) ^ 2 := by ring
      _ = (N : ℝ)⁻¹ * ∑ i, ((Q₁ (x i / ρ) : ℤ) : ℝ) ^ 2 := by
        rw [inv_mul_cancel₀ (pow_ne_zero 2 hρ), mul_one]

/-- **One-step rounded vector-to-scalar factorization.** Pushing one rounded
vector transition forward by the normalized rounded squared radius gives exactly
the scalar rounded-radius kernel `Hkernel`. -/
theorem roundedRadiusSq_map_roundedPkernel {ρ : ℝ} (hρ : 0 < ρ)
    (A : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    (roundedPkernel A ρ N x).map (roundedRadiusSq ρ N) =
      Hkernel A ρ N (roundedRadiusSq ρ N x) := by
  have hJ : Measurable (Jmap A N (radiusSq N x)) := by
    apply measurable_pi_iff.mpr
    intro i
    unfold Jmap
    exact continuous_tanh.measurable.comp (by fun_prop)
  have hrounded :
      Measurable (roundedRadiusSq ρ N ∘ Qρ ρ) :=
    (measurable_roundedRadiusSq ρ N).comp (measurable_Qρ ρ N)
  have hpoint :
      (roundedRadiusSq ρ N ∘ Qρ ρ) ∘ Jmap A N (radiusSq N x) =
        Hmap A ρ N (roundedRadiusSq ρ N x) := by
    funext g
    exact (roundedRadiusSq_Qρ ρ N _).trans
      (roundedInitialRadius_Jmap hρ A N x g)
  calc
    (roundedPkernel A ρ N x).map (roundedRadiusSq ρ N) =
        ((Pkernel A N x).map (Qρ ρ)).map (roundedRadiusSq ρ N) :=
      congrArg (fun μ : Measure (Fin N → ℝ) => μ.map (roundedRadiusSq ρ N))
        (roundedPkernel_apply_eq_map A ρ N x)
    _ = (Pkernel A N x).map (roundedRadiusSq ρ N ∘ Qρ ρ) :=
      Measure.map_map (measurable_roundedRadiusSq ρ N) (measurable_Qρ ρ N)
    _ = (Jkernel A N (radiusSq N x)).map
        (roundedRadiusSq ρ N ∘ Qρ ρ) :=
      congrArg (fun μ : Measure (Fin N → ℝ) =>
        μ.map (roundedRadiusSq ρ N ∘ Qρ ρ))
        (Pkernel_eq_Jkernel_radiusSq A N x)
    _ = ((gaussianVec N).map (Jmap A N (radiusSq N x))).map
        (roundedRadiusSq ρ N ∘ Qρ ρ) :=
      congrArg (fun μ : Measure (Fin N → ℝ) =>
        μ.map (roundedRadiusSq ρ N ∘ Qρ ρ))
        (Jkernel_apply A N (radiusSq N x))
    _ = (gaussianVec N).map
        ((roundedRadiusSq ρ N ∘ Qρ ρ) ∘ Jmap A N (radiusSq N x)) :=
      Measure.map_map hrounded hJ
    _ = (gaussianVec N).map
        (Hmap A ρ N (roundedRadiusSq ρ N x)) := by rw [hpoint]
    _ = Hkernel A ρ N (roundedRadiusSq ρ N x) :=
      (Hkernel_apply A ρ N (roundedRadiusSq ρ N x)).symm

/-- Kernel form of the one-step rounded radius factorization. -/
lemma roundedPkernel_map_roundedRadiusSq {ρ : ℝ} (hρ : 0 < ρ)
    (A : ℝ) (N : ℕ) :
    (roundedPkernel A ρ N).map (roundedRadiusSq ρ N) =
      (Hkernel A ρ N).comap (roundedRadiusSq ρ N)
        (measurable_roundedRadiusSq ρ N) := by
  ext x
  rw [Kernel.map_apply _ (measurable_roundedRadiusSq ρ N),
    Kernel.comap_apply, roundedRadiusSq_map_roundedPkernel hρ]

/-- Measure-level one-step intertwining between the rounded vector chain and
the scalar rounded-radius chain. -/
lemma roundedRadiusSq_map_roundedPkernel_comp {ρ : ℝ} (hρ : 0 < ρ)
    (A : ℝ) (N : ℕ) (μ : Measure (Fin N → ℝ))
    [IsProbabilityMeasure μ] :
    ((roundedPkernel A ρ N) ∘ₘ μ).map (roundedRadiusSq ρ N) =
      (Hkernel A ρ N) ∘ₘ (μ.map (roundedRadiusSq ρ N)) := by
  rw [Measure.map_comp, roundedPkernel_map_roundedRadiusSq hρ,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  exact measurable_roundedRadiusSq ρ N

/-- **Rounded radius law at arbitrary times.** The normalized rounded squared
radius of the vector chain has exactly the law of the scalar `Hkernel` chain. -/
theorem roundedRadiusSq_map_roundedPkernel_pow {ρ : ℝ} (hρ : 0 < ρ)
    (A : ℝ) (N : ℕ) (x : Fin N → ℝ) (t : ℕ) :
    (((roundedPkernel A ρ N) ^ t) x).map (roundedRadiusSq ρ N) =
      ((Hkernel A ρ N) ^ t) (roundedRadiusSq ρ N x) := by
  induction t with
  | zero =>
    rw [pow_zero]
    change (Kernel.id x).map (roundedRadiusSq ρ N) =
      Kernel.id (roundedRadiusSq ρ N x)
    rw [Kernel.id_apply, Kernel.id_apply,
      Measure.map_dirac' (measurable_roundedRadiusSq ρ N)]
  | succ t ih =>
    rw [pow_succ' (roundedPkernel A ρ N), pow_succ' (Hkernel A ρ N)]
    change
      (((roundedPkernel A ρ N) ∘ₖ ((roundedPkernel A ρ N) ^ t)) x).map
          (roundedRadiusSq ρ N) =
        ((Hkernel A ρ N) ∘ₖ ((Hkernel A ρ N) ^ t))
          (roundedRadiusSq ρ N x)
    rw [Kernel.comp_apply, roundedRadiusSq_map_roundedPkernel_comp hρ, ih,
      Kernel.comp_apply]

/-- The normalized rounded squared radius vanishes exactly at the zero vector. -/
lemma roundedRadiusSq_eq_zero_iff {ρ : ℝ} (hρ : 0 < ρ)
    (N : ℕ) (x : Fin N → ℝ) :
    roundedRadiusSq ρ N x = 0 ↔ x = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst N
    constructor
    · intro _
      exact Subsingleton.elim _ _
    · intro _
      simp [roundedRadiusSq]
  · have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hnorm : ((N : ℝ) * ρ ^ 2)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero hNreal (pow_ne_zero 2 hρ.ne'))
    constructor
    · intro hx
      have hsum : ∑ i, (x i) ^ 2 = 0 := by
        unfold roundedRadiusSq at hx
        exact (mul_eq_zero.mp hx).resolve_left hnorm
      apply funext
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (x j))).mp hsum i (Finset.mem_univ i)
      exact (sq_eq_zero_iff).mp hi
    · intro hx
      subst x
      simp [roundedRadiusSq]

/-- The vector and scalar rounded chains have exactly the same survival mass
away from their absorbing origins at every time. -/
lemma roundedPkernel_pow_compl_singleton_zero_eq_Hkernel_pow
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) (N : ℕ)
    (x : Fin N → ℝ) (t : ℕ) :
    (((roundedPkernel A ρ N) ^ t) x) ({(0 : Fin N → ℝ)}ᶜ) =
      (((Hkernel A ρ N) ^ t) (roundedRadiusSq ρ N x)) ({(0 : ℝ)}ᶜ) := by
  have hpre :
      (roundedRadiusSq ρ N) ⁻¹' ({(0 : ℝ)}ᶜ) =
        ({(0 : Fin N → ℝ)}ᶜ) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact not_congr (roundedRadiusSq_eq_zero_iff hρ N y)
  calc
    (((roundedPkernel A ρ N) ^ t) x) ({(0 : Fin N → ℝ)}ᶜ) =
        (((roundedPkernel A ρ N) ^ t) x)
          ((roundedRadiusSq ρ N) ⁻¹' ({(0 : ℝ)}ᶜ)) := by rw [hpre]
    _ = ((((roundedPkernel A ρ N) ^ t) x).map
          (roundedRadiusSq ρ N)) ({(0 : ℝ)}ᶜ) :=
      (Measure.map_apply (measurable_roundedRadiusSq ρ N)
        (measurableSet_singleton (0 : ℝ)).compl).symm
    _ = (((Hkernel A ρ N) ^ t) (roundedRadiusSq ρ N x))
        ({(0 : ℝ)}ᶜ) := by
      rw [roundedRadiusSq_map_roundedPkernel_pow hρ]

/-- Canonical path-space survival identity for the rounded vector chain: the
coordinate-process absorption time exceeds `t` exactly with the `t`-step mass
away from the zero vector. -/
theorem measure_roundedVectorAbsorptionTime_gt_eq
    (A ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) (t : ℕ) :
    (markovPathMeasure (Measure.dirac x) (roundedPkernel A ρ N))
        {ω |
          (t : WithTop ℕ) <
            absorptionTime
              (fun (s : ℕ) (ω : ℕ → (Fin N → ℝ)) => ω s) ω} =
      ((roundedPkernel A ρ N) ^ t) x ({(0 : Fin N → ℝ)}ᶜ) :=
  measure_absorptionTime_gt_eq_of_ae_kernel_pow
    (X := fun (s : ℕ) (ω : ℕ → (Fin N → ℝ)) => ω s)
    (κ := roundedPkernel A ρ N) (x := x)
    (fun s =>
      markovPathMeasure_ae_absorbing
        (Measure.dirac x) (roundedPkernel A ρ N)
        (isAbsorbing_roundedPkernel A ρ N) s)
    t (measurable_pi_apply t)
    (markovPathMeasure_dirac_map_eval x (roundedPkernel A ρ N) t)

/-- The total-variation distance of the rounded vector chain from the absorbing
zero vector is its survival mass away from zero. -/
lemma tvDist_roundedPkernel_pow_dirac
    (A ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) (t : ℕ) :
    tvDist (((roundedPkernel A ρ N) ^ t) x)
        (Measure.dirac (0 : Fin N → ℝ)) =
      ((((roundedPkernel A ρ N) ^ t) x)
        ({(0 : Fin N → ℝ)}ᶜ)).toReal :=
  tvDist_pow_dirac (measurableSet_singleton (0 : Fin N → ℝ)) x t

/-- The rounded-vector TV distance from the absorbing origin equals the
canonical path-space survival probability of its absorption time. -/
theorem tvDist_roundedPkernel_pow_eq_survival
    (A ρ : ℝ) (N : ℕ) (x : Fin N → ℝ) (t : ℕ) :
    tvDist (((roundedPkernel A ρ N) ^ t) x)
        (Measure.dirac (0 : Fin N → ℝ)) =
      ((markovPathMeasure (Measure.dirac x) (roundedPkernel A ρ N))
        {ω |
          (t : WithTop ℕ) <
            absorptionTime
              (fun (s : ℕ) (ω : ℕ → (Fin N → ℝ)) => ω s) ω}).toReal := by
  rw [tvDist_roundedPkernel_pow_dirac,
    measure_roundedVectorAbsorptionTime_gt_eq]

/-- The rounded vector chain and its scalar rounded-radius reduction have
exactly the same total-variation distance from their absorbing origins. -/
lemma tvDist_roundedPkernel_pow_eq_Hkernel_pow
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) (N : ℕ)
    (x : Fin N → ℝ) (t : ℕ) :
    tvDist (((roundedPkernel A ρ N) ^ t) x)
        (Measure.dirac (0 : Fin N → ℝ)) =
      tvDist (((Hkernel A ρ N) ^ t) (roundedRadiusSq ρ N x))
        (Measure.dirac (0 : ℝ)) := by
  rw [tvDist_roundedPkernel_pow_dirac, tvDist_Hkernel_pow_dirac,
    roundedPkernel_pow_compl_singleton_zero_eq_Hkernel_pow hρ]

/-- **Fixed-precision subcritical dimension cutoff for the rounded vector
chain.** At the deterministic rounded-map center, the vector-chain TV distance
from the absorbing zero vector drops from one to zero in the paper's bounded
window `[\bar t_N - 1, \bar t_N + 2]`. -/
theorem subcritical_dimension_cutoff_roundedVector
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1)
    (htime :
      Filter.Tendsto
        (fun N : ℕ => roundedDimensionCutoffTime A ρ N (x N))
        Filter.atTop Filter.atTop) :
    Filter.Tendsto
        (fun N : ℕ =>
          tvDist
            (((roundedPkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) - 1))
              (Qρ ρ (x N)))
            (Measure.dirac (0 : Fin N → ℝ)))
        Filter.atTop (𝓝 1) ∧
      Filter.Tendsto
        (fun N : ℕ =>
          tvDist
            (((roundedPkernel A ρ N) ^
                (roundedDimensionCutoffTime A ρ N (x N) + 2))
              (Qρ ρ (x N)))
            (Measure.dirac (0 : Fin N → ℝ)))
        Filter.atTop (𝓝 0) := by
  have hscalar :=
    (subcritical_dimension_cutoff hA hA_lt hρ hρ_lt x hx htime).2
  constructor
  · simpa only [tvDist_roundedPkernel_pow_eq_Hkernel_pow hρ,
      roundedRadiusSq_Qρ] using hscalar.1
  · simpa only [tvDist_roundedPkernel_pow_eq_Hkernel_pow hρ,
      roundedRadiusSq_Qρ] using hscalar.2

/-- Mixing-time consequence of the rounded-vector fixed-precision cutoff. For
every fixed `ε ∈ (0,1)`, the vector mixing time lies in the same eventual
bounded window as the scalar rounded-radius chain. -/
theorem subcritical_dimension_cutoff_roundedVector_mixingTime_bounds
    {A ρ : ℝ}
    (hA : 0 < A) (hA_lt : A < latticeThreshold)
    (hρ : 0 < ρ) (hρ_lt : ρ < 1)
    (x : ∀ N : ℕ, Fin N → ℝ)
    (hx : ∀ N : ℕ, ∀ i : Fin N, |x N i| ≤ 1)
    (htime :
      Filter.Tendsto
        (fun N : ℕ => roundedDimensionCutoffTime A ρ N (x N))
        Filter.atTop Filter.atTop)
    {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((roundedDimensionCutoffTime A ρ N (x N) - 1 : ℕ) : ℕ∞) <
          mixingTime
            (dSeq (roundedPkernel A ρ N) (Qρ ρ (x N))
              (Measure.dirac (0 : Fin N → ℝ)))
            ε ∧
        mixingTime
            (dSeq (roundedPkernel A ρ N) (Qρ ρ (x N))
              (Measure.dirac (0 : Fin N → ℝ)))
            ε ≤
          ((roundedDimensionCutoffTime A ρ N (x N) + 2 : ℕ) : ℕ∞) := by
  have hscalar :=
    subcritical_dimension_cutoff_mixingTime_bounds
      hA hA_lt hρ hρ_lt x hx htime hε hε_lt
  filter_upwards [hscalar] with N hN
  have hdseq :
      dSeq (roundedPkernel A ρ N) (Qρ ρ (x N))
          (Measure.dirac (0 : Fin N → ℝ)) =
        dSeq (Hkernel A ρ N) (roundedInitialRadius ρ N (x N))
          (Measure.dirac (0 : ℝ)) := by
    funext t
    unfold dSeq
    simpa only [roundedRadiusSq_Qρ] using
      (tvDist_roundedPkernel_pow_eq_Hkernel_pow
        hρ A N (Qρ ρ (x N)) t)
  rw [hdseq]
  exact hN

end AbsorptionCutoff
