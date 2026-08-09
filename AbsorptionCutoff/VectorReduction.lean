/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Chains
import AbsorptionCutoff.GaussianSum

/-!
# Reduction to the squared-radius chain

Formalizes the paper's §2 (`subsec:vector-radius-kernels`) reduction
`prop:gaussian-tv-reduction`: after one Gaussian step the vector law depends on the
previous state only through its normalized squared radius `r_N(x) = N⁻¹‖x‖₂²`, which
factorizes the vector kernel through the scalar squared-radius kernel `K_{A,N}` (`Kchain`)
and the reconstruction kernel `J_{A,N}`.

## Main definitions
* `AbsorptionCutoff.radiusSq N x` — the normalized squared radius `r_N(x) = N⁻¹∑ᵢ xᵢ²`.
* `AbsorptionCutoff.Jmap A N q g` — the reconstruction map `(tanh(A√q·gᵢ))ᵢ`.
* `AbsorptionCutoff.Jkernel A N` — the **reconstruction kernel** `J_{A,N}` on `ℝ → (Fin N → ℝ)`:
  `J(q,·)` is the law of `(tanh(A√q·Gᵢ))ᵢ`, `G ∼ 𝒢_N`. A Markov kernel.

## Main results (this file, so far)
* `AbsorptionCutoff.radiusSq_Jmap` — `r_N ∘ (reconstruction) = F_{A,N}` pointwise, the pointwise
  seed of `(r_N)_#J_{A,N}(q,·) = K_{A,N}(q,·)`.
-/

open MeasureTheory ProbabilityTheory BigOperators

namespace AbsorptionCutoff

/-- **Normalized squared radius** `r_N(x) = N⁻¹‖x‖₂² = N⁻¹∑ᵢ xᵢ²` (paper: `r_N(x)`). The
observable through which the one-step vector law depends on the current state. -/
noncomputable def radiusSq (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (x i) ^ 2

lemma measurable_radiusSq (N : ℕ) : Measurable (radiusSq N) := by
  unfold radiusSq
  fun_prop

/-- In positive dimension, the normalized squared radius vanishes exactly at the zero
vector. -/
lemma radiusSq_eq_zero_iff {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    radiusSq N x = 0 ↔ x = 0 := by
  have hN0 : (N : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))
  constructor
  · intro hx
    have hsum : ∑ i, (x i) ^ 2 = 0 := by
      exact (mul_eq_zero.mp (show (N : ℝ)⁻¹ * ∑ i, (x i) ^ 2 = 0 from hx)).resolve_left hN0
    funext i
    have hi : (x i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp hsum i
        (Finset.mem_univ i)
    simpa only [Pi.zero_apply] using sq_eq_zero_iff.mp hi
  · rintro rfl
    simp [radiusSq]

/-- In positive dimension, pushing a vector measure forward by the normalized squared
radius preserves its atom at the origin. -/
lemma map_radiusSq_apply_singleton_zero {N : ℕ} (hN : 0 < N)
    (π : Measure (Fin N → ℝ)) :
    (π.map (radiusSq N)) ({0} : Set ℝ) = π ({0} : Set (Fin N → ℝ)) := by
  rw [Measure.map_apply (measurable_radiusSq N) (measurableSet_singleton 0)]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, radiusSq_eq_zero_iff hN]

/-- The **reconstruction map** `(tanh(A√q·gᵢ))ᵢ` — one coordinate of the vector step map
`tanh(𝖶x)` after the Gaussian isotropy `𝖶x =ᵈ A√(r_N(x))·G` (paper proof of
`prop:gaussian-tv-reduction`). -/
noncomputable def Jmap (A : ℝ) (N : ℕ) (q : ℝ) (g : Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.tanh (A * Real.sqrt q * g i)

/-- `J_{A,N}` is jointly measurable in `(q, g)` (each coordinate is continuous). -/
lemma measurable_Jmap (A : ℝ) (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => Jmap A N p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Jmap
  exact continuous_tanh.measurable.comp (by fun_prop)

/-- **Reconstruction kernel** `J_{A,N}` on `ℝ → (Fin N → ℝ)` (paper
`subsec:vector-radius-kernels`): `J(q,·)` is the law of `(tanh(A√q·Gᵢ))ᵢ`, `G ∼ 𝒢_N`.
Built as the pushforward of `δ_q ⊗ 𝒢_N` under the joint reconstruction map. A Markov
kernel. -/
noncomputable def Jkernel (A : ℝ) (N : ℕ) : Kernel ℝ (Fin N → ℝ) :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const ℝ (gaussianVec N)))
    (fun p => Jmap A N p.1 p.2)

instance (A : ℝ) (N : ℕ) : IsMarkovKernel (Jkernel A N) := by
  unfold Jkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_Jmap A N)

/-- **Pointwise seed of the radius factorization**: the normalized squared radius of the
reconstruction is exactly the squared-radius random map, `r_N(Jmap A N q g) = F_{A,N}(q,g)`.
This is what makes `(r_N)_#J_{A,N}(q,·) = K_{A,N}(q,·)` hold (paper:
`(r_N)_#J_{A,N}(q,·) = K_{A,N}(q,·)`). -/
lemma radiusSq_Jmap (A : ℝ) (N : ℕ) (q : ℝ) (g : Fin N → ℝ) :
    radiusSq N (Jmap A N q g) = Fmap A N q g :=
  rfl

/-- The reconstruction kernel at `q` is the pushforward of the Gaussian vector `𝒢_N` under
the reconstruction map: `J_{A,N}(q,·) = (𝒢_N)_#(Jmap A N q)`. Reduces the
`deterministic ⊗ const` construction the same way as `isAbsorbing_Hkernel`. -/
lemma Jkernel_apply (A : ℝ) (N : ℕ) (q : ℝ) :
    Jkernel A N q = (gaussianVec N).map (Jmap A N q) := by
  unfold Jkernel
  rw [Kernel.map_apply _ (measurable_Jmap A N), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, id_eq, Measure.dirac_prod,
    Measure.map_map (measurable_Jmap A N) (by fun_prop : Measurable (Prod.mk q))]
  rfl

/-- The squared-radius kernel at `q` is the pushforward of `𝒢_N` under the squared-radius
random map: `K_{A,N}(q,·) = (𝒢_N)_#(F_{A,N}(q,·))`. Companion of `Jkernel_apply` for
`Kchain`. -/
lemma Kchain_apply (A : ℝ) (N : ℕ) (q : ℝ) :
    Kchain A N q = (gaussianVec N).map (Fmap A N q) := by
  unfold Kchain
  rw [Kernel.map_apply _ (measurable_Fmap A N), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, id_eq, Measure.dirac_prod,
    Measure.map_map (measurable_Fmap A N) (by fun_prop : Measurable (Prod.mk q))]
  rfl

/-- **Radius factorization of the reconstruction kernel** (paper: `(r_N)_#J_{A,N}(q,·) =
K_{A,N}(q,·)`): pushing the reconstruction kernel forward under the normalized squared
radius recovers the scalar squared-radius kernel. This is the identity that drives the
induction `(r_N)_#P_{A,N}^t(x,·)=K_{A,N}^t(q,·)` in `prop:gaussian-tv-reduction`. -/
lemma radiusSq_map_Jkernel (A : ℝ) (N : ℕ) (q : ℝ) :
    (Jkernel A N q).map (radiusSq N) = Kchain A N q := by
  have hJq : Measurable (Jmap A N q) := by
    apply measurable_pi_iff.mpr
    intro i
    unfold Jmap
    exact continuous_tanh.measurable.comp (by fun_prop)
  calc (Jkernel A N q).map (radiusSq N)
      = ((gaussianVec N).map (Jmap A N q)).map (radiusSq N) := by rw [Jkernel_apply]
    _ = (gaussianVec N).map (radiusSq N ∘ Jmap A N q) :=
        Measure.map_map (measurable_radiusSq N) hJq
    _ = (gaussianVec N).map (Fmap A N q) := by congr 1
    _ = Kchain A N q := (Kchain_apply A N q).symm

/-- **Kernel form of the reconstruction radius factorization**: mapping `J_{A,N}` by
`r_N` gives exactly the scalar kernel `K_{A,N}`. -/
lemma Jkernel_map_radiusSq (A : ℝ) (N : ℕ) :
    (Jkernel A N).map (radiusSq N) = Kchain A N := by
  ext q
  rw [Kernel.map_apply _ (measurable_radiusSq N), radiusSq_map_Jkernel]

/-- The radius law of a vector distribution reconstructed from a scalar law `ν` is
exactly the result of evolving `ν` by `K_{A,N}`. This is the identity
`(r_N)_#(νJ)=νK` used in both directions of the invariant-law transfer. -/
lemma radiusSq_map_Jkernel_comp (A : ℝ) (N : ℕ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] :
    ((Jkernel A N) ∘ₘ ν).map (radiusSq N) = (Kchain A N) ∘ₘ ν := by
  rw [Measure.map_comp ν (Jkernel A N) (measurable_radiusSq N),
    Jkernel_map_radiusSq]

/-- Variance `A²/N` of a single Gaussian weight `(𝖶_{A}^{(N)})_{ij} ∼ 𝒩(0, A²/N)`
(paper `eq:gaussian-weights`), as an `ℝ≥0`. -/
noncomputable def weightVar (A : ℝ) (N : ℕ) : NNReal := (A ^ 2 / N).toNNReal

/-- The **Gaussian weight matrix law**: an `N×N` matrix (as `Fin N → Fin N → ℝ`) with
independent entries `∼ 𝒩(0, A²/N)` (paper `eq:gaussian-weights`). -/
noncomputable def gaussianMat (A : ℝ) (N : ℕ) : Measure (Fin N → Fin N → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 (weightVar A N)))

instance (A : ℝ) (N : ℕ) : IsProbabilityMeasure (gaussianMat A N) := by
  unfold gaussianMat; infer_instance

/-- The **vector step map** `tanh(𝖶x)` applied coordinatewise: `(𝖶x)ᵢ = ∑ⱼ 𝖶ᵢⱼ xⱼ`
(paper `eq:unrounded-chain`). -/
noncomputable def Pstep (N : ℕ) (x : Fin N → ℝ) (W : Fin N → Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.tanh (∑ j, W i j * x j)

/-- `Pstep` is jointly measurable in `(x, 𝖶)` (each coordinate is continuous). -/
lemma measurable_Pstep (N : ℕ) :
    Measurable (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) => Pstep N p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Pstep
  apply continuous_tanh.measurable.comp
  apply Finset.measurable_sum
  intro j _
  fun_prop

/-- **Unrounded vector transition kernel** `P_{A,N}` on `Fin N → ℝ` (paper
`eq:unrounded-chain`): `P(x,·)` is the law of `tanh(𝖶x)`, `𝖶 ∼ gaussianMat A N`. Built as
the pushforward of `δ_x ⊗ gaussianMat A N` under the step map. A Markov kernel. -/
noncomputable def Pkernel (A : ℝ) (N : ℕ) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const _ (gaussianMat A N)))
    (fun p => Pstep N p.1 p.2)

instance (A : ℝ) (N : ℕ) : IsMarkovKernel (Pkernel A N) := by
  unfold Pkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_Pstep N)

/-- The vector kernel at `x` is the pushforward of the weight-matrix law under the step
map: `P_{A,N}(x,·) = (gaussianMat A N)_#(Pstep N x)`. Companion of `Jkernel_apply`. -/
lemma Pkernel_apply (A : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    Pkernel A N x = (gaussianMat A N).map (Pstep N x) := by
  unfold Pkernel
  rw [Kernel.map_apply _ (measurable_Pstep N), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, id_eq, Measure.dirac_prod,
    Measure.map_map (measurable_Pstep N) (by fun_prop : Measurable (Prod.mk x))]
  rfl

/-- **Row assembly of the Gaussian isotropy** (paper: `𝖶x` has law `A√(r_N x)·G`). Pushing
the weight-matrix law through the linear part `𝖶 ↦ (∑ⱼ 𝖶ᵢⱼxⱼ)ᵢ` of the step map gives the
i.i.d. Gaussian vector with per-coordinate variance `A²·r_N(x)`: the rows are independent
(product structure), and each row is the scalar isotropy `map_sum_mul_gaussianPi` at
variance `weightVar A N = A²/N`, whose `(∑xⱼ²)·(A²/N) = A²·r_N(x)`. -/
lemma map_rowMap_gaussianMat (A : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    (gaussianMat A N).map (fun W i => ∑ j, W i j * x j)
      = Measure.pi (fun _ : Fin N => gaussianReal 0 ((A ^ 2 * radiusSq N x).toNNReal)) := by
  have hvar : (∑ j, (x j) ^ 2).toNNReal * weightVar A N
      = (A ^ 2 * radiusSq N x).toNNReal := by
    rw [weightVar, ← Real.toNNReal_mul (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))]
    congr 1
    unfold radiusSq
    ring
  unfold gaussianMat
  haveI : ∀ _i : Fin N, IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin N => gaussianReal 0 (weightVar A N))).map
        (fun w : Fin N → ℝ => ∑ j, w j * x j)) :=
    fun _ => Measure.isProbabilityMeasure_map
      (by fun_prop : Measurable (fun w : Fin N → ℝ => ∑ j, w j * x j)).aemeasurable
  rw [Measure.pi_map_pi
    (fun _ => (by fun_prop : Measurable (fun w : Fin N → ℝ => ∑ j, w j * x j)).aemeasurable)]
  congr 1
  funext i
  rw [map_sum_mul_gaussianPi (weightVar A N) x, hvar]

lemma radiusSq_nonneg (N : ℕ) (x : Fin N → ℝ) : 0 ≤ radiusSq N x := by
  unfold radiusSq; positivity

/-- Scaling identity for the reconstruction coordinate: the law of `tanh(A√q·G)` with
`G ∼ 𝒩(0,1)` equals `tanh` pushed forward from `𝒩(0, A²q)` (for `q ≥ 0`). Bridges the
reconstruction side (variance `1`, scale inside `tanh`) and the vector side (variance
`A²q`, bare `tanh`). -/
lemma map_tanh_scale_gaussian (A q : ℝ) (hq : 0 ≤ q) :
    (gaussianReal 0 1).map (fun g => Real.tanh (A * Real.sqrt q * g))
      = (gaussianReal 0 (A ^ 2 * q).toNNReal).map Real.tanh := by
  have hinner : (gaussianReal 0 1).map (fun g => (A * Real.sqrt q) * g)
      = gaussianReal 0 (A ^ 2 * q).toNNReal := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · rw [mul_one, show A ^ 2 * q = (A * Real.sqrt q) ^ 2 by rw [mul_pow, Real.sq_sqrt hq]]
      exact (Real.toNNReal_of_nonneg (sq_nonneg _)).symm
  calc (gaussianReal 0 1).map (fun g => Real.tanh (A * Real.sqrt q * g))
      = (gaussianReal 0 1).map (Real.tanh ∘ (fun g => (A * Real.sqrt q) * g)) := rfl
    _ = ((gaussianReal 0 1).map (fun g => (A * Real.sqrt q) * g)).map Real.tanh :=
        (Measure.map_map continuous_tanh.measurable (by fun_prop)).symm
    _ = (gaussianReal 0 (A ^ 2 * q).toNNReal).map Real.tanh := by rw [hinner]

/-- The reconstruction kernel as an explicit product measure: each coordinate is the law of
`tanh(A√q·G)`, `G ∼ 𝒩(0,1)` (paper: `J_{A,N}(q,·)` is the law of `(tanh(A√q·Gᵢ))ᵢ`). -/
lemma Jkernel_apply_pi (A : ℝ) (N : ℕ) (q : ℝ) :
    Jkernel A N q
      = Measure.pi (fun _ : Fin N =>
          (gaussianReal 0 1).map (fun g => Real.tanh (A * Real.sqrt q * g))) := by
  rw [Jkernel_apply]
  unfold gaussianVec Jmap
  haveI : ∀ _i : Fin N, IsProbabilityMeasure
      ((gaussianReal 0 1).map (fun g : ℝ => Real.tanh (A * Real.sqrt q * g))) :=
    fun _ => Measure.isProbabilityMeasure_map
      (continuous_tanh.measurable.comp (by fun_prop)).aemeasurable
  rw [Measure.pi_map_pi (fun _ =>
    (show Measurable (fun g : ℝ => Real.tanh (A * Real.sqrt q * g)) from
      continuous_tanh.measurable.comp (by fun_prop)).aemeasurable)]

/-- **Gaussian isotropy / vector kernel factorization** (paper
`eq:gaussian-vector-kernel-factorization`): the unrounded vector kernel depends on the
state only through its normalized squared radius, `P_{A,N}(x,·) = J_{A,N}(r_N(x),·)`. Since
`𝖶x =ᵈ A√(r_N x)·G`, applying `tanh` coordinatewise identifies the two laws. Combines the
row assembly `map_rowMap_gaussianMat`, the reconstruction product form `Jkernel_apply_pi`,
and the coordinate scaling `map_tanh_scale_gaussian`. -/
theorem Pkernel_eq_Jkernel_radiusSq (A : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    Pkernel A N x = Jkernel A N (radiusSq N x) := by
  have htanh : Measurable (fun v : Fin N → ℝ => fun i => Real.tanh (v i)) := by
    apply measurable_pi_iff.mpr; intro i
    exact continuous_tanh.measurable.comp (measurable_pi_apply i)
  have hrow : Measurable (fun W : Fin N → Fin N → ℝ => fun i => ∑ j, W i j * x j) := by
    apply measurable_pi_iff.mpr; intro i; apply Finset.measurable_sum; intro j _; fun_prop
  have hstep : Pstep N x
      = (fun v : Fin N → ℝ => fun i => Real.tanh (v i)) ∘ (fun W i => ∑ j, W i j * x j) := by
    funext W i; rfl
  rw [Pkernel_apply, hstep, ← Measure.map_map htanh hrow, map_rowMap_gaussianMat]
  haveI : ∀ _i : Fin N, IsProbabilityMeasure
      ((gaussianReal 0 (A ^ 2 * radiusSq N x).toNNReal).map Real.tanh) :=
    fun _ => Measure.isProbabilityMeasure_map continuous_tanh.measurable.aemeasurable
  rw [Measure.pi_map_pi (fun _ => continuous_tanh.measurable.aemeasurable), Jkernel_apply_pi]
  congr 1
  funext i
  exact (map_tanh_scale_gaussian A (radiusSq N x) (radiusSq_nonneg N x)).symm

/-- **Kernel form of the vector factorization**: `P_{A,N}` is the reconstruction kernel
`J_{A,N}` pulled back along the current normalized squared radius. This is the
compositional form used for the first identity in `eq:gaussian-vector-radius-laws`. -/
lemma Pkernel_eq_Jkernel_comap_radiusSq (A : ℝ) (N : ℕ) :
    Pkernel A N = (Jkernel A N).comap (radiusSq N) (measurable_radiusSq N) := by
  ext x
  rw [Kernel.comap_apply, Pkernel_eq_Jkernel_radiusSq]

/-- **Measure-level vector factorization**: one `P_{A,N}` step from any vector
distribution is obtained by pushing that distribution to its radius law and then applying
the reconstruction kernel `J_{A,N}`. -/
lemma Pkernel_comp_eq_Jkernel_comp_map_radiusSq (A : ℝ) (N : ℕ)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ] :
    (Pkernel A N) ∘ₘ μ = (Jkernel A N) ∘ₘ (μ.map (radiusSq N)) := by
  rw [Pkernel_eq_Jkernel_comap_radiusSq,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

/-- **One-step radius law** (`t=1` case of `eq:gaussian-vector-radius-laws`): the normalized
squared radius pushes the one-step vector law to the scalar squared-radius kernel,
`(r_N)_# P_{A,N}(x,·) = K_{A,N}(r_N(x),·)`. Immediate from the isotropy factorization
`Pkernel_eq_Jkernel_radiusSq` followed by the radius factorization `radiusSq_map_Jkernel`. -/
lemma radiusSq_map_Pkernel (A : ℝ) (N : ℕ) (x : Fin N → ℝ) :
    (Pkernel A N x).map (radiusSq N) = Kchain A N (radiusSq N x) := by
  rw [Pkernel_eq_Jkernel_radiusSq, radiusSq_map_Jkernel]

/-- **Kernel form of the one-step radius law**: mapping the vector transition kernel by
`r_N` is the scalar transition kernel pulled back along `r_N`. This is the compositional
form used to lift the one-step law to arbitrary initial measures and then to kernel powers. -/
lemma Pkernel_map_radiusSq (A : ℝ) (N : ℕ) :
    (Pkernel A N).map (radiusSq N)
      = (Kchain A N).comap (radiusSq N) (measurable_radiusSq N) := by
  ext x
  rw [Kernel.map_apply _ (measurable_radiusSq N),
    Kernel.comap_apply, radiusSq_map_Pkernel]

/-- **Measure-level one-step radius intertwining**: evolving a vector distribution by
`P_{A,N}` and then taking `r_N` has the same law as first taking `r_N` and then evolving
by `K_{A,N}`. This is the induction step for the radius law at arbitrary times. -/
lemma radiusSq_map_Pkernel_comp (A : ℝ) (N : ℕ) (μ : Measure (Fin N → ℝ))
    [IsProbabilityMeasure μ] :
    ((Pkernel A N) ∘ₘ μ).map (radiusSq N)
      = (Kchain A N) ∘ₘ (μ.map (radiusSq N)) := by
  rw [Measure.map_comp, Pkernel_map_radiusSq,
    ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  exact measurable_radiusSq N

/-- **Radius law at arbitrary times** (second identity in
`eq:gaussian-vector-radius-laws`): if the vector chain starts from `x`, then its
normalized squared radius after `t` steps has law `K_{A,N}^t(r_N(x), ·)`. -/
theorem radiusSq_map_Pkernel_pow (A : ℝ) (N : ℕ) (x : Fin N → ℝ) (t : ℕ) :
    (((Pkernel A N) ^ t) x).map (radiusSq N)
      = ((Kchain A N) ^ t) (radiusSq N x) := by
  induction t with
  | zero =>
    rw [pow_zero]
    change (Kernel.id x).map (radiusSq N) = Kernel.id (radiusSq N x)
    rw [Kernel.id_apply, Kernel.id_apply, Measure.map_dirac' (measurable_radiusSq N)]
  | succ t ih =>
    rw [pow_succ' (Pkernel A N), pow_succ' (Kchain A N)]
    change (((Pkernel A N) ∘ₖ ((Pkernel A N) ^ t)) x).map (radiusSq N)
      = ((Kchain A N) ∘ₖ ((Kchain A N) ^ t)) (radiusSq N x)
    rw [Kernel.comp_apply, radiusSq_map_Pkernel_comp, ih, Kernel.comp_apply]

/-- **Vector law at positive times** (first identity in
`eq:gaussian-vector-radius-laws`, in successor form): after `t+1` vector steps, the law
is obtained by evolving the initial radius for `t` scalar steps and then reconstructing
through `J_{A,N}`. -/
theorem Pkernel_pow_succ_eq_Jkernel_comp_Kchain_pow
    (A : ℝ) (N : ℕ) (x : Fin N → ℝ) (t : ℕ) :
    ((Pkernel A N) ^ (t + 1)) x
      = (Jkernel A N) ∘ₘ (((Kchain A N) ^ t) (radiusSq N x)) := by
  rw [pow_succ' (Pkernel A N)]
  change ((Pkernel A N) ∘ₖ ((Pkernel A N) ^ t)) x
    = (Jkernel A N) ∘ₘ (((Kchain A N) ^ t) (radiusSq N x))
  rw [Kernel.comp_apply, Pkernel_comp_eq_Jkernel_comp_map_radiusSq,
    radiusSq_map_Pkernel_pow]

/-- **Invariant-law transfer, scalar to vector** (first direction in
`prop:gaussian-tv-reduction`): if `ν` is invariant for the squared-radius kernel
`K_{A,N}`, then the reconstructed law `νJ_{A,N}` is invariant for the vector kernel
`P_{A,N}`. This is the paper's identity `(νJ)P = (νK)J = νJ`. -/
theorem invariant_Pkernel_of_invariant_Kchain
    (A : ℝ) (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν) :
    Kernel.Invariant (Pkernel A N) ((Jkernel A N) ∘ₘ ν) := by
  unfold Kernel.Invariant
  rw [Pkernel_comp_eq_Jkernel_comp_map_radiusSq,
    radiusSq_map_Jkernel_comp, hν]

/-- **Invariant vector laws are reconstructed from their radius laws**: if `π` is
invariant for `P_{A,N}`, then `π = ((r_N)_#π)J_{A,N}`. This is the middle equality
`π = πP = νJ` in the converse direction of the paper's invariant-law transfer. -/
theorem eq_Jkernel_comp_map_radiusSq_of_invariant_Pkernel
    (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π) :
    π = (Jkernel A N) ∘ₘ (π.map (radiusSq N)) := by
  calc
    π = (Pkernel A N) ∘ₘ π := hπ.def.symm
    _ = (Jkernel A N) ∘ₘ (π.map (radiusSq N)) :=
      Pkernel_comp_eq_Jkernel_comp_map_radiusSq A N π

/-- **Invariant-law transfer, vector to scalar** (second direction in
`prop:gaussian-tv-reduction`): the normalized squared-radius pushforward of every
`P_{A,N}`-invariant vector law is invariant for `K_{A,N}`. This is obtained by applying
`(r_N)_#` to the paper's equality `πP = π`. -/
theorem invariant_Kchain_map_radiusSq_of_invariant_Pkernel
    (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π) :
    Kernel.Invariant (Kchain A N) (π.map (radiusSq N)) := by
  unfold Kernel.Invariant
  calc
    (Kchain A N) ∘ₘ (π.map (radiusSq N))
        = ((Pkernel A N) ∘ₘ π).map (radiusSq N) :=
          (radiusSq_map_Pkernel_comp A N π).symm
    _ = π.map (radiusSq N) := congrArg (fun μ => μ.map (radiusSq N)) hπ.def

/-- **Lower half of the Gaussian TV bracket** (`eq:gaussian-tv-bracket`): observing the
normalized squared radius contracts total variation, so the scalar-chain distance from
`ν` is at most the vector-chain distance from its reconstructed invariant law `νJ`. -/
theorem tvDist_Kchain_pow_le_Pkernel_pow
    (A : ℝ) (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Kernel.Invariant (Kchain A N) ν) (x : Fin N → ℝ) (t : ℕ) :
    tvDist (((Kchain A N) ^ t) (radiusSq N x)) ν
      ≤ tvDist (((Pkernel A N) ^ t) x) ((Jkernel A N) ∘ₘ ν) := by
  calc
    tvDist (((Kchain A N) ^ t) (radiusSq N x)) ν
        = tvDist ((((Pkernel A N) ^ t) x).map (radiusSq N))
            (((Jkernel A N) ∘ₘ ν).map (radiusSq N)) := by
          rw [radiusSq_map_Pkernel_pow, radiusSq_map_Jkernel_comp, hν]
    _ ≤ tvDist (((Pkernel A N) ^ t) x) ((Jkernel A N) ∘ₘ ν) :=
      tvDist_map_le _ _ (radiusSq N) (measurable_radiusSq N)

/-- **Upper half of the Gaussian TV bracket** (`eq:gaussian-tv-bracket`): at positive
times both the vector-chain law and its reconstructed invariant law are obtained by
applying `Jkernel`, which contracts total variation. -/
theorem tvDist_Pkernel_pow_succ_le_Kchain_pow
    (A : ℝ) (N : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x : Fin N → ℝ) (t : ℕ) :
    tvDist (((Pkernel A N) ^ (t + 1)) x) ((Jkernel A N) ∘ₘ ν)
      ≤ tvDist (((Kchain A N) ^ t) (radiusSq N x)) ν := by
  rw [Pkernel_pow_succ_eq_Jkernel_comp_Kchain_pow]
  exact tvDist_comp_le (Jkernel A N) (((Kchain A N) ^ t) (radiusSq N x)) ν

end AbsorptionCutoff
