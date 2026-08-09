/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.MeanMap.Basic
import AbsorptionCutoff.Rounding
import AbsorptionCutoff.Cutoff

/-!
# The squared-radius Markov chains

Formalizes the paper's §2 (`sec:setup`) scalar reduction: by Gaussian rotational
invariance the vector chain reduces to the **squared-radius chain**, a Markov kernel
on `ℝ` driven by the random map `F_{A,N}(q,g) = N⁻¹ ∑ tanh²(A√q·gᵢ)`
(`eq:gaussian-random-map`, `eq:gaussian-q-kernel`).

## Main definitions
* `AbsorptionCutoff.gaussianVec N` — standard Gaussian `𝒢_N` on `ℝ^N` (`= Fin N → ℝ`).
* `AbsorptionCutoff.Fmap A N q g` — the random map `F_{A,N}(q,g)`.
* `AbsorptionCutoff.Kchain A N` — the unrounded squared-radius transition kernel `K_{A,N}`
  on `ℝ`: `K(q,·) = law of F_{A,N}(q, G)`, `G ∼ 𝒢_N`. A Markov kernel.
* `AbsorptionCutoff.Hmap A ρ N h g`, `AbsorptionCutoff.Hkernel A ρ N` — the
  **rounded** squared-radius map
  `H_{A,ρ,N}(h,g) = N⁻¹ ∑ Q₁(ρ⁻¹·tanh(ρA√h·gᵢ))²` and its Markov kernel.

The one-step mean is the mean map `V_A` (`integral_Fmap`, `eq:gaussian-q-moments`);
see `MeanMap.lean` for `V_A` and its properties.

## Main results
* `AbsorptionCutoff.Fmap_nonneg`, `AbsorptionCutoff.Fmap_lt_one` — the chain
  takes values in `[0,1)`.
* `AbsorptionCutoff.integral_Fmap` — `∫ F_{A,N}(q,·) d𝒢_N = V_A(q)` (mean = `V_A`).
* `AbsorptionCutoff.isAbsorbing_Hkernel` — the origin is absorbing for the rounded chain
  (`Hkernel A ρ N 0 = δ_0`): instantiating `tvDist_pow_dirac` here yields the
  total-variation cutoff driver `eq:tv-absorption`.

## Downstream use
`AbsorptionCutoff.AbsorptionTime` develops the stopping-time and survival identities,
while `AbsorptionCutoff.VectorReduction` and `AbsorptionCutoff.RoundedVectorReduction` complete
the vector-to-scalar reductions used by the cutoff theorems.
-/

open MeasureTheory ProbabilityTheory BigOperators

namespace AbsorptionCutoff

/-- Standard Gaussian measure `𝒢_N` on `ℝ^N` (`= Fin N → ℝ`). -/
noncomputable def gaussianVec (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (N : ℕ) : IsProbabilityMeasure (gaussianVec N) := by
  unfold gaussianVec; infer_instance

/-- The random map `F_{A,N}(q,g) = N⁻¹ ∑ᵢ tanh²(A√q·gᵢ)` (paper `eq:gaussian-random-map`). -/
noncomputable def Fmap (A : ℝ) (N : ℕ) (q : ℝ) (g : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, Real.tanh (A * Real.sqrt q * g i) ^ 2

lemma Fmap_nonneg (A : ℝ) (N : ℕ) (q : ℝ) (g : Fin N → ℝ) : 0 ≤ Fmap A N q g := by
  unfold Fmap; positivity

/-- `F_{A,N}(q,g) < 1` (`N ≥ 1`): the average of `N` values each `< 1`. So the
squared-radius chain takes values in `[0,1)` (paper: "`Z` takes values in `[0,1]`"). -/
lemma Fmap_lt_one {A : ℝ} {N : ℕ} (hN : 0 < N) (q : ℝ) (g : Fin N → ℝ) : Fmap A N q g < 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hsum : ∑ i, Real.tanh (A * Real.sqrt q * g i) ^ 2 < (N : ℝ) := by
    calc ∑ i, Real.tanh (A * Real.sqrt q * g i) ^ 2 < ∑ _i : Fin N, (1 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => Real.tanh_sq_lt_one _)
      _ = (N : ℝ) := by simp
  unfold Fmap
  rw [show (1 : ℝ) = (N : ℝ)⁻¹ * (N : ℝ) by field_simp]
  exact mul_lt_mul_of_pos_left hsum (inv_pos.mpr hNpos)

/-- `F_{A,N}` is jointly measurable in `(q, g)` (it is even continuous). -/
lemma measurable_Fmap (A : ℝ) (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => Fmap A N p.1 p.2) := by
  apply Continuous.measurable
  unfold Fmap
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i _
  exact (continuous_tanh.comp (by fun_prop)).pow 2

/-- **Unrounded squared-radius transition kernel** `K_{A,N}` on `ℝ`
(paper `eq:gaussian-q-kernel`): `K(q,·)` is the law of `F_{A,N}(q, G)`, `G ∼ 𝒢_N`.
Built as the pushforward of `δ_q ⊗ 𝒢_N` under the joint map `F_{A,N}`. -/
noncomputable def Kchain (A : ℝ) (N : ℕ) : Kernel ℝ ℝ :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const ℝ (gaussianVec N)))
    (fun p => Fmap A N p.1 p.2)

instance (A : ℝ) (N : ℕ) : IsMarkovKernel (Kchain A N) := by
  unfold Kchain
  exact Kernel.IsMarkovKernel.map _ (measurable_Fmap A N)

/-- The rounded squared-radius map `H_{A,ρ,N}(h,g) = N⁻¹ ∑ Q₁(ρ⁻¹·tanh(ρA√h·gᵢ))²`
(paper `eq:rounded-coordinate-observable`, `eq:subcritical-exact-grid-transition`). -/
noncomputable def Hmap (A ρ : ℝ) (N : ℕ) (h : ℝ) (g : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, ((Q₁ (ρ⁻¹ * Real.tanh (ρ * A * Real.sqrt h * g i)) : ℤ) : ℝ) ^ 2

lemma Hmap_nonneg (A ρ : ℝ) (N : ℕ) (h : ℝ) (g : Fin N → ℝ) : 0 ≤ Hmap A ρ N h g := by
  unfold Hmap; positivity

/-- From `h = 0` the map collapses to `0`: `√0 = 0`, so every coordinate is
`Q₁(ρ⁻¹·tanh 0) = Q₁ 0 = 0`. This is what makes the origin absorbing. -/
lemma Hmap_zero (A ρ : ℝ) (N : ℕ) (g : Fin N → ℝ) : Hmap A ρ N 0 g = 0 := by
  have hQ : Q₁ (0 : ℝ) = 0 := (Q₁_zero_iff 0).mpr (by norm_num)
  unfold Hmap
  simp [Real.sqrt_zero, Real.tanh_zero, hQ]

/-- `H_{A,ρ,N}` is jointly measurable (`Q₁` is measurable, though not continuous). -/
lemma measurable_Hmap (A ρ : ℝ) (N : ℕ) :
    Measurable (fun p : ℝ × (Fin N → ℝ) => Hmap A ρ N p.1 p.2) := by
  unfold Hmap
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Measurable.pow_const
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := by fun_prop
  apply hcast.comp
  apply measurable_Q₁.comp
  apply Measurable.const_mul
  exact continuous_tanh.measurable.comp (by fun_prop)

/-- **Rounded squared-radius transition kernel** `H_{A,ρ,N}` on `ℝ` (paper §2):
`H(h,·)` is the law of `Hmap A ρ N h G`, `G ∼ 𝒢_N`. A Markov kernel. Its absorbing
state `0` (the zero grid bin) drives the total-variation cutoff via `eq:tv-absorption`. -/
noncomputable def Hkernel (A ρ : ℝ) (N : ℕ) : Kernel ℝ ℝ :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const ℝ (gaussianVec N)))
    (fun p => Hmap A ρ N p.1 p.2)

instance (A ρ : ℝ) (N : ℕ) : IsMarkovKernel (Hkernel A ρ N) := by
  unfold Hkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_Hmap A ρ N)

/-- **The origin is absorbing for the rounded chain**: `H_{A,ρ,N}(0,·) = δ_0`
(paper §2, the zero grid bin is a trap). Instantiating the abstract absorption
identity `tvDist_pow_dirac` at `Hkernel A ρ N` with this `a = 0` gives the
total-variation cutoff driver `eq:tv-absorption`. Proof: `Hkernel 0` is the law of
`Hmap A ρ N 0 · = 0` (a.e. constant), hence `δ_0`. -/
lemma isAbsorbing_Hkernel (A ρ : ℝ) (N : ℕ) : IsAbsorbing (Hkernel A ρ N) 0 := by
  unfold IsAbsorbing Hkernel
  rw [Kernel.map_apply _ (measurable_Hmap A ρ N), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, id_eq, Measure.dirac_prod,
    Measure.map_map (measurable_Hmap A ρ N) (by fun_prop : Measurable (Prod.mk (0 : ℝ)))]
  rw [show (fun p : ℝ × (Fin N → ℝ) => Hmap A ρ N p.1 p.2) ∘ (Prod.mk (0 : ℝ))
      = (fun _ => (0 : ℝ)) from funext (fun g => Hmap_zero A ρ N g)]
  rw [Measure.map_const]
  simp

/-- **`eq:tv-absorption` for the rounded chain.** The TV distance from the `t`-step
law started at `x` to the absorbing point mass `δ_0` equals the survival mass off the
origin, `ℙ(τ_ρ > t)`: `‖H^t(x,·) − δ_0‖_TV = H^t(x, {0}ᶜ)`. Instantiation of the
abstract `tvDist_pow_dirac`. -/
lemma tvDist_Hkernel_pow_dirac (A ρ : ℝ) (N : ℕ) (x : ℝ) (t : ℕ) :
    tvDist (((Hkernel A ρ N) ^ t) x) (Measure.dirac 0)
      = ((((Hkernel A ρ N) ^ t) x) ({0}ᶜ)).toReal :=
  tvDist_pow_dirac (measurableSet_singleton 0) x t

/-- The distance of the rounded chain to the absorbing origin is nonincreasing in
time (paper `rem:intro-profile-mixing`). Combines `isAbsorbing_Hkernel` with the
abstract `dSeq_dirac_antitone`. -/
lemma dSeq_Hkernel_dirac_antitone (A ρ : ℝ) (N : ℕ) (x : ℝ) :
    Antitone (dSeq (Hkernel A ρ N) x (Measure.dirac 0)) :=
  dSeq_dirac_antitone (measurableSet_singleton 0) (isAbsorbing_Hkernel A ρ N) x

/-- **The one-step mean of the squared-radius chain is `V_A`**
(paper `eq:gaussian-q-moments`, `𝔼[Z_{t+1} ∣ Z_t = q] = V_A(q)`): each coordinate is
a `𝒢_N`-marginal `∼ N(0,1)`, so `∫ F_{A,N}(q,·) d𝒢_N = N⁻¹·N·V_A(q) = V_A(q)`. This
links the chain to the mean map studied in `MeanMap.lean`. -/
lemma integral_Fmap {A : ℝ} {N : ℕ} (hN : N ≠ 0) (q : ℝ) :
    ∫ g, Fmap A N q g ∂(gaussianVec N) = V A q := by
  have hInt : ∀ i : Fin N, Integrable
      (fun g : Fin N → ℝ => Real.tanh (A * Real.sqrt q * g i) ^ 2) (gaussianVec N) := by
    intro i
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((continuous_tanh.comp (by fun_prop)).pow 2).measurable.aestronglyMeasurable ?_
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact (Real.tanh_sq_lt_one _).le
  have hmarg : ∀ i : Fin N,
      ∫ g, Real.tanh (A * Real.sqrt q * g i) ^ 2 ∂(gaussianVec N) = V A q := by
    intro i
    have hpm : (gaussianVec N).map (Function.eval i) = gaussianReal 0 1 := by
      unfold gaussianVec; rw [Measure.pi_map_eval]; simp
    have hf : AEStronglyMeasurable (fun x : ℝ => Real.tanh (A * Real.sqrt q * x) ^ 2)
        ((gaussianVec N).map (Function.eval i)) :=
      Continuous.aestronglyMeasurable ((continuous_tanh.comp (by fun_prop)).pow 2)
    have hφ : AEMeasurable (Function.eval i) (gaussianVec N) := (measurable_pi_apply i).aemeasurable
    have key := integral_map hφ hf
    rw [hpm] at key
    exact key.symm
  unfold Fmap
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hInt i)]
  simp_rw [hmarg]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end AbsorptionCutoff
