/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.ScoreTensorization
import AbsorptionCutoff.Supercritical.InvariantSelection
import AbsorptionCutoff.StoppedMoment

/-!
# Dynamic estimates for the supercritical cutoff

This module develops the dynamic concentration and synchronous-coupling
estimates used in Chapter 6 after the one-step score-smoothing argument.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- Squared `tanh` at a Gaussian-scaled coordinate is monotone in the
nonnegative squared radius. -/
lemma tanh_sq_sqrt_mul_mono {A q₀ q₁ g : ℝ} (hqq : q₀ ≤ q₁) :
    Real.tanh (A * Real.sqrt q₀ * g) ^ 2 ≤
      Real.tanh (A * Real.sqrt q₁ * g) ^ 2 := by
  have hev (q : ℝ) :
      Real.tanh (A * Real.sqrt q * g) ^ 2 =
        Real.tanh (|A * g| * Real.sqrt q) ^ 2 := by
    rw [mul_right_comm A (Real.sqrt q) g]
    rcases abs_cases (A * g) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, Real.tanh_neg, neg_sq]
  rw [hev q₀, hev q₁]
  have harg : |A * g| * Real.sqrt q₀ ≤ |A * g| * Real.sqrt q₁ :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqq) (abs_nonneg _)
  have htanh := tanh_strictMono.monotone harg
  have htanh_nonneg : 0 ≤ Real.tanh (|A * g| * Real.sqrt q₀) := by
    calc
      0 = Real.tanh 0 := Real.tanh_zero.symm
      _ ≤ Real.tanh (|A * g| * Real.sqrt q₀) :=
        tanh_strictMono.monotone
          (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  nlinarith

/-- The random squared-radius update is samplewise monotone on nonnegative
radii. This is the order input for the paper's synchronous coupling. -/
lemma monotoneOn_Fmap (A : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    MonotoneOn (fun q => Fmap A N q g) (Set.Ici 0) := by
  intro q₀ _ q₁ _ hqq
  unfold Fmap
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ => tanh_sq_sqrt_mul_mono hqq)
    (inv_nonneg.mpr (Nat.cast_nonneg N))

/-- Under synchronous Gaussian noise, the expected one-step distance is
exactly the distance between the two deterministic mean-map images. -/
lemma integral_abs_Fmap_sub_eq_abs_V_sub
    {A q q' : ℝ} {N : ℕ} (hN : N ≠ 0) (hq : 0 ≤ q) (hq' : 0 ≤ q') :
    ∫ g, |Fmap A N q g - Fmap A N q' g| ∂(gaussianVec N) =
      |V A q - V A q'| := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hInt (r : ℝ) : Integrable (Fmap A N r) (gaussianVec N) := by
    have hpair :
        Measurable (fun g : Fin N → ℝ => (r, g)) :=
      measurable_const.prodMk measurable_id
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((measurable_Fmap A N).comp hpair).aestronglyMeasurable) ?_
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_of_nonneg (Fmap_nonneg A N r g)]
    exact (Fmap_lt_one hNpos r g).le
  rcases le_total q q' with hqq | hqq
  · have hpoint (g : Fin N → ℝ) :
        Fmap A N q g ≤ Fmap A N q' g :=
      monotoneOn_Fmap A N g hq hq' hqq
    have hV : V A q ≤ V A q' := by
      rw [← integral_Fmap hN q, ← integral_Fmap hN q']
      exact integral_mono (hInt q) (hInt q') hpoint
    have habs (g : Fin N → ℝ) :
        |Fmap A N q g - Fmap A N q' g| =
          Fmap A N q' g - Fmap A N q g := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hpoint g))]
      ring
    have habsV : |V A q - V A q'| = V A q' - V A q := by
      rw [abs_of_nonpos (sub_nonpos.mpr hV)]
      ring
    calc
      ∫ g, |Fmap A N q g - Fmap A N q' g| ∂(gaussianVec N) =
          ∫ g, (Fmap A N q' g - Fmap A N q g) ∂(gaussianVec N) :=
        integral_congr_ae (Filter.Eventually.of_forall habs)
      _ = (∫ g, Fmap A N q' g ∂(gaussianVec N)) -
          ∫ g, Fmap A N q g ∂(gaussianVec N) :=
        integral_sub (hInt q') (hInt q)
      _ = V A q' - V A q := by rw [integral_Fmap hN, integral_Fmap hN]
      _ = |V A q - V A q'| := habsV.symm
  · have hpoint (g : Fin N → ℝ) :
        Fmap A N q' g ≤ Fmap A N q g :=
      monotoneOn_Fmap A N g hq' hq hqq
    have hV : V A q' ≤ V A q := by
      rw [← integral_Fmap hN q', ← integral_Fmap hN q]
      exact integral_mono (hInt q') (hInt q) hpoint
    have habs (g : Fin N → ℝ) :
        |Fmap A N q g - Fmap A N q' g| =
          Fmap A N q g - Fmap A N q' g :=
      abs_of_nonneg (sub_nonneg.mpr (hpoint g))
    have habsV : |V A q - V A q'| = V A q - V A q' :=
      abs_of_nonneg (sub_nonneg.mpr hV)
    calc
      ∫ g, |Fmap A N q g - Fmap A N q' g| ∂(gaussianVec N) =
          ∫ g, (Fmap A N q g - Fmap A N q' g) ∂(gaussianVec N) :=
        integral_congr_ae (Filter.Eventually.of_forall habs)
      _ = (∫ g, Fmap A N q g ∂(gaussianVec N)) -
          ∫ g, Fmap A N q' g ∂(gaussianVec N) :=
        integral_sub (hInt q) (hInt q')
      _ = V A q - V A q' := by rw [integral_Fmap hN, integral_Fmap hN]
      _ = |V A q - V A q'| := habsV.symm

/-- The pair of squared-radius updates obtained by using the same Gaussian
vector in both coordinates. -/
noncomputable def synchronousFmap (A : ℝ) (N : ℕ)
    (p : (ℝ × ℝ) × (Fin N → ℝ)) : ℝ × ℝ :=
  (Fmap A N p.1.1 p.2, Fmap A N p.1.2 p.2)

/-- The synchronous pair update is jointly measurable in the two radii and
the shared Gaussian noise. -/
lemma measurable_synchronousFmap (A : ℝ) (N : ℕ) :
    Measurable (synchronousFmap A N) := by
  apply Continuous.measurable
  apply Continuous.prodMk
  · unfold Fmap
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro i _
    exact (continuous_tanh.comp (by fun_prop)).pow 2
  · unfold Fmap
    apply Continuous.const_mul
    apply continuous_finsetSum
    intro i _
    exact (continuous_tanh.comp (by fun_prop)).pow 2

/-- The synchronous coupling kernel for two copies of the squared-radius
chain: both coordinates use one shared Gaussian vector. -/
noncomputable def synchronousKchain (A : ℝ) (N : ℕ) :
    Kernel (ℝ × ℝ) (ℝ × ℝ) :=
  Kernel.map
    ((Kernel.deterministic id measurable_id).prod
      (Kernel.const (ℝ × ℝ) (gaussianVec N)))
    (synchronousFmap A N)

instance (A : ℝ) (N : ℕ) : IsMarkovKernel (synchronousKchain A N) := by
  unfold synchronousKchain
  exact Kernel.IsMarkovKernel.map _ (measurable_synchronousFmap A N)

/-- At a fixed pair of radii, the synchronous kernel is the law of the two
updates driven by a common Gaussian vector. -/
lemma synchronousKchain_apply (A : ℝ) (N : ℕ) (q : ℝ × ℝ) :
    synchronousKchain A N q =
      (gaussianVec N).map (fun g => (Fmap A N q.1 g, Fmap A N q.2 g)) := by
  unfold synchronousKchain
  rw [Kernel.map_apply _ (measurable_synchronousFmap A N), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, id_eq, Measure.dirac_prod,
    Measure.map_map (measurable_synchronousFmap A N)
      (by fun_prop : Measurable (Prod.mk q))]
  rfl

/-- The first marginal of the synchronous coupling is the squared-radius
transition from the first input radius. -/
lemma synchronousKchain_map_fst (A : ℝ) (N : ℕ) (q : ℝ × ℝ) :
    (synchronousKchain A N q).map Prod.fst = Kchain A N q.1 := by
  have hpair : Measurable
      (fun g : Fin N → ℝ => (Fmap A N q.1 g, Fmap A N q.2 g)) :=
    (continuous_Fmap_right A N q.1).measurable.prodMk
      (continuous_Fmap_right A N q.2).measurable
  rw [synchronousKchain_apply, Kchain_apply,
    Measure.map_map measurable_fst hpair]
  rfl

/-- The second marginal of the synchronous coupling is the squared-radius
transition from the second input radius. -/
lemma synchronousKchain_map_snd (A : ℝ) (N : ℕ) (q : ℝ × ℝ) :
    (synchronousKchain A N q).map Prod.snd = Kchain A N q.2 := by
  have hpair : Measurable
      (fun g : Fin N → ℝ => (Fmap A N q.1 g, Fmap A N q.2 g)) :=
    (continuous_Fmap_right A N q.1).measurable.prodMk
      (continuous_Fmap_right A N q.2).measurable
  rw [synchronousKchain_apply, Kchain_apply,
    Measure.map_map measurable_snd hpair]
  rfl

/-- Under the synchronous pair kernel, the expected coordinate distance after
one step is exactly the distance between the two mean-map images. -/
lemma integral_abs_fst_sub_snd_synchronousKchain
    {A q q' : ℝ} {N : ℕ} (hN : N ≠ 0) (hq : 0 ≤ q) (hq' : 0 ≤ q') :
    ∫ p, |p.1 - p.2| ∂(synchronousKchain A N (q, q')) =
      |V A q - V A q'| := by
  rw [synchronousKchain_apply, integral_map]
  · exact integral_abs_Fmap_sub_eq_abs_V_sub hN hq hq'
  · exact ((continuous_Fmap_right A N q).measurable.prodMk
      (continuous_Fmap_right A N q').measurable).aemeasurable
  · exact (measurable_fst.sub measurable_snd).abs.aestronglyMeasurable

/-- Every synchronous transition in positive dimension is supported on the
square `[0,1]²`. -/
lemma synchronousKchain_apply_prod_Icc_compl
    {A : ℝ} {N : ℕ} (hN : 0 < N) (q : ℝ × ℝ) :
    synchronousKchain A N q
      ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
  rw [synchronousKchain_apply,
    Measure.map_apply
      ((continuous_Fmap_right A N q.1).measurable.prodMk
        (continuous_Fmap_right A N q.2).measurable)
      (measurableSet_Icc.prod measurableSet_Icc).compl]
  have hpreimage :
      (fun g : Fin N → ℝ => (Fmap A N q.1 g, Fmap A N q.2 g)) ⁻¹'
          ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = ∅ := by
    ext g
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false]
    constructor
    · intro hg
      exact hg ⟨⟨Fmap_nonneg A N q.1 g, (Fmap_lt_one hN q.1 g).le⟩,
        ⟨Fmap_nonneg A N q.2 g, (Fmap_lt_one hN q.2 g).le⟩⟩
    · intro hfalse
      exact hfalse.elim
  rw [hpreimage, measure_empty]

/-- Every positive-time coordinate of a canonical synchronous pair path lies
in `[0,1]²` almost surely. -/
lemma markovPathMeasure_ae_eval_succ_mem_synchronousKchain_prod_Icc
    {A : ℝ} {N : ℕ} (hN : 0 < N)
    (μ₀ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ₀] (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure μ₀ (synchronousKchain A N)),
      ω (t + 1) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  have hzero : ∀ q : ℝ × ℝ,
      synchronousKchain A N q
        ((Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
    synchronousKchain_apply_prod_Icc_compl hN
  rw [ae_iff]
  have hset :
      {ω : ℕ → ℝ × ℝ |
          ω (t + 1) ∉ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1} =
        (fun ω : ℕ → ℝ × ℝ => ω (t + 1)) ⁻¹'
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)ᶜ := rfl
  rw [show {ω : ℕ → ℝ × ℝ |
      ¬ω (t + 1) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1} =
      {ω : ℕ → ℝ × ℝ |
        ω (t + 1) ∉ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1} by rfl,
    hset, ← Measure.map_apply (measurable_pi_apply (t + 1))
      (measurableSet_Icc.prod measurableSet_Icc).compl,
    markovPathMeasure_map_eval_succ,
    Measure.bind_apply (measurableSet_Icc.prod measurableSet_Icc).compl
      (synchronousKchain A N).aemeasurable]
  simp only [hzero, lintegral_zero]

/-- A canonical synchronous path started in `[0,1]²` remains there at every
fixed time almost surely. -/
lemma markovPathMeasure_dirac_ae_eval_mem_synchronousKchain_prod_Icc
    {A : ℝ} {N : ℕ} {q : ℝ × ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hN : 0 < N) (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (synchronousKchain A N)),
      ω t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  cases t with
  | zero =>
      have hω0 :
          ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (synchronousKchain A N)),
            ω 0 = q := by
        rw [ae_iff]
        have hset :
            {ω : ℕ → ℝ × ℝ | ω 0 ≠ q} =
              (fun ω : ℕ → ℝ × ℝ => ω 0) ⁻¹' ({q} : Set (ℝ × ℝ))ᶜ := by
          ext ω
          simp
        rw [show {ω : ℕ → ℝ × ℝ | ¬ω 0 = q} =
            {ω : ℕ → ℝ × ℝ | ω 0 ≠ q} by rfl,
          hset, ← Measure.map_apply (measurable_pi_apply 0)
            (measurableSet_singleton q).compl,
          markovPathMeasure_map_zero]
        simp
      filter_upwards [hω0] with ω hω
      simpa only [hω] using hq
  | succ t =>
      exact markovPathMeasure_ae_eval_succ_mem_synchronousKchain_prod_Icc
        hN (Measure.dirac q) t

/-- Along the canonical synchronous pair path, the conditional expected
next-step coordinate distance is the distance between the current mean-map
images. -/
lemma condExp_abs_fst_sub_snd_eval_succ_eq_abs_V_sub
    {A : ℝ} {N : ℕ} (hN : 0 < N) {q : ℝ × ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    (markovPathMeasure (Measure.dirac q) (synchronousKchain A N))[
        fun ω => |(ω (t + 1)).1 - (ω (t + 1)).2| | Filtration.piLE t]
      =ᵐ[markovPathMeasure (Measure.dirac q) (synchronousKchain A N)]
        fun ω => |V A (ω t).1 - V A (ω t).2| := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  let φ : ℝ × ℝ → ℝ := fun p => |p.1 - p.2|
  have hφ : StronglyMeasurable φ := by
    exact (measurable_fst.sub measurable_snd).abs.stronglyMeasurable
  have hsuppNext :
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (synchronousKchain A N)),
        ω (t + 1) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    markovPathMeasure_ae_eval_succ_mem_synchronousKchain_prod_Icc
      hN (Measure.dirac q) t
  have hφint :
      Integrable (fun ω : ℕ → ℝ × ℝ => φ (ω (t + 1)))
        (markovPathMeasure (Measure.dirac q) (synchronousKchain A N)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((measurable_pi_apply (t + 1)).fst.sub
        (measurable_pi_apply (t + 1)).snd).abs.aestronglyMeasurable) ?_
    filter_upwards [hsuppNext] with ω hω
    simp only [φ, Real.norm_eq_abs, abs_abs]
    exact abs_le.mpr ⟨by linarith [hω.1.1, hω.2.2],
      by linarith [hω.2.1, hω.1.2]⟩
  have heq :=
    condExp_markovPathMeasure_eval_succ
      (Measure.dirac q) (synchronousKchain A N) t hφ hφint
  have hsupp :=
    markovPathMeasure_dirac_ae_eval_mem_synchronousKchain_prod_Icc
      (A := A) hq hN t
  filter_upwards [heq, hsupp] with ω hω hωsupp
  rw [hω]
  exact integral_abs_fst_sub_snd_synchronousKchain
    hN.ne' hωsupp.1.1 hωsupp.2.1

/-- At each fixed time, the first-coordinate marginal of the synchronous pair
path is the scalar `Kchain` path started from the first input coordinate. -/
lemma markovPathMeasure_map_eval_synchronousKchain_map_fst
    (A : ℝ) (N : ℕ) (q : ℝ × ℝ) (t : ℕ) :
    ((markovPathMeasure (Measure.dirac q) (synchronousKchain A N)).map
        (fun ω => ω t)).map Prod.fst =
      (markovPathMeasure (Measure.dirac q.1) (Kchain A N)).map
        (fun ω => ω t) := by
  induction t with
  | zero =>
      rw [markovPathMeasure_map_zero, markovPathMeasure_map_zero]
      simp
  | succ t ih =>
      rw [markovPathMeasure_map_eval_succ,
        markovPathMeasure_map_eval_succ]
      ext s hs
      rw [Measure.map_apply measurable_fst hs,
        Measure.bind_apply (measurable_fst hs)
          (synchronousKchain A N).aemeasurable,
        Measure.bind_apply hs (Kchain A N).aemeasurable]
      have hkernel (p : ℝ × ℝ) :
          synchronousKchain A N p (Prod.fst ⁻¹' s) =
            Kchain A N p.1 s := by
        have hm := congrArg (fun μ : Measure ℝ => μ s)
          (synchronousKchain_map_fst A N p)
        rw [Measure.map_apply measurable_fst hs] at hm
        exact hm
      simp_rw [hkernel]
      rw [← ih, lintegral_map
        ((Kchain A N).measurable_coe hs) measurable_fst]

/-- At each fixed time, the second-coordinate marginal of the synchronous
pair path is the scalar `Kchain` path started from the second input
coordinate. -/
lemma markovPathMeasure_map_eval_synchronousKchain_map_snd
    (A : ℝ) (N : ℕ) (q : ℝ × ℝ) (t : ℕ) :
    ((markovPathMeasure (Measure.dirac q) (synchronousKchain A N)).map
        (fun ω => ω t)).map Prod.snd =
      (markovPathMeasure (Measure.dirac q.2) (Kchain A N)).map
        (fun ω => ω t) := by
  induction t with
  | zero =>
      rw [markovPathMeasure_map_zero, markovPathMeasure_map_zero]
      simp
  | succ t ih =>
      rw [markovPathMeasure_map_eval_succ,
        markovPathMeasure_map_eval_succ]
      ext s hs
      rw [Measure.map_apply measurable_snd hs,
        Measure.bind_apply (measurable_snd hs)
          (synchronousKchain A N).aemeasurable,
        Measure.bind_apply hs (Kchain A N).aemeasurable]
      have hkernel (p : ℝ × ℝ) :
          synchronousKchain A N p (Prod.snd ⁻¹' s) =
            Kchain A N p.2 s := by
        have hm := congrArg (fun μ : Measure ℝ => μ s)
          (synchronousKchain_map_snd A N p)
        rw [Measure.map_apply measurable_snd hs] at hm
        exact hm
      simp_rw [hkernel]
      rw [← ih, lintegral_map
        ((Kchain A N).measurable_coe hs) measurable_snd]

/-- The probability that a synchronous pair path is outside `J × J` at a
fixed time is at most the sum of the corresponding scalar path
probabilities. -/
lemma markovPathMeasure_measureReal_eval_not_mem_prod_le
    (A : ℝ) (N : ℕ) (q : ℝ × ℝ) (t : ℕ)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    (markovPathMeasure (Measure.dirac q) (synchronousKchain A N)).real
        {ω : ℕ → ℝ × ℝ | ω t ∉ J ×ˢ J} ≤
      (markovPathMeasure (Measure.dirac q.1) (Kchain A N)).real
          {ω : ℕ → ℝ | ω t ∉ J} +
        (markovPathMeasure (Measure.dirac q.2) (Kchain A N)).real
          {ω : ℕ → ℝ | ω t ∉ J} := by
  let μ :=
    markovPathMeasure (Measure.dirac q) (synchronousKchain A N)
  let μ₁ := markovPathMeasure (Measure.dirac q.1) (Kchain A N)
  let μ₂ := markovPathMeasure (Measure.dirac q.2) (Kchain A N)
  let B₁ : Set (ℕ → ℝ × ℝ) :=
    (fun ω => ω t) ⁻¹' (Prod.fst ⁻¹' Jᶜ)
  let B₂ : Set (ℕ → ℝ × ℝ) :=
    (fun ω => ω t) ⁻¹' (Prod.snd ⁻¹' Jᶜ)
  have hunion :
      {ω : ℕ → ℝ × ℝ | ω t ∉ J ×ˢ J} = B₁ ∪ B₂ := by
    ext ω
    simp only [B₁, B₂, Set.mem_union, Set.mem_setOf_eq, Set.mem_prod]
    tauto
  have hfst : μ.real B₁ =
      μ₁.real {ω : ℕ → ℝ | ω t ∉ J} := by
    change μ.real ((fun ω => ω t) ⁻¹' (Prod.fst ⁻¹' Jᶜ)) =
      μ₁.real ((fun ω => ω t) ⁻¹' Jᶜ)
    calc
      μ.real ((fun ω => ω t) ⁻¹' (Prod.fst ⁻¹' Jᶜ)) =
          (μ.map (fun ω => ω t)).real (Prod.fst ⁻¹' Jᶜ) :=
        (map_measureReal_apply (μ := μ) (measurable_pi_apply t)
          (hJ.compl.preimage measurable_fst)).symm
      _ = ((μ.map (fun ω => ω t)).map Prod.fst).real Jᶜ := by
        symm
        exact map_measureReal_apply measurable_fst hJ.compl
      _ = (μ₁.map (fun ω => ω t)).real Jᶜ := by
        rw [markovPathMeasure_map_eval_synchronousKchain_map_fst]
      _ = μ₁.real ((fun ω => ω t) ⁻¹' Jᶜ) :=
        map_measureReal_apply (measurable_pi_apply t) hJ.compl
  have hsnd : μ.real B₂ =
      μ₂.real {ω : ℕ → ℝ | ω t ∉ J} := by
    change μ.real ((fun ω => ω t) ⁻¹' (Prod.snd ⁻¹' Jᶜ)) =
      μ₂.real ((fun ω => ω t) ⁻¹' Jᶜ)
    calc
      μ.real ((fun ω => ω t) ⁻¹' (Prod.snd ⁻¹' Jᶜ)) =
          (μ.map (fun ω => ω t)).real (Prod.snd ⁻¹' Jᶜ) :=
        (map_measureReal_apply (μ := μ) (measurable_pi_apply t)
          (hJ.compl.preimage measurable_snd)).symm
      _ = ((μ.map (fun ω => ω t)).map Prod.snd).real Jᶜ := by
        symm
        exact map_measureReal_apply measurable_snd hJ.compl
      _ = (μ₂.map (fun ω => ω t)).real Jᶜ := by
        rw [markovPathMeasure_map_eval_synchronousKchain_map_snd]
      _ = μ₂.real ((fun ω => ω t) ⁻¹' Jᶜ) :=
        map_measureReal_apply (measurable_pi_apply t) hJ.compl
  rw [hunion]
  exact (measureReal_union_le B₁ B₂).trans_eq
    (congrArg₂ (· + ·) hfst hsnd)

/-- The centered one-step noise has second moment at most `1/(4N)`, stated
directly under the scalar transition kernel. -/
lemma integral_sq_sub_V_Kchain_le
    {A q : ℝ} {N : ℕ} (hN : 0 < N) :
    ∫ y, (y - V A q) ^ 2 ∂(Kchain A N q) ≤
      1 / (4 * (N : ℝ)) := by
  rw [integral_Kchain A N q (by fun_prop)]
  exact integral_sq_Fmap_sub_V_le hN

/-- The one-step squared error about a deterministic target splits exactly
into squared mean-map error and centered kernel noise. -/
lemma integral_sq_sub_Kchain_eq
    {A q r : ℝ} {N : ℕ} (hN : 0 < N) :
    ∫ y, (y - r) ^ 2 ∂(Kchain A N q) =
      (V A q - r) ^ 2 +
        ∫ y, (y - V A q) ^ 2 ∂(Kchain A N q) := by
  rw [integral_Kchain A N q (by fun_prop),
    integral_Kchain A N q (by fun_prop)]
  exact integral_sq_Fmap_sub_fixed_eq hN

/-- Kernel-facing one-step squared-error recursion with the uniform
`1/(4N)` noise contribution. -/
lemma integral_sq_sub_Kchain_le
    {A q r : ℝ} {N : ℕ} (hN : 0 < N) :
    ∫ y, (y - r) ^ 2 ∂(Kchain A N q) ≤
      (V A q - r) ^ 2 + 1 / (4 * (N : ℝ)) := by
  rw [integral_sq_sub_Kchain_eq hN]
  exact add_le_add le_rfl (integral_sq_sub_V_Kchain_le hN)

/-- A local mean-map contraction turns the kernel error estimate into the
one-step deterministic-orbit recursion used in the stopped argument. -/
lemma integral_sq_sub_V_Kchain_le_of_abs_V_sub_le
    {A q r κ : ℝ} {N : ℕ} (hN : 0 < N) (hκ : 0 ≤ κ)
    (hcontract : |V A q - V A r| ≤ κ * |q - r|) :
    ∫ y, (y - V A r) ^ 2 ∂(Kchain A N q) ≤
      κ ^ 2 * (q - r) ^ 2 + 1 / (4 * (N : ℝ)) := by
  have hsq :
      (V A q - V A r) ^ 2 ≤ (κ * |q - r|) ^ 2 := by
    rw [← sq_abs (V A q - V A r)]
    exact
      (sq_le_sq₀ (abs_nonneg (V A q - V A r))
        (mul_nonneg hκ (abs_nonneg (q - r)))).2 hcontract
  calc
    ∫ y, (y - V A r) ^ 2 ∂(Kchain A N q) ≤
        (V A q - V A r) ^ 2 + 1 / (4 * (N : ℝ)) :=
      integral_sq_sub_Kchain_le hN
    _ ≤ (κ * |q - r|) ^ 2 + 1 / (4 * (N : ℝ)) :=
      add_le_add hsq le_rfl
    _ = κ ^ 2 * (q - r) ^ 2 + 1 / (4 * (N : ℝ)) := by
      rw [mul_pow, sq_abs]

/-- A real random variable supported in `[0,1]` has integrable squared error
about every deterministic target. -/
lemma integrable_sq_sub_of_ae_mem_Icc
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (r : ℝ)
    (hstrong : AEStronglyMeasurable (fun ω => (X ω - r) ^ 2) μ)
    (hsupp : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => (X ω - r) ^ 2) μ := by
  refine Integrable.mono'
    (integrable_const ((1 + |r|) ^ 2)) hstrong ?_
  filter_upwards [hsupp] with ω hω
  rw [Real.norm_eq_abs, abs_sq]
  have habs : |X ω - r| ≤ 1 + |r| := by
    calc
      |X ω - r| ≤ |X ω| + |r| := abs_sub _ _
      _ = X ω + |r| := by rw [abs_of_nonneg hω.1]
      _ ≤ 1 + |r| := add_le_add hω.2 le_rfl
  rw [← sq_abs (X ω - r)]
  exact
    (sq_le_sq₀ (abs_nonneg (X ω - r))
      (by positivity : 0 ≤ 1 + |r|)).2 habs

/-- Along a canonical scalar path, the conditional expectation of next-step
squared error is the corresponding one-step kernel integral. -/
lemma condExp_sq_eval_succ_sub_eq_integral_Kchain
    {A r : ℝ} {N : ℕ} (hN : 0 < N)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ) :
    (markovPathMeasure μ₀ (Kchain A N))[
        fun ω => (ω (t + 1) - r) ^ 2 | Filtration.piLE t]
      =ᵐ[markovPathMeasure μ₀ (Kchain A N)]
        fun ω => ∫ y, (y - r) ^ 2 ∂(Kchain A N (ω t)) := by
  let ψ : ((((i : Finset.Iic t) → ℝ) × ℝ) → ℝ) :=
    fun p => (p.2 - r) ^ 2
  have hψ : StronglyMeasurable ψ := by
    dsimp only [ψ]
    fun_prop
  have hsupp :
      ∀ᵐ ω ∂(markovPathMeasure μ₀ (Kchain A N)),
        ω (t + 1) ∈ Set.Icc (0 : ℝ) 1 :=
    markovPathMeasure_ae_eval_succ_mem_Kchain_Icc hN μ₀ t
  have hψint :
      Integrable (fun ω : ℕ → ℝ =>
        ψ (Preorder.frestrictLe t ω, ω (t + 1)))
        (markovPathMeasure μ₀ (Kchain A N)) := by
    dsimp only [ψ]
    apply integrable_sq_sub_of_ae_mem_Icc
      (markovPathMeasure μ₀ (Kchain A N))
      (fun ω : ℕ → ℝ => ω (t + 1)) r
    · have hm : Measurable (fun ω : ℕ → ℝ => ω (t + 1)) :=
        measurable_pi_apply (t + 1)
      exact ((hm.sub measurable_const).pow_const 2).aestronglyMeasurable
    · exact hsupp
  simpa only [ψ, Preorder.frestrictLe_apply] using
    (condExp_markovPathMeasure_prefix_eval_succ_piLE
      μ₀ (Kchain A N) t hψ hψint)

/-- An a.e. local mean-map contraction gives the conditional squared-error
recursion along a canonical scalar path. -/
lemma condExp_sq_eval_succ_sub_V_le_of_abs_V_sub_le
    {A r κ : ℝ} {N : ℕ} (hN : 0 < N) (hκ : 0 ≤ κ)
    (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (t : ℕ)
    (hcontract :
      ∀ᵐ ω ∂(markovPathMeasure μ₀ (Kchain A N)),
        |V A (ω t) - V A r| ≤ κ * |ω t - r|) :
    (markovPathMeasure μ₀ (Kchain A N))[
        fun ω => (ω (t + 1) - V A r) ^ 2 | Filtration.piLE t]
      ≤ᵐ[markovPathMeasure μ₀ (Kchain A N)]
        fun ω => κ ^ 2 * (ω t - r) ^ 2 + 1 / (4 * (N : ℝ)) := by
  have heq :=
    condExp_sq_eval_succ_sub_eq_integral_Kchain
      (A := A) (r := V A r) hN μ₀ t
  filter_upwards [heq, hcontract] with ω hω hωcontract
  rw [hω]
  exact integral_sq_sub_V_Kchain_le_of_abs_V_sub_le
    hN hκ hωcontract

/-- Integrating the conditional estimate gives the one-step second-moment
recursion along a canonical path started in `[0,1]`. -/
lemma integral_sq_eval_succ_sub_V_le_of_abs_V_sub_le
    {A q r κ : ℝ} {N : ℕ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hN : 0 < N) (hκ : 0 ≤ κ) (t : ℕ)
    (hcontract :
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
        |V A (ω t) - V A r| ≤ κ * |ω t - r|) :
    ∫ ω, (ω (t + 1) - V A r) ^ 2
        ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) ≤
      κ ^ 2 *
          ∫ ω, (ω t - r) ^ 2
            ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) +
        1 / (4 * (N : ℝ)) := by
  let μ := markovPathMeasure (Measure.dirac q) (Kchain A N)
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp (s : ℕ) :
      ∀ᵐ ω ∂μ, ω s ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc hq hN s
  have hInt (s : ℕ) (a : ℝ) :
      Integrable (fun ω : ℕ → ℝ => (ω s - a) ^ 2) μ := by
    apply integrable_sq_sub_of_ae_mem_Icc μ (fun ω : ℕ → ℝ => ω s) a
    · have hm : Measurable (fun ω : ℕ → ℝ => ω s) :=
        measurable_pi_apply s
      exact ((hm.sub measurable_const).pow_const 2).aestronglyMeasurable
    · exact hsupp s
  have hcond :
      μ[fun ω => (ω (t + 1) - V A r) ^ 2 | Filtration.piLE t]
        ≤ᵐ[μ]
          fun ω => κ ^ 2 * (ω t - r) ^ 2 + 1 / (4 * (N : ℝ)) := by
    simpa only [μ] using
      condExp_sq_eval_succ_sub_V_le_of_abs_V_sub_le
        hN hκ (Measure.dirac q) t hcontract
  have hright :
      Integrable
        (fun ω : ℕ → ℝ =>
          κ ^ 2 * (ω t - r) ^ 2 + 1 / (4 * (N : ℝ))) μ :=
    ((hInt t r).const_mul (κ ^ 2)).add (integrable_const _)
  change
    (∫ ω, (ω (t + 1) - V A r) ^ 2 ∂μ) ≤
      κ ^ 2 * ∫ ω, (ω t - r) ^ 2 ∂μ + 1 / (4 * (N : ℝ))
  calc
    ∫ ω, (ω (t + 1) - V A r) ^ 2 ∂μ =
        ∫ ω, μ[fun ω => (ω (t + 1) - V A r) ^ 2 |
          Filtration.piLE t] ω ∂μ :=
      (integral_condExp (Filtration.piLE.le t)).symm
    _ ≤ ∫ ω, (κ ^ 2 * (ω t - r) ^ 2 +
        1 / (4 * (N : ℝ))) ∂μ :=
      integral_mono_ae integrable_condExp hright hcond
    _ = κ ^ 2 * ∫ ω, (ω t - r) ^ 2 ∂μ +
        1 / (4 * (N : ℝ)) := by
      rw [integral_add ((hInt t r).const_mul (κ ^ 2))
        (integrable_const _), integral_const_mul, integral_const,
        probReal_univ, one_smul]

/-- If the deterministic orbit and the random path remain in a common
`κ`-contractive regime, their squared distance is uniformly bounded by the
fixed point of the one-step variance recursion. -/
lemma integral_sq_eval_sub_V_iterate_le_of_forall_abs_V_sub_le
    {A q κ : ℝ} {N : ℕ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hN : 0 < N) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hcontract :
      ∀ s : ℕ,
        ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
          |V A (ω s) - V A ((V A)^[s] q)| ≤
            κ * |ω s - (V A)^[s] q|)
    (t : ℕ) :
    ∫ ω, (ω t - (V A)^[t] q) ^ 2
        ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) ≤
      (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) := by
  let μ := markovPathMeasure (Measure.dirac q) (Kchain A N)
  let m : ℕ → ℝ :=
    fun s => ∫ ω, (ω s - (V A)^[s] q) ^ 2 ∂μ
  have hrec : ∀ s : ℕ,
      m (s + 1) ≤ κ ^ 2 * m s + 1 / (4 * (N : ℝ)) := by
    intro s
    have hstep :=
      integral_sq_eval_succ_sub_V_le_of_abs_V_sub_le
        hq hN hκ0 s (hcontract s)
    simpa only [μ, m, Function.iterate_succ_apply'] using hstep
  have hκsq : κ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hκ0 zero_le_one).2 hκ1
  have hgeom :=
    geom_recursion_bound_contraction
      (m := m) (a := κ ^ 2) (B := 1 / (4 * (N : ℝ)))
      (sq_nonneg κ) hκsq hrec t
  have hω0 :
      ∀ᵐ ω ∂μ, ω 0 = q := by
    change
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
        ω 0 = q
    rw [ae_iff]
    have hset :
        {ω : ℕ → ℝ | ω 0 ≠ q} =
          (fun ω : ℕ → ℝ => ω 0) ⁻¹' ({q} : Set ℝ)ᶜ := by
      ext ω
      simp
    rw [show {ω : ℕ → ℝ | ¬ω 0 = q} =
        {ω : ℕ → ℝ | ω 0 ≠ q} by rfl,
      hset, ← Measure.map_apply (measurable_pi_apply 0)
        (measurableSet_singleton q).compl,
      markovPathMeasure_map_zero]
    simp
  have hm0 : m 0 = 0 := by
    dsimp only [m, Function.iterate_zero, id_eq]
    apply integral_eq_zero_of_ae
    filter_upwards [hω0] with ω hω
    simp [hω]
  have hden : 0 < 1 - κ ^ 2 := sub_pos.mpr hκsq
  have hfixed :
      0 ≤ (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) := by
    exact div_nonneg (by positivity) hden.le
  rw [hm0, max_eq_right hfixed] at hgeom
  exact hgeom

/-- The first exit from the stable interval through horizon `T`, capped by
the sentinel `T+1` if no exit occurs. -/
noncomputable def stableIntervalExitTime
    (qStar R : ℝ) (T : ℕ) (ω : ℕ → ℝ) : ℕ :=
  sInf ({t : ℕ |
    t ≤ T ∧ ω t ∉ Set.Icc (qStar - R) (qStar + R)} ∪ {T + 1})

/-- The capped stable-interval exit time never exceeds its sentinel. -/
lemma stableIntervalExitTime_le_sentinel
    (qStar R : ℝ) (T : ℕ) (ω : ℕ → ℝ) :
    stableIntervalExitTime qStar R T ω ≤ T + 1 := by
  unfold stableIntervalExitTime
  exact Nat.sInf_le
    (Set.mem_union_right _ (Set.mem_singleton (T + 1)))

/-- Before the capped exit time, every state through the current index lies
in the stable interval, and conversely. -/
lemma lt_stableIntervalExitTime_iff
    {qStar R : ℝ} {T t : ℕ} {ω : ℕ → ℝ} (htT : t ≤ T) :
    t < stableIntervalExitTime qStar R T ω ↔
      ∀ u ≤ t, ω u ∈ Set.Icc (qStar - R) (qStar + R) := by
  let S : Set ℕ :=
    {u : ℕ |
      u ≤ T ∧ ω u ∉ Set.Icc (qStar - R) (qStar + R)} ∪ {T + 1}
  have hSne : S.Nonempty :=
    ⟨T + 1, Set.mem_union_right _ (Set.mem_singleton _)⟩
  change t < sInf S ↔ _
  constructor
  · intro ht u hut
    by_contra hubad
    have huS : u ∈ S :=
      Set.mem_union_left _ ⟨hut.trans htT, hubad⟩
    exact (not_le_of_gt ht) ((Nat.sInf_le huS).trans hut)
  · intro hall
    have hmin : sInf S ∈ S := Nat.sInf_mem hSne
    by_contra hnot
    have hmint : sInf S ≤ t := not_lt.mp hnot
    rcases hmin with hbad | hsentinel
    · exact hbad.2 (hall (sInf S) hmint)
    · have heq : sInf S = T + 1 :=
        Set.mem_singleton_iff.mp hsentinel
      omega

/-- Survival through time `t` places the time-`t` coordinate in the stable
interval. -/
lemma eval_mem_stableInterval_of_lt_stableIntervalExitTime
    {qStar R : ℝ} {T t : ℕ} {ω : ℕ → ℝ} (htT : t ≤ T)
    (hsurvive : t < stableIntervalExitTime qStar R T ω) :
    ω t ∈ Set.Icc (qStar - R) (qStar + R) := by
  exact (lt_stableIntervalExitTime_iff htT).mp hsurvive t le_rfl

/-- A derivative bound on a positive stable interval gives a two-point
contraction bound throughout that interval. -/
lemma abs_V_sub_le_mul_abs_sub_of_mem_stableInterval
    {A qStar R κ x y : ℝ}
    (hA : A ≠ 0) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hx : x ∈ Set.Icc (qStar - R) (qStar + R))
    (hy : y ∈ Set.Icc (qStar - R) (qStar + R)) :
    |V A x - V A y| ≤ κ * |x - y| := by
  have hdiff :
      ∀ z ∈ Set.Icc (qStar - R) (qStar + R),
        DifferentiableAt ℝ (V A) z := by
    intro z hz
    have hzpos : 0 < z := by
      linarith [hz.1, hRq]
    exact (hasDerivAt_V hA hzpos).differentiableAt
  have hbound :
      ∀ z ∈ Set.Icc (qStar - R) (qStar + R),
        ‖deriv (V A) z‖ ≤ κ := by
    intro z hz
    rw [Real.norm_eq_abs]
    apply hderiv z
    rw [abs_le]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hmv :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (qStar - R) (qStar + R)) hy hx
  simpa only [Real.norm_eq_abs] using hmv

/-- The synchronous conditional distance contracts on a common stable
interval; outside that localization event, the global `[0,1]²` support pays
one unit through an indicator. -/
lemma condExp_abs_fst_sub_snd_eval_succ_le_mul_add_indicator
    {A qStar R κ : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar) (hκ : 0 ≤ κ)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) {q : ℝ × ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    (markovPathMeasure (Measure.dirac q) (synchronousKchain A N))[
        fun ω => |(ω (t + 1)).1 - (ω (t + 1)).2| | Filtration.piLE t]
      ≤ᵐ[markovPathMeasure (Measure.dirac q) (synchronousKchain A N)]
        fun ω =>
          κ * |(ω t).1 - (ω t).2| +
            {ω : ℕ → ℝ × ℝ |
              ω t ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
                Set.Icc (qStar - R) (qStar + R)}.indicator
              (fun _ => (1 : ℝ)) ω := by
  have heq :=
    condExp_abs_fst_sub_snd_eval_succ_eq_abs_V_sub
      (A := A) hN hq t
  have hsupp :=
    markovPathMeasure_dirac_ae_eval_mem_synchronousKchain_prod_Icc
      (A := A) hq hN t
  filter_upwards [heq, hsupp] with ω hω hωsupp
  rw [hω]
  by_cases hlocal :
      ω t ∈ Set.Icc (qStar - R) (qStar + R) ×ˢ
        Set.Icc (qStar - R) (qStar + R)
  · rw [Set.indicator_of_notMem (by simpa using hlocal), add_zero]
    exact abs_V_sub_le_mul_abs_sub_of_mem_stableInterval
      hA hRq hderiv hlocal.1 hlocal.2
  · rw [Set.indicator_of_mem (by simpa using hlocal)]
    have hV : |V A (ω t).1 - V A (ω t).2| ≤ 1 := by
      rw [abs_le]
      exact ⟨by
          linarith [V_nonneg A (ω t).1, (V_lt_one A (ω t).2).le],
        by linarith [V_nonneg A (ω t).2, (V_lt_one A (ω t).1).le]⟩
    calc
      |V A (ω t).1 - V A (ω t).2| ≤ 1 := hV
      _ ≤ κ * |(ω t).1 - (ω t).2| + 1 := by
        linarith [mul_nonneg hκ (abs_nonneg ((ω t).1 - (ω t).2))]

/-- Coordinate distance at every fixed time is integrable along a canonical
synchronous pair path started in `[0,1]²`. -/
lemma integrable_abs_fst_sub_snd_eval_synchronousKchain
    {A : ℝ} {N : ℕ} (hN : 0 < N) {q : ℝ × ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    Integrable (fun ω : ℕ → ℝ × ℝ => |(ω t).1 - (ω t).2|)
      (markovPathMeasure (Measure.dirac q) (synchronousKchain A N)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_pi_apply t).fst.sub
      (measurable_pi_apply t).snd).abs.aestronglyMeasurable) ?_
  filter_upwards [
    markovPathMeasure_dirac_ae_eval_mem_synchronousKchain_prod_Icc
      (A := A) hq hN t] with ω hω
  simp only [Real.norm_eq_abs, abs_abs]
  exact abs_le.mpr ⟨by linarith [hω.1.1, hω.2.2],
    by linarith [hω.2.1, hω.1.2]⟩

/-- Integrating the localized conditional estimate gives the synchronous
distance recursion with the current bad-localization probability as its
additive error. -/
lemma integral_abs_fst_sub_snd_eval_succ_le_mul_add_measureReal
    {A qStar R κ : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar) (hκ : 0 ≤ κ)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) {q : ℝ × ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) (t : ℕ) :
    ∫ ω, |(ω (t + 1)).1 - (ω (t + 1)).2|
        ∂(markovPathMeasure (Measure.dirac q) (synchronousKchain A N)) ≤
      κ * ∫ ω, |(ω t).1 - (ω t).2|
        ∂(markovPathMeasure (Measure.dirac q) (synchronousKchain A N)) +
      (markovPathMeasure (Measure.dirac q) (synchronousKchain A N)).real
        {ω : ℕ → ℝ × ℝ |
          ω t ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
            Set.Icc (qStar - R) (qStar + R)} := by
  let μ :=
    markovPathMeasure (Measure.dirac q) (synchronousKchain A N)
  let B : Set (ℕ → ℝ × ℝ) :=
    {ω | ω t ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
      Set.Icc (qStar - R) (qStar + R)}
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hB : MeasurableSet B := by
    dsimp only [B]
    exact ((measurable_pi_apply t)
      (measurableSet_Icc.prod measurableSet_Icc)).compl
  have hdistInt (s : ℕ) :
      Integrable (fun ω : ℕ → ℝ × ℝ => |(ω s).1 - (ω s).2|) μ := by
    simpa only [μ] using
      integrable_abs_fst_sub_snd_eval_synchronousKchain
        (A := A) hN hq s
  have hindInt :
      Integrable (B.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB
  have hright :
      Integrable (fun ω : ℕ → ℝ × ℝ =>
        κ * |(ω t).1 - (ω t).2| +
          B.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((hdistInt t).const_mul κ).add hindInt
  have hcond :
      μ[fun ω => |(ω (t + 1)).1 - (ω (t + 1)).2| |
          Filtration.piLE t]
        ≤ᵐ[μ] fun ω =>
          κ * |(ω t).1 - (ω t).2| +
            B.indicator (fun _ => (1 : ℝ)) ω := by
    simpa only [μ, B] using
      condExp_abs_fst_sub_snd_eval_succ_le_mul_add_indicator
        hA hRq hκ hderiv hN hq t
  change
    (∫ ω, |(ω (t + 1)).1 - (ω (t + 1)).2| ∂μ) ≤
      κ * ∫ ω, |(ω t).1 - (ω t).2| ∂μ + μ.real B
  calc
    ∫ ω, |(ω (t + 1)).1 - (ω (t + 1)).2| ∂μ =
        ∫ ω, μ[fun ω => |(ω (t + 1)).1 - (ω (t + 1)).2| |
          Filtration.piLE t] ω ∂μ :=
      (integral_condExp (Filtration.piLE.le t)).symm
    _ ≤ ∫ ω, (κ * |(ω t).1 - (ω t).2| +
        B.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
      integral_mono_ae integrable_condExp hright hcond
    _ = κ * ∫ ω, |(ω t).1 - (ω t).2| ∂μ + μ.real B := by
      rw [integral_add ((hdistInt t).const_mul κ) hindInt,
        integral_const_mul, integral_indicator_const, smul_eq_mul, mul_one]
      exact hB

/-- A uniform bad-localization bound through time `t` iterates the
synchronous recursion while retaining geometric decay of the starting
distance. -/
lemma integral_abs_fst_sub_snd_eval_le_pow_mul_add
    {A qStar R κ B : ℝ} {N : ℕ}
    (hA : A ≠ 0) (hRq : R < qStar) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hB : 0 ≤ B)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hN : 0 < N) {q : ℝ × ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) {t : ℕ}
    (hbad : ∀ s < t,
      (markovPathMeasure (Measure.dirac q) (synchronousKchain A N)).real
        {ω : ℕ → ℝ × ℝ |
          ω s ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
            Set.Icc (qStar - R) (qStar + R)} ≤ B) :
    ∫ ω, |(ω t).1 - (ω t).2|
        ∂(markovPathMeasure (Measure.dirac q) (synchronousKchain A N)) ≤
      κ ^ t * |q.1 - q.2| + B / (1 - κ) := by
  let μ :=
    markovPathMeasure (Measure.dirac q) (synchronousKchain A N)
  let m : ℕ → ℝ :=
    fun s => ∫ ω, |(ω s).1 - (ω s).2| ∂μ
  have hrec : ∀ s < t, m (s + 1) ≤ κ * m s + B := by
    intro s hs
    have hstep :=
      integral_abs_fst_sub_snd_eval_succ_le_mul_add_measureReal
        hA hRq hκ0 hderiv hN hq s
    have hstep' : m (s + 1) ≤ κ * m s +
        (markovPathMeasure (Measure.dirac q) (synchronousKchain A N)).real
          {ω : ℕ → ℝ × ℝ |
            ω s ∉ Set.Icc (qStar - R) (qStar + R) ×ˢ
              Set.Icc (qStar - R) (qStar + R)} := by
      simpa only [m, μ] using hstep
    exact hstep'.trans (add_le_add_right (hbad s hs) _)
  have hiter :=
    geom_recursion_bound_contraction_pow_of_lt
      hκ0 hκ1 hB hrec
  have hm0 : m 0 = |q.1 - q.2| := by
    dsimp only [m, μ]
    rw [← integral_map
      (μ := markovPathMeasure (Measure.dirac q) (synchronousKchain A N))
      (φ := fun ω : ℕ → ℝ × ℝ => ω 0)
      (f := fun p : ℝ × ℝ => |p.1 - p.2|)
      (measurable_pi_apply 0).aemeasurable
      (measurable_fst.sub measurable_snd).abs.aestronglyMeasurable,
      markovPathMeasure_map_zero]
    simp
  rw [hm0] at hiter
  exact hiter

/-- While the random path survives in the stable interval, it contracts
toward any deterministic orbit coordinate lying in the same interval. -/
lemma abs_V_eval_sub_V_iterate_le_of_lt_stableIntervalExitTime
    {A q qStar R κ : ℝ} {T t : ℕ} {ω : ℕ → ℝ}
    (hA : A ≠ 0) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t ≤ T)
    (horbit :
      (V A)^[t] q ∈ Set.Icc (qStar - R) (qStar + R))
    (hsurvive : t < stableIntervalExitTime qStar R T ω) :
    |V A (ω t) - V A ((V A)^[t] q)| ≤
      κ * |ω t - (V A)^[t] q| := by
  exact abs_V_sub_le_mul_abs_sub_of_mem_stableInterval
    hA hRq hderiv
      (eval_mem_stableInterval_of_lt_stableIntervalExitTime htT hsurvive)
      horbit

/-- Killing the same squared error at time `t+1` only decreases it relative
to killing at time `t`, since survival to `t+1` implies survival to `t`. -/
lemma indicator_sq_succ_lt_stableIntervalExitTime_le
    {qStar R : ℝ} {T t : ℕ} (e : (ℕ → ℝ) → ℝ)
    (ω : ℕ → ℝ) :
    {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
        (fun ω => e ω ^ 2) ω ≤
      {ω | t < stableIntervalExitTime qStar R T ω}.indicator
        (fun ω => e ω ^ 2) ω := by
  by_cases hsucc : t + 1 < stableIntervalExitTime qStar R T ω
  · have hcurr : t < stableIntervalExitTime qStar R T ω :=
      lt_trans (Nat.lt_succ_self t) hsucc
    rw [Set.indicator_of_mem
        (show ω ∈
          {ω | t + 1 < stableIntervalExitTime qStar R T ω} from hsucc),
      Set.indicator_of_mem
        (show ω ∈
          {ω | t < stableIntervalExitTime qStar R T ω} from hcurr)]
  · rw [Set.indicator_of_notMem
        (show ω ∉
          {ω | t + 1 < stableIntervalExitTime qStar R T ω} from hsucc)]
    exact Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω

/-- Stable-interval membership at time `t` is visible in the canonical
coordinate filtration at time `t`. -/
lemma measurableSet_eval_mem_stableInterval
    (qStar R : ℝ) (t : ℕ) :
    MeasurableSet[Filtration.piLE t]
      {ω : ℕ → ℝ | ω t ∈ Set.Icc (qStar - R) (qStar + R)} := by
  have heval :
      Measurable[Filtration.piLE t] (fun ω : ℕ → ℝ => ω t) := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    have hrestrict :
        Measurable[MeasurableSpace.comap (Preorder.frestrictLe t) inferInstance]
          (Preorder.frestrictLe t :
            (ℕ → ℝ) → ((i : Finset.Iic t) → ℝ)) :=
      comap_measurable _
    exact
      (measurable_pi_apply
        ⟨t, Finset.mem_Iic.mpr le_rfl⟩).comp hrestrict
  exact heval measurableSet_Icc

/-- Survival of the capped stable-interval exit through time `t` is visible
in the canonical filtration at time `t`. -/
lemma measurableSet_lt_stableIntervalExitTime
    {qStar R : ℝ} {T t : ℕ} (htT : t ≤ T) :
    MeasurableSet[Filtration.piLE t]
      {ω : ℕ → ℝ | t < stableIntervalExitTime qStar R T ω} := by
  rw [show
    {ω : ℕ → ℝ | t < stableIntervalExitTime qStar R T ω} =
      ⋂ u : ℕ,
        {ω | u ≤ t →
          ω u ∈ Set.Icc (qStar - R) (qStar + R)} by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq,
      lt_stableIntervalExitTime_iff htT]]
  apply MeasurableSet.iInter
  intro u
  by_cases hut : u ≤ t
  · simp only [hut, true_implies]
    exact (Filtration.piLE (X := fun _ : ℕ => ℝ)).mono hut _
      (measurableSet_eval_mem_stableInterval qStar R u)
  · simp [hut]

/-- Exit from the stable interval through the tracked horizon is an ambient
measurable path event. -/
lemma measurableSet_stableIntervalExitTime_le
    (qStar R : ℝ) (T : ℕ) :
    MeasurableSet
      {ω : ℕ → ℝ | stableIntervalExitTime qStar R T ω ≤ T} := by
  rw [show
    {ω : ℕ → ℝ | stableIntervalExitTime qStar R T ω ≤ T} =
      {ω | T < stableIntervalExitTime qStar R T ω}ᶜ by
        ext ω
        simp]
  exact ((Filtration.piLE (X := fun _ : ℕ => ℝ)).le T _
    (measurableSet_lt_stableIntervalExitTime le_rfl)).compl

/-- On survival through time `t`, the conditional next-step squared error
obeys the local contraction recursion against the deterministic iterate. -/
lemma condExp_sq_eval_succ_sub_V_iterate_le_on_lt_stableIntervalExitTime
    {A q qStar R κ : ℝ} {N T t : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hκ : 0 ≤ κ) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t + 1 ≤ T)
    (horbit :
      (V A)^[t] q ∈ Set.Icc (qStar - R) (qStar + R)) :
    ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
      t < stableIntervalExitTime qStar R T ω →
        (markovPathMeasure (Measure.dirac q) (Kchain A N))[
            fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2 |
              Filtration.piLE t] ω ≤
          κ ^ 2 * (ω t - (V A)^[t] q) ^ 2 +
            1 / (4 * (N : ℝ)) := by
  have heq :=
    condExp_sq_eval_succ_sub_eq_integral_Kchain
      (A := A) (r := V A ((V A)^[t] q)) hN
      (Measure.dirac q) t
  rw [show
    (fun ω : ℕ → ℝ => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) =
      (fun ω : ℕ → ℝ =>
        (ω (t + 1) - V A ((V A)^[t] q)) ^ 2) by
      funext ω
      rw [Function.iterate_succ_apply']]
  filter_upwards [heq] with ω hω
  intro hsurvive
  have htT' : t ≤ T := by omega
  have hcontract :=
    abs_V_eval_sub_V_iterate_le_of_lt_stableIntervalExitTime
      hA hRq hderiv htT' horbit hsurvive
  rw [hω]
  exact integral_sq_sub_V_Kchain_le_of_abs_V_sub_le
    hN hκ hcontract

/-- The stopped next-step squared error satisfies the paper's killed
conditional recursion through every step strictly before the horizon. -/
lemma condExp_indicator_sq_eval_succ_sub_V_iterate_le
    {A q qStar R κ : ℝ} {N T t : ℕ}
    (hA : A ≠ 0) (hN : 0 < N) (hκ : 0 ≤ κ) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t + 1 ≤ T)
    (horbit :
      (V A)^[t] q ∈ Set.Icc (qStar - R) (qStar + R)) :
    (markovPathMeasure (Measure.dirac q) (Kchain A N))[
        fun ω =>
          {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω |
          Filtration.piLE t] ≤ᵐ[
      markovPathMeasure (Measure.dirac q) (Kchain A N)]
        fun ω =>
          {ω | t < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => κ ^ 2 * (ω t - (V A)^[t] q) ^ 2 +
              1 / (4 * (N : ℝ))) ω := by
  let μ := markovPathMeasure (Measure.dirac q) (Kchain A N)
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp :
      ∀ᵐ ω ∂μ, ω (t + 1) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_ae_eval_succ_mem_Kchain_Icc
        hN (Measure.dirac q) t
  have hint_sq :
      Integrable
        (fun ω : ℕ → ℝ =>
          (ω (t + 1) - (V A)^[t + 1] q) ^ 2) μ := by
    apply integrable_sq_sub_of_ae_mem_Icc μ
      (fun ω : ℕ → ℝ => ω (t + 1)) ((V A)^[t + 1] q)
    · exact
        (((measurable_pi_apply (t + 1)).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact hsupp
  have htT' : t ≤ T := by omega
  have hS0 :
      MeasurableSet[Filtration.piLE t]
        {ω : ℕ → ℝ | t < stableIntervalExitTime qStar R T ω} :=
    measurableSet_lt_stableIntervalExitTime htT'
  have hS1 :
      MeasurableSet
        {ω : ℕ → ℝ | t + 1 < stableIntervalExitTime qStar R T ω} :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le (t + 1) _
      (measurableSet_lt_stableIntervalExitTime htT)
  have hS0ambient :
      MeasurableSet
        {ω : ℕ → ℝ | t < stableIntervalExitTime qStar R T ω} :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le t _ hS0
  have hint_L := hint_sq.indicator hS1
  have hint_M := hint_sq.indicator hS0ambient
  have hpoint :
      ∀ ω : ℕ → ℝ,
        {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω ≤
          {ω | t < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω :=
    indicator_sq_succ_lt_stableIntervalExitTime_le _
  have hmono :=
    condExp_mono (m := Filtration.piLE t)
      hint_L hint_M (ae_of_all μ hpoint)
  have hcore :=
    condExp_sq_eval_succ_sub_V_iterate_le_on_lt_stableIntervalExitTime
      hA hN hκ hRq hderiv htT horbit
  change
    μ[fun ω =>
        {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
          (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω |
      Filtration.piLE t] ≤ᵐ[μ] _
  refine hmono.trans ?_
  refine (condExp_indicator hint_sq hS0).trans_le ?_
  filter_upwards [hcore] with ω hω
  by_cases h : ω ∈
      {ω | t < stableIntervalExitTime qStar R T ω}
  · simp only [Set.indicator_of_mem h]
    exact hω h
  · simp [Set.indicator_of_notMem h]

/-- The squared error between the canonical path and its deterministic orbit,
killed upon leaving the stable interval. -/
noncomputable def stableIntervalKilledErrorMoment
    (A : ℝ) (N : ℕ) (q qStar R : ℝ) (T t : ℕ) : ℝ :=
  ∫ ω,
    {ω | t < stableIntervalExitTime qStar R T ω}.indicator
      (fun ω => (ω t - (V A)^[t] q) ^ 2) ω
    ∂(markovPathMeasure (Measure.dirac q) (Kchain A N))

/-- Integrating the killed conditional estimate gives the scalar one-step
recursion for the stopped orbit-error moment. -/
lemma stableIntervalKilledErrorMoment_succ_le
    {A q qStar R κ : ℝ} {N T t : ℕ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hA : A ≠ 0) (hN : 0 < N) (hκ : 0 ≤ κ) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t + 1 ≤ T)
    (horbit :
      (V A)^[t] q ∈ Set.Icc (qStar - R) (qStar + R)) :
    stableIntervalKilledErrorMoment A N q qStar R T (t + 1) ≤
      κ ^ 2 * stableIntervalKilledErrorMoment A N q qStar R T t +
        1 / (4 * (N : ℝ)) := by
  let μ := markovPathMeasure (Measure.dirac q) (Kchain A N)
  let S0 : Set (ℕ → ℝ) :=
    {ω | t < stableIntervalExitTime qStar R T ω}
  let E : (ℕ → ℝ) → ℝ :=
    fun ω => ω t - (V A)^[t] q
  let d : ℝ := 1 / (4 * (N : ℝ))
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp :
      ∀ᵐ ω ∂μ, ω t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc hq hN t
  have hint_Esq : Integrable (fun ω => E ω ^ 2) μ := by
    apply integrable_sq_sub_of_ae_mem_Icc μ
      (fun ω : ℕ → ℝ => ω t) ((V A)^[t] q)
    · exact
        (((measurable_pi_apply t).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact hsupp
  have htT' : t ≤ T := by omega
  have hS0filtration : MeasurableSet[Filtration.piLE t] S0 := by
    simpa only [S0] using
      (measurableSet_lt_stableIntervalExitTime htT')
  have hS0 : MeasurableSet S0 :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le t _ hS0filtration
  have hEqSR :
      (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω * E ω ^ 2) =
        S0.indicator (fun ω => E ω ^ 2) := by
    ext ω
    by_cases h : ω ∈ S0 <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hint_SR :
      Integrable
        (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω * E ω ^ 2) μ := by
    rw [hEqSR]
    exact hint_Esq.indicator hS0
  have hEqH :
      (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω *
        (κ ^ 2 * E ω ^ 2 + d)) =
        S0.indicator (fun ω => κ ^ 2 * E ω ^ 2 + d) := by
    ext ω
    by_cases h : ω ∈ S0 <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  have hint_H :
      Integrable
        (fun ω => S0.indicator (fun _ => (1 : ℝ)) ω *
          (κ ^ 2 * E ω ^ 2 + d)) μ := by
    rw [hEqH]
    exact
      ((hint_Esq.const_mul (κ ^ 2)).add (integrable_const d)).indicator hS0
  have hcond0 :
      μ[fun ω =>
          {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω |
        Filtration.piLE t] ≤ᵐ[μ]
        fun ω => S0.indicator
          (fun ω => κ ^ 2 * E ω ^ 2 + d) ω := by
    simpa only [μ, S0, E, d] using
      (condExp_indicator_sq_eval_succ_sub_V_iterate_le
        hA hN hκ hRq hderiv htT horbit)
  have hcond :
      μ[fun ω =>
          {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
            (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω |
        Filtration.piLE t] ≤ᵐ[μ]
        fun ω => S0.indicator (fun _ => (1 : ℝ)) ω *
          (κ ^ 2 * E ω ^ 2 + d) := by
    filter_upwards [hcond0] with ω hω
    by_cases h : ω ∈ S0
    · simpa [Set.indicator_of_mem h] using hω
    · simpa [Set.indicator_of_notMem h] using hω
  have hrec :=
    integral_le_of_condExp_le
      (μ := μ) (m := Filtration.piLE t) (S0 := S0) (R := E)
      (G := fun ω =>
        {ω | t + 1 < stableIntervalExitTime qStar R T ω}.indicator
          (fun ω => (ω (t + 1) - (V A)^[t + 1] q) ^ 2) ω)
      (k := κ ^ 2) (d := d)
      (Filtration.piLE.le t) (by dsimp only [d]; positivity)
      hS0 hcond hint_H hint_SR
  rw [hEqSR] at hrec
  simpa only [stableIntervalKilledErrorMoment, μ, S0, E, d] using hrec

/-- Through the capped horizon, the killed orbit-error second moment is
uniformly of order `N⁻¹` inside a common stable interval. -/
lemma stableIntervalKilledErrorMoment_le
    {A q qStar R κ : ℝ} {N T t : ℕ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hA : A ≠ 0) (hN : 0 < N)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (htT : t ≤ T)
    (horbit :
      ∀ s ≤ t, (V A)^[s] q ∈ Set.Icc (qStar - R) (qStar + R)) :
    stableIntervalKilledErrorMoment A N q qStar R T t ≤
      (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) := by
  let m : ℕ → ℝ :=
    fun s => stableIntervalKilledErrorMoment A N q qStar R T s
  have hrec :
      ∀ s < t, m (s + 1) ≤
        κ ^ 2 * m s + 1 / (4 * (N : ℝ)) := by
    intro s hst
    apply stableIntervalKilledErrorMoment_succ_le
      hq hA hN hκ0 hRq hderiv
    · exact (Nat.succ_le_of_lt hst).trans htT
    · exact horbit s hst.le
  have hκsq : κ ^ 2 < 1 := by
    simpa using (sq_lt_sq₀ hκ0 zero_le_one).2 hκ1
  have hgeom :=
    geom_recursion_bound_contraction_of_lt
      (m := m) (a := κ ^ 2) (B := 1 / (4 * (N : ℝ)))
      (sq_nonneg κ) hκsq hrec
  have hω0 :
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
        ω 0 = q := by
    rw [ae_iff]
    have hset :
        {ω : ℕ → ℝ | ω 0 ≠ q} =
          (fun ω : ℕ → ℝ => ω 0) ⁻¹' ({q} : Set ℝ)ᶜ := by
      ext ω
      simp
    rw [show {ω : ℕ → ℝ | ¬ω 0 = q} =
        {ω : ℕ → ℝ | ω 0 ≠ q} by rfl,
      hset, ← Measure.map_apply (measurable_pi_apply 0)
        (measurableSet_singleton q).compl,
      markovPathMeasure_map_zero]
    simp
  have hm0 : m 0 = 0 := by
    dsimp only [m, stableIntervalKilledErrorMoment,
      Function.iterate_zero, id_eq]
    apply integral_eq_zero_of_ae
    filter_upwards [hω0] with ω hω
    simp [hω]
  have hden : 0 < 1 - κ ^ 2 := sub_pos.mpr hκsq
  have hfixed :
      0 ≤ (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) :=
    div_nonneg (by positivity) hden.le
  rw [hm0, max_eq_right hfixed] at hgeom
  exact hgeom

/-- A path whose deterministic orbit stays inside the stable interval by a
margin `η` cannot exit through time `T` when every one-step deviation is at
most `δ` and `δ + κ η ≤ η`. -/
lemma stableIntervalExitTime_eq_sentinel_of_step_deviation_le
    {A q qStar R κ η δ : ℝ} {T : ℕ} {ω : ℕ → ℝ}
    (hA : A ≠ 0) (hκ0 : 0 ≤ κ) (hη0 : 0 ≤ η) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (horbit :
      ∀ s ≤ T, |(V A)^[s] q - qStar| ≤ R - η)
    (hω0 : ω 0 = q)
    (hstep :
      ∀ s < T, |ω (s + 1) - V A (ω s)| ≤ δ) :
    stableIntervalExitTime qStar R T ω = T + 1 := by
  have hboth :
      ∀ s ≤ T,
        |ω s - (V A)^[s] q| ≤ η ∧
          ω s ∈ Set.Icc (qStar - R) (qStar + R) := by
    intro s hsT
    induction s with
    | zero =>
        constructor
        · simp [hω0, hη0]
        · have hmargin := horbit 0 (Nat.zero_le T)
          simp only [Function.iterate_zero, id_eq] at hmargin
          rw [abs_le] at hmargin
          exact
            ⟨by linarith [hmargin.1], by linarith [hmargin.2]⟩
    | succ s ih =>
        have hsT' : s ≤ T := (Nat.le_succ s).trans hsT
        have hslt : s < T := Nat.lt_of_succ_le hsT
        have ih' := ih hsT'
        have horbit_s_abs := horbit s hsT'
        have horbit_s_mem :
            (V A)^[s] q ∈
              Set.Icc (qStar - R) (qStar + R) := by
          rw [abs_le] at horbit_s_abs
          exact
            ⟨by linarith [horbit_s_abs.1, hη0],
              by linarith [horbit_s_abs.2, hη0]⟩
        have hcontract :=
          abs_V_sub_le_mul_abs_sub_of_mem_stableInterval
            hA hRq hderiv ih'.2 horbit_s_mem
        have htrack :
            |ω (s + 1) - (V A)^[s + 1] q| ≤ η := by
          rw [Function.iterate_succ_apply']
          calc
            |ω (s + 1) - V A ((V A)^[s] q)| ≤
                |ω (s + 1) - V A (ω s)| +
                  |V A (ω s) - V A ((V A)^[s] q)| :=
              abs_sub_le _ _ _
            _ ≤ δ + κ * |ω s - (V A)^[s] q| :=
              add_le_add (hstep s hslt) hcontract
            _ ≤ δ + κ * η :=
              add_le_add le_rfl
                (mul_le_mul_of_nonneg_left ih'.1 hκ0)
            _ ≤ η := hbuffer
        have horbit_next_abs := horbit (s + 1) hsT
        have hpath_next_abs : |ω (s + 1) - qStar| ≤ R := by
          calc
            |ω (s + 1) - qStar| ≤
                |ω (s + 1) - (V A)^[s + 1] q| +
                  |(V A)^[s + 1] q - qStar| :=
              abs_sub_le _ _ _
            _ ≤ η + (R - η) :=
              add_le_add htrack horbit_next_abs
            _ = R := by ring
        rw [abs_le] at hpath_next_abs
        exact
          ⟨htrack,
            ⟨by linarith [hpath_next_abs.1],
              by linarith [hpath_next_abs.2]⟩⟩
  have hsurvive :
      T < stableIntervalExitTime qStar R T ω :=
    (lt_stableIntervalExitTime_iff le_rfl).2
      (fun s hs => (hboth s hs).2)
  have hsentinel :=
    stableIntervalExitTime_le_sentinel qStar R T ω
  omega

/-- The canonical path exits the stable interval through time `T` only if
some one-step deviation exceeds `δ`; Hoeffding and a union bound therefore
give an exponentially small exit probability. -/
lemma markovPathMeasure_measureReal_stableIntervalExitTime_le
    {A q qStar R κ η δ : ℝ} {N T : ℕ}
    (hA : A ≠ 0) (hN : 0 < N)
    (hκ0 : 0 ≤ κ) (hη0 : 0 ≤ η) (hδ : 0 < δ) (hRq : R < qStar)
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (horbit :
      ∀ s ≤ T, |(V A)^[s] q - qStar| ≤ R - η) :
    (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
        {ω : ℕ → ℝ |
          stableIntervalExitTime qStar R T ω ≤ T} ≤
      2 * T * Real.exp (-2 * N * δ ^ 2) := by
  let μ := markovPathMeasure (Measure.dirac q) (Kchain A N)
  let Eexit : Set (ℕ → ℝ) :=
    {ω | stableIntervalExitTime qStar R T ω ≤ T}
  let Edev : Set (ℕ → ℝ) :=
    finiteHorizonKchainStepDeviationEvent A δ T
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hω0 : ∀ᵐ ω ∂μ, ω 0 = q := by
    change
      ∀ᵐ ω ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)),
        ω 0 = q
    rw [ae_iff]
    have hset :
        {ω : ℕ → ℝ | ω 0 ≠ q} =
          (fun ω : ℕ → ℝ => ω 0) ⁻¹' ({q} : Set ℝ)ᶜ := by
      ext ω
      simp
    rw [show {ω : ℕ → ℝ | ¬ω 0 = q} =
        {ω : ℕ → ℝ | ω 0 ≠ q} by rfl,
      hset, ← Measure.map_apply (measurable_pi_apply 0)
        (measurableSet_singleton q).compl,
      markovPathMeasure_map_zero]
    simp
  have hsubset :
      ∀ᵐ ω ∂μ, ω ∈ Eexit → ω ∈ Edev := by
    filter_upwards [hω0] with ω hω0
    intro hexit
    by_contra hnotdev
    have hstep :
        ∀ s < T, |ω (s + 1) - V A (ω s)| ≤ δ := by
      intro s hsT
      apply le_of_not_gt
      intro hgt
      apply hnotdev
      dsimp only [Edev, finiteHorizonKchainStepDeviationEvent]
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨s, ⟨Finset.mem_range.mpr hsT, hgt⟩⟩
    have hsentinel :=
      stableIntervalExitTime_eq_sentinel_of_step_deviation_le
        hA hκ0 hη0 hRq hderiv hbuffer horbit hω0 hstep
    change stableIntervalExitTime qStar R T ω ≤ T at hexit
    rw [hsentinel] at hexit
    omega
  have hmeasure : μ Eexit ≤ μ Edev :=
    measure_mono_ae hsubset
  have hreal : μ.real Eexit ≤ μ.real Edev := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top μ Edev) hmeasure
  calc
    μ.real Eexit ≤ μ.real Edev := hreal
    _ ≤ 2 * T * Real.exp (-2 * N * δ ^ 2) := by
      simpa only [μ, Edev] using
        (markovPathMeasure_measureReal_finiteHorizonKchainStepDeviationEvent_le
          (A := A) (q := q) hN hδ)

/-- Splitting over survival and exit removes the stopping: the full
orbit-error moment is bounded by the killed moment plus the probability of
exit through the horizon. -/
lemma integral_sq_eval_sub_V_iterate_le_killed_add_exit
    {A q qStar R : ℝ} {N T t : ℕ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hN : 0 < N)
    (htT : t ≤ T)
    (horbit01 : (V A)^[t] q ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, (ω t - (V A)^[t] q) ^ 2
        ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) ≤
      stableIntervalKilledErrorMoment A N q qStar R T t +
        (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
          {ω : ℕ → ℝ |
            stableIntervalExitTime qStar R T ω ≤ T} := by
  let μ := markovPathMeasure (Measure.dirac q) (Kchain A N)
  let S : Set (ℕ → ℝ) :=
    {ω | t < stableIntervalExitTime qStar R T ω}
  let B : Set (ℕ → ℝ) :=
    {ω | stableIntervalExitTime qStar R T ω ≤ t}
  let BT : Set (ℕ → ℝ) :=
    {ω | stableIntervalExitTime qStar R T ω ≤ T}
  let E : (ℕ → ℝ) → ℝ :=
    fun ω => (ω t - (V A)^[t] q) ^ 2
  haveI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    infer_instance
  have hsupp :
      ∀ᵐ ω ∂μ, ω t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [μ] using
      markovPathMeasure_dirac_ae_eval_mem_Kchain_Icc hq hN t
  have hint_E : Integrable E μ := by
    apply integrable_sq_sub_of_ae_mem_Icc μ
      (fun ω : ℕ → ℝ => ω t) ((V A)^[t] q)
    · exact
        (((measurable_pi_apply t).sub measurable_const).pow_const 2)
          |>.aestronglyMeasurable
    · exact hsupp
  have hSfiltration : MeasurableSet[Filtration.piLE t] S := by
    simpa only [S] using
      measurableSet_lt_stableIntervalExitTime htT
  have hS : MeasurableSet S :=
    (Filtration.piLE (X := fun _ : ℕ => ℝ)).le t _ hSfiltration
  have hB : MeasurableSet B := by
    rw [show B = Sᶜ by
      ext ω
      simp [B, S]]
    exact hS.compl
  have hBT : MeasurableSet BT := by
    simpa only [BT] using
      measurableSet_stableIntervalExitTime_le qStar R T
  have hsplit : E = S.indicator E + B.indicator E := by
    funext ω
    simp only [Pi.add_apply]
    by_cases h : t < stableIntervalExitTime qStar R T ω
    · have hn :
          ¬stableIntervalExitTime qStar R T ω ≤ t :=
        Nat.not_le_of_lt h
      rw [Set.indicator_of_mem (show ω ∈ S from h),
        Set.indicator_of_notMem (show ω ∉ B from hn), add_zero]
    · have hb :
          stableIntervalExitTime qStar R T ω ≤ t :=
        Nat.le_of_not_gt h
      rw [Set.indicator_of_notMem (show ω ∉ S from h),
        Set.indicator_of_mem (show ω ∈ B from hb), zero_add]
  have hEle : ∀ᵐ ω ∂μ, E ω ≤ 1 := by
    filter_upwards [hsupp] with ω hω
    dsimp only [E]
    have hlower : -1 ≤ ω t - (V A)^[t] q := by
      linarith [hω.1, horbit01.2]
    have hupper : ω t - (V A)^[t] q ≤ 1 := by
      linarith [hω.2, horbit01.1]
    nlinarith [sq_nonneg (ω t - (V A)^[t] q)]
  have hbad :
      ∫ ω, B.indicator E ω ∂μ ≤ μ.real BT := by
    have hright :
        Integrable (BT.indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hBT
    calc
      ∫ ω, B.indicator E ω ∂μ ≤
          ∫ ω, BT.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        apply integral_mono_ae (hint_E.indicator hB) hright
        filter_upwards [hEle] with ω hω
        by_cases hb : ω ∈ B
        · have hbT : ω ∈ BT := by
            change stableIntervalExitTime qStar R T ω ≤ t at hb
            change stableIntervalExitTime qStar R T ω ≤ T
            exact hb.trans htT
          simp only [Set.indicator_of_mem hb,
            Set.indicator_of_mem hbT]
          exact hω
        · rw [Set.indicator_of_notMem hb]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      _ = μ.real BT := by
        rw [integral_indicator_const, smul_eq_mul, mul_one]
        exact hBT
  change
    (∫ ω, E ω ∂μ) ≤
      (∫ ω, S.indicator E ω ∂μ) + μ.real BT
  calc
    ∫ ω, E ω ∂μ =
        ∫ ω, (S.indicator E + B.indicator E) ω ∂μ :=
      integral_congr_ae
        (Filter.Eventually.of_forall fun ω => congrFun hsplit ω)
    _ = (∫ ω, S.indicator E ω ∂μ) +
        ∫ ω, B.indicator E ω ∂μ :=
      integral_add (hint_E.indicator hS) (hint_E.indicator hB)
    _ ≤ (∫ ω, S.indicator E ω ∂μ) + μ.real BT :=
      add_le_add le_rfl hbad

/-- Uniform dynamic orbit concentration through the stable horizon: the full
second moment is the stopped `O(N⁻¹)` term plus the exponentially small
no-exit error. -/
lemma integral_sq_eval_sub_V_iterate_le_inv_add_exp
    {A q qStar R κ η δ : ℝ} {N T t : ℕ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hA : A ≠ 0) (hN : 0 < N)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (horbit :
      ∀ s ≤ T, |(V A)^[s] q - qStar| ≤ R - η)
    (htT : t ≤ T) :
    ∫ ω, (ω t - (V A)^[t] q) ^ 2
        ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) ≤
      (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
        2 * T * Real.exp (-2 * N * δ ^ 2) := by
  have hRq : R < qStar :=
    hRinterior.trans_le (min_le_left _ _)
  have hRone : R < 1 - qStar :=
    hRinterior.trans_le (min_le_right _ _)
  have horbit_mem :
      ∀ s ≤ T,
        (V A)^[s] q ∈ Set.Icc (qStar - R) (qStar + R) := by
    intro s hsT
    have hs := horbit s hsT
    rw [abs_le] at hs
    exact
      ⟨by linarith [hs.1, hη0], by linarith [hs.2, hη0]⟩
  have horbit01 :
      (V A)^[t] q ∈ Set.Icc (0 : ℝ) 1 := by
    have hs := horbit_mem t htT
    exact
      ⟨by linarith [hs.1, hRq], by linarith [hs.2, hRone]⟩
  calc
    ∫ ω, (ω t - (V A)^[t] q) ^ 2
        ∂(markovPathMeasure (Measure.dirac q) (Kchain A N)) ≤
        stableIntervalKilledErrorMoment A N q qStar R T t +
          (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
            {ω : ℕ → ℝ |
              stableIntervalExitTime qStar R T ω ≤ T} :=
      integral_sq_eval_sub_V_iterate_le_killed_add_exit
        hq hN htT horbit01
    _ ≤ (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
          (markovPathMeasure (Measure.dirac q) (Kchain A N)).real
            {ω : ℕ → ℝ |
              stableIntervalExitTime qStar R T ω ≤ T} :=
      add_le_add
        (stableIntervalKilledErrorMoment_le
          hq hA hN hκ0 hκ1 hRq hderiv htT
          (fun s hst => horbit_mem s (hst.trans htT)))
        le_rfl
    _ ≤ (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
        2 * T * Real.exp (-2 * N * δ ^ 2) :=
      add_le_add le_rfl
        (markovPathMeasure_measureReal_stableIntervalExitTime_le
          hA hN hκ0 hη0 hδ hRq hderiv hbuffer horbit)

/-- For varying dimensions and linearly bounded horizons, the dynamic orbit
error is eventually bounded by one explicit inverse-dimension envelope. -/
lemma eventually_integral_sq_eval_sub_V_iterate_le_inv_nat
    {A qStar R κ η δ C : ℝ}
    (hA : A ≠ 0)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hη0 : 0 ≤ η) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hRinterior : R < min qStar (1 - qStar))
    (hderiv :
      ∀ z : ℝ, |z - qStar| ≤ R → |deriv (V A) z| ≤ κ)
    (hbuffer : δ + κ * η ≤ η)
    (q : ℕ → ℝ) (t T : ℕ → ℕ)
    (hq :
      ∀ᶠ N : ℕ in Filter.atTop,
        q N ∈ Set.Icc (0 : ℝ) 1)
    (htT :
      ∀ᶠ N : ℕ in Filter.atTop,
        t N ≤ T N)
    (hT :
      ∀ᶠ N : ℕ in Filter.atTop,
        (T N : ℝ) ≤ C * (N : ℝ))
    (horbit :
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ s ≤ T N,
          |(V A)^[s] (q N) - qStar| ≤ R - η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∫ ω, (ω (t N) - (V A)^[t N] (q N)) ^ 2
          ∂(markovPathMeasure (Measure.dirac (q N)) (Kchain A N)) ≤
        ((1 / 4) / (1 - κ ^ 2) + 2 * C) / (N : ℝ) := by
  have hc : 0 < 2 * δ ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hδ)
  have hrem :=
    eventually_two_nat_horizon_mul_exp_neg_le_mul_inv_nat
      hC hc hT
  filter_upwards
      [hq, htT, horbit, hrem,
        Filter.eventually_ge_atTop (1 : ℕ)] with
      N hqN htTN horbitN hremN hN
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hNreal : (0 : ℝ) < N := by
    exact_mod_cast hNpos
  have hremN' :
      2 * (T N : ℝ) * Real.exp (-2 * N * δ ^ 2) ≤
        2 * C / (N : ℝ) := by
    rw [show -2 * (N : ℝ) * δ ^ 2 =
        -(2 * δ ^ 2) * (N : ℝ) by ring]
    exact hremN
  have hfull :=
    integral_sq_eval_sub_V_iterate_le_inv_add_exp
      hqN hA hNpos hκ0 hκ1 hη0 hδ hRinterior
      hderiv hbuffer horbitN htTN
  calc
    ∫ ω, (ω (t N) - (V A)^[t N] (q N)) ^ 2
        ∂(markovPathMeasure (Measure.dirac (q N)) (Kchain A N)) ≤
        (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
          2 * (T N : ℝ) * Real.exp (-2 * N * δ ^ 2) :=
      hfull
    _ ≤ (1 / (4 * (N : ℝ))) / (1 - κ ^ 2) +
        2 * C / (N : ℝ) :=
      add_le_add le_rfl hremN'
    _ = ((1 / 4) / (1 - κ ^ 2) + 2 * C) / (N : ℝ) := by
      have hκsq : κ ^ 2 < 1 := by
        simpa using (sq_lt_sq₀ hκ0 zero_le_one).2 hκ1
      field_simp [hNreal.ne', (sub_pos.mpr hκsq).ne']

end AbsorptionCutoff
