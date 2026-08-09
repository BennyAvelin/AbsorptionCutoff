/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Total-variation cutoff and mixing time

Statement-level formalization of the paper's introductory definitions
(`def:intro-cutoff`, `def:intro-mixing-time`, §1). Getting these *types* to
type-check already pins down the ambiguous spots flagged in the LaTeX source.

## Main definitions
* `AbsorptionCutoff.tvDist` — total-variation distance `sup_B |μ(B) − ν(B)|`.
* `AbsorptionCutoff.dSeq`   — distance to equilibrium `d(t) = ‖κ^t(x,·) − π‖_TV` via the
  Mathlib kernel power `κ ^ t`.
* `AbsorptionCutoff.HasCutoff` — total-variation cutoff at `tCut n` with window `w n`
  (windowed convention), for a family indexed by `n → ∞`.
* `AbsorptionCutoff.mixingTime` — `t_mix(ε) = inf{t : d(t) ≤ ε}`, `⊤` if none.
* `AbsorptionCutoff.IsAbsorbing` — a point `a` is absorbing for a kernel `κ`.

## Main results
* `AbsorptionCutoff.tvDist_comm`, `AbsorptionCutoff.tvDist_le_one`,
  `AbsorptionCutoff.tvDist_bddAbove` —
  `tvDist` is symmetric, `≤ 1` between probability measures, and its defining `iSup`
  is a genuine (bounded) supremum.
* `AbsorptionCutoff.tvDist_dirac` — core of `eq:tv-absorption`: TV distance to a point mass
  `δ_a` equals the survival mass `μ({a}ᶜ)`.
* `AbsorptionCutoff.tvDist_pow_dirac` — kernel form:
  `‖κ^t(x,·) − δ_a‖_TV = κ^t(x,{a}ᶜ)`.
* `AbsorptionCutoff.absorb_mass_mono` /
  `AbsorptionCutoff.dSeq_dirac_antitone` — absorption mass is nondecreasing, so `d(t)` is
  nonincreasing (`rem:intro-profile-mixing`).
* `AbsorptionCutoff.instMarkovPow` — powers of a Markov kernel are Markov kernels.

## Downstream use
`AbsorptionCutoff.Chains` specializes the absorbing-kernel identities to the rounded
radius chain. The fixed-width development packages its exact profile as
`HasCutoff` and derives the manuscript's `O_ε(window)` mixing-time bounds.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace AbsorptionCutoff

variable {E : Type*} [MeasurableSpace E]

/-- Total-variation distance `‖μ − ν‖_TV = sup_B |μ(B) − ν(B)|` over measurable `B`
(paper §2 convention). -/
noncomputable def tvDist (μ ν : Measure E) : ℝ :=
  ⨆ s : {s : Set E // MeasurableSet s}, |(μ s.1).toReal - (ν s.1).toReal|

lemma tvDist_nonneg (μ ν : Measure E) : 0 ≤ tvDist μ ν :=
  Real.iSup_nonneg (fun _ => abs_nonneg _)

lemma tvDist_self (μ : Measure E) : tvDist μ μ = 0 := by
  simp only [tvDist, sub_self, abs_zero, ciSup_const]

/-- Total-variation distance is symmetric (`|a − b| = |b − a|`). -/
lemma tvDist_comm (μ ν : Measure E) : tvDist μ ν = tvDist ν μ :=
  iSup_congr (fun _ => abs_sub_comm _ _)

/-- For probability measures each set-discrepancy `|μ(s) − ν(s)|` lies in `[0,1]`. -/
private lemma tvDist_term_le_one (μ ν : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (s : Set E) : |(μ s).toReal - (ν s).toReal| ≤ 1 := by
  have hμ : (μ s).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  have hν : (ν s).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  rw [abs_le]
  exact ⟨by linarith [ENNReal.toReal_nonneg (a := μ s), ENNReal.toReal_nonneg (a := ν s)],
    by linarith [ENNReal.toReal_nonneg (a := μ s), ENNReal.toReal_nonneg (a := ν s)]⟩

/-- The set of set-discrepancies is bounded above (by `1`) for probability measures,
so the defining `iSup` of `tvDist` is a genuine supremum (needed for `le_ciSup`). -/
lemma tvDist_bddAbove (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove (Set.range fun s : {s : Set E // MeasurableSet s} =>
      |(μ s.1).toReal - (ν s.1).toReal|) :=
  ⟨1, by rintro _ ⟨s, rfl⟩; exact tvDist_term_le_one μ ν s.1⟩

/-- Total-variation distance between probability measures is at most `1`
(the `sup_B |μ(B) − ν(B)|` convention). -/
lemma tvDist_le_one (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ 1 := by
  haveI : Nonempty {s : Set E // MeasurableSet s} := ⟨⟨∅, MeasurableSet.empty⟩⟩
  exact ciSup_le (fun s => tvDist_term_le_one μ ν s.1)

/-- **Total variation contracts under measurable maps**: pushing two probability
measures forward by the same measurable function cannot increase their total-variation
distance. This is the data-processing step used for the lower bound in
`eq:gaussian-tv-bracket`. -/
lemma tvDist_map_le {F : Type*} [MeasurableSpace F]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E → F) (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  unfold tvDist
  refine ciSup_le fun s => ?_
  rw [Measure.map_apply hf s.prop, Measure.map_apply hf s.prop]
  exact le_ciSup (tvDist_bddAbove μ ν)
    ⟨f ⁻¹' s.1, hf s.prop⟩

/-- Every individual measurable-set discrepancy is bounded by total variation. This is
the pointwise input for the layer-cake proof that Markov kernels contract `tvDist`. -/
lemma abs_measure_toReal_sub_le_tvDist (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set E) (hs : MeasurableSet s) :
    |(μ s).toReal - (ν s).toReal| ≤ tvDist μ ν := by
  unfold tvDist
  exact le_ciSup (tvDist_bddAbove μ ν) ⟨s, hs⟩

/-- The one-sided bounded-test form of the total-variation inequality: the difference
of the expectations of any measurable `[0,1]`-valued function is at most `tvDist`.
This is the layer-cake step in the proof that Markov kernels contract total variation. -/
lemma integral_sub_le_tvDist (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E → ℝ) (hf : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) :
    (∫ x, f x ∂μ) - ∫ x, f x ∂ν ≤ tvDist μ ν := by
  have hf_int_μ : Integrable f μ :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
      exact hf_le_one x)
  have hf_int_ν : Integrable f ν :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
      exact hf_le_one x)
  have htail_meas (ξ : Measure E) :
      Measurable fun t : ℝ => ξ.real {x | t ≤ f x} :=
    Measurable.ennreal_toReal <| Antitone.measurable fun _ _ hst =>
      measure_mono fun _ hx => hst.trans hx
  have htail_int (ξ : Measure E) [IsProbabilityMeasure ξ] :
      IntegrableOn (fun t : ℝ => ξ.real {x | t ≤ f x}) (Set.Ioc 0 1) := by
    apply (integrableOn_const (C := (1 : ℝ)) (by simp [Real.volume_Ioc])).mono'
      (htail_meas ξ).aestronglyMeasurable.restrict
    filter_upwards [] with t
    rw [measureReal_def, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
  rw [hf_int_μ.integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall hf_nonneg) (Eventually.of_forall hf_le_one),
    hf_int_ν.integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall hf_nonneg) (Eventually.of_forall hf_le_one),
    ← integral_sub (htail_int μ) (htail_int ν)]
  calc
    (∫ t in Set.Ioc 0 1,
        μ.real {x | t ≤ f x} - ν.real {x | t ≤ f x})
        ≤ ∫ (_t : ℝ) in Set.Ioc 0 1, tvDist μ ν := by
          apply integral_mono_ae
          · exact (htail_int μ).sub (htail_int ν)
          · exact integrableOn_const (by simp [Real.volume_Ioc])
          · filter_upwards [] with t
            exact le_trans (le_abs_self _)
              (abs_measure_toReal_sub_le_tvDist μ ν _
                (hf measurableSet_Ici))
    _ = tvDist μ ν := by
      rw [setIntegral_const, Real.volume_real_Ioc]
      norm_num

/-- Absolute-value form of the bounded-test total-variation inequality. -/
lemma abs_integral_sub_le_tvDist (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E → ℝ) (hf : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ tvDist μ ν := by
  rw [abs_le]
  constructor
  · have h := integral_sub_le_tvDist ν μ f hf hf_nonneg hf_le_one
    rw [← tvDist_comm μ ν] at h
    linarith
  · exact integral_sub_le_tvDist μ ν f hf hf_nonneg hf_le_one

/-- **Total variation contracts under Markov kernels**: evolving two probability
measures through the same Markov kernel cannot increase their total-variation distance. -/
lemma tvDist_comp_le {F : Type*} [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ tvDist μ ν := by
  unfold tvDist
  refine ciSup_le fun s => ?_
  rw [Measure.bind_apply s.prop κ.aemeasurable,
    Measure.bind_apply s.prop κ.aemeasurable,
    ← integral_toReal (κ.measurable_coe s.prop).aemeasurable
      (Eventually.of_forall fun x =>
        lt_of_le_of_lt (prob_le_one : κ x s.1 ≤ 1) ENNReal.one_lt_top),
    ← integral_toReal (κ.measurable_coe s.prop).aemeasurable
      (Eventually.of_forall fun x =>
        lt_of_le_of_lt (prob_le_one : κ x s.1 ≤ 1) ENNReal.one_lt_top)]
  exact abs_integral_sub_le_tvDist μ ν
    (fun x => (κ x s.1).toReal)
    (κ.measurable_coe s.prop).ennreal_toReal
    (fun _ => ENNReal.toReal_nonneg)
    (fun x => by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one)

/-- **Core of `eq:tv-absorption`.** For a probability measure, the total-variation
distance to a point mass `δ_a` equals the survival mass `μ({a}ᶜ)` off that point.
Applied to `μ = P^t(x,·)` with `a` the absorbing state, this is exactly
`‖P^t(x,·) − δ_a‖_TV = ℙ(τ > t)`. -/
lemma tvDist_dirac (μ : Measure E) [IsProbabilityMeasure μ] {a : E}
    (ha : MeasurableSet ({a} : Set E)) :
    tvDist μ (Measure.dirac a) = (μ {a}ᶜ).toReal := by
  haveI : Nonempty {s : Set E // MeasurableSet s} := ⟨⟨∅, MeasurableSet.empty⟩⟩
  set M := (μ {a}ᶜ).toReal with hM
  have hac : MeasurableSet ({a}ᶜ : Set E) := ha.compl
  have hbound : ∀ s : {s : Set E // MeasurableSet s},
      |(μ s.1).toReal - ((Measure.dirac a) s.1).toReal| ≤ M := by
    rintro ⟨s, hs⟩
    simp only
    rw [Measure.dirac_apply' a hs]
    by_cases hmem : a ∈ s
    · simp only [Set.indicator_of_mem hmem, Pi.one_apply, ENNReal.toReal_one]
      have hle : (μ s).toReal ≤ 1 := by
        rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      have hcompl : (μ sᶜ).toReal = 1 - (μ s).toReal := by
        rw [prob_compl_eq_one_sub hs,
          ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
      have hsub : sᶜ ⊆ ({a}ᶜ : Set E) := by
        intro x hx; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl; exact hx hmem
      have heq : |(μ s).toReal - 1| = (μ sᶜ).toReal := by
        rw [abs_of_nonpos (by linarith), hcompl]; ring
      rw [heq]; exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
    · simp only [Set.indicator_of_notMem hmem, ENNReal.toReal_zero, sub_zero,
        abs_of_nonneg ENNReal.toReal_nonneg]
      have hsub : s ⊆ ({a}ᶜ : Set E) := by
        intro x hx; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rintro rfl; exact hmem hx
      exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
  apply le_antisymm
  · exact ciSup_le hbound
  · have hbdd : BddAbove (Set.range fun s : {s : Set E // MeasurableSet s} =>
        |(μ s.1).toReal - ((Measure.dirac a) s.1).toReal|) :=
      ⟨M, by rintro _ ⟨s, rfl⟩; exact hbound s⟩
    have hle := le_ciSup hbdd (⟨{a}ᶜ, hac⟩ : {s : Set E // MeasurableSet s})
    have hval : |(μ ({a}ᶜ)).toReal - ((Measure.dirac a) ({a}ᶜ)).toReal| = M := by
      rw [Measure.dirac_apply' a hac,
        Set.indicator_of_notMem (by simp : a ∉ ({a}ᶜ : Set E)),
        ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
    rw [hval] at hle
    exact hle

/-- Distance to equilibrium at integer time `t`: `d(t) = ‖κ^t(x, ·) − π‖_TV`. -/
noncomputable def dSeq (κ : Kernel E E) (x : E) (π : Measure E) (t : ℕ) : ℝ :=
  tvDist ((κ ^ t) x) π

/-- A point `a` is absorbing for `κ` if the chain started at `a` stays at `a`
(the rounded chain's origin, `eq:absorption-time`). -/
def IsAbsorbing (κ : Kernel E E) (a : E) : Prop := κ a = Measure.dirac a

/-- For an absorbing state, the mass at `a` is nondecreasing in time; equivalently
the survival mass is nonincreasing, so `d(t)` is nonincreasing
(paper `rem:intro-profile-mixing`). -/
lemma absorb_mass_mono {κ : Kernel E E} {a : E}
    (ha : MeasurableSet ({a} : Set E)) (habs : IsAbsorbing κ a) (x : E) (t : ℕ) :
    (κ ^ t) x {a} ≤ (κ ^ (t + 1)) x {a} := by
  have hpt : ∀ y, ({a} : Set E).indicator (1 : E → ENNReal) y ≤ κ y {a} := by
    intro y
    rcases eq_or_ne y a with hy | hy
    · rw [hy]; simp [IsAbsorbing] at habs; simp [habs, Measure.dirac_apply' a ha]
    · rw [Set.indicator_of_notMem (by simpa using hy)]; positivity
  calc (κ ^ t) x {a}
      = ∫⁻ y, ({a} : Set E).indicator 1 y ∂((κ ^ t) x) := (lintegral_indicator_one ha).symm
    _ ≤ ∫⁻ y, κ y {a} ∂((κ ^ t) x) := lintegral_mono hpt
    _ = (κ ^ (t + 1)) x {a} := (Kernel.pow_succ_apply_eq_lintegral κ t x ha).symm

/-- A power of a Markov kernel is a Markov kernel (so `κ^t(x,·)` is a probability
measure). Not automatic in Mathlib: `*` on kernels does not trigger the `comp`
instance, so we recurse through `∘ₖ`. -/
instance instMarkovPow {κ : Kernel E E} [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ n ih => rw [pow_succ]; haveI := ih; exact inferInstanceAs (IsMarkovKernel ((κ ^ n) ∘ₖ κ))

/-- **`eq:tv-absorption`, kernel form.** The TV distance from `κ^t(x,·)` to the
point mass at an absorbing state equals the survival mass `κ^t(x, {a}ᶜ)`; for the
rounded chain with absorbing origin this is `‖P^t(x,·) − δ₀‖_TV = ℙ(τ > t)`. -/
lemma tvDist_pow_dirac {κ : Kernel E E} [IsMarkovKernel κ] {a : E}
    (ha : MeasurableSet ({a} : Set E)) (x : E) (t : ℕ) :
    tvDist ((κ ^ t) x) (Measure.dirac a) = (((κ ^ t) x) {a}ᶜ).toReal :=
  tvDist_dirac _ ha

/-- The distance to an absorbing point mass is nonincreasing in time
(paper `rem:intro-profile-mixing`: `d_r` is nonincreasing). -/
lemma dSeq_dirac_antitone {κ : Kernel E E} [IsMarkovKernel κ] {a : E}
    (ha : MeasurableSet ({a} : Set E)) (habs : IsAbsorbing κ a) (x : E) :
    Antitone (dSeq κ x (Measure.dirac a)) := by
  refine antitone_nat_of_succ_le (fun t => ?_)
  change tvDist ((κ ^ (t + 1)) x) (Measure.dirac a) ≤ tvDist ((κ ^ t) x) (Measure.dirac a)
  rw [tvDist_dirac _ ha, tvDist_dirac _ ha]
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [prob_compl_eq_one_sub ha, prob_compl_eq_one_sub ha]
  exact tsub_le_tsub_left (absorb_mass_mono ha habs x t) 1

/-- **Total-variation cutoff** at time `tCut n` with window `w n`, for a family of
chains indexed by `n → ∞` (paper `def:intro-cutoff`, windowed convention). `d n t`
is the distance to equilibrium of the `n`-th chain at time `t`. -/
def HasCutoff (d : ℕ → ℕ → ℝ) (tCut w : ℕ → ℝ) : Prop :=
  Tendsto (fun c : ℝ => liminf (fun n => d n ⌊tCut n - c * w n⌋₊) atTop) atTop (𝓝 1) ∧
  Tendsto (fun c : ℝ => limsup (fun n => d n ⌊tCut n + c * w n⌋₊) atTop) atTop (𝓝 0)

/-- **Mixing time** `t_mix(ε) = inf{t : d(t) ≤ ε}`, with value `⊤` if no such `t`
exists (paper `def:intro-mixing-time`). -/
noncomputable def mixingTime (d : ℕ → ℝ) (ε : ℝ) : ℕ∞ :=
  sInf ((Nat.cast : ℕ → ℕ∞) '' {t | d t ≤ ε})

end AbsorptionCutoff
