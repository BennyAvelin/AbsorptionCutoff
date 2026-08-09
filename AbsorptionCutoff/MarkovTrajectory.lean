/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import AbsorptionCutoff.AbsorptionTime

/-!
# Canonical trajectories for a homogeneous Markov kernel

Specializes Mathlib's Ionescu--Tulcea trajectory measure to a time-homogeneous kernel.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- Regard a homogeneous kernel as a history-dependent kernel by reading only the last
coordinate of the history. -/
noncomputable def markovHistoryKernel {E : Type*} [MeasurableSpace E]
    (κ : Kernel E E) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → E) E :=
  Kernel.comap κ (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance instMarkovHistoryKernel {E : Type*} [MeasurableSpace E]
    (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovHistoryKernel κ n) := by
  unfold markovHistoryKernel
  infer_instance

/-- The canonical path-space law obtained by starting from `μ₀` and iterating the
homogeneous Markov kernel `κ`. -/
noncomputable def markovPathMeasure {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) (κ : Kernel E E) [IsMarkovKernel κ] :
    Measure (ℕ → E) :=
  Kernel.trajMeasure μ₀ (markovHistoryKernel κ)

/-- The time-zero coordinate marginal of the canonical path law is the initial
distribution `μ₀`. This is the base case of the induction identifying the coordinate
marginals of `markovPathMeasure` with the kernel powers. -/
theorem markovPathMeasure_map_zero {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) (κ : Kernel E E) [IsMarkovKernel κ] :
    (markovPathMeasure μ₀ κ).map (fun x => x 0) = μ₀ := by
  have hfun : (fun x : ℕ → E => x 0)
      = ⇑(MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => E)) ∘ Preorder.frestrictLe 0 := by
    funext x
    simp only [Function.comp_apply, MeasurableEquiv.piUnique_apply, Preorder.frestrictLe_apply]
    congr 1
  rw [markovPathMeasure, hfun,
    ← Measure.map_map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => E)).measurable
      (Preorder.measurable_frestrictLe 0),
    Kernel.trajMeasure, Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  exact MeasurableEquiv.map_map_symm _

/-- Composing a `comap`ped kernel with a measure amounts to first pushing the measure
forward along the reindexing map. -/
private lemma comap_comp_measure {α β γ : Type*}
    {_ : MeasurableSpace α} {_ : MeasurableSpace β} {_ : MeasurableSpace γ}
    (κ : Kernel α β) (g : γ → α) (hg : Measurable g) (ν : Measure γ) :
    (κ.comap g hg) ∘ₘ ν = κ ∘ₘ (ν.map g) := by
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]

/-- The canonical path law is a probability measure. -/
instance instIsProbabilityMeasureMarkovPathMeasure {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (κ : Kernel E E) [IsMarkovKernel κ] :
    IsProbabilityMeasure (markovPathMeasure μ₀ κ) := by
  unfold markovPathMeasure; infer_instance

/-- One-step recursion for the coordinate marginals of the canonical path law:
the time-`t+1` marginal is the time-`t` marginal pushed one step through `κ`. -/
theorem markovPathMeasure_map_eval_succ {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (κ : Kernel E E) [IsMarkovKernel κ] (t : ℕ) :
    (markovPathMeasure μ₀ κ).map (fun x => x (t + 1))
      = κ ∘ₘ ((markovPathMeasure μ₀ κ).map (fun x => x t)) := by
  haveI : IsProbabilityMeasure ((markovPathMeasure μ₀ κ).map (Preorder.frestrictLe t)) :=
    Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe t).aemeasurable
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => E) (μ₀ := μ₀) (κ := markovHistoryKernel κ) (a := t)
  have hgmeas : Measurable (fun x : ℕ → E => (Preorder.frestrictLe t x, x (t + 1))) := by
    fun_prop
  have hπ : (fun x : (i : Finset.Iic t) → E => x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)
        ∘ (Preorder.frestrictLe t : (ℕ → E) → _) = fun x : ℕ → E => x t := rfl
  have hmm : (Measure.map (Preorder.frestrictLe t) (markovPathMeasure μ₀ κ)).map
        (fun x : (i : Finset.Iic t) → E => x ⟨t, Finset.mem_Iic.mpr le_rfl⟩)
      = (markovPathMeasure μ₀ κ).map (fun x => x t) := by
    rw [← hπ]
    exact Measure.map_map (measurable_pi_apply _) (Preorder.measurable_frestrictLe t)
  have hcomap : (markovHistoryKernel κ t)
        ∘ₘ ((markovPathMeasure μ₀ κ).map (Preorder.frestrictLe t))
      = κ ∘ₘ ((markovPathMeasure μ₀ κ).map (fun x => x t)) := by
    rw [markovHistoryKernel, comap_comp_measure, hmm]
  calc (markovPathMeasure μ₀ κ).map (fun x => x (t + 1))
      = ((markovPathMeasure μ₀ κ).map
          (fun x => (Preorder.frestrictLe t x, x (t + 1)))).map Prod.snd :=
        (Measure.map_map measurable_snd hgmeas).symm
    _ = ((markovPathMeasure μ₀ κ).map (Preorder.frestrictLe t)
          ⊗ₘ markovHistoryKernel κ t).map Prod.snd := by rw [markovPathMeasure, hjoint]
    _ = markovHistoryKernel κ t ∘ₘ ((markovPathMeasure μ₀ κ).map (Preorder.frestrictLe t)) :=
        Measure.snd_compProd _ _
    _ = κ ∘ₘ ((markovPathMeasure μ₀ κ).map (fun x => x t)) := hcomap

/-- Under the canonical homogeneous Markov path law, the regular conditional
distribution of the next coordinate given the whole prefix is the homogeneous
kernel evaluated at the last coordinate of that prefix. -/
theorem condDistrib_markovPathMeasure_eval_succ
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀]
    (κ : Kernel E E) [IsMarkovKernel κ] (t : ℕ) :
    condDistrib (fun x : ℕ → E => x (t + 1)) (Preorder.frestrictLe t)
        (markovPathMeasure μ₀ κ)
      =ᵐ[(markovPathMeasure μ₀ κ).map (Preorder.frestrictLe t)]
        markovHistoryKernel κ t := by
  exact Kernel.condDistrib_trajMeasure

/-- Conditional expectation of a function of the next coordinate under the
canonical homogeneous Markov path law is integration against the one-step
kernel at the current coordinate. -/
theorem condExp_markovPathMeasure_eval_succ
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀]
    (κ : Kernel E E) [IsMarkovKernel κ] (t : ℕ)
    {φ : E → ℝ} (hφ : StronglyMeasurable φ)
    (hφ_int : Integrable (fun ω : ℕ → E => φ (ω (t + 1)))
      (markovPathMeasure μ₀ κ)) :
    (markovPathMeasure μ₀ κ)[fun ω => φ (ω (t + 1)) |
        MeasurableSpace.comap (Preorder.frestrictLe t) inferInstance]
      =ᵐ[markovPathMeasure μ₀ κ]
        fun ω => ∫ y, φ y ∂κ (ω t) := by
  have hprefix : Measurable
      (Preorder.frestrictLe t :
        (ℕ → E) → ((i : Finset.Iic t) → E)) :=
    Preorder.measurable_frestrictLe t
  have hcond :=
    condExp_ae_eq_integral_condDistrib
      (μ := markovPathMeasure μ₀ κ)
      (X := Preorder.frestrictLe t)
      (Y := fun ω : ℕ → E => ω (t + 1))
      hprefix
      (measurable_pi_apply (t + 1)).aemeasurable hφ hφ_int
  have hk := condDistrib_markovPathMeasure_eval_succ μ₀ κ t
  have hintPrefix :
      (fun x => ∫ y, φ y ∂
          condDistrib (fun ω : ℕ → E => ω (t + 1))
            (Preorder.frestrictLe t) (markovPathMeasure μ₀ κ) x)
        =ᵐ[(markovPathMeasure μ₀ κ).map (Preorder.frestrictLe t)]
      fun x => ∫ y, φ y ∂markovHistoryKernel κ t x :=
    hk.fun_comp fun ν => ∫ y, φ y ∂ν
  have hintPath :
      (fun ω => ∫ y, φ y ∂
          condDistrib (fun x : ℕ → E => x (t + 1))
            (Preorder.frestrictLe t) (markovPathMeasure μ₀ κ)
            (Preorder.frestrictLe t ω))
        =ᵐ[markovPathMeasure μ₀ κ]
      fun ω => ∫ y, φ y ∂markovHistoryKernel κ t
        (Preorder.frestrictLe t ω) :=
    MeasureTheory.ae_of_ae_map
      hprefix.aemeasurable hintPrefix
  refine hcond.trans (hintPath.trans ?_)
  filter_upwards with ω
  rw [markovHistoryKernel, Kernel.comap_apply]
  rfl

/-- Prefix-dependent version of
`condExp_markovPathMeasure_eval_succ`, used for centered one-step noise
whose center is a function of the current state. -/
theorem condExp_markovPathMeasure_prefix_eval_succ
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀]
    (κ : Kernel E E) [IsMarkovKernel κ] (t : ℕ)
    {ψ : (((i : Finset.Iic t) → E) × E) → ℝ}
    (hψ : StronglyMeasurable ψ)
    (hψ_int : Integrable (fun ω : ℕ → E =>
      ψ (Preorder.frestrictLe t ω, ω (t + 1)))
      (markovPathMeasure μ₀ κ)) :
    (markovPathMeasure μ₀ κ)[fun ω =>
        ψ (Preorder.frestrictLe t ω, ω (t + 1)) |
      MeasurableSpace.comap (Preorder.frestrictLe t) inferInstance]
      =ᵐ[markovPathMeasure μ₀ κ]
        fun ω => ∫ y, ψ (Preorder.frestrictLe t ω, y) ∂κ (ω t) := by
  have hprefix : Measurable
      (Preorder.frestrictLe t :
        (ℕ → E) → ((i : Finset.Iic t) → E)) :=
    Preorder.measurable_frestrictLe t
  have hcond :=
    condExp_prod_ae_eq_integral_condDistrib
      (μ := markovPathMeasure μ₀ κ)
      (X := Preorder.frestrictLe t)
      (Y := fun ω : ℕ → E => ω (t + 1))
      hprefix (measurable_pi_apply (t + 1)).aemeasurable hψ hψ_int
  have hk := condDistrib_markovPathMeasure_eval_succ μ₀ κ t
  have hintPrefix :
      (fun x => ∫ y, ψ (x, y) ∂
          condDistrib (fun ω : ℕ → E => ω (t + 1))
            (Preorder.frestrictLe t) (markovPathMeasure μ₀ κ) x)
        =ᵐ[(markovPathMeasure μ₀ κ).map (Preorder.frestrictLe t)]
      fun x => ∫ y, ψ (x, y) ∂markovHistoryKernel κ t x := by
    filter_upwards [hk] with x hx
    rw [hx]
  have hintPath :
      (fun ω => ∫ y, ψ (Preorder.frestrictLe t ω, y) ∂
          condDistrib (fun x : ℕ → E => x (t + 1))
            (Preorder.frestrictLe t) (markovPathMeasure μ₀ κ)
            (Preorder.frestrictLe t ω))
        =ᵐ[markovPathMeasure μ₀ κ]
      fun ω => ∫ y, ψ (Preorder.frestrictLe t ω, y) ∂
        markovHistoryKernel κ t (Preorder.frestrictLe t ω) :=
    MeasureTheory.ae_of_ae_map hprefix.aemeasurable hintPrefix
  refine hcond.trans (hintPath.trans ?_)
  filter_upwards with ω
  rw [markovHistoryKernel, Kernel.comap_apply]
  rfl

/-- The prefix-dependent next-step identity stated with Mathlib's canonical
coordinate filtration. -/
theorem condExp_markovPathMeasure_prefix_eval_succ_piLE
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀]
    (κ : Kernel E E) [IsMarkovKernel κ] (t : ℕ)
    {ψ : (((i : Finset.Iic t) → E) × E) → ℝ}
    (hψ : StronglyMeasurable ψ)
    (hψ_int : Integrable (fun ω : ℕ → E =>
      ψ (Preorder.frestrictLe t ω, ω (t + 1)))
      (markovPathMeasure μ₀ κ)) :
    (markovPathMeasure μ₀ κ)[fun ω =>
        ψ (Preorder.frestrictLe t ω, ω (t + 1)) |
      Filtration.piLE t]
      =ᵐ[markovPathMeasure μ₀ κ]
        fun ω => ∫ y, ψ (Preorder.frestrictLe t ω, y) ∂κ (ω t) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact condExp_markovPathMeasure_prefix_eval_succ μ₀ κ t hψ hψ_int

/-- The time-`t` coordinate marginal of the canonical path law is the initial
distribution pushed `t` steps through the kernel: `κ^t ∘ₘ μ₀`. -/
theorem markovPathMeasure_map_eval {E : Type*} [MeasurableSpace E]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (κ : Kernel E E) [IsMarkovKernel κ] (t : ℕ) :
    (markovPathMeasure μ₀ κ).map (fun x => x t) = (κ ^ t) ∘ₘ μ₀ := by
  induction t with
  | zero =>
    rw [pow_zero, show (1 : Kernel E E) = Kernel.id from rfl, Measure.id_comp]
    exact markovPathMeasure_map_zero μ₀ κ
  | succ t ih =>
    rw [markovPathMeasure_map_eval_succ, ih, pow_succ']
    exact Measure.comp_assoc

/-- Coordinate marginals of the path law started at a point `x` are the kernel powers:
`(markovPathMeasure (δ_x) κ).map (·t) = (κ^t) x`. This is the form consumed by the
absorption-time survival bridge `measure_absorptionTime_gt_eq_kernel_pow`. -/
theorem markovPathMeasure_dirac_map_eval {E : Type*} [MeasurableSpace E]
    (x : E) (κ : Kernel E E) [IsMarkovKernel κ] (t : ℕ) :
    (markovPathMeasure (Measure.dirac x) κ).map (fun ω => ω t) = (κ ^ t) x := by
  rw [markovPathMeasure_map_eval, Measure.dirac_bind (Kernel.measurable _) x]

/-- If the origin is absorbing for `κ` (`κ 0 = δ₀`), then the coordinate process on the
canonical path law is absorbing **almost everywhere**: once it hits `0` at time `t`, it
stays `0` at time `t+1` for `markovPathMeasure`-a.e. path. (Pathwise absorption fails on
the raw path space; only this a.e. version holds.) -/
theorem markovPathMeasure_ae_absorbing {E : Type*} [MeasurableSpace E] [Zero E]
    [MeasurableSingletonClass E]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (κ : Kernel E E) [IsMarkovKernel κ]
    (hκ : κ 0 = Measure.dirac 0) (t : ℕ) :
    ∀ᵐ ω ∂(markovPathMeasure μ₀ κ), ω t = 0 → ω (t + 1) = 0 := by
  haveI : IsProbabilityMeasure ((markovPathMeasure μ₀ κ).map (Preorder.frestrictLe t)) :=
    Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe t).aemeasurable
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => E) (μ₀ := μ₀) (κ := markovHistoryKernel κ) (a := t)
  rw [show Kernel.trajMeasure μ₀ (markovHistoryKernel κ) = markovPathMeasure μ₀ κ from rfl]
    at hjoint
  set S : Set (((i : Finset.Iic t) → E) × E) :=
    {p | p.1 ⟨t, Finset.mem_Iic.mpr le_rfl⟩ = 0 ∧ p.2 ≠ 0} with hS_def
  have hfm : Measurable
      (fun p : ((i : Finset.Iic t) → E) × E => p.1 ⟨t, Finset.mem_Iic.mpr le_rfl⟩) := by fun_prop
  have hSmeas : MeasurableSet S := by
    have h1 : MeasurableSet
        {p : ((i : Finset.Iic t) → E) × E | p.1 ⟨t, Finset.mem_Iic.mpr le_rfl⟩ = 0} :=
      hfm (measurableSet_singleton (0 : E))
    have h2 : MeasurableSet {p : ((i : Finset.Iic t) → E) × E | p.2 ≠ 0} :=
      measurable_snd (measurableSet_singleton (0 : E)).compl
    exact h1.inter h2
  rw [ae_iff]
  have hset : {ω : ℕ → E | ¬(ω t = 0 → ω (t + 1) = 0)}
      = (fun ω => (Preorder.frestrictLe t ω, ω (t + 1))) ⁻¹' S := by
    ext ω
    simp only [hS_def, Set.mem_setOf_eq, Set.mem_preimage, Classical.not_imp,
      Preorder.frestrictLe_apply]
  rw [hset, ← Measure.map_apply (by fun_prop) hSmeas, ← hjoint,
    Measure.compProd_apply hSmeas]
  have hzero : ∀ h : (i : Finset.Iic t) → E,
      (markovHistoryKernel κ t h) (Prod.mk h ⁻¹' S) = 0 := by
    intro h
    rw [markovHistoryKernel, Kernel.comap_apply]
    by_cases hh : h ⟨t, Finset.mem_Iic.mpr le_rfl⟩ = 0
    · rw [hh, hκ, Measure.dirac_apply' _ (hSmeas.preimage (by fun_prop)),
        Set.indicator_of_notMem (fun hmem => hmem.2 rfl)]
    · have hempty : Prod.mk h ⁻¹' S = ∅ := by
        ext y
        simp only [Set.mem_preimage, hS_def, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        exact fun h1 => absurd h1 hh
      rw [hempty, measure_empty]
  simp only [hzero, lintegral_zero]

end AbsorptionCutoff
