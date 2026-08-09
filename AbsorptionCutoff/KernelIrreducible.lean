/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Irreducible

/-!
# Uniqueness of invariant probabilities for irreducible kernels

This file supplies the measure-theoretic uniqueness theorem missing from the
current `Kernel.IsIrreducible` API.  The proof uses the greatest common
submeasure of two invariant probabilities and their mutually singular
residuals; it does not require a path-space ergodic theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

variable {α : Type*} [MeasurableSpace α]

/-- A measure invariant under a kernel is invariant under every iterate of
that kernel. -/
lemma invariant_pow {κ : Kernel α α} {μ : Measure α}
    (hμ : κ.Invariant μ) (n : ℕ) :
    (κ ^ n).Invariant μ := by
  induction n with
  | zero =>
      change Kernel.id ∘ₘ μ = μ
      exact Measure.id_comp
  | succ n ih =>
      rw [pow_succ]
      exact ih.comp hμ

/-- The irreducibility measure is absolutely continuous with respect to every
nonzero finite invariant measure. -/
lemma irreducibleMeasure_absolutelyContinuous_invariant
    {φ μ : Measure α} {κ : Kernel α α} [Kernel.IsIrreducible φ κ]
    [IsFiniteMeasure μ] (hμ_ne : μ ≠ 0) (hμ : κ.Invariant μ) :
    φ ≪ μ := by
  intro s hμs
  let t := toMeasurable μ s
  have ht : MeasurableSet t := measurableSet_toMeasurable μ s
  have hμt : μ t = 0 := by
    simpa [t] using hμs
  by_contra hφs
  have hφt : 0 < φ t := by
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hφs) ?_
    exact measure_mono (subset_toMeasurable μ s)
  let S : ℕ → Set α := fun n => {x | 0 < (κ ^ n) x t}
  have hS_union : (⋃ n, S n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ :=
      Kernel.IsIrreducible.irreducible (φ := φ) (κ := κ) ht hφt x
    exact Set.mem_iUnion.2 ⟨n, hn⟩
  have hμ_union : μ (⋃ n, S n) ≠ 0 := by
    rw [hS_union, ne_eq, Measure.measure_univ_eq_zero]
    exact hμ_ne
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hμ_union
  have hmeas : Measurable fun x => (κ ^ n) x t :=
    (κ ^ n).measurable_coe ht
  have hlintegral : 0 < ∫⁻ x, (κ ^ n) x t ∂μ := by
    rw [lintegral_pos_iff_support hmeas]
    simpa only [S, Function.support, ne_eq, pos_iff_ne_zero] using hn
  have hμt_pos : 0 < μ t := by
    rw [← (invariant_pow hμ n).def, Measure.bind_apply ht (κ ^ n).aemeasurable]
    exact hlintegral
  exact hμt_pos.ne' hμt

/-- A Markov kernel irreducible with respect to a nonzero measure has at most
one invariant probability measure. -/
theorem invariant_probability_unique
    {φ μ ν : Measure α} {κ : Kernel α α}
    [IsMarkovKernel κ] [Kernel.IsIrreducible φ κ]
    (hφ : φ ≠ 0) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : κ.Invariant μ) (hν : κ.Invariant ν) :
    μ = ν := by
  by_contra hμν
  let ξ := μ ⊓ ν
  let μ' := μ - ξ
  let ν' := ν - ξ
  have hξμ : ξ ≤ μ := inf_le_left
  have hξν : ξ ≤ ν := inf_le_right
  letI : IsFiniteMeasure ξ := isFiniteMeasure_of_le μ hξμ
  have hcomp_mono {ρ σ : Measure α} (hρσ : ρ ≤ σ) :
      κ ∘ₘ ρ ≤ κ ∘ₘ σ := by
    refine Measure.le_intro fun s hs _ => ?_
    rw [Measure.bind_apply hs κ.aemeasurable,
      Measure.bind_apply hs κ.aemeasurable]
    exact lintegral_mono' hρσ le_rfl
  have hξ : κ.Invariant ξ := by
    have hcomp_le : κ ∘ₘ ξ ≤ ξ := by
      apply le_inf
      · exact (hcomp_mono hξμ).trans_eq hμ.def
      · exact (hcomp_mono hξν).trans_eq hν.def
    exact Measure.eq_of_le_of_measure_univ_eq hcomp_le (by simp)
  have hμ_split : μ' + ξ = μ :=
    Measure.sub_add_cancel_of_le hξμ
  have hν_split : ν' + ξ = ν :=
    Measure.sub_add_cancel_of_le hξν
  have invariant_sub {ρ : Measure α} [IsFiniteMeasure ρ]
      (hξρ : ξ ≤ ρ) (hρ : κ.Invariant ρ) :
      κ.Invariant (ρ - ξ) := by
    have hsplit : ρ - ξ + ξ = ρ :=
      Measure.sub_add_cancel_of_le hξρ
    have heq : κ ∘ₘ (ρ - ξ) + ξ = (ρ - ξ) + ξ := by
      calc
        κ ∘ₘ (ρ - ξ) + ξ = κ ∘ₘ (ρ - ξ) + κ ∘ₘ ξ := by rw [hξ.def]
        _ = κ ∘ₘ ((ρ - ξ) + ξ) := Measure.comp_add.symm
        _ = κ ∘ₘ ρ := by rw [hsplit]
        _ = ρ := hρ.def
        _ = (ρ - ξ) + ξ := hsplit.symm
    apply le_antisymm
    · apply Measure.le_of_add_le_add_left (μ := ξ)
      simpa [add_comm] using heq.le
    · apply Measure.le_of_add_le_add_left (μ := ξ)
      simpa [add_comm] using heq.ge
  have hμ' : κ.Invariant μ' := invariant_sub hξμ hμ
  have hν' : κ.Invariant ν' := invariant_sub hξν hν
  have hsing : μ' ⟂ₘ ν' := by
    apply Measure.mutuallySingular_of_disjoint
    intro ρ hρμ hρν
    have hρξ_le : ρ + ξ ≤ ξ := by
      apply le_inf
      · exact (add_le_add hρμ le_rfl).trans_eq hμ_split
      · exact (add_le_add hρν le_rfl).trans_eq hν_split
    have : ξ + ρ ≤ ξ + 0 := by
      simpa [add_comm] using hρξ_le
    exact Measure.le_of_add_le_add_left this
  have hμ'_ne : μ' ≠ 0 := by
    intro hzero
    apply hμν
    apply Measure.eq_of_le_of_isProbabilityMeasure
    calc
      μ = μ' + ξ := hμ_split.symm
      _ = ξ := by rw [hzero, zero_add]
      _ ≤ ν := hξν
  have hν'_ne : ν' ≠ 0 := by
    intro hzero
    apply hμν
    symm
    apply Measure.eq_of_le_of_isProbabilityMeasure
    calc
      ν = ν' + ξ := hν_split.symm
      _ = ξ := by rw [hzero, zero_add]
      _ ≤ μ := hξμ
  have hφμ : φ ≪ μ' :=
    irreducibleMeasure_absolutelyContinuous_invariant hμ'_ne hμ'
  have hφν : φ ≪ ν' :=
    irreducibleMeasure_absolutelyContinuous_invariant hν'_ne hν'
  have : φ ⟂ₘ φ := hsing.mono_ac hφμ hφν
  exact hφ (Measure.MutuallySingular.self_iff φ |>.mp this)

end AbsorptionCutoff
