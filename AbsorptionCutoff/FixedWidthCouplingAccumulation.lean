/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthCouplingSubproducts

/-!
# Fixed-width accumulated coupling error

This continuation module extracts the iid multiplier process from sequential
independence, proves the required subproduct bounds, and accumulates the scalar
rounding recursion over logarithmic time horizons.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Sequential independence of each finite prefix from its next coordinate
implies mutual independence of every finite initial segment. -/
lemma iIndepFun_fin_prefix_of_indepFun_prefix_next
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : ℕ → Ω → β)
    (hf : ∀ n, Measurable (f n))
    (hseq : ∀ n, IndepFun (fun ω (i : Fin n) ↦ f i ω) (f n) μ) :
    ∀ n, iIndepFun (fun i : Fin n ↦ f i) μ := by
  intro n
  induction n with
  | zero =>
      rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
      intro S sets hsets
      have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
      subst S
      simp
  | succ n ih =>
      rw [iIndepFun_iff_map_fun_eq_pi_map
        (fun i : Fin (n + 1) ↦ (hf i).aemeasurable)]
      let e : (Fin (n + 1) → β) ≃ᵐ β × (Fin n → β) :=
        MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ β) (Fin.last n)
      rw [← e.map_measurableEquiv_injective.eq_iff]
      calc
        Measure.map e
            (Measure.map (fun ω (i : Fin (n + 1)) ↦ f i ω) μ) =
            Measure.map
              (fun ω ↦ (f n ω, fun i : Fin n ↦ f i ω)) μ := by
          rw [Measure.map_map e.measurable]
          · congr 1
            funext ω
            apply Prod.ext
            · simp [e]
            · funext i
              simp only [Function.comp_apply]
              dsimp [e, MeasurableEquiv.piFinSuccAbove,
                Fin.insertNthEquiv, Fin.removeNth]
              rw [Fin.succAbove_last]
              rfl
          · exact measurable_pi_lambda _ fun i ↦ hf i
        _ = (Measure.map (f n) μ).prod
            (Measure.map (fun ω (i : Fin n) ↦ f i ω) μ) :=
          (hseq n).symm.map_prod_eq_prod_map_map
            (hf n).aemeasurable
            (measurable_pi_lambda
              (fun ω (i : Fin n) ↦ f i ω) fun i ↦ hf i).aemeasurable
        _ = (Measure.map (f n) μ).prod
            (Measure.pi (fun i : Fin n ↦ Measure.map (f i) μ)) := by
          rw [(iIndepFun_iff_map_fun_eq_pi_map
            (fun i : Fin n ↦ (hf i).aemeasurable)).mp ih]
        _ = Measure.map e
            (Measure.pi (fun i : Fin (n + 1) ↦ Measure.map (f i) μ)) := by
          have hmap := (measurePreserving_piFinSuccAbove
            (fun i : Fin (n + 1) ↦ Measure.map (f i) μ)
            (Fin.last n)).map_eq
          simpa [e] using hmap.symm

/-- Mutual independence of every finite initial segment implies mutual
independence of the full sequence. -/
lemma iIndepFun_of_iIndepFun_fin_prefix
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (f : ℕ → Ω → β)
    (hfin : ∀ n, iIndepFun (fun i : Fin n ↦ f i) μ) :
    iIndepFun f μ := by
  rw [iIndepFun_iff_finset]
  intro s
  let g : s → Fin (s.sup id + 1) := fun i ↦
    ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    exact congrArg Fin.val hij
  have hind := (hfin (s.sup id + 1)).precomp (g := g) hg
  change iIndepFun (fun i : s ↦ f i) μ
  simpa only [g] using hind

/-- The synchronous discrepancy multipliers form a mutually independent
process under the canonical matrix Gaussian law. -/
lemma iIndepFun_fixedWidthDiscrepancyMultiplier
    (A : ℝ) {N : ℕ} (hN : 0 < N) (ρ : ℝ) (x0 : Fin N → ℝ) :
    iIndepFun
      (fixedWidthDiscrepancyMultiplier hN ρ x0)
      (fixedWidthMatrixGaussianMeasure A N) := by
  apply iIndepFun_of_iIndepFun_fin_prefix
  apply iIndepFun_fin_prefix_of_indepFun_prefix_next
  · exact fun n ↦ measurable_fixedWidthDiscrepancyMultiplier hN ρ x0 n
  · intro n
    change IndepFun
      (fixedWidthDiscrepancyMultiplierPrefix hN ρ x0 n)
      (fixedWidthDiscrepancyMultiplier hN ρ x0 n)
      (fixedWidthMatrixGaussianMeasure A N)
    exact indepFun_fixedWidthDiscrepancyMultiplierPrefix_next A hN ρ x0 n

end AbsorptionCutoff
