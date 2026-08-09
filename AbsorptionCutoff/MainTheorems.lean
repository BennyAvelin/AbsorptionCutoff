/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.FixedWidthAbsorptionRegenerationFinal
import AbsorptionCutoff.RoundedVectorReduction
import AbsorptionCutoff.Metastability
import AbsorptionCutoff.Supercritical.CutoffLimitAssembly
import AbsorptionCutoff.Supercritical.PowerSingularityRenewal

/-!
# Main theorems

This file gathers the headline results from the paper's `Main results`
subsection. Each declaration is an alias of the proved capstone in its source
module, so the statements here remain exactly synchronized with the underlying
formalization.

The paper's rounded-metastability theorem has two logically independent
conclusions. They appear below as separate aliases: exponential persistence as
the dimension tends to infinity and almost-sure absorption in every fixed
positive dimension.
-/

namespace AbsorptionCutoff.MainTheorems

/-! ## Fixed-width vanishing-mesh cutoff -/

/-- Paper `thm:rounded-gaussian-nearest-cutoff`. -/
alias rounded_gaussian_nearest_cutoff :=
  AbsorptionCutoff.tendsto_tvDist_roundedPkernel_fixedWidthMesh

/-! ## Fixed-precision dimension cutoff -/

/-- Paper `thm:subcritical-dimension-cutoff`. -/
alias subcritical_dimension_cutoff :=
  AbsorptionCutoff.subcritical_dimension_cutoff_roundedVector

/-! ## Rounded metastability and fixed-dimensional absorption -/

/-- Exponential-persistence clause of paper
`thm:rounded-qualitative-metastability`. -/
alias rounded_qualitative_metastability :=
  AbsorptionCutoff.exists_exponential_absorption_survival

/-- Fixed-dimensional almost-sure-absorption clause of paper
`thm:rounded-qualitative-metastability`. -/
alias rounded_fixed_dimension_absorption :=
  AbsorptionCutoff.tendsto_Hkernel_survival_and_ae_absorption

/-! ## Supercritical dimension cutoff -/

/-- Paper `thm:gaussian-process-cutoff`. -/
alias gaussian_process_cutoff :=
  AbsorptionCutoff.exists_stationary_family_hasCutoff_of_forall_mem_Icc

/-- Paper `cor:gaussian-vector-cutoff`. -/
alias gaussian_vector_cutoff :=
  AbsorptionCutoff.exists_reconstructed_invariant_vector_family_hasCutoff_of_forall_mem_Icc

/-! ## Fixed-dimensional stationary singularity -/

/-- Paper `thm:nd-power-singularity`. -/
alias nd_power_singularity :=
  AbsorptionCutoff.invariant_powerSingularity

end AbsorptionCutoff.MainTheorems
