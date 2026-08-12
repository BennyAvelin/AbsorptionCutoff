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

The paper's rounded-metastability theorem is exposed below as one combined
paper-facing capstone. The former clause-level declarations remain available
under compatibility names.
-/

namespace AbsorptionCutoff.MainTheorems

/-! ## Fixed-width vanishing-mesh cutoff -/

/-- Paper `thm:rounded-gaussian-nearest-cutoff`, including the pointwise
TV/survival identity, the Gaussian profile for every offset, and the explicit
cutoff corollary. -/
alias rounded_gaussian_nearest_cutoff :=
  AbsorptionCutoff.rounded_gaussian_nearest_cutoff_paper

/-- Compatibility alias for the profile-only public surface from before the
paper theorem was bundled literally. -/
alias rounded_gaussian_nearest_cutoff_profile :=
  AbsorptionCutoff.tendsto_tvDist_roundedPkernel_fixedWidthMesh

/-- Compatibility alias for the first bundled surface, specialized to one
Gaussian offset. -/
alias rounded_gaussian_nearest_cutoff_at :=
  AbsorptionCutoff.rounded_gaussian_nearest_cutoff_paper_at

/-! ## Fixed-precision dimension cutoff -/

/-- Complete public surface of paper
`thm:subcritical-dimension-cutoff:intro` and
`thm:subcritical-dimension-cutoff`: macroscopic rounded initial radii imply
divergence of the deterministic center, the exact `-1`/`+2` survival limits,
and their equivalent total-variation limits. -/
alias subcritical_dimension_cutoff :=
  AbsorptionCutoff.subcritical_dimension_cutoff_roundedVector_paper

/-- Compatibility alias for the detailed theorem
`thm:subcritical-dimension-cutoff`, with cutoff-time divergence supplied as a
hypothesis. -/
alias subcritical_dimension_cutoff_of_tendsto_cutoffTime :=
  AbsorptionCutoff.subcritical_dimension_cutoff_roundedVector

/-- Complete survival-and-TV form of the detailed theorem
`thm:subcritical-dimension-cutoff`, with cutoff-time divergence supplied as a
hypothesis. -/
alias subcritical_dimension_cutoff_full_of_tendsto_cutoffTime :=
  AbsorptionCutoff.subcritical_dimension_cutoff_roundedVector_of_tendsto_cutoffTime

/-- Compatibility alias for the first-pass introduction wrapper, which exposes
the cutoff-time divergence and TV pair but omits the equivalent survival pair. -/
alias subcritical_dimension_cutoff_tv :=
  AbsorptionCutoff.subcritical_dimension_cutoff_roundedVector_intro

/-! ## Rounded metastability and fixed-dimensional absorption -/

/-- Paper `thm:rounded-qualitative-metastability`, including entrance, exit,
exponential persistence, and fixed-dimensional absorption. -/
alias rounded_qualitative_metastability :=
  AbsorptionCutoff.rounded_qualitative_metastability_paper

/-- Compatibility alias for the former conditional scalar persistence API. -/
alias rounded_exponential_persistence_from_rightmost_component :=
  AbsorptionCutoff.exists_exponential_absorption_survival

/-- Stronger scalar-radius formulation of fixed-dimensional absorption,
including survival convergence and allowing every initial radius in the full
canonical interval. -/
alias rounded_fixed_dimension_absorption_scalar :=
  AbsorptionCutoff.tendsto_Hkernel_survival_and_ae_absorption

/-- Fixed-dimensional almost-sure-absorption clause of paper
`thm:rounded-qualitative-metastability`. -/
alias rounded_fixed_dimension_absorption :=
  AbsorptionCutoff.ae_absorption_roundedPkernel_of_rounded_state

/-! ## Supercritical dimension cutoff -/

/-- Paper `thm:gaussian-process-cutoff`. -/
alias gaussian_process_cutoff :=
  AbsorptionCutoff.exists_unique_nonzero_invariant_family_hasCutoff_of_forall_mem_Icc

/-- Paper `cor:gaussian-vector-cutoff`. -/
alias gaussian_vector_cutoff :=
  AbsorptionCutoff.exists_unique_nonzero_invariant_vector_family_cutoff_of_forall_mem_Icc

/-! ## Fixed-dimensional stationary singularity -/

/-- Paper `thm:nd-power-singularity:intro`. -/
alias nd_power_singularity :=
  AbsorptionCutoff.invariant_powerSingularity

end AbsorptionCutoff.MainTheorems
