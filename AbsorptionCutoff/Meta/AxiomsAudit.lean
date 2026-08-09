/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.MainTheorems

/-!
# Axiom audit

Machine-checked record of the axioms the headline theorems depend on.

This development contains no `sorry` and declares no custom `axiom`, so every
public theorem reduces to Mathlib's three standard foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`. Building this file prints
those dependencies for inspection (see the CI log).

The module is deliberately **not** imported by `AbsorptionCutoff.lean`: it exists only
for its `#print axioms` output, and is built explicitly with
`lake build AbsorptionCutoff.Meta.AxiomsAudit`, which keeps the default `lake build`
free of informational traces.
-/

/-! ## Fixed-width vanishing-mesh cutoff -/

#print axioms AbsorptionCutoff.MainTheorems.rounded_gaussian_nearest_cutoff

/-! ## Fixed-precision dimension cutoff -/

#print axioms AbsorptionCutoff.MainTheorems.subcritical_dimension_cutoff

/-! ## Rounded metastability and fixed-dimensional absorption -/

#print axioms AbsorptionCutoff.MainTheorems.rounded_qualitative_metastability
#print axioms AbsorptionCutoff.MainTheorems.rounded_fixed_dimension_absorption

/-! ## Supercritical dimension cutoff -/

#print axioms AbsorptionCutoff.MainTheorems.gaussian_process_cutoff
#print axioms AbsorptionCutoff.MainTheorems.gaussian_vector_cutoff

/-! ## Fixed-dimensional stationary singularity -/

#print axioms AbsorptionCutoff.MainTheorems.nd_power_singularity
