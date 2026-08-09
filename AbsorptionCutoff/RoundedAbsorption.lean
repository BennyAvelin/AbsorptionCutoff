/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Chains
import AbsorptionCutoff.MarkovTrajectory

/-!
# Absorption time of the rounded Gaussian chain on its canonical path space

Instantiates the abstract absorption-time survival bridges (`AbsorptionTime.lean`) at
the concrete rounded squared-radius chain `Hkernel A ρ N` (`Chains.lean`) run on its
canonical Ionescu–Tulcea path law (`MarkovTrajectory.lean`). This closes
`eq:tv-absorption` in `τ`-form: the survival probability of the absorption time
`τ_ρ` (the first hitting time of the absorbing state `0` by the coordinate process)
equals the terminal off-origin mass `(H^t)(x, {0}ᶜ)`, and the TV distance to the
absorbing point mass `δ₀` is its real cast.

## Main results
* `AbsorptionCutoff.measure_roundedAbsorptionTime_gt_eq` — `ℙ(τ_ρ > t) = (H^t)(x, {0}ᶜ)`.
* `AbsorptionCutoff.tvDist_Hkernel_pow_eq_survival` — `‖H^t(x,·) − δ₀‖_TV = ℙ(τ_ρ > t)`.
-/

open MeasureTheory ProbabilityTheory

namespace AbsorptionCutoff

/-- **Survival identity for the rounded Gaussian chain** (`eq:tv-absorption`, `τ`-form).
Under the canonical path law started at `x`, the probability that the absorption time
`τ_ρ` (first hitting time of `0` by the coordinate process `ω ↦ ω s`) exceeds `t` equals
the off-origin mass of the `t`-step kernel: `ℙ(τ_ρ > t) = (H^t)(x, {0}ᶜ)`.

The three inputs to the abstract a.e.-bridge `measure_absorptionTime_gt_eq_of_ae_kernel_pow`
are: a.e. absorption of the coordinate process (`markovPathMeasure_ae_absorbing`, fed the
concrete trap `isAbsorbing_Hkernel : H(0,·) = δ₀`), measurability of the coordinate map
(`measurable_pi_apply`), and the coordinate-marginal law (`markovPathMeasure_dirac_map_eval`,
`map (·t) = (H^t)x`). -/
theorem measure_roundedAbsorptionTime_gt_eq (A ρ : ℝ) (N : ℕ) (x : ℝ) (t : ℕ) :
    (markovPathMeasure (Measure.dirac x) (Hkernel A ρ N))
        {ω | (t : WithTop ℕ) < absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω}
      = ((Hkernel A ρ N) ^ t) x ({0}ᶜ) :=
  measure_absorptionTime_gt_eq_of_ae_kernel_pow (X := fun (s : ℕ) (ω : ℕ → ℝ) => ω s)
    (κ := Hkernel A ρ N) (x := x)
    (fun s => markovPathMeasure_ae_absorbing (Measure.dirac x) (Hkernel A ρ N)
      (isAbsorbing_Hkernel A ρ N) s)
    t (measurable_pi_apply t)
    (markovPathMeasure_dirac_map_eval x (Hkernel A ρ N) t)

/-- **`eq:tv-absorption` in `τ`-form for the rounded Gaussian chain.** The TV distance
from the `t`-step law started at `x` to the absorbing point mass `δ₀` equals the survival
probability `ℙ(τ_ρ > t)` (as a real). Combines the kernel-form `tvDist_Hkernel_pow_dirac`
with the survival identity `measure_roundedAbsorptionTime_gt_eq`. -/
theorem tvDist_Hkernel_pow_eq_survival (A ρ : ℝ) (N : ℕ) (x : ℝ) (t : ℕ) :
    tvDist (((Hkernel A ρ N) ^ t) x) (Measure.dirac 0)
      = ((markovPathMeasure (Measure.dirac x) (Hkernel A ρ N))
          {ω | (t : WithTop ℕ) < absorptionTime (fun (s : ℕ) (ω : ℕ → ℝ) => ω s) ω}).toReal := by
  rw [tvDist_Hkernel_pow_dirac, measure_roundedAbsorptionTime_gt_eq]

end AbsorptionCutoff
