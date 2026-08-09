/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.StationaryEquation
import AbsorptionCutoff.Supercritical.RenewalApprox
import AbsorptionCutoff.Supercritical.RenewalEquation

/-!
# The key renewal theorem at the tilted increment law (§7)

Continuation of `AbsorptionCutoff.Supercritical.StationaryEquation`, split off at the
point where that module reached 1861 lines and a 106 s focused build. It is the
*join* of the chapter's two halves: `StationaryEquation` supplies the tilted
increment law `μ̂_{A,N}` together with every hypothesis the abstract renewal
theory asks for — nonlatticeness, a finite second moment, positive drift, and a
strict exponential moment below the Cramér exponent — while `RenewalApprox`
supplies the abstract key renewal theorem itself. Neither module imports the
other, so the instantiation belongs here.

This is unit **A-6** of the Chapter 7 lane: the input that paper
`lem:nd-gaussian-renewal` consumes.

## Deviation to keep in view

The abstract theorem `Renewal.tendsto_tsum_integral_comp_sub_of_driNorm` is
proved by approximation in the directly-Riemann-integrable norm rather than
through Feller's interval theorem, and therefore asks for a **continuous**
kernel where the paper asks only for an a.e. continuous one. Indicators are not
`‖·‖_DRI`-approximable by continuous functions, so the gap is real. It is
harmless for the chapter, whose forcing is Gaussian-driven hence atomless, but
continuity of the forcing is an explicit obligation at every application of the
theorems below — not something free.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AbsorptionCutoff

/-! ### A-6 — the key renewal theorem at `μ̂_{A,N}` -/

/-- **The key renewal theorem for the tilted log-radial walk** (paper
`lem:nd-gaussian-renewal`, the linear-renewal input of §7).

For every continuous kernel `z` of finite directly-Riemann-integrable norm,

`∑ₙ ∫ z(y − s) μ̂_{A,N}^{*n}(ds) ⟶ (∫ z) / m̂_{A,N}`  as  `y → ∞`,

where `m̂_{A,N} = ∫ z dμ̂_{A,N} > 0` is the tilted drift. All four hypotheses of
the abstract theorem are discharged from §7's own analysis of the tilted
increment law:

* nonlattice — `tiltedIncrementLaw_not_concentrated_on_lattice`, from
  atomlessness of the Gaussian radial law;
* `MemLp id 2` — `memLp_id_two_tiltedIncrementLaw`;
* positive drift — `integral_id_tiltedIncrementLaw_pos`, i.e.
  `F'(β_{A,N}) > 0`;
* a strict exponential moment — `expTransform_tiltedIncrementLaw_lt_one` at
  `θ = β_{A,N}/2`, which is the Chernoff bound `ℳ_{A,N}(β_{A,N}/2) < 1`
  strictly below the Cramér root.

Only `hzc` is an obligation left to the caller; see the module doc-string. -/
theorem tendsto_tsum_integral_comp_sub_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) {z : ℝ → ℂ} (hzc : Continuous z)
    (hz : Renewal.driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto
      (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(Renewal.convPow (tiltedIncrementLaw A N) n))
      Filter.atTop
      (nhds ((∫ x : ℝ, z x) / ((∫ x, x ∂tiltedIncrementLaw A N : ℝ) : ℂ))) := by
  haveI := isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  have hβmem := cramerExponent_mem hA hN hsc
  exact Renewal.tendsto_tsum_integral_comp_sub_of_driNorm
    (tiltedIncrementLaw_not_concentrated_on_lattice hA hN)
    (memLp_id_two_tiltedIncrementLaw hA hN hsc)
    (integral_id_tiltedIncrementLaw_pos hA hN hsc)
    (θ := cramerExponent A N / 2) (by linarith [hβmem.1])
    (expTransform_tiltedIncrementLaw_lt_one hA hN hsc (by linarith [hβmem.1])
      (by linarith [hβmem.1]))
    hzc hz

/-- **The key renewal theorem at `μ̂_{A,N}`, for real-valued kernels** (A-6b).
Real form of `tendsto_tsum_integral_comp_sub_tiltedIncrementLaw`; this is the
shape paper `lem:nd-gaussian-renewal` consumes, its forcing `Ψ_y(1)` being a
total-variation mass and hence real. -/
theorem tendsto_tsum_integral_comp_sub_tiltedIncrementLaw_real {A : ℝ} (hA : 0 < A)
    {N : ℕ} (hN : 0 < N) (hsc : Supercritical A N) {z : ℝ → ℝ} (hzc : Continuous z)
    (hz : Renewal.driNorm (fun x => ‖z x‖ₑ) ≠ ∞) :
    Filter.Tendsto
      (fun y : ℝ => ∑' n, ∫ s, z (y - s) ∂(Renewal.convPow (tiltedIncrementLaw A N) n))
      Filter.atTop
      (nhds ((∫ x : ℝ, z x) / (∫ x, x ∂tiltedIncrementLaw A N))) := by
  haveI := isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  have hβmem := cramerExponent_mem hA hN hsc
  exact Renewal.tendsto_tsum_integral_comp_sub_of_driNorm_real
    (tiltedIncrementLaw_not_concentrated_on_lattice hA hN)
    (memLp_id_two_tiltedIncrementLaw hA hN hsc)
    (integral_id_tiltedIncrementLaw_pos hA hN hsc)
    (θ := cramerExponent A N / 2) (by linarith [hβmem.1])
    (expTransform_tiltedIncrementLaw_lt_one hA hN hsc (by linarith [hβmem.1])
      (by linarith [hβmem.1]))
    hzc hz

/-! ### `lem:nd-gaussian-renewal` — the paper-facing renewal limit

`AbsorptionCutoff.Supercritical.RenewalEquation` proves the abstract renewal-equation
solution theory; the two theorems below instantiate it at the tilted increment
law, which is the form paper §7 uses.
-/

/-- **Scalar form of `lem:nd-gaussian-renewal`.** A solution of the renewal
equation driven by `μ̂_{A,N}`, with continuous directly Riemann integrable
forcing, satisfies

  `h y ⟶ (∫ ψ) / m̂_{A,N}`  as  `y → ∞`.

The hypotheses on `h` and `ψ` are the paper's own, transcribed:
`hbot` is `eq:nd-renewal-left-boundary`, `htop` is
`eq:nd-renewal-right-minimality`, `hloc` is local boundedness, `hren` is the
scalar renewal equation obtained from `eq:nd-abstract-renewal-equation` at
`φ = 1`, and `hψd` is `eq:nd-dri-definition`. `hψc` is the standing continuity
obligation of the d.R.i.-norm route — the paper asks only for a.e. continuity.

Everything about `μ̂_{A,N}` itself is discharged here from §7's own analysis; in
particular `hexp` is `𝔼e^{−β_{A,N}Sₙ} = 1`, which is
`expTransform_convPow_tiltedIncrementLaw`. -/
theorem tendsto_of_renewalEquation_tiltedIncrementLaw {A : ℝ} (hA : 0 < A) {N : ℕ}
    (hN : 0 < N) (hsc : Supercritical A N) {h ψ : ℝ → ℝ}
    (hψc : Continuous ψ) (hψd : Renewal.driNorm (fun x => ‖ψ x‖ₑ) ≠ ∞)
    (hh : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => h (y - s))
      (Renewal.convPow (tiltedIncrementLaw A N) n))
    (hren : ∀ y : ℝ, h y = (∫ z, h (y - z) ∂tiltedIncrementLaw A N) + ψ y)
    (hbot : Filter.Tendsto h Filter.atBot (nhds 0))
    (hloc : ∀ L : ℝ, ∃ C : ℝ, ∀ u, u ≤ L → |h u| ≤ C)
    (htop : Filter.Tendsto (fun u => Real.exp (-(cramerExponent A N * u)) * |h u|)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto h Filter.atTop
      (nhds ((∫ x : ℝ, ψ x) / (∫ x, x ∂tiltedIncrementLaw A N))) := by
  haveI := isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  have hβmem := cramerExponent_mem hA hN hsc
  exact Renewal.tendsto_of_renewalEquation_of_driNorm
    (tiltedIncrementLaw_not_concentrated_on_lattice hA hN)
    (memLp_id_two_tiltedIncrementLaw hA hN hsc)
    (integral_id_tiltedIncrementLaw_pos hA hN hsc)
    (θ := cramerExponent A N / 2) (by linarith [hβmem.1])
    (expTransform_tiltedIncrementLaw_lt_one hA hN hsc (by linarith [hβmem.1])
      (by linarith [hβmem.1]))
    (expTransform_convPow_tiltedIncrementLaw hA hN hsc)
    hψc hψd hh hren hbot hloc htop

/-- **`lem:nd-gaussian-renewal`, `eq:nd-abstract-renewal-limit`.** For every
continuous test function `φ` on the sphere, writing `a = ∫ φ dσ̄_N`,

  `ℋ_y(φ) ⟶ (∫ φ dσ̄_N) · (∫ Ψ_t(1) dt) / m̂_{A,N}`.

`Hφ = y ↦ ℋ_y(φ)` and `Ψφ = y ↦ Ψ_y(φ)`; `h` and `ψ` are their `φ = 1`
counterparts. `hang` is the paper's display at L4901–4906, which the product form
of the tilted kernel `eq:nd-tilted-kernel` supplies: the angular integral factors
out as the constant `a`, leaving the same scalar convolution for every `φ`. That
is why no measure on `𝕊^{N−1}` appears anywhere in the statement. -/
theorem tendsto_angular_of_renewalEquation_tiltedIncrementLaw {A : ℝ} (hA : 0 < A)
    {N : ℕ} (hN : 0 < N) (hsc : Supercritical A N) {h ψ Hφ Ψφ : ℝ → ℝ} {a : ℝ}
    (hψc : Continuous ψ) (hψd : Renewal.driNorm (fun x => ‖ψ x‖ₑ) ≠ ∞)
    (hΨφd : Renewal.driNorm (fun x => ‖Ψφ x‖ₑ) ≠ ∞)
    (hh : ∀ (n : ℕ) (y : ℝ), Integrable (fun s => h (y - s))
      (Renewal.convPow (tiltedIncrementLaw A N) n))
    (hren : ∀ y : ℝ, h y = (∫ z, h (y - z) ∂tiltedIncrementLaw A N) + ψ y)
    (hang : ∀ y : ℝ, Hφ y = a * (∫ z, h (y - z) ∂tiltedIncrementLaw A N) + Ψφ y)
    (hbot : Filter.Tendsto h Filter.atBot (nhds 0))
    (hloc : ∀ L : ℝ, ∃ C : ℝ, ∀ u, u ≤ L → |h u| ≤ C)
    (htop : Filter.Tendsto (fun u => Real.exp (-(cramerExponent A N * u)) * |h u|)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto Hφ Filter.atTop
      (nhds (a * ((∫ x : ℝ, ψ x) / (∫ x, x ∂tiltedIncrementLaw A N)))) := by
  haveI := isProbabilityMeasure_tiltedIncrementLaw hA hN hsc
  have hβmem := cramerExponent_mem hA hN hsc
  exact Renewal.tendsto_angular_of_renewalEquation_of_driNorm
    (tiltedIncrementLaw_not_concentrated_on_lattice hA hN)
    (memLp_id_two_tiltedIncrementLaw hA hN hsc)
    (integral_id_tiltedIncrementLaw_pos hA hN hsc)
    (θ := cramerExponent A N / 2) (by linarith [hβmem.1])
    (expTransform_tiltedIncrementLaw_lt_one hA hN hsc (by linarith [hβmem.1])
      (by linarith [hβmem.1]))
    (expTransform_convPow_tiltedIncrementLaw hA hN hsc)
    hψc hψd hΨφd hh hren hang hbot hloc htop

end AbsorptionCutoff
