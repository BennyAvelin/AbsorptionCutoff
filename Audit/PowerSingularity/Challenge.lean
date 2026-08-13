/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Mathlib

/-!
# Mathlib-only challenge: stationary power singularity

This file is the comparator challenge surface for the paper's fixed-dimensional
stationary result `thm:nd-power-singularity:intro`: in the supercritical regime
every invariant law of the unrounded vector chain that avoids the origin has an
exact power-law singularity at the origin, with exponent the Cramér exponent
`β_{A,N}` and angular part the normalized surface measure.

It imports only `Mathlib`. Every object the statement mentions is rebuilt below
from Mathlib primitives. The source correspondences are:

* `gaussianVec`: `AbsorptionCutoff/Chains.lean`;
* `weightVar`, `gaussianMat`, `Pstep`, `Pkernel`: `AbsorptionCutoff/VectorReduction.lean`;
* `gaussianSquaredNorm`, `gaussianEuclideanNorm`:
  `AbsorptionCutoff/Supercritical/GaussianRadial.lean`;
* `logRadialIncrement`, `logRadialDrift`, `Supercritical`,
  `gaussianTransferMoment`, `cramerExponent`, `tiltedIncrementLaw`:
  `AbsorptionCutoff/Supercritical/StationaryEquation.lean`;
* `tanhVec`, `logRadius`, `angular`, `etaDefect`, `angularPlus`, `angularZero`,
  `logPolarLaw`, `logPolarStep`: `AbsorptionCutoff/Supercritical/LogPolar.lean`;
* the three forcing objects: `AbsorptionCutoff/Supercritical/NonlinearForcing.lean`;
* `normalizedSphereLaw`, `normalizedAngularLaw`, `powerSingularityConstant` and
  the theorem: `AbsorptionCutoff/Supercritical/PowerSingularityRenewal.lean`.

The challenge reproduces `cramerExponent` and `powerSingularityConstant` exactly
as the development defines them: an `sInf` over a root set and a ratio of
integrals. The theorem exposes the coefficient existentially, as in the paper,
while its proof uses `powerSingularityConstant` as the witness.

The only proof omitted in this file is the final theorem's.
-/

namespace AbsorptionCutoff.StatementAudit.PowerSingularity

open Filter MeasureTheory ProbabilityTheory Topology

noncomputable section

/-! ## Gaussian laws and the vector chain -/

/-- `tanh` is continuous; built from `sinh / cosh`. -/
lemma continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')

/-- Standard Gaussian measure on `ℝ^N`. -/
def gaussianVec (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (N : ℕ) : IsProbabilityMeasure (gaussianVec N) := by
  unfold gaussianVec; infer_instance

/-- Entry variance `A²/N` of the Gaussian weight matrix. -/
def weightVar (A : ℝ) (N : ℕ) : NNReal := (A ^ 2 / N).toNNReal

/-- The Gaussian weight-matrix law: independent entries `∼ 𝒩(0, A²/N)`. -/
def gaussianMat (A : ℝ) (N : ℕ) : Measure (Fin N → Fin N → ℝ) :=
  Measure.pi (fun _ => Measure.pi (fun _ => gaussianReal 0 (weightVar A N)))

instance (A : ℝ) (N : ℕ) : IsProbabilityMeasure (gaussianMat A N) := by
  unfold gaussianMat; infer_instance

/-- The vector step map `tanh(𝖶x)`, applied coordinatewise. -/
def Pstep (N : ℕ) (x : Fin N → ℝ) (W : Fin N → Fin N → ℝ) : Fin N → ℝ :=
  fun i => Real.tanh (∑ j, W i j * x j)

lemma measurable_Pstep (N : ℕ) :
    Measurable (fun p : (Fin N → ℝ) × (Fin N → Fin N → ℝ) => Pstep N p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold Pstep
  apply continuous_tanh.measurable.comp
  apply Finset.measurable_sum
  intro j _
  fun_prop

/-- The unrounded vector transition kernel. -/
def Pkernel (A : ℝ) (N : ℕ) : Kernel (Fin N → ℝ) (Fin N → ℝ) :=
  Kernel.map ((Kernel.deterministic id measurable_id).prod (Kernel.const _ (gaussianMat A N)))
    (fun p => Pstep N p.1 p.2)

instance (A : ℝ) (N : ℕ) : IsMarkovKernel (Pkernel A N) := by
  unfold Pkernel
  exact Kernel.IsMarkovKernel.map _ (measurable_Pstep N)

/-! ## Log-radial increments, supercriticality, and the Cramér exponent -/

/-- Squared Euclidean norm on `Fin N → ℝ` (whose default norm is the sup norm). -/
def gaussianSquaredNorm (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  ∑ i, (g i) ^ 2

/-- Euclidean norm on `Fin N → ℝ`. -/
def gaussianEuclideanNorm (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  Real.sqrt (gaussianSquaredNorm N g)

/-- The log-radial increment `−log((A/√N)‖g‖)`. -/
def logRadialIncrement (A : ℝ) (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  -Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g)

/-- The log-radial drift `E[log((A/√N)‖G‖)]`. -/
def logRadialDrift (A : ℝ) (N : ℕ) : ℝ :=
  ∫ g, Real.log ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ∂gaussianVec N

/-- Fixed-dimension supercriticality: the log-radial multiplier has positive drift. -/
def Supercritical (A : ℝ) (N : ℕ) : Prop := 0 < logRadialDrift A N

/-- The Gaussian transfer moment `ℳ_{A,N}(β) = E[((A/√N)‖G‖)^{−β}]`. -/
def gaussianTransferMoment (A : ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  ∫ g, ((A / Real.sqrt N) * gaussianEuclideanNorm N g) ^ (-β) ∂gaussianVec N

/-- The Cramér exponent: the root of `ℳ_{A,N}(β) = 1` in `(0, N)`. -/
def cramerExponent (A : ℝ) (N : ℕ) : ℝ :=
  sInf {β | β ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧ gaussianTransferMoment A N β = 1}

/-- The Cramér-tilted increment law `\hat μ_{A,N}`. -/
def tiltedIncrementLaw (A : ℝ) (N : ℕ) : Measure ℝ :=
  ((gaussianVec N).tilted
      (fun g => cramerExponent A N * logRadialIncrement A N g)).map
    (logRadialIncrement A N)

/-! ## Log-polar coordinates -/

/-- Coordinatewise `tanh`. -/
def tanhVec (N : ℕ) (v : Fin N → ℝ) : Fin N → ℝ := fun i => Real.tanh (v i)

/-- The log-radial coordinate `Y = −log‖x‖₂`. -/
def logRadius (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  -Real.log (gaussianEuclideanNorm N x)

/-- The angular coordinate `Θ = x/‖x‖₂`, valued in the unit sphere. -/
def angular (N : ℕ) (x : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) :=
  (gaussianEuclideanNorm N x)⁻¹ • (WithLp.toLp 2 x)

/-- The nonlinear defect `η`, comparing `tanh(rv)` with its linearization `rv`. -/
def etaDefect (N : ℕ) (r : ℝ) (v : Fin N → ℝ) : ℝ :=
  Real.log (r * gaussianEuclideanNorm N v / gaussianEuclideanNorm N (tanhVec N (r • v)))

/-- The nonlinear angular update `Θ₊`. -/
def angularPlus (N : ℕ) (r : ℝ) (v : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) :=
  angular N (tanhVec N (r • v))

/-- The linearized angular update `Θ₀`. -/
def angularZero (N : ℕ) (v : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) :=
  angular N v

/-- The log-polar law of a state law `π`. -/
def logPolarLaw (N : ℕ) (π : Measure (Fin N → ℝ)) :
    Measure (ℝ × EuclideanSpace ℝ (Fin N)) :=
  π.map fun x => (logRadius N x, angular N x)

/-- One step of the chain in log-polar coordinates. -/
def logPolarStep (N : ℕ) (y : ℝ) (θ : EuclideanSpace ℝ (Fin N))
    (W : Fin N → Fin N → ℝ) : ℝ × EuclideanSpace ℝ (Fin N) :=
  (y - Real.log (gaussianEuclideanNorm N (Matrix.mulVec W (WithLp.ofLp θ)))
     + etaDefect N (Real.exp (-y)) (Matrix.mulVec W (WithLp.ofLp θ)),
   angularPlus N (Real.exp (-y)) (Matrix.mulVec W (WithLp.ofLp θ)))

/-! ## The nonlinear renewal forcing -/

/-- The nonlinear summand of the forcing. -/
def nonlinearForcingPlusIntegrand (N : ℕ) (y : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) : ℝ :=
  if y < (logPolarStep N q.1.1 q.1.2 q.2).1 then
    φ (logPolarStep N q.1.1 q.1.2 q.2).2
  else 0

/-- The linearized summand of the forcing. -/
def nonlinearForcingZeroIntegrand (N : ℕ) (y : ℝ)
    (φ : EuclideanSpace ℝ (Fin N) → ℝ)
    (q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ)) : ℝ :=
  let v := Matrix.mulVec q.2 (WithLp.ofLp q.1.2)
  if y < q.1.1 - Real.log (gaussianEuclideanNorm N v) then
    φ (angularZero N v)
  else 0

/-- The scalar nonlinear renewal forcing `Ψ_y^π(φ)`. -/
def nonlinearForcing (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ))
    (β y : ℝ) (φ : EuclideanSpace ℝ (Fin N) → ℝ) : ℝ :=
  Real.exp (β * y) *
    (∫ q, nonlinearForcingPlusIntegrand N y φ q
        ∂(logPolarLaw N π).prod (gaussianMat A N) -
      ∫ q, nonlinearForcingZeroIntegrand N y φ q
        ∂(logPolarLaw N π).prod (gaussianMat A N))

/-! ## The angular limit law and the singularity constant -/

/-- The normalized surface measure on the unit sphere. -/
def normalizedSphereLaw (N : ℕ) :
    Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere

/-- The normalized surface measure, pushed into the ambient space. -/
def normalizedAngularLaw (N : ℕ) :
    Measure (EuclideanSpace ℝ (Fin N)) :=
  Measure.map Subtype.val (normalizedSphereLaw N)

/-- The power-singularity constant: the total forcing at `φ = 1`, divided by the
mean of the tilted increment law. -/
def powerSingularityConstant
    (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ)) : ℝ :=
  (∫ y, nonlinearForcing A N π (cramerExponent A N) y (fun _ => 1)) /
    (∫ z, z ∂tiltedIncrementLaw A N)

/-! ## The theorem under audit -/

/-- **Stationary power singularity** (paper
`thm:nd-power-singularity:intro`). The paper establishes existence and
uniqueness of its named nonzero invariant law before this theorem and then
fixes that law. Correspondingly, this theorem takes an origin-free invariant
probability as input. The Gamma-form Cramér equation has a unique root, shared
by both conclusions, and the supplied law has a positive power-singularity
coefficient. As `s ↓ 0`,

`s^{−β} · π{0 < ‖x‖ ≤ s, x/‖x‖ ∈ B} → c · σ̄(B)`

for every measurable `B` whose boundary is `σ̄`-null, and the same with the
angular constraint dropped. The directional conclusion is the paper's normalized
formulation, including its coherent zero limit when `σ̄(B) = 0`. For the radial
conclusion, the paper writes the equivalent `π{0 < ‖x‖ ≤ s} ∼ c s^β`; here
`c > 0`. -/
theorem nd_power_singularity
    {A : ℝ} (hA : 0 < A) {N : ℕ} (hN : 0 < N)
    (hsc : Supercritical A N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (hπ0 : π ({0} : Set (Fin N → ℝ)) = 0) :
    ∃ β : ℝ, β ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧
      A ^ (-β) * (N : ℝ) ^ (β / 2) * 2 ^ (-β / 2) *
        Real.Gamma (((N : ℝ) - β) / 2) /
          Real.Gamma ((N : ℝ) / 2) = 1 ∧
      (∀ γ : ℝ, γ ∈ Set.Ioo (0 : ℝ) (N : ℝ) ∧
        A ^ (-γ) * (N : ℝ) ^ (γ / 2) * 2 ^ (-γ / 2) *
          Real.Gamma (((N : ℝ) - γ) / 2) /
            Real.Gamma ((N : ℝ) / 2) = 1 → γ = β) ∧
    ∃ c : ℝ, 0 < c ∧
      (∀ (B : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)),
        MeasurableSet B → normalizedSphereLaw N (frontier B) = 0 →
          Filter.Tendsto
            (fun s =>
              ENNReal.ofReal (s ^ (-β)) *
                π {x | 0 < gaussianEuclideanNorm N x ∧
                  gaussianEuclideanNorm N x ≤ s ∧
                  angular N x ∈ Subtype.val '' B})
            (𝓝[>] (0 : ℝ))
            (nhds (ENNReal.ofReal c * normalizedSphereLaw N B))) ∧
        Filter.Tendsto
          (fun s =>
            ENNReal.ofReal (s ^ (-β)) *
              π {x | 0 < gaussianEuclideanNorm N x ∧
                gaussianEuclideanNorm N x ≤ s})
          (𝓝[>] (0 : ℝ))
          (nhds (ENNReal.ofReal c)) := by
  sorry

end

end AbsorptionCutoff.StatementAudit.PowerSingularity
