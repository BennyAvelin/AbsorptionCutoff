/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.MainTheorems

/-!
# Solution to the stationary power singularity challenge

This file repeats, verbatim, the statement vocabulary and the theorem of
`Audit/PowerSingularity/Challenge.lean`, and proves the theorem from the
development's public index `AbsorptionCutoff.MainTheorems`.

Each audit definition is a literal copy of its project counterpart, so the bridge
lemmas below all hold by `rfl`; they are stated explicitly rather than left to
unification so that any future drift between the two vocabularies fails loudly
here instead of silently changing what the comparator checks.
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

/-! ## Bridges to the development

Each audit definition was copied verbatim from its source module, so every bridge
is `rfl`. Stating them makes any future divergence a build error. -/

lemma gaussianVec_eq (N : ℕ) : gaussianVec N = AbsorptionCutoff.gaussianVec N := rfl

lemma weightVar_eq (A : ℝ) (N : ℕ) : weightVar A N = AbsorptionCutoff.weightVar A N := rfl

lemma gaussianMat_eq (A : ℝ) (N : ℕ) : gaussianMat A N = AbsorptionCutoff.gaussianMat A N := rfl

lemma Pstep_eq (N : ℕ) : Pstep N = AbsorptionCutoff.Pstep N := rfl

lemma Pkernel_eq (A : ℝ) (N : ℕ) : Pkernel A N = AbsorptionCutoff.Pkernel A N := rfl

lemma gaussianSquaredNorm_eq (N : ℕ) :
    gaussianSquaredNorm N = AbsorptionCutoff.gaussianSquaredNorm N := rfl

lemma gaussianEuclideanNorm_eq (N : ℕ) :
    gaussianEuclideanNorm N = AbsorptionCutoff.gaussianEuclideanNorm N := rfl

lemma tanhVec_eq (N : ℕ) : tanhVec N = AbsorptionCutoff.tanhVec N := rfl

lemma logRadius_eq (N : ℕ) : logRadius N = AbsorptionCutoff.logRadius N := rfl

lemma angular_eq (N : ℕ) : angular N = AbsorptionCutoff.angular N := rfl

lemma angularZero_eq (N : ℕ) : angularZero N = AbsorptionCutoff.angularZero N := rfl

lemma logRadialIncrement_eq (A : ℝ) (N : ℕ) :
    logRadialIncrement A N = AbsorptionCutoff.logRadialIncrement A N := rfl

lemma logRadialDrift_eq (A : ℝ) (N : ℕ) :
    logRadialDrift A N = AbsorptionCutoff.logRadialDrift A N := rfl

lemma Supercritical_eq (A : ℝ) (N : ℕ) :
    Supercritical A N = AbsorptionCutoff.Supercritical A N := rfl

lemma gaussianTransferMoment_eq (A : ℝ) (N : ℕ) :
    gaussianTransferMoment A N = AbsorptionCutoff.gaussianTransferMoment A N := rfl

lemma cramerExponent_eq (A : ℝ) (N : ℕ) :
    cramerExponent A N = AbsorptionCutoff.cramerExponent A N := rfl

lemma tiltedIncrementLaw_eq (A : ℝ) (N : ℕ) :
    tiltedIncrementLaw A N = AbsorptionCutoff.tiltedIncrementLaw A N := rfl

lemma etaDefect_eq (N : ℕ) : etaDefect N = AbsorptionCutoff.etaDefect N := rfl

lemma angularPlus_eq (N : ℕ) : angularPlus N = AbsorptionCutoff.angularPlus N := rfl

lemma logPolarLaw_eq (N : ℕ) (π : Measure (Fin N → ℝ)) :
    logPolarLaw N π = AbsorptionCutoff.logPolarLaw N π := rfl

lemma logPolarStep_eq (N : ℕ) : logPolarStep N = AbsorptionCutoff.logPolarStep N := rfl

lemma nonlinearForcingPlusIntegrand_eq (N : ℕ) (y : ℝ) :
    nonlinearForcingPlusIntegrand N y = AbsorptionCutoff.nonlinearForcingPlusIntegrand N y := rfl

lemma nonlinearForcingZeroIntegrand_eq (N : ℕ) (y : ℝ) :
    nonlinearForcingZeroIntegrand N y = AbsorptionCutoff.nonlinearForcingZeroIntegrand N y := rfl

lemma nonlinearForcing_eq (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ)) :
    nonlinearForcing A N π = AbsorptionCutoff.nonlinearForcing A N π := rfl

lemma normalizedSphereLaw_eq (N : ℕ) :
    normalizedSphereLaw N = AbsorptionCutoff.normalizedSphereLaw N := rfl

lemma normalizedAngularLaw_eq (N : ℕ) :
    normalizedAngularLaw N = AbsorptionCutoff.normalizedAngularLaw N := rfl

lemma powerSingularityConstant_eq (A : ℝ) (N : ℕ) (π : Measure (Fin N → ℝ)) :
    powerSingularityConstant A N π = AbsorptionCutoff.powerSingularityConstant A N π := rfl

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
angular constraint dropped. This normalized formulation is equivalent to the
paper's `∼` when `σ̄(B) > 0`; when `σ̄(B) = 0`, it gives the coherent zero-limit
reading without adding a set hypothesis absent from the paper. -/
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
          (nhds (ENNReal.ofReal c))
:=
  AbsorptionCutoff.MainTheorems.nd_power_singularity hA hN hsc π hπ hπ0

end

end AbsorptionCutoff.StatementAudit.PowerSingularity
