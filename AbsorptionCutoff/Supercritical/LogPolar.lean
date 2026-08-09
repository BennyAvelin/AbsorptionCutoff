/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import AbsorptionCutoff.Supercritical.StationaryRenewal

/-!
# Log-polar coordinates for the supercritical stationary law (§7)

Unit **A-8-pre** of the Chapter 7 lane. Paper §7 states its nonlinear half —
`lem:nd-gaussian-polar-perturbation`, the nonlinear renewal forcing, and
`thm:nd-power-singularity` — entirely in log-polar coordinates

  `r = ‖x‖₂`,  `θ = x/‖x‖₂`,  `y = −log r`,

so that a power singularity of `π_{A,N}` at the origin becomes an exponential
tail for `Y`. Nothing of this apparatus existed in the repo: only the *Cartesian*
weak stationary equation (`vector_stationary_equation`) did.

This module is also where `𝕊^{N−1}` enters the formalization for the first time.
The angular variable lives on `EuclideanSpace ℝ (Fin N)`, following the existing
convention in `GaussianRadial.lean` and `StationaryEquation.lean`: chain
coordinates are `Fin N → ℝ`, and `WithLp.toLp 2` transports them to
`EuclideanSpace` wherever isotropy or the norm is needed
(`map_toLp_gaussianVec`, `gaussianEuclideanNorm_eq_norm`).

Contents follow tex L4505–4610:

* `logRadius`, `angular` — the coordinates `Y` and `Θ`;
* `etaDefect` — the nonlinear defect `η` of `eq:nd-eta-definition`, which
  measures how much `tanh` contracts the step below its linearization;
* `angularPlus`, `angularZero` — the true and linearized angular updates of
  `eq:nd-angular-definitions`.

The full log-polar stationary equation `eq:nd-log-polar-stationary` and the
linearized kernel are developed in the subsequent A-8 units.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace AbsorptionCutoff

/-! ### The coordinates

Throughout, `gaussianEuclideanNorm N` is — despite its name, which records where
it was first needed — the plain Euclidean norm of a coordinate vector; see
`gaussianEuclideanNorm_eq_norm`. -/

/-- Coordinatewise `tanh`. The vector chain's update is `tanh` applied entrywise
to `A‖x‖₂ g/√N`, so this is the nonlinearity that separates the true log-polar
step from its linearization. -/
noncomputable def tanhVec (N : ℕ) (v : Fin N → ℝ) : Fin N → ℝ := fun i => Real.tanh (v i)

/-- `tanh` is a coordinatewise contraction, so it does not increase the Euclidean
norm. This is what makes the defect `η` below nonnegative. -/
lemma gaussianEuclideanNorm_tanhVec_le (N : ℕ) (v : Fin N → ℝ) :
    gaussianEuclideanNorm N (tanhVec N v) ≤ gaussianEuclideanNorm N v := by
  unfold gaussianEuclideanNorm
  refine Real.sqrt_le_sqrt ?_
  simp only [gaussianSquaredNorm, tanhVec]
  exact Finset.sum_le_sum fun i _ => tanh_sq_le_sq (v i)

/-- The Euclidean norm is absolutely homogeneous. -/
lemma gaussianEuclideanNorm_smul (N : ℕ) (r : ℝ) (v : Fin N → ℝ) :
    gaussianEuclideanNorm N (r • v) = |r| * gaussianEuclideanNorm N v := by
  simp only [gaussianEuclideanNorm, gaussianSquaredNorm, Pi.smul_apply, smul_eq_mul, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

/-- The paper's logarithmic radial coordinate `Y = −log‖x‖₂` (tex L4505–4507).
The origin corresponds to `Y = +∞`, so a power singularity of `π_{A,N}` at zero
is an exponential tail for `Y`. -/
noncomputable def logRadius (N : ℕ) (x : Fin N → ℝ) : ℝ :=
  -Real.log (gaussianEuclideanNorm N x)

/-- The paper's angular coordinate `Θ = x/‖x‖₂`, valued in `𝕊^{N−1}` inside
`EuclideanSpace ℝ (Fin N)`. -/
noncomputable def angular (N : ℕ) (x : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) :=
  (gaussianEuclideanNorm N x)⁻¹ • (WithLp.toLp 2 x)

/-- `Θ` really does land on the unit sphere, away from the origin. -/
lemma norm_angular (N : ℕ) {x : Fin N → ℝ} (hx : gaussianEuclideanNorm N x ≠ 0) :
    ‖angular N x‖ = 1 := by
  have hpos : 0 < gaussianEuclideanNorm N x :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity) (Ne.symm hx)
  rw [angular, norm_smul, ← gaussianEuclideanNorm_eq_norm, norm_inv, Real.norm_eq_abs,
    abs_of_pos hpos, inv_mul_cancel₀ hx]

/-! ### The nonlinear defect and the two angular updates -/

/-- The **nonlinear defect** `η` of `eq:nd-eta-definition`:

  `η(r, v) = log (r‖v‖₂ / ‖tanh(r v)‖₂)`,

measuring how much the `tanh` step falls short of its linearization. The paper
writes `η(r, θ, W)` with `v = Wθ`; the definition depends on `(θ, W)` only
through that product, so it is stated here in `v`. -/
noncomputable def etaDefect (N : ℕ) (r : ℝ) (v : Fin N → ℝ) : ℝ :=
  Real.log (r * gaussianEuclideanNorm N v / gaussianEuclideanNorm N (tanhVec N (r • v)))

/-- **`η ≥ 0`.** The step `tanh(rv)` is never longer than its linearization `rv`,
so the ratio defining `η` is at least one. This sign is exactly what makes the
nonlinear renewal forcing nonnegative at `φ = 1`
(`prop:nd-forcing-admissibility`, tex L5255–5262). -/
lemma etaDefect_nonneg (N : ℕ) {r : ℝ} (hr : 0 < r) {v : Fin N → ℝ}
    (hv : gaussianEuclideanNorm N (tanhVec N (r • v)) ≠ 0) :
    0 ≤ etaDefect N r v := by
  have hb0 : 0 < gaussianEuclideanNorm N (tanhVec N (r • v)) :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity) (Ne.symm hv)
  have hle : gaussianEuclideanNorm N (tanhVec N (r • v)) ≤ r * gaussianEuclideanNorm N v := by
    have h1 := gaussianEuclideanNorm_tanhVec_le N (r • v)
    rwa [gaussianEuclideanNorm_smul, abs_of_pos hr] at h1
  exact Real.log_nonneg (by rw [le_div_iff₀ hb0, one_mul]; exact hle)

/-- The true angular update `Θ₊` of `eq:nd-angular-definitions`: the direction of
the actual `tanh` step. -/
noncomputable def angularPlus (N : ℕ) (r : ℝ) (v : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) :=
  angular N (tanhVec N (r • v))

/-- The linearized angular update `Θ₀` of `eq:nd-angular-definitions`: the
direction of `Wθ` itself, with the nonlinearity dropped. The whole nonlinear
renewal forcing is the discrepancy between the `Θ₊` and `Θ₀` pictures. -/
noncomputable def angularZero (N : ℕ) (v : Fin N → ℝ) : EuclideanSpace ℝ (Fin N) :=
  angular N v

/-! ### The left boundary of the log-radial variable -/

/-- On the state space `𝒦_N ⊆ [−1,1]^N` the Euclidean norm is at most `√N`. -/
lemma gaussianEuclideanNorm_le_sqrt_nat (N : ℕ) {x : Fin N → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    gaussianEuclideanNorm N x ≤ Real.sqrt N := by
  unfold gaussianEuclideanNorm
  refine Real.sqrt_le_sqrt ?_
  simp only [gaussianSquaredNorm]
  calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        have := hx i; nlinarith [abs_nonneg (x i), sq_abs (x i)]
    _ = N := by simp

/-- **`Y ≥ −½ log N`** on the state space (tex L4511–4513). This is the source of
the renewal equation's left-boundary condition
`eq:nd-renewal-left-boundary`: below `−½log N` the weighted tail measure `ℋ_y`
has mass at most `e^{β_{A,N} y}`, which vanishes as `y → −∞`. -/
lemma neg_half_log_le_logRadius (N : ℕ) {x : Fin N → ℝ} (hx : ∀ i, |x i| ≤ 1)
    (hx0 : gaussianEuclideanNorm N x ≠ 0) :
    -(Real.log N / 2) ≤ logRadius N x := by
  have hpos : 0 < gaussianEuclideanNorm N x :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity) (Ne.symm hx0)
  have hN : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with hN0 | hN0
    · subst hN0; simp [gaussianEuclideanNorm, gaussianSquaredNorm] at hpos
    · exact_mod_cast hN0
  have hle := gaussianEuclideanNorm_le_sqrt_nat N hx
  have hlog : Real.log (gaussianEuclideanNorm N x) ≤ Real.log N / 2 := by
    calc Real.log (gaussianEuclideanNorm N x) ≤ Real.log (Real.sqrt N) :=
          Real.log_le_log hpos hle
      _ = Real.log N / 2 := by
          rw [Real.log_sqrt hN.le]
  simpa [logRadius, neg_le_neg_iff] using hlog

/-! ### Measurability

All four maps are stated unconditionally. `angular` and `etaDefect` are only
*meaningful* off `{‖x‖₂ = 0}`, but Lean's junk values (`Real.log 0 = 0`,
`(0 : ℝ)⁻¹ = 0`) keep them total, and the origin is `π_{A,N}`-null anyway by
origin-freeness, so nothing downstream needs the restriction. -/

lemma measurable_gaussianEuclideanNorm (N : ℕ) : Measurable (gaussianEuclideanNorm N) := by
  unfold gaussianEuclideanNorm
  exact (measurable_gaussianSquaredNorm N).sqrt

lemma measurable_tanhVec (N : ℕ) : Measurable (tanhVec N) :=
  measurable_pi_lambda _ fun i => continuous_tanh.measurable.comp (measurable_pi_apply i)

lemma measurable_logRadius (N : ℕ) : Measurable (logRadius N) :=
  ((measurable_gaussianEuclideanNorm N).log).neg

lemma measurable_angular (N : ℕ) : Measurable (angular N) := by
  unfold angular
  exact ((measurable_gaussianEuclideanNorm N).inv).smul (by fun_prop)

/-- Scaling is jointly measurable in the scalar and the vector; both `η` and `Θ₊`
are built on `r • v`, and the forcing integrates over `r = e^{−Y}` as well as
over the Gaussian, so joint measurability is what is actually needed. -/
lemma measurable_smul_prod (N : ℕ) : Measurable fun p : ℝ × (Fin N → ℝ) => p.1 • p.2 :=
  measurable_fst.smul measurable_snd

lemma measurable_etaDefect (N : ℕ) :
    Measurable fun p : ℝ × (Fin N → ℝ) => etaDefect N p.1 p.2 := by
  unfold etaDefect
  refine Measurable.log
    ((measurable_fst.mul ((measurable_gaussianEuclideanNorm N).comp measurable_snd)).div ?_)
  exact (measurable_gaussianEuclideanNorm N).comp
    ((measurable_tanhVec N).comp (measurable_smul_prod N))

lemma measurable_angularPlus (N : ℕ) :
    Measurable fun p : ℝ × (Fin N → ℝ) => angularPlus N p.1 p.2 :=
  (measurable_angular N).comp ((measurable_tanhVec N).comp (measurable_smul_prod N))

lemma measurable_angularZero (N : ℕ) : Measurable (angularZero N) := measurable_angular N

/-! ### The log-polar law `Ω_{A,N}` -/

lemma measurable_logPolarCoords (N : ℕ) :
    Measurable fun x : Fin N → ℝ => (logRadius N x, angular N x) :=
  (measurable_logRadius N).prodMk (measurable_angular N)

/-- The **log-polar law** `Ω_{A,N}` (tex L4509–4511): the image of the invariant
law `π_{A,N}` under `x ↦ (Y, Θ) = (−log‖x‖₂, x/‖x‖₂)`.

Everything in §7's nonlinear half is an assertion about this law: the power
singularity of `π_{A,N}` at the origin is the exponential tail of its first
marginal, and the limiting angular law `σ̄_N` is the limit of its conditional
second marginal. -/
noncomputable def logPolarLaw (N : ℕ) (π : Measure (Fin N → ℝ)) :
    Measure (ℝ × EuclideanSpace ℝ (Fin N)) :=
  π.map fun x => (logRadius N x, angular N x)

instance isProbabilityMeasure_logPolarLaw (N : ℕ) (π : Measure (Fin N → ℝ))
    [IsProbabilityMeasure π] : IsProbabilityMeasure (logPolarLaw N π) :=
  Measure.isProbabilityMeasure_map (measurable_logPolarCoords N).aemeasurable

/-- Integration against `Ω_{A,N}` is integration of the composed function against
`π_{A,N}`. This is the form every later computation uses. -/
lemma integral_logPolarLaw (N : ℕ) (π : Measure (Fin N → ℝ))
    {Ξ : ℝ × EuclideanSpace ℝ (Fin N) → ℝ} (hΞ : AEStronglyMeasurable Ξ (logPolarLaw N π)) :
    ∫ p, Ξ p ∂logPolarLaw N π = ∫ x, Ξ (logRadius N x, angular N x) ∂π := by
  rw [logPolarLaw, integral_map (measurable_logPolarCoords N).aemeasurable hΞ]

/-! ### One chain step in log-polar coordinates

The pointwise half of `eq:nd-log-polar-stationary` (tex L4534–4548): a single
application of `Pstep` decomposes exactly into the linear log-radial increment
`−log‖Wθ‖₂`, the nonlinear defect `η`, and the true angular update `Θ₊`. This is
what makes the log-polar equation "just `eq:nd-weak-stationary-equation` written
in polar coordinates". -/

/-- Vanishing of the Euclidean norm detects the zero vector. -/
lemma gaussianEuclideanNorm_eq_zero_iff (N : ℕ) (x : Fin N → ℝ) :
    gaussianEuclideanNorm N x = 0 ↔ x = 0 := by
  rw [gaussianEuclideanNorm_eq_norm, norm_eq_zero]
  constructor
  · intro h; funext i; simpa using congrFun (congrArg WithLp.ofLp h) i
  · intro h; rw [h]; rfl

/-- `tanh` kills only the zero vector, so the nonlinear step never collapses a
nonzero state. -/
lemma tanhVec_eq_zero_iff (N : ℕ) (v : Fin N → ℝ) : tanhVec N v = 0 ↔ v = 0 := by
  constructor
  · intro h; funext i
    have hi : Real.tanh (v i) = Real.tanh 0 := by rw [Real.tanh_zero]; exact congrFun h i
    simpa using Real.tanh_injective hi
  · intro h; rw [h]; funext i; simp [tanhVec]

/-- The angular coordinate in chain coordinates. `angular` is its image in
`EuclideanSpace`; the linear algebra (`Matrix.mulVec`) happens here. -/
noncomputable def angularCoord (N : ℕ) (x : Fin N → ℝ) : Fin N → ℝ :=
  (gaussianEuclideanNorm N x)⁻¹ • x

lemma angular_eq_toLp_angularCoord (N : ℕ) (x : Fin N → ℝ) :
    angular N x = WithLp.toLp 2 (angularCoord N x) := rfl

/-- The vector step is coordinatewise `tanh` of `Wx`. -/
lemma Pstep_eq_tanhVec_mulVec (N : ℕ) (x : Fin N → ℝ) (W : Fin N → Fin N → ℝ) :
    Pstep N x W = tanhVec N (Matrix.mulVec W x) := rfl

/-- **Polar factorization of one step**: `Wx = r · Wθ`, so the step is
`tanh(r · Wθ)` — exactly the argument of `η` and `Θ₊`. -/
lemma Pstep_eq_tanhVec_smul (N : ℕ) {x : Fin N → ℝ} (W : Fin N → Fin N → ℝ)
    (hx : gaussianEuclideanNorm N x ≠ 0) :
    Pstep N x W
      = tanhVec N (gaussianEuclideanNorm N x • Matrix.mulVec W (angularCoord N x)) := by
  rw [Pstep_eq_tanhVec_mulVec, angularCoord, Matrix.mulVec_smul, smul_smul,
    mul_inv_cancel₀ hx, one_smul]

/-- **The angular update of one step is `Θ₊`**, by definition once the step is
factored. -/
lemma angular_Pstep (N : ℕ) {x : Fin N → ℝ} (W : Fin N → Fin N → ℝ)
    (hx : gaussianEuclideanNorm N x ≠ 0) :
    angular N (Pstep N x W)
      = angularPlus N (gaussianEuclideanNorm N x) (Matrix.mulVec W (angularCoord N x)) := by
  rw [Pstep_eq_tanhVec_smul N W hx, angularPlus]

/-- **The log-radial update of one step**:

  `Y(Pstep x W) = Y(x) − log‖Wθ‖₂ + η(r, Wθ)`,

the paper's `y − log‖Wθ‖₂ + η(e^{−y}, θ, W)` (tex L4539–4542). The linear
increment and the nonlinear defect separate exactly; no approximation is
involved, because `η` is *defined* as the discrepancy. -/
lemma logRadius_Pstep (N : ℕ) {x : Fin N → ℝ} (W : Fin N → Fin N → ℝ)
    (hx : gaussianEuclideanNorm N x ≠ 0)
    (hv : Matrix.mulVec W (angularCoord N x) ≠ 0) :
    logRadius N (Pstep N x W)
      = logRadius N x - Real.log (gaussianEuclideanNorm N (Matrix.mulVec W (angularCoord N x)))
        + etaDefect N (gaussianEuclideanNorm N x) (Matrix.mulVec W (angularCoord N x)) := by
  set r := gaussianEuclideanNorm N x with hrdef
  set v := Matrix.mulVec W (angularCoord N x) with hvdef
  have hr0 : 0 < r :=
    lt_of_le_of_ne (by rw [hrdef]; unfold gaussianEuclideanNorm; positivity) (Ne.symm hx)
  have hvn : gaussianEuclideanNorm N v ≠ 0 := fun h =>
    hv ((gaussianEuclideanNorm_eq_zero_iff N v).1 h)
  have htn : gaussianEuclideanNorm N (tanhVec N (r • v)) ≠ 0 := by
    intro h
    have h2 := (tanhVec_eq_zero_iff N _).1 ((gaussianEuclideanNorm_eq_zero_iff N _).1 h)
    exact hv (by simpa [smul_eq_zero, hr0.ne'] using h2)
  rw [Pstep_eq_tanhVec_smul N W hx, logRadius, logRadius, etaDefect,
    Real.log_div (by positivity) htn, Real.log_mul hr0.ne' hvn]
  ring

/-! ### The degenerate direction is null

The decomposition above needs `Wθ ≠ 0`, which the paper disposes of in one line:
"the event `Wθ = 0` has probability zero for each fixed `θ`" (tex L4530–4531).
Here it comes from `map_rowMap_gaussianMat`: the law of `W ↦ Wθ` is a product of
centered Gaussians of variance `A²·r_N(θ) > 0`, and a nondegenerate Gaussian has
no atoms. -/

lemma gaussianReal_singleton_zero_of_var_ne_zero (σ : NNReal) (hσ : σ ≠ 0) :
    gaussianReal 0 σ {(0 : ℝ)} = 0 :=
  gaussianReal_absolutelyContinuous 0 hσ Real.volume_singleton

/-- **`Wθ ≠ 0` almost surely**, for every nonzero direction `θ`. -/
lemma gaussianMat_mulVec_eq_zero {A : ℝ} (hA : A ≠ 0) {N : ℕ} (hN : 0 < N) {θ : Fin N → ℝ}
    (hθ : θ ≠ 0) : gaussianMat A N {W | Matrix.mulVec W θ = 0} = 0 := by
  have hA2 : 0 < A ^ 2 := lt_of_le_of_ne (sq_nonneg A) (Ne.symm (pow_ne_zero 2 hA))
  have hsq : 0 < ∑ j, (θ j) ^ 2 := by
    rcases Function.ne_iff.1 hθ with ⟨i, hi⟩
    refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (by simpa using hi)))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < A ^ 2 * radiusSq N θ := by unfold radiusSq; positivity
  have hvar : ((A ^ 2 * radiusSq N θ).toNNReal) ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]; exact hpos
  have hmeas : Measurable (fun (W : Fin N → Fin N → ℝ) i => ∑ j, W i j * θ j) :=
    measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ => by fun_prop
  have hset : {W : Fin N → Fin N → ℝ | Matrix.mulVec W θ = 0}
      = (fun W i => ∑ j, W i j * θ j) ⁻¹' {(0 : Fin N → ℝ)} := rfl
  have hsing : ({(0 : Fin N → ℝ)} : Set (Fin N → ℝ)) = Set.univ.pi fun _ => {(0 : ℝ)} := by
    ext w; simp [funext_iff]
  rw [hset, ← Measure.map_apply hmeas (measurableSet_singleton _), map_rowMap_gaussianMat,
    hsing, Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hN⟩ : Fin N))
    (gaussianReal_singleton_zero_of_var_ne_zero _ hvar)

/-- The angular coordinate of a nonzero state is itself nonzero, so
`gaussianMat_mulVec_eq_zero` applies to it. -/
lemma angularCoord_ne_zero (N : ℕ) {x : Fin N → ℝ} (hx : gaussianEuclideanNorm N x ≠ 0) :
    angularCoord N x ≠ 0 := by
  intro h
  refine hx ((gaussianEuclideanNorm_eq_zero_iff N x).2 ?_)
  have hxz : (gaussianEuclideanNorm N x)⁻¹ • x = 0 := h
  rcases smul_eq_zero.1 hxz with h1 | h1
  · exact absurd (inv_eq_zero.1 h1) hx
  · exact h1

/-! ### The log-polar step map

Packaging the two coordinate identities into a single map on `ℝ × 𝕊^{N−1}` — the
right-hand side of `eq:nd-log-polar-stationary` (tex L4539–4544), with the
paper's `r = e^{−y}` substituted. -/

/-- One step of the chain read entirely in log-polar coordinates:

  `(y, θ) ↦ (y − log‖Wθ‖₂ + η(e^{−y}, Wθ), Θ₊(e^{−y}, Wθ))`. -/
noncomputable def logPolarStep (N : ℕ) (y : ℝ) (θ : EuclideanSpace ℝ (Fin N))
    (W : Fin N → Fin N → ℝ) : ℝ × EuclideanSpace ℝ (Fin N) :=
  (y - Real.log (gaussianEuclideanNorm N (Matrix.mulVec W (WithLp.ofLp θ)))
     + etaDefect N (Real.exp (-y)) (Matrix.mulVec W (WithLp.ofLp θ)),
   angularPlus N (Real.exp (-y)) (Matrix.mulVec W (WithLp.ofLp θ)))

/-- `e^{−Y} = ‖x‖₂`: the paper's substitution `r = e^{−y}`. -/
lemma exp_neg_logRadius (N : ℕ) {x : Fin N → ℝ} (hx : gaussianEuclideanNorm N x ≠ 0) :
    Real.exp (-logRadius N x) = gaussianEuclideanNorm N x := by
  have hpos : 0 < gaussianEuclideanNorm N x :=
    lt_of_le_of_ne (by unfold gaussianEuclideanNorm; positivity) (Ne.symm hx)
  rw [logRadius, neg_neg, Real.exp_log hpos]

lemma ofLp_angular (N : ℕ) (x : Fin N → ℝ) :
    WithLp.ofLp (angular N x) = angularCoord N x := rfl

/-- **The log-polar step map computes the chain step**: applying `logPolarStep`
to the coordinates of `x` gives the coordinates of `Pstep N x W`. This is the
pointwise content of `eq:nd-log-polar-stationary`; integrating it against an
invariant law is all that remains. -/
lemma logPolarStep_logRadius_angular (N : ℕ) {x : Fin N → ℝ} (W : Fin N → Fin N → ℝ)
    (hx : gaussianEuclideanNorm N x ≠ 0)
    (hv : Matrix.mulVec W (angularCoord N x) ≠ 0) :
    logPolarStep N (logRadius N x) (angular N x) W
      = (logRadius N (Pstep N x W), angular N (Pstep N x W)) := by
  rw [logPolarStep, ofLp_angular, exp_neg_logRadius N hx,
    logRadius_Pstep N W hx hv, angular_Pstep N W hx]

lemma measurable_mulVec_ofLp (N : ℕ) :
    Measurable fun q : EuclideanSpace ℝ (Fin N) × (Fin N → Fin N → ℝ) =>
      Matrix.mulVec q.2 (WithLp.ofLp q.1) := by
  have hof : Measurable fun q : EuclideanSpace ℝ (Fin N) × (Fin N → Fin N → ℝ) =>
      (WithLp.ofLp q.1 : Fin N → ℝ) := (WithLp.measurable_ofLp 2 (Fin N → ℝ)).comp measurable_fst
  refine measurable_pi_lambda _ fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)).mul
    ((measurable_pi_apply j).comp hof)

/-- Abbreviation for the direction `Wθ` as a function of the whole argument
`((y, θ), W)`. Kept separate because the nested product makes unification
expensive if `logPolarStep` is unfolded in one go. -/
private lemma measurable_step_dir (N : ℕ) :
    Measurable fun q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      Matrix.mulVec q.2 (WithLp.ofLp q.1.2) :=
  (measurable_mulVec_ofLp N).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

private lemma measurable_step_radius (N : ℕ) :
    Measurable fun q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      Real.exp (-q.1.1) := by fun_prop

@[simp] lemma logPolarStep_fst (N : ℕ) (y : ℝ) (θ : EuclideanSpace ℝ (Fin N))
    (W : Fin N → Fin N → ℝ) :
    (logPolarStep N y θ W).1
      = y - Real.log (gaussianEuclideanNorm N (Matrix.mulVec W (WithLp.ofLp θ)))
        + etaDefect N (Real.exp (-y)) (Matrix.mulVec W (WithLp.ofLp θ)) := rfl

@[simp] lemma logPolarStep_snd (N : ℕ) (y : ℝ) (θ : EuclideanSpace ℝ (Fin N))
    (W : Fin N → Fin N → ℝ) :
    (logPolarStep N y θ W).2
      = angularPlus N (Real.exp (-y)) (Matrix.mulVec W (WithLp.ofLp θ)) := rfl

lemma measurable_logPolarStep_fst (N : ℕ) :
    Measurable fun q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      (logPolarStep N q.1.1 q.1.2 q.2).1 := by
  simp only [logPolarStep_fst]
  exact ((measurable_fst.comp measurable_fst).sub
      (((measurable_gaussianEuclideanNorm N).comp (measurable_step_dir N)).log)).add
    ((measurable_etaDefect N).comp ((measurable_step_radius N).prodMk (measurable_step_dir N)))

lemma measurable_logPolarStep_snd (N : ℕ) :
    Measurable fun q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      (logPolarStep N q.1.1 q.1.2 q.2).2 := by
  simp only [logPolarStep_snd, angularPlus]
  exact (measurable_angular N).comp
    ((measurable_tanhVec N).comp ((measurable_step_radius N).smul (measurable_step_dir N)))

lemma measurable_logPolarStep (N : ℕ) :
    Measurable fun q : (ℝ × EuclideanSpace ℝ (Fin N)) × (Fin N → Fin N → ℝ) =>
      logPolarStep N q.1.1 q.1.2 q.2 :=
  (measurable_logPolarStep_fst N).prodMk (measurable_logPolarStep_snd N)

/-! ### The log-polar stationary equation -/

/-- **The stationary equation in log-polar coordinates**
(`eq:nd-log-polar-stationary`, tex L4534–4548):

  `∫ Ξ dΩ_{A,N} = ∫ 𝔼[Ξ(y − log‖Wθ‖₂ + η, Θ₊)] dΩ_{A,N}`

for every bounded measurable `Ξ`. As the paper says, this "is just
`eq:nd-weak-stationary-equation` written in polar coordinates" — and here that is
literally the proof: `vector_stationary_equation` supplied with the test function
`Ξ ∘ (Y, Θ)`, then rewritten by `logPolarStep_logRadius_angular`.

The two `a.e.` conditions the pointwise identity needs are exactly the two the
paper waves at: the invariant law is origin-free (`horigin`), and `Wθ ≠ 0`
almost surely (`gaussianMat_mulVec_eq_zero`). -/
theorem logPolar_stationary_equation {A : ℝ} (hA : A ≠ 0) {N : ℕ} (hN : 0 < N)
    (π : Measure (Fin N → ℝ)) [IsProbabilityMeasure π]
    (hπ : Kernel.Invariant (Pkernel A N) π)
    (horigin : π {x | gaussianEuclideanNorm N x = 0} = 0)
    {Ξ : ℝ × EuclideanSpace ℝ (Fin N) → ℝ} (hΞ : Measurable Ξ) {C : ℝ}
    (hΞb : ∀ p, ‖Ξ p‖ ≤ C) :
    ∫ p, Ξ p ∂logPolarLaw N π
      = ∫ p, (∫ W, Ξ (logPolarStep N p.1 p.2 W) ∂gaussianMat A N) ∂logPolarLaw N π := by
  -- `π`-a.e. the state is away from the origin
  have hae : ∀ᵐ x ∂π, gaussianEuclideanNorm N x ≠ 0 := by
    rw [ae_iff]
    simpa using horigin
  -- the test function pulled back to Cartesian coordinates
  set φ : (Fin N → ℝ) → ℝ := fun x => Ξ (logRadius N x, angular N x) with hφdef
  have hφ : Measurable φ := hΞ.comp (measurable_logPolarCoords N)
  -- the inner integrands agree `π`-a.e., because for each good `x` they agree
  -- `gaussianMat`-a.e.
  have hinner : ∀ᵐ x ∂π,
      (∫ W, φ (Pstep N x W) ∂gaussianMat A N)
        = ∫ W, Ξ (logPolarStep N (logRadius N x) (angular N x) W) ∂gaussianMat A N := by
    filter_upwards [hae] with x hx
    refine (integral_congr_ae ?_).symm
    have hnull : gaussianMat A N {W | Matrix.mulVec W (angularCoord N x) = 0} = 0 :=
      gaussianMat_mulVec_eq_zero hA hN (angularCoord_ne_zero N hx)
    have haeW : ∀ᵐ W ∂gaussianMat A N, Matrix.mulVec W (angularCoord N x) ≠ 0 := by
      rw [ae_iff]
      simp only [ne_eq, not_not]
      exact hnull
    filter_upwards [haeW] with W hW
    rw [logPolarStep_logRadius_angular N W hx hW]
  calc ∫ p, Ξ p ∂logPolarLaw N π
      = ∫ x, φ x ∂π := integral_logPolarLaw N π hΞ.aestronglyMeasurable
    _ = ∫ x, (∫ W, φ (Pstep N x W) ∂gaussianMat A N) ∂π :=
        vector_stationary_equation A N π hπ hφ (fun x => hΞb _)
    _ = ∫ x, (∫ W, Ξ (logPolarStep N (logRadius N x) (angular N x) W) ∂gaussianMat A N) ∂π :=
        integral_congr_ae hinner
    _ = ∫ p, (∫ W, Ξ (logPolarStep N p.1 p.2 W) ∂gaussianMat A N) ∂logPolarLaw N π :=
        (integral_logPolarLaw N π
          ((hΞ.comp (measurable_logPolarStep N)).stronglyMeasurable.integral_prod_right'
            (ν := gaussianMat A N)).aestronglyMeasurable).symm

end AbsorptionCutoff
