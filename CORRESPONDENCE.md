# Manuscript-to-Lean correspondence

A map from the bundled release snapshot of *Absorption cutoff and stationary
singularities for rounded Gaussian random dynamical systems* (Benny Avelin) to
this Lean development, together with an explicit ledger of every known place
where the two differ. The exact source is
[`manuscript/manuscript.pdf`](manuscript/manuscript.pdf).

The full dependency graph — 956 declaration references (952 distinct Lean
names), each carrying its `\lean{}` name — lives in the blueprint
(`blueprint/src/content.tex`); this file records the paper-facing surface and
the divergences.

## Headline results

Every paper-facing result below is exposed as an alias in
[`AbsorptionCutoff/MainTheorems.lean`](AbsorptionCutoff/MainTheorems.lean) and is
independently checked by `leanprover/comparator` against a Mathlib-only
restatement. The focused absorption row is an additional compatibility surface,
not a seventh manuscript theorem.

| Manuscript | Lean alias | Proved in | Comparator |
|---|---|---|---|
| `thm:rounded-gaussian-nearest-cutoff` (§3) | `rounded_gaussian_nearest_cutoff` | `AbsorptionCutoff/FixedWidthAbsorptionRegenerationFinal.lean` | `Audit/FixedWidthCutoff/` |
| `thm:subcritical-dimension-cutoff` (§4) | `subcritical_dimension_cutoff` | `AbsorptionCutoff/RoundedVectorReduction.lean` | `Audit/DimensionCutoff/` |
| `thm:rounded-qualitative-metastability` (§5) | `rounded_qualitative_metastability` | `AbsorptionCutoff/Metastability.lean` | `Audit/Metastability/` |
| Focused audit of its absorption clause | `rounded_fixed_dimension_absorption` | `AbsorptionCutoff/Metastability.lean` | `Audit/FixedDimensionAbsorption/` |
| `thm:gaussian-process-cutoff` (§6) | `gaussian_process_cutoff` | `AbsorptionCutoff/Supercritical/CutoffLimitAssembly.lean` | `Audit/ScalarCutoff/` |
| `cor:gaussian-vector-cutoff` (§6) | `gaussian_vector_cutoff` | `AbsorptionCutoff/Supercritical/CutoffLimitAssembly.lean` | `Audit/VectorCutoff/` |
| `thm:nd-power-singularity:intro` (§7) | `nd_power_singularity` | `AbsorptionCutoff/Supercritical/PowerSingularityRenewal.lean` | `Audit/PowerSingularity/` |

The manuscript has six headline statement blocks. Its metastability theorem has
two logically independent conclusions — exponential persistence as the
dimension grows and almost-sure absorption in each fixed dimension. The combined
paper-facing alias contains both, with the absorption clause quantified over the
paper's full state space `(ρℤ)^N ∩ [-1-ρ/2, 1+ρ/2]^N`. The same clause also
remains available through a focused compatibility alias, giving seven comparator
targets in total.

## Coverage by section

- **§2, common setup and scalar estimates.** Complete for the routes §§3–7
  consume: the path-space absorption identity, the vector/radius reduction,
  invariant selection, stopped tracking, affine entrance, and the full Koenigs
  asymptotic.
- **§3, fixed-width cutoff.** Complete. The development proves the positive-drift
  first-passage central limit theorem and its canonical and post-floor forms;
  specializes it to the Gaussian log-radius recursion with its finite nonlinear
  correction; establishes synchronous rounded/unrounded coupling, entrance,
  restart, and post-entrance absorption; and derives the exact rounded survival
  and total-variation profiles, packaged as the full manuscript `HasCutoff`
  predicate together with the manuscript's `O_ε(window)` mixing-time bounds.
  The formalized predicate checks that the center tends to infinity, the window
  is eventually positive and little-o of the center, and both cutoff limits hold.
- **§4, fixed-precision dimension cutoff.** Complete, including the
  rounded-vector lift and the mixing-time consequences.
- **§5, qualitative metastability.** Complete through exponential persistence and
  almost-sure absorption from every point of the full finite rounded state space
  `(ρℤ)^N ∩ [-1-ρ/2, 1+ρ/2]^N`.
- **§6, supercritical dimension cutoff.** Complete in scalar and reconstructed
  vector form, including the two-sided profiles and the full `HasCutoff`
  wrappers. The constant window one is proved admissible from divergence of the
  supercritical cutoff center.
- **§7, stationary singularity.** Complete for the full theorem stated in the
  introduction and for every fixed positive dimension. The development proves
  the Gamma-form characterization and uniqueness of the Cramér exponent, the
  positive coefficient, the directional limit on continuity sets of the unit
  sphere, and the radial limit. It also contains the stationary weak equation,
  the log-polar apparatus, the key renewal theorem and its Gaussian
  instantiation, the polar perturbation, and nonlinear forcing admissibility.

Two libraries were built in-project because Mathlib has no equivalent: the
positive-drift first-passage development behind §3, and the renewal-theory
development (renewal measure, directly-Riemann-integrable norm, Blackwell for
bandlimited kernels, and the key renewal theorem) behind §7.

## Divergence ledger

These are the known differences between the manuscript and the Lean development.
All of them are packaging or proof-route differences, or places where the Lean
result is *stronger*. After unfolding the standing notation and the equivalent
regime formulations recorded below, the manuscript's hypotheses imply those of
the corresponding Lean declaration, and its conclusion implies the manuscript's
conclusion.

1. **§3 is stated sequentially.** The manuscript writes the limit as `ρ ↓ 0`;
   the public `rounded_gaussian_nearest_cutoff` gives the equivalent formulation
   along every positive sequence `ρ_r → 0`, at the manuscript's exact floored
   `L_ρ = log(‖x₀‖₂/ρ)` time. It bundles the exact TV/survival identity,
   Gaussian profile limit, and same-scale full `HasCutoff` conclusion; the former
   profile-only result remains available as
   `tendsto_tvDist_roundedPkernel_fixedWidthMesh`.
2. **The renewal route differs in two harmless ways.** Lean sends the terminal
   convolution term to zero using local finiteness of the renewal measure rather
   than a walk realization with almost-sure drift to `+∞`, and its signed
   key-renewal theorem acts directly on signed kernels instead of splitting
   `Ψ = Ψ⁺ − Ψ⁻`.
3. **The manuscript's measure/operator packaging is only partially mirrored.** The
   renewal capstone is stated test-function by test-function rather than as one
   theorem about a family of finite signed sphere measures. The explicit vector
   transition-density fixed-point equations of `prop:nd-stationary-equation`, the
   bounded rank-one transfer operator of `lem:nd-gaussian-transfer`, and the
   continuous-linear-functional packaging of `Ψ_y^π` are not standalone
   declarations, because the theorem route consumes the weak equation, the scalar
   transfer moments, and bounded test-function evaluations directly.
4. **Two §7 intermediates are omitted as objects.** Lean proves the log-polar
   stationary equation directly from `vector_stationary_equation` and does not
   define `eq:nd-linear-markov-additive` or `eq:nd-transfer-operator`.
5. **Forcing continuity is proved in a stronger form.** The manuscript asks for
   continuous angular tests; `continuous_nonlinearForcing` gives continuity in the
   radial level for every *bounded measurable* angular test.
6. **The supercritical hypothesis is encoded by the drift.** The manuscript
   writes `A > A_c(N)`, while Lean assumes `0 < A` and
   `Supercritical A N`, where `Supercritical` means that the logarithmic radial
   multiplier has positive mean. This is the defining characterization of the
   same fixed-dimensional regime used in the paper.
7. **Only the radial tail notation differs.** The manuscript and Lean now both
   state the directional conclusion as normalized convergence: the directional
   probability, multiplied by `s^{-β}`, converges to `c σ̄_N(B)`. This remains
   meaningful when `σ̄_N(B) = 0`. The manuscript writes the radial conclusion
   as `π(0 < ‖x‖₂ ≤ s) \sim c s^β`, whereas Lean states the equivalent
   normalized limit `s^{-β} π(0 < ‖x‖₂ ≤ s) → c`; here `c > 0`.
8. **The metastability family is indexed by positive dimensions.** The paper's
   family `Y_0^{(N)}` is defined for `N ≥ 1`. Lean represents it as a function on
   natural numbers and therefore states its compact-well hypothesis as
   `∀ N, 0 < N → roundedRadiusSq ρ N (x N) ∈ B`. This excludes the formal
   zero-dimensional value without changing the asymptotic claim. The same
   capstone additionally exposes the uniform entrance and finite-horizon exit
   estimates used to prove exponential survival.

On the continuity hypothesis of the key renewal theorem: the Lean proof
approximates the forcing in the directly Riemann integrable norm and therefore
needs `y ↦ Ψ_y(φ)` genuinely continuous, not merely a.e. continuous. The
manuscript's `lem:nd-gaussian-renewal` states that hypothesis, so the two agree.
It is not a restriction at the point of use: the only forcing the lemma is
applied to is that of `def:nd-nonlinear-forcing`, and
`prop:nd-forcing-admissibility` proves it continuous.

## What the comparator does and does not establish

Each Mathlib-only challenge contains one intentional statement-level `sorry`;
the corresponding solution proves that exact statement from the development.
For each of the seven audited declarations, the comparator confirms three
things: the solution proves the **same elaborated statement** as the challenge;
it uses no axiom outside `propext`, `Quot.sound`, `Classical.choice`; and the Lean
kernel accepts it. Both sides are built inside a `landrun` sandbox.

It does **not** establish that the challenge statement is the theorem you care
about — that is a human reading, and it is exactly the reading the challenge files
are written to make cheap. Each `Audit/<Name>/Challenge.lean` imports only
Mathlib and rebuilds its vocabulary from Mathlib primitives, so it can be checked
without reading the 70k-line development.
