# Manuscript-to-Lean correspondence

A map from *Absorption cutoff and stationary singularities for rounded Gaussian
random dynamical systems* (Benny Avelin) to this Lean development, together with
an explicit ledger of every known place where the two differ.

The full dependency graph — 946 declarations, each carrying its `\lean{}` name —
lives in the blueprint (`blueprint/src/content.tex`); this file records the
paper-facing surface and the divergences.

## Headline results

Every one of these is exposed as an alias in
[`AbsorptionCutoff/MainTheorems.lean`](AbsorptionCutoff/MainTheorems.lean) and is independently
checked by `leanprover/comparator` against a Mathlib-only restatement.

| Manuscript | Lean alias | Proved in | Comparator |
|---|---|---|---|
| `thm:rounded-gaussian-nearest-cutoff` (§3) | `rounded_gaussian_nearest_cutoff` | `AbsorptionCutoff/FixedWidthAbsorptionRegenerationFinal.lean` | `Audit/FixedWidthCutoff/` |
| `thm:subcritical-dimension-cutoff` (§4) | `subcritical_dimension_cutoff` | `AbsorptionCutoff/RoundedVectorReduction.lean` | `Audit/DimensionCutoff/` |
| `thm:rounded-qualitative-metastability` (§5), persistence clause | `rounded_qualitative_metastability` | `AbsorptionCutoff/Metastability.lean` | `Audit/Metastability/` |
| `thm:rounded-qualitative-metastability` (§5), absorption clause | `rounded_fixed_dimension_absorption` | `AbsorptionCutoff/Metastability.lean` | `Audit/FixedDimensionAbsorption/` |
| `thm:gaussian-process-cutoff` (§6) | `gaussian_process_cutoff` | `AbsorptionCutoff/Supercritical/CutoffLimitAssembly.lean` | `Audit/ScalarCutoff/` |
| `cor:gaussian-vector-cutoff` (§6) | `gaussian_vector_cutoff` | `AbsorptionCutoff/Supercritical/CutoffLimitAssembly.lean` | `Audit/VectorCutoff/` |
| `thm:nd-power-singularity` (§7) | `nd_power_singularity` | `AbsorptionCutoff/Supercritical/PowerSingularityRenewal.lean` | `Audit/PowerSingularity/` |

The manuscript's metastability theorem has two logically independent
conclusions — exponential persistence as the dimension grows, and almost-sure
absorption in each fixed dimension. They appear as two separate aliases above,
and are audited separately.

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
  and total-variation profiles, packaged as `HasCutoff` together with the
  manuscript's `O_ε(window)` mixing-time bounds.
- **§4, fixed-precision dimension cutoff.** Complete, including the
  rounded-vector lift and the mixing-time consequences.
- **§5, qualitative metastability.** Complete through exponential persistence and
  fixed-state-space almost-sure absorption.
- **§6, supercritical dimension cutoff.** Complete in scalar and reconstructed
  vector form, including the two-sided profiles and the `HasCutoff` wrappers.
- **§7, stationary singularity.** Complete: the stationary weak equation, the
  log-polar apparatus, the Cramér exponent, the key renewal theorem and its
  Gaussian instantiation, the polar perturbation, nonlinear forcing
  admissibility, and the final power-singularity assembly.

Two libraries were built in-project because Mathlib has no equivalent: the
positive-drift first-passage development behind §3, and the renewal-theory
development (renewal measure, directly-Riemann-integrable norm, Blackwell for
bandlimited kernels, and the key renewal theorem) behind §7.

## Divergence ledger

These are the known differences between the manuscript and the Lean development.
All of them are packaging or proof-route differences, or places where the Lean
result is *stronger*; there is no hypothesis in this development weaker than the
manuscript's.

1. **§3 is stated sequentially.** The manuscript writes the limit as `ρ ↓ 0`;
   `tendsto_tvDist_roundedPkernel_fixedWidthMesh` gives the equivalent
   formulation along every positive sequence `ρ_r → 0`, at the manuscript's exact
   floored `L_ρ = log(‖x₀‖₂/ρ)` time.
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

On the continuity hypothesis of the key renewal theorem: the Lean proof
approximates the forcing in the directly Riemann integrable norm and therefore
needs `y ↦ Ψ_y(φ)` genuinely continuous, not merely a.e. continuous. The
manuscript's `lem:nd-gaussian-renewal` states that hypothesis, so the two agree.
It is not a restriction at the point of use: the only forcing the lemma is
applied to is that of `def:nd-nonlinear-forcing`, and
`prop:nd-forcing-admissibility` proves it continuous.

## What the comparator does and does not establish

For each of the seven theorems the comparator confirms three things: the solution
proves the **same elaborated statement** as the Mathlib-only challenge; it uses no
axiom outside `propext`, `Quot.sound`, `Classical.choice`; and the Lean kernel
accepts it. Both sides are built inside a `landrun` sandbox.

It does **not** establish that the challenge statement is the theorem you care
about — that is a human reading, and it is exactly the reading the challenge files
are written to make cheap. Each `Audit/<Name>/Challenge.lean` imports only
Mathlib and rebuilds its vocabulary from Mathlib primitives, so it can be checked
without reading the 70k-line development.
