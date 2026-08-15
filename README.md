# AbsorptionCutoff

A machine-checked **Lean 4** formalization of the manuscript *Absorption cutoff
and stationary singularities for rounded Gaussian random dynamical systems*
(Benny Avelin), built on
[`mathlib`](https://github.com/leanprover-community/mathlib4).

[![CI](https://github.com/BennyAvelin/AbsorptionCutoff/actions/workflows/build.yml/badge.svg)](https://github.com/BennyAvelin/AbsorptionCutoff/actions/workflows/build.yml)
[![Comparator audit](https://github.com/BennyAvelin/AbsorptionCutoff/actions/workflows/comparator.yml/badge.svg)](https://github.com/BennyAvelin/AbsorptionCutoff/actions/workflows/comparator.yml)

Release version: `1.1.0`

## What this is

The manuscript studies the Gaussian random dynamical system on `ℝ^N`

> `x_{t+1} = Q_ρ( tanh(W_t x_t) )`,   `W_t` i.i.d. with entries `∼ 𝒩(0, A²/N)`,

where `tanh` acts coordinatewise and `Q_ρ` rounds each coordinate to the nearest
point of the grid `ρℤ`. Rounding makes the zero bin absorbing, and the paper
describes when and how sharply the chain is absorbed — and, in the supercritical
regime, what the invariant law looks like near the origin.

- **86 Lean modules and roughly 72,000 lines** under `AbsorptionCutoff/`, plus
  **15 audit modules and roughly 3,800 lines** in the Mathlib-only audit surface
  (`Audit.lean` and `Audit/`).
- **No `sorry`** anywhere in the production library under `AbsorptionCutoff/`.
  (Each comparator challenge in `Audit/` contains its single intentional
  statement-level `sorry`, filled by the corresponding solution file.)
- **No custom `axiom`.** The seven audited declarations use no axioms beyond
  Mathlib's three standard foundational axioms — `propext`, `Classical.choice`,
  `Quot.sound` — verified by
  [`AbsorptionCutoff/Meta/AxiomsAudit.lean`](AbsorptionCutoff/Meta/AxiomsAudit.lean).
- Pinned to Lean `v4.32.0` and Mathlib `v4.32.0`.

## Scope and faithfulness

**Every theorem in the manuscript's main-results section is formalized.** The
manuscript has six headline statement blocks; they are exposed through the six
paper-facing aliases in
[`AbsorptionCutoff/MainTheorems.lean`](AbsorptionCutoff/MainTheorems.lean). There
are seven comparator targets because the fixed-dimensional absorption clause of
the metastability theorem also has a focused compatibility alias and an
independent audit. Where a Lean statement is packaged differently from the
manuscript, it is recorded theorem by theorem in
[`CORRESPONDENCE.md`](CORRESPONDENCE.md). Every difference listed there is
packaging, proof route, or a case where the Lean result is *stronger*. After
unfolding the standing notation and equivalent regime formulations, the
manuscript's hypotheses imply those of the corresponding Lean declaration, and
its conclusion implies the manuscript's conclusion.

## The manuscript

The current manuscript snapshot tracked by this repository is included as
[`manuscript/manuscript.pdf`](manuscript/manuscript.pdf), together
with self-contained LaTeX build inputs. Its SHA-256 digest and provenance are
recorded in
[`manuscript/README.md`](manuscript/README.md). This copy makes the source-to-Lean
correspondence reviewable before an arXiv version is available. The manuscript
snapshot shipped with formalization release 1.1.0 remains available at tag
`v1.1`.

## Main results

All six paper-facing results are stated in
[`AbsorptionCutoff/MainTheorems.lean`](AbsorptionCutoff/MainTheorems.lean),
alongside compatibility aliases used by the seven focused audits.

The shared `HasCutoff` predicate implements the manuscript's full cutoff
definition: the center tends to infinity, the window is eventually positive and
is little-o of the center, and the two early/late total-variation limits hold.
The two limit conditions alone are available separately as `HasCutoffLimits`.

**Fixed-width vanishing-mesh cutoff** — `rounded_gaussian_nearest_cutoff`. Fix the
dimension `N` and assume `0 < A < A_c(N)`. Along any positive mesh sequence
`ρ_r → 0`, at the paper's floored time the total-variation distance equals the
canonical absorption-time survival probability and converges to `Φ(−a)`. The
same theorem includes the full manuscript `HasCutoff` conclusion at center
`L_ρ/γ_{A,N}` with window `σ_N γ_{A,N}^{-3/2}√L_ρ` and Gaussian profile; in
particular the center diverges and the window is positive and little-o of it.

**Fixed-precision dimension cutoff** — `subcritical_dimension_cutoff`. Fix the mesh
`ρ ∈ (0,1)` and a width below the lattice threshold `A_lat`. As `N → ∞` the
distance from `δ₀` tends to `1` one step before the deterministic terminal-scale
entrance time and to `0` two steps after it.

**Metastability** — `rounded_qualitative_metastability` is the combined
paper-facing theorem. Starting from a positive-dimensional family whose rounded
radii remain in a compact subset of a rightmost positive-drift component, the
chain survives for a time **exponential in `N`** with probability tending to one;
while in each *fixed* dimension it is absorbed almost surely from every point of
the full paper state space `(ρℤ)^N ∩ [-1-ρ/2, 1+ρ/2]^N`. The focused
compatibility alias `rounded_fixed_dimension_absorption` exposes this same
full-state-space clause separately and is audited independently.

**Supercritical dimension cutoff** — `gaussian_process_cutoff` and
`gaussian_vector_cutoff`. For `A > 1`, the scalar squared-radius chain and the
reconstructed vector chain both have total-variation cutoff at

> `t_N = ( ½·log N + log|κ(A, q*, q₀)| ) / |log V_A′(q*)|`

with the admissible constant window `1`, against an eventually unique family of invariant laws whose
`(q − q*)²`-variance is `O(1/N)`. Here `q*` is the positive fixed point of the
Gaussian mean map `V_A` and `κ` its Koenigs coefficient.

**Stationary power singularity** — `nd_power_singularity`. In fixed dimension and
the supercritical regime, every invariant law `π` of the unrounded vector chain
that gives the origin zero mass and lives in the coordinate box has an exact
power-law singularity at the origin: for `s ↓ 0`,

> `s^{−β} · π{ 0 < ‖x‖₂ ≤ s, x/‖x‖₂ ∈ B }  →  C(A,N,π) · σ̄(B)`

for every measurable `B` whose boundary is null for the normalized surface
measure `σ̄`, with `β = β_{A,N}` the Cramér exponent — the root of the Gaussian
transfer moment equation `ℳ_{A,N}(β) = 1` in `(0,N)` — and `C(A,N,π) > 0`.

## Verified against a Mathlib-only statement

So that the claims above can be checked without trusting the ~70k-line
development, **the six paper-facing results and the focused
fixed-dimensional-absorption alias are independently verified by
[`leanprover/comparator`](https://github.com/leanprover/comparator)**. Each is
restated using **only Mathlib** — no project definitions — in a `Challenge.lean`
ending in one intentional `sorry`, and a `Solution.lean` proves that exact
statement from the library. The comparator confirms the two have identical
elaborated types, that the proof uses no axiom outside the three standard ones,
and that the Lean kernel accepts it, building both sides in a `landrun` sandbox.

| Directory | Checked theorem |
| --- | --- |
| [`Audit/FixedWidthCutoff/`](Audit/FixedWidthCutoff/) | `AbsorptionCutoff.StatementAudit.FixedWidthCutoff.rounded_gaussian_nearest_cutoff` |
| [`Audit/DimensionCutoff/`](Audit/DimensionCutoff/) | `…DimensionCutoff.subcritical_dimension_cutoff` |
| [`Audit/Metastability/`](Audit/Metastability/) | `…Metastability.rounded_qualitative_metastability` |
| [`Audit/FixedDimensionAbsorption/`](Audit/FixedDimensionAbsorption/) | `…FixedDimensionAbsorption.rounded_fixed_dimension_absorption` |
| [`Audit/ScalarCutoff/`](Audit/ScalarCutoff/) | `…ScalarCutoff.gaussian_process_cutoff` |
| [`Audit/VectorCutoff/`](Audit/VectorCutoff/) | `…VectorCutoff.gaussian_vector_cutoff` |
| [`Audit/PowerSingularity/`](Audit/PowerSingularity/) | `…PowerSingularity.nd_power_singularity` |

Each challenge rebuilds its statement vocabulary from Mathlib primitives; each
solution repeats it verbatim and bridges to the development
with `rfl` lemmas, so the Mathlib-only statement is *definitionally* the
development's theorem rather than merely equivalent to it. Every configuration
permits only

```json
["propext", "Quot.sound", "Classical.choice"]
```

and sets `enable_nanoda: false`. All seven audit targets printed
`Your solution is okay!` in the full-suite rerun on 2026-08-13.

For ordinary Lean development, build natively first:

```bash
lake exe cache get
lake build           # complete library; parallel native build
lake build Audit     # library plus all seven audit challenge/solutions
```

The current checkout completes both targets successfully. The audit target's
output includes the seven expected warnings for the intentional `sorry`s in the
challenge files. Prefer `lake build` over `lake env lean <file>` when you want
parallel compilation; the latter is a focused, mostly serial single-file
check. Lean's task-pool size can be set with `LEAN_NUM_THREADS` when needed.

To reproduce the comparator audit in its pinned sandbox:

```bash
docker build -f docker/audit.Dockerfile -t absorptioncutoff-audit .
scripts/audit-docker.sh          # or: scripts/audit-docker.sh PowerSingularity
```

Docker is used for the comparator's controlled Linux/Landlock environment, not
because Lean requires Docker for normal builds. The image pins its base images
by digest, Elan archives by checksum, and comparator, `lean4export`, and
`landrun` by commit. Ubuntu's package index is not snapshot-pinned, so rebuilding
the image is not claimed to be bit-for-bit reproducible. Two further caveats are stated
in full in [`formalization.yaml`](formalization.yaml) and belong here too:
the comparator is invoked through
[`docker/landrun-argv-shim.sh`](docker/landrun-argv-shim.sh), which repairs an
argv-forwarding bug in current `landrun` and changes nothing about the sandbox
flags; and the `systemd-run` hardening from the comparator's documentation is
**not** applied — the run is confined by the container instead, which is a weaker
guarantee than the documented one.

## Blueprint

The formal dependency graph is maintained as a
[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) under
[`blueprint/`](blueprint/): **956 declaration references (952 distinct Lean
names)**, each carrying its `\lean{}` name and `\leanok` status. The generated
declaration list is committed, and after building the audit library all names
resolve against the project via
`lake exe checkdecls blueprint/lean_decls`. The build workflow runs this check
on every commit.

## Building

The project uses [`elan`](https://github.com/leanprover/elan) and Lake; the
toolchain is pinned in [`lean-toolchain`](lean-toolchain).

```bash
lake exe cache get   # prebuilt Mathlib oleans -- avoids a multi-hour build
lake build           # complete native library build
lake build Audit     # complete native build plus audit surface
```

`lake exe cache get` requires the committed
[`lake-manifest.json`](lake-manifest.json), which pins the exact dependency
revisions. `lake build Audit` elaborates the whole tree, the audit root, and the
seven challenge/solution pairs; its output includes one expected `sorry` warning
from each challenge. Live build status and timings are in the
[Actions tab](https://github.com/BennyAvelin/AbsorptionCutoff/actions) and the
badges above. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for practical notes on
working with a development of this size.

The pinned local comparator audit was rerun on 2026-08-13 from commit `b0943d9`
on the merged `main` branch with `scripts/audit-docker.sh`. All seven
configurations printed `Your solution is okay!` and passed: fixed-width,
dimension, metastability, fixed-dimensional absorption, scalar cutoff, vector
cutoff, and power singularity. The committed `Audit/*/comparator.json` files
record the per-target configurations; the successful output is preserved in
the [comparator CI run](https://github.com/BennyAvelin/AbsorptionCutoff/actions/runs/31692518893).

To use the library, `import AbsorptionCutoff` pulls in the whole development; the public
results are in `import AbsorptionCutoff.MainTheorems`.

## Repository layout

```
AbsorptionCutoff/
  Rounding.lean, Lattice.lean      nearest-grid rounding; the lattice threshold
  Chains.lean, VectorReduction.lean, RoundedVectorReduction.lean
                                   the scalar, vector and rounded kernels
  MeanMap/                         the Gaussian mean map V_A and its dynamics
  Cutoff.lean                      total variation, cutoff admissibility/limits, mixing time
  FirstPassageCLT.lean             positive-drift first-passage asymptotics
  FixedWidth*.lean                 the fixed-width cutoff route (§3)
  DimensionCutoff.lean, OrbitAmplification.lean, RadiusConcentration.lean   (§4)
  Metastability.lean               persistence and absorption (§5)
  Supercritical/                   the supercritical route (§6) and the
                                   stationary/renewal theory (§7)
  MainTheorems.lean                paper-facing and compatibility aliases
  Meta/AxiomsAudit.lean            #print axioms for those seven
AbsorptionCutoff.lean                      root module (imports the whole library)
Audit/                             Mathlib-only comparator challenges/solutions
blueprint/                         the formal dependency graph
manuscript/                        fixed source snapshot and its provenance
notes/                             companion proof notes (see below)
docker/, scripts/                  the pinned audit environment and runners
```

## Companion proof notes

Two results the manuscript cites from the literature had to be *proved* here,
because Mathlib contains neither: a central limit theorem for the first passage
time of a positive-drift random walk, and the key renewal theorem for directly
Riemann integrable functions. Those proofs appear nowhere in the paper, so
[`notes/formalized-libraries.tex`](notes/formalized-libraries.tex) records both
at outline level and maps every step to the declaration carrying it. The longer
arguments behind it are
[`CH3_FIRST_PASSAGE_CLT_PROOF.tex`](CH3_FIRST_PASSAGE_CLT_PROOF.tex) (the
first-passage route) and
[`A4G4_BLACKWELL_PROOF_NOTE.tex`](A4G4_BLACKWELL_PROOF_NOTE.tex) (the
Abel-regularized Fourier argument that identifies Blackwell's constant).

## How this was built

This project was motivated in part by two large-scale Lean formalizations by
Scott Armstrong and collaborators:
[`DeGiorgi`](https://github.com/scottnarmstrong/DeGiorgi), by Scott Armstrong and
Julia Kempe, which formalizes core elliptic De Giorgi–Nash–Moser theory, and
[`CoarseGraining`](https://github.com/scottnarmstrong/CoarseGraining), by Scott
Armstrong and Tuomo Kuusi, which formalizes coarse-graining theory and
quantitative stochastic homogenization. They demonstrated that closely
supervised, LLM-assisted formalization can bring substantial modern analysis
into Lean on a practical timescale. In particular, CoarseGraining's explicit
manuscript-to-Lean correspondence and independent comparator checks helped
motivate the release and audit structure used here.

This development was produced by **autoformalization**: the Lean code was written
from the manuscript's arguments by large language models — OpenAI's ChatGPT and
Anthropic's Claude — driven by agentic coding harnesses under the close
supervision of the author, rather than typed by hand. The models, tooling, cost,
and review status are disclosed in
[`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

The Lean kernel checks the proof terms for the formal statements actually
written: the production library contains no `sorry` and declares no custom
axiom, both machine-verified, and the seven audited declarations are additionally
comparator-checked against Mathlib-only restatements. Kernel checking alone does
not establish that those statements faithfully express the manuscript. That
semantic correspondence is documented theorem by theorem in
[`CORRESPONDENCE.md`](CORRESPONDENCE.md) and has been reviewed by the author; it
has not received external peer review.

The public Git history begins from a curated release snapshot. The roughly
2,870 earlier agentic development commits reported in
[`formalization.yaml`](formalization.yaml) are not part of this repository's
public history. Release-level corrections are summarized in
[`CHANGELOG.md`](CHANGELOG.md).

## Author and citation

The Lean development is by **Benny Avelin** (Department of Mathematics, Uppsala
University). If you use this formalization, please cite it using the metadata in
[`CITATION.cff`](CITATION.cff).

## Acknowledgements

Built on [Lean 4](https://lean-lang.org) and
[Mathlib](https://github.com/leanprover-community/mathlib4). The audit in
[`Audit/`](Audit/) uses
[`leanprover/comparator`](https://github.com/leanprover/comparator),
[`lean4export`](https://github.com/leanprover/lean4export), and
[`landrun`](https://github.com/Zouuup/landrun); the blueprint uses
[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) and
[`checkdecls`](https://github.com/PatrickMassot/checkdecls). Template provenance
and retained third-party attribution are recorded in [`NOTICE`](NOTICE).

## License

The Lean source, documentation, scripts, and project metadata are licensed under
the **Apache License 2.0** (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)). The
bundled manuscript and its source inputs are © 2026 Benny Avelin, all rights
reserved, and are not covered by the Apache license; see
[`manuscript/README.md`](manuscript/README.md).
