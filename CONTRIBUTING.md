# Contributing / building notes

This repository is primarily a finished artifact rather than an actively
solicited collaborative project, but issues and pull requests are welcome.

## Building locally

Use the native Lean build for development. Lake builds independent modules in
parallel; a single `lake env lean <file>` invocation is useful for a focused
check but is largely serial and will not show the same CPU utilization.

```bash
lake exe cache get   # prebuilt Mathlib oleans -- do not skip
lake build           # the complete library
lake build Audit     # library plus the audit surface
```

The current checkout completes both native targets successfully. The audit
target's output includes the seven expected warnings for the intentional `sorry`s in
`Audit/*/Challenge.lean`; those are statement placeholders used by the
comparator and are not library gaps.
Set `LEAN_NUM_THREADS` to control Lean's task pool when needed, for example
`LEAN_NUM_THREADS=8 lake build Audit`.

The toolchain is pinned in [`lean-toolchain`](lean-toolchain), so
[`elan`](https://github.com/leanprover/elan) installs the right Lean
automatically, and `lake exe cache get` needs the committed
[`lake-manifest.json`](lake-manifest.json) to resolve the exact dependency
revisions.

A few practical notes for working with a development of this size:

- **Never run `lake clean`.** It wipes the Mathlib oleans and forces a
  multi-hour rebuild from source. To force a project-only rebuild, delete the
  artifacts under `.lake/build/lib/lean/AbsorptionCutoff` (and the corresponding
  `.lake/build/ir/AbsorptionCutoff`) and re-run `lake build`.

- **Lake invalidates by content hash, not mtime**, so `touch` does not trigger a
  rebuild. To force one file, delete its `.olean`/`.ilean` under
  `.lake/build/lib/lean/AbsorptionCutoff/<path>` and its `.c`/`.o` under
  `.lake/build/ir/AbsorptionCutoff/<path>`, then `lake build AbsorptionCutoff.<Module>`.

- **Watch per-module build time.** Modules here are deliberately split once a
  focused rebuild approaches ~90 seconds, because that is the point at which a
  one-lemma edit/build loop stops being usable. If a file you are growing
  crosses it, split the next coherent package into a continuation module rather
  than continuing to add declarations.

- **Profiling a slow file:**

  ```bash
  lake env lean --profile AbsorptionCutoff/<...>/YourFile.lean 2>&1 | tail -25
  ```

## Invariants to preserve

- **No `sorry` and no custom `axiom` in `AbsorptionCutoff/`.** The six
  paper-facing results and focused absorption alias reduce to Mathlib's three
  standard foundational axioms;
  [`AbsorptionCutoff/Meta/AxiomsAudit.lean`](AbsorptionCutoff/Meta/AxiomsAudit.lean)
  rejects any namespace-local custom axiom or `sorryAx` dependency and prints
  the audited declarations' axiom sets; CI builds it so the log carries the
  evidence.

- **The only `sorry`s in the repository are the seven intentional ones** in
  `Audit/*/Challenge.lean` — each is the body of the theorem being challenged,
  filled by the corresponding `Solution.lean`. That is why `Audit` is a separate
  library outside `defaultTargets`: a plain `lake build` never elaborates them.

- **Keep the challenge and solution vocabularies identical.** Each
  `Audit/<Name>/Solution.lean` repeats its challenge's definitions verbatim and
  then bridges them to the development with `rfl` lemmas. Those bridges exist so
  that any future drift becomes a build error here instead of silently changing
  what the comparator checks. If you change a definition in `AbsorptionCutoff/` that
  appears in a challenge, expect the corresponding bridge to fail, and update
  **both** files.

- **Keep the blueprint in sync.** A newly proved declaration gets `\lean{...}`
  and `\leanok` in `blueprint/src/content.tex`; `lake exe checkdecls
  blueprint/lean_decls` must resolve every `\lean{}` name against the built
  project. Regenerate and commit `blueprint/lean_decls` with `leanblueprint web`
  whenever the blueprint changes. Run `lake build Audit` before `checkdecls` so
  every configured Lake library root is available.

## Re-running the audit

See the "Verified against a Mathlib-only statement" section of the
[README](README.md). Native `lake build Audit` checks that the full audit
surface elaborates. `scripts/audit-docker.sh` is the reproducibility and
comparator-sandbox workflow: it runs the same build inside the pinned Linux
image and then invokes `leanprover/comparator`. Docker is needed here because
the comparator's Landlock sandbox cannot run directly on macOS; it is not
required for ordinary Lean development. The GitHub workflow builds and runs the
same pinned comparator toolchain directly on a Linux runner.

## Licensing contributions

By submitting a contribution, you agree that it may be distributed under this
repository's Apache License 2.0. Do not submit third-party material unless its
license is compatible and its attribution and modification notices are retained.
The bundled manuscript and its source inputs are not an open contribution target
and remain all rights reserved.
