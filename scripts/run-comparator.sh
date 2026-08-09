#!/usr/bin/env bash
#
# Run leanprover/comparator over the Mathlib-only audit surface in `Audit/`.
#
# For each challenge the comparator checks that the solution proves the *same*
# elaborated statement as the challenge, uses no axiom outside
# `permitted_axioms`, and is accepted by the Lean kernel -- building both inside
# a landrun sandbox. A pass prints "Your solution is okay!".
#
# Requires COMPARATOR_BIN, plus landrun and lean4export on PATH or in
# COMPARATOR_LANDRUN / COMPARATOR_LEAN4EXPORT. `docker/audit.Dockerfile` builds
# an image with all three pinned; the CI job supplies them directly. Must be run
# from the repository root, and the project must already be built (the sandbox
# re-elaborates only Challenge and Solution).
#
# Usage:
#   scripts/run-comparator.sh                       # every challenge
#   scripts/run-comparator.sh FixedDimensionAbsorption   # named ones only

set -euo pipefail

: "${COMPARATOR_BIN:?set COMPARATOR_BIN to the comparator binary}"

if [ "$#" -gt 0 ]; then
  configs=()
  for name in "$@"; do
    configs+=("Audit/${name}/comparator.json")
  done
else
  configs=(Audit/*/comparator.json)
fi

status=0
for cfg in "${configs[@]}"; do
  echo "::group::${cfg}"
  if lake env "${COMPARATOR_BIN}" "${cfg}"; then
    echo "PASS ${cfg}"
  else
    echo "FAIL ${cfg}"
    status=1
  fi
  echo "::endgroup::"
done

if [ "${status}" -ne 0 ]; then
  echo "comparator: at least one challenge failed" >&2
fi
exit "${status}"
