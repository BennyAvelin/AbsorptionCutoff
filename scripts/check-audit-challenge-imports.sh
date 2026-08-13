#!/usr/bin/env bash
set -euo pipefail

status=0

for challenge in Audit/*/Challenge.lean; do
  imports="$(sed -n '/^[[:space:]]*import[[:space:]]/p' "$challenge")"
  normalized_imports="$(printf '%s\n' "$imports" | sed 's/^[[:space:]]*//; s/[[:space:]]*$//; s/[[:space:]][[:space:]]*/ /g')"
  if [[ "$normalized_imports" != "import Mathlib" ]]; then
    echo "$challenge must import only Mathlib; found:" >&2
    echo "$imports" >&2
    status=1
  fi
done

exit "$status"
