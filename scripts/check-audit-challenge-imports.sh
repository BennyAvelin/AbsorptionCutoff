#!/usr/bin/env bash
set -euo pipefail

status=0

for challenge in Audit/*/Challenge.lean; do
  imports="$(sed -n '/^import /p' "$challenge")"
  if [[ "$imports" != "import Mathlib" ]]; then
    echo "$challenge must import only Mathlib; found:" >&2
    echo "$imports" >&2
    status=1
  fi
done

exit "$status"
