#!/usr/bin/env bash
# Assemble the tracked public-release payload from the current committed HEAD.
# The destination must not exist or must be an empty directory. This script
# never initializes Git, creates tags, configures remotes, or pushes anything.

set -euo pipefail

if [ "$#" -ne 1 ]; then
  echo "usage: $0 DESTINATION" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
destination="$1"

if [ -e "${destination}" ] && [ ! -d "${destination}" ]; then
  echo "destination exists and is not a directory: ${destination}" >&2
  exit 2
fi

mkdir -p "${destination}"
if find "${destination}" -mindepth 1 -maxdepth 1 -print -quit | grep -q .; then
  echo "destination must be empty: ${destination}" >&2
  exit 2
fi

release_paths=(
  .dockerignore
  .gitattributes
  .github
  .gitignore
  A4G4_BLACKWELL_PROOF_NOTE.tex
  Audit
  Audit.lean
  CH3_FIRST_PASSAGE_CLT_PROOF.tex
  CITATION.cff
  CONTRIBUTING.md
  CORRESPONDENCE.md
  LICENSE
  AbsorptionCutoff
  AbsorptionCutoff.lean
  README.md
  blueprint
  docker
  formalization.yaml
  lake-manifest.json
  lakefile.toml
  lean-toolchain
  notes
  scripts
)

cd "${repo_root}"
git archive --format=tar HEAD -- "${release_paths[@]}" | tar -xf - -C "${destination}"

for excluded in \
  CLAUDE.md GAP_ANALYSIS.md HANDOFF.md PAPER_UPDATES.md RELEASE_PLAN.md TODO.md aux notes/aux
do
  if [ -e "${destination}/${excluded}" ]; then
    echo "internal file leaked into release payload: ${excluded}" >&2
    exit 1
  fi
done

echo "assembled release payload at ${destination}"
