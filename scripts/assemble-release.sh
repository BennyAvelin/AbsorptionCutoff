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

if [ -n "$(git -C "${repo_root}" status --porcelain=v1 --untracked-files=all)" ]; then
  echo "refusing to assemble from a dirty worktree; commit or stash all changes first" >&2
  git -C "${repo_root}" status --short >&2
  exit 1
fi

if [ -e "${destination}" ] && [ ! -d "${destination}" ]; then
  echo "destination exists and is not a directory: ${destination}" >&2
  exit 2
fi

mkdir -p "${destination}"
destination="$(cd "${destination}" && pwd)"
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
  CHANGELOG.md
  CH3_FIRST_PASSAGE_CLT_PROOF.tex
  CITATION.cff
  CONTRIBUTING.md
  CORRESPONDENCE.md
  LICENSE
  NOTICE
  SECURITY.md
  AbsorptionCutoff
  AbsorptionCutoff.lean
  README.md
  blueprint
  docker
  formalization.yaml
  lake-manifest.json
  lakefile.toml
  lean-toolchain
  manuscript
  notes
  scripts
)

cd "${repo_root}"
for path in "${release_paths[@]}"; do
  if ! git cat-file -e "HEAD:${path}" 2>/dev/null; then
    echo "release path is missing from committed HEAD: ${path}" >&2
    exit 1
  fi
done

git archive --format=tar HEAD -- "${release_paths[@]}" | tar -xf - -C "${destination}"

if find "${destination}" -type l -print -quit | grep -q .; then
  echo "release payload must not contain symbolic links" >&2
  exit 1
fi

for excluded in .git .lake .DS_Store aux CLAUDE.md GAP_ANALYSIS.md HANDOFF.md PAPER_UPDATES.md RELEASE_PLAN.md TODO.md; do
  if find "${destination}" -name "${excluded}" -print -quit | grep -q .; then
    echo "internal file leaked into release payload: ${excluded}" >&2
    exit 1
  fi
done

if find "${destination}" -type f \( \
  -name '*.olean' -o -name '*.ilean' -o -name '*.synctex.gz' -o -name '*.log' \
\) -print -quit | grep -q .; then
  echo "build artifact leaked into release payload" >&2
  exit 1
fi

(cd "${destination}" && scripts/check-release-metadata.sh)

printf 'assembled release payload from commit %s at %s\n' \
  "$(git rev-parse HEAD)" "${destination}"
