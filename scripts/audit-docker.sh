#!/usr/bin/env bash
#
# Run the comparator audit locally, inside the pinned Linux image built by
# `docker/audit.Dockerfile`.
#
# Why the copy: Landlock -- which landrun, and therefore the comparator, rely on
# -- cannot govern Docker Desktop's `fakeowner` bind-mount filesystem. Every read
# inside the sandbox fails with EACCES there, even though the same read succeeds
# unsandboxed. So the repository is bind-mounted read-only at /src and copied
# into an ext4 named volume at /project, where the sandbox behaves. The volume
# also persists `.lake`, so only the first run pays for the full build. (The CI
# job needs none of this: a GitHub runner's checkout is on an ordinary
# filesystem.)
#
# Prerequisite:
#   docker build -f docker/audit.Dockerfile -t absorptioncutoff-audit .
#
# Usage:
#   scripts/audit-docker.sh                    # every challenge
#   scripts/audit-docker.sh FixedWidthCutoff   # named ones only

set -euo pipefail

IMAGE="${AUDIT_IMAGE:-absorptioncutoff-audit}"
VOLUME="${AUDIT_VOLUME:-absorptioncutoff-project}"
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

docker run --rm --pull=never \
  -v "${repo_root}":/src:ro \
  -v "${VOLUME}":/project \
  "${IMAGE}" bash -lc '
    set -euo pipefail
    find /project -type f \( -name .env -o -name ".env.*" -o -name "*.pem" -o -name "*.key" \) \
      ! -name .env.example -delete
    rsync -a --delete --exclude .git --exclude .lake \
      --include .env.example --exclude .env --exclude ".env.*" \
      --exclude "*.pem" --exclude "*.key" /src/ /project/
    cd /project
    lake exe cache get
    lake build
    lake build Audit
    scripts/run-comparator.sh "$@"
  ' bash "$@"
