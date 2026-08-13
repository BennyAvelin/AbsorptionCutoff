# Environment for the leanprover/comparator audit of the Mathlib-only statement
# surface in `Audit/`.
#
# `landrun` needs the Landlock LSM, so the audit cannot run on macOS directly.
# This image provides a Linux environment for it; the same pins are used by
# `.github/workflows/comparator.yml`, so local and CI runs check the same thing.
#
# All four components are pinned. comparator and lean4export must target the
# project's Lean version -- both of the commits below are the v4.32.0 window.
#
# Build (from the repository root):
#   docker build -f docker/audit.Dockerfile -t absorptioncutoff-audit .
#
# Run: use `scripts/audit-docker.sh`, which bind-mounts the repository read-only
# at /src and copies it into an ext4 named volume at /project. Do *not* run the
# comparator directly against a bind mount: Landlock cannot govern Docker
# Desktop's `fakeowner` filesystem, so every read inside the sandbox fails with
# EACCES even though the same read succeeds unsandboxed. Verified 2026-08-03.

FROM golang:1.25.12-trixie@sha256:76b0883ac35e19ca7340b058f8b37f0ca6bd4e3e43c6fcfbfe990a0c8a2611bd AS landrun-build
# v0.1.17 execs correctly on arm64. It does swallow the `--` that the comparator
# passes through to lean4export, which `docker/landrun-argv-shim.sh` repairs --
# see that file for why v0.1.15, which lacks the `--` bug, is not usable here.
ARG LANDRUN_REF=62823c05e58ec22c1f91b4c8468318c1f97f2d32
RUN git clone https://github.com/Zouuup/landrun /src \
 && cd /src \
 && git checkout --detach "${LANDRUN_REF}" \
 && test "$(git rev-parse HEAD)" = "${LANDRUN_REF}" \
 && go build -o /out/landrun cmd/landrun/main.go

FROM ubuntu:24.04@sha256:561618e2c15bf2397621dd04f96926663a3b5616c189cf7e38db7e82f5c538ea

ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.32.0
ARG ELAN_VERSION=v4.2.3
ARG ELAN_SHA256_AMD64=df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2
ARG ELAN_SHA256_ARM64=cb69af0803b04157bc30201c29c12fca882bb3ad8b43476b8d2d3064810bc3ac
ARG TARGETARCH
ARG LEAN4EXPORT_REF=4e7915201d3f9f04470d9eae002fa695f7cdc589
ARG COMPARATOR_REF=07bc4ea40f2266dcb861820a2ec1fa3244ed307f

# The base, source, and installer inputs are pinned. Ubuntu's package index is
# intentionally not snapshot-pinned, so builds are controlled but not expected
# to be byte-for-byte identical indefinitely.
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git rsync \
 && rm -rf /var/lib/apt/lists/*

COPY --from=landrun-build /out/landrun /usr/local/bin/landrun
COPY docker/landrun-argv-shim.sh /usr/local/bin/landrun-shim
RUN chmod 0755 /usr/local/bin/landrun-shim

# The comparator's guarantees assume it is not run by a privileged user.
USER ubuntu
ENV HOME=/home/ubuntu
ENV PATH=/home/ubuntu/.elan/bin:${PATH}

RUN set -eux; \
    case "${TARGETARCH}" in \
      amd64) elan_target=x86_64-unknown-linux-gnu; elan_sha256="${ELAN_SHA256_AMD64}" ;; \
      arm64) elan_target=aarch64-unknown-linux-gnu; elan_sha256="${ELAN_SHA256_ARM64}" ;; \
      *) echo "unsupported Docker target architecture: ${TARGETARCH}" >&2; exit 1 ;; \
    esac; \
    curl -fsSL -o /tmp/elan.tar.gz \
      "https://github.com/leanprover/elan/releases/download/${ELAN_VERSION}/elan-${elan_target}.tar.gz"; \
    echo "${elan_sha256}  /tmp/elan.tar.gz" | sha256sum -c -; \
    tar -xzf /tmp/elan.tar.gz -C /tmp; \
    /tmp/elan-init -y --no-modify-path --default-toolchain "${LEAN_TOOLCHAIN}"; \
    rm -f /tmp/elan-init /tmp/elan.tar.gz; \
    lean --version

RUN git clone https://github.com/leanprover/lean4export "${HOME}/lean4export" \
 && cd "${HOME}/lean4export" \
 && git checkout --detach "${LEAN4EXPORT_REF}" \
 && lake build

RUN git clone https://github.com/leanprover/comparator "${HOME}/comparator" \
 && cd "${HOME}/comparator" \
 && git checkout --detach "${COMPARATOR_REF}" \
 && lake build

ENV LANDRUN_REAL=/usr/local/bin/landrun
ENV COMPARATOR_LANDRUN=/usr/local/bin/landrun-shim
ENV COMPARATOR_LEAN4EXPORT=/home/ubuntu/lean4export/.lake/build/bin/lean4export
ENV COMPARATOR_BIN=/home/ubuntu/comparator/.lake/build/bin/comparator

# A fresh named volume inherits the ownership of the image directory it covers,
# so `/project/.lake` must belong to `ubuntu` here -- otherwise the volume is
# root-owned and the unprivileged user cannot write build artifacts into it.
USER root
RUN mkdir -p /project/.lake && chown -R ubuntu:ubuntu /project
USER ubuntu

WORKDIR /project
CMD ["bash"]
