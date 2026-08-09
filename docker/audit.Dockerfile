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

FROM golang:1.25 AS landrun-build
# v0.1.17 execs correctly on arm64. It does swallow the `--` that the comparator
# passes through to lean4export, which `docker/landrun-argv-shim.sh` repairs --
# see that file for why v0.1.15, which lacks the `--` bug, is not usable here.
ARG LANDRUN_REF=v0.1.17
RUN git clone --depth 1 --branch "${LANDRUN_REF}" https://github.com/Zouuup/landrun /src \
 && cd /src \
 && go build -o /out/landrun cmd/landrun/main.go

FROM ubuntu:24.04

ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.32.0
ARG LEAN4EXPORT_REF=4e7915201d3f9f04470d9eae002fa695f7cdc589
ARG COMPARATOR_REF=07bc4ea40f2266dcb861820a2ec1fa3244ed307f

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

RUN curl -sSfL https://elan.lean-lang.org/elan-init.sh \
      | sh -s -- -y --default-toolchain "${LEAN_TOOLCHAIN}"

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
