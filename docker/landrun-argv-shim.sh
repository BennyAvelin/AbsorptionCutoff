#!/usr/bin/env bash
#
# Argv-forwarding shim around landrun. Installed as COMPARATOR_LANDRUN.
#
# Why it exists: landrun >= 0.1.16 parses its command line with urfave/cli v3,
# which consumes the first literal `--` it encounters. The comparator invokes
#
#     landrun <sandbox flags> lean4export <module> -- <decls...>
#
# so the `--` that belongs to *lean4export* is swallowed; lean4export then reads
# the declaration names as further modules and fails with
# "object file ... does not exist". Passing an explicit `--` before the command
# makes urfave stop parsing there and forward the remainder untouched.
#
# This shim changes argv forwarding only: every sandbox flag is handed to the
# real landrun unmodified, so the Landlock restrictions applied are exactly the
# ones the comparator asked for. It grants nothing and relaxes nothing.
#
# Why not just pin landrun v0.1.15, which does not have the `--` bug: its
# `--ldd` dependency detection omits the aarch64 dynamic loader, so the
# sandboxed process cannot exec at all on arm64 ("permission denied" right after
# "Landlock restrictions applied successfully").
#
# Both upstream issues are worth reporting.

set -euo pipefail

: "${LANDRUN_REAL:=/usr/local/bin/landrun}"

# landrun flags that take a separate value; everything else starting with `-` is
# a boolean flag. Mirrors landrun --help.
value_flags=(--ro --rox --rw --rwx --env --log-level --bind-tcp --connect-tcp)

flags=()
while [ "$#" -gt 0 ]; do
  case "$1" in
    --)
      # Already separated by the caller; nothing to repair.
      shift
      break
      ;;
    -*)
      takes_value=0
      for vf in "${value_flags[@]}"; do
        if [ "$1" = "${vf}" ]; then takes_value=1; break; fi
      done
      flags+=("$1")
      shift
      if [ "${takes_value}" -eq 1 ] && [ "$#" -gt 0 ]; then
        flags+=("$1")
        shift
      fi
      ;;
    *)
      # First non-flag token: the command to sandbox.
      break
      ;;
  esac
done

exec "${LANDRUN_REAL}" ${flags[@]+"${flags[@]}"} -- "$@"
