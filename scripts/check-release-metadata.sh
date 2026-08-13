#!/usr/bin/env bash
# Check inexpensive release invariants without downloading dependencies.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${repo_root}"

lake_version="$(sed -n 's/^version = "\([^"]*\)"/\1/p' lakefile.toml)"
readme_version="$(sed -n 's/^Release version: `\([^`]*\)`/\1/p' README.md)"
cff_version="$(sed -n 's/^version: \(.*\)/\1/p' CITATION.cff | head -n 1)"
yaml_version="$(sed -n 's/^  release_version: "\([^"]*\)"/\1/p' formalization.yaml)"
yaml_tag="$(sed -n 's/^  release_tag: "\([^"]*\)"/\1/p' formalization.yaml)"

for value in "${readme_version}" "${cff_version}" "${yaml_version}"; do
  if [ "${value}" != "${lake_version}" ]; then
    echo "release version mismatch: lake=${lake_version}, README=${readme_version}, CFF=${cff_version}, formalization=${yaml_version}" >&2
    exit 1
  fi
done

expected_tag="v${lake_version%.*}"
if [ "${yaml_tag}" != "${expected_tag}" ]; then
  echo "release tag mismatch: expected ${expected_tag}, found ${yaml_tag}" >&2
  exit 1
fi

if command -v sha256sum >/dev/null 2>&1; then
  checksum=(sha256sum -c)
else
  checksum=(shasum -a 256 -c)
fi
if ! "${checksum[@]}" manuscript/SHA256SUMS; then
  echo "manuscript checksum mismatch" >&2
  exit 1
fi

python3 - <<'PY'
import json
import re
from pathlib import Path

paths = sorted(Path("Audit").glob("*/comparator.json"))
if len(paths) != 7:
    raise SystemExit(f"expected 7 comparator configs, found {len(paths)}")

expected_challenges = set()
for path in paths:
    with path.open(encoding="utf-8") as stream:
        config = json.load(stream)
    if config.get("permitted_axioms") != ["propext", "Quot.sound", "Classical.choice"]:
        raise SystemExit(f"unexpected permitted axioms in {path}")
    if config.get("enable_nanoda") is not False:
        raise SystemExit(f"enable_nanoda must be false in {path}")
    target = path.parent.name
    expected_challenge = f"Audit.{target}.Challenge"
    expected_solution = f"Audit.{target}.Solution"
    if config.get("challenge_module") != expected_challenge:
        raise SystemExit(f"unexpected challenge module in {path}")
    if config.get("solution_module") != expected_solution:
        raise SystemExit(f"unexpected solution module in {path}")
    theorem_names = config.get("theorem_names")
    if not isinstance(theorem_names, list) or len(theorem_names) != 1:
        raise SystemExit(f"expected exactly one theorem name in {path}")
    if not isinstance(theorem_names[0], str) or not theorem_names[0].strip():
        raise SystemExit(f"invalid theorem name in {path}")
    expected_challenges.add(path.parent / "Challenge.lean")
print("comparator JSON: okay")


def lean_code(text: str) -> str:
    """Remove nested comments and string literals while preserving line breaks."""
    output = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                index += 2
            else:
                if text[index] == "\n":
                    output.append("\n")
                index += 1
            continue
        if in_string:
            char = text[index]
            if char == "\n":
                output.append("\n")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if text.startswith("/-", index):
            block_depth = 1
            index += 2
        elif text.startswith("--", index):
            newline = text.find("\n", index + 2)
            if newline == -1:
                break
            output.append("\n")
            index = newline + 1
        elif text[index] == '"':
            in_string = True
            index += 1
        else:
            output.append(text[index])
            index += 1
    if block_depth:
        raise SystemExit("unterminated Lean block comment encountered during release scan")
    if in_string:
        raise SystemExit("unterminated Lean string encountered during release scan")
    return "".join(output)


placeholder_pattern = re.compile(r"\b(?:sorry|admit|sorryAx)\b")
custom_axiom_pattern = re.compile(r"\b(?:axiom|constant)\b")

production_paths = [Path("AbsorptionCutoff.lean"), *sorted(Path("AbsorptionCutoff").rglob("*.lean"))]
audit_paths = [Path("Audit.lean"), *sorted(Path("Audit").rglob("*.lean"))]

all_lean_paths = {
    path
    for path in Path(".").rglob("*.lean")
    if ".git" not in path.parts and ".lake" not in path.parts
}
known_lean_paths = set(production_paths + audit_paths)
unexpected_lean_paths = sorted(all_lean_paths - known_lean_paths)
if unexpected_lean_paths:
    raise SystemExit(f"Lean files outside the production/audit roots: {unexpected_lean_paths!r}")

for path in production_paths:
    code = lean_code(path.read_text(encoding="utf-8"))
    placeholders = placeholder_pattern.findall(code)
    if path == Path("AbsorptionCutoff/Meta/AxiomsAudit.lean"):
        if placeholders != ["sorryAx"]:
            raise SystemExit(
                f"expected only the semantic audit's sorryAx reference in {path}, "
                f"found {placeholders!r}"
            )
    elif placeholders:
        raise SystemExit(f"production placeholder token(s) {placeholders!r} in {path}")
    custom_axioms = custom_axiom_pattern.findall(code)
    if custom_axioms:
        raise SystemExit(f"custom axiom declaration token(s) {custom_axioms!r} in {path}")

total_challenge_placeholders = 0
for path in audit_paths:
    code = lean_code(path.read_text(encoding="utf-8"))
    placeholders = placeholder_pattern.findall(code)
    if path in expected_challenges:
        if placeholders != ["sorry"]:
            raise SystemExit(
                f"expected exactly one intentional sorry in {path}, found {placeholders!r}"
            )
        total_challenge_placeholders += 1
    elif placeholders:
        raise SystemExit(f"unexpected audit placeholder token(s) {placeholders!r} in {path}")

if total_challenge_placeholders != 7:
    raise SystemExit(
        f"expected 7 intentional challenge sorries, found {total_challenge_placeholders}"
    )
print("Lean release invariants: okay")
PY

scripts/check-audit-challenge-imports.sh
echo "release metadata: ${lake_version} / ${yaml_tag} okay"
