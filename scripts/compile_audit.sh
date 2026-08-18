#!/usr/bin/env bash
set -euo pipefail

printf 'lean-toolchain: '; cat lean-toolchain
printf 'mathlib pin: '; grep -A4 '\[\[require\]\]' lakefile.toml | tr '\n' ' '; echo

# Source-level and mathematical audits do not require Lean.  Run these first so
# the script remains useful in restricted artifact environments.
python3 scripts/generate_carry_certificates.py
python3 scripts/arithmetic_audit.py
python3 scripts/infinite_family_audit.py
python3 scripts/static_lean_audit.py

if grep -R -n -E '(^|[^A-Za-z])(sorry|admit|axiom)([^A-Za-z]|$)' A277223 --include='*.lean'; then
  echo 'ERROR: forbidden placeholder/custom axiom found' >&2
  exit 1
fi

# In a Git checkout, ensure generated proof certificates are reproducible.  A
# distributed artifact may not contain .git metadata, so that check is skipped
# there rather than being mistaken for a proof failure.
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git diff --exit-code -- \
    A277223/CarryObstruction/Eight.lean \
    A277223/CarryObstruction/Ten.lean
else
  echo 'NOTE: no Git worktree metadata; generated-certificate drift check skipped'
fi

# From this point onward a real Lean installation is mandatory.
command -v lean >/dev/null || { echo 'ERROR: lean not found; elaboration/kernel check not started' >&2; exit 127; }
command -v lake >/dev/null || { echo 'ERROR: lake not found; elaboration/kernel check not started' >&2; exit 127; }
lean --version
lake --version

lake update
lake exe cache get
lake build
