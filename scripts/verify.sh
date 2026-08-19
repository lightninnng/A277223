#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

python3 scripts/generate_carry_certificates.py

if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  git diff --exit-code -- \
    A277223/CarryObstruction/EightData.lean \
    A277223/CarryObstruction/Eight.lean \
    A277223/CarryObstruction/TenData.lean \
    A277223/CarryObstruction/Ten.lean
fi

python3 scripts/arithmetic_audit.py
python3 scripts/infinite_family_audit.py
python3 scripts/static_lean_audit.py

command -v lake >/dev/null 2>&1 || {
  echo "lake is required for the formal build" >&2
  exit 127
}

lake exe cache get
lake build
